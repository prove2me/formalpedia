-- Prove2me | solution 1 for syracuse_descends_range_1323480_1325480
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:36.126236+00:00
-- url     : https://prove2.me/submissions/e4a9c7c9-9c87-4b3b-ab41-5774b15cbd73

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


theorem B1490953 : Blo 1323480 1490953 := bbase (se 2 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 1490953 = 1118215) (by norm_num)
theorem B2514989 : Blo 1323480 2514989 := bbase (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) (by norm_num)
theorem B2981933 : Blo 1323480 2981933 := bbase (se 3 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 2981933 = 1118225) (by norm_num)
theorem B1490989 : Blo 1323480 1490989 := bbase (se 3 (by rfl) ⟨279560, by rfl⟩ : syracuseStep 1490989 = 559121) (by norm_num)
theorem B6045749 : Blo 1323480 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B2236477 : Blo 1323480 2236477 := bbase (se 3 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 2236477 = 838679) (by norm_num)
theorem B3350605 : Blo 1323480 3350605 := bbase (se 3 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 3350605 = 1256477) (by norm_num)
theorem B1491025 : Blo 1323480 1491025 := bbase (se 2 (by rfl) ⟨559134, by rfl⟩ : syracuseStep 1491025 = 1118269) (by norm_num)
theorem B2982005 : Blo 1323480 2982005 := bbase (se 5 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 2982005 = 279563) (by norm_num)
theorem B1491061 : Blo 1323480 1491061 := bbase (se 5 (by rfl) ⟨69893, by rfl⟩ : syracuseStep 1491061 = 139787) (by norm_num)
theorem B4472981 : Blo 1323480 4472981 := bbase (se 6 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 4472981 = 209671) (by norm_num)
theorem B2236565 : Blo 1323480 2236565 := bbase (se 6 (by rfl) ⟨52419, by rfl⟩ : syracuseStep 2236565 = 104839) (by norm_num)
theorem B1491097 : Blo 1323480 1491097 := bbase (se 2 (by rfl) ⟨559161, by rfl⟩ : syracuseStep 1491097 = 1118323) (by norm_num)
theorem B3350717 : Blo 1323480 3350717 := bbase (se 3 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 3350717 = 1256519) (by norm_num)
theorem B2982077 : Blo 1323480 2982077 := bbase (se 3 (by rfl) ⟨559139, by rfl⟩ : syracuseStep 2982077 = 1118279) (by norm_num)
theorem B1491133 : Blo 1323480 1491133 := bbase (se 3 (by rfl) ⟨279587, by rfl⟩ : syracuseStep 1491133 = 559175) (by norm_num)
theorem B2515141 : Blo 1323480 2515141 := bbase (se 4 (by rfl) ⟨235794, by rfl⟩ : syracuseStep 2515141 = 471589) (by norm_num)
theorem B2982149 : Blo 1323480 2982149 := bbase (se 4 (by rfl) ⟨279576, by rfl⟩ : syracuseStep 2982149 = 559153) (by norm_num)
theorem B2236693 : Blo 1323480 2236693 := bbase (se 6 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 2236693 = 104845) (by norm_num)
theorem B6037829 : Blo 1323480 6037829 := bbase (se 4 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 6037829 = 1132093) (by norm_num)
theorem B2982221 : Blo 1323480 2982221 := bbase (se 3 (by rfl) ⟨559166, by rfl⟩ : syracuseStep 2982221 = 1118333) (by norm_num)
theorem B3350909 : Blo 1323480 3350909 := bbase (se 3 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 3350909 = 1256591) (by norm_num)
theorem B2982293 : Blo 1323480 2982293 := bbase (se 6 (by rfl) ⟨69897, by rfl⟩ : syracuseStep 2982293 = 139795) (by norm_num)
theorem B6455717 : Blo 1323480 6455717 := bbase (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) (by norm_num)
theorem B5366245 : Blo 1323480 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B6447605 : Blo 1323480 6447605 := bbase (se 5 (by rfl) ⟨302231, by rfl⟩ : syracuseStep 6447605 = 604463) (by norm_num)
theorem B2515445 : Blo 1323480 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B3875381 : Blo 1323480 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B4473413 : Blo 1323480 4473413 := bbase (se 4 (by rfl) ⟨419382, by rfl⟩ : syracuseStep 4473413 = 838765) (by norm_num)
theorem B6709877 : Blo 1323480 6709877 := bbase (se 5 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 6709877 = 629051) (by norm_num)
theorem B2122381 : Blo 1323480 2122381 := bbase (se 3 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 2122381 = 795893) (by norm_num)
theorem B13591189 : Blo 1323480 13591189 := bbase (se 6 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 13591189 = 637087) (by norm_num)
theorem B3351253 : Blo 1323480 3351253 := bbase (se 7 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 3351253 = 78545) (by norm_num)
theorem B5030693 : Blo 1323480 5030693 := bbase (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) (by norm_num)
theorem B1884989 : Blo 1323480 1884989 := bbase (se 3 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 1884989 = 706871) (by norm_num)
theorem B3351365 : Blo 1323480 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B1885069 : Blo 1323480 1885069 := bbase (se 3 (by rfl) ⟨353450, by rfl⟩ : syracuseStep 1885069 = 706901) (by norm_num)
theorem B2827237 : Blo 1323480 2827237 := bbase (se 4 (by rfl) ⟨265053, by rfl⟩ : syracuseStep 2827237 = 530107) (by norm_num)
theorem B1885189 : Blo 1323480 1885189 := bbase (se 4 (by rfl) ⟨176736, by rfl⟩ : syracuseStep 1885189 = 353473) (by norm_num)
theorem B3351557 : Blo 1323480 3351557 := bbase (se 4 (by rfl) ⟨314208, by rfl⟩ : syracuseStep 3351557 = 628417) (by norm_num)
theorem B6702101 : Blo 1323480 6702101 := bbase (se 6 (by rfl) ⟨157080, by rfl⟩ : syracuseStep 6702101 = 314161) (by norm_num)
theorem B5661733 : Blo 1323480 5661733 := bbase (se 4 (by rfl) ⟨530787, by rfl⟩ : syracuseStep 5661733 = 1061575) (by norm_num)
theorem B2548781 : Blo 1323480 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B8487989 : Blo 1323480 8487989 := bbase (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) (by norm_num)
theorem B5030981 : Blo 1323480 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B1885285 : Blo 1323480 1885285 := bbase (se 4 (by rfl) ⟨176745, by rfl⟩ : syracuseStep 1885285 = 353491) (by norm_num)
theorem B2827381 : Blo 1323480 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B2385085 : Blo 1323480 2385085 := bbase (se 3 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 2385085 = 894407) (by norm_num)
theorem B2516197 : Blo 1323480 2516197 := bbase (se 4 (by rfl) ⟨235893, by rfl⟩ : syracuseStep 2516197 = 471787) (by norm_num)
theorem B9544949 : Blo 1323480 9544949 := bbase (se 5 (by rfl) ⟨447419, by rfl⟩ : syracuseStep 9544949 = 894839) (by norm_num)
theorem B1361197 : Blo 1323480 1361197 := bbase (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) (by norm_num)
theorem B2385229 : Blo 1323480 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B3351901 : Blo 1323480 3351901 := bbase (se 3 (by rfl) ⟨628481, by rfl⟩ : syracuseStep 3351901 = 1256963) (by norm_num)
theorem B2516341 : Blo 1323480 2516341 := bbase (se 5 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 2516341 = 235907) (by norm_num)
theorem B6800773 : Blo 1323480 6800773 := bbase (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) (by norm_num)
theorem B3352013 : Blo 1323480 3352013 := bbase (se 3 (by rfl) ⟨628502, by rfl⟩ : syracuseStep 3352013 = 1257005) (by norm_num)
theorem B2827757 : Blo 1323480 2827757 := bbase (se 3 (by rfl) ⟨530204, by rfl⟩ : syracuseStep 2827757 = 1060409) (by norm_num)
theorem B2385445 : Blo 1323480 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B32212565 : Blo 1323480 32212565 := bbase (se 8 (by rfl) ⟨188745, by rfl⟩ : syracuseStep 32212565 = 377491) (by norm_num)
theorem B1885781 : Blo 1323480 1885781 := bbase (se 8 (by rfl) ⟨11049, by rfl⟩ : syracuseStep 1885781 = 22099) (by norm_num)
theorem B3352205 : Blo 1323480 3352205 := bbase (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) (by norm_num)
theorem B25462421 : Blo 1323480 25462421 := bbase (se 6 (by rfl) ⟨596775, by rfl⟩ : syracuseStep 25462421 = 1193551) (by norm_num)
theorem B7546517 : Blo 1323480 7546517 := bbase (se 6 (by rfl) ⟨176871, by rfl⟩ : syracuseStep 7546517 = 353743) (by norm_num)
theorem B4245173 : Blo 1323480 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B7538453 : Blo 1323480 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B4245301 : Blo 1323480 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B2828125 : Blo 1323480 2828125 := bbase (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) (by norm_num)
theorem B3630997 : Blo 1323480 3630997 := bbase (se 6 (by rfl) ⟨85101, by rfl⟩ : syracuseStep 3630997 = 170203) (by norm_num)
theorem B3352549 : Blo 1323480 3352549 := bbase (se 4 (by rfl) ⟨314301, by rfl⟩ : syracuseStep 3352549 = 628603) (by norm_num)
theorem B2582525 : Blo 1323480 2582525 := bbase (se 3 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 2582525 = 968447) (by norm_num)
theorem B1509421 : Blo 1323480 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B1591373 : Blo 1323480 1591373 := bbase (se 3 (by rfl) ⟨298382, by rfl⟩ : syracuseStep 1591373 = 596765) (by norm_num)
theorem B3352661 : Blo 1323480 3352661 := bbase (se 8 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 3352661 = 39289) (by norm_num)
theorem B2386037 : Blo 1323480 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B9545845 : Blo 1323480 9545845 := bbase (se 5 (by rfl) ⟨447461, by rfl⟩ : syracuseStep 9545845 = 894923) (by norm_num)
theorem B1886333 : Blo 1323480 1886333 := bbase (se 3 (by rfl) ⟨353687, by rfl⟩ : syracuseStep 1886333 = 707375) (by norm_num)
theorem B20400277 : Blo 1323480 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B2418853 : Blo 1323480 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B5032165 : Blo 1323480 5032165 := bbase (se 4 (by rfl) ⟨471765, by rfl⟩ : syracuseStep 5032165 = 943531) (by norm_num)
theorem B4466933 : Blo 1323480 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B3352853 : Blo 1323480 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B6703397 : Blo 1323480 6703397 := bbase (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) (by norm_num)
theorem B2386253 : Blo 1323480 2386253 := bbase (se 3 (by rfl) ⟨447422, by rfl⟩ : syracuseStep 2386253 = 894845) (by norm_num)
theorem B1591709 : Blo 1323480 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B1591825 : Blo 1323480 1591825 := bbase (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) (by norm_num)
theorem B5032469 : Blo 1323480 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B1591897 : Blo 1323480 1591897 := bbase (se 2 (by rfl) ⟨596961, by rfl⟩ : syracuseStep 1591897 = 1193923) (by norm_num)
theorem B3770981 : Blo 1323480 3770981 := bbase (se 4 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 3770981 = 707059) (by norm_num)
theorem B2386541 : Blo 1323480 2386541 := bbase (se 3 (by rfl) ⟨447476, by rfl⟩ : syracuseStep 2386541 = 894953) (by norm_num)
theorem B3353197 : Blo 1323480 3353197 := bbase (se 3 (by rfl) ⟨628724, by rfl⟩ : syracuseStep 3353197 = 1257449) (by norm_num)
theorem B1591921 : Blo 1323480 1591921 := bbase (se 2 (by rfl) ⟨596970, by rfl⟩ : syracuseStep 1591921 = 1193941) (by norm_num)
theorem B3181189 : Blo 1323480 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B4467365 : Blo 1323480 4467365 := bbase (se 4 (by rfl) ⟨418815, by rfl⟩ : syracuseStep 4467365 = 837631) (by norm_num)
theorem B1985237 : Blo 1323480 1985237 := bbase (se 7 (by rfl) ⟨23264, by rfl⟩ : syracuseStep 1985237 = 46529) (by norm_num)
theorem B3353309 : Blo 1323480 3353309 := bbase (se 3 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 3353309 = 1257491) (by norm_num)
theorem B1985261 : Blo 1323480 1985261 := bbase (se 3 (by rfl) ⟨372236, by rfl⟩ : syracuseStep 1985261 = 744473) (by norm_num)
theorem B1592065 : Blo 1323480 1592065 := bbase (se 2 (by rfl) ⟨597024, by rfl⟩ : syracuseStep 1592065 = 1194049) (by norm_num)
theorem B1985285 : Blo 1323480 1985285 := bbase (se 4 (by rfl) ⟨186120, by rfl⟩ : syracuseStep 1985285 = 372241) (by norm_num)
theorem B1723141 : Blo 1323480 1723141 := bbase (se 4 (by rfl) ⟨161544, by rfl⟩ : syracuseStep 1723141 = 323089) (by norm_num)
theorem B1985309 : Blo 1323480 1985309 := bbase (se 3 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 1985309 = 744491) (by norm_num)
theorem B1985333 : Blo 1323480 1985333 := bbase (se 5 (by rfl) ⟨93062, by rfl⟩ : syracuseStep 1985333 = 186125) (by norm_num)
theorem B7547701 : Blo 1323480 7547701 := bbase (se 5 (by rfl) ⟨353798, by rfl⟩ : syracuseStep 7547701 = 707597) (by norm_num)
theorem B1985357 : Blo 1323480 1985357 := bbase (se 3 (by rfl) ⟨372254, by rfl⟩ : syracuseStep 1985357 = 744509) (by norm_num)
theorem B1985381 : Blo 1323480 1985381 := bbase (se 4 (by rfl) ⟨186129, by rfl⟩ : syracuseStep 1985381 = 372259) (by norm_num)
theorem B1887085 : Blo 1323480 1887085 := bbase (se 3 (by rfl) ⟨353828, by rfl⟩ : syracuseStep 1887085 = 707657) (by norm_num)
theorem B1985405 : Blo 1323480 1985405 := bbase (se 3 (by rfl) ⟨372263, by rfl⟩ : syracuseStep 1985405 = 744527) (by norm_num)
theorem B6359957 : Blo 1323480 6359957 := bbase (se 6 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 6359957 = 298123) (by norm_num)
theorem B1985429 : Blo 1323480 1985429 := bbase (se 6 (by rfl) ⟨46533, by rfl⟩ : syracuseStep 1985429 = 93067) (by norm_num)
theorem B3353501 : Blo 1323480 3353501 := bbase (se 3 (by rfl) ⟨628781, by rfl⟩ : syracuseStep 3353501 = 1257563) (by norm_num)
theorem B1985453 : Blo 1323480 1985453 := bbase (se 3 (by rfl) ⟨372272, by rfl⟩ : syracuseStep 1985453 = 744545) (by norm_num)
theorem B1985477 : Blo 1323480 1985477 := bbase (se 4 (by rfl) ⟨186138, by rfl⟩ : syracuseStep 1985477 = 372277) (by norm_num)
theorem B1985501 : Blo 1323480 1985501 := bbase (se 3 (by rfl) ⟨372281, by rfl⟩ : syracuseStep 1985501 = 744563) (by norm_num)
theorem B1985525 : Blo 1323480 1985525 := bbase (se 5 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 1985525 = 186143) (by norm_num)
theorem B1985549 : Blo 1323480 1985549 := bbase (se 3 (by rfl) ⟨372290, by rfl⟩ : syracuseStep 1985549 = 744581) (by norm_num)
theorem B1985573 : Blo 1323480 1985573 := bbase (se 4 (by rfl) ⟨186147, by rfl⟩ : syracuseStep 1985573 = 372295) (by norm_num)
theorem B5237797 : Blo 1323480 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B1985597 : Blo 1323480 1985597 := bbase (se 3 (by rfl) ⟨372299, by rfl⟩ : syracuseStep 1985597 = 744599) (by norm_num)
theorem B1985621 : Blo 1323480 1985621 := bbase (se 8 (by rfl) ⟨11634, by rfl⟩ : syracuseStep 1985621 = 23269) (by norm_num)
theorem B4467797 : Blo 1323480 4467797 := bbase (se 8 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 4467797 = 52357) (by norm_num)
theorem B12725333 : Blo 1323480 12725333 := bbase (se 8 (by rfl) ⟨74562, by rfl⟩ : syracuseStep 12725333 = 149125) (by norm_num)
theorem B1985645 : Blo 1323480 1985645 := bbase (se 3 (by rfl) ⟨372308, by rfl⟩ : syracuseStep 1985645 = 744617) (by norm_num)
theorem B1985669 : Blo 1323480 1985669 := bbase (se 4 (by rfl) ⟨186156, by rfl⟩ : syracuseStep 1985669 = 372313) (by norm_num)
theorem B1985693 : Blo 1323480 1985693 := bbase (se 3 (by rfl) ⟨372317, by rfl⟩ : syracuseStep 1985693 = 744635) (by norm_num)
theorem B1985717 : Blo 1323480 1985717 := bbase (se 5 (by rfl) ⟨93080, by rfl⟩ : syracuseStep 1985717 = 186161) (by norm_num)
theorem B6368453 : Blo 1323480 6368453 := bbase (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) (by norm_num)
theorem B1985741 : Blo 1323480 1985741 := bbase (se 3 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 1985741 = 744653) (by norm_num)
theorem B1985765 : Blo 1323480 1985765 := bbase (se 4 (by rfl) ⟨186165, by rfl⟩ : syracuseStep 1985765 = 372331) (by norm_num)
theorem B3181805 : Blo 1323480 3181805 := bbase (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) (by norm_num)
theorem B3353845 : Blo 1323480 3353845 := bbase (se 5 (by rfl) ⟨157211, by rfl⟩ : syracuseStep 3353845 = 314423) (by norm_num)
theorem B1985789 : Blo 1323480 1985789 := bbase (se 3 (by rfl) ⟨372335, by rfl⟩ : syracuseStep 1985789 = 744671) (by norm_num)
theorem B1985813 : Blo 1323480 1985813 := bbase (se 6 (by rfl) ⟨46542, by rfl⟩ : syracuseStep 1985813 = 93085) (by norm_num)
theorem B6450469 : Blo 1323480 6450469 := bbase (se 4 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 6450469 = 1209463) (by norm_num)
theorem B1985837 : Blo 1323480 1985837 := bbase (se 3 (by rfl) ⟨372344, by rfl⟩ : syracuseStep 1985837 = 744689) (by norm_num)
theorem B2829629 : Blo 1323480 2829629 := bbase (se 3 (by rfl) ⟨530555, by rfl⟩ : syracuseStep 2829629 = 1061111) (by norm_num)
theorem B1985861 : Blo 1323480 1985861 := bbase (se 4 (by rfl) ⟨186174, by rfl⟩ : syracuseStep 1985861 = 372349) (by norm_num)
theorem B5098837 : Blo 1323480 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B1985885 : Blo 1323480 1985885 := bbase (se 3 (by rfl) ⟨372353, by rfl⟩ : syracuseStep 1985885 = 744707) (by norm_num)
theorem B3353957 : Blo 1323480 3353957 := bbase (se 4 (by rfl) ⟨314433, by rfl⟩ : syracuseStep 3353957 = 628867) (by norm_num)
theorem B1985909 : Blo 1323480 1985909 := bbase (se 5 (by rfl) ⟨93089, by rfl⟩ : syracuseStep 1985909 = 186179) (by norm_num)
theorem B1985933 : Blo 1323480 1985933 := bbase (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) (by norm_num)
theorem B4771237 : Blo 1323480 4771237 := bbase (se 4 (by rfl) ⟨447303, by rfl⟩ : syracuseStep 4771237 = 894607) (by norm_num)
theorem B1985957 : Blo 1323480 1985957 := bbase (se 4 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 1985957 = 372367) (by norm_num)
theorem B3181997 : Blo 1323480 3181997 := bbase (se 3 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 3181997 = 1193249) (by norm_num)
theorem B1985981 : Blo 1323480 1985981 := bbase (se 3 (by rfl) ⟨372371, by rfl⟩ : syracuseStep 1985981 = 744743) (by norm_num)
theorem B2829773 : Blo 1323480 2829773 := bbase (se 3 (by rfl) ⟨530582, by rfl⟩ : syracuseStep 2829773 = 1061165) (by norm_num)
theorem B1986005 : Blo 1323480 1986005 := bbase (se 7 (by rfl) ⟨23273, by rfl⟩ : syracuseStep 1986005 = 46547) (by norm_num)
theorem B1986029 : Blo 1323480 1986029 := bbase (se 3 (by rfl) ⟨372380, by rfl⟩ : syracuseStep 1986029 = 744761) (by norm_num)
theorem B4468229 : Blo 1323480 4468229 := bbase (se 4 (by rfl) ⟨418896, by rfl⟩ : syracuseStep 4468229 = 837793) (by norm_num)
theorem B1986053 : Blo 1323480 1986053 := bbase (se 4 (by rfl) ⟨186192, by rfl⟩ : syracuseStep 1986053 = 372385) (by norm_num)
theorem B1986077 : Blo 1323480 1986077 := bbase (se 3 (by rfl) ⟨372389, by rfl⟩ : syracuseStep 1986077 = 744779) (by norm_num)
theorem B3354149 : Blo 1323480 3354149 := bbase (se 4 (by rfl) ⟨314451, by rfl⟩ : syracuseStep 3354149 = 628903) (by norm_num)
theorem B1986101 : Blo 1323480 1986101 := bbase (se 5 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 1986101 = 186197) (by norm_num)
theorem B6704693 : Blo 1323480 6704693 := bbase (se 5 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 6704693 = 628565) (by norm_num)
theorem B1986125 : Blo 1323480 1986125 := bbase (se 3 (by rfl) ⟨372398, by rfl⟩ : syracuseStep 1986125 = 744797) (by norm_num)
theorem B1986149 : Blo 1323480 1986149 := bbase (se 4 (by rfl) ⟨186201, by rfl⟩ : syracuseStep 1986149 = 372403) (by norm_num)
theorem B1986173 : Blo 1323480 1986173 := bbase (se 3 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 1986173 = 744815) (by norm_num)
theorem B1986197 : Blo 1323480 1986197 := bbase (se 6 (by rfl) ⟨46551, by rfl⟩ : syracuseStep 1986197 = 93103) (by norm_num)
theorem B1986221 : Blo 1323480 1986221 := bbase (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) (by norm_num)
theorem B1986245 : Blo 1323480 1986245 := bbase (se 4 (by rfl) ⟨186210, by rfl⟩ : syracuseStep 1986245 = 372421) (by norm_num)
theorem B1986269 : Blo 1323480 1986269 := bbase (se 3 (by rfl) ⟨372425, by rfl⟩ : syracuseStep 1986269 = 744851) (by norm_num)
theorem B1986293 : Blo 1323480 1986293 := bbase (se 5 (by rfl) ⟨93107, by rfl⟩ : syracuseStep 1986293 = 186215) (by norm_num)
theorem B3772165 : Blo 1323480 3772165 := bbase (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) (by norm_num)
theorem B1511173 : Blo 1323480 1511173 := bbase (se 4 (by rfl) ⟨141672, by rfl⟩ : syracuseStep 1511173 = 283345) (by norm_num)
theorem B1986317 : Blo 1323480 1986317 := bbase (se 3 (by rfl) ⟨372434, by rfl⟩ : syracuseStep 1986317 = 744869) (by norm_num)
theorem B1986341 : Blo 1323480 1986341 := bbase (se 4 (by rfl) ⟨186219, by rfl⟩ : syracuseStep 1986341 = 372439) (by norm_num)
theorem B2830133 : Blo 1323480 2830133 := bbase (se 5 (by rfl) ⟨132662, by rfl⟩ : syracuseStep 2830133 = 265325) (by norm_num)
theorem B1986365 : Blo 1323480 1986365 := bbase (se 3 (by rfl) ⟨372443, by rfl⟩ : syracuseStep 1986365 = 744887) (by norm_num)
theorem B2387789 : Blo 1323480 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B1986389 : Blo 1323480 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B1986413 : Blo 1323480 1986413 := bbase (se 3 (by rfl) ⟨372452, by rfl⟩ : syracuseStep 1986413 = 744905) (by norm_num)
theorem B3354493 : Blo 1323480 3354493 := bbase (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) (by norm_num)
theorem B1986437 : Blo 1323480 1986437 := bbase (se 4 (by rfl) ⟨186228, by rfl⟩ : syracuseStep 1986437 = 372457) (by norm_num)
theorem B6041477 : Blo 1323480 6041477 := bbase (se 4 (by rfl) ⟨566388, by rfl⟩ : syracuseStep 6041477 = 1132777) (by norm_num)
theorem B1986461 : Blo 1323480 1986461 := bbase (se 3 (by rfl) ⟨372461, by rfl⟩ : syracuseStep 1986461 = 744923) (by norm_num)
theorem B3772325 : Blo 1323480 3772325 := bbase (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) (by norm_num)
theorem B1675181 : Blo 1323480 1675181 := bbase (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) (by norm_num)
theorem B4468661 : Blo 1323480 4468661 := bbase (se 5 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 4468661 = 418937) (by norm_num)
theorem B1986485 : Blo 1323480 1986485 := bbase (se 5 (by rfl) ⟨93116, by rfl⟩ : syracuseStep 1986485 = 186233) (by norm_num)
theorem B1986509 : Blo 1323480 1986509 := bbase (se 3 (by rfl) ⟨372470, by rfl⟩ : syracuseStep 1986509 = 744941) (by norm_num)
theorem B1675237 : Blo 1323480 1675237 := bbase (se 4 (by rfl) ⟨157053, by rfl⟩ : syracuseStep 1675237 = 314107) (by norm_num)
theorem B1986533 : Blo 1323480 1986533 := bbase (se 4 (by rfl) ⟨186237, by rfl⟩ : syracuseStep 1986533 = 372475) (by norm_num)
theorem B1511401 : Blo 1323480 1511401 := bbase (se 2 (by rfl) ⟨566775, by rfl⟩ : syracuseStep 1511401 = 1133551) (by norm_num)
theorem B3182573 : Blo 1323480 3182573 := bbase (se 3 (by rfl) ⟨596732, by rfl⟩ : syracuseStep 3182573 = 1193465) (by norm_num)
theorem B3354605 : Blo 1323480 3354605 := bbase (se 3 (by rfl) ⟨628988, by rfl⟩ : syracuseStep 3354605 = 1257977) (by norm_num)
theorem B1986557 : Blo 1323480 1986557 := bbase (se 3 (by rfl) ⟨372479, by rfl⟩ : syracuseStep 1986557 = 744959) (by norm_num)
theorem B25440277 : Blo 1323480 25440277 := bbase (se 6 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 25440277 = 1192513) (by norm_num)
theorem B1986581 : Blo 1323480 1986581 := bbase (se 6 (by rfl) ⟨46560, by rfl⟩ : syracuseStep 1986581 = 93121) (by norm_num)
theorem B1511465 : Blo 1323480 1511465 := bbase (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) (by norm_num)
theorem B1986605 : Blo 1323480 1986605 := bbase (se 3 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 1986605 = 744977) (by norm_num)
theorem B1675333 : Blo 1323480 1675333 := bbase (se 4 (by rfl) ⟨157062, by rfl⟩ : syracuseStep 1675333 = 314125) (by norm_num)
theorem B1986629 : Blo 1323480 1986629 := bbase (se 4 (by rfl) ⟨186246, by rfl⟩ : syracuseStep 1986629 = 372493) (by norm_num)
theorem B5656661 : Blo 1323480 5656661 := bbase (se 8 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 5656661 = 66289) (by norm_num)
theorem B1986653 : Blo 1323480 1986653 := bbase (se 3 (by rfl) ⟨372497, by rfl⟩ : syracuseStep 1986653 = 744995) (by norm_num)
theorem B2977901 : Blo 1323480 2977901 := bbase (se 3 (by rfl) ⟨558356, by rfl⟩ : syracuseStep 2977901 = 1116713) (by norm_num)
theorem B10735733 : Blo 1323480 10735733 := bbase (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) (by norm_num)
theorem B1986677 : Blo 1323480 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B12087413 : Blo 1323480 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B1986701 : Blo 1323480 1986701 := bbase (se 3 (by rfl) ⟨372506, by rfl⟩ : syracuseStep 1986701 = 745013) (by norm_num)
theorem B3772565 : Blo 1323480 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B1986725 : Blo 1323480 1986725 := bbase (se 4 (by rfl) ⟨186255, by rfl⟩ : syracuseStep 1986725 = 372511) (by norm_num)
theorem B3354797 : Blo 1323480 3354797 := bbase (se 3 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 3354797 = 1258049) (by norm_num)
theorem B2977973 : Blo 1323480 2977973 := bbase (se 5 (by rfl) ⟨139592, by rfl⟩ : syracuseStep 2977973 = 279185) (by norm_num)
theorem B1986749 : Blo 1323480 1986749 := bbase (se 3 (by rfl) ⟨372515, by rfl⟩ : syracuseStep 1986749 = 745031) (by norm_num)
theorem B3395789 : Blo 1323480 3395789 := bbase (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) (by norm_num)
theorem B1986773 : Blo 1323480 1986773 := bbase (se 7 (by rfl) ⟨23282, by rfl⟩ : syracuseStep 1986773 = 46565) (by norm_num)
theorem B1986797 : Blo 1323480 1986797 := bbase (se 3 (by rfl) ⟨372524, by rfl⟩ : syracuseStep 1986797 = 745049) (by norm_num)
theorem B1675505 : Blo 1323480 1675505 := bbase (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) (by norm_num)
theorem B2978045 : Blo 1323480 2978045 := bbase (se 3 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 2978045 = 1116767) (by norm_num)
theorem B1986821 : Blo 1323480 1986821 := bbase (se 4 (by rfl) ⟨186264, by rfl⟩ : syracuseStep 1986821 = 372529) (by norm_num)
theorem B1986845 : Blo 1323480 1986845 := bbase (se 3 (by rfl) ⟨372533, by rfl⟩ : syracuseStep 1986845 = 745067) (by norm_num)
theorem B1675561 : Blo 1323480 1675561 := bbase (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) (by norm_num)
theorem B1986869 : Blo 1323480 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B2978117 : Blo 1323480 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B1986893 : Blo 1323480 1986893 := bbase (se 3 (by rfl) ⟨372542, by rfl⟩ : syracuseStep 1986893 = 745085) (by norm_num)
theorem B11317589 : Blo 1323480 11317589 := bbase (se 10 (by rfl) ⟨16578, by rfl⟩ : syracuseStep 11317589 = 33157) (by norm_num)
theorem B3772757 : Blo 1323480 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B4469093 : Blo 1323480 4469093 := bbase (se 4 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 4469093 = 837955) (by norm_num)
theorem B1986917 : Blo 1323480 1986917 := bbase (se 4 (by rfl) ⟨186273, by rfl⟩ : syracuseStep 1986917 = 372547) (by norm_num)
theorem B3182957 : Blo 1323480 3182957 := bbase (se 3 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 3182957 = 1193609) (by norm_num)
theorem B2683253 : Blo 1323480 2683253 := bbase (se 5 (by rfl) ⟨125777, by rfl⟩ : syracuseStep 2683253 = 251555) (by norm_num)
theorem B5656949 : Blo 1323480 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B1986941 : Blo 1323480 1986941 := bbase (se 3 (by rfl) ⟨372551, by rfl⟩ : syracuseStep 1986941 = 745103) (by norm_num)
theorem B1675657 : Blo 1323480 1675657 := bbase (se 2 (by rfl) ⟨628371, by rfl⟩ : syracuseStep 1675657 = 1256743) (by norm_num)
theorem B1700233 : Blo 1323480 1700233 := bbase (se 2 (by rfl) ⟨637587, by rfl⟩ : syracuseStep 1700233 = 1275175) (by norm_num)
theorem B2978189 : Blo 1323480 2978189 := bbase (se 3 (by rfl) ⟨558410, by rfl⟩ : syracuseStep 2978189 = 1116821) (by norm_num)
theorem B7156117 : Blo 1323480 7156117 := bbase (se 6 (by rfl) ⟨167721, by rfl⟩ : syracuseStep 7156117 = 335443) (by norm_num)
theorem B1986965 : Blo 1323480 1986965 := bbase (se 6 (by rfl) ⟨46569, by rfl⟩ : syracuseStep 1986965 = 93139) (by norm_num)
theorem B1986989 : Blo 1323480 1986989 := bbase (se 3 (by rfl) ⟨372560, by rfl⟩ : syracuseStep 1986989 = 745121) (by norm_num)
theorem B1987013 : Blo 1323480 1987013 := bbase (se 4 (by rfl) ⟨186282, by rfl⟩ : syracuseStep 1987013 = 372565) (by norm_num)
theorem B2978261 : Blo 1323480 2978261 := bbase (se 7 (by rfl) ⟨34901, by rfl⟩ : syracuseStep 2978261 = 69803) (by norm_num)
theorem B1987037 : Blo 1323480 1987037 := bbase (se 3 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 1987037 = 745139) (by norm_num)
theorem B1987061 : Blo 1323480 1987061 := bbase (se 5 (by rfl) ⟨93143, by rfl⟩ : syracuseStep 1987061 = 186287) (by norm_num)
theorem B1987085 : Blo 1323480 1987085 := bbase (se 3 (by rfl) ⟨372578, by rfl⟩ : syracuseStep 1987085 = 745157) (by norm_num)
theorem B2978333 : Blo 1323480 2978333 := bbase (se 3 (by rfl) ⟨558437, by rfl⟩ : syracuseStep 2978333 = 1116875) (by norm_num)
theorem B1987109 : Blo 1323480 1987109 := bbase (se 4 (by rfl) ⟨186291, by rfl⟩ : syracuseStep 1987109 = 372583) (by norm_num)
theorem B1675829 : Blo 1323480 1675829 := bbase (se 5 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 1675829 = 157109) (by norm_num)
theorem B1987133 : Blo 1323480 1987133 := bbase (se 3 (by rfl) ⟨372587, by rfl⟩ : syracuseStep 1987133 = 745175) (by norm_num)
theorem B1987157 : Blo 1323480 1987157 := bbase (se 8 (by rfl) ⟨11643, by rfl⟩ : syracuseStep 1987157 = 23287) (by norm_num)
theorem B1413721 : Blo 1323480 1413721 := bbase (se 2 (by rfl) ⟨530145, by rfl⟩ : syracuseStep 1413721 = 1060291) (by norm_num)
theorem B2978405 : Blo 1323480 2978405 := bbase (se 4 (by rfl) ⟨279225, by rfl⟩ : syracuseStep 2978405 = 558451) (by norm_num)
theorem B1675885 : Blo 1323480 1675885 := bbase (se 3 (by rfl) ⟨314228, by rfl⟩ : syracuseStep 1675885 = 628457) (by norm_num)
theorem B1987181 : Blo 1323480 1987181 := bbase (se 3 (by rfl) ⟨372596, by rfl⟩ : syracuseStep 1987181 = 745193) (by norm_num)
theorem B1987205 : Blo 1323480 1987205 := bbase (se 4 (by rfl) ⟨186300, by rfl⟩ : syracuseStep 1987205 = 372601) (by norm_num)
theorem B1987229 : Blo 1323480 1987229 := bbase (se 3 (by rfl) ⟨372605, by rfl⟩ : syracuseStep 1987229 = 745211) (by norm_num)
theorem B1413793 : Blo 1323480 1413793 := bbase (se 2 (by rfl) ⟨530172, by rfl⟩ : syracuseStep 1413793 = 1060345) (by norm_num)
theorem B2978477 : Blo 1323480 2978477 := bbase (se 3 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 2978477 = 1116929) (by norm_num)
theorem B1987253 : Blo 1323480 1987253 := bbase (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) (by norm_num)
theorem B1675981 : Blo 1323480 1675981 := bbase (se 3 (by rfl) ⟨314246, by rfl⟩ : syracuseStep 1675981 = 628493) (by norm_num)
theorem B1987277 : Blo 1323480 1987277 := bbase (se 3 (by rfl) ⟨372614, by rfl⟩ : syracuseStep 1987277 = 745229) (by norm_num)
theorem B1987301 : Blo 1323480 1987301 := bbase (se 4 (by rfl) ⟨186309, by rfl⟩ : syracuseStep 1987301 = 372619) (by norm_num)
theorem B2978549 : Blo 1323480 2978549 := bbase (se 5 (by rfl) ⟨139619, by rfl⟩ : syracuseStep 2978549 = 279239) (by norm_num)
theorem B12907253 : Blo 1323480 12907253 := bbase (se 5 (by rfl) ⟨605027, by rfl⟩ : syracuseStep 12907253 = 1210055) (by norm_num)
theorem B1987325 : Blo 1323480 1987325 := bbase (se 3 (by rfl) ⟨372623, by rfl⟩ : syracuseStep 1987325 = 745247) (by norm_num)
theorem B4469525 : Blo 1323480 4469525 := bbase (se 6 (by rfl) ⟨104754, by rfl⟩ : syracuseStep 4469525 = 209509) (by norm_num)
theorem B1987349 : Blo 1323480 1987349 := bbase (se 6 (by rfl) ⟨46578, by rfl⟩ : syracuseStep 1987349 = 93157) (by norm_num)
theorem B1987373 : Blo 1323480 1987373 := bbase (se 3 (by rfl) ⟨372632, by rfl⟩ : syracuseStep 1987373 = 745265) (by norm_num)
theorem B2978621 : Blo 1323480 2978621 := bbase (se 3 (by rfl) ⟨558491, by rfl⟩ : syracuseStep 2978621 = 1116983) (by norm_num)
theorem B6705989 : Blo 1323480 6705989 := bbase (se 4 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 6705989 = 1257373) (by norm_num)
theorem B1987397 : Blo 1323480 1987397 := bbase (se 4 (by rfl) ⟨186318, by rfl⟩ : syracuseStep 1987397 = 372637) (by norm_num)
theorem B1413973 : Blo 1323480 1413973 := bbase (se 9 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 1413973 = 8285) (by norm_num)
theorem B1987421 : Blo 1323480 1987421 := bbase (se 3 (by rfl) ⟨372641, by rfl⟩ : syracuseStep 1987421 = 745283) (by norm_num)
theorem B1987445 : Blo 1323480 1987445 := bbase (se 5 (by rfl) ⟨93161, by rfl⟩ : syracuseStep 1987445 = 186323) (by norm_num)
theorem B1676153 : Blo 1323480 1676153 := bbase (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) (by norm_num)
theorem B3396485 : Blo 1323480 3396485 := bbase (se 4 (by rfl) ⟨318420, by rfl⟩ : syracuseStep 3396485 = 636841) (by norm_num)
theorem B2978693 : Blo 1323480 2978693 := bbase (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) (by norm_num)
theorem B1987469 : Blo 1323480 1987469 := bbase (se 3 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 1987469 = 745301) (by norm_num)
theorem B22942613 : Blo 1323480 22942613 := bbase (se 6 (by rfl) ⟨537717, by rfl⟩ : syracuseStep 22942613 = 1075435) (by norm_num)
theorem B1987493 : Blo 1323480 1987493 := bbase (se 4 (by rfl) ⟨186327, by rfl⟩ : syracuseStep 1987493 = 372655) (by norm_num)
theorem B1676209 : Blo 1323480 1676209 := bbase (se 2 (by rfl) ⟨628578, by rfl⟩ : syracuseStep 1676209 = 1257157) (by norm_num)
theorem B1987517 : Blo 1323480 1987517 := bbase (se 3 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 1987517 = 745319) (by norm_num)
theorem B3019717 : Blo 1323480 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B2978765 : Blo 1323480 2978765 := bbase (se 3 (by rfl) ⟨558518, by rfl⟩ : syracuseStep 2978765 = 1117037) (by norm_num)
theorem B2266061 : Blo 1323480 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B1987541 : Blo 1323480 1987541 := bbase (se 7 (by rfl) ⟨23291, by rfl⟩ : syracuseStep 1987541 = 46583) (by norm_num)
theorem B2683885 : Blo 1323480 2683885 := bbase (se 3 (by rfl) ⟨503228, by rfl⟩ : syracuseStep 2683885 = 1006457) (by norm_num)
theorem B1987565 : Blo 1323480 1987565 := bbase (se 3 (by rfl) ⟨372668, by rfl⟩ : syracuseStep 1987565 = 745337) (by norm_num)
theorem B5026805 : Blo 1323480 5026805 := bbase (se 5 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 5026805 = 471263) (by norm_num)
theorem B1987589 : Blo 1323480 1987589 := bbase (se 4 (by rfl) ⟨186336, by rfl⟩ : syracuseStep 1987589 = 372673) (by norm_num)
theorem B1676305 : Blo 1323480 1676305 := bbase (se 2 (by rfl) ⟨628614, by rfl⟩ : syracuseStep 1676305 = 1257229) (by norm_num)
theorem B2978837 : Blo 1323480 2978837 := bbase (se 6 (by rfl) ⟨69816, by rfl⟩ : syracuseStep 2978837 = 139633) (by norm_num)
theorem B1987613 : Blo 1323480 1987613 := bbase (se 3 (by rfl) ⟨372677, by rfl⟩ : syracuseStep 1987613 = 745355) (by norm_num)
theorem B1987637 : Blo 1323480 1987637 := bbase (se 5 (by rfl) ⟨93170, by rfl⟩ : syracuseStep 1987637 = 186341) (by norm_num)
theorem B1987661 : Blo 1323480 1987661 := bbase (se 3 (by rfl) ⟨372686, by rfl⟩ : syracuseStep 1987661 = 745373) (by norm_num)
theorem B2978909 : Blo 1323480 2978909 := bbase (se 3 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 2978909 = 1117091) (by norm_num)
theorem B5657701 : Blo 1323480 5657701 := bbase (se 4 (by rfl) ⟨530409, by rfl⟩ : syracuseStep 5657701 = 1060819) (by norm_num)
theorem B1987685 : Blo 1323480 1987685 := bbase (se 4 (by rfl) ⟨186345, by rfl⟩ : syracuseStep 1987685 = 372691) (by norm_num)
theorem B2233453 : Blo 1323480 2233453 := bbase (se 3 (by rfl) ⟨418772, by rfl⟩ : syracuseStep 2233453 = 837545) (by norm_num)
theorem B1987709 : Blo 1323480 1987709 := bbase (se 3 (by rfl) ⟨372695, by rfl⟩ : syracuseStep 1987709 = 745391) (by norm_num)
theorem B1987733 : Blo 1323480 1987733 := bbase (se 6 (by rfl) ⟨46587, by rfl⟩ : syracuseStep 1987733 = 93175) (by norm_num)
theorem B2978981 : Blo 1323480 2978981 := bbase (se 4 (by rfl) ⟨279279, by rfl⟩ : syracuseStep 2978981 = 558559) (by norm_num)
theorem B1987757 : Blo 1323480 1987757 := bbase (se 3 (by rfl) ⟨372704, by rfl⟩ : syracuseStep 1987757 = 745409) (by norm_num)
theorem B1676477 : Blo 1323480 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B2233541 : Blo 1323480 2233541 := bbase (se 4 (by rfl) ⟨209394, by rfl⟩ : syracuseStep 2233541 = 418789) (by norm_num)
theorem B4469957 : Blo 1323480 4469957 := bbase (se 4 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 4469957 = 838117) (by norm_num)
theorem B1987781 : Blo 1323480 1987781 := bbase (se 4 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 1987781 = 372709) (by norm_num)
theorem B1987805 : Blo 1323480 1987805 := bbase (se 3 (by rfl) ⟨372713, by rfl⟩ : syracuseStep 1987805 = 745427) (by norm_num)
theorem B2979053 : Blo 1323480 2979053 := bbase (se 3 (by rfl) ⟨558572, by rfl⟩ : syracuseStep 2979053 = 1117145) (by norm_num)
theorem B1676533 : Blo 1323480 1676533 := bbase (se 5 (by rfl) ⟨78587, by rfl⟩ : syracuseStep 1676533 = 157175) (by norm_num)
theorem B1987829 : Blo 1323480 1987829 := bbase (se 5 (by rfl) ⟨93179, by rfl⟩ : syracuseStep 1987829 = 186359) (by norm_num)
theorem B1987853 : Blo 1323480 1987853 := bbase (se 3 (by rfl) ⟨372722, by rfl⟩ : syracuseStep 1987853 = 745445) (by norm_num)
theorem B1414417 : Blo 1323480 1414417 := bbase (se 2 (by rfl) ⟨530406, by rfl⟩ : syracuseStep 1414417 = 1060813) (by norm_num)
theorem B5027093 : Blo 1323480 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B14316821 : Blo 1323480 14316821 := bbase (se 6 (by rfl) ⟨335550, by rfl⟩ : syracuseStep 14316821 = 671101) (by norm_num)
theorem B1987877 : Blo 1323480 1987877 := bbase (se 4 (by rfl) ⟨186363, by rfl⟩ : syracuseStep 1987877 = 372727) (by norm_num)
theorem B2979125 : Blo 1323480 2979125 := bbase (se 5 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 2979125 = 279293) (by norm_num)
theorem B3773749 : Blo 1323480 3773749 := bbase (se 5 (by rfl) ⟨176894, by rfl⟩ : syracuseStep 3773749 = 353789) (by norm_num)
theorem B1987901 : Blo 1323480 1987901 := bbase (se 3 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 1987901 = 745463) (by norm_num)
theorem B2233669 : Blo 1323480 2233669 := bbase (se 4 (by rfl) ⟨209406, by rfl⟩ : syracuseStep 2233669 = 418813) (by norm_num)
theorem B1676629 : Blo 1323480 1676629 := bbase (se 14 (by rfl) ⟨153, by rfl⟩ : syracuseStep 1676629 = 307) (by norm_num)
theorem B1987925 : Blo 1323480 1987925 := bbase (se 16 (by rfl) ⟨45, by rfl⟩ : syracuseStep 1987925 = 91) (by norm_num)
theorem B1987949 : Blo 1323480 1987949 := bbase (se 3 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 1987949 = 745481) (by norm_num)
theorem B2979197 : Blo 1323480 2979197 := bbase (se 3 (by rfl) ⟨558599, by rfl⟩ : syracuseStep 2979197 = 1117199) (by norm_num)
theorem B1987973 : Blo 1323480 1987973 := bbase (se 4 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 1987973 = 372745) (by norm_num)
theorem B1414541 : Blo 1323480 1414541 := bbase (se 3 (by rfl) ⟨265226, by rfl⟩ : syracuseStep 1414541 = 530453) (by norm_num)
theorem B2233757 : Blo 1323480 2233757 := bbase (se 3 (by rfl) ⟨418829, by rfl⟩ : syracuseStep 2233757 = 837659) (by norm_num)
theorem B1987997 : Blo 1323480 1987997 := bbase (se 3 (by rfl) ⟨372749, by rfl⟩ : syracuseStep 1987997 = 745499) (by norm_num)
theorem B1988021 : Blo 1323480 1988021 := bbase (se 5 (by rfl) ⟨93188, by rfl⟩ : syracuseStep 1988021 = 186377) (by norm_num)
theorem B2979269 : Blo 1323480 2979269 := bbase (se 4 (by rfl) ⟨279306, by rfl⟩ : syracuseStep 2979269 = 558613) (by norm_num)
theorem B1988045 : Blo 1323480 1988045 := bbase (se 3 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 1988045 = 745517) (by norm_num)
theorem B1988069 : Blo 1323480 1988069 := bbase (se 4 (by rfl) ⟨186381, by rfl⟩ : syracuseStep 1988069 = 372763) (by norm_num)
theorem B1988093 : Blo 1323480 1988093 := bbase (se 3 (by rfl) ⟨372767, by rfl⟩ : syracuseStep 1988093 = 745535) (by norm_num)
theorem B1676801 : Blo 1323480 1676801 := bbase (se 2 (by rfl) ⟨628800, by rfl⟩ : syracuseStep 1676801 = 1257601) (by norm_num)
theorem B2979341 : Blo 1323480 2979341 := bbase (se 3 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 2979341 = 1117253) (by norm_num)
theorem B1988117 : Blo 1323480 1988117 := bbase (se 6 (by rfl) ⟨46596, by rfl⟩ : syracuseStep 1988117 = 93193) (by norm_num)
theorem B2233885 : Blo 1323480 2233885 := bbase (se 3 (by rfl) ⟨418853, by rfl⟩ : syracuseStep 2233885 = 837707) (by norm_num)
theorem B1988141 : Blo 1323480 1988141 := bbase (se 3 (by rfl) ⟨372776, by rfl⟩ : syracuseStep 1988141 = 745553) (by norm_num)
theorem B1676857 : Blo 1323480 1676857 := bbase (se 2 (by rfl) ⟨628821, by rfl⟩ : syracuseStep 1676857 = 1257643) (by norm_num)
theorem B1988165 : Blo 1323480 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B2979413 : Blo 1323480 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B1988189 : Blo 1323480 1988189 := bbase (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) (by norm_num)
theorem B2233973 : Blo 1323480 2233973 := bbase (se 5 (by rfl) ⟨104717, by rfl⟩ : syracuseStep 2233973 = 209435) (by norm_num)
theorem B4470389 : Blo 1323480 4470389 := bbase (se 5 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 4470389 = 419099) (by norm_num)
theorem B1988213 : Blo 1323480 1988213 := bbase (se 5 (by rfl) ⟨93197, by rfl⟩ : syracuseStep 1988213 = 186395) (by norm_num)
theorem B1414793 : Blo 1323480 1414793 := bbase (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) (by norm_num)
theorem B1676953 : Blo 1323480 1676953 := bbase (se 2 (by rfl) ⟨628857, by rfl⟩ : syracuseStep 1676953 = 1257715) (by norm_num)
theorem B2979485 : Blo 1323480 2979485 := bbase (se 3 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 2979485 = 1117307) (by norm_num)
theorem B2512613 : Blo 1323480 2512613 := bbase (se 4 (by rfl) ⟨235557, by rfl⟩ : syracuseStep 2512613 = 471115) (by norm_num)
theorem B2979557 : Blo 1323480 2979557 := bbase (se 4 (by rfl) ⟨279333, by rfl⟩ : syracuseStep 2979557 = 558667) (by norm_num)
theorem B2234101 : Blo 1323480 2234101 := bbase (se 5 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 2234101 = 209447) (by norm_num)
theorem B2979629 : Blo 1323480 2979629 := bbase (se 3 (by rfl) ⟨558680, by rfl⟩ : syracuseStep 2979629 = 1117361) (by norm_num)
theorem B5658437 : Blo 1323480 5658437 := bbase (se 4 (by rfl) ⟨530478, by rfl⟩ : syracuseStep 5658437 = 1060957) (by norm_num)
theorem B1677125 : Blo 1323480 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B2234189 : Blo 1323480 2234189 := bbase (se 3 (by rfl) ⟨418910, by rfl⟩ : syracuseStep 2234189 = 837821) (by norm_num)
theorem B2512757 : Blo 1323480 2512757 := bbase (se 5 (by rfl) ⟨117785, by rfl⟩ : syracuseStep 2512757 = 235571) (by norm_num)
theorem B2979701 : Blo 1323480 2979701 := bbase (se 5 (by rfl) ⟨139673, by rfl⟩ : syracuseStep 2979701 = 279347) (by norm_num)
theorem B1677181 : Blo 1323480 1677181 := bbase (se 3 (by rfl) ⟨314471, by rfl⟩ : syracuseStep 1677181 = 628943) (by norm_num)
theorem B2979773 : Blo 1323480 2979773 := bbase (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) (by norm_num)
theorem B2234317 : Blo 1323480 2234317 := bbase (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) (by norm_num)
theorem B1677277 : Blo 1323480 1677277 := bbase (se 3 (by rfl) ⟨314489, by rfl⟩ : syracuseStep 1677277 = 628979) (by norm_num)
theorem B2979845 : Blo 1323480 2979845 := bbase (se 4 (by rfl) ⟨279360, by rfl⟩ : syracuseStep 2979845 = 558721) (by norm_num)
theorem B2234405 : Blo 1323480 2234405 := bbase (se 4 (by rfl) ⟨209475, by rfl⟩ : syracuseStep 2234405 = 418951) (by norm_num)
theorem B4470821 : Blo 1323480 4470821 := bbase (se 4 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 4470821 = 838279) (by norm_num)
theorem B1488937 : Blo 1323480 1488937 := bbase (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) (by norm_num)
theorem B1415237 : Blo 1323480 1415237 := bbase (se 4 (by rfl) ⟨132678, by rfl⟩ : syracuseStep 1415237 = 265357) (by norm_num)
theorem B1488973 : Blo 1323480 1488973 := bbase (se 3 (by rfl) ⟨279182, by rfl⟩ : syracuseStep 1488973 = 558365) (by norm_num)
theorem B2979917 : Blo 1323480 2979917 := bbase (se 3 (by rfl) ⟨558734, by rfl⟩ : syracuseStep 2979917 = 1117469) (by norm_num)
theorem B3184717 : Blo 1323480 3184717 := bbase (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) (by norm_num)
theorem B18118741 : Blo 1323480 18118741 := bbase (se 8 (by rfl) ⟨106164, by rfl⟩ : syracuseStep 18118741 = 212329) (by norm_num)
theorem B19093589 : Blo 1323480 19093589 := bbase (se 8 (by rfl) ⟨111876, by rfl⟩ : syracuseStep 19093589 = 223753) (by norm_num)
theorem B6707285 : Blo 1323480 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B1489009 : Blo 1323480 1489009 := bbase (se 2 (by rfl) ⟨558378, by rfl⟩ : syracuseStep 1489009 = 1116757) (by norm_num)
theorem B1677449 : Blo 1323480 1677449 := bbase (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) (by norm_num)
theorem B1489045 : Blo 1323480 1489045 := bbase (se 6 (by rfl) ⟨34899, by rfl⟩ : syracuseStep 1489045 = 69799) (by norm_num)
theorem B2513045 : Blo 1323480 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B8485013 : Blo 1323480 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B2979989 : Blo 1323480 2979989 := bbase (se 6 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 2979989 = 139687) (by norm_num)
theorem B2234533 : Blo 1323480 2234533 := bbase (se 4 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 2234533 = 418975) (by norm_num)
theorem B1489081 : Blo 1323480 1489081 := bbase (se 2 (by rfl) ⟨558405, by rfl⟩ : syracuseStep 1489081 = 1116811) (by norm_num)
theorem B1677505 : Blo 1323480 1677505 := bbase (se 2 (by rfl) ⟨629064, by rfl⟩ : syracuseStep 1677505 = 1258129) (by norm_num)
theorem B1489117 : Blo 1323480 1489117 := bbase (se 3 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 1489117 = 558419) (by norm_num)
theorem B2980061 : Blo 1323480 2980061 := bbase (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) (by norm_num)
theorem B2234621 : Blo 1323480 2234621 := bbase (se 3 (by rfl) ⟨418991, by rfl⟩ : syracuseStep 2234621 = 837983) (by norm_num)
theorem B1489153 : Blo 1323480 1489153 := bbase (se 2 (by rfl) ⟨558432, by rfl⟩ : syracuseStep 1489153 = 1116865) (by norm_num)
theorem B1489189 : Blo 1323480 1489189 := bbase (se 4 (by rfl) ⟨139611, by rfl⟩ : syracuseStep 1489189 = 279223) (by norm_num)
theorem B2980133 : Blo 1323480 2980133 := bbase (se 4 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 2980133 = 558775) (by norm_num)
theorem B2513197 : Blo 1323480 2513197 := bbase (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) (by norm_num)
theorem B1489225 : Blo 1323480 1489225 := bbase (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) (by norm_num)
theorem B1489261 : Blo 1323480 1489261 := bbase (se 3 (by rfl) ⟨279236, by rfl⟩ : syracuseStep 1489261 = 558473) (by norm_num)
theorem B2980205 : Blo 1323480 2980205 := bbase (se 3 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 2980205 = 1117577) (by norm_num)
theorem B2234749 : Blo 1323480 2234749 := bbase (se 3 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 2234749 = 838031) (by norm_num)
theorem B2120069 : Blo 1323480 2120069 := bbase (se 4 (by rfl) ⟨198756, by rfl⟩ : syracuseStep 2120069 = 397513) (by norm_num)
theorem B1489297 : Blo 1323480 1489297 := bbase (se 2 (by rfl) ⟨558486, by rfl⟩ : syracuseStep 1489297 = 1116973) (by norm_num)
theorem B1489333 : Blo 1323480 1489333 := bbase (se 5 (by rfl) ⟨69812, by rfl⟩ : syracuseStep 1489333 = 139625) (by norm_num)
theorem B5028277 : Blo 1323480 5028277 := bbase (se 5 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 5028277 = 471401) (by norm_num)
theorem B2980277 : Blo 1323480 2980277 := bbase (se 5 (by rfl) ⟨139700, by rfl⟩ : syracuseStep 2980277 = 279401) (by norm_num)
theorem B3578309 : Blo 1323480 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B2234837 : Blo 1323480 2234837 := bbase (se 7 (by rfl) ⟨26189, by rfl⟩ : syracuseStep 2234837 = 52379) (by norm_num)
theorem B4471253 : Blo 1323480 4471253 := bbase (se 7 (by rfl) ⟨52397, by rfl⟩ : syracuseStep 4471253 = 104795) (by norm_num)
theorem B1489369 : Blo 1323480 1489369 := bbase (se 2 (by rfl) ⟨558513, by rfl⟩ : syracuseStep 1489369 = 1117027) (by norm_num)
theorem B1489405 : Blo 1323480 1489405 := bbase (se 3 (by rfl) ⟨279263, by rfl⟩ : syracuseStep 1489405 = 558527) (by norm_num)
theorem B2980349 : Blo 1323480 2980349 := bbase (se 3 (by rfl) ⟨558815, by rfl⟩ : syracuseStep 2980349 = 1117631) (by norm_num)
theorem B1489441 : Blo 1323480 1489441 := bbase (se 2 (by rfl) ⟨558540, by rfl⟩ : syracuseStep 1489441 = 1117081) (by norm_num)
theorem B1489477 : Blo 1323480 1489477 := bbase (se 4 (by rfl) ⟨139638, by rfl⟩ : syracuseStep 1489477 = 279277) (by norm_num)
theorem B2980421 : Blo 1323480 2980421 := bbase (se 4 (by rfl) ⟨279414, by rfl⟩ : syracuseStep 2980421 = 558829) (by norm_num)
theorem B2234965 : Blo 1323480 2234965 := bbase (se 8 (by rfl) ⟨13095, by rfl⟩ : syracuseStep 2234965 = 26191) (by norm_num)
theorem B2513501 : Blo 1323480 2513501 := bbase (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) (by norm_num)
theorem B2120293 : Blo 1323480 2120293 := bbase (se 4 (by rfl) ⟨198777, by rfl⟩ : syracuseStep 2120293 = 397555) (by norm_num)
theorem B1489513 : Blo 1323480 1489513 := bbase (se 2 (by rfl) ⟨558567, by rfl⟩ : syracuseStep 1489513 = 1117135) (by norm_num)
theorem B1489549 : Blo 1323480 1489549 := bbase (se 3 (by rfl) ⟨279290, by rfl⟩ : syracuseStep 1489549 = 558581) (by norm_num)
theorem B2980493 : Blo 1323480 2980493 := bbase (se 3 (by rfl) ⟨558842, by rfl⟩ : syracuseStep 2980493 = 1117685) (by norm_num)
theorem B2120357 : Blo 1323480 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2235053 : Blo 1323480 2235053 := bbase (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) (by norm_num)
theorem B1489585 : Blo 1323480 1489585 := bbase (se 2 (by rfl) ⟨558594, by rfl⟩ : syracuseStep 1489585 = 1117189) (by norm_num)
theorem B1489621 : Blo 1323480 1489621 := bbase (se 7 (by rfl) ⟨17456, by rfl⟩ : syracuseStep 1489621 = 34913) (by norm_num)
theorem B2980565 : Blo 1323480 2980565 := bbase (se 7 (by rfl) ⟨34928, by rfl⟩ : syracuseStep 2980565 = 69857) (by norm_num)
theorem B5028581 : Blo 1323480 5028581 := bbase (se 4 (by rfl) ⟨471429, by rfl⟩ : syracuseStep 5028581 = 942859) (by norm_num)
theorem B1489657 : Blo 1323480 1489657 := bbase (se 2 (by rfl) ⟨558621, by rfl⟩ : syracuseStep 1489657 = 1117243) (by norm_num)
theorem B1489693 : Blo 1323480 1489693 := bbase (se 3 (by rfl) ⟨279317, by rfl⟩ : syracuseStep 1489693 = 558635) (by norm_num)
theorem B2980637 : Blo 1323480 2980637 := bbase (se 3 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 2980637 = 1117739) (by norm_num)
theorem B2120485 : Blo 1323480 2120485 := bbase (se 4 (by rfl) ⟨198795, by rfl⟩ : syracuseStep 2120485 = 397591) (by norm_num)
theorem B2235181 : Blo 1323480 2235181 := bbase (se 3 (by rfl) ⟨419096, by rfl⟩ : syracuseStep 2235181 = 838193) (by norm_num)
theorem B2013997 : Blo 1323480 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B1489729 : Blo 1323480 1489729 := bbase (se 2 (by rfl) ⟨558648, by rfl⟩ : syracuseStep 1489729 = 1117297) (by norm_num)
theorem B1489765 : Blo 1323480 1489765 := bbase (se 4 (by rfl) ⟨139665, by rfl⟩ : syracuseStep 1489765 = 279331) (by norm_num)
theorem B2980709 : Blo 1323480 2980709 := bbase (se 4 (by rfl) ⟨279441, by rfl⟩ : syracuseStep 2980709 = 558883) (by norm_num)
theorem B2235269 : Blo 1323480 2235269 := bbase (se 4 (by rfl) ⟨209556, by rfl⟩ : syracuseStep 2235269 = 419113) (by norm_num)
theorem B4471685 : Blo 1323480 4471685 := bbase (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) (by norm_num)
theorem B1489801 : Blo 1323480 1489801 := bbase (se 2 (by rfl) ⟨558675, by rfl⟩ : syracuseStep 1489801 = 1117351) (by norm_num)
theorem B1489837 : Blo 1323480 1489837 := bbase (se 3 (by rfl) ⟨279344, by rfl⟩ : syracuseStep 1489837 = 558689) (by norm_num)
theorem B2980781 : Blo 1323480 2980781 := bbase (se 3 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 2980781 = 1117793) (by norm_num)
theorem B5733301 : Blo 1323480 5733301 := bbase (se 5 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 5733301 = 537497) (by norm_num)
theorem B1489873 : Blo 1323480 1489873 := bbase (se 2 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 1489873 = 1117405) (by norm_num)
theorem B1489909 : Blo 1323480 1489909 := bbase (se 5 (by rfl) ⟨69839, by rfl⟩ : syracuseStep 1489909 = 139679) (by norm_num)
theorem B10058741 : Blo 1323480 10058741 := bbase (se 5 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 10058741 = 943007) (by norm_num)
theorem B2980853 : Blo 1323480 2980853 := bbase (se 5 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 2980853 = 279455) (by norm_num)
theorem B2235397 : Blo 1323480 2235397 := bbase (se 4 (by rfl) ⟨209568, by rfl⟩ : syracuseStep 2235397 = 419137) (by norm_num)
theorem B1489945 : Blo 1323480 1489945 := bbase (se 2 (by rfl) ⟨558729, by rfl⟩ : syracuseStep 1489945 = 1117459) (by norm_num)
theorem B6454325 : Blo 1323480 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B1489981 : Blo 1323480 1489981 := bbase (se 3 (by rfl) ⟨279371, by rfl⟩ : syracuseStep 1489981 = 558743) (by norm_num)
theorem B2980925 : Blo 1323480 2980925 := bbase (se 3 (by rfl) ⟨558923, by rfl⟩ : syracuseStep 2980925 = 1117847) (by norm_num)
theorem B2235485 : Blo 1323480 2235485 := bbase (se 3 (by rfl) ⟨419153, by rfl⟩ : syracuseStep 2235485 = 838307) (by norm_num)
theorem B1490017 : Blo 1323480 1490017 := bbase (se 2 (by rfl) ⟨558756, by rfl⟩ : syracuseStep 1490017 = 1117513) (by norm_num)
theorem B6364261 : Blo 1323480 6364261 := bbase (se 4 (by rfl) ⟨596649, by rfl⟩ : syracuseStep 6364261 = 1193299) (by norm_num)
theorem B1490053 : Blo 1323480 1490053 := bbase (se 4 (by rfl) ⟨139692, by rfl⟩ : syracuseStep 1490053 = 279385) (by norm_num)
theorem B2980997 : Blo 1323480 2980997 := bbase (se 4 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 2980997 = 558937) (by norm_num)
theorem B4299925 : Blo 1323480 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B1432733 : Blo 1323480 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B1490089 : Blo 1323480 1490089 := bbase (se 2 (by rfl) ⟨558783, by rfl⟩ : syracuseStep 1490089 = 1117567) (by norm_num)
theorem B1490125 : Blo 1323480 1490125 := bbase (se 3 (by rfl) ⟨279398, by rfl⟩ : syracuseStep 1490125 = 558797) (by norm_num)
theorem B2981069 : Blo 1323480 2981069 := bbase (se 3 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 2981069 = 1117901) (by norm_num)
theorem B2235613 : Blo 1323480 2235613 := bbase (se 3 (by rfl) ⟨419177, by rfl⟩ : syracuseStep 2235613 = 838355) (by norm_num)
theorem B1490161 : Blo 1323480 1490161 := bbase (se 2 (by rfl) ⟨558810, by rfl⟩ : syracuseStep 1490161 = 1117621) (by norm_num)
theorem B1490197 : Blo 1323480 1490197 := bbase (se 6 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 1490197 = 69853) (by norm_num)
theorem B2981141 : Blo 1323480 2981141 := bbase (se 6 (by rfl) ⟨69870, by rfl⟩ : syracuseStep 2981141 = 139741) (by norm_num)
theorem B2235701 : Blo 1323480 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B4472117 : Blo 1323480 4472117 := bbase (se 5 (by rfl) ⟨209630, by rfl⟩ : syracuseStep 4472117 = 419261) (by norm_num)
theorem B1490233 : Blo 1323480 1490233 := bbase (se 2 (by rfl) ⟨558837, by rfl⟩ : syracuseStep 1490233 = 1117675) (by norm_num)
theorem B1432909 : Blo 1323480 1432909 := bbase (se 3 (by rfl) ⟨268670, by rfl⟩ : syracuseStep 1432909 = 537341) (by norm_num)
theorem B2514253 : Blo 1323480 2514253 := bbase (se 3 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 2514253 = 942845) (by norm_num)
theorem B1490269 : Blo 1323480 1490269 := bbase (se 3 (by rfl) ⟨279425, by rfl⟩ : syracuseStep 1490269 = 558851) (by norm_num)
theorem B2981213 : Blo 1323480 2981213 := bbase (se 3 (by rfl) ⟨558977, by rfl⟩ : syracuseStep 2981213 = 1117955) (by norm_num)
theorem B6708581 : Blo 1323480 6708581 := bbase (se 4 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 6708581 = 1257859) (by norm_num)
theorem B1490305 : Blo 1323480 1490305 := bbase (se 2 (by rfl) ⟨558864, by rfl⟩ : syracuseStep 1490305 = 1117729) (by norm_num)
theorem B10050965 : Blo 1323480 10050965 := bbase (se 6 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 10050965 = 471139) (by norm_num)
theorem B1490341 : Blo 1323480 1490341 := bbase (se 4 (by rfl) ⟨139719, by rfl⟩ : syracuseStep 1490341 = 279439) (by norm_num)
theorem B2981285 : Blo 1323480 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B2235829 : Blo 1323480 2235829 := bbase (se 5 (by rfl) ⟨104804, by rfl⟩ : syracuseStep 2235829 = 209609) (by norm_num)
theorem B1490377 : Blo 1323480 1490377 := bbase (se 2 (by rfl) ⟨558891, by rfl⟩ : syracuseStep 1490377 = 1117783) (by norm_num)
theorem B2514397 : Blo 1323480 2514397 := bbase (se 3 (by rfl) ⟨471449, by rfl⟩ : syracuseStep 2514397 = 942899) (by norm_num)
theorem B4242917 : Blo 1323480 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B3022309 : Blo 1323480 3022309 := bbase (se 4 (by rfl) ⟨283341, by rfl⟩ : syracuseStep 3022309 = 566683) (by norm_num)
theorem B1490413 : Blo 1323480 1490413 := bbase (se 3 (by rfl) ⟨279452, by rfl⟩ : syracuseStep 1490413 = 558905) (by norm_num)
theorem B2981357 : Blo 1323480 2981357 := bbase (se 3 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 2981357 = 1118009) (by norm_num)
theorem B2235917 : Blo 1323480 2235917 := bbase (se 3 (by rfl) ⟨419234, by rfl⟩ : syracuseStep 2235917 = 838469) (by norm_num)
theorem B1490449 : Blo 1323480 1490449 := bbase (se 2 (by rfl) ⟨558918, by rfl⟩ : syracuseStep 1490449 = 1117837) (by norm_num)
theorem B3350069 : Blo 1323480 3350069 := bbase (se 5 (by rfl) ⟨157034, by rfl⟩ : syracuseStep 3350069 = 314069) (by norm_num)
theorem B1490485 : Blo 1323480 1490485 := bbase (se 5 (by rfl) ⟨69866, by rfl⟩ : syracuseStep 1490485 = 139733) (by norm_num)
theorem B2981429 : Blo 1323480 2981429 := bbase (se 5 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 2981429 = 279509) (by norm_num)
theorem B1490521 : Blo 1323480 1490521 := bbase (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) (by norm_num)
theorem B2514557 : Blo 1323480 2514557 := bbase (se 3 (by rfl) ⟨471479, by rfl⟩ : syracuseStep 2514557 = 942959) (by norm_num)
theorem B1490557 : Blo 1323480 1490557 := bbase (se 3 (by rfl) ⟨279479, by rfl⟩ : syracuseStep 1490557 = 558959) (by norm_num)
theorem B2981501 : Blo 1323480 2981501 := bbase (se 3 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 2981501 = 1118063) (by norm_num)
theorem B2236045 : Blo 1323480 2236045 := bbase (se 3 (by rfl) ⟨419258, by rfl⟩ : syracuseStep 2236045 = 838517) (by norm_num)
theorem B1490593 : Blo 1323480 1490593 := bbase (se 2 (by rfl) ⟨558972, by rfl⟩ : syracuseStep 1490593 = 1117945) (by norm_num)
theorem B4030133 : Blo 1323480 4030133 := bbase (se 5 (by rfl) ⟨188912, by rfl⟩ : syracuseStep 4030133 = 377825) (by norm_num)
theorem B1490629 : Blo 1323480 1490629 := bbase (se 4 (by rfl) ⟨139746, by rfl⟩ : syracuseStep 1490629 = 279493) (by norm_num)
theorem B2981573 : Blo 1323480 2981573 := bbase (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) (by norm_num)
theorem B2236133 : Blo 1323480 2236133 := bbase (se 4 (by rfl) ⟨209637, by rfl⟩ : syracuseStep 2236133 = 419275) (by norm_num)
theorem B4472549 : Blo 1323480 4472549 := bbase (se 4 (by rfl) ⟨419301, by rfl⟩ : syracuseStep 4472549 = 838603) (by norm_num)
theorem B1490665 : Blo 1323480 1490665 := bbase (se 2 (by rfl) ⟨558999, by rfl⟩ : syracuseStep 1490665 = 1117999) (by norm_num)
theorem B3350261 : Blo 1323480 3350261 := bbase (se 5 (by rfl) ⟨157043, by rfl⟩ : syracuseStep 3350261 = 314087) (by norm_num)
theorem B3399421 : Blo 1323480 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B6700805 : Blo 1323480 6700805 := bbase (se 4 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 6700805 = 1256401) (by norm_num)
theorem B2514701 : Blo 1323480 2514701 := bbase (se 3 (by rfl) ⟨471506, by rfl⟩ : syracuseStep 2514701 = 943013) (by norm_num)
theorem B1490701 : Blo 1323480 1490701 := bbase (se 3 (by rfl) ⟨279506, by rfl⟩ : syracuseStep 1490701 = 559013) (by norm_num)
theorem B2981645 : Blo 1323480 2981645 := bbase (se 3 (by rfl) ⟨559058, by rfl⟩ : syracuseStep 2981645 = 1118117) (by norm_num)
theorem B1490737 : Blo 1323480 1490737 := bbase (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) (by norm_num)
theorem B2686781 : Blo 1323480 2686781 := bbase (se 3 (by rfl) ⟨503771, by rfl⟩ : syracuseStep 2686781 = 1007543) (by norm_num)
theorem B1490773 : Blo 1323480 1490773 := bbase (se 9 (by rfl) ⟨4367, by rfl⟩ : syracuseStep 1490773 = 8735) (by norm_num)
theorem B2981717 : Blo 1323480 2981717 := bbase (se 9 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 2981717 = 17471) (by norm_num)
theorem B2236261 : Blo 1323480 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1490809 : Blo 1323480 1490809 := bbase (se 2 (by rfl) ⟨559053, by rfl⟩ : syracuseStep 1490809 = 1118107) (by norm_num)
theorem B1490845 : Blo 1323480 1490845 := bbase (se 3 (by rfl) ⟨279533, by rfl⟩ : syracuseStep 1490845 = 559067) (by norm_num)
theorem B2981789 : Blo 1323480 2981789 := bbase (se 3 (by rfl) ⟨559085, by rfl⟩ : syracuseStep 2981789 = 1118171) (by norm_num)
theorem B2236349 : Blo 1323480 2236349 := bbase (se 3 (by rfl) ⟨419315, by rfl⟩ : syracuseStep 2236349 = 838631) (by norm_num)
theorem B1490881 : Blo 1323480 1490881 := bbase (se 2 (by rfl) ⟨559080, by rfl⟩ : syracuseStep 1490881 = 1118161) (by norm_num)
theorem B2015189 : Blo 1323480 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B1490917 : Blo 1323480 1490917 := bbase (se 4 (by rfl) ⟨139773, by rfl⟩ : syracuseStep 1490917 = 279547) (by norm_num)
theorem B2981861 : Blo 1323480 2981861 := bbase (se 4 (by rfl) ⟨279549, by rfl⟩ : syracuseStep 2981861 = 559099) (by norm_num)
theorem B2121709 : Blo 1323480 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B4030499 : Blo 1323480 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B2981969 : Blo 1323480 2981969 := bstep (se 2 (by rfl) ⟨1118238, by rfl⟩ : syracuseStep 2981969 = 2236477) B2236477
theorem B2515043 : Blo 1323480 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B2981987 : Blo 1323480 2981987 := bstep (se 1 (by rfl) ⟨2236490, by rfl⟩ : syracuseStep 2981987 = 4472981) B4472981
theorem B1491043 : Blo 1323480 1491043 := bstep (se 1 (by rfl) ⟨1118282, by rfl⟩ : syracuseStep 1491043 = 2236565) B2236565
theorem B4030573 : Blo 1323480 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B24158321 : Blo 1323480 24158321 := bstep (se 2 (by rfl) ⟨9059370, by rfl⟩ : syracuseStep 24158321 = 18118741) B18118741
theorem B2236531 : Blo 1323480 2236531 := bstep (se 1 (by rfl) ⟨1677398, by rfl⟩ : syracuseStep 2236531 = 3354797) B3354797
theorem B4243661 : Blo 1323480 4243661 := bstep (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) B1591373
theorem B7545059 : Blo 1323480 7545059 := bstep (se 1 (by rfl) ⟨5658794, by rfl⟩ : syracuseStep 7545059 = 11317589) B11317589
theorem B2121971 : Blo 1323480 2121971 := bstep (se 1 (by rfl) ⟨1591478, by rfl⟩ : syracuseStep 2121971 = 3182957) B3182957
theorem B2236673 : Blo 1323480 2236673 := bstep (se 2 (by rfl) ⟨838752, by rfl⟩ : syracuseStep 2236673 = 1677505) B1677505
theorem B6709553 : Blo 1323480 6709553 := bstep (se 2 (by rfl) ⟨2516082, by rfl⟩ : syracuseStep 6709553 = 5032165) B5032165
theorem B5030221 : Blo 1323480 5030221 := bstep (se 3 (by rfl) ⟨943166, by rfl⟩ : syracuseStep 5030221 = 1886333) B1886333
theorem B4473197 : Blo 1323480 4473197 := bstep (se 3 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 4473197 = 1677449) B1677449
theorem B2982257 : Blo 1323480 2982257 := bstep (se 2 (by rfl) ⟨1118346, by rfl⟩ : syracuseStep 2982257 = 2236693) B2236693
theorem B2982275 : Blo 1323480 2982275 := bstep (se 1 (by rfl) ⟨2236706, by rfl⟩ : syracuseStep 2982275 = 4473413) B4473413
theorem B6701453 : Blo 1323480 6701453 := bstep (se 3 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 6701453 = 2513045) B2513045
theorem B22626701 : Blo 1323480 22626701 := bstep (se 3 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 22626701 = 8485013) B8485013
theorem B3350929 : Blo 1323480 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B4473251 : Blo 1323480 4473251 := bstep (se 1 (by rfl) ⟨3354938, by rfl⟩ : syracuseStep 4473251 = 6709877) B6709877
theorem B15295075 : Blo 1323480 15295075 := bstep (se 1 (by rfl) ⟨11471306, by rfl⟩ : syracuseStep 15295075 = 22942613) B22942613
theorem B3351203 : Blo 1323480 3351203 := bstep (se 1 (by rfl) ⟨2513402, by rfl⟩ : syracuseStep 3351203 = 5026805) B5026805
theorem B2122433 : Blo 1323480 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B51602197 : Blo 1323480 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B1884961 : Blo 1323480 1884961 := bstep (se 2 (by rfl) ⟨706860, by rfl⟩ : syracuseStep 1884961 = 1413721) B1413721
theorem B2122529 : Blo 1323480 2122529 := bstep (se 2 (by rfl) ⟨795948, by rfl⟩ : syracuseStep 2122529 = 1591897) B1591897
theorem B2827057 : Blo 1323480 2827057 := bstep (se 2 (by rfl) ⟨1060146, by rfl⟩ : syracuseStep 2827057 = 2120293) B2120293
theorem B2122561 : Blo 1323480 2122561 := bstep (se 2 (by rfl) ⟨795960, by rfl⟩ : syracuseStep 2122561 = 1591921) B1591921
theorem B3351395 : Blo 1323480 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B9544547 : Blo 1323480 9544547 := bstep (se 1 (by rfl) ⟨7158410, by rfl⟩ : syracuseStep 9544547 = 14316821) B14316821
theorem B18121585 : Blo 1323480 18121585 := bstep (se 2 (by rfl) ⟨6795594, by rfl⟩ : syracuseStep 18121585 = 13591189) B13591189
theorem B10060685 : Blo 1323480 10060685 := bstep (se 3 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 10060685 = 3772757) B3772757
theorem B2827313 : Blo 1323480 2827313 := bstep (se 2 (by rfl) ⟨1060242, by rfl⟩ : syracuseStep 2827313 = 2120485) B2120485
theorem B4244557 : Blo 1323480 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B16974947 : Blo 1323480 16974947 := bstep (se 1 (by rfl) ⟨12731210, by rfl⟩ : syracuseStep 16974947 = 25462421) B25462421
theorem B5031011 : Blo 1323480 5031011 := bstep (se 1 (by rfl) ⟨3773258, by rfl⟩ : syracuseStep 5031011 = 7546517) B7546517
theorem B1885297 : Blo 1323480 1885297 := bstep (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) B1413973
theorem B2516113 : Blo 1323480 2516113 := bstep (se 2 (by rfl) ⟨943542, by rfl⟩ : syracuseStep 2516113 = 1887085) B1887085
theorem B7546061 : Blo 1323480 7546061 := bstep (se 3 (by rfl) ⟨1414886, by rfl⟩ : syracuseStep 7546061 = 2829773) B2829773
theorem B7644401 : Blo 1323480 7644401 := bstep (se 2 (by rfl) ⟨2866650, by rfl⟩ : syracuseStep 7644401 = 5733301) B5733301
theorem B3769649 : Blo 1323480 3769649 := bstep (se 2 (by rfl) ⟨1413618, by rfl⟩ : syracuseStep 3769649 = 2827237) B2827237
theorem B1721683 : Blo 1323480 1721683 := bstep (se 1 (by rfl) ⟨1291262, by rfl⟩ : syracuseStep 1721683 = 2582525) B2582525
theorem B1590691 : Blo 1323480 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B3769841 : Blo 1323480 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B1590835 : Blo 1323480 1590835 := bstep (se 1 (by rfl) ⟨1193126, by rfl⟩ : syracuseStep 1590835 = 2386253) B2386253
theorem B3180113 : Blo 1323480 3180113 := bstep (se 2 (by rfl) ⟨1192542, by rfl⟩ : syracuseStep 3180113 = 2385085) B2385085
theorem B2385539 : Blo 1323480 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1885889 : Blo 1323480 1885889 := bstep (se 2 (by rfl) ⟨707208, by rfl⟩ : syracuseStep 1885889 = 1414417) B1414417
theorem B5031665 : Blo 1323480 5031665 := bstep (se 2 (by rfl) ⟨1886874, by rfl⟩ : syracuseStep 5031665 = 3773749) B3773749
theorem B5654285 : Blo 1323480 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B3180305 : Blo 1323480 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B3352337 : Blo 1323480 3352337 := bstep (se 2 (by rfl) ⟨1257126, by rfl⟩ : syracuseStep 3352337 = 2514253) B2514253
theorem B3352387 : Blo 1323480 3352387 := bstep (se 1 (by rfl) ⟨2514290, by rfl⟩ : syracuseStep 3352387 = 5028581) B5028581
theorem B3352529 : Blo 1323480 3352529 := bstep (se 2 (by rfl) ⟨1257198, by rfl⟩ : syracuseStep 3352529 = 2514397) B2514397
theorem B4302883 : Blo 1323480 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B3180593 : Blo 1323480 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B4245635 : Blo 1323480 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B1886419 : Blo 1323480 1886419 := bstep (se 1 (by rfl) ⟨1414814, by rfl⟩ : syracuseStep 1886419 = 2829629) B2829629
theorem B2828611 : Blo 1323480 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B4532561 : Blo 1323480 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B4467149 : Blo 1323480 4467149 := bstep (se 3 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 4467149 = 1675181) B1675181
theorem B3770833 : Blo 1323480 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B4467203 : Blo 1323480 4467203 := bstep (se 1 (by rfl) ⟨3350402, by rfl⟩ : syracuseStep 4467203 = 6700805) B6700805
theorem B1886755 : Blo 1323480 1886755 := bstep (se 1 (by rfl) ⟨1415066, by rfl⟩ : syracuseStep 1886755 = 2830133) B2830133
theorem B1591859 : Blo 1323480 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B68774453 : Blo 1323480 68774453 := bstep (se 5 (by rfl) ⟨3223802, by rfl⟩ : syracuseStep 68774453 = 6447605) B6447605
theorem B2828945 : Blo 1323480 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B1985249 : Blo 1323480 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B3771107 : Blo 1323480 3771107 := bstep (se 1 (by rfl) ⟨2828330, by rfl⟩ : syracuseStep 3771107 = 5656661) B5656661
theorem B1985267 : Blo 1323480 1985267 := bstep (se 1 (by rfl) ⟨1488950, by rfl⟩ : syracuseStep 1985267 = 2977901) B2977901
theorem B1985297 : Blo 1323480 1985297 := bstep (se 2 (by rfl) ⟨744486, by rfl⟩ : syracuseStep 1985297 = 1488973) B1488973
theorem B4467473 : Blo 1323480 4467473 := bstep (se 2 (by rfl) ⟨1675302, by rfl⟩ : syracuseStep 4467473 = 3350605) B3350605
theorem B4246289 : Blo 1323480 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B1985315 : Blo 1323480 1985315 := bstep (se 1 (by rfl) ⟨1488986, by rfl⟩ : syracuseStep 1985315 = 2977973) B2977973
theorem B2263859 : Blo 1323480 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B1985345 : Blo 1323480 1985345 := bstep (se 2 (by rfl) ⟨744504, by rfl⟩ : syracuseStep 1985345 = 1489009) B1489009
theorem B1985363 : Blo 1323480 1985363 := bstep (se 1 (by rfl) ⟨1489022, by rfl⟩ : syracuseStep 1985363 = 2978045) B2978045
theorem B1985393 : Blo 1323480 1985393 := bstep (se 2 (by rfl) ⟨744522, by rfl⟩ : syracuseStep 1985393 = 1489045) B1489045
theorem B27200369 : Blo 1323480 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1985411 : Blo 1323480 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B4025219 : Blo 1323480 4025219 := bstep (se 1 (by rfl) ⟨3018914, by rfl⟩ : syracuseStep 4025219 = 6037829) B6037829
theorem B1985441 : Blo 1323480 1985441 := bstep (se 2 (by rfl) ⟨744540, by rfl⟩ : syracuseStep 1985441 = 1489081) B1489081
theorem B3771299 : Blo 1323480 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B3353521 : Blo 1323480 3353521 := bstep (se 2 (by rfl) ⟨1257570, by rfl⟩ : syracuseStep 3353521 = 2515141) B2515141
theorem B1985459 : Blo 1323480 1985459 := bstep (se 1 (by rfl) ⟨1489094, by rfl⟩ : syracuseStep 1985459 = 2978189) B2978189
theorem B4303811 : Blo 1323480 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B1985489 : Blo 1323480 1985489 := bstep (se 2 (by rfl) ⟨744558, by rfl⟩ : syracuseStep 1985489 = 1489117) B1489117
theorem B1985507 : Blo 1323480 1985507 := bstep (se 1 (by rfl) ⟨1489130, by rfl⟩ : syracuseStep 1985507 = 2978261) B2978261
theorem B1985537 : Blo 1323480 1985537 := bstep (se 2 (by rfl) ⟨744576, by rfl⟩ : syracuseStep 1985537 = 1489153) B1489153
theorem B1985555 : Blo 1323480 1985555 := bstep (se 1 (by rfl) ⟨1489166, by rfl⟩ : syracuseStep 1985555 = 2978333) B2978333
theorem B2583587 : Blo 1323480 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B1985585 : Blo 1323480 1985585 := bstep (se 2 (by rfl) ⟨744594, by rfl⟩ : syracuseStep 1985585 = 1489189) B1489189
theorem B1985603 : Blo 1323480 1985603 := bstep (se 1 (by rfl) ⟨1489202, by rfl⟩ : syracuseStep 1985603 = 2978405) B2978405
theorem B3820621 : Blo 1323480 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1985633 : Blo 1323480 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B1985651 : Blo 1323480 1985651 := bstep (se 1 (by rfl) ⟨1489238, by rfl⟩ : syracuseStep 1985651 = 2978477) B2978477
theorem B1985681 : Blo 1323480 1985681 := bstep (se 2 (by rfl) ⟨744630, by rfl⟩ : syracuseStep 1985681 = 1489261) B1489261
theorem B1985699 : Blo 1323480 1985699 := bstep (se 1 (by rfl) ⟨1489274, by rfl⟩ : syracuseStep 1985699 = 2978549) B2978549
theorem B8604835 : Blo 1323480 8604835 := bstep (se 1 (by rfl) ⟨6453626, by rfl⟩ : syracuseStep 8604835 = 12907253) B12907253
theorem B1985729 : Blo 1323480 1985729 := bstep (se 2 (by rfl) ⟨744648, by rfl⟩ : syracuseStep 1985729 = 1489297) B1489297
theorem B3353795 : Blo 1323480 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B10054853 : Blo 1323480 10054853 := bstep (se 4 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 10054853 = 1885285) B1885285
theorem B1985747 : Blo 1323480 1985747 := bstep (se 1 (by rfl) ⟨1489310, by rfl⟩ : syracuseStep 1985747 = 2978621) B2978621
theorem B1985777 : Blo 1323480 1985777 := bstep (se 2 (by rfl) ⟨744666, by rfl⟩ : syracuseStep 1985777 = 1489333) B1489333
theorem B6704369 : Blo 1323480 6704369 := bstep (se 2 (by rfl) ⟨2514138, by rfl⟩ : syracuseStep 6704369 = 5028277) B5028277
theorem B2264323 : Blo 1323480 2264323 := bstep (se 1 (by rfl) ⟨1698242, by rfl⟩ : syracuseStep 2264323 = 3396485) B3396485
theorem B1985795 : Blo 1323480 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B1985825 : Blo 1323480 1985825 := bstep (se 2 (by rfl) ⟨744684, by rfl⟩ : syracuseStep 1985825 = 1489369) B1489369
theorem B4468013 : Blo 1323480 4468013 := bstep (se 3 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 4468013 = 1675505) B1675505
theorem B7154993 : Blo 1323480 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B1985843 : Blo 1323480 1985843 := bstep (se 1 (by rfl) ⟨1489382, by rfl⟩ : syracuseStep 1985843 = 2978765) B2978765
theorem B1985873 : Blo 1323480 1985873 := bstep (se 2 (by rfl) ⟨744702, by rfl⟩ : syracuseStep 1985873 = 1489405) B1489405
theorem B4468067 : Blo 1323480 4468067 := bstep (se 1 (by rfl) ⟨3351050, by rfl⟩ : syracuseStep 4468067 = 6702101) B6702101
theorem B1985891 : Blo 1323480 1985891 := bstep (se 1 (by rfl) ⟨1489418, by rfl⟩ : syracuseStep 1985891 = 2978837) B2978837
theorem B1699187 : Blo 1323480 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B1985921 : Blo 1323480 1985921 := bstep (se 2 (by rfl) ⟨744720, by rfl⟩ : syracuseStep 1985921 = 1489441) B1489441
theorem B3353987 : Blo 1323480 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B1985939 : Blo 1323480 1985939 := bstep (se 1 (by rfl) ⟨1489454, by rfl⟩ : syracuseStep 1985939 = 2978909) B2978909
theorem B1985969 : Blo 1323480 1985969 := bstep (se 2 (by rfl) ⟨744738, by rfl⟩ : syracuseStep 1985969 = 1489477) B1489477
theorem B1985987 : Blo 1323480 1985987 := bstep (se 1 (by rfl) ⟨1489490, by rfl⟩ : syracuseStep 1985987 = 2978981) B2978981
theorem B1986017 : Blo 1323480 1986017 := bstep (se 2 (by rfl) ⟨744756, by rfl⟩ : syracuseStep 1986017 = 1489513) B1489513
theorem B1986035 : Blo 1323480 1986035 := bstep (se 1 (by rfl) ⟨1489526, by rfl⟩ : syracuseStep 1986035 = 2979053) B2979053
theorem B7540229 : Blo 1323480 7540229 := bstep (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) B1413793
theorem B1986065 : Blo 1323480 1986065 := bstep (se 2 (by rfl) ⟨744774, by rfl⟩ : syracuseStep 1986065 = 1489549) B1489549
theorem B1986083 : Blo 1323480 1986083 := bstep (se 1 (by rfl) ⟨1489562, by rfl⟩ : syracuseStep 1986083 = 2979125) B2979125
theorem B1986113 : Blo 1323480 1986113 := bstep (se 2 (by rfl) ⟨744792, by rfl⟩ : syracuseStep 1986113 = 1489585) B1489585
theorem B1986131 : Blo 1323480 1986131 := bstep (se 1 (by rfl) ⟨1489598, by rfl⟩ : syracuseStep 1986131 = 2979197) B2979197
theorem B4468337 : Blo 1323480 4468337 := bstep (se 2 (by rfl) ⟨1675626, by rfl⟩ : syracuseStep 4468337 = 3351253) B3351253
theorem B1986161 : Blo 1323480 1986161 := bstep (se 2 (by rfl) ⟨744810, by rfl⟩ : syracuseStep 1986161 = 1489621) B1489621
theorem B1986179 : Blo 1323480 1986179 := bstep (se 1 (by rfl) ⟨1489634, by rfl⟩ : syracuseStep 1986179 = 2979269) B2979269
theorem B7155341 : Blo 1323480 7155341 := bstep (se 3 (by rfl) ⟨1341626, by rfl⟩ : syracuseStep 7155341 = 2683253) B2683253
theorem B1986209 : Blo 1323480 1986209 := bstep (se 2 (by rfl) ⟨744828, by rfl⟩ : syracuseStep 1986209 = 1489657) B1489657
theorem B2297521 : Blo 1323480 2297521 := bstep (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) B1723141
theorem B1986227 : Blo 1323480 1986227 := bstep (se 1 (by rfl) ⟨1489670, by rfl⟩ : syracuseStep 1986227 = 2979341) B2979341
theorem B3772109 : Blo 1323480 3772109 := bstep (se 3 (by rfl) ⟨707270, by rfl⟩ : syracuseStep 3772109 = 1414541) B1414541
theorem B1986257 : Blo 1323480 1986257 := bstep (se 2 (by rfl) ⟨744846, by rfl⟩ : syracuseStep 1986257 = 1489693) B1489693
theorem B21475043 : Blo 1323480 21475043 := bstep (se 1 (by rfl) ⟨16106282, by rfl⟩ : syracuseStep 21475043 = 32212565) B32212565
theorem B1986275 : Blo 1323480 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B10063601 : Blo 1323480 10063601 := bstep (se 2 (by rfl) ⟨3773850, by rfl⟩ : syracuseStep 10063601 = 7547701) B7547701
theorem B1986305 : Blo 1323480 1986305 := bstep (se 2 (by rfl) ⟨744864, by rfl⟩ : syracuseStep 1986305 = 1489729) B1489729
theorem B1986323 : Blo 1323480 1986323 := bstep (se 1 (by rfl) ⟨1489742, by rfl⟩ : syracuseStep 1986323 = 2979485) B2979485
theorem B2830115 : Blo 1323480 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B1986353 : Blo 1323480 1986353 := bstep (se 2 (by rfl) ⟨744882, by rfl⟩ : syracuseStep 1986353 = 1489765) B1489765
theorem B1675075 : Blo 1323480 1675075 := bstep (se 1 (by rfl) ⟨1256306, by rfl⟩ : syracuseStep 1675075 = 2512613) B2512613
theorem B1986371 : Blo 1323480 1986371 := bstep (se 1 (by rfl) ⟨1489778, by rfl⟩ : syracuseStep 1986371 = 2979557) B2979557
theorem B1986401 : Blo 1323480 1986401 := bstep (se 2 (by rfl) ⟨744900, by rfl⟩ : syracuseStep 1986401 = 1489801) B1489801
theorem B5025635 : Blo 1323480 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B1986419 : Blo 1323480 1986419 := bstep (se 1 (by rfl) ⟨1489814, by rfl⟩ : syracuseStep 1986419 = 2979629) B2979629
theorem B3772291 : Blo 1323480 3772291 := bstep (se 1 (by rfl) ⟨2829218, by rfl⟩ : syracuseStep 3772291 = 5658437) B5658437
theorem B1986449 : Blo 1323480 1986449 := bstep (se 2 (by rfl) ⟨744918, by rfl⟩ : syracuseStep 1986449 = 1489837) B1489837
theorem B1675171 : Blo 1323480 1675171 := bstep (se 1 (by rfl) ⟨1256378, by rfl⟩ : syracuseStep 1675171 = 2512757) B2512757
theorem B1986467 : Blo 1323480 1986467 := bstep (se 1 (by rfl) ⟨1489850, by rfl⟩ : syracuseStep 1986467 = 2979701) B2979701
theorem B4026289 : Blo 1323480 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B1986497 : Blo 1323480 1986497 := bstep (se 2 (by rfl) ⟨744936, by rfl⟩ : syracuseStep 1986497 = 1489873) B1489873
theorem B7540685 : Blo 1323480 7540685 := bstep (se 3 (by rfl) ⟨1413878, by rfl⟩ : syracuseStep 7540685 = 2827757) B2827757
theorem B1986515 : Blo 1323480 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B1986545 : Blo 1323480 1986545 := bstep (se 2 (by rfl) ⟨744954, by rfl⟩ : syracuseStep 1986545 = 1489909) B1489909
theorem B1986563 : Blo 1323480 1986563 := bstep (se 1 (by rfl) ⟨1489922, by rfl⟩ : syracuseStep 1986563 = 2979845) B2979845
theorem B8491013 : Blo 1323480 8491013 := bstep (se 4 (by rfl) ⟨796032, by rfl⟩ : syracuseStep 8491013 = 1592065) B1592065
theorem B1986593 : Blo 1323480 1986593 := bstep (se 2 (by rfl) ⟨744972, by rfl⟩ : syracuseStep 1986593 = 1489945) B1489945
theorem B6983729 : Blo 1323480 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1986611 : Blo 1323480 1986611 := bstep (se 1 (by rfl) ⟨1489958, by rfl⟩ : syracuseStep 1986611 = 2979917) B2979917
theorem B7548977 : Blo 1323480 7548977 := bstep (se 2 (by rfl) ⟨2830866, by rfl⟩ : syracuseStep 7548977 = 5661733) B5661733
theorem B1986641 : Blo 1323480 1986641 := bstep (se 2 (by rfl) ⟨744990, by rfl⟩ : syracuseStep 1986641 = 1489981) B1489981
theorem B1986659 : Blo 1323480 1986659 := bstep (se 1 (by rfl) ⟨1489994, by rfl⟩ : syracuseStep 1986659 = 2979989) B2979989
theorem B1986689 : Blo 1323480 1986689 := bstep (se 2 (by rfl) ⟨745008, by rfl⟩ : syracuseStep 1986689 = 1490017) B1490017
theorem B4468877 : Blo 1323480 4468877 := bstep (se 3 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 4468877 = 1675829) B1675829
theorem B2977937 : Blo 1323480 2977937 := bstep (se 2 (by rfl) ⟨1116726, by rfl⟩ : syracuseStep 2977937 = 2233453) B2233453
theorem B1986707 : Blo 1323480 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B2977955 : Blo 1323480 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B1986737 : Blo 1323480 1986737 := bstep (se 2 (by rfl) ⟨745026, by rfl⟩ : syracuseStep 1986737 = 1490053) B1490053
theorem B4468931 : Blo 1323480 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1986755 : Blo 1323480 1986755 := bstep (se 1 (by rfl) ⟨1490066, by rfl⟩ : syracuseStep 1986755 = 2980133) B2980133
theorem B34402501 : Blo 1323480 34402501 := bstep (se 4 (by rfl) ⟨3225234, by rfl⟩ : syracuseStep 34402501 = 6450469) B6450469
theorem B1986785 : Blo 1323480 1986785 := bstep (se 2 (by rfl) ⟨745044, by rfl⟩ : syracuseStep 1986785 = 1490089) B1490089
theorem B1986803 : Blo 1323480 1986803 := bstep (se 1 (by rfl) ⟨1490102, by rfl⟩ : syracuseStep 1986803 = 2980205) B2980205
theorem B1413379 : Blo 1323480 1413379 := bstep (se 1 (by rfl) ⟨1060034, by rfl⟩ : syracuseStep 1413379 = 2120069) B2120069
theorem B1986833 : Blo 1323480 1986833 := bstep (se 2 (by rfl) ⟨745062, by rfl⟩ : syracuseStep 1986833 = 1490125) B1490125
theorem B1986851 : Blo 1323480 1986851 := bstep (se 1 (by rfl) ⟨1490138, by rfl⟩ : syracuseStep 1986851 = 2980277) B2980277
theorem B3354929 : Blo 1323480 3354929 := bstep (se 2 (by rfl) ⟨1258098, by rfl⟩ : syracuseStep 3354929 = 2516197) B2516197
theorem B1986881 : Blo 1323480 1986881 := bstep (se 2 (by rfl) ⟨745080, by rfl⟩ : syracuseStep 1986881 = 1490161) B1490161
theorem B1986899 : Blo 1323480 1986899 := bstep (se 1 (by rfl) ⟨1490174, by rfl⟩ : syracuseStep 1986899 = 2980349) B2980349
theorem B3354979 : Blo 1323480 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B3772781 : Blo 1323480 3772781 := bstep (se 3 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 3772781 = 1414793) B1414793
theorem B1986929 : Blo 1323480 1986929 := bstep (se 2 (by rfl) ⟨745098, by rfl⟩ : syracuseStep 1986929 = 1490197) B1490197
theorem B1986947 : Blo 1323480 1986947 := bstep (se 1 (by rfl) ⟨1490210, by rfl⟩ : syracuseStep 1986947 = 2980421) B2980421
theorem B1814929 : Blo 1323480 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B1675667 : Blo 1323480 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B1986977 : Blo 1323480 1986977 := bstep (se 2 (by rfl) ⟨745116, by rfl⟩ : syracuseStep 1986977 = 1490233) B1490233
theorem B2978225 : Blo 1323480 2978225 := bstep (se 2 (by rfl) ⟨1116834, by rfl⟩ : syracuseStep 2978225 = 2233669) B2233669
theorem B1986995 : Blo 1323480 1986995 := bstep (se 1 (by rfl) ⟨1490246, by rfl⟩ : syracuseStep 1986995 = 2980493) B2980493
theorem B2978243 : Blo 1323480 2978243 := bstep (se 1 (by rfl) ⟨2233682, by rfl⟩ : syracuseStep 2978243 = 4467365) B4467365
theorem B4469201 : Blo 1323480 4469201 := bstep (se 2 (by rfl) ⟨1675950, by rfl⟩ : syracuseStep 4469201 = 3351901) B3351901
theorem B1987025 : Blo 1323480 1987025 := bstep (se 2 (by rfl) ⟨745134, by rfl⟩ : syracuseStep 1987025 = 1490269) B1490269
theorem B1323491 : Blo 1323480 1323491 := bstep (se 1 (by rfl) ⟨992618, by rfl⟩ : syracuseStep 1323491 = 1985237) B1985237
theorem B1987043 : Blo 1323480 1987043 := bstep (se 1 (by rfl) ⟨1490282, by rfl⟩ : syracuseStep 1987043 = 2980565) B2980565
theorem B3355121 : Blo 1323480 3355121 := bstep (se 2 (by rfl) ⟨1258170, by rfl⟩ : syracuseStep 3355121 = 2516341) B2516341
theorem B1323507 : Blo 1323480 1323507 := bstep (se 1 (by rfl) ⟨992630, by rfl⟩ : syracuseStep 1323507 = 1985261) B1985261
theorem B1987073 : Blo 1323480 1987073 := bstep (se 2 (by rfl) ⟨745152, by rfl⟩ : syracuseStep 1987073 = 1490305) B1490305
theorem B1323523 : Blo 1323480 1323523 := bstep (se 1 (by rfl) ⟨992642, by rfl⟩ : syracuseStep 1323523 = 1985285) B1985285
theorem B1323539 : Blo 1323480 1323539 := bstep (se 1 (by rfl) ⟨992654, by rfl⟩ : syracuseStep 1323539 = 1985309) B1985309
theorem B1987091 : Blo 1323480 1987091 := bstep (se 1 (by rfl) ⟨1490318, by rfl⟩ : syracuseStep 1987091 = 2980637) B2980637
theorem B1323555 : Blo 1323480 1323555 := bstep (se 1 (by rfl) ⟨992666, by rfl⟩ : syracuseStep 1323555 = 1985333) B1985333
theorem B6361649 : Blo 1323480 6361649 := bstep (se 2 (by rfl) ⟨2385618, by rfl⟩ : syracuseStep 6361649 = 4771237) B4771237
theorem B1987121 : Blo 1323480 1987121 := bstep (se 2 (by rfl) ⟨745170, by rfl⟩ : syracuseStep 1987121 = 1490341) B1490341
theorem B1323571 : Blo 1323480 1323571 := bstep (se 1 (by rfl) ⟨992678, by rfl⟩ : syracuseStep 1323571 = 1985357) B1985357
theorem B1323587 : Blo 1323480 1323587 := bstep (se 1 (by rfl) ⟨992690, by rfl⟩ : syracuseStep 1323587 = 1985381) B1985381
theorem B1987139 : Blo 1323480 1987139 := bstep (se 1 (by rfl) ⟨1490354, by rfl⟩ : syracuseStep 1987139 = 2980709) B2980709
theorem B1323603 : Blo 1323480 1323603 := bstep (se 1 (by rfl) ⟨992702, by rfl⟩ : syracuseStep 1323603 = 1985405) B1985405
theorem B1987169 : Blo 1323480 1987169 := bstep (se 2 (by rfl) ⟨745188, by rfl⟩ : syracuseStep 1987169 = 1490377) B1490377
theorem B4239971 : Blo 1323480 4239971 := bstep (se 1 (by rfl) ⟨3179978, by rfl⟩ : syracuseStep 4239971 = 6359957) B6359957
theorem B1323619 : Blo 1323480 1323619 := bstep (se 1 (by rfl) ⟨992714, by rfl⟩ : syracuseStep 1323619 = 1985429) B1985429
theorem B1323635 : Blo 1323480 1323635 := bstep (se 1 (by rfl) ⟨992726, by rfl⟩ : syracuseStep 1323635 = 1985453) B1985453
theorem B1987187 : Blo 1323480 1987187 := bstep (se 1 (by rfl) ⟨1490390, by rfl⟩ : syracuseStep 1987187 = 2980781) B2980781
theorem B1323651 : Blo 1323480 1323651 := bstep (se 1 (by rfl) ⟨992738, by rfl⟩ : syracuseStep 1323651 = 1985477) B1985477
theorem B1987217 : Blo 1323480 1987217 := bstep (se 2 (by rfl) ⟨745206, by rfl⟩ : syracuseStep 1987217 = 1490413) B1490413
theorem B1323667 : Blo 1323480 1323667 := bstep (se 1 (by rfl) ⟨992750, by rfl⟩ : syracuseStep 1323667 = 1985501) B1985501
theorem B1323683 : Blo 1323480 1323683 := bstep (se 1 (by rfl) ⟨992762, by rfl⟩ : syracuseStep 1323683 = 1985525) B1985525
theorem B6705827 : Blo 1323480 6705827 := bstep (se 1 (by rfl) ⟨5029370, by rfl⟩ : syracuseStep 6705827 = 10058741) B10058741
theorem B1987235 : Blo 1323480 1987235 := bstep (se 1 (by rfl) ⟨1490426, by rfl⟩ : syracuseStep 1987235 = 2980853) B2980853
theorem B1323699 : Blo 1323480 1323699 := bstep (se 1 (by rfl) ⟨992774, by rfl⟩ : syracuseStep 1323699 = 1985549) B1985549
theorem B1987265 : Blo 1323480 1987265 := bstep (se 2 (by rfl) ⟨745224, by rfl⟩ : syracuseStep 1987265 = 1490449) B1490449
theorem B1323715 : Blo 1323480 1323715 := bstep (se 1 (by rfl) ⟨992786, by rfl⟩ : syracuseStep 1323715 = 1985573) B1985573
theorem B2978513 : Blo 1323480 2978513 := bstep (se 2 (by rfl) ⟨1116942, by rfl⟩ : syracuseStep 2978513 = 2233885) B2233885
theorem B1323731 : Blo 1323480 1323731 := bstep (se 1 (by rfl) ⟨992798, by rfl⟩ : syracuseStep 1323731 = 1985597) B1985597
theorem B1987283 : Blo 1323480 1987283 := bstep (se 1 (by rfl) ⟨1490462, by rfl⟩ : syracuseStep 1987283 = 2980925) B2980925
theorem B1323747 : Blo 1323480 1323747 := bstep (se 1 (by rfl) ⟨992810, by rfl⟩ : syracuseStep 1323747 = 1985621) B1985621
theorem B2978531 : Blo 1323480 2978531 := bstep (se 1 (by rfl) ⟨2233898, by rfl⟩ : syracuseStep 2978531 = 4467797) B4467797
theorem B8483555 : Blo 1323480 8483555 := bstep (se 1 (by rfl) ⟨6362666, by rfl⟩ : syracuseStep 8483555 = 12725333) B12725333
theorem B1987313 : Blo 1323480 1987313 := bstep (se 2 (by rfl) ⟨745242, by rfl⟩ : syracuseStep 1987313 = 1490485) B1490485
theorem B1323763 : Blo 1323480 1323763 := bstep (se 1 (by rfl) ⟨992822, by rfl⟩ : syracuseStep 1323763 = 1985645) B1985645
theorem B1323779 : Blo 1323480 1323779 := bstep (se 1 (by rfl) ⟨992834, by rfl⟩ : syracuseStep 1323779 = 1985669) B1985669
theorem B1987331 : Blo 1323480 1987331 := bstep (se 1 (by rfl) ⟨1490498, by rfl⟩ : syracuseStep 1987331 = 2980997) B2980997
theorem B1323795 : Blo 1323480 1323795 := bstep (se 1 (by rfl) ⟨992846, by rfl⟩ : syracuseStep 1323795 = 1985693) B1985693
theorem B1987361 : Blo 1323480 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1323811 : Blo 1323480 1323811 := bstep (se 1 (by rfl) ⟨992858, by rfl⟩ : syracuseStep 1323811 = 1985717) B1985717
theorem B1323827 : Blo 1323480 1323827 := bstep (se 1 (by rfl) ⟨992870, by rfl⟩ : syracuseStep 1323827 = 1985741) B1985741
theorem B1987379 : Blo 1323480 1987379 := bstep (se 1 (by rfl) ⟨1490534, by rfl⟩ : syracuseStep 1987379 = 2981069) B2981069
theorem B24171317 : Blo 1323480 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B1323843 : Blo 1323480 1323843 := bstep (se 1 (by rfl) ⟨992882, by rfl⟩ : syracuseStep 1323843 = 1985765) B1985765
theorem B5026637 : Blo 1323480 5026637 := bstep (se 3 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 5026637 = 1884989) B1884989
theorem B1987409 : Blo 1323480 1987409 := bstep (se 2 (by rfl) ⟨745278, by rfl⟩ : syracuseStep 1987409 = 1490557) B1490557
theorem B7164749 : Blo 1323480 7164749 := bstep (se 3 (by rfl) ⟨1343390, by rfl⟩ : syracuseStep 7164749 = 2686781) B2686781
theorem B1323859 : Blo 1323480 1323859 := bstep (se 1 (by rfl) ⟨992894, by rfl⟩ : syracuseStep 1323859 = 1985789) B1985789
theorem B1323875 : Blo 1323480 1323875 := bstep (se 1 (by rfl) ⟨992906, by rfl⟩ : syracuseStep 1323875 = 1985813) B1985813
theorem B1987427 : Blo 1323480 1987427 := bstep (se 1 (by rfl) ⟨1490570, by rfl⟩ : syracuseStep 1987427 = 2981141) B2981141
theorem B1323891 : Blo 1323480 1323891 := bstep (se 1 (by rfl) ⟨992918, by rfl⟩ : syracuseStep 1323891 = 1985837) B1985837
theorem B1987457 : Blo 1323480 1987457 := bstep (se 2 (by rfl) ⟨745296, by rfl⟩ : syracuseStep 1987457 = 1490593) B1490593
theorem B1323907 : Blo 1323480 1323907 := bstep (se 1 (by rfl) ⟨992930, by rfl⟩ : syracuseStep 1323907 = 1985861) B1985861
theorem B1323923 : Blo 1323480 1323923 := bstep (se 1 (by rfl) ⟨992942, by rfl⟩ : syracuseStep 1323923 = 1985885) B1985885
theorem B1987475 : Blo 1323480 1987475 := bstep (se 1 (by rfl) ⟨1490606, by rfl⟩ : syracuseStep 1987475 = 2981213) B2981213
theorem B1323939 : Blo 1323480 1323939 := bstep (se 1 (by rfl) ⟨992954, by rfl⟩ : syracuseStep 1323939 = 1985909) B1985909
theorem B1987505 : Blo 1323480 1987505 := bstep (se 2 (by rfl) ⟨745314, by rfl⟩ : syracuseStep 1987505 = 1490629) B1490629
theorem B1323955 : Blo 1323480 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B1323971 : Blo 1323480 1323971 := bstep (se 1 (by rfl) ⟨992978, by rfl⟩ : syracuseStep 1323971 = 1985957) B1985957
theorem B1987523 : Blo 1323480 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B1323987 : Blo 1323480 1323987 := bstep (se 1 (by rfl) ⟨992990, by rfl⟩ : syracuseStep 1323987 = 1985981) B1985981
theorem B1987553 : Blo 1323480 1987553 := bstep (se 2 (by rfl) ⟨745332, by rfl⟩ : syracuseStep 1987553 = 1490665) B1490665
theorem B1324003 : Blo 1323480 1324003 := bstep (se 1 (by rfl) ⟨993002, by rfl⟩ : syracuseStep 1324003 = 1986005) B1986005
theorem B4469741 : Blo 1323480 4469741 := bstep (se 3 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 4469741 = 1676153) B1676153
theorem B2978801 : Blo 1323480 2978801 := bstep (se 2 (by rfl) ⟨1117050, by rfl⟩ : syracuseStep 2978801 = 2234101) B2234101
theorem B1324019 : Blo 1323480 1324019 := bstep (se 1 (by rfl) ⟨993014, by rfl⟩ : syracuseStep 1324019 = 1986029) B1986029
theorem B1987571 : Blo 1323480 1987571 := bstep (se 1 (by rfl) ⟨1490678, by rfl⟩ : syracuseStep 1987571 = 2981357) B2981357
theorem B2978819 : Blo 1323480 2978819 := bstep (se 1 (by rfl) ⟨2234114, by rfl⟩ : syracuseStep 2978819 = 4468229) B4468229
theorem B1324035 : Blo 1323480 1324035 := bstep (se 1 (by rfl) ⟨993026, by rfl⟩ : syracuseStep 1324035 = 1986053) B1986053
theorem B1987601 : Blo 1323480 1987601 := bstep (se 2 (by rfl) ⟨745350, by rfl⟩ : syracuseStep 1987601 = 1490701) B1490701
theorem B1324051 : Blo 1323480 1324051 := bstep (se 1 (by rfl) ⟨993038, by rfl⟩ : syracuseStep 1324051 = 1986077) B1986077
theorem B2233379 : Blo 1323480 2233379 := bstep (se 1 (by rfl) ⟨1675034, by rfl⟩ : syracuseStep 2233379 = 3350069) B3350069
theorem B1324067 : Blo 1323480 1324067 := bstep (se 1 (by rfl) ⟨993050, by rfl⟩ : syracuseStep 1324067 = 1986101) B1986101
theorem B4469795 : Blo 1323480 4469795 := bstep (se 1 (by rfl) ⟨3352346, by rfl⟩ : syracuseStep 4469795 = 6704693) B6704693
theorem B1987619 : Blo 1323480 1987619 := bstep (se 1 (by rfl) ⟨1490714, by rfl⟩ : syracuseStep 1987619 = 2981429) B2981429
theorem B1324083 : Blo 1323480 1324083 := bstep (se 1 (by rfl) ⟨993062, by rfl⟩ : syracuseStep 1324083 = 1986125) B1986125
theorem B1324099 : Blo 1323480 1324099 := bstep (se 1 (by rfl) ⟨993074, by rfl⟩ : syracuseStep 1324099 = 1986149) B1986149
theorem B1987649 : Blo 1323480 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B1324115 : Blo 1323480 1324115 := bstep (se 1 (by rfl) ⟨993086, by rfl⟩ : syracuseStep 1324115 = 1986173) B1986173
theorem B1676371 : Blo 1323480 1676371 := bstep (se 1 (by rfl) ⟨1257278, by rfl⟩ : syracuseStep 1676371 = 2514557) B2514557
theorem B1987667 : Blo 1323480 1987667 := bstep (se 1 (by rfl) ⟨1490750, by rfl⟩ : syracuseStep 1987667 = 2981501) B2981501
theorem B1324131 : Blo 1323480 1324131 := bstep (se 1 (by rfl) ⟨993098, by rfl⟩ : syracuseStep 1324131 = 1986197) B1986197
theorem B1987697 : Blo 1323480 1987697 := bstep (se 2 (by rfl) ⟨745386, by rfl⟩ : syracuseStep 1987697 = 1490773) B1490773
theorem B1324147 : Blo 1323480 1324147 := bstep (se 1 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 1324147 = 1986221) B1986221
theorem B1324163 : Blo 1323480 1324163 := bstep (se 1 (by rfl) ⟨993122, by rfl⟩ : syracuseStep 1324163 = 1986245) B1986245
theorem B1987715 : Blo 1323480 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B1324179 : Blo 1323480 1324179 := bstep (se 1 (by rfl) ⟨993134, by rfl⟩ : syracuseStep 1324179 = 1986269) B1986269
theorem B1987745 : Blo 1323480 1987745 := bstep (se 2 (by rfl) ⟨745404, by rfl⟩ : syracuseStep 1987745 = 1490809) B1490809
theorem B2233507 : Blo 1323480 2233507 := bstep (se 1 (by rfl) ⟨1675130, by rfl⟩ : syracuseStep 2233507 = 3350261) B3350261
theorem B1324195 : Blo 1323480 1324195 := bstep (se 1 (by rfl) ⟨993146, by rfl⟩ : syracuseStep 1324195 = 1986293) B1986293
theorem B1324211 : Blo 1323480 1324211 := bstep (se 1 (by rfl) ⟨993158, by rfl⟩ : syracuseStep 1324211 = 1986317) B1986317
theorem B1676467 : Blo 1323480 1676467 := bstep (se 1 (by rfl) ⟨1257350, by rfl⟩ : syracuseStep 1676467 = 2514701) B2514701
theorem B1987763 : Blo 1323480 1987763 := bstep (se 1 (by rfl) ⟨1490822, by rfl⟩ : syracuseStep 1987763 = 2981645) B2981645
theorem B1324227 : Blo 1323480 1324227 := bstep (se 1 (by rfl) ⟨993170, by rfl⟩ : syracuseStep 1324227 = 1986341) B1986341
theorem B1987793 : Blo 1323480 1987793 := bstep (se 2 (by rfl) ⟨745422, by rfl⟩ : syracuseStep 1987793 = 1490845) B1490845
theorem B1324243 : Blo 1323480 1324243 := bstep (se 1 (by rfl) ⟨993182, by rfl⟩ : syracuseStep 1324243 = 1986365) B1986365
theorem B1324259 : Blo 1323480 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B1987811 : Blo 1323480 1987811 := bstep (se 1 (by rfl) ⟨1490858, by rfl⟩ : syracuseStep 1987811 = 2981717) B2981717
theorem B1324275 : Blo 1323480 1324275 := bstep (se 1 (by rfl) ⟨993206, by rfl⟩ : syracuseStep 1324275 = 1986413) B1986413
theorem B1987841 : Blo 1323480 1987841 := bstep (se 2 (by rfl) ⟨745440, by rfl⟩ : syracuseStep 1987841 = 1490881) B1490881
theorem B1324291 : Blo 1323480 1324291 := bstep (se 1 (by rfl) ⟨993218, by rfl⟩ : syracuseStep 1324291 = 1986437) B1986437
theorem B4027651 : Blo 1323480 4027651 := bstep (se 1 (by rfl) ⟨3020738, by rfl⟩ : syracuseStep 4027651 = 6041477) B6041477
theorem B2979089 : Blo 1323480 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B1324307 : Blo 1323480 1324307 := bstep (se 1 (by rfl) ⟨993230, by rfl⟩ : syracuseStep 1324307 = 1986461) B1986461
theorem B1987859 : Blo 1323480 1987859 := bstep (se 1 (by rfl) ⟨1490894, by rfl⟩ : syracuseStep 1987859 = 2981789) B2981789
theorem B2979107 : Blo 1323480 2979107 := bstep (se 1 (by rfl) ⟨2234330, by rfl⟩ : syracuseStep 2979107 = 4468661) B4468661
theorem B1324323 : Blo 1323480 1324323 := bstep (se 1 (by rfl) ⟨993242, by rfl⟩ : syracuseStep 1324323 = 1986485) B1986485
theorem B2233649 : Blo 1323480 2233649 := bstep (se 2 (by rfl) ⟨837618, by rfl⟩ : syracuseStep 2233649 = 1675237) B1675237
theorem B4470065 : Blo 1323480 4470065 := bstep (se 2 (by rfl) ⟨1676274, by rfl⟩ : syracuseStep 4470065 = 3352549) B3352549
theorem B1324339 : Blo 1323480 1324339 := bstep (se 1 (by rfl) ⟨993254, by rfl⟩ : syracuseStep 1324339 = 1986509) B1986509
theorem B1987889 : Blo 1323480 1987889 := bstep (se 2 (by rfl) ⟨745458, by rfl⟩ : syracuseStep 1987889 = 1490917) B1490917
theorem B1324355 : Blo 1323480 1324355 := bstep (se 1 (by rfl) ⟨993266, by rfl⟩ : syracuseStep 1324355 = 1986533) B1986533
theorem B1987907 : Blo 1323480 1987907 := bstep (se 1 (by rfl) ⟨1490930, by rfl⟩ : syracuseStep 1987907 = 2981861) B2981861
theorem B1324371 : Blo 1323480 1324371 := bstep (se 1 (by rfl) ⟨993278, by rfl⟩ : syracuseStep 1324371 = 1986557) B1986557
theorem B1987937 : Blo 1323480 1987937 := bstep (se 2 (by rfl) ⟨745476, by rfl⟩ : syracuseStep 1987937 = 1490953) B1490953
theorem B1324387 : Blo 1323480 1324387 := bstep (se 1 (by rfl) ⟨993290, by rfl⟩ : syracuseStep 1324387 = 1986581) B1986581
theorem B33920369 : Blo 1323480 33920369 := bstep (se 2 (by rfl) ⟨12720138, by rfl⟩ : syracuseStep 33920369 = 25440277) B25440277
theorem B1324403 : Blo 1323480 1324403 := bstep (se 1 (by rfl) ⟨993302, by rfl⟩ : syracuseStep 1324403 = 1986605) B1986605
theorem B1987955 : Blo 1323480 1987955 := bstep (se 1 (by rfl) ⟨1490966, by rfl⟩ : syracuseStep 1987955 = 2981933) B2981933
theorem B1324419 : Blo 1323480 1324419 := bstep (se 1 (by rfl) ⟨993314, by rfl⟩ : syracuseStep 1324419 = 1986629) B1986629
theorem B2012561 : Blo 1323480 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B1987985 : Blo 1323480 1987985 := bstep (se 2 (by rfl) ⟨745494, by rfl⟩ : syracuseStep 1987985 = 1490989) B1490989
theorem B1324435 : Blo 1323480 1324435 := bstep (se 1 (by rfl) ⟨993326, by rfl⟩ : syracuseStep 1324435 = 1986653) B1986653
theorem B7157155 : Blo 1323480 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B1324451 : Blo 1323480 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B8058275 : Blo 1323480 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B1988003 : Blo 1323480 1988003 := bstep (se 1 (by rfl) ⟨1491002, by rfl⟩ : syracuseStep 1988003 = 2982005) B2982005
theorem B2233777 : Blo 1323480 2233777 := bstep (se 2 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 2233777 = 1675333) B1675333
theorem B1324467 : Blo 1323480 1324467 := bstep (se 1 (by rfl) ⟨993350, by rfl⟩ : syracuseStep 1324467 = 1986701) B1986701
theorem B1988033 : Blo 1323480 1988033 := bstep (se 2 (by rfl) ⟨745512, by rfl⟩ : syracuseStep 1988033 = 1491025) B1491025
theorem B1324483 : Blo 1323480 1324483 := bstep (se 1 (by rfl) ⟨993362, by rfl⟩ : syracuseStep 1324483 = 1986725) B1986725
theorem B6706637 : Blo 1323480 6706637 := bstep (se 3 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 6706637 = 2514989) B2514989
theorem B2233811 : Blo 1323480 2233811 := bstep (se 1 (by rfl) ⟨1675358, by rfl⟩ : syracuseStep 2233811 = 3350717) B3350717
theorem B1324499 : Blo 1323480 1324499 := bstep (se 1 (by rfl) ⟨993374, by rfl⟩ : syracuseStep 1324499 = 1986749) B1986749
theorem B1988051 : Blo 1323480 1988051 := bstep (se 1 (by rfl) ⟨1491038, by rfl⟩ : syracuseStep 1988051 = 2982077) B2982077
theorem B1324515 : Blo 1323480 1324515 := bstep (se 1 (by rfl) ⟨993386, by rfl⟩ : syracuseStep 1324515 = 1986773) B1986773
theorem B12727793 : Blo 1323480 12727793 := bstep (se 2 (by rfl) ⟨4772922, by rfl⟩ : syracuseStep 12727793 = 9545845) B9545845
theorem B1988081 : Blo 1323480 1988081 := bstep (se 2 (by rfl) ⟨745530, by rfl⟩ : syracuseStep 1988081 = 1491061) B1491061
theorem B1324531 : Blo 1323480 1324531 := bstep (se 1 (by rfl) ⟨993398, by rfl⟩ : syracuseStep 1324531 = 1986797) B1986797
theorem B1324547 : Blo 1323480 1324547 := bstep (se 1 (by rfl) ⟨993410, by rfl⟩ : syracuseStep 1324547 = 1986821) B1986821
theorem B1988099 : Blo 1323480 1988099 := bstep (se 1 (by rfl) ⟨1491074, by rfl⟩ : syracuseStep 1988099 = 2982149) B2982149
theorem B3773965 : Blo 1323480 3773965 := bstep (se 3 (by rfl) ⟨707618, by rfl⟩ : syracuseStep 3773965 = 1415237) B1415237
theorem B1324563 : Blo 1323480 1324563 := bstep (se 1 (by rfl) ⟨993422, by rfl⟩ : syracuseStep 1324563 = 1986845) B1986845
theorem B36271637 : Blo 1323480 36271637 := bstep (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) B1700233
theorem B1988129 : Blo 1323480 1988129 := bstep (se 2 (by rfl) ⟨745548, by rfl⟩ : syracuseStep 1988129 = 1491097) B1491097
theorem B1324579 : Blo 1323480 1324579 := bstep (se 1 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 1324579 = 1986869) B1986869
theorem B2979377 : Blo 1323480 2979377 := bstep (se 2 (by rfl) ⟨1117266, by rfl⟩ : syracuseStep 2979377 = 2234533) B2234533
theorem B1324595 : Blo 1323480 1324595 := bstep (se 1 (by rfl) ⟨993446, by rfl⟩ : syracuseStep 1324595 = 1986893) B1986893
theorem B1988147 : Blo 1323480 1988147 := bstep (se 1 (by rfl) ⟨1491110, by rfl⟩ : syracuseStep 1988147 = 2982221) B2982221
theorem B2979395 : Blo 1323480 2979395 := bstep (se 1 (by rfl) ⟨2234546, by rfl⟩ : syracuseStep 2979395 = 4469093) B4469093
theorem B1324611 : Blo 1323480 1324611 := bstep (se 1 (by rfl) ⟨993458, by rfl⟩ : syracuseStep 1324611 = 1986917) B1986917
theorem B1988177 : Blo 1323480 1988177 := bstep (se 2 (by rfl) ⟨745566, by rfl⟩ : syracuseStep 1988177 = 1491133) B1491133
theorem B2233939 : Blo 1323480 2233939 := bstep (se 1 (by rfl) ⟨1675454, by rfl⟩ : syracuseStep 2233939 = 3350909) B3350909
theorem B1324627 : Blo 1323480 1324627 := bstep (se 1 (by rfl) ⟨993470, by rfl⟩ : syracuseStep 1324627 = 1986941) B1986941
theorem B1324643 : Blo 1323480 1324643 := bstep (se 1 (by rfl) ⟨993482, by rfl⟩ : syracuseStep 1324643 = 1986965) B1986965
theorem B1988195 : Blo 1323480 1988195 := bstep (se 1 (by rfl) ⟨1491146, by rfl⟩ : syracuseStep 1988195 = 2982293) B2982293
theorem B1324659 : Blo 1323480 1324659 := bstep (se 1 (by rfl) ⟨993494, by rfl⟩ : syracuseStep 1324659 = 1986989) B1986989
theorem B1324675 : Blo 1323480 1324675 := bstep (se 1 (by rfl) ⟨993506, by rfl⟩ : syracuseStep 1324675 = 1987013) B1987013
theorem B1324691 : Blo 1323480 1324691 := bstep (se 1 (by rfl) ⟨993518, by rfl⟩ : syracuseStep 1324691 = 1987037) B1987037
theorem B1324707 : Blo 1323480 1324707 := bstep (se 1 (by rfl) ⟨993530, by rfl⟩ : syracuseStep 1324707 = 1987061) B1987061
theorem B1676963 : Blo 1323480 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B1324723 : Blo 1323480 1324723 := bstep (se 1 (by rfl) ⟨993542, by rfl⟩ : syracuseStep 1324723 = 1987085) B1987085
theorem B1324739 : Blo 1323480 1324739 := bstep (se 1 (by rfl) ⟨993554, by rfl⟩ : syracuseStep 1324739 = 1987109) B1987109
theorem B1324755 : Blo 1323480 1324755 := bstep (se 1 (by rfl) ⟨993566, by rfl⟩ : syracuseStep 1324755 = 1987133) B1987133
theorem B2234081 : Blo 1323480 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B1324771 : Blo 1323480 1324771 := bstep (se 1 (by rfl) ⟨993578, by rfl⟩ : syracuseStep 1324771 = 1987157) B1987157
theorem B1324787 : Blo 1323480 1324787 := bstep (se 1 (by rfl) ⟨993590, by rfl⟩ : syracuseStep 1324787 = 1987181) B1987181
theorem B1324803 : Blo 1323480 1324803 := bstep (se 1 (by rfl) ⟨993602, by rfl⟩ : syracuseStep 1324803 = 1987205) B1987205
theorem B1324819 : Blo 1323480 1324819 := bstep (se 1 (by rfl) ⟨993614, by rfl⟩ : syracuseStep 1324819 = 1987229) B1987229
theorem B1324835 : Blo 1323480 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B1324851 : Blo 1323480 1324851 := bstep (se 1 (by rfl) ⟨993638, by rfl⟩ : syracuseStep 1324851 = 1987277) B1987277
theorem B1324867 : Blo 1323480 1324867 := bstep (se 1 (by rfl) ⟨993650, by rfl⟩ : syracuseStep 1324867 = 1987301) B1987301
theorem B4470605 : Blo 1323480 4470605 := bstep (se 3 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 4470605 = 1676477) B1676477
theorem B2979665 : Blo 1323480 2979665 := bstep (se 2 (by rfl) ⟨1117374, by rfl⟩ : syracuseStep 2979665 = 2234749) B2234749
theorem B1324883 : Blo 1323480 1324883 := bstep (se 1 (by rfl) ⟨993662, by rfl⟩ : syracuseStep 1324883 = 1987325) B1987325
theorem B2234209 : Blo 1323480 2234209 := bstep (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) B1675657
theorem B2979683 : Blo 1323480 2979683 := bstep (se 1 (by rfl) ⟨2234762, by rfl⟩ : syracuseStep 2979683 = 4469525) B4469525
theorem B1324899 : Blo 1323480 1324899 := bstep (se 1 (by rfl) ⟨993674, by rfl⟩ : syracuseStep 1324899 = 1987349) B1987349
theorem B9541489 : Blo 1323480 9541489 := bstep (se 2 (by rfl) ⟨3578058, by rfl⟩ : syracuseStep 9541489 = 7156117) B7156117
theorem B1324915 : Blo 1323480 1324915 := bstep (se 1 (by rfl) ⟨993686, by rfl⟩ : syracuseStep 1324915 = 1987373) B1987373
theorem B2234243 : Blo 1323480 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B4470659 : Blo 1323480 4470659 := bstep (se 1 (by rfl) ⟨3352994, by rfl⟩ : syracuseStep 4470659 = 6705989) B6705989
theorem B1324931 : Blo 1323480 1324931 := bstep (se 1 (by rfl) ⟨993698, by rfl⟩ : syracuseStep 1324931 = 1987397) B1987397
theorem B1324947 : Blo 1323480 1324947 := bstep (se 1 (by rfl) ⟨993710, by rfl⟩ : syracuseStep 1324947 = 1987421) B1987421
theorem B1324963 : Blo 1323480 1324963 := bstep (se 1 (by rfl) ⟨993722, by rfl⟩ : syracuseStep 1324963 = 1987445) B1987445
theorem B1324979 : Blo 1323480 1324979 := bstep (se 1 (by rfl) ⟨993734, by rfl⟩ : syracuseStep 1324979 = 1987469) B1987469
theorem B1324995 : Blo 1323480 1324995 := bstep (se 1 (by rfl) ⟨993746, by rfl⟩ : syracuseStep 1324995 = 1987493) B1987493
theorem B1325011 : Blo 1323480 1325011 := bstep (se 1 (by rfl) ⟨993758, by rfl⟩ : syracuseStep 1325011 = 1987517) B1987517
theorem B1325027 : Blo 1323480 1325027 := bstep (se 1 (by rfl) ⟨993770, by rfl⟩ : syracuseStep 1325027 = 1987541) B1987541
theorem B1325043 : Blo 1323480 1325043 := bstep (se 1 (by rfl) ⟨993782, by rfl⟩ : syracuseStep 1325043 = 1987565) B1987565
theorem B2234371 : Blo 1323480 2234371 := bstep (se 1 (by rfl) ⟨1675778, by rfl⟩ : syracuseStep 2234371 = 3351557) B3351557
theorem B1325059 : Blo 1323480 1325059 := bstep (se 1 (by rfl) ⟨993794, by rfl⟩ : syracuseStep 1325059 = 1987589) B1987589
theorem B1325075 : Blo 1323480 1325075 := bstep (se 1 (by rfl) ⟨993806, by rfl⟩ : syracuseStep 1325075 = 1987613) B1987613
theorem B5658659 : Blo 1323480 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B1325091 : Blo 1323480 1325091 := bstep (se 1 (by rfl) ⟨993818, by rfl⟩ : syracuseStep 1325091 = 1987637) B1987637
theorem B1325107 : Blo 1323480 1325107 := bstep (se 1 (by rfl) ⟨993830, by rfl⟩ : syracuseStep 1325107 = 1987661) B1987661
theorem B1325123 : Blo 1323480 1325123 := bstep (se 1 (by rfl) ⟨993842, by rfl⟩ : syracuseStep 1325123 = 1987685) B1987685
theorem B11319365 : Blo 1323480 11319365 := bstep (se 4 (by rfl) ⟨1061190, by rfl⟩ : syracuseStep 11319365 = 2122381) B2122381
theorem B1325139 : Blo 1323480 1325139 := bstep (se 1 (by rfl) ⟨993854, by rfl⟩ : syracuseStep 1325139 = 1987709) B1987709
theorem B1325155 : Blo 1323480 1325155 := bstep (se 1 (by rfl) ⟨993866, by rfl⟩ : syracuseStep 1325155 = 1987733) B1987733
theorem B2979953 : Blo 1323480 2979953 := bstep (se 2 (by rfl) ⟨1117482, by rfl⟩ : syracuseStep 2979953 = 2234965) B2234965
theorem B1325171 : Blo 1323480 1325171 := bstep (se 1 (by rfl) ⟨993878, by rfl⟩ : syracuseStep 1325171 = 1987757) B1987757
theorem B1489027 : Blo 1323480 1489027 := bstep (se 1 (by rfl) ⟨1116770, by rfl⟩ : syracuseStep 1489027 = 2233541) B2233541
theorem B2979971 : Blo 1323480 2979971 := bstep (se 1 (by rfl) ⟨2234978, by rfl⟩ : syracuseStep 2979971 = 4469957) B4469957
theorem B1325187 : Blo 1323480 1325187 := bstep (se 1 (by rfl) ⟨993890, by rfl⟩ : syracuseStep 1325187 = 1987781) B1987781
theorem B2234513 : Blo 1323480 2234513 := bstep (se 2 (by rfl) ⟨837942, by rfl⟩ : syracuseStep 2234513 = 1675885) B1675885
theorem B4470929 : Blo 1323480 4470929 := bstep (se 2 (by rfl) ⟨1676598, by rfl⟩ : syracuseStep 4470929 = 3353197) B3353197
theorem B1325203 : Blo 1323480 1325203 := bstep (se 1 (by rfl) ⟨993902, by rfl⟩ : syracuseStep 1325203 = 1987805) B1987805
theorem B6363299 : Blo 1323480 6363299 := bstep (se 1 (by rfl) ⟨4772474, by rfl⟩ : syracuseStep 6363299 = 9544949) B9544949
theorem B1325219 : Blo 1323480 1325219 := bstep (se 1 (by rfl) ⟨993914, by rfl⟩ : syracuseStep 1325219 = 1987829) B1987829
theorem B4241585 : Blo 1323480 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1325235 : Blo 1323480 1325235 := bstep (se 1 (by rfl) ⟨993926, by rfl⟩ : syracuseStep 1325235 = 1987853) B1987853
theorem B1325251 : Blo 1323480 1325251 := bstep (se 1 (by rfl) ⟨993938, by rfl⟩ : syracuseStep 1325251 = 1987877) B1987877
theorem B1325267 : Blo 1323480 1325267 := bstep (se 1 (by rfl) ⟨993950, by rfl⟩ : syracuseStep 1325267 = 1987901) B1987901
theorem B1325283 : Blo 1323480 1325283 := bstep (se 1 (by rfl) ⟨993962, by rfl⟩ : syracuseStep 1325283 = 1987925) B1987925
theorem B1325299 : Blo 1323480 1325299 := bstep (se 1 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 1325299 = 1987949) B1987949
theorem B1325315 : Blo 1323480 1325315 := bstep (se 1 (by rfl) ⟨993986, by rfl⟩ : syracuseStep 1325315 = 1987973) B1987973
theorem B2234641 : Blo 1323480 2234641 := bstep (se 2 (by rfl) ⟨837990, by rfl⟩ : syracuseStep 2234641 = 1675981) B1675981
theorem B1489171 : Blo 1323480 1489171 := bstep (se 1 (by rfl) ⟨1116878, by rfl⟩ : syracuseStep 1489171 = 2233757) B2233757
theorem B1325331 : Blo 1323480 1325331 := bstep (se 1 (by rfl) ⟨993998, by rfl⟩ : syracuseStep 1325331 = 1987997) B1987997
theorem B1325347 : Blo 1323480 1325347 := bstep (se 1 (by rfl) ⟨994010, by rfl⟩ : syracuseStep 1325347 = 1988021) B1988021
theorem B2234675 : Blo 1323480 2234675 := bstep (se 1 (by rfl) ⟨1676006, by rfl⟩ : syracuseStep 2234675 = 3352013) B3352013
theorem B1325363 : Blo 1323480 1325363 := bstep (se 1 (by rfl) ⟨994022, by rfl⟩ : syracuseStep 1325363 = 1988045) B1988045
theorem B1325379 : Blo 1323480 1325379 := bstep (se 1 (by rfl) ⟨994034, by rfl⟩ : syracuseStep 1325379 = 1988069) B1988069
theorem B1325395 : Blo 1323480 1325395 := bstep (se 1 (by rfl) ⟨994046, by rfl⟩ : syracuseStep 1325395 = 1988093) B1988093
theorem B1325411 : Blo 1323480 1325411 := bstep (se 1 (by rfl) ⟨994058, by rfl⟩ : syracuseStep 1325411 = 1988117) B1988117
theorem B1325427 : Blo 1323480 1325427 := bstep (se 1 (by rfl) ⟨994070, by rfl⟩ : syracuseStep 1325427 = 1988141) B1988141
theorem B1325443 : Blo 1323480 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B2980241 : Blo 1323480 2980241 := bstep (se 2 (by rfl) ⟨1117590, by rfl⟩ : syracuseStep 2980241 = 2235181) B2235181
theorem B2685329 : Blo 1323480 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B1325459 : Blo 1323480 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B1489315 : Blo 1323480 1489315 := bstep (se 1 (by rfl) ⟨1116986, by rfl⟩ : syracuseStep 1489315 = 2233973) B2233973
theorem B2980259 : Blo 1323480 2980259 := bstep (se 1 (by rfl) ⟨2235194, by rfl⟩ : syracuseStep 2980259 = 4470389) B4470389
theorem B1325475 : Blo 1323480 1325475 := bstep (se 1 (by rfl) ⟨994106, by rfl⟩ : syracuseStep 1325475 = 1988213) B1988213
theorem B2234803 : Blo 1323480 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B2513425 : Blo 1323480 2513425 := bstep (se 2 (by rfl) ⟨942534, by rfl⟩ : syracuseStep 2513425 = 1885069) B1885069
theorem B1489459 : Blo 1323480 1489459 := bstep (se 1 (by rfl) ⟨1117094, by rfl⟩ : syracuseStep 1489459 = 2234189) B2234189
theorem B2234945 : Blo 1323480 2234945 := bstep (se 2 (by rfl) ⟨838104, by rfl⟩ : syracuseStep 2234945 = 1676209) B1676209
theorem B3578513 : Blo 1323480 3578513 := bstep (se 2 (by rfl) ⟨1341942, by rfl⟩ : syracuseStep 3578513 = 2683885) B2683885
theorem B4471469 : Blo 1323480 4471469 := bstep (se 3 (by rfl) ⟨838400, by rfl⟩ : syracuseStep 4471469 = 1676801) B1676801
theorem B2513585 : Blo 1323480 2513585 := bstep (se 2 (by rfl) ⟨942594, by rfl⟩ : syracuseStep 2513585 = 1885189) B1885189
theorem B2980529 : Blo 1323480 2980529 := bstep (se 2 (by rfl) ⟨1117698, by rfl⟩ : syracuseStep 2980529 = 2235397) B2235397
theorem B2235073 : Blo 1323480 2235073 := bstep (se 2 (by rfl) ⟨838152, by rfl⟩ : syracuseStep 2235073 = 1676305) B1676305
theorem B1489603 : Blo 1323480 1489603 := bstep (se 1 (by rfl) ⟨1117202, by rfl⟩ : syracuseStep 1489603 = 2234405) B2234405
theorem B2980547 : Blo 1323480 2980547 := bstep (se 1 (by rfl) ⟨2235410, by rfl⟩ : syracuseStep 2980547 = 4470821) B4470821
theorem B12729059 : Blo 1323480 12729059 := bstep (se 1 (by rfl) ⟨9546794, by rfl⟩ : syracuseStep 12729059 = 19093589) B19093589
theorem B2235107 : Blo 1323480 2235107 := bstep (se 1 (by rfl) ⟨1676330, by rfl⟩ : syracuseStep 2235107 = 3352661) B3352661
theorem B4471523 : Blo 1323480 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B8485681 : Blo 1323480 8485681 := bstep (se 2 (by rfl) ⟨3182130, by rfl⟩ : syracuseStep 8485681 = 6364261) B6364261
theorem B7543601 : Blo 1323480 7543601 := bstep (se 2 (by rfl) ⟨2828850, by rfl⟩ : syracuseStep 7543601 = 5657701) B5657701
theorem B1489747 : Blo 1323480 1489747 := bstep (se 1 (by rfl) ⟨1117310, by rfl⟩ : syracuseStep 1489747 = 2234621) B2234621
theorem B2235235 : Blo 1323480 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B5733233 : Blo 1323480 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B5028749 : Blo 1323480 5028749 := bstep (se 3 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 5028749 = 1885781) B1885781
theorem B6364109 : Blo 1323480 6364109 := bstep (se 3 (by rfl) ⟨1193270, by rfl⟩ : syracuseStep 6364109 = 2386541) B2386541
theorem B2980817 : Blo 1323480 2980817 := bstep (se 2 (by rfl) ⟨1117806, by rfl⟩ : syracuseStep 2980817 = 2235613) B2235613
theorem B1489891 : Blo 1323480 1489891 := bstep (se 1 (by rfl) ⟨1117418, by rfl⟩ : syracuseStep 1489891 = 2234837) B2234837
theorem B2980835 : Blo 1323480 2980835 := bstep (se 1 (by rfl) ⟨2235626, by rfl⟩ : syracuseStep 2980835 = 4471253) B4471253
theorem B2235377 : Blo 1323480 2235377 := bstep (se 2 (by rfl) ⟨838266, by rfl⟩ : syracuseStep 2235377 = 1676533) B1676533
theorem B4471793 : Blo 1323480 4471793 := bstep (se 2 (by rfl) ⟨1676922, by rfl⟩ : syracuseStep 4471793 = 3353845) B3353845
theorem B2513987 : Blo 1323480 2513987 := bstep (se 1 (by rfl) ⟨1885490, by rfl⟩ : syracuseStep 2513987 = 3770981) B3770981
theorem B7642181 : Blo 1323480 7642181 := bstep (se 4 (by rfl) ⟨716454, by rfl⟩ : syracuseStep 7642181 = 1432909) B1432909
theorem B2235505 : Blo 1323480 2235505 := bstep (se 2 (by rfl) ⟨838314, by rfl⟩ : syracuseStep 2235505 = 1676629) B1676629
theorem B6798449 : Blo 1323480 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B1490035 : Blo 1323480 1490035 := bstep (se 1 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 1490035 = 2235053) B2235053
theorem B10747021 : Blo 1323480 10747021 := bstep (se 3 (by rfl) ⟨2015066, by rfl⟩ : syracuseStep 10747021 = 4030133) B4030133
theorem B2235539 : Blo 1323480 2235539 := bstep (se 1 (by rfl) ⟨1676654, by rfl⟩ : syracuseStep 2235539 = 3353309) B3353309
theorem B9067697 : Blo 1323480 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B2981105 : Blo 1323480 2981105 := bstep (se 2 (by rfl) ⟨1117914, by rfl⟩ : syracuseStep 2981105 = 2235829) B2235829
theorem B1490179 : Blo 1323480 1490179 := bstep (se 1 (by rfl) ⟨1117634, by rfl⟩ : syracuseStep 1490179 = 2235269) B2235269
theorem B2981123 : Blo 1323480 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B2235667 : Blo 1323480 2235667 := bstep (se 1 (by rfl) ⟨1676750, by rfl⟩ : syracuseStep 2235667 = 3353501) B3353501
theorem B4029745 : Blo 1323480 4029745 := bstep (se 2 (by rfl) ⟨1511154, by rfl⟩ : syracuseStep 4029745 = 3022309) B3022309
theorem B1490323 : Blo 1323480 1490323 := bstep (se 1 (by rfl) ⟨1117742, by rfl⟩ : syracuseStep 1490323 = 2235485) B2235485
theorem B2235809 : Blo 1323480 2235809 := bstep (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) B1676857
theorem B2121203 : Blo 1323480 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B4472333 : Blo 1323480 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B2981393 : Blo 1323480 2981393 := bstep (se 2 (by rfl) ⟨1118022, by rfl⟩ : syracuseStep 2981393 = 2236045) B2236045
theorem B2235937 : Blo 1323480 2235937 := bstep (se 2 (by rfl) ⟨838476, by rfl⟩ : syracuseStep 2235937 = 1676953) B1676953
theorem B1490467 : Blo 1323480 1490467 := bstep (se 1 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 1490467 = 2235701) B2235701
theorem B2981411 : Blo 1323480 2981411 := bstep (se 1 (by rfl) ⟨2236058, by rfl⟩ : syracuseStep 2981411 = 4472117) B4472117
theorem B2235971 : Blo 1323480 2235971 := bstep (se 1 (by rfl) ⟨1676978, by rfl⟩ : syracuseStep 2235971 = 3353957) B3353957
theorem B4472387 : Blo 1323480 4472387 := bstep (se 1 (by rfl) ⟨3354290, by rfl⟩ : syracuseStep 4472387 = 6708581) B6708581
theorem B6700643 : Blo 1323480 6700643 := bstep (se 1 (by rfl) ⟨5025482, by rfl⟩ : syracuseStep 6700643 = 10050965) B10050965
theorem B2121331 : Blo 1323480 2121331 := bstep (se 1 (by rfl) ⟨1590998, by rfl⟩ : syracuseStep 2121331 = 3181997) B3181997
theorem B5029553 : Blo 1323480 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B2014897 : Blo 1323480 2014897 := bstep (se 2 (by rfl) ⟨755586, by rfl⟩ : syracuseStep 2014897 = 1511173) B1511173
theorem B1490611 : Blo 1323480 1490611 := bstep (se 1 (by rfl) ⟨1117958, by rfl⟩ : syracuseStep 1490611 = 2235917) B2235917
theorem B2236099 : Blo 1323480 2236099 := bstep (se 1 (by rfl) ⟨1677074, by rfl⟩ : syracuseStep 2236099 = 3354149) B3354149
theorem B5660401 : Blo 1323480 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B2981681 : Blo 1323480 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B1490755 : Blo 1323480 1490755 := bstep (se 1 (by rfl) ⟨1118066, by rfl⟩ : syracuseStep 1490755 = 2236133) B2236133
theorem B2981699 : Blo 1323480 2981699 := bstep (se 1 (by rfl) ⟨2236274, by rfl⟩ : syracuseStep 2981699 = 4472549) B4472549
theorem B2236241 : Blo 1323480 2236241 := bstep (se 2 (by rfl) ⟨838590, by rfl⟩ : syracuseStep 2236241 = 1677181) B1677181
theorem B4472657 : Blo 1323480 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B4841329 : Blo 1323480 4841329 := bstep (se 2 (by rfl) ⟨1815498, by rfl⟩ : syracuseStep 4841329 = 3630997) B3630997
theorem B2514883 : Blo 1323480 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B2236369 : Blo 1323480 2236369 := bstep (se 2 (by rfl) ⟨838638, by rfl⟩ : syracuseStep 2236369 = 1677277) B1677277
theorem B1490899 : Blo 1323480 1490899 := bstep (se 1 (by rfl) ⟨1118174, by rfl⟩ : syracuseStep 1490899 = 2236349) B2236349
theorem B2015201 : Blo 1323480 2015201 := bstep (se 2 (by rfl) ⟨755700, by rfl⟩ : syracuseStep 2015201 = 1511401) B1511401
theorem B1343459 : Blo 1323480 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B2121715 : Blo 1323480 2121715 := bstep (se 1 (by rfl) ⟨1591286, by rfl⟩ : syracuseStep 2121715 = 3182573) B3182573
theorem B2236403 : Blo 1323480 2236403 := bstep (se 1 (by rfl) ⟨1677302, by rfl⟩ : syracuseStep 2236403 = 3354605) B3354605
theorem B5660675 : Blo 1323480 5660675 := bstep (se 1 (by rfl) ⟨4245506, by rfl⟩ : syracuseStep 5660675 = 8491013) B8491013
theorem B16105547 : Blo 1323480 16105547 := bstep (se 1 (by rfl) ⟨12079160, by rfl⟩ : syracuseStep 16105547 = 24158321) B24158321
theorem B10747997 : Blo 1323480 10747997 := bstep (se 3 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 10747997 = 4030499) B4030499
theorem B5374097 : Blo 1323480 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B5030039 : Blo 1323480 5030039 := bstep (se 1 (by rfl) ⟨3772529, by rfl⟩ : syracuseStep 5030039 = 7545059) B7545059
theorem B2982041 : Blo 1323480 2982041 := bstep (se 2 (by rfl) ⟨1118265, by rfl⟩ : syracuseStep 2982041 = 2236531) B2236531
theorem B1491115 : Blo 1323480 1491115 := bstep (se 1 (by rfl) ⟨1118336, by rfl⟩ : syracuseStep 1491115 = 2236673) B2236673
theorem B4473035 : Blo 1323480 4473035 := bstep (se 1 (by rfl) ⟨3354776, by rfl⟩ : syracuseStep 4473035 = 6709553) B6709553
theorem B2236619 : Blo 1323480 2236619 := bstep (se 1 (by rfl) ⟨1677464, by rfl⟩ : syracuseStep 2236619 = 3354929) B3354929
theorem B2515187 : Blo 1323480 2515187 := bstep (se 1 (by rfl) ⟨1886390, by rfl⟩ : syracuseStep 2515187 = 3772781) B3772781
theorem B2982131 : Blo 1323480 2982131 := bstep (se 1 (by rfl) ⟨2236598, by rfl⟩ : syracuseStep 2982131 = 4473197) B4473197
theorem B2982167 : Blo 1323480 2982167 := bstep (se 1 (by rfl) ⟨2236625, by rfl⟩ : syracuseStep 2982167 = 4473251) B4473251
theorem B2515225 : Blo 1323480 2515225 := bstep (se 2 (by rfl) ⟨943209, by rfl⟩ : syracuseStep 2515225 = 1886419) B1886419
theorem B18129197 : Blo 1323480 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B2236747 : Blo 1323480 2236747 := bstep (se 1 (by rfl) ⟨1677560, by rfl⟩ : syracuseStep 2236747 = 3355121) B3355121
theorem B2826647 : Blo 1323480 2826647 := bstep (se 1 (by rfl) ⟨2119985, by rfl⟩ : syracuseStep 2826647 = 4239971) B4239971
theorem B4473305 : Blo 1323480 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B16114211 : Blo 1323480 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B3351091 : Blo 1323480 3351091 := bstep (se 1 (by rfl) ⟨2513318, by rfl⟩ : syracuseStep 3351091 = 5026637) B5026637
theorem B4776499 : Blo 1323480 4776499 := bstep (se 1 (by rfl) ⟨3582374, by rfl⟩ : syracuseStep 4776499 = 7164749) B7164749
theorem B3351233 : Blo 1323480 3351233 := bstep (se 2 (by rfl) ⟨1256712, by rfl⟩ : syracuseStep 3351233 = 2513425) B2513425
theorem B1884875 : Blo 1323480 1884875 := bstep (se 1 (by rfl) ⟨1413656, by rfl⟩ : syracuseStep 1884875 = 2827313) B2827313
theorem B2515673 : Blo 1323480 2515673 := bstep (se 2 (by rfl) ⟨943377, by rfl⟩ : syracuseStep 2515673 = 1886755) B1886755
theorem B19079981 : Blo 1323480 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B5030707 : Blo 1323480 5030707 := bstep (se 1 (by rfl) ⟨3773030, by rfl⟩ : syracuseStep 5030707 = 7546061) B7546061
theorem B5096267 : Blo 1323480 5096267 := bstep (se 1 (by rfl) ⟨3822200, by rfl⟩ : syracuseStep 5096267 = 7644401) B7644401
theorem B45892453 : Blo 1323480 45892453 := bstep (se 4 (by rfl) ⟨4302417, by rfl⟩ : syracuseStep 45892453 = 8604835) B8604835
theorem B3769409 : Blo 1323480 3769409 := bstep (se 2 (by rfl) ⟨1413528, by rfl⟩ : syracuseStep 3769409 = 2827057) B2827057
theorem B11314241 : Blo 1323480 11314241 := bstep (se 2 (by rfl) ⟨4242840, by rfl⟩ : syracuseStep 11314241 = 8485681) B8485681
theorem B1590359 : Blo 1323480 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B3769523 : Blo 1323480 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B10052909 : Blo 1323480 10052909 := bstep (se 3 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 10052909 = 3769841) B3769841
theorem B7538021 : Blo 1323480 7538021 := bstep (se 4 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 7538021 = 1413379) B1413379
theorem B21480805 : Blo 1323480 21480805 := bstep (se 4 (by rfl) ⟨2013825, by rfl⟩ : syracuseStep 21480805 = 4027651) B4027651
theorem B7546243 : Blo 1323480 7546243 := bstep (se 1 (by rfl) ⟨5659682, by rfl⟩ : syracuseStep 7546243 = 11319365) B11319365
theorem B2827723 : Blo 1323480 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B4244957 : Blo 1323480 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B14329361 : Blo 1323480 14329361 := bstep (se 2 (by rfl) ⟨5373510, by rfl⟩ : syracuseStep 14329361 = 10747021) B10747021
theorem B2295577 : Blo 1323480 2295577 := bstep (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) B1721683
theorem B1509239 : Blo 1323480 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B3352499 : Blo 1323480 3352499 := bstep (se 1 (by rfl) ⟨2514374, by rfl⟩ : syracuseStep 3352499 = 5028749) B5028749
theorem B5031953 : Blo 1323480 5031953 := bstep (se 2 (by rfl) ⟨1886982, by rfl⟩ : syracuseStep 5031953 = 3773965) B3773965
theorem B1722391 : Blo 1323480 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B6703235 : Blo 1323480 6703235 := bstep (se 1 (by rfl) ⟨5027426, by rfl⟩ : syracuseStep 6703235 = 10054853) B10054853
theorem B2828441 : Blo 1323480 2828441 := bstep (se 2 (by rfl) ⟨1060665, by rfl⟩ : syracuseStep 2828441 = 2121331) B2121331
theorem B7547201 : Blo 1323480 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B10733917 : Blo 1323480 10733917 := bstep (se 3 (by rfl) ⟨2012609, by rfl⟩ : syracuseStep 10733917 = 4025219) B4025219
theorem B4467095 : Blo 1323480 4467095 := bstep (se 1 (by rfl) ⟨3350321, by rfl⟩ : syracuseStep 4467095 = 6700643) B6700643
theorem B4770227 : Blo 1323480 4770227 := bstep (se 1 (by rfl) ⟨3577670, by rfl⟩ : syracuseStep 4770227 = 7155341) B7155341
theorem B3353035 : Blo 1323480 3353035 := bstep (se 1 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 3353035 = 5029553) B5029553
theorem B1886743 : Blo 1323480 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B5368385 : Blo 1323480 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B3353177 : Blo 1323480 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B3582557 : Blo 1323480 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B2828953 : Blo 1323480 2828953 := bstep (se 2 (by rfl) ⟨1060857, by rfl⟩ : syracuseStep 2828953 = 2121715) B2121715
theorem B4655819 : Blo 1323480 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B5032651 : Blo 1323480 5032651 := bstep (se 1 (by rfl) ⟨3774488, by rfl⟩ : syracuseStep 5032651 = 7548977) B7548977
theorem B5737177 : Blo 1323480 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B1985291 : Blo 1323480 1985291 := bstep (se 1 (by rfl) ⟨1488968, by rfl⟩ : syracuseStep 1985291 = 2977937) B2977937
theorem B1985303 : Blo 1323480 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B8481581 : Blo 1323480 8481581 := bstep (se 3 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 8481581 = 3180593) B3180593
theorem B2829107 : Blo 1323480 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B1985369 : Blo 1323480 1985369 := bstep (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) B1489027
theorem B4467635 : Blo 1323480 4467635 := bstep (se 1 (by rfl) ⟨3350726, by rfl⟩ : syracuseStep 4467635 = 6701453) B6701453
theorem B15084467 : Blo 1323480 15084467 := bstep (se 1 (by rfl) ⟨11313350, by rfl⟩ : syracuseStep 15084467 = 22626701) B22626701
theorem B1985483 : Blo 1323480 1985483 := bstep (se 1 (by rfl) ⟨1489112, by rfl⟩ : syracuseStep 1985483 = 2978225) B2978225
theorem B1985495 : Blo 1323480 1985495 := bstep (se 1 (by rfl) ⟨1489121, by rfl⟩ : syracuseStep 1985495 = 2978243) B2978243
theorem B1985561 : Blo 1323480 1985561 := bstep (se 2 (by rfl) ⟨744585, by rfl⟩ : syracuseStep 1985561 = 1489171) B1489171
theorem B16968797 : Blo 1323480 16968797 := bstep (se 3 (by rfl) ⟨3181649, by rfl⟩ : syracuseStep 16968797 = 6363299) B6363299
theorem B1985675 : Blo 1323480 1985675 := bstep (se 1 (by rfl) ⟨1489256, by rfl⟩ : syracuseStep 1985675 = 2978513) B2978513
theorem B1985687 : Blo 1323480 1985687 := bstep (se 1 (by rfl) ⟨1489265, by rfl⟩ : syracuseStep 1985687 = 2978531) B2978531
theorem B5655703 : Blo 1323480 5655703 := bstep (se 1 (by rfl) ⟨4241777, by rfl⟩ : syracuseStep 5655703 = 8483555) B8483555
theorem B4467905 : Blo 1323480 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B1985753 : Blo 1323480 1985753 := bstep (se 2 (by rfl) ⟨744657, by rfl⟩ : syracuseStep 1985753 = 1489315) B1489315
theorem B1985867 : Blo 1323480 1985867 := bstep (se 1 (by rfl) ⟨1489400, by rfl⟩ : syracuseStep 1985867 = 2978801) B2978801
theorem B1985879 : Blo 1323480 1985879 := bstep (se 1 (by rfl) ⟨1489409, by rfl⟩ : syracuseStep 1985879 = 2978819) B2978819
theorem B11316631 : Blo 1323480 11316631 := bstep (se 1 (by rfl) ⟨8487473, by rfl⟩ : syracuseStep 11316631 = 16974947) B16974947
theorem B3354007 : Blo 1323480 3354007 := bstep (se 1 (by rfl) ⟨2515505, by rfl⟩ : syracuseStep 3354007 = 5031011) B5031011
theorem B1985945 : Blo 1323480 1985945 := bstep (se 2 (by rfl) ⟨744729, by rfl⟩ : syracuseStep 1985945 = 1489459) B1489459
theorem B1986059 : Blo 1323480 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B1986071 : Blo 1323480 1986071 := bstep (se 1 (by rfl) ⟨1489553, by rfl⟩ : syracuseStep 1986071 = 2979107) B2979107
theorem B22613579 : Blo 1323480 22613579 := bstep (se 1 (by rfl) ⟨16960184, by rfl⟩ : syracuseStep 22613579 = 33920369) B33920369
theorem B1986137 : Blo 1323480 1986137 := bstep (se 2 (by rfl) ⟨744801, by rfl⟩ : syracuseStep 1986137 = 1489603) B1489603
theorem B183480005 : Blo 1323480 183480005 := bstep (se 4 (by rfl) ⟨17201250, by rfl⟩ : syracuseStep 183480005 = 34402501) B34402501
theorem B1986251 : Blo 1323480 1986251 := bstep (se 1 (by rfl) ⟨1489688, by rfl⟩ : syracuseStep 1986251 = 2979377) B2979377
theorem B1986263 : Blo 1323480 1986263 := bstep (se 1 (by rfl) ⟨1489697, by rfl⟩ : syracuseStep 1986263 = 2979395) B2979395
theorem B4468445 : Blo 1323480 4468445 := bstep (se 3 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 4468445 = 1675667) B1675667
theorem B2830081 : Blo 1323480 2830081 := bstep (se 2 (by rfl) ⟨1061280, by rfl⟩ : syracuseStep 2830081 = 2122561) B2122561
theorem B1986329 : Blo 1323480 1986329 := bstep (se 2 (by rfl) ⟨744873, by rfl⟩ : syracuseStep 1986329 = 1489747) B1489747
theorem B24162113 : Blo 1323480 24162113 := bstep (se 2 (by rfl) ⟨9060792, by rfl⟩ : syracuseStep 24162113 = 18121585) B18121585
theorem B3354443 : Blo 1323480 3354443 := bstep (se 1 (by rfl) ⟨2515832, by rfl⟩ : syracuseStep 3354443 = 5031665) B5031665
theorem B18124661 : Blo 1323480 18124661 := bstep (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) B1699187
theorem B1986443 : Blo 1323480 1986443 := bstep (se 1 (by rfl) ⟨1489832, by rfl⟩ : syracuseStep 1986443 = 2979665) B2979665
theorem B1986455 : Blo 1323480 1986455 := bstep (se 1 (by rfl) ⟨1489841, by rfl⟩ : syracuseStep 1986455 = 2979683) B2979683
theorem B1986521 : Blo 1323480 1986521 := bstep (se 2 (by rfl) ⟨744945, by rfl⟩ : syracuseStep 1986521 = 1489891) B1489891
theorem B3772439 : Blo 1323480 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B1986635 : Blo 1323480 1986635 := bstep (se 1 (by rfl) ⟨1489976, by rfl⟩ : syracuseStep 1986635 = 2979953) B2979953
theorem B1986647 : Blo 1323480 1986647 := bstep (se 1 (by rfl) ⟨1489985, by rfl⟩ : syracuseStep 1986647 = 2979971) B2979971
theorem B2830423 : Blo 1323480 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B1986713 : Blo 1323480 1986713 := bstep (se 2 (by rfl) ⟨745017, by rfl⟩ : syracuseStep 1986713 = 1490035) B1490035
theorem B3354817 : Blo 1323480 3354817 := bstep (se 2 (by rfl) ⟨1258056, by rfl⟩ : syracuseStep 3354817 = 2516113) B2516113
theorem B2978009 : Blo 1323480 2978009 := bstep (se 2 (by rfl) ⟨1116753, by rfl⟩ : syracuseStep 2978009 = 2233507) B2233507
theorem B1986827 : Blo 1323480 1986827 := bstep (se 1 (by rfl) ⟨1490120, by rfl⟩ : syracuseStep 1986827 = 2980241) B2980241
theorem B1790219 : Blo 1323480 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B1986839 : Blo 1323480 1986839 := bstep (se 1 (by rfl) ⟨1490129, by rfl⟩ : syracuseStep 1986839 = 2980259) B2980259
theorem B2978099 : Blo 1323480 2978099 := bstep (se 1 (by rfl) ⟨2233574, by rfl⟩ : syracuseStep 2978099 = 4467149) B4467149
theorem B2978135 : Blo 1323480 2978135 := bstep (se 1 (by rfl) ⟨2233601, by rfl⟩ : syracuseStep 2978135 = 4467203) B4467203
theorem B3019097 : Blo 1323480 3019097 := bstep (se 2 (by rfl) ⟨1132161, by rfl⟩ : syracuseStep 3019097 = 2264323) B2264323
theorem B1986905 : Blo 1323480 1986905 := bstep (se 2 (by rfl) ⟨745089, by rfl⟩ : syracuseStep 1986905 = 1490179) B1490179
theorem B15085925 : Blo 1323480 15085925 := bstep (se 4 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 15085925 = 2828611) B2828611
theorem B1675723 : Blo 1323480 1675723 := bstep (se 1 (by rfl) ⟨1256792, by rfl⟩ : syracuseStep 1675723 = 2513585) B2513585
theorem B1987019 : Blo 1323480 1987019 := bstep (se 1 (by rfl) ⟨1490264, by rfl⟩ : syracuseStep 1987019 = 2980529) B2980529
theorem B1987031 : Blo 1323480 1987031 := bstep (se 1 (by rfl) ⟨1490273, by rfl⟩ : syracuseStep 1987031 = 2980547) B2980547
theorem B1323499 : Blo 1323480 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B1323511 : Blo 1323480 1323511 := bstep (se 1 (by rfl) ⟨992633, by rfl⟩ : syracuseStep 1323511 = 1985267) B1985267
theorem B1323531 : Blo 1323480 1323531 := bstep (se 1 (by rfl) ⟨992648, by rfl⟩ : syracuseStep 1323531 = 1985297) B1985297
theorem B2978315 : Blo 1323480 2978315 := bstep (se 1 (by rfl) ⟨2233736, by rfl⟩ : syracuseStep 2978315 = 4467473) B4467473
theorem B2830859 : Blo 1323480 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B1323543 : Blo 1323480 1323543 := bstep (se 1 (by rfl) ⟨992657, by rfl⟩ : syracuseStep 1323543 = 1985315) B1985315
theorem B1987097 : Blo 1323480 1987097 := bstep (se 2 (by rfl) ⟨745161, by rfl⟩ : syracuseStep 1987097 = 1490323) B1490323
theorem B1323563 : Blo 1323480 1323563 := bstep (se 1 (by rfl) ⟨992672, by rfl⟩ : syracuseStep 1323563 = 1985345) B1985345
theorem B1323575 : Blo 1323480 1323575 := bstep (se 1 (by rfl) ⟨992681, by rfl⟩ : syracuseStep 1323575 = 1985363) B1985363
theorem B2978369 : Blo 1323480 2978369 := bstep (se 2 (by rfl) ⟨1116888, by rfl⟩ : syracuseStep 2978369 = 2233777) B2233777
theorem B1323595 : Blo 1323480 1323595 := bstep (se 1 (by rfl) ⟨992696, by rfl⟩ : syracuseStep 1323595 = 1985393) B1985393
theorem B3822155 : Blo 1323480 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B18133579 : Blo 1323480 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1323607 : Blo 1323480 1323607 := bstep (se 1 (by rfl) ⟨992705, by rfl⟩ : syracuseStep 1323607 = 1985411) B1985411
theorem B1323627 : Blo 1323480 1323627 := bstep (se 1 (by rfl) ⟨992720, by rfl⟩ : syracuseStep 1323627 = 1985441) B1985441
theorem B1323639 : Blo 1323480 1323639 := bstep (se 1 (by rfl) ⟨992729, by rfl⟩ : syracuseStep 1323639 = 1985459) B1985459
theorem B1323659 : Blo 1323480 1323659 := bstep (se 1 (by rfl) ⟨992744, by rfl⟩ : syracuseStep 1323659 = 1985489) B1985489
theorem B1987211 : Blo 1323480 1987211 := bstep (se 1 (by rfl) ⟨1490408, by rfl⟩ : syracuseStep 1987211 = 2980817) B2980817
theorem B1323671 : Blo 1323480 1323671 := bstep (se 1 (by rfl) ⟨992753, by rfl⟩ : syracuseStep 1323671 = 1985507) B1985507
theorem B1987223 : Blo 1323480 1987223 := bstep (se 1 (by rfl) ⟨1490417, by rfl⟩ : syracuseStep 1987223 = 2980835) B2980835
theorem B1323691 : Blo 1323480 1323691 := bstep (se 1 (by rfl) ⟨992768, by rfl⟩ : syracuseStep 1323691 = 1985537) B1985537
theorem B1323703 : Blo 1323480 1323703 := bstep (se 1 (by rfl) ⟨992777, by rfl⟩ : syracuseStep 1323703 = 1985555) B1985555
theorem B1323723 : Blo 1323480 1323723 := bstep (se 1 (by rfl) ⟨992792, by rfl⟩ : syracuseStep 1323723 = 1985585) B1985585
theorem B1323735 : Blo 1323480 1323735 := bstep (se 1 (by rfl) ⟨992801, by rfl⟩ : syracuseStep 1323735 = 1985603) B1985603
theorem B1675991 : Blo 1323480 1675991 := bstep (se 1 (by rfl) ⟨1256993, by rfl⟩ : syracuseStep 1675991 = 2513987) B2513987
theorem B1987289 : Blo 1323480 1987289 := bstep (se 2 (by rfl) ⟨745233, by rfl⟩ : syracuseStep 1987289 = 1490467) B1490467
theorem B1323755 : Blo 1323480 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B1323767 : Blo 1323480 1323767 := bstep (se 1 (by rfl) ⟨992825, by rfl⟩ : syracuseStep 1323767 = 1985651) B1985651
theorem B9679621 : Blo 1323480 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B1323787 : Blo 1323480 1323787 := bstep (se 1 (by rfl) ⟨992840, by rfl⟩ : syracuseStep 1323787 = 1985681) B1985681
theorem B1323799 : Blo 1323480 1323799 := bstep (se 1 (by rfl) ⟨992849, by rfl⟩ : syracuseStep 1323799 = 1985699) B1985699
theorem B2978585 : Blo 1323480 2978585 := bstep (se 2 (by rfl) ⟨1116969, by rfl⟩ : syracuseStep 2978585 = 2233939) B2233939
theorem B1323819 : Blo 1323480 1323819 := bstep (se 1 (by rfl) ⟨992864, by rfl⟩ : syracuseStep 1323819 = 1985729) B1985729
theorem B1323831 : Blo 1323480 1323831 := bstep (se 1 (by rfl) ⟨992873, by rfl⟩ : syracuseStep 1323831 = 1985747) B1985747
theorem B4469579 : Blo 1323480 4469579 := bstep (se 1 (by rfl) ⟨3352184, by rfl⟩ : syracuseStep 4469579 = 6704369) B6704369
theorem B1323851 : Blo 1323480 1323851 := bstep (se 1 (by rfl) ⟨992888, by rfl⟩ : syracuseStep 1323851 = 1985777) B1985777
theorem B1987403 : Blo 1323480 1987403 := bstep (se 1 (by rfl) ⟨1490552, by rfl⟩ : syracuseStep 1987403 = 2981105) B2981105
theorem B1323863 : Blo 1323480 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B1987415 : Blo 1323480 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B1323883 : Blo 1323480 1323883 := bstep (se 1 (by rfl) ⟨992912, by rfl⟩ : syracuseStep 1323883 = 1985825) B1985825
theorem B2978675 : Blo 1323480 2978675 := bstep (se 1 (by rfl) ⟨2234006, by rfl⟩ : syracuseStep 2978675 = 4468013) B4468013
theorem B1323895 : Blo 1323480 1323895 := bstep (se 1 (by rfl) ⟨992921, by rfl⟩ : syracuseStep 1323895 = 1985843) B1985843
theorem B1323915 : Blo 1323480 1323915 := bstep (se 1 (by rfl) ⟨992936, by rfl⟩ : syracuseStep 1323915 = 1985873) B1985873
theorem B2978711 : Blo 1323480 2978711 := bstep (se 1 (by rfl) ⟨2234033, by rfl⟩ : syracuseStep 2978711 = 4468067) B4468067
theorem B1323927 : Blo 1323480 1323927 := bstep (se 1 (by rfl) ⟨992945, by rfl⟩ : syracuseStep 1323927 = 1985891) B1985891
theorem B1987481 : Blo 1323480 1987481 := bstep (se 2 (by rfl) ⟨745305, by rfl⟩ : syracuseStep 1987481 = 1490611) B1490611
theorem B1323947 : Blo 1323480 1323947 := bstep (se 1 (by rfl) ⟨992960, by rfl⟩ : syracuseStep 1323947 = 1985921) B1985921
theorem B1323959 : Blo 1323480 1323959 := bstep (se 1 (by rfl) ⟨992969, by rfl⟩ : syracuseStep 1323959 = 1985939) B1985939
theorem B1323979 : Blo 1323480 1323979 := bstep (se 1 (by rfl) ⟨992984, by rfl⟩ : syracuseStep 1323979 = 1985969) B1985969
theorem B1323991 : Blo 1323480 1323991 := bstep (se 1 (by rfl) ⟨992993, by rfl⟩ : syracuseStep 1323991 = 1985987) B1985987
theorem B1324011 : Blo 1323480 1324011 := bstep (se 1 (by rfl) ⟨993008, by rfl⟩ : syracuseStep 1324011 = 1986017) B1986017
theorem B1324023 : Blo 1323480 1324023 := bstep (se 1 (by rfl) ⟨993017, by rfl⟩ : syracuseStep 1324023 = 1986035) B1986035
theorem B1414135 : Blo 1323480 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B5026819 : Blo 1323480 5026819 := bstep (se 1 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 5026819 = 7540229) B7540229
theorem B1324043 : Blo 1323480 1324043 := bstep (se 1 (by rfl) ⟨993032, by rfl⟩ : syracuseStep 1324043 = 1986065) B1986065
theorem B1987595 : Blo 1323480 1987595 := bstep (se 1 (by rfl) ⟨1490696, by rfl⟩ : syracuseStep 1987595 = 2981393) B2981393
theorem B1324055 : Blo 1323480 1324055 := bstep (se 1 (by rfl) ⟨993041, by rfl⟩ : syracuseStep 1324055 = 1986083) B1986083
theorem B1987607 : Blo 1323480 1987607 := bstep (se 1 (by rfl) ⟨1490705, by rfl⟩ : syracuseStep 1987607 = 2981411) B2981411
theorem B1324075 : Blo 1323480 1324075 := bstep (se 1 (by rfl) ⟨993056, by rfl⟩ : syracuseStep 1324075 = 1986113) B1986113
theorem B1324087 : Blo 1323480 1324087 := bstep (se 1 (by rfl) ⟨993065, by rfl⟩ : syracuseStep 1324087 = 1986131) B1986131
theorem B2978891 : Blo 1323480 2978891 := bstep (se 1 (by rfl) ⟨2234168, by rfl⟩ : syracuseStep 2978891 = 4468337) B4468337
theorem B1324107 : Blo 1323480 1324107 := bstep (se 1 (by rfl) ⟨993080, by rfl⟩ : syracuseStep 1324107 = 1986161) B1986161
theorem B1324119 : Blo 1323480 1324119 := bstep (se 1 (by rfl) ⟨993089, by rfl⟩ : syracuseStep 1324119 = 1986179) B1986179
theorem B2233433 : Blo 1323480 2233433 := bstep (se 2 (by rfl) ⟨837537, by rfl⟩ : syracuseStep 2233433 = 1675075) B1675075
theorem B4469849 : Blo 1323480 4469849 := bstep (se 2 (by rfl) ⟨1676193, by rfl⟩ : syracuseStep 4469849 = 3352387) B3352387
theorem B1987673 : Blo 1323480 1987673 := bstep (se 2 (by rfl) ⟨745377, by rfl⟩ : syracuseStep 1987673 = 1490755) B1490755
theorem B10056797 : Blo 1323480 10056797 := bstep (se 3 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 10056797 = 3771299) B3771299
theorem B1324139 : Blo 1323480 1324139 := bstep (se 1 (by rfl) ⟨993104, by rfl⟩ : syracuseStep 1324139 = 1986209) B1986209
theorem B1324151 : Blo 1323480 1324151 := bstep (se 1 (by rfl) ⟨993113, by rfl⟩ : syracuseStep 1324151 = 1986227) B1986227
theorem B2978945 : Blo 1323480 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B1324171 : Blo 1323480 1324171 := bstep (se 1 (by rfl) ⟨993128, by rfl⟩ : syracuseStep 1324171 = 1986257) B1986257
theorem B14316695 : Blo 1323480 14316695 := bstep (se 1 (by rfl) ⟨10737521, by rfl⟩ : syracuseStep 14316695 = 21475043) B21475043
theorem B1324183 : Blo 1323480 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B1324203 : Blo 1323480 1324203 := bstep (se 1 (by rfl) ⟨993152, by rfl⟩ : syracuseStep 1324203 = 1986305) B1986305
theorem B1324215 : Blo 1323480 1324215 := bstep (se 1 (by rfl) ⟨993161, by rfl⟩ : syracuseStep 1324215 = 1986323) B1986323
theorem B1324235 : Blo 1323480 1324235 := bstep (se 1 (by rfl) ⟨993176, by rfl⟩ : syracuseStep 1324235 = 1986353) B1986353
theorem B1987787 : Blo 1323480 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B1324247 : Blo 1323480 1324247 := bstep (se 1 (by rfl) ⟨993185, by rfl⟩ : syracuseStep 1324247 = 1986371) B1986371
theorem B1987799 : Blo 1323480 1987799 := bstep (se 1 (by rfl) ⟨1490849, by rfl⟩ : syracuseStep 1987799 = 2981699) B2981699
theorem B2233561 : Blo 1323480 2233561 := bstep (se 2 (by rfl) ⟨837585, by rfl⟩ : syracuseStep 2233561 = 1675171) B1675171
theorem B1324267 : Blo 1323480 1324267 := bstep (se 1 (by rfl) ⟨993200, by rfl⟩ : syracuseStep 1324267 = 1986401) B1986401
theorem B1324279 : Blo 1323480 1324279 := bstep (se 1 (by rfl) ⟨993209, by rfl⟩ : syracuseStep 1324279 = 1986419) B1986419
theorem B1324299 : Blo 1323480 1324299 := bstep (se 1 (by rfl) ⟨993224, by rfl⟩ : syracuseStep 1324299 = 1986449) B1986449
theorem B1324311 : Blo 1323480 1324311 := bstep (se 1 (by rfl) ⟨993233, by rfl⟩ : syracuseStep 1324311 = 1986467) B1986467
theorem B1987865 : Blo 1323480 1987865 := bstep (se 2 (by rfl) ⟨745449, by rfl⟩ : syracuseStep 1987865 = 1490899) B1490899
theorem B1324331 : Blo 1323480 1324331 := bstep (se 1 (by rfl) ⟨993248, by rfl⟩ : syracuseStep 1324331 = 1986497) B1986497
theorem B5027123 : Blo 1323480 5027123 := bstep (se 1 (by rfl) ⟨3770342, by rfl⟩ : syracuseStep 5027123 = 7540685) B7540685
theorem B1324343 : Blo 1323480 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B1324363 : Blo 1323480 1324363 := bstep (se 1 (by rfl) ⟨993272, by rfl⟩ : syracuseStep 1324363 = 1986545) B1986545
theorem B1324375 : Blo 1323480 1324375 := bstep (se 1 (by rfl) ⟨993281, by rfl⟩ : syracuseStep 1324375 = 1986563) B1986563
theorem B2979161 : Blo 1323480 2979161 := bstep (se 2 (by rfl) ⟨1117185, by rfl⟩ : syracuseStep 2979161 = 2234371) B2234371
theorem B1324395 : Blo 1323480 1324395 := bstep (se 1 (by rfl) ⟨993296, by rfl⟩ : syracuseStep 1324395 = 1986593) B1986593
theorem B1324407 : Blo 1323480 1324407 := bstep (se 1 (by rfl) ⟨993305, by rfl⟩ : syracuseStep 1324407 = 1986611) B1986611
theorem B1324427 : Blo 1323480 1324427 := bstep (se 1 (by rfl) ⟨993320, by rfl⟩ : syracuseStep 1324427 = 1986641) B1986641
theorem B1987979 : Blo 1323480 1987979 := bstep (se 1 (by rfl) ⟨1490984, by rfl⟩ : syracuseStep 1987979 = 2981969) B2981969
theorem B1324439 : Blo 1323480 1324439 := bstep (se 1 (by rfl) ⟨993329, by rfl⟩ : syracuseStep 1324439 = 1986659) B1986659
theorem B1676695 : Blo 1323480 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B1987991 : Blo 1323480 1987991 := bstep (se 1 (by rfl) ⟨1490993, by rfl⟩ : syracuseStep 1987991 = 2981987) B2981987
theorem B1324459 : Blo 1323480 1324459 := bstep (se 1 (by rfl) ⟨993344, by rfl⟩ : syracuseStep 1324459 = 1986689) B1986689
theorem B2979251 : Blo 1323480 2979251 := bstep (se 1 (by rfl) ⟨2234438, by rfl⟩ : syracuseStep 2979251 = 4468877) B4468877
theorem B1324471 : Blo 1323480 1324471 := bstep (se 1 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 1324471 = 1986707) B1986707
theorem B1324491 : Blo 1323480 1324491 := bstep (se 1 (by rfl) ⟨993368, by rfl⟩ : syracuseStep 1324491 = 1986737) B1986737
theorem B2979287 : Blo 1323480 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1324503 : Blo 1323480 1324503 := bstep (se 1 (by rfl) ⟨993377, by rfl⟩ : syracuseStep 1324503 = 1986755) B1986755
theorem B1988057 : Blo 1323480 1988057 := bstep (se 2 (by rfl) ⟨745521, by rfl⟩ : syracuseStep 1988057 = 1491043) B1491043
theorem B1324523 : Blo 1323480 1324523 := bstep (se 1 (by rfl) ⟨993392, by rfl⟩ : syracuseStep 1324523 = 1986785) B1986785
theorem B1324535 : Blo 1323480 1324535 := bstep (se 1 (by rfl) ⟨993401, by rfl⟩ : syracuseStep 1324535 = 1986803) B1986803
theorem B1324555 : Blo 1323480 1324555 := bstep (se 1 (by rfl) ⟨993416, by rfl⟩ : syracuseStep 1324555 = 1986833) B1986833
theorem B1324567 : Blo 1323480 1324567 := bstep (se 1 (by rfl) ⟨993425, by rfl⟩ : syracuseStep 1324567 = 1986851) B1986851
theorem B1324587 : Blo 1323480 1324587 := bstep (se 1 (by rfl) ⟨993440, by rfl⟩ : syracuseStep 1324587 = 1986881) B1986881
theorem B1324599 : Blo 1323480 1324599 := bstep (se 1 (by rfl) ⟨993449, by rfl⟩ : syracuseStep 1324599 = 1986899) B1986899
theorem B1324619 : Blo 1323480 1324619 := bstep (se 1 (by rfl) ⟨993464, by rfl⟩ : syracuseStep 1324619 = 1986929) B1986929
theorem B1988171 : Blo 1323480 1988171 := bstep (se 1 (by rfl) ⟨1491128, by rfl⟩ : syracuseStep 1988171 = 2982257) B2982257
theorem B1324631 : Blo 1323480 1324631 := bstep (se 1 (by rfl) ⟨993473, by rfl⟩ : syracuseStep 1324631 = 1986947) B1986947
theorem B1988183 : Blo 1323480 1988183 := bstep (se 1 (by rfl) ⟨1491137, by rfl⟩ : syracuseStep 1988183 = 2982275) B2982275
theorem B1324651 : Blo 1323480 1324651 := bstep (se 1 (by rfl) ⟨993488, by rfl⟩ : syracuseStep 1324651 = 1986977) B1986977
theorem B1324663 : Blo 1323480 1324663 := bstep (se 1 (by rfl) ⟨993497, by rfl⟩ : syracuseStep 1324663 = 1986995) B1986995
theorem B2979467 : Blo 1323480 2979467 := bstep (se 1 (by rfl) ⟨2234600, by rfl⟩ : syracuseStep 2979467 = 4469201) B4469201
theorem B1324683 : Blo 1323480 1324683 := bstep (se 1 (by rfl) ⟨993512, by rfl⟩ : syracuseStep 1324683 = 1987025) B1987025
theorem B1324695 : Blo 1323480 1324695 := bstep (se 1 (by rfl) ⟨993521, by rfl⟩ : syracuseStep 1324695 = 1987043) B1987043
theorem B1324715 : Blo 1323480 1324715 := bstep (se 1 (by rfl) ⟨993536, by rfl⟩ : syracuseStep 1324715 = 1987073) B1987073
theorem B1324727 : Blo 1323480 1324727 := bstep (se 1 (by rfl) ⟨993545, by rfl⟩ : syracuseStep 1324727 = 1987091) B1987091
theorem B2979521 : Blo 1323480 2979521 := bstep (se 2 (by rfl) ⟨1117320, by rfl⟩ : syracuseStep 2979521 = 2234641) B2234641
theorem B4241099 : Blo 1323480 4241099 := bstep (se 1 (by rfl) ⟨3180824, by rfl⟩ : syracuseStep 4241099 = 6361649) B6361649
theorem B1324747 : Blo 1323480 1324747 := bstep (se 1 (by rfl) ⟨993560, by rfl⟩ : syracuseStep 1324747 = 1987121) B1987121
theorem B1324759 : Blo 1323480 1324759 := bstep (se 1 (by rfl) ⟨993569, by rfl⟩ : syracuseStep 1324759 = 1987139) B1987139
theorem B1324779 : Blo 1323480 1324779 := bstep (se 1 (by rfl) ⟨993584, by rfl⟩ : syracuseStep 1324779 = 1987169) B1987169
theorem B1324791 : Blo 1323480 1324791 := bstep (se 1 (by rfl) ⟨993593, by rfl⟩ : syracuseStep 1324791 = 1987187) B1987187
theorem B1324811 : Blo 1323480 1324811 := bstep (se 1 (by rfl) ⟨993608, by rfl⟩ : syracuseStep 1324811 = 1987217) B1987217
theorem B6706961 : Blo 1323480 6706961 := bstep (se 2 (by rfl) ⟨2515110, by rfl⟩ : syracuseStep 6706961 = 5030221) B5030221
theorem B2234135 : Blo 1323480 2234135 := bstep (se 1 (by rfl) ⟨1675601, by rfl⟩ : syracuseStep 2234135 = 3351203) B3351203
theorem B4470551 : Blo 1323480 4470551 := bstep (se 1 (by rfl) ⟨3352913, by rfl⟩ : syracuseStep 4470551 = 6705827) B6705827
theorem B1324823 : Blo 1323480 1324823 := bstep (se 1 (by rfl) ⟨993617, by rfl⟩ : syracuseStep 1324823 = 1987235) B1987235
theorem B1324843 : Blo 1323480 1324843 := bstep (se 1 (by rfl) ⟨993632, by rfl⟩ : syracuseStep 1324843 = 1987265) B1987265
theorem B1414955 : Blo 1323480 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B1324855 : Blo 1323480 1324855 := bstep (se 1 (by rfl) ⟨993641, by rfl⟩ : syracuseStep 1324855 = 1987283) B1987283
theorem B1324875 : Blo 1323480 1324875 := bstep (se 1 (by rfl) ⟨993656, by rfl⟩ : syracuseStep 1324875 = 1987313) B1987313
theorem B1324887 : Blo 1323480 1324887 := bstep (se 1 (by rfl) ⟨993665, by rfl⟩ : syracuseStep 1324887 = 1987331) B1987331
theorem B81573733 : Blo 1323480 81573733 := bstep (se 4 (by rfl) ⟨7647537, by rfl⟩ : syracuseStep 81573733 = 15295075) B15295075
theorem B1324907 : Blo 1323480 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B1324919 : Blo 1323480 1324919 := bstep (se 1 (by rfl) ⟨993689, by rfl⟩ : syracuseStep 1324919 = 1987379) B1987379
theorem B1324939 : Blo 1323480 1324939 := bstep (se 1 (by rfl) ⟨993704, by rfl⟩ : syracuseStep 1324939 = 1987409) B1987409
theorem B2234263 : Blo 1323480 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B6363031 : Blo 1323480 6363031 := bstep (se 1 (by rfl) ⟨4772273, by rfl⟩ : syracuseStep 6363031 = 9544547) B9544547
theorem B2979737 : Blo 1323480 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B1324951 : Blo 1323480 1324951 := bstep (se 1 (by rfl) ⟨993713, by rfl⟩ : syracuseStep 1324951 = 1987427) B1987427
theorem B1324971 : Blo 1323480 1324971 := bstep (se 1 (by rfl) ⟨993728, by rfl⟩ : syracuseStep 1324971 = 1987457) B1987457
theorem B6707123 : Blo 1323480 6707123 := bstep (se 1 (by rfl) ⟨5030342, by rfl⟩ : syracuseStep 6707123 = 10060685) B10060685
theorem B1324983 : Blo 1323480 1324983 := bstep (se 1 (by rfl) ⟨993737, by rfl⟩ : syracuseStep 1324983 = 1987475) B1987475
theorem B5027777 : Blo 1323480 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1325003 : Blo 1323480 1325003 := bstep (se 1 (by rfl) ⟨993752, by rfl⟩ : syracuseStep 1325003 = 1987505) B1987505
theorem B1325015 : Blo 1323480 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B5658589 : Blo 1323480 5658589 := bstep (se 3 (by rfl) ⟨1060985, by rfl⟩ : syracuseStep 5658589 = 2121971) B2121971
theorem B1325035 : Blo 1323480 1325035 := bstep (se 1 (by rfl) ⟨993776, by rfl⟩ : syracuseStep 1325035 = 1987553) B1987553
theorem B2979827 : Blo 1323480 2979827 := bstep (se 1 (by rfl) ⟨2234870, by rfl⟩ : syracuseStep 2979827 = 4469741) B4469741
theorem B1325047 : Blo 1323480 1325047 := bstep (se 1 (by rfl) ⟨993785, by rfl⟩ : syracuseStep 1325047 = 1987571) B1987571
theorem B1325067 : Blo 1323480 1325067 := bstep (se 1 (by rfl) ⟨993800, by rfl⟩ : syracuseStep 1325067 = 1987601) B1987601
theorem B1488919 : Blo 1323480 1488919 := bstep (se 1 (by rfl) ⟨1116689, by rfl⟩ : syracuseStep 1488919 = 2233379) B2233379
theorem B2979863 : Blo 1323480 2979863 := bstep (se 1 (by rfl) ⟨2234897, by rfl⟩ : syracuseStep 2979863 = 4469795) B4469795
theorem B1325079 : Blo 1323480 1325079 := bstep (se 1 (by rfl) ⟨993809, by rfl⟩ : syracuseStep 1325079 = 1987619) B1987619
theorem B1325099 : Blo 1323480 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B1325111 : Blo 1323480 1325111 := bstep (se 1 (by rfl) ⟨993833, by rfl⟩ : syracuseStep 1325111 = 1987667) B1987667
theorem B1325131 : Blo 1323480 1325131 := bstep (se 1 (by rfl) ⟨993848, by rfl⟩ : syracuseStep 1325131 = 1987697) B1987697
theorem B1325143 : Blo 1323480 1325143 := bstep (se 1 (by rfl) ⟨993857, by rfl⟩ : syracuseStep 1325143 = 1987715) B1987715
theorem B1325163 : Blo 1323480 1325163 := bstep (se 1 (by rfl) ⟨993872, by rfl⟩ : syracuseStep 1325163 = 1987745) B1987745
theorem B1325175 : Blo 1323480 1325175 := bstep (se 1 (by rfl) ⟨993881, by rfl⟩ : syracuseStep 1325175 = 1987763) B1987763
theorem B1325195 : Blo 1323480 1325195 := bstep (se 1 (by rfl) ⟨993896, by rfl⟩ : syracuseStep 1325195 = 1987793) B1987793
theorem B1325207 : Blo 1323480 1325207 := bstep (se 1 (by rfl) ⟨993905, by rfl⟩ : syracuseStep 1325207 = 1987811) B1987811
theorem B1325227 : Blo 1323480 1325227 := bstep (se 1 (by rfl) ⟨993920, by rfl⟩ : syracuseStep 1325227 = 1987841) B1987841
theorem B1325239 : Blo 1323480 1325239 := bstep (se 1 (by rfl) ⟨993929, by rfl⟩ : syracuseStep 1325239 = 1987859) B1987859
theorem B1489099 : Blo 1323480 1489099 := bstep (se 1 (by rfl) ⟨1116824, by rfl⟩ : syracuseStep 1489099 = 2233649) B2233649
theorem B2513099 : Blo 1323480 2513099 := bstep (se 1 (by rfl) ⟨1884824, by rfl⟩ : syracuseStep 2513099 = 3769649) B3769649
theorem B2980043 : Blo 1323480 2980043 := bstep (se 1 (by rfl) ⟨2235032, by rfl⟩ : syracuseStep 2980043 = 4470065) B4470065
theorem B1325259 : Blo 1323480 1325259 := bstep (se 1 (by rfl) ⟨993944, by rfl⟩ : syracuseStep 1325259 = 1987889) B1987889
theorem B1325271 : Blo 1323480 1325271 := bstep (se 1 (by rfl) ⟨993953, by rfl⟩ : syracuseStep 1325271 = 1987907) B1987907
theorem B1325291 : Blo 1323480 1325291 := bstep (se 1 (by rfl) ⟨993968, by rfl⟩ : syracuseStep 1325291 = 1987937) B1987937
theorem B1325303 : Blo 1323480 1325303 := bstep (se 1 (by rfl) ⟨993977, by rfl⟩ : syracuseStep 1325303 = 1987955) B1987955
theorem B2980097 : Blo 1323480 2980097 := bstep (se 2 (by rfl) ⟨1117536, by rfl⟩ : syracuseStep 2980097 = 2235073) B2235073
theorem B1341707 : Blo 1323480 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B1325323 : Blo 1323480 1325323 := bstep (se 1 (by rfl) ⟨993992, by rfl⟩ : syracuseStep 1325323 = 1987985) B1987985
theorem B5372183 : Blo 1323480 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B1325335 : Blo 1323480 1325335 := bstep (se 1 (by rfl) ⟨994001, by rfl⟩ : syracuseStep 1325335 = 1988003) B1988003
theorem B1325355 : Blo 1323480 1325355 := bstep (se 1 (by rfl) ⟨994016, by rfl⟩ : syracuseStep 1325355 = 1988033) B1988033
theorem B4471091 : Blo 1323480 4471091 := bstep (se 1 (by rfl) ⟨3353318, by rfl⟩ : syracuseStep 4471091 = 6706637) B6706637
theorem B1489207 : Blo 1323480 1489207 := bstep (se 1 (by rfl) ⟨1116905, by rfl⟩ : syracuseStep 1489207 = 2233811) B2233811
theorem B1325367 : Blo 1323480 1325367 := bstep (se 1 (by rfl) ⟨994025, by rfl⟩ : syracuseStep 1325367 = 1988051) B1988051
theorem B8485195 : Blo 1323480 8485195 := bstep (se 1 (by rfl) ⟨6363896, by rfl⟩ : syracuseStep 8485195 = 12727793) B12727793
theorem B1325387 : Blo 1323480 1325387 := bstep (se 1 (by rfl) ⟨994040, by rfl⟩ : syracuseStep 1325387 = 1988081) B1988081
theorem B1325399 : Blo 1323480 1325399 := bstep (se 1 (by rfl) ⟨994049, by rfl⟩ : syracuseStep 1325399 = 1988099) B1988099
theorem B24181091 : Blo 1323480 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B1325419 : Blo 1323480 1325419 := bstep (se 1 (by rfl) ⟨994064, by rfl⟩ : syracuseStep 1325419 = 1988129) B1988129
theorem B68802929 : Blo 1323480 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B1325431 : Blo 1323480 1325431 := bstep (se 1 (by rfl) ⟨994073, by rfl⟩ : syracuseStep 1325431 = 1988147) B1988147
theorem B2513281 : Blo 1323480 2513281 := bstep (se 2 (by rfl) ⟨942480, by rfl⟩ : syracuseStep 2513281 = 1884961) B1884961
theorem B2120075 : Blo 1323480 2120075 := bstep (se 1 (by rfl) ⟨1590056, by rfl⟩ : syracuseStep 2120075 = 3180113) B3180113
theorem B1325451 : Blo 1323480 1325451 := bstep (se 1 (by rfl) ⟨994088, by rfl⟩ : syracuseStep 1325451 = 1988177) B1988177
theorem B1325463 : Blo 1323480 1325463 := bstep (se 1 (by rfl) ⟨994097, by rfl⟩ : syracuseStep 1325463 = 1988195) B1988195
theorem B2980313 : Blo 1323480 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B1489387 : Blo 1323480 1489387 := bstep (se 1 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 1489387 = 2234081) B2234081
theorem B2120203 : Blo 1323480 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B2234891 : Blo 1323480 2234891 := bstep (se 1 (by rfl) ⟨1676168, by rfl⟩ : syracuseStep 2234891 = 3352337) B3352337
theorem B2980403 : Blo 1323480 2980403 := bstep (se 1 (by rfl) ⟨2235302, by rfl⟩ : syracuseStep 2980403 = 4470605) B4470605
theorem B4471361 : Blo 1323480 4471361 := bstep (se 2 (by rfl) ⟨1676760, by rfl⟩ : syracuseStep 4471361 = 3353521) B3353521
theorem B1489495 : Blo 1323480 1489495 := bstep (se 1 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 1489495 = 2234243) B2234243
theorem B2980439 : Blo 1323480 2980439 := bstep (se 1 (by rfl) ⟨2235329, by rfl⟩ : syracuseStep 2980439 = 4470659) B4470659
theorem B2235019 : Blo 1323480 2235019 := bstep (se 1 (by rfl) ⟨1676264, by rfl⟩ : syracuseStep 2235019 = 3352529) B3352529
theorem B1489675 : Blo 1323480 1489675 := bstep (se 1 (by rfl) ⟨1117256, by rfl⟩ : syracuseStep 1489675 = 2234513) B2234513
theorem B2980619 : Blo 1323480 2980619 := bstep (se 1 (by rfl) ⟨2235464, by rfl⟩ : syracuseStep 2980619 = 4470929) B4470929
theorem B5094161 : Blo 1323480 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B5659409 : Blo 1323480 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B2235161 : Blo 1323480 2235161 := bstep (se 2 (by rfl) ⟨838185, by rfl⟩ : syracuseStep 2235161 = 1676371) B1676371
theorem B2513729 : Blo 1323480 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B2980673 : Blo 1323480 2980673 := bstep (se 2 (by rfl) ⟨1117752, by rfl⟩ : syracuseStep 2980673 = 2235505) B2235505
theorem B1489783 : Blo 1323480 1489783 := bstep (se 1 (by rfl) ⟨1117337, by rfl⟩ : syracuseStep 1489783 = 2234675) B2234675
theorem B3021707 : Blo 1323480 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B2235289 : Blo 1323480 2235289 := bstep (se 2 (by rfl) ⟨838233, by rfl⟩ : syracuseStep 2235289 = 1676467) B1676467
theorem B2980889 : Blo 1323480 2980889 := bstep (se 2 (by rfl) ⟨1117833, by rfl⟩ : syracuseStep 2980889 = 2235667) B2235667
theorem B45849635 : Blo 1323480 45849635 := bstep (se 1 (by rfl) ⟨34387226, by rfl⟩ : syracuseStep 45849635 = 68774453) B68774453
theorem B1489963 : Blo 1323480 1489963 := bstep (se 1 (by rfl) ⟨1117472, by rfl⟩ : syracuseStep 1489963 = 2234945) B2234945
theorem B9542701 : Blo 1323480 9542701 := bstep (se 3 (by rfl) ⟨1789256, by rfl⟩ : syracuseStep 9542701 = 3578513) B3578513
theorem B7543853 : Blo 1323480 7543853 := bstep (se 3 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 7543853 = 2828945) B2828945
theorem B5372993 : Blo 1323480 5372993 := bstep (se 2 (by rfl) ⟨2014872, by rfl⟩ : syracuseStep 5372993 = 4029745) B4029745
theorem B4471901 : Blo 1323480 4471901 := bstep (se 3 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 4471901 = 1676963) B1676963
theorem B2980979 : Blo 1323480 2980979 := bstep (se 1 (by rfl) ⟨2235734, by rfl⟩ : syracuseStep 2980979 = 4471469) B4471469
theorem B2514071 : Blo 1323480 2514071 := bstep (se 1 (by rfl) ⟨1885553, by rfl⟩ : syracuseStep 2514071 = 3771107) B3771107
theorem B8486039 : Blo 1323480 8486039 := bstep (se 1 (by rfl) ⟨6364529, by rfl⟩ : syracuseStep 8486039 = 12729059) B12729059
theorem B1490071 : Blo 1323480 1490071 := bstep (se 1 (by rfl) ⟨1117553, by rfl⟩ : syracuseStep 1490071 = 2235107) B2235107
theorem B2981015 : Blo 1323480 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B5029037 : Blo 1323480 5029037 := bstep (se 3 (by rfl) ⟨942944, by rfl⟩ : syracuseStep 5029037 = 1885889) B1885889
theorem B5029067 : Blo 1323480 5029067 := bstep (se 1 (by rfl) ⟨3771800, by rfl⟩ : syracuseStep 5029067 = 7543601) B7543601
theorem B9542873 : Blo 1323480 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B2120921 : Blo 1323480 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B4242739 : Blo 1323480 4242739 := bstep (se 1 (by rfl) ⟨3182054, by rfl⟩ : syracuseStep 4242739 = 6364109) B6364109
theorem B1490251 : Blo 1323480 1490251 := bstep (se 1 (by rfl) ⟨1117688, by rfl⟩ : syracuseStep 1490251 = 2235377) B2235377
theorem B2981195 : Blo 1323480 2981195 := bstep (se 1 (by rfl) ⟨2235896, by rfl⟩ : syracuseStep 2981195 = 4471793) B4471793
theorem B5094787 : Blo 1323480 5094787 := bstep (se 1 (by rfl) ⟨3821090, by rfl⟩ : syracuseStep 5094787 = 7642181) B7642181
theorem B2981249 : Blo 1323480 2981249 := bstep (se 2 (by rfl) ⟨1117968, by rfl⟩ : syracuseStep 2981249 = 2235937) B2235937
theorem B2121113 : Blo 1323480 2121113 := bstep (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) B1590835
theorem B5660077 : Blo 1323480 5660077 := bstep (se 3 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 5660077 = 2122529) B2122529
theorem B1490359 : Blo 1323480 1490359 := bstep (se 1 (by rfl) ⟨1117769, by rfl⟩ : syracuseStep 1490359 = 2235539) B2235539
theorem B6045131 : Blo 1323480 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B2235863 : Blo 1323480 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B3063361 : Blo 1323480 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B2686529 : Blo 1323480 2686529 := bstep (se 2 (by rfl) ⟨1007448, by rfl⟩ : syracuseStep 2686529 = 2014897) B2014897
theorem B2235991 : Blo 1323480 2235991 := bstep (se 1 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 2235991 = 3353987) B3353987
theorem B2981465 : Blo 1323480 2981465 := bstep (se 2 (by rfl) ⟨1118049, by rfl⟩ : syracuseStep 2981465 = 2236099) B2236099
theorem B1490539 : Blo 1323480 1490539 := bstep (se 1 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 1490539 = 2235809) B2235809
theorem B2981555 : Blo 1323480 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B1490647 : Blo 1323480 1490647 := bstep (se 1 (by rfl) ⟨1117985, by rfl⟩ : syracuseStep 1490647 = 2235971) B2235971
theorem B2981591 : Blo 1323480 2981591 := bstep (se 1 (by rfl) ⟨2236193, by rfl⟩ : syracuseStep 2981591 = 4472387) B4472387
theorem B2514739 : Blo 1323480 2514739 := bstep (se 1 (by rfl) ⟨1886054, by rfl⟩ : syracuseStep 2514739 = 3772109) B3772109
theorem B12721985 : Blo 1323480 12721985 := bstep (se 2 (by rfl) ⟨4770744, by rfl⟩ : syracuseStep 12721985 = 9541489) B9541489
theorem B6455105 : Blo 1323480 6455105 := bstep (se 2 (by rfl) ⟨2420664, by rfl⟩ : syracuseStep 6455105 = 4841329) B4841329
theorem B6709067 : Blo 1323480 6709067 := bstep (se 1 (by rfl) ⟨5031800, by rfl⟩ : syracuseStep 6709067 = 10063601) B10063601
theorem B5029721 : Blo 1323480 5029721 := bstep (se 2 (by rfl) ⟨1886145, by rfl⟩ : syracuseStep 5029721 = 3772291) B3772291
theorem B11476829 : Blo 1323480 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B1490827 : Blo 1323480 1490827 := bstep (se 1 (by rfl) ⟨1118120, by rfl⟩ : syracuseStep 1490827 = 2236241) B2236241
theorem B2981771 : Blo 1323480 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B3350423 : Blo 1323480 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B5373869 : Blo 1323480 5373869 := bstep (se 3 (by rfl) ⟨1007600, by rfl⟩ : syracuseStep 5373869 = 2015201) B2015201
theorem B2981825 : Blo 1323480 2981825 := bstep (se 2 (by rfl) ⟨1118184, by rfl⟩ : syracuseStep 2981825 = 2236369) B2236369
theorem B1490935 : Blo 1323480 1490935 := bstep (se 1 (by rfl) ⟨1118201, by rfl⟩ : syracuseStep 1490935 = 2236403) B2236403
theorem B2514959 : Blo 1323480 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B14311541 : Blo 1323480 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B2982023 : Blo 1323480 2982023 := bstep (se 1 (by rfl) ⟨2236517, by rfl⟩ : syracuseStep 2982023 = 4473035) B4473035
theorem B1491079 : Blo 1323480 1491079 := bstep (se 1 (by rfl) ⟨1118309, by rfl⟩ : syracuseStep 1491079 = 2236619) B2236619
theorem B4473089 : Blo 1323480 4473089 := bstep (se 2 (by rfl) ⟨1677408, by rfl⟩ : syracuseStep 4473089 = 3354817) B3354817
theorem B1884431 : Blo 1323480 1884431 := bstep (se 1 (by rfl) ⟨1413323, by rfl⟩ : syracuseStep 1884431 = 2826647) B2826647
theorem B2982203 : Blo 1323480 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B2548103 : Blo 1323480 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B11313593 : Blo 1323480 11313593 := bstep (se 2 (by rfl) ⟨4242597, by rfl⟩ : syracuseStep 11313593 = 8485195) B8485195
theorem B2982329 : Blo 1323480 2982329 := bstep (se 2 (by rfl) ⟨1118373, by rfl⟩ : syracuseStep 2982329 = 2236747) B2236747
theorem B14311889 : Blo 1323480 14311889 := bstep (se 2 (by rfl) ⟨5366958, by rfl⟩ : syracuseStep 14311889 = 10733917) B10733917
theorem B3351041 : Blo 1323480 3351041 := bstep (se 2 (by rfl) ⟨1256640, by rfl⟩ : syracuseStep 3351041 = 2513281) B2513281
theorem B2826937 : Blo 1323480 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B9544463 : Blo 1323480 9544463 := bstep (se 1 (by rfl) ⟨7158347, by rfl⟩ : syracuseStep 9544463 = 14316695) B14316695
theorem B6701939 : Blo 1323480 6701939 := bstep (se 1 (by rfl) ⟨5026454, by rfl⟩ : syracuseStep 6701939 = 10052909) B10052909
theorem B3351415 : Blo 1323480 3351415 := bstep (se 1 (by rfl) ⟨2513561, by rfl⟩ : syracuseStep 3351415 = 5027123) B5027123
theorem B6710201 : Blo 1323480 6710201 := bstep (se 2 (by rfl) ⟨2516325, by rfl⟩ : syracuseStep 6710201 = 5032651) B5032651
theorem B9552907 : Blo 1323480 9552907 := bstep (se 1 (by rfl) ⟨7164680, by rfl⟩ : syracuseStep 9552907 = 14329361) B14329361
theorem B2827399 : Blo 1323480 2827399 := bstep (se 1 (by rfl) ⟨2120549, by rfl⟩ : syracuseStep 2827399 = 4241099) B4241099
theorem B3351851 : Blo 1323480 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B1885513 : Blo 1323480 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B6702425 : Blo 1323480 6702425 := bstep (se 2 (by rfl) ⟨2513409, by rfl⟩ : syracuseStep 6702425 = 5026819) B5026819
theorem B12723601 : Blo 1323480 12723601 := bstep (se 2 (by rfl) ⟨4771350, by rfl⟩ : syracuseStep 12723601 = 9542701) B9542701
theorem B1885627 : Blo 1323480 1885627 := bstep (se 1 (by rfl) ⟨1414220, by rfl⟩ : syracuseStep 1885627 = 2828441) B2828441
theorem B5031467 : Blo 1323480 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B45868619 : Blo 1323480 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B3180151 : Blo 1323480 3180151 := bstep (se 1 (by rfl) ⟨2385113, by rfl⟩ : syracuseStep 3180151 = 4770227) B4770227
theorem B28641073 : Blo 1323480 28641073 := bstep (se 2 (by rfl) ⟨10740402, by rfl⟩ : syracuseStep 28641073 = 21480805) B21480805
theorem B6793049 : Blo 1323480 6793049 := bstep (se 2 (by rfl) ⟨2547393, by rfl⟩ : syracuseStep 6793049 = 5094787) B5094787
theorem B10061657 : Blo 1323480 10061657 := bstep (se 2 (by rfl) ⟨3773121, by rfl⟩ : syracuseStep 10061657 = 7546243) B7546243
theorem B5654387 : Blo 1323480 5654387 := bstep (se 1 (by rfl) ⟨4240790, by rfl⟩ : syracuseStep 5654387 = 8481581) B8481581
theorem B7546769 : Blo 1323480 7546769 := bstep (se 2 (by rfl) ⟨2830038, by rfl⟩ : syracuseStep 7546769 = 5660077) B5660077
theorem B3770297 : Blo 1323480 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B30566423 : Blo 1323480 30566423 := bstep (se 1 (by rfl) ⟨22924817, by rfl⟩ : syracuseStep 30566423 = 45849635) B45849635
theorem B3581995 : Blo 1323480 3581995 := bstep (se 1 (by rfl) ⟨2686496, by rfl⟩ : syracuseStep 3581995 = 5372993) B5372993
theorem B15091757 : Blo 1323480 15091757 := bstep (se 3 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 15091757 = 5659409) B5659409
theorem B3352691 : Blo 1323480 3352691 := bstep (se 1 (by rfl) ⟨2514518, by rfl⟩ : syracuseStep 3352691 = 5029037) B5029037
theorem B3352711 : Blo 1323480 3352711 := bstep (se 1 (by rfl) ⟨2514533, by rfl⟩ : syracuseStep 3352711 = 5029067) B5029067
theorem B4024637 : Blo 1323480 4024637 := bstep (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) B1509239
theorem B15075719 : Blo 1323480 15075719 := bstep (se 1 (by rfl) ⟨11306789, by rfl⟩ : syracuseStep 15075719 = 22613579) B22613579
theorem B3352985 : Blo 1323480 3352985 := bstep (se 2 (by rfl) ⟨1257369, by rfl⟩ : syracuseStep 3352985 = 2514739) B2514739
theorem B14330317 : Blo 1323480 14330317 := bstep (se 3 (by rfl) ⟨2686934, by rfl⟩ : syracuseStep 14330317 = 5373869) B5373869
theorem B8481323 : Blo 1323480 8481323 := bstep (se 1 (by rfl) ⟨6360992, by rfl⟩ : syracuseStep 8481323 = 12721985) B12721985
theorem B16108075 : Blo 1323480 16108075 := bstep (se 1 (by rfl) ⟨12081056, by rfl⟩ : syracuseStep 16108075 = 24162113) B24162113
theorem B4303403 : Blo 1323480 4303403 := bstep (se 1 (by rfl) ⟨3227552, by rfl⟩ : syracuseStep 4303403 = 6455105) B6455105
theorem B3353147 : Blo 1323480 3353147 := bstep (se 1 (by rfl) ⟨2514860, by rfl⟩ : syracuseStep 3353147 = 5029721) B5029721
theorem B1985225 : Blo 1323480 1985225 := bstep (se 2 (by rfl) ⟨744459, by rfl⟩ : syracuseStep 1985225 = 1488919) B1488919
theorem B3582731 : Blo 1323480 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B3353359 : Blo 1323480 3353359 := bstep (se 1 (by rfl) ⟨2515019, by rfl⟩ : syracuseStep 3353359 = 5030039) B5030039
theorem B9186085 : Blo 1323480 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B10062629 : Blo 1323480 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B1985339 : Blo 1323480 1985339 := bstep (se 1 (by rfl) ⟨1489004, by rfl⟩ : syracuseStep 1985339 = 2978009) B2978009
theorem B1985399 : Blo 1323480 1985399 := bstep (se 1 (by rfl) ⟨1489049, by rfl⟩ : syracuseStep 1985399 = 2978099) B2978099
theorem B1985423 : Blo 1323480 1985423 := bstep (se 1 (by rfl) ⟨1489067, by rfl⟩ : syracuseStep 1985423 = 2978135) B2978135
theorem B1985465 : Blo 1323480 1985465 := bstep (se 2 (by rfl) ⟨744549, by rfl⟩ : syracuseStep 1985465 = 1489099) B1489099
theorem B1985543 : Blo 1323480 1985543 := bstep (se 1 (by rfl) ⟨1489157, by rfl⟩ : syracuseStep 1985543 = 2978315) B2978315
theorem B1887239 : Blo 1323480 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B10742807 : Blo 1323480 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B3353633 : Blo 1323480 3353633 := bstep (se 2 (by rfl) ⟨1257612, by rfl⟩ : syracuseStep 3353633 = 2515225) B2515225
theorem B1985579 : Blo 1323480 1985579 := bstep (se 1 (by rfl) ⟨1489184, by rfl⟩ : syracuseStep 1985579 = 2978369) B2978369
theorem B1985609 : Blo 1323480 1985609 := bstep (se 2 (by rfl) ⟨744603, by rfl⟩ : syracuseStep 1985609 = 1489207) B1489207
theorem B1985723 : Blo 1323480 1985723 := bstep (se 1 (by rfl) ⟨1489292, by rfl⟩ : syracuseStep 1985723 = 2978585) B2978585
theorem B1985783 : Blo 1323480 1985783 := bstep (se 1 (by rfl) ⟨1489337, by rfl⟩ : syracuseStep 1985783 = 2978675) B2978675
theorem B1985807 : Blo 1323480 1985807 := bstep (se 1 (by rfl) ⟨1489355, by rfl⟩ : syracuseStep 1985807 = 2978711) B2978711
theorem B1985849 : Blo 1323480 1985849 := bstep (se 2 (by rfl) ⟨744693, by rfl⟩ : syracuseStep 1985849 = 1489387) B1489387
theorem B1985927 : Blo 1323480 1985927 := bstep (se 1 (by rfl) ⟨1489445, by rfl⟩ : syracuseStep 1985927 = 2978891) B2978891
theorem B6704531 : Blo 1323480 6704531 := bstep (se 1 (by rfl) ⟨5028398, by rfl⟩ : syracuseStep 6704531 = 10056797) B10056797
theorem B4468121 : Blo 1323480 4468121 := bstep (se 2 (by rfl) ⟨1675545, by rfl⟩ : syracuseStep 4468121 = 3351091) B3351091
theorem B6368665 : Blo 1323480 6368665 := bstep (se 2 (by rfl) ⟨2388249, by rfl⟩ : syracuseStep 6368665 = 4776499) B4776499
theorem B1985963 : Blo 1323480 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B24178105 : Blo 1323480 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B1985993 : Blo 1323480 1985993 := bstep (se 2 (by rfl) ⟨744747, by rfl⟩ : syracuseStep 1985993 = 1489495) B1489495
theorem B48344525 : Blo 1323480 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B3771937 : Blo 1323480 3771937 := bstep (se 2 (by rfl) ⟨1414476, by rfl⟩ : syracuseStep 3771937 = 2828953) B2828953
theorem B1986107 : Blo 1323480 1986107 := bstep (se 1 (by rfl) ⟨1489580, by rfl⟩ : syracuseStep 1986107 = 2979161) B2979161
theorem B5025347 : Blo 1323480 5025347 := bstep (se 1 (by rfl) ⟨3769010, by rfl⟩ : syracuseStep 5025347 = 7538021) B7538021
theorem B1986167 : Blo 1323480 1986167 := bstep (se 1 (by rfl) ⟨1489625, by rfl⟩ : syracuseStep 1986167 = 2979251) B2979251
theorem B1986191 : Blo 1323480 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2829971 : Blo 1323480 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B12906161 : Blo 1323480 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B1986233 : Blo 1323480 1986233 := bstep (se 2 (by rfl) ⟨744837, by rfl⟩ : syracuseStep 1986233 = 1489675) B1489675
theorem B5656301 : Blo 1323480 5656301 := bstep (se 3 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 5656301 = 2121113) B2121113
theorem B1986311 : Blo 1323480 1986311 := bstep (se 1 (by rfl) ⟨1489733, by rfl⟩ : syracuseStep 1986311 = 2979467) B2979467
theorem B1986347 : Blo 1323480 1986347 := bstep (se 1 (by rfl) ⟨1489760, by rfl⟩ : syracuseStep 1986347 = 2979521) B2979521
theorem B61189937 : Blo 1323480 61189937 := bstep (se 2 (by rfl) ⟨22946226, by rfl⟩ : syracuseStep 61189937 = 45892453) B45892453
theorem B1986377 : Blo 1323480 1986377 := bstep (se 2 (by rfl) ⟨744891, by rfl⟩ : syracuseStep 1986377 = 1489783) B1489783
theorem B1986491 : Blo 1323480 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B1986551 : Blo 1323480 1986551 := bstep (se 1 (by rfl) ⟨1489913, by rfl⟩ : syracuseStep 1986551 = 2979827) B2979827
theorem B3354635 : Blo 1323480 3354635 := bstep (se 1 (by rfl) ⟨2515976, by rfl⟩ : syracuseStep 3354635 = 5031953) B5031953
theorem B1986575 : Blo 1323480 1986575 := bstep (se 1 (by rfl) ⟨1489931, by rfl⟩ : syracuseStep 1986575 = 2979863) B2979863
theorem B1986617 : Blo 1323480 1986617 := bstep (se 2 (by rfl) ⟨744981, by rfl⟩ : syracuseStep 1986617 = 1489963) B1489963
theorem B4468823 : Blo 1323480 4468823 := bstep (se 1 (by rfl) ⟨3351617, by rfl⟩ : syracuseStep 4468823 = 6703235) B6703235
theorem B12243077 : Blo 1323480 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B1675399 : Blo 1323480 1675399 := bstep (se 1 (by rfl) ⟨1256549, by rfl⟩ : syracuseStep 1675399 = 2513099) B2513099
theorem B1986695 : Blo 1323480 1986695 := bstep (se 1 (by rfl) ⟨1490021, by rfl⟩ : syracuseStep 1986695 = 2980043) B2980043
theorem B1986731 : Blo 1323480 1986731 := bstep (se 1 (by rfl) ⟨1490048, by rfl⟩ : syracuseStep 1986731 = 2980097) B2980097
theorem B7540937 : Blo 1323480 7540937 := bstep (se 2 (by rfl) ⟨2827851, by rfl⟩ : syracuseStep 7540937 = 5655703) B5655703
theorem B1986761 : Blo 1323480 1986761 := bstep (se 2 (by rfl) ⟨745035, by rfl⟩ : syracuseStep 1986761 = 1490071) B1490071
theorem B1413383 : Blo 1323480 1413383 := bstep (se 1 (by rfl) ⟨1060037, by rfl⟩ : syracuseStep 1413383 = 2120075) B2120075
theorem B2978063 : Blo 1323480 2978063 := bstep (se 1 (by rfl) ⟨2233547, by rfl⟩ : syracuseStep 2978063 = 4467095) B4467095
theorem B2978081 : Blo 1323480 2978081 := bstep (se 2 (by rfl) ⟨1116780, by rfl⟩ : syracuseStep 2978081 = 2233561) B2233561
theorem B1986875 : Blo 1323480 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B1986935 : Blo 1323480 1986935 := bstep (se 1 (by rfl) ⟨1490201, by rfl⟩ : syracuseStep 1986935 = 2980403) B2980403
theorem B1986959 : Blo 1323480 1986959 := bstep (se 1 (by rfl) ⟨1490219, by rfl⟩ : syracuseStep 1986959 = 2980439) B2980439
theorem B2388371 : Blo 1323480 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B5656985 : Blo 1323480 5656985 := bstep (se 2 (by rfl) ⟨2121369, by rfl⟩ : syracuseStep 5656985 = 4242739) B4242739
theorem B1987001 : Blo 1323480 1987001 := bstep (se 2 (by rfl) ⟨745125, by rfl⟩ : syracuseStep 1987001 = 1490251) B1490251
theorem B1323527 : Blo 1323480 1323527 := bstep (se 1 (by rfl) ⟨992645, by rfl⟩ : syracuseStep 1323527 = 1985291) B1985291
theorem B3396107 : Blo 1323480 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B1987079 : Blo 1323480 1987079 := bstep (se 1 (by rfl) ⟨1490309, by rfl⟩ : syracuseStep 1987079 = 2980619) B2980619
theorem B1323535 : Blo 1323480 1323535 := bstep (se 1 (by rfl) ⟨992651, by rfl⟩ : syracuseStep 1323535 = 1985303) B1985303
theorem B5026333 : Blo 1323480 5026333 := bstep (se 3 (by rfl) ⟨942437, by rfl⟩ : syracuseStep 5026333 = 1884875) B1884875
theorem B1675819 : Blo 1323480 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B1987115 : Blo 1323480 1987115 := bstep (se 1 (by rfl) ⟨1490336, by rfl⟩ : syracuseStep 1987115 = 2980673) B2980673
theorem B1323579 : Blo 1323480 1323579 := bstep (se 1 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 1323579 = 1985369) B1985369
theorem B4469309 : Blo 1323480 4469309 := bstep (se 3 (by rfl) ⟨837995, by rfl⟩ : syracuseStep 4469309 = 1675991) B1675991
theorem B1987145 : Blo 1323480 1987145 := bstep (se 2 (by rfl) ⟨745179, by rfl⟩ : syracuseStep 1987145 = 1490359) B1490359
theorem B2978423 : Blo 1323480 2978423 := bstep (se 1 (by rfl) ⟨2233817, by rfl⟩ : syracuseStep 2978423 = 4467635) B4467635
theorem B10056311 : Blo 1323480 10056311 := bstep (se 1 (by rfl) ⟨7542233, by rfl⟩ : syracuseStep 10056311 = 15084467) B15084467
theorem B1323655 : Blo 1323480 1323655 := bstep (se 1 (by rfl) ⟨992741, by rfl⟩ : syracuseStep 1323655 = 1985483) B1985483
theorem B1323663 : Blo 1323480 1323663 := bstep (se 1 (by rfl) ⟨992747, by rfl⟩ : syracuseStep 1323663 = 1985495) B1985495
theorem B1323707 : Blo 1323480 1323707 := bstep (se 1 (by rfl) ⟨992780, by rfl⟩ : syracuseStep 1323707 = 1985561) B1985561
theorem B1987259 : Blo 1323480 1987259 := bstep (se 1 (by rfl) ⟨1490444, by rfl⟩ : syracuseStep 1987259 = 2980889) B2980889
theorem B1987319 : Blo 1323480 1987319 := bstep (se 1 (by rfl) ⟨1490489, by rfl⟩ : syracuseStep 1987319 = 2980979) B2980979
theorem B4084481 : Blo 1323480 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B1323783 : Blo 1323480 1323783 := bstep (se 1 (by rfl) ⟨992837, by rfl⟩ : syracuseStep 1323783 = 1985675) B1985675
theorem B1323791 : Blo 1323480 1323791 := bstep (se 1 (by rfl) ⟨992843, by rfl⟩ : syracuseStep 1323791 = 1985687) B1985687
theorem B1676047 : Blo 1323480 1676047 := bstep (se 1 (by rfl) ⟨1257035, by rfl⟩ : syracuseStep 1676047 = 2514071) B2514071
theorem B5657359 : Blo 1323480 5657359 := bstep (se 1 (by rfl) ⟨4243019, by rfl⟩ : syracuseStep 5657359 = 8486039) B8486039
theorem B1987343 : Blo 1323480 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B3773213 : Blo 1323480 3773213 := bstep (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) B1414955
theorem B2978603 : Blo 1323480 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B1987385 : Blo 1323480 1987385 := bstep (se 2 (by rfl) ⟨745269, by rfl⟩ : syracuseStep 1987385 = 1490539) B1490539
theorem B1323835 : Blo 1323480 1323835 := bstep (se 1 (by rfl) ⟨992876, by rfl⟩ : syracuseStep 1323835 = 1985753) B1985753
theorem B6361915 : Blo 1323480 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B1413947 : Blo 1323480 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B1323911 : Blo 1323480 1323911 := bstep (se 1 (by rfl) ⟨992933, by rfl⟩ : syracuseStep 1323911 = 1985867) B1985867
theorem B1987463 : Blo 1323480 1987463 := bstep (se 1 (by rfl) ⟨1490597, by rfl⟩ : syracuseStep 1987463 = 2981195) B2981195
theorem B1323919 : Blo 1323480 1323919 := bstep (se 1 (by rfl) ⟨992939, by rfl⟩ : syracuseStep 1323919 = 1985879) B1985879
theorem B1987499 : Blo 1323480 1987499 := bstep (se 1 (by rfl) ⟨1490624, by rfl⟩ : syracuseStep 1987499 = 2981249) B2981249
theorem B1323963 : Blo 1323480 1323963 := bstep (se 1 (by rfl) ⟨992972, by rfl⟩ : syracuseStep 1323963 = 1985945) B1985945
theorem B1987529 : Blo 1323480 1987529 := bstep (se 2 (by rfl) ⟨745323, by rfl⟩ : syracuseStep 1987529 = 1490647) B1490647
theorem B3773441 : Blo 1323480 3773441 := bstep (se 2 (by rfl) ⟨1415040, by rfl⟩ : syracuseStep 3773441 = 2830081) B2830081
theorem B1324039 : Blo 1323480 1324039 := bstep (se 1 (by rfl) ⟨993029, by rfl⟩ : syracuseStep 1324039 = 1986059) B1986059
theorem B1324047 : Blo 1323480 1324047 := bstep (se 1 (by rfl) ⟨993035, by rfl⟩ : syracuseStep 1324047 = 1986071) B1986071
theorem B1791019 : Blo 1323480 1791019 := bstep (se 1 (by rfl) ⟨1343264, by rfl⟩ : syracuseStep 1791019 = 2686529) B2686529
theorem B1324091 : Blo 1323480 1324091 := bstep (se 1 (by rfl) ⟨993068, by rfl⟩ : syracuseStep 1324091 = 1986137) B1986137
theorem B1987643 : Blo 1323480 1987643 := bstep (se 1 (by rfl) ⟨1490732, by rfl⟩ : syracuseStep 1987643 = 2981465) B2981465
theorem B1987703 : Blo 1323480 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B122320003 : Blo 1323480 122320003 := bstep (se 1 (by rfl) ⟨91740002, by rfl⟩ : syracuseStep 122320003 = 183480005) B183480005
theorem B1324167 : Blo 1323480 1324167 := bstep (se 1 (by rfl) ⟨993125, by rfl⟩ : syracuseStep 1324167 = 1986251) B1986251
theorem B1324175 : Blo 1323480 1324175 := bstep (se 1 (by rfl) ⟨993131, by rfl⟩ : syracuseStep 1324175 = 1986263) B1986263
theorem B1987727 : Blo 1323480 1987727 := bstep (se 1 (by rfl) ⟨1490795, by rfl⟩ : syracuseStep 1987727 = 2981591) B2981591
theorem B2978963 : Blo 1323480 2978963 := bstep (se 1 (by rfl) ⟨2234222, by rfl⟩ : syracuseStep 2978963 = 4468445) B4468445
theorem B1987769 : Blo 1323480 1987769 := bstep (se 2 (by rfl) ⟨745413, by rfl⟩ : syracuseStep 1987769 = 1490827) B1490827
theorem B1324219 : Blo 1323480 1324219 := bstep (se 1 (by rfl) ⟨993164, by rfl⟩ : syracuseStep 1324219 = 1986329) B1986329
theorem B2979017 : Blo 1323480 2979017 := bstep (se 2 (by rfl) ⟨1117131, by rfl⟩ : syracuseStep 2979017 = 2234263) B2234263
theorem B8484041 : Blo 1323480 8484041 := bstep (se 2 (by rfl) ⟨3181515, by rfl⟩ : syracuseStep 8484041 = 6363031) B6363031
theorem B1324295 : Blo 1323480 1324295 := bstep (se 1 (by rfl) ⟨993221, by rfl⟩ : syracuseStep 1324295 = 1986443) B1986443
theorem B1987847 : Blo 1323480 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B2233615 : Blo 1323480 2233615 := bstep (se 1 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 2233615 = 3350423) B3350423
theorem B1324303 : Blo 1323480 1324303 := bstep (se 1 (by rfl) ⟨993227, by rfl⟩ : syracuseStep 1324303 = 1986455) B1986455
theorem B1987883 : Blo 1323480 1987883 := bstep (se 1 (by rfl) ⟨1490912, by rfl⟩ : syracuseStep 1987883 = 2981825) B2981825
theorem B1324347 : Blo 1323480 1324347 := bstep (se 1 (by rfl) ⟨993260, by rfl⟩ : syracuseStep 1324347 = 1986521) B1986521
theorem B1987913 : Blo 1323480 1987913 := bstep (se 2 (by rfl) ⟨745467, by rfl⟩ : syracuseStep 1987913 = 1490935) B1490935
theorem B3773783 : Blo 1323480 3773783 := bstep (se 1 (by rfl) ⟨2830337, by rfl⟩ : syracuseStep 3773783 = 5660675) B5660675
theorem B10737031 : Blo 1323480 10737031 := bstep (se 1 (by rfl) ⟨8052773, by rfl⟩ : syracuseStep 10737031 = 16105547) B16105547
theorem B1324423 : Blo 1323480 1324423 := bstep (se 1 (by rfl) ⟨993317, by rfl⟩ : syracuseStep 1324423 = 1986635) B1986635
theorem B1324431 : Blo 1323480 1324431 := bstep (se 1 (by rfl) ⟨993323, by rfl⟩ : syracuseStep 1324431 = 1986647) B1986647
theorem B7165331 : Blo 1323480 7165331 := bstep (se 1 (by rfl) ⟨5373998, by rfl⟩ : syracuseStep 7165331 = 10747997) B10747997
theorem B1324475 : Blo 1323480 1324475 := bstep (se 1 (by rfl) ⟨993356, by rfl⟩ : syracuseStep 1324475 = 1986713) B1986713
theorem B1988027 : Blo 1323480 1988027 := bstep (se 1 (by rfl) ⟨1491020, by rfl⟩ : syracuseStep 1988027 = 2982041) B2982041
theorem B3773897 : Blo 1323480 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B1676791 : Blo 1323480 1676791 := bstep (se 1 (by rfl) ⟨1257593, by rfl⟩ : syracuseStep 1676791 = 2515187) B2515187
theorem B1988087 : Blo 1323480 1988087 := bstep (se 1 (by rfl) ⟨1491065, by rfl⟩ : syracuseStep 1988087 = 2982131) B2982131
theorem B1324551 : Blo 1323480 1324551 := bstep (se 1 (by rfl) ⟨993413, by rfl⟩ : syracuseStep 1324551 = 1986827) B1986827
theorem B1324559 : Blo 1323480 1324559 := bstep (se 1 (by rfl) ⟨993419, by rfl⟩ : syracuseStep 1324559 = 1986839) B1986839
theorem B1988111 : Blo 1323480 1988111 := bstep (se 1 (by rfl) ⟨1491083, by rfl⟩ : syracuseStep 1988111 = 2982167) B2982167
theorem B1988153 : Blo 1323480 1988153 := bstep (se 2 (by rfl) ⟨745557, by rfl⟩ : syracuseStep 1988153 = 1491115) B1491115
theorem B2012731 : Blo 1323480 2012731 := bstep (se 1 (by rfl) ⟨1509548, by rfl⟩ : syracuseStep 2012731 = 3019097) B3019097
theorem B1324603 : Blo 1323480 1324603 := bstep (se 1 (by rfl) ⟨993452, by rfl⟩ : syracuseStep 1324603 = 1986905) B1986905
theorem B10057283 : Blo 1323480 10057283 := bstep (se 1 (by rfl) ⟨7542962, by rfl⟩ : syracuseStep 10057283 = 15085925) B15085925
theorem B1324679 : Blo 1323480 1324679 := bstep (se 1 (by rfl) ⟨993509, by rfl⟩ : syracuseStep 1324679 = 1987019) B1987019
theorem B1324687 : Blo 1323480 1324687 := bstep (se 1 (by rfl) ⟨993515, by rfl⟩ : syracuseStep 1324687 = 1987031) B1987031
theorem B1324731 : Blo 1323480 1324731 := bstep (se 1 (by rfl) ⟨993548, by rfl⟩ : syracuseStep 1324731 = 1987097) B1987097
theorem B1324807 : Blo 1323480 1324807 := bstep (se 1 (by rfl) ⟨993605, by rfl⟩ : syracuseStep 1324807 = 1987211) B1987211
theorem B1324815 : Blo 1323480 1324815 := bstep (se 1 (by rfl) ⟨993611, by rfl⟩ : syracuseStep 1324815 = 1987223) B1987223
theorem B2234155 : Blo 1323480 2234155 := bstep (se 1 (by rfl) ⟨1675616, by rfl⟩ : syracuseStep 2234155 = 3351233) B3351233
theorem B1324859 : Blo 1323480 1324859 := bstep (se 1 (by rfl) ⟨993644, by rfl⟩ : syracuseStep 1324859 = 1987289) B1987289
theorem B1677115 : Blo 1323480 1677115 := bstep (se 1 (by rfl) ⟨1257836, by rfl⟩ : syracuseStep 1677115 = 2515673) B2515673
theorem B12719987 : Blo 1323480 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B3397511 : Blo 1323480 3397511 := bstep (se 1 (by rfl) ⟨2548133, by rfl⟩ : syracuseStep 3397511 = 5096267) B5096267
theorem B2979719 : Blo 1323480 2979719 := bstep (se 1 (by rfl) ⟨2234789, by rfl⟩ : syracuseStep 2979719 = 4469579) B4469579
theorem B1324935 : Blo 1323480 1324935 := bstep (se 1 (by rfl) ⟨993701, by rfl⟩ : syracuseStep 1324935 = 1987403) B1987403
theorem B1324943 : Blo 1323480 1324943 := bstep (se 1 (by rfl) ⟨993707, by rfl⟩ : syracuseStep 1324943 = 1987415) B1987415
theorem B2234297 : Blo 1323480 2234297 := bstep (se 2 (by rfl) ⟨837861, by rfl⟩ : syracuseStep 2234297 = 1675723) B1675723
theorem B4470713 : Blo 1323480 4470713 := bstep (se 2 (by rfl) ⟨1676517, by rfl⟩ : syracuseStep 4470713 = 3353035) B3353035
theorem B1324987 : Blo 1323480 1324987 := bstep (se 1 (by rfl) ⟨993740, by rfl⟩ : syracuseStep 1324987 = 1987481) B1987481
theorem B1325063 : Blo 1323480 1325063 := bstep (se 1 (by rfl) ⟨993797, by rfl⟩ : syracuseStep 1325063 = 1987595) B1987595
theorem B1325071 : Blo 1323480 1325071 := bstep (se 1 (by rfl) ⟨993803, by rfl⟩ : syracuseStep 1325071 = 1987607) B1987607
theorem B4773917 : Blo 1323480 4773917 := bstep (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) B1790219
theorem B2512939 : Blo 1323480 2512939 := bstep (se 1 (by rfl) ⟨1884704, by rfl⟩ : syracuseStep 2512939 = 3769409) B3769409
theorem B7542827 : Blo 1323480 7542827 := bstep (se 1 (by rfl) ⟨5657120, by rfl⟩ : syracuseStep 7542827 = 11314241) B11314241
theorem B1488955 : Blo 1323480 1488955 := bstep (se 1 (by rfl) ⟨1116716, by rfl⟩ : syracuseStep 1488955 = 2233433) B2233433
theorem B2979899 : Blo 1323480 2979899 := bstep (se 1 (by rfl) ⟨2234924, by rfl⟩ : syracuseStep 2979899 = 4469849) B4469849
theorem B14325821 : Blo 1323480 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B1325115 : Blo 1323480 1325115 := bstep (se 1 (by rfl) ⟨993836, by rfl⟩ : syracuseStep 1325115 = 1987673) B1987673
theorem B2513015 : Blo 1323480 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B1325191 : Blo 1323480 1325191 := bstep (se 1 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 1325191 = 1987787) B1987787
theorem B1325199 : Blo 1323480 1325199 := bstep (se 1 (by rfl) ⟨993899, by rfl⟩ : syracuseStep 1325199 = 1987799) B1987799
theorem B2980025 : Blo 1323480 2980025 := bstep (se 2 (by rfl) ⟨1117509, by rfl⟩ : syracuseStep 2980025 = 2235019) B2235019
theorem B1325243 : Blo 1323480 1325243 := bstep (se 1 (by rfl) ⟨993932, by rfl⟩ : syracuseStep 1325243 = 1987865) B1987865
theorem B16963829 : Blo 1323480 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B1325319 : Blo 1323480 1325319 := bstep (se 1 (by rfl) ⟨993989, by rfl⟩ : syracuseStep 1325319 = 1987979) B1987979
theorem B1325327 : Blo 1323480 1325327 := bstep (se 1 (by rfl) ⟨993995, by rfl⟩ : syracuseStep 1325327 = 1987991) B1987991
theorem B7649569 : Blo 1323480 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B1325371 : Blo 1323480 1325371 := bstep (se 1 (by rfl) ⟨994028, by rfl⟩ : syracuseStep 1325371 = 1988057) B1988057
theorem B1325447 : Blo 1323480 1325447 := bstep (se 1 (by rfl) ⟨994085, by rfl⟩ : syracuseStep 1325447 = 1988171) B1988171
theorem B1325455 : Blo 1323480 1325455 := bstep (se 1 (by rfl) ⟨994091, by rfl⟩ : syracuseStep 1325455 = 1988183) B1988183
theorem B6707609 : Blo 1323480 6707609 := bstep (se 2 (by rfl) ⟨2515353, by rfl⟩ : syracuseStep 6707609 = 5030707) B5030707
theorem B4471307 : Blo 1323480 4471307 := bstep (se 1 (by rfl) ⟨3353480, by rfl⟩ : syracuseStep 4471307 = 6706961) B6706961
theorem B1489423 : Blo 1323480 1489423 := bstep (se 1 (by rfl) ⟨1117067, by rfl⟩ : syracuseStep 1489423 = 2234135) B2234135
theorem B2980367 : Blo 1323480 2980367 := bstep (se 1 (by rfl) ⟨2235275, by rfl⟩ : syracuseStep 2980367 = 4470551) B4470551
theorem B2980385 : Blo 1323480 2980385 := bstep (se 2 (by rfl) ⟨1117644, by rfl⟩ : syracuseStep 2980385 = 2235289) B2235289
theorem B2234999 : Blo 1323480 2234999 := bstep (se 1 (by rfl) ⟨1676249, by rfl⟩ : syracuseStep 2234999 = 3352499) B3352499
theorem B4471415 : Blo 1323480 4471415 := bstep (se 1 (by rfl) ⟨3353561, by rfl⟩ : syracuseStep 4471415 = 6707123) B6707123
theorem B2980727 : Blo 1323480 2980727 := bstep (se 1 (by rfl) ⟨2235545, by rfl⟩ : syracuseStep 2980727 = 4471091) B4471091
theorem B16120727 : Blo 1323480 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B1489927 : Blo 1323480 1489927 := bstep (se 1 (by rfl) ⟨1117445, by rfl⟩ : syracuseStep 1489927 = 2234891) B2234891
theorem B3578923 : Blo 1323480 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B2980907 : Blo 1323480 2980907 := bstep (se 1 (by rfl) ⟨2235680, by rfl⟩ : syracuseStep 2980907 = 4471361) B4471361
theorem B2235451 : Blo 1323480 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B3103879 : Blo 1323480 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B1490107 : Blo 1323480 1490107 := bstep (se 1 (by rfl) ⟨1117580, by rfl⟩ : syracuseStep 1490107 = 2235161) B2235161
theorem B15088841 : Blo 1323480 15088841 := bstep (se 2 (by rfl) ⟨5658315, by rfl⟩ : syracuseStep 15088841 = 11316631) B11316631
theorem B2235593 : Blo 1323480 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B4472009 : Blo 1323480 4472009 := bstep (se 2 (by rfl) ⟨1677003, by rfl⟩ : syracuseStep 4472009 = 3354007) B3354007
theorem B2014471 : Blo 1323480 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B5029235 : Blo 1323480 5029235 := bstep (se 1 (by rfl) ⟨3771926, by rfl⟩ : syracuseStep 5029235 = 7543853) B7543853
theorem B11312531 : Blo 1323480 11312531 := bstep (se 1 (by rfl) ⟨8484398, by rfl⟩ : syracuseStep 11312531 = 16968797) B16968797
theorem B2981267 : Blo 1323480 2981267 := bstep (se 1 (by rfl) ⟨2235950, by rfl⟩ : syracuseStep 2981267 = 4471901) B4471901
theorem B2981321 : Blo 1323480 2981321 := bstep (se 2 (by rfl) ⟨1117995, by rfl⟩ : syracuseStep 2981321 = 2235991) B2235991
theorem B7544285 : Blo 1323480 7544285 := bstep (se 3 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 7544285 = 2829107) B2829107
theorem B4030087 : Blo 1323480 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B1490575 : Blo 1323480 1490575 := bstep (se 1 (by rfl) ⟨1117931, by rfl⟩ : syracuseStep 1490575 = 2235863) B2235863
theorem B108764977 : Blo 1323480 108764977 := bstep (se 2 (by rfl) ⟨40786866, by rfl⟩ : syracuseStep 108764977 = 81573733) B81573733
theorem B2236295 : Blo 1323480 2236295 := bstep (se 1 (by rfl) ⟨1677221, by rfl⟩ : syracuseStep 2236295 = 3354443) B3354443
theorem B4472711 : Blo 1323480 4472711 := bstep (se 1 (by rfl) ⟨3354533, by rfl⟩ : syracuseStep 4472711 = 6709067) B6709067
theorem B7651219 : Blo 1323480 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B12083107 : Blo 1323480 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B7544785 : Blo 1323480 7544785 := bstep (se 2 (by rfl) ⟨2829294, by rfl⟩ : syracuseStep 7544785 = 5658589) B5658589
theorem B2236423 : Blo 1323480 2236423 := bstep (se 1 (by rfl) ⟨1677317, by rfl⟩ : syracuseStep 2236423 = 3354635) B3354635
theorem B3350585 : Blo 1323480 3350585 := bstep (se 2 (by rfl) ⟨1256469, by rfl⟩ : syracuseStep 3350585 = 2512939) B2512939
theorem B4775993 : Blo 1323480 4775993 := bstep (se 2 (by rfl) ⟨1790997, by rfl⟩ : syracuseStep 4775993 = 3581995) B3581995
theorem B81510461 : Blo 1323480 81510461 := bstep (se 3 (by rfl) ⟨15283211, by rfl⟩ : syracuseStep 81510461 = 30566423) B30566423
theorem B12730445 : Blo 1323480 12730445 := bstep (se 3 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 12730445 = 4773917) B4773917
theorem B2982059 : Blo 1323480 2982059 := bstep (se 1 (by rfl) ⟨2236544, by rfl⟩ : syracuseStep 2982059 = 4473089) B4473089
theorem B19087589 : Blo 1323480 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B85909733 : Blo 1323480 85909733 := bstep (se 4 (by rfl) ⟨8054037, by rfl⟩ : syracuseStep 85909733 = 16108075) B16108075
theorem B2515475 : Blo 1323480 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B4473467 : Blo 1323480 4473467 := bstep (se 1 (by rfl) ⟨3355100, by rfl⟩ : syracuseStep 4473467 = 6710201) B6710201
theorem B2515627 : Blo 1323480 2515627 := bstep (se 1 (by rfl) ⟨1886720, by rfl⟩ : syracuseStep 2515627 = 3773441) B3773441
theorem B3769021 : Blo 1323480 3769021 := bstep (se 3 (by rfl) ⟨706691, by rfl⟩ : syracuseStep 3769021 = 1413383) B1413383
theorem B6701777 : Blo 1323480 6701777 := bstep (se 2 (by rfl) ⟨2513166, by rfl⟩ : syracuseStep 6701777 = 5026333) B5026333
theorem B2515855 : Blo 1323480 2515855 := bstep (se 1 (by rfl) ⟨1886891, by rfl⟩ : syracuseStep 2515855 = 3773783) B3773783
theorem B3769249 : Blo 1323480 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B4776887 : Blo 1323480 4776887 := bstep (se 1 (by rfl) ⟨3582665, by rfl⟩ : syracuseStep 4776887 = 7165331) B7165331
theorem B2515931 : Blo 1323480 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B12248113 : Blo 1323480 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B8479991 : Blo 1323480 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B3769591 : Blo 1323480 3769591 := bstep (se 1 (by rfl) ⟨2827193, by rfl⟩ : syracuseStep 3769591 = 5654387) B5654387
theorem B5031179 : Blo 1323480 5031179 := bstep (se 1 (by rfl) ⟨3773384, by rfl⟩ : syracuseStep 5031179 = 7546769) B7546769
theorem B10061171 : Blo 1323480 10061171 := bstep (se 1 (by rfl) ⟨7545878, by rfl⟩ : syracuseStep 10061171 = 15091757) B15091757
theorem B40797701 : Blo 1323480 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B3769865 : Blo 1323480 3769865 := bstep (se 2 (by rfl) ⟨1413699, by rfl⟩ : syracuseStep 3769865 = 2827399) B2827399
theorem B4138505 : Blo 1323480 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B5654215 : Blo 1323480 5654215 := bstep (se 1 (by rfl) ⟨4240661, by rfl⟩ : syracuseStep 5654215 = 8481323) B8481323
theorem B2868935 : Blo 1323480 2868935 := bstep (se 1 (by rfl) ⟨2151701, by rfl⟩ : syracuseStep 2868935 = 4303403) B4303403
theorem B32237473 : Blo 1323480 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B7161871 : Blo 1323480 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B3770525 : Blo 1323480 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B3352823 : Blo 1323480 3352823 := bstep (se 1 (by rfl) ⟨2514617, by rfl⟩ : syracuseStep 3352823 = 5029235) B5029235
theorem B32229683 : Blo 1323480 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B1886647 : Blo 1323480 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B8604107 : Blo 1323480 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B3770867 : Blo 1323480 3770867 := bstep (se 1 (by rfl) ⟨2828150, by rfl⟩ : syracuseStep 3770867 = 5656301) B5656301
theorem B10201625 : Blo 1323480 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B5032637 : Blo 1323480 5032637 := bstep (se 3 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 5032637 = 1887239) B1887239
theorem B1985273 : Blo 1323480 1985273 := bstep (se 2 (by rfl) ⟨744477, by rfl⟩ : syracuseStep 1985273 = 1488955) B1488955
theorem B8162051 : Blo 1323480 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B1985375 : Blo 1323480 1985375 := bstep (se 1 (by rfl) ⟨1489031, by rfl⟩ : syracuseStep 1985375 = 2978063) B2978063
theorem B1985387 : Blo 1323480 1985387 := bstep (se 1 (by rfl) ⟨1489040, by rfl⟩ : syracuseStep 1985387 = 2978081) B2978081
theorem B3771323 : Blo 1323480 3771323 := bstep (se 1 (by rfl) ⟨2828492, by rfl⟩ : syracuseStep 3771323 = 5656985) B5656985
theorem B1985615 : Blo 1323480 1985615 := bstep (se 1 (by rfl) ⟨1489211, by rfl⟩ : syracuseStep 1985615 = 2978423) B2978423
theorem B6704207 : Blo 1323480 6704207 := bstep (se 1 (by rfl) ⟨5028155, by rfl⟩ : syracuseStep 6704207 = 10056311) B10056311
theorem B2722987 : Blo 1323480 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B1985735 : Blo 1323480 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B4467959 : Blo 1323480 4467959 := bstep (se 1 (by rfl) ⟨3350969, by rfl⟩ : syracuseStep 4467959 = 6701939) B6701939
theorem B19107089 : Blo 1323480 19107089 := bstep (se 2 (by rfl) ⟨7165158, by rfl⟩ : syracuseStep 19107089 = 14330317) B14330317
theorem B1985897 : Blo 1323480 1985897 := bstep (se 2 (by rfl) ⟨744711, by rfl⟩ : syracuseStep 1985897 = 1489423) B1489423
theorem B5025149 : Blo 1323480 5025149 := bstep (se 3 (by rfl) ⟨942215, by rfl⟩ : syracuseStep 5025149 = 1884431) B1884431
theorem B1985975 : Blo 1323480 1985975 := bstep (se 1 (by rfl) ⟨1489481, by rfl⟩ : syracuseStep 1985975 = 2978963) B2978963
theorem B1986011 : Blo 1323480 1986011 := bstep (se 1 (by rfl) ⟨1489508, by rfl⟩ : syracuseStep 1986011 = 2979017) B2979017
theorem B5656027 : Blo 1323480 5656027 := bstep (se 1 (by rfl) ⟨4242020, by rfl⟩ : syracuseStep 5656027 = 8484041) B8484041
theorem B4468283 : Blo 1323480 4468283 := bstep (se 1 (by rfl) ⟨3351212, by rfl⟩ : syracuseStep 4468283 = 6702425) B6702425
theorem B6794941 : Blo 1323480 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B3354311 : Blo 1323480 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B6704855 : Blo 1323480 6704855 := bstep (se 1 (by rfl) ⟨5028641, by rfl⟩ : syracuseStep 6704855 = 10057283) B10057283
theorem B6368989 : Blo 1323480 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B8482553 : Blo 1323480 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B4468553 : Blo 1323480 4468553 := bstep (se 2 (by rfl) ⟨1675707, by rfl⟩ : syracuseStep 4468553 = 3351415) B3351415
theorem B42938261 : Blo 1323480 42938261 := bstep (se 6 (by rfl) ⟨1006365, by rfl⟩ : syracuseStep 42938261 = 2012731) B2012731
theorem B2265007 : Blo 1323480 2265007 := bstep (se 1 (by rfl) ⟨1698755, by rfl⟩ : syracuseStep 2265007 = 3397511) B3397511
theorem B1986479 : Blo 1323480 1986479 := bstep (se 1 (by rfl) ⟨1489859, by rfl⟩ : syracuseStep 1986479 = 2979719) B2979719
theorem B1986569 : Blo 1323480 1986569 := bstep (se 2 (by rfl) ⟨744963, by rfl⟩ : syracuseStep 1986569 = 1489927) B1489927
theorem B9056285 : Blo 1323480 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B1986599 : Blo 1323480 1986599 := bstep (se 1 (by rfl) ⟨1489949, by rfl⟩ : syracuseStep 1986599 = 2979899) B2979899
theorem B2388025 : Blo 1323480 2388025 := bstep (se 2 (by rfl) ⟨895509, by rfl⟩ : syracuseStep 2388025 = 1791019) B1791019
theorem B1675343 : Blo 1323480 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1986683 : Blo 1323480 1986683 := bstep (se 1 (by rfl) ⟨1490012, by rfl⟩ : syracuseStep 1986683 = 2980025) B2980025
theorem B11309219 : Blo 1323480 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B2683091 : Blo 1323480 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B1986809 : Blo 1323480 1986809 := bstep (se 2 (by rfl) ⟨745053, by rfl⟩ : syracuseStep 1986809 = 1490107) B1490107
theorem B1986911 : Blo 1323480 1986911 := bstep (se 1 (by rfl) ⟨1490183, by rfl⟩ : syracuseStep 1986911 = 2980367) B2980367
theorem B2978153 : Blo 1323480 2978153 := bstep (se 2 (by rfl) ⟨1116807, by rfl⟩ : syracuseStep 2978153 = 2233615) B2233615
theorem B1986923 : Blo 1323480 1986923 := bstep (se 1 (by rfl) ⟨1490192, by rfl⟩ : syracuseStep 1986923 = 2980385) B2980385
theorem B1323483 : Blo 1323480 1323483 := bstep (se 1 (by rfl) ⟨992612, by rfl⟩ : syracuseStep 1323483 = 1985225) B1985225
theorem B14316041 : Blo 1323480 14316041 := bstep (se 2 (by rfl) ⟨5368515, by rfl⟩ : syracuseStep 14316041 = 10737031) B10737031
theorem B8491553 : Blo 1323480 8491553 := bstep (se 2 (by rfl) ⟨3184332, by rfl⟩ : syracuseStep 8491553 = 6368665) B6368665
theorem B1323559 : Blo 1323480 1323559 := bstep (se 1 (by rfl) ⟨992669, by rfl⟩ : syracuseStep 1323559 = 1985339) B1985339
theorem B1323599 : Blo 1323480 1323599 := bstep (se 1 (by rfl) ⟨992699, by rfl⟩ : syracuseStep 1323599 = 1985399) B1985399
theorem B1987151 : Blo 1323480 1987151 := bstep (se 1 (by rfl) ⟨1490363, by rfl⟩ : syracuseStep 1987151 = 2980727) B2980727
theorem B1323615 : Blo 1323480 1323615 := bstep (se 1 (by rfl) ⟨992711, by rfl⟩ : syracuseStep 1323615 = 1985423) B1985423
theorem B1323643 : Blo 1323480 1323643 := bstep (se 1 (by rfl) ⟨992732, by rfl⟩ : syracuseStep 1323643 = 1985465) B1985465
theorem B1323695 : Blo 1323480 1323695 := bstep (se 1 (by rfl) ⟨992771, by rfl⟩ : syracuseStep 1323695 = 1985543) B1985543
theorem B1323719 : Blo 1323480 1323719 := bstep (se 1 (by rfl) ⟨992789, by rfl⟩ : syracuseStep 1323719 = 1985579) B1985579
theorem B1987271 : Blo 1323480 1987271 := bstep (se 1 (by rfl) ⟨1490453, by rfl⟩ : syracuseStep 1987271 = 2980907) B2980907
theorem B1323739 : Blo 1323480 1323739 := bstep (se 1 (by rfl) ⟨992804, by rfl⟩ : syracuseStep 1323739 = 1985609) B1985609
theorem B1323815 : Blo 1323480 1323815 := bstep (se 1 (by rfl) ⟨992861, by rfl⟩ : syracuseStep 1323815 = 1985723) B1985723
theorem B4240201 : Blo 1323480 4240201 := bstep (se 2 (by rfl) ⟨1590075, by rfl⟩ : syracuseStep 4240201 = 3180151) B3180151
theorem B1323855 : Blo 1323480 1323855 := bstep (se 1 (by rfl) ⟨992891, by rfl⟩ : syracuseStep 1323855 = 1985783) B1985783
theorem B1323871 : Blo 1323480 1323871 := bstep (se 1 (by rfl) ⟨992903, by rfl⟩ : syracuseStep 1323871 = 1985807) B1985807
theorem B1987433 : Blo 1323480 1987433 := bstep (se 2 (by rfl) ⟨745287, by rfl⟩ : syracuseStep 1987433 = 1490575) B1490575
theorem B1323899 : Blo 1323480 1323899 := bstep (se 1 (by rfl) ⟨992924, by rfl⟩ : syracuseStep 1323899 = 1985849) B1985849
theorem B1323951 : Blo 1323480 1323951 := bstep (se 1 (by rfl) ⟨992963, by rfl⟩ : syracuseStep 1323951 = 1985927) B1985927
theorem B7541687 : Blo 1323480 7541687 := bstep (se 1 (by rfl) ⟨5656265, by rfl⟩ : syracuseStep 7541687 = 11312531) B11312531
theorem B4469687 : Blo 1323480 4469687 := bstep (se 1 (by rfl) ⟨3352265, by rfl⟩ : syracuseStep 4469687 = 6704531) B6704531
theorem B1987511 : Blo 1323480 1987511 := bstep (se 1 (by rfl) ⟨1490633, by rfl⟩ : syracuseStep 1987511 = 2981267) B2981267
theorem B2978747 : Blo 1323480 2978747 := bstep (se 1 (by rfl) ⟨2234060, by rfl⟩ : syracuseStep 2978747 = 4468121) B4468121
theorem B1323975 : Blo 1323480 1323975 := bstep (se 1 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 1323975 = 1985963) B1985963
theorem B1323995 : Blo 1323480 1323995 := bstep (se 1 (by rfl) ⟨992996, by rfl⟩ : syracuseStep 1323995 = 1985993) B1985993
theorem B1987547 : Blo 1323480 1987547 := bstep (se 1 (by rfl) ⟨1490660, by rfl⟩ : syracuseStep 1987547 = 2981321) B2981321
theorem B1324071 : Blo 1323480 1324071 := bstep (se 1 (by rfl) ⟨993053, by rfl⟩ : syracuseStep 1324071 = 1986107) B1986107
theorem B2978873 : Blo 1323480 2978873 := bstep (se 2 (by rfl) ⟨1117077, by rfl⟩ : syracuseStep 2978873 = 2234155) B2234155
theorem B38188097 : Blo 1323480 38188097 := bstep (se 2 (by rfl) ⟨14320536, by rfl⟩ : syracuseStep 38188097 = 28641073) B28641073
theorem B145019969 : Blo 1323480 145019969 := bstep (se 2 (by rfl) ⟨54382488, by rfl⟩ : syracuseStep 145019969 = 108764977) B108764977
theorem B1324111 : Blo 1323480 1324111 := bstep (se 1 (by rfl) ⟨993083, by rfl⟩ : syracuseStep 1324111 = 1986167) B1986167
theorem B1324127 : Blo 1323480 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1324155 : Blo 1323480 1324155 := bstep (se 1 (by rfl) ⟨993116, by rfl⟩ : syracuseStep 1324155 = 1986233) B1986233
theorem B1324207 : Blo 1323480 1324207 := bstep (se 1 (by rfl) ⟨993155, by rfl⟩ : syracuseStep 1324207 = 1986311) B1986311
theorem B1324231 : Blo 1323480 1324231 := bstep (se 1 (by rfl) ⟨993173, by rfl⟩ : syracuseStep 1324231 = 1986347) B1986347
theorem B40793291 : Blo 1323480 40793291 := bstep (se 1 (by rfl) ⟨30594968, by rfl⟩ : syracuseStep 40793291 = 61189937) B61189937
theorem B16110809 : Blo 1323480 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B1324251 : Blo 1323480 1324251 := bstep (se 1 (by rfl) ⟨993188, by rfl⟩ : syracuseStep 1324251 = 1986377) B1986377
theorem B1324327 : Blo 1323480 1324327 := bstep (se 1 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 1324327 = 1986491) B1986491
theorem B1324367 : Blo 1323480 1324367 := bstep (se 1 (by rfl) ⟨993275, by rfl⟩ : syracuseStep 1324367 = 1986551) B1986551
theorem B1324383 : Blo 1323480 1324383 := bstep (se 1 (by rfl) ⟨993287, by rfl⟩ : syracuseStep 1324383 = 1986575) B1986575
theorem B1676639 : Blo 1323480 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B1324411 : Blo 1323480 1324411 := bstep (se 1 (by rfl) ⟨993308, by rfl⟩ : syracuseStep 1324411 = 1986617) B1986617
theorem B2979215 : Blo 1323480 2979215 := bstep (se 1 (by rfl) ⟨2234411, by rfl⟩ : syracuseStep 2979215 = 4468823) B4468823
theorem B9541027 : Blo 1323480 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B1324463 : Blo 1323480 1324463 := bstep (se 1 (by rfl) ⟨993347, by rfl⟩ : syracuseStep 1324463 = 1986695) B1986695
theorem B1988015 : Blo 1323480 1988015 := bstep (se 1 (by rfl) ⟨1491011, by rfl⟩ : syracuseStep 1988015 = 2982023) B2982023
theorem B1324487 : Blo 1323480 1324487 := bstep (se 1 (by rfl) ⟨993365, by rfl⟩ : syracuseStep 1324487 = 1986731) B1986731
theorem B5027291 : Blo 1323480 5027291 := bstep (se 1 (by rfl) ⟨3770468, by rfl⟩ : syracuseStep 5027291 = 7540937) B7540937
theorem B1324507 : Blo 1323480 1324507 := bstep (se 1 (by rfl) ⟨993380, by rfl⟩ : syracuseStep 1324507 = 1986761) B1986761
theorem B2233865 : Blo 1323480 2233865 := bstep (se 2 (by rfl) ⟨837699, by rfl⟩ : syracuseStep 2233865 = 1675399) B1675399
theorem B4470281 : Blo 1323480 4470281 := bstep (se 2 (by rfl) ⟨1676355, by rfl⟩ : syracuseStep 4470281 = 3352711) B3352711
theorem B1988105 : Blo 1323480 1988105 := bstep (se 2 (by rfl) ⟨745539, by rfl⟩ : syracuseStep 1988105 = 1491079) B1491079
theorem B1324583 : Blo 1323480 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B1988135 : Blo 1323480 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B1324623 : Blo 1323480 1324623 := bstep (se 1 (by rfl) ⟨993467, by rfl⟩ : syracuseStep 1324623 = 1986935) B1986935
theorem B1324639 : Blo 1323480 1324639 := bstep (se 1 (by rfl) ⟨993479, by rfl⟩ : syracuseStep 1324639 = 1986959) B1986959
theorem B7542395 : Blo 1323480 7542395 := bstep (se 1 (by rfl) ⟨5656796, by rfl⟩ : syracuseStep 7542395 = 11313593) B11313593
theorem B1324667 : Blo 1323480 1324667 := bstep (se 1 (by rfl) ⟨993500, by rfl⟩ : syracuseStep 1324667 = 1987001) B1987001
theorem B1988219 : Blo 1323480 1988219 := bstep (se 1 (by rfl) ⟨1491164, by rfl⟩ : syracuseStep 1988219 = 2982329) B2982329
theorem B9541259 : Blo 1323480 9541259 := bstep (se 1 (by rfl) ⟨7155944, by rfl⟩ : syracuseStep 9541259 = 14311889) B14311889
theorem B2234027 : Blo 1323480 2234027 := bstep (se 1 (by rfl) ⟨1675520, by rfl⟩ : syracuseStep 2234027 = 3351041) B3351041
theorem B1324719 : Blo 1323480 1324719 := bstep (se 1 (by rfl) ⟨993539, by rfl⟩ : syracuseStep 1324719 = 1987079) B1987079
theorem B1324743 : Blo 1323480 1324743 := bstep (se 1 (by rfl) ⟨993557, by rfl⟩ : syracuseStep 1324743 = 1987115) B1987115
theorem B2979539 : Blo 1323480 2979539 := bstep (se 1 (by rfl) ⟨2234654, by rfl⟩ : syracuseStep 2979539 = 4469309) B4469309
theorem B1324763 : Blo 1323480 1324763 := bstep (se 1 (by rfl) ⟨993572, by rfl⟩ : syracuseStep 1324763 = 1987145) B1987145
theorem B1324839 : Blo 1323480 1324839 := bstep (se 1 (by rfl) ⟨993629, by rfl⟩ : syracuseStep 1324839 = 1987259) B1987259
theorem B1324879 : Blo 1323480 1324879 := bstep (se 1 (by rfl) ⟨993659, by rfl⟩ : syracuseStep 1324879 = 1987319) B1987319
theorem B6362975 : Blo 1323480 6362975 := bstep (se 1 (by rfl) ⟨4772231, by rfl⟩ : syracuseStep 6362975 = 9544463) B9544463
theorem B1324895 : Blo 1323480 1324895 := bstep (se 1 (by rfl) ⟨993671, by rfl⟩ : syracuseStep 1324895 = 1987343) B1987343
theorem B1324923 : Blo 1323480 1324923 := bstep (se 1 (by rfl) ⟨993692, by rfl⟩ : syracuseStep 1324923 = 1987385) B1987385
theorem B1324975 : Blo 1323480 1324975 := bstep (se 1 (by rfl) ⟨993731, by rfl⟩ : syracuseStep 1324975 = 1987463) B1987463
theorem B1324999 : Blo 1323480 1324999 := bstep (se 1 (by rfl) ⟨993749, by rfl⟩ : syracuseStep 1324999 = 1987499) B1987499
theorem B1325019 : Blo 1323480 1325019 := bstep (se 1 (by rfl) ⟨993764, by rfl⟩ : syracuseStep 1325019 = 1987529) B1987529
theorem B1325095 : Blo 1323480 1325095 := bstep (se 1 (by rfl) ⟨993821, by rfl⟩ : syracuseStep 1325095 = 1987643) B1987643
theorem B2234425 : Blo 1323480 2234425 := bstep (se 2 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 2234425 = 1675819) B1675819
theorem B1325135 : Blo 1323480 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B1325151 : Blo 1323480 1325151 := bstep (se 1 (by rfl) ⟨993863, by rfl⟩ : syracuseStep 1325151 = 1987727) B1987727
theorem B1325179 : Blo 1323480 1325179 := bstep (se 1 (by rfl) ⟨993884, by rfl⟩ : syracuseStep 1325179 = 1987769) B1987769
theorem B1325231 : Blo 1323480 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B2234567 : Blo 1323480 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1325255 : Blo 1323480 1325255 := bstep (se 1 (by rfl) ⟨993941, by rfl⟩ : syracuseStep 1325255 = 1987883) B1987883
theorem B1325275 : Blo 1323480 1325275 := bstep (se 1 (by rfl) ⟨993956, by rfl⟩ : syracuseStep 1325275 = 1987913) B1987913
theorem B1325351 : Blo 1323480 1325351 := bstep (se 1 (by rfl) ⟨994013, by rfl⟩ : syracuseStep 1325351 = 1988027) B1988027
theorem B1325391 : Blo 1323480 1325391 := bstep (se 1 (by rfl) ⟨994043, by rfl⟩ : syracuseStep 1325391 = 1988087) B1988087
theorem B1325407 : Blo 1323480 1325407 := bstep (se 1 (by rfl) ⟨994055, by rfl⟩ : syracuseStep 1325407 = 1988111) B1988111
theorem B2234729 : Blo 1323480 2234729 := bstep (se 2 (by rfl) ⟨838023, by rfl⟩ : syracuseStep 2234729 = 1676047) B1676047
theorem B7543145 : Blo 1323480 7543145 := bstep (se 2 (by rfl) ⟨2828679, by rfl⟩ : syracuseStep 7543145 = 5657359) B5657359
theorem B4471145 : Blo 1323480 4471145 := bstep (se 2 (by rfl) ⟨1676679, by rfl⟩ : syracuseStep 4471145 = 3353359) B3353359
theorem B1325435 : Blo 1323480 1325435 := bstep (se 1 (by rfl) ⟨994076, by rfl⟩ : syracuseStep 1325435 = 1988153) B1988153
theorem B30579079 : Blo 1323480 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B4528699 : Blo 1323480 4528699 := bstep (se 1 (by rfl) ⟨3396524, by rfl⟩ : syracuseStep 4528699 = 6793049) B6793049
theorem B6707771 : Blo 1323480 6707771 := bstep (se 1 (by rfl) ⟨5030828, by rfl⟩ : syracuseStep 6707771 = 10061657) B10061657
theorem B2513531 : Blo 1323480 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B1489531 : Blo 1323480 1489531 := bstep (se 1 (by rfl) ⟨1117148, by rfl⟩ : syracuseStep 1489531 = 2234297) B2234297
theorem B2980475 : Blo 1323480 2980475 := bstep (se 1 (by rfl) ⟨2235356, by rfl⟩ : syracuseStep 2980475 = 4470713) B4470713
theorem B12737209 : Blo 1323480 12737209 := bstep (se 2 (by rfl) ⟨4776453, by rfl⟩ : syracuseStep 12737209 = 9552907) B9552907
theorem B5028551 : Blo 1323480 5028551 := bstep (se 1 (by rfl) ⟨3771413, by rfl⟩ : syracuseStep 5028551 = 7542827) B7542827
theorem B9550547 : Blo 1323480 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B2235127 : Blo 1323480 2235127 := bstep (se 1 (by rfl) ⟨1676345, by rfl⟩ : syracuseStep 2235127 = 3352691) B3352691
theorem B2980601 : Blo 1323480 2980601 := bstep (se 2 (by rfl) ⟨1117725, by rfl⟩ : syracuseStep 2980601 = 2235451) B2235451
theorem B163093337 : Blo 1323480 163093337 := bstep (se 2 (by rfl) ⟨61160001, by rfl⟩ : syracuseStep 163093337 = 122320003) B122320003
theorem B10050479 : Blo 1323480 10050479 := bstep (se 1 (by rfl) ⟨7537859, by rfl⟩ : syracuseStep 10050479 = 15075719) B15075719
theorem B2235323 : Blo 1323480 2235323 := bstep (se 1 (by rfl) ⟨1676492, by rfl⟩ : syracuseStep 2235323 = 3352985) B3352985
theorem B4471739 : Blo 1323480 4471739 := bstep (se 1 (by rfl) ⟨3353804, by rfl⟩ : syracuseStep 4471739 = 6707609) B6707609
theorem B2980871 : Blo 1323480 2980871 := bstep (se 1 (by rfl) ⟨2235653, by rfl⟩ : syracuseStep 2980871 = 4471307) B4471307
theorem B2685961 : Blo 1323480 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B2235431 : Blo 1323480 2235431 := bstep (se 1 (by rfl) ⟨1676573, by rfl⟩ : syracuseStep 2235431 = 3353147) B3353147
theorem B1489999 : Blo 1323480 1489999 := bstep (se 1 (by rfl) ⟨1117499, by rfl⟩ : syracuseStep 1489999 = 2234999) B2234999
theorem B2980943 : Blo 1323480 2980943 := bstep (se 1 (by rfl) ⟨2235707, by rfl⟩ : syracuseStep 2980943 = 4471415) B4471415
theorem B2514017 : Blo 1323480 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B16964801 : Blo 1323480 16964801 := bstep (se 2 (by rfl) ⟨6361800, by rfl⟩ : syracuseStep 16964801 = 12723601) B12723601
theorem B6708419 : Blo 1323480 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B2514169 : Blo 1323480 2514169 := bstep (se 2 (by rfl) ⟨942813, by rfl⟩ : syracuseStep 2514169 = 1885627) B1885627
theorem B10747151 : Blo 1323480 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B2235721 : Blo 1323480 2235721 := bstep (se 2 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 2235721 = 1676791) B1676791
theorem B2235755 : Blo 1323480 2235755 := bstep (se 1 (by rfl) ⟨1676816, by rfl⟩ : syracuseStep 2235755 = 3353633) B3353633
theorem B5029249 : Blo 1323480 5029249 := bstep (se 2 (by rfl) ⟨1885968, by rfl⟩ : syracuseStep 5029249 = 3771937) B3771937
theorem B2388487 : Blo 1323480 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B10059227 : Blo 1323480 10059227 := bstep (se 1 (by rfl) ⟨7544420, by rfl⟩ : syracuseStep 10059227 = 15088841) B15088841
theorem B1490395 : Blo 1323480 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B2981339 : Blo 1323480 2981339 := bstep (se 1 (by rfl) ⟨2236004, by rfl⟩ : syracuseStep 2981339 = 4472009) B4472009
theorem B5373449 : Blo 1323480 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B5029523 : Blo 1323480 5029523 := bstep (se 1 (by rfl) ⟨3772142, by rfl⟩ : syracuseStep 5029523 = 7544285) B7544285
theorem B3350231 : Blo 1323480 3350231 := bstep (se 1 (by rfl) ⟨2512673, by rfl⟩ : syracuseStep 3350231 = 5025347) B5025347
theorem B2236153 : Blo 1323480 2236153 := bstep (se 2 (by rfl) ⟨838557, by rfl⟩ : syracuseStep 2236153 = 1677115) B1677115
theorem B1490863 : Blo 1323480 1490863 := bstep (se 1 (by rfl) ⟨1118147, by rfl⟩ : syracuseStep 1490863 = 2236295) B2236295
theorem B2981807 : Blo 1323480 2981807 := bstep (se 1 (by rfl) ⟨2236355, by rfl⟩ : syracuseStep 2981807 = 4472711) B4472711
theorem B10059713 : Blo 1323480 10059713 := bstep (se 2 (by rfl) ⟨3772392, by rfl⟩ : syracuseStep 10059713 = 7544785) B7544785
theorem B2981897 : Blo 1323480 2981897 := bstep (se 2 (by rfl) ⟨1118211, by rfl⟩ : syracuseStep 2981897 = 2236423) B2236423
theorem B6037523 : Blo 1323480 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B8486963 : Blo 1323480 8486963 := bstep (se 1 (by rfl) ⟨6365222, by rfl⟩ : syracuseStep 8486963 = 12730445) B12730445
theorem B9544027 : Blo 1323480 9544027 := bstep (se 1 (by rfl) ⟨7158020, by rfl⟩ : syracuseStep 9544027 = 14316041) B14316041
theorem B5661035 : Blo 1323480 5661035 := bstep (se 1 (by rfl) ⟨4245776, by rfl⟩ : syracuseStep 5661035 = 8491553) B8491553
theorem B2982311 : Blo 1323480 2982311 := bstep (se 1 (by rfl) ⟨2236733, by rfl⟩ : syracuseStep 2982311 = 4473467) B4473467
theorem B40772105 : Blo 1323480 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B2515529 : Blo 1323480 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B10740539 : Blo 1323480 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B5653327 : Blo 1323480 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B16982945 : Blo 1323480 16982945 := bstep (se 2 (by rfl) ⟨6368604, by rfl⟩ : syracuseStep 16982945 = 12737209) B12737209
theorem B3351527 : Blo 1323480 3351527 := bstep (se 1 (by rfl) ⟨2513645, by rfl⟩ : syracuseStep 3351527 = 5027291) B5027291
theorem B27198467 : Blo 1323480 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B5653601 : Blo 1323480 5653601 := bstep (se 2 (by rfl) ⟨2120100, by rfl⟩ : syracuseStep 5653601 = 4240201) B4240201
theorem B3581281 : Blo 1323480 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B5736071 : Blo 1323480 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B6702749 : Blo 1323480 6702749 := bstep (se 3 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 6702749 = 2513531) B2513531
theorem B3352225 : Blo 1323480 3352225 := bstep (se 2 (by rfl) ⟨1257084, by rfl⟩ : syracuseStep 3352225 = 2514169) B2514169
theorem B6801083 : Blo 1323480 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B3352367 : Blo 1323480 3352367 := bstep (se 1 (by rfl) ⟨2514275, by rfl⟩ : syracuseStep 3352367 = 5028551) B5028551
theorem B6367031 : Blo 1323480 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B7538953 : Blo 1323480 7538953 := bstep (se 2 (by rfl) ⟨2827107, by rfl⟩ : syracuseStep 7538953 = 5654215) B5654215
theorem B3582299 : Blo 1323480 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B3353015 : Blo 1323480 3353015 := bstep (se 1 (by rfl) ⟨2514761, by rfl⟩ : syracuseStep 3353015 = 5029523) B5029523
theorem B5655035 : Blo 1323480 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B28625507 : Blo 1323480 28625507 := bstep (se 1 (by rfl) ⟨21469130, by rfl⟩ : syracuseStep 28625507 = 42938261) B42938261
theorem B54340307 : Blo 1323480 54340307 := bstep (se 1 (by rfl) ⟨40755230, by rfl⟩ : syracuseStep 54340307 = 81510461) B81510461
theorem B7539479 : Blo 1323480 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1788727 : Blo 1323480 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B57273155 : Blo 1323480 57273155 := bstep (se 1 (by rfl) ⟨42954866, by rfl⟩ : syracuseStep 57273155 = 85909733) B85909733
theorem B4467581 : Blo 1323480 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B1985435 : Blo 1323480 1985435 := bstep (se 1 (by rfl) ⟨1489076, by rfl⟩ : syracuseStep 1985435 = 2978153) B2978153
theorem B6704045 : Blo 1323480 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B24153061 : Blo 1323480 24153061 := bstep (se 4 (by rfl) ⟨2264349, by rfl⟩ : syracuseStep 24153061 = 4528699) B4528699
theorem B4467851 : Blo 1323480 4467851 := bstep (se 1 (by rfl) ⟨3350888, by rfl⟩ : syracuseStep 4467851 = 6701777) B6701777
theorem B50900237 : Blo 1323480 50900237 := bstep (se 3 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 50900237 = 19087589) B19087589
theorem B1985831 : Blo 1323480 1985831 := bstep (se 1 (by rfl) ⟨1489373, by rfl⟩ : syracuseStep 1985831 = 2978747) B2978747
theorem B1985915 : Blo 1323480 1985915 := bstep (se 1 (by rfl) ⟨1489436, by rfl⟩ : syracuseStep 1985915 = 2978873) B2978873
theorem B1986041 : Blo 1323480 1986041 := bstep (se 2 (by rfl) ⟨744765, by rfl⟩ : syracuseStep 1986041 = 1489531) B1489531
theorem B3354119 : Blo 1323480 3354119 := bstep (se 1 (by rfl) ⟨2515589, by rfl⟩ : syracuseStep 3354119 = 5031179) B5031179
theorem B3354169 : Blo 1323480 3354169 := bstep (se 2 (by rfl) ⟨1257813, by rfl⟩ : syracuseStep 3354169 = 2515627) B2515627
theorem B5025361 : Blo 1323480 5025361 := bstep (se 2 (by rfl) ⟨1884510, by rfl⟩ : syracuseStep 5025361 = 3769021) B3769021
theorem B1986143 : Blo 1323480 1986143 := bstep (se 1 (by rfl) ⟨1489607, by rfl⟩ : syracuseStep 1986143 = 2979215) B2979215
theorem B6360839 : Blo 1323480 6360839 := bstep (se 1 (by rfl) ⟨4770629, by rfl⟩ : syracuseStep 6360839 = 9541259) B9541259
theorem B1986359 : Blo 1323480 1986359 := bstep (se 1 (by rfl) ⟨1489769, by rfl⟩ : syracuseStep 1986359 = 2979539) B2979539
theorem B3354473 : Blo 1323480 3354473 := bstep (se 2 (by rfl) ⟨1257927, by rfl⟩ : syracuseStep 3354473 = 2515855) B2515855
theorem B5025665 : Blo 1323480 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B16330817 : Blo 1323480 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1986665 : Blo 1323480 1986665 := bstep (se 2 (by rfl) ⟨744999, by rfl⟩ : syracuseStep 1986665 = 1489999) B1489999
theorem B5026121 : Blo 1323480 5026121 := bstep (se 2 (by rfl) ⟨1884795, by rfl⟩ : syracuseStep 5026121 = 3769591) B3769591
theorem B1986983 : Blo 1323480 1986983 := bstep (se 1 (by rfl) ⟨1490237, by rfl⟩ : syracuseStep 1986983 = 2980475) B2980475
theorem B3355091 : Blo 1323480 3355091 := bstep (se 1 (by rfl) ⟨2516318, by rfl⟩ : syracuseStep 3355091 = 5032637) B5032637
theorem B1323515 : Blo 1323480 1323515 := bstep (se 1 (by rfl) ⟨992636, by rfl⟩ : syracuseStep 1323515 = 1985273) B1985273
theorem B1987067 : Blo 1323480 1987067 := bstep (se 1 (by rfl) ⟨1490300, by rfl⟩ : syracuseStep 1987067 = 2980601) B2980601
theorem B6705665 : Blo 1323480 6705665 := bstep (se 2 (by rfl) ⟨2514624, by rfl⟩ : syracuseStep 6705665 = 5029249) B5029249
theorem B108728891 : Blo 1323480 108728891 := bstep (se 1 (by rfl) ⟨81546668, by rfl⟩ : syracuseStep 108728891 = 163093337) B163093337
theorem B1323583 : Blo 1323480 1323583 := bstep (se 1 (by rfl) ⟨992687, by rfl⟩ : syracuseStep 1323583 = 1985375) B1985375
theorem B1323591 : Blo 1323480 1323591 := bstep (se 1 (by rfl) ⟨992693, by rfl⟩ : syracuseStep 1323591 = 1985387) B1985387
theorem B7541369 : Blo 1323480 7541369 := bstep (se 2 (by rfl) ⟨2828013, by rfl⟩ : syracuseStep 7541369 = 5656027) B5656027
theorem B1987193 : Blo 1323480 1987193 := bstep (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) B1490395
theorem B1987247 : Blo 1323480 1987247 := bstep (se 1 (by rfl) ⟨1490435, by rfl⟩ : syracuseStep 1987247 = 2980871) B2980871
theorem B1323743 : Blo 1323480 1323743 := bstep (se 1 (by rfl) ⟨992807, by rfl⟩ : syracuseStep 1323743 = 1985615) B1985615
theorem B4469471 : Blo 1323480 4469471 := bstep (se 1 (by rfl) ⟨3352103, by rfl⟩ : syracuseStep 4469471 = 6704207) B6704207
theorem B1987295 : Blo 1323480 1987295 := bstep (se 1 (by rfl) ⟨1490471, by rfl⟩ : syracuseStep 1987295 = 2980943) B2980943
theorem B11309867 : Blo 1323480 11309867 := bstep (se 1 (by rfl) ⟨8482400, by rfl⟩ : syracuseStep 11309867 = 16964801) B16964801
theorem B1323823 : Blo 1323480 1323823 := bstep (se 1 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 1323823 = 1985735) B1985735
theorem B2978639 : Blo 1323480 2978639 := bstep (se 1 (by rfl) ⟨2233979, by rfl⟩ : syracuseStep 2978639 = 4467959) B4467959
theorem B7164767 : Blo 1323480 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B1323931 : Blo 1323480 1323931 := bstep (se 1 (by rfl) ⟨992948, by rfl⟩ : syracuseStep 1323931 = 1985897) B1985897
theorem B1323983 : Blo 1323480 1323983 := bstep (se 1 (by rfl) ⟨992987, by rfl⟩ : syracuseStep 1323983 = 1985975) B1985975
theorem B8491985 : Blo 1323480 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B1324007 : Blo 1323480 1324007 := bstep (se 1 (by rfl) ⟨993005, by rfl⟩ : syracuseStep 1324007 = 1986011) B1986011
theorem B6706151 : Blo 1323480 6706151 := bstep (se 1 (by rfl) ⟨5029613, by rfl⟩ : syracuseStep 6706151 = 10059227) B10059227
theorem B1987559 : Blo 1323480 1987559 := bstep (se 1 (by rfl) ⟨1490669, by rfl⟩ : syracuseStep 1987559 = 2981339) B2981339
theorem B2978855 : Blo 1323480 2978855 := bstep (se 1 (by rfl) ⟨2234141, by rfl⟩ : syracuseStep 2978855 = 4468283) B4468283
theorem B2233487 : Blo 1323480 2233487 := bstep (se 1 (by rfl) ⟨1675115, by rfl⟩ : syracuseStep 2233487 = 3350231) B3350231
theorem B4469903 : Blo 1323480 4469903 := bstep (se 1 (by rfl) ⟨3352427, by rfl⟩ : syracuseStep 4469903 = 6704855) B6704855
theorem B2979035 : Blo 1323480 2979035 := bstep (se 1 (by rfl) ⟨2234276, by rfl⟩ : syracuseStep 2979035 = 4468553) B4468553
theorem B3020009 : Blo 1323480 3020009 := bstep (se 2 (by rfl) ⟨1132503, by rfl⟩ : syracuseStep 3020009 = 2265007) B2265007
theorem B1987817 : Blo 1323480 1987817 := bstep (se 2 (by rfl) ⟨745431, by rfl⟩ : syracuseStep 1987817 = 1490863) B1490863
theorem B1324319 : Blo 1323480 1324319 := bstep (se 1 (by rfl) ⟨993239, by rfl⟩ : syracuseStep 1324319 = 1986479) B1986479
theorem B1987871 : Blo 1323480 1987871 := bstep (se 1 (by rfl) ⟨1490903, by rfl⟩ : syracuseStep 1987871 = 2981807) B2981807
theorem B6706475 : Blo 1323480 6706475 := bstep (se 1 (by rfl) ⟨5029856, by rfl⟩ : syracuseStep 6706475 = 10059713) B10059713
theorem B1324379 : Blo 1323480 1324379 := bstep (se 1 (by rfl) ⟨993284, by rfl⟩ : syracuseStep 1324379 = 1986569) B1986569
theorem B9549161 : Blo 1323480 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B1324399 : Blo 1323480 1324399 := bstep (se 1 (by rfl) ⟨993299, by rfl⟩ : syracuseStep 1324399 = 1986599) B1986599
theorem B2233723 : Blo 1323480 2233723 := bstep (se 1 (by rfl) ⟨1675292, by rfl⟩ : syracuseStep 2233723 = 3350585) B3350585
theorem B3183995 : Blo 1323480 3183995 := bstep (se 1 (by rfl) ⟨2387996, by rfl⟩ : syracuseStep 3183995 = 4775993) B4775993
theorem B2979233 : Blo 1323480 2979233 := bstep (se 2 (by rfl) ⟨1117212, by rfl⟩ : syracuseStep 2979233 = 2234425) B2234425
theorem B1324455 : Blo 1323480 1324455 := bstep (se 1 (by rfl) ⟨993341, by rfl⟩ : syracuseStep 1324455 = 1986683) B1986683
theorem B3184033 : Blo 1323480 3184033 := bstep (se 2 (by rfl) ⟨1194012, by rfl⟩ : syracuseStep 3184033 = 2388025) B2388025
theorem B1988039 : Blo 1323480 1988039 := bstep (se 1 (by rfl) ⟨1491029, by rfl⟩ : syracuseStep 1988039 = 2982059) B2982059
theorem B1324539 : Blo 1323480 1324539 := bstep (se 1 (by rfl) ⟨993404, by rfl⟩ : syracuseStep 1324539 = 1986809) B1986809
theorem B1324607 : Blo 1323480 1324607 := bstep (se 1 (by rfl) ⟨993455, by rfl⟩ : syracuseStep 1324607 = 1986911) B1986911
theorem B1324615 : Blo 1323480 1324615 := bstep (se 1 (by rfl) ⟨993461, by rfl⟩ : syracuseStep 1324615 = 1986923) B1986923
theorem B1324767 : Blo 1323480 1324767 := bstep (se 1 (by rfl) ⟨993575, by rfl⟩ : syracuseStep 1324767 = 1987151) B1987151
theorem B1324847 : Blo 1323480 1324847 := bstep (se 1 (by rfl) ⟨993635, by rfl⟩ : syracuseStep 1324847 = 1987271) B1987271
theorem B1324955 : Blo 1323480 1324955 := bstep (se 1 (by rfl) ⟨993716, by rfl⟩ : syracuseStep 1324955 = 1987433) B1987433
theorem B5027791 : Blo 1323480 5027791 := bstep (se 1 (by rfl) ⟨3770843, by rfl⟩ : syracuseStep 5027791 = 7541687) B7541687
theorem B2979791 : Blo 1323480 2979791 := bstep (se 1 (by rfl) ⟨2234843, by rfl⟩ : syracuseStep 2979791 = 4469687) B4469687
theorem B1325007 : Blo 1323480 1325007 := bstep (se 1 (by rfl) ⟨993755, by rfl⟩ : syracuseStep 1325007 = 1987511) B1987511
theorem B3184591 : Blo 1323480 3184591 := bstep (se 1 (by rfl) ⟨2388443, by rfl⟩ : syracuseStep 3184591 = 4776887) B4776887
theorem B1325031 : Blo 1323480 1325031 := bstep (se 1 (by rfl) ⟨993773, by rfl⟩ : syracuseStep 1325031 = 1987547) B1987547
theorem B1677287 : Blo 1323480 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B3184649 : Blo 1323480 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B25458731 : Blo 1323480 25458731 := bstep (se 1 (by rfl) ⟨19094048, by rfl⟩ : syracuseStep 25458731 = 38188097) B38188097
theorem B96679979 : Blo 1323480 96679979 := bstep (se 1 (by rfl) ⟨72509984, by rfl⟩ : syracuseStep 96679979 = 145019969) B145019969
theorem B27195527 : Blo 1323480 27195527 := bstep (se 1 (by rfl) ⟨20396645, by rfl⟩ : syracuseStep 27195527 = 40793291) B40793291
theorem B14522597 : Blo 1323480 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B6707447 : Blo 1323480 6707447 := bstep (se 1 (by rfl) ⟨5030585, by rfl⟩ : syracuseStep 6707447 = 10061171) B10061171
theorem B4471037 : Blo 1323480 4471037 := bstep (se 3 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 4471037 = 1676639) B1676639
theorem B1325343 : Blo 1323480 1325343 := bstep (se 1 (by rfl) ⟨994007, by rfl⟩ : syracuseStep 1325343 = 1988015) B1988015
theorem B2980169 : Blo 1323480 2980169 := bstep (se 2 (by rfl) ⟨1117563, by rfl⟩ : syracuseStep 2980169 = 2235127) B2235127
theorem B1489243 : Blo 1323480 1489243 := bstep (se 1 (by rfl) ⟨1116932, by rfl⟩ : syracuseStep 1489243 = 2233865) B2233865
theorem B2513243 : Blo 1323480 2513243 := bstep (se 1 (by rfl) ⟨1884932, by rfl⟩ : syracuseStep 2513243 = 3769865) B3769865
theorem B2980187 : Blo 1323480 2980187 := bstep (se 1 (by rfl) ⟨2235140, by rfl⟩ : syracuseStep 2980187 = 4470281) B4470281
theorem B2759003 : Blo 1323480 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B1325403 : Blo 1323480 1325403 := bstep (se 1 (by rfl) ⟨994052, by rfl⟩ : syracuseStep 1325403 = 1988105) B1988105
theorem B1325423 : Blo 1323480 1325423 := bstep (se 1 (by rfl) ⟨994067, by rfl⟩ : syracuseStep 1325423 = 1988135) B1988135
theorem B5028263 : Blo 1323480 5028263 := bstep (se 1 (by rfl) ⟨3771197, by rfl⟩ : syracuseStep 5028263 = 7542395) B7542395
theorem B1325479 : Blo 1323480 1325479 := bstep (se 1 (by rfl) ⟨994109, by rfl⟩ : syracuseStep 1325479 = 1988219) B1988219
theorem B1489351 : Blo 1323480 1489351 := bstep (se 1 (by rfl) ⟨1117013, by rfl⟩ : syracuseStep 1489351 = 2234027) B2234027
theorem B4241983 : Blo 1323480 4241983 := bstep (se 1 (by rfl) ⟨3181487, by rfl⟩ : syracuseStep 4241983 = 6362975) B6362975
theorem B6707933 : Blo 1323480 6707933 := bstep (se 3 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 6707933 = 2515475) B2515475
theorem B2513683 : Blo 1323480 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B1489711 : Blo 1323480 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B2235215 : Blo 1323480 2235215 := bstep (se 1 (by rfl) ⟨1676411, by rfl⟩ : syracuseStep 2235215 = 3352823) B3352823
theorem B21486455 : Blo 1323480 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B1489819 : Blo 1323480 1489819 := bstep (se 1 (by rfl) ⟨1117364, by rfl⟩ : syracuseStep 1489819 = 2234729) B2234729
theorem B5028763 : Blo 1323480 5028763 := bstep (se 1 (by rfl) ⟨3771572, by rfl⟩ : syracuseStep 5028763 = 7543145) B7543145
theorem B2980763 : Blo 1323480 2980763 := bstep (se 1 (by rfl) ⟨2235572, by rfl⟩ : syracuseStep 2980763 = 4471145) B4471145
theorem B2513911 : Blo 1323480 2513911 := bstep (se 1 (by rfl) ⟨1885433, by rfl⟩ : syracuseStep 2513911 = 3770867) B3770867
theorem B4471847 : Blo 1323480 4471847 := bstep (se 1 (by rfl) ⟨3353885, by rfl⟩ : syracuseStep 4471847 = 6707771) B6707771
theorem B2980961 : Blo 1323480 2980961 := bstep (se 2 (by rfl) ⟨1117860, by rfl⟩ : syracuseStep 2980961 = 2235721) B2235721
theorem B7650493 : Blo 1323480 7650493 := bstep (se 3 (by rfl) ⟨1434467, by rfl⟩ : syracuseStep 7650493 = 2868935) B2868935
theorem B12721369 : Blo 1323480 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B6700319 : Blo 1323480 6700319 := bstep (se 1 (by rfl) ⟨5025239, by rfl⟩ : syracuseStep 6700319 = 10050479) B10050479
theorem B2514215 : Blo 1323480 2514215 := bstep (se 1 (by rfl) ⟨1885661, by rfl⟩ : syracuseStep 2514215 = 3771323) B3771323
theorem B1490215 : Blo 1323480 1490215 := bstep (se 1 (by rfl) ⟨1117661, by rfl⟩ : syracuseStep 1490215 = 2235323) B2235323
theorem B2981159 : Blo 1323480 2981159 := bstep (se 1 (by rfl) ⟨2235869, by rfl⟩ : syracuseStep 2981159 = 4471739) B4471739
theorem B21765469 : Blo 1323480 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B1490287 : Blo 1323480 1490287 := bstep (se 1 (by rfl) ⟨1117715, by rfl⟩ : syracuseStep 1490287 = 2235431) B2235431
theorem B4472279 : Blo 1323480 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B12738059 : Blo 1323480 12738059 := bstep (se 1 (by rfl) ⟨9553544, by rfl⟩ : syracuseStep 12738059 = 19107089) B19107089
theorem B1490503 : Blo 1323480 1490503 := bstep (se 1 (by rfl) ⟨1117877, by rfl⟩ : syracuseStep 1490503 = 2235755) B2235755
theorem B9059921 : Blo 1323480 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B3350099 : Blo 1323480 3350099 := bstep (se 1 (by rfl) ⟨2512574, by rfl⟩ : syracuseStep 3350099 = 5025149) B5025149
theorem B2981537 : Blo 1323480 2981537 := bstep (se 2 (by rfl) ⟨1118076, by rfl⟩ : syracuseStep 2981537 = 2236153) B2236153
theorem B2236207 : Blo 1323480 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B42983297 : Blo 1323480 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B10887211 : Blo 1323480 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B3350747 : Blo 1323480 3350747 := bstep (se 1 (by rfl) ⟨2513060, by rfl⟩ : syracuseStep 3350747 = 5026121) B5026121
theorem B2236727 : Blo 1323480 2236727 := bstep (se 1 (by rfl) ⟨1677545, by rfl⟩ : syracuseStep 2236727 = 3355091) B3355091
theorem B27181403 : Blo 1323480 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B10051937 : Blo 1323480 10051937 := bstep (se 2 (by rfl) ⟨3769476, by rfl⟩ : syracuseStep 10051937 = 7538953) B7538953
theorem B7160359 : Blo 1323480 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B4776511 : Blo 1323480 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B11321963 : Blo 1323480 11321963 := bstep (se 1 (by rfl) ⟨8491472, by rfl⟩ : syracuseStep 11321963 = 16982945) B16982945
theorem B8053357 : Blo 1323480 8053357 := bstep (se 3 (by rfl) ⟨1510004, by rfl⟩ : syracuseStep 8053357 = 3020009) B3020009
theorem B5661323 : Blo 1323480 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B3769067 : Blo 1323480 3769067 := bstep (se 1 (by rfl) ⟨2826800, by rfl⟩ : syracuseStep 3769067 = 5653601) B5653601
theorem B6366107 : Blo 1323480 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B3351577 : Blo 1323480 3351577 := bstep (se 2 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 3351577 = 2513683) B2513683
theorem B2384969 : Blo 1323480 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B7537769 : Blo 1323480 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B4244687 : Blo 1323480 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B32204081 : Blo 1323480 32204081 := bstep (se 2 (by rfl) ⟨12076530, by rfl⟩ : syracuseStep 32204081 = 24153061) B24153061
theorem B3351881 : Blo 1323480 3351881 := bstep (se 2 (by rfl) ⟨1256955, by rfl⟩ : syracuseStep 3351881 = 2513911) B2513911
theorem B2123099 : Blo 1323480 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B18130351 : Blo 1323480 18130351 := bstep (se 1 (by rfl) ⟨13597763, by rfl⟩ : syracuseStep 18130351 = 27195527) B27195527
theorem B3352175 : Blo 1323480 3352175 := bstep (se 1 (by rfl) ⟨2514131, by rfl⟩ : syracuseStep 3352175 = 5028263) B5028263
theorem B36226871 : Blo 1323480 36226871 := bstep (se 1 (by rfl) ⟨27170153, by rfl⟩ : syracuseStep 36226871 = 54340307) B54340307
theorem B4245377 : Blo 1323480 4245377 := bstep (se 2 (by rfl) ⟨1592016, by rfl⟩ : syracuseStep 4245377 = 3184033) B3184033
theorem B33933491 : Blo 1323480 33933491 := bstep (se 1 (by rfl) ⟨25450118, by rfl⟩ : syracuseStep 33933491 = 50900237) B50900237
theorem B4466879 : Blo 1323480 4466879 := bstep (se 1 (by rfl) ⟨3350159, by rfl⟩ : syracuseStep 4466879 = 6700319) B6700319
theorem B6039947 : Blo 1323480 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B6703721 : Blo 1323480 6703721 := bstep (se 2 (by rfl) ⟨2513895, by rfl⟩ : syracuseStep 6703721 = 5027791) B5027791
theorem B4246121 : Blo 1323480 4246121 := bstep (se 2 (by rfl) ⟨1592295, by rfl⟩ : syracuseStep 4246121 = 3184591) B3184591
theorem B4025015 : Blo 1323480 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B72485927 : Blo 1323480 72485927 := bstep (se 1 (by rfl) ⟨54364445, by rfl⟩ : syracuseStep 72485927 = 108728891) B108728891
theorem B1985657 : Blo 1323480 1985657 := bstep (se 2 (by rfl) ⟨744621, by rfl⟩ : syracuseStep 1985657 = 1489243) B1489243
theorem B12725369 : Blo 1323480 12725369 := bstep (se 2 (by rfl) ⟨4772013, by rfl⟩ : syracuseStep 12725369 = 9544027) B9544027
theorem B7539911 : Blo 1323480 7539911 := bstep (se 1 (by rfl) ⟨5654933, by rfl⟩ : syracuseStep 7539911 = 11309867) B11309867
theorem B1985759 : Blo 1323480 1985759 := bstep (se 1 (by rfl) ⟨1489319, by rfl⟩ : syracuseStep 1985759 = 2978639) B2978639
theorem B1985801 : Blo 1323480 1985801 := bstep (se 2 (by rfl) ⟨744675, by rfl⟩ : syracuseStep 1985801 = 1489351) B1489351
theorem B18132311 : Blo 1323480 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B1985903 : Blo 1323480 1985903 := bstep (se 1 (by rfl) ⟨1489427, by rfl⟩ : syracuseStep 1985903 = 2978855) B2978855
theorem B5655977 : Blo 1323480 5655977 := bstep (se 2 (by rfl) ⟨2120991, by rfl⟩ : syracuseStep 5655977 = 4241983) B4241983
theorem B1986023 : Blo 1323480 1986023 := bstep (se 1 (by rfl) ⟨1489517, by rfl⟩ : syracuseStep 1986023 = 2979035) B2979035
theorem B1986155 : Blo 1323480 1986155 := bstep (se 1 (by rfl) ⟨1489616, by rfl⟩ : syracuseStep 1986155 = 2979233) B2979233
theorem B29429365 : Blo 1323480 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B8490653 : Blo 1323480 8490653 := bstep (se 3 (by rfl) ⟨1591997, by rfl⟩ : syracuseStep 8490653 = 3183995) B3183995
theorem B1986281 : Blo 1323480 1986281 := bstep (se 2 (by rfl) ⟨744855, by rfl⟩ : syracuseStep 1986281 = 1489711) B1489711
theorem B4468499 : Blo 1323480 4468499 := bstep (se 1 (by rfl) ⟨3351374, by rfl⟩ : syracuseStep 4468499 = 6702749) B6702749
theorem B4534055 : Blo 1323480 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B1986425 : Blo 1323480 1986425 := bstep (se 2 (by rfl) ⟨744909, by rfl⟩ : syracuseStep 1986425 = 1489819) B1489819
theorem B6705017 : Blo 1323480 6705017 := bstep (se 2 (by rfl) ⟨2514381, by rfl⟩ : syracuseStep 6705017 = 5028763) B5028763
theorem B1986527 : Blo 1323480 1986527 := bstep (se 1 (by rfl) ⟨1489895, by rfl⟩ : syracuseStep 1986527 = 2979791) B2979791
theorem B1986779 : Blo 1323480 1986779 := bstep (se 1 (by rfl) ⟨1490084, by rfl⟩ : syracuseStep 1986779 = 2980169) B2980169
theorem B1675495 : Blo 1323480 1675495 := bstep (se 1 (by rfl) ⟨1256621, by rfl⟩ : syracuseStep 1675495 = 2513243) B2513243
theorem B1986791 : Blo 1323480 1986791 := bstep (se 1 (by rfl) ⟨1490093, by rfl⟩ : syracuseStep 1986791 = 2980187) B2980187
theorem B2388199 : Blo 1323480 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B16961825 : Blo 1323480 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B1986953 : Blo 1323480 1986953 := bstep (se 2 (by rfl) ⟨745107, by rfl⟩ : syracuseStep 1986953 = 1490215) B1490215
theorem B19083671 : Blo 1323480 19083671 := bstep (se 1 (by rfl) ⟨14312753, by rfl⟩ : syracuseStep 19083671 = 28625507) B28625507
theorem B29020625 : Blo 1323480 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B1987049 : Blo 1323480 1987049 := bstep (se 2 (by rfl) ⟨745143, by rfl⟩ : syracuseStep 1987049 = 1490287) B1490287
theorem B2978297 : Blo 1323480 2978297 := bstep (se 2 (by rfl) ⟨1116861, by rfl⟩ : syracuseStep 2978297 = 2233723) B2233723
theorem B5026319 : Blo 1323480 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B14324303 : Blo 1323480 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B2978387 : Blo 1323480 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B1323623 : Blo 1323480 1323623 := bstep (se 1 (by rfl) ⟨992717, by rfl⟩ : syracuseStep 1323623 = 1985435) B1985435
theorem B1987175 : Blo 1323480 1987175 := bstep (se 1 (by rfl) ⟨1490381, by rfl⟩ : syracuseStep 1987175 = 2980763) B2980763
theorem B4469363 : Blo 1323480 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B1987307 : Blo 1323480 1987307 := bstep (se 1 (by rfl) ⟨1490480, by rfl⟩ : syracuseStep 1987307 = 2980961) B2980961
theorem B2978567 : Blo 1323480 2978567 := bstep (se 1 (by rfl) ⟨2233925, by rfl⟩ : syracuseStep 2978567 = 4467851) B4467851
theorem B1987337 : Blo 1323480 1987337 := bstep (se 2 (by rfl) ⟨745251, by rfl⟩ : syracuseStep 1987337 = 1490503) B1490503
theorem B1323887 : Blo 1323480 1323887 := bstep (se 1 (by rfl) ⟨992915, by rfl⟩ : syracuseStep 1323887 = 1985831) B1985831
theorem B1676143 : Blo 1323480 1676143 := bstep (se 1 (by rfl) ⟨1257107, by rfl⟩ : syracuseStep 1676143 = 2514215) B2514215
theorem B1987439 : Blo 1323480 1987439 := bstep (se 1 (by rfl) ⟨1490579, by rfl⟩ : syracuseStep 1987439 = 2981159) B2981159
theorem B4469633 : Blo 1323480 4469633 := bstep (se 2 (by rfl) ⟨1676112, by rfl⟩ : syracuseStep 4469633 = 3352225) B3352225
theorem B1323943 : Blo 1323480 1323943 := bstep (se 1 (by rfl) ⟨992957, by rfl⟩ : syracuseStep 1323943 = 1985915) B1985915
theorem B1324027 : Blo 1323480 1324027 := bstep (se 1 (by rfl) ⟨993020, by rfl⟩ : syracuseStep 1324027 = 1986041) B1986041
theorem B8492039 : Blo 1323480 8492039 := bstep (se 1 (by rfl) ⟨6369029, by rfl⟩ : syracuseStep 8492039 = 12738059) B12738059
theorem B2233399 : Blo 1323480 2233399 := bstep (se 1 (by rfl) ⟨1675049, by rfl⟩ : syracuseStep 2233399 = 3350099) B3350099
theorem B1324095 : Blo 1323480 1324095 := bstep (se 1 (by rfl) ⟨993071, by rfl⟩ : syracuseStep 1324095 = 1986143) B1986143
theorem B1987691 : Blo 1323480 1987691 := bstep (se 1 (by rfl) ⟨1490768, by rfl⟩ : syracuseStep 1987691 = 2981537) B2981537
theorem B4240559 : Blo 1323480 4240559 := bstep (se 1 (by rfl) ⟨3180419, by rfl⟩ : syracuseStep 4240559 = 6360839) B6360839
theorem B1324239 : Blo 1323480 1324239 := bstep (se 1 (by rfl) ⟨993179, by rfl⟩ : syracuseStep 1324239 = 1986359) B1986359
theorem B1987931 : Blo 1323480 1987931 := bstep (se 1 (by rfl) ⟨1490948, by rfl⟩ : syracuseStep 1987931 = 2981897) B2981897
theorem B5657975 : Blo 1323480 5657975 := bstep (se 1 (by rfl) ⟨4243481, by rfl⟩ : syracuseStep 5657975 = 8486963) B8486963
theorem B1324443 : Blo 1323480 1324443 := bstep (se 1 (by rfl) ⟨993332, by rfl⟩ : syracuseStep 1324443 = 1986665) B1986665
theorem B3774023 : Blo 1323480 3774023 := bstep (se 1 (by rfl) ⟨2830517, by rfl⟩ : syracuseStep 3774023 = 5661035) B5661035
theorem B1324655 : Blo 1323480 1324655 := bstep (se 1 (by rfl) ⟨993491, by rfl⟩ : syracuseStep 1324655 = 1986983) B1986983
theorem B1988207 : Blo 1323480 1988207 := bstep (se 1 (by rfl) ⟨1491155, by rfl⟩ : syracuseStep 1988207 = 2982311) B2982311
theorem B1324711 : Blo 1323480 1324711 := bstep (se 1 (by rfl) ⟨993533, by rfl⟩ : syracuseStep 1324711 = 1987067) B1987067
theorem B4470443 : Blo 1323480 4470443 := bstep (se 1 (by rfl) ⟨3352832, by rfl⟩ : syracuseStep 4470443 = 6705665) B6705665
theorem B1677019 : Blo 1323480 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B5027579 : Blo 1323480 5027579 := bstep (se 1 (by rfl) ⟨3770684, by rfl⟩ : syracuseStep 5027579 = 7541369) B7541369
theorem B1324795 : Blo 1323480 1324795 := bstep (se 1 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 1324795 = 1987193) B1987193
theorem B1324831 : Blo 1323480 1324831 := bstep (se 1 (by rfl) ⟨993623, by rfl⟩ : syracuseStep 1324831 = 1987247) B1987247
theorem B2979647 : Blo 1323480 2979647 := bstep (se 1 (by rfl) ⟨2234735, by rfl⟩ : syracuseStep 2979647 = 4469471) B4469471
theorem B1324863 : Blo 1323480 1324863 := bstep (se 1 (by rfl) ⟨993647, by rfl⟩ : syracuseStep 1324863 = 1987295) B1987295
theorem B2234351 : Blo 1323480 2234351 := bstep (se 1 (by rfl) ⟨1675763, by rfl⟩ : syracuseStep 2234351 = 3351527) B3351527
theorem B4470767 : Blo 1323480 4470767 := bstep (se 1 (by rfl) ⟨3353075, by rfl⟩ : syracuseStep 4470767 = 6706151) B6706151
theorem B1325039 : Blo 1323480 1325039 := bstep (se 1 (by rfl) ⟨993779, by rfl⟩ : syracuseStep 1325039 = 1987559) B1987559
theorem B1488991 : Blo 1323480 1488991 := bstep (se 1 (by rfl) ⟨1116743, by rfl⟩ : syracuseStep 1488991 = 2233487) B2233487
theorem B2979935 : Blo 1323480 2979935 := bstep (se 1 (by rfl) ⟨2234951, by rfl⟩ : syracuseStep 2979935 = 4469903) B4469903
theorem B1325211 : Blo 1323480 1325211 := bstep (se 1 (by rfl) ⟨993908, by rfl⟩ : syracuseStep 1325211 = 1987817) B1987817
theorem B1325247 : Blo 1323480 1325247 := bstep (se 1 (by rfl) ⟨993935, by rfl⟩ : syracuseStep 1325247 = 1987871) B1987871
theorem B4470983 : Blo 1323480 4470983 := bstep (se 1 (by rfl) ⟨3353237, by rfl⟩ : syracuseStep 4470983 = 6706475) B6706475
theorem B1325359 : Blo 1323480 1325359 := bstep (se 1 (by rfl) ⟨994019, by rfl⟩ : syracuseStep 1325359 = 1988039) B1988039
theorem B40802629 : Blo 1323480 40802629 := bstep (se 4 (by rfl) ⟨3825246, by rfl⟩ : syracuseStep 40802629 = 7650493) B7650493
theorem B3824047 : Blo 1323480 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B2234911 : Blo 1323480 2234911 := bstep (se 1 (by rfl) ⟨1676183, by rfl⟩ : syracuseStep 2234911 = 3352367) B3352367
theorem B15080093 : Blo 1323480 15080093 := bstep (se 3 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 15080093 = 5655035) B5655035
theorem B16972487 : Blo 1323480 16972487 := bstep (se 1 (by rfl) ⟨12729365, by rfl⟩ : syracuseStep 16972487 = 25458731) B25458731
theorem B64453319 : Blo 1323480 64453319 := bstep (se 1 (by rfl) ⟨48339989, by rfl⟩ : syracuseStep 64453319 = 96679979) B96679979
theorem B9681731 : Blo 1323480 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B4471631 : Blo 1323480 4471631 := bstep (se 1 (by rfl) ⟨3353723, by rfl⟩ : syracuseStep 4471631 = 6707447) B6707447
theorem B2980691 : Blo 1323480 2980691 := bstep (se 1 (by rfl) ⟨2235518, by rfl⟩ : syracuseStep 2980691 = 4471037) B4471037
theorem B2235343 : Blo 1323480 2235343 := bstep (se 1 (by rfl) ⟨1676507, by rfl⟩ : syracuseStep 2235343 = 3353015) B3353015
theorem B4775041 : Blo 1323480 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B4471955 : Blo 1323480 4471955 := bstep (se 1 (by rfl) ⟨3353966, by rfl⟩ : syracuseStep 4471955 = 6707933) B6707933
theorem B38182103 : Blo 1323480 38182103 := bstep (se 1 (by rfl) ⟨28636577, by rfl⟩ : syracuseStep 38182103 = 57273155) B57273155
theorem B1490143 : Blo 1323480 1490143 := bstep (se 1 (by rfl) ⟨1117607, by rfl⟩ : syracuseStep 1490143 = 2235215) B2235215
theorem B2981231 : Blo 1323480 2981231 := bstep (se 1 (by rfl) ⟨2235923, by rfl⟩ : syracuseStep 2981231 = 4471847) B4471847
theorem B4472225 : Blo 1323480 4472225 := bstep (se 2 (by rfl) ⟨1677084, by rfl⟩ : syracuseStep 4472225 = 3354169) B3354169
theorem B6700481 : Blo 1323480 6700481 := bstep (se 2 (by rfl) ⟨2512680, by rfl⟩ : syracuseStep 6700481 = 5025361) B5025361
theorem B2981519 : Blo 1323480 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B2236079 : Blo 1323480 2236079 := bstep (se 1 (by rfl) ⟨1677059, by rfl⟩ : syracuseStep 2236079 = 3354119) B3354119
theorem B2981609 : Blo 1323480 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B2236315 : Blo 1323480 2236315 := bstep (se 1 (by rfl) ⟨1677236, by rfl⟩ : syracuseStep 2236315 = 3354473) B3354473
theorem B3350443 : Blo 1323480 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B28655531 : Blo 1323480 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B4472765 : Blo 1323480 4472765 := bstep (se 3 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 4472765 = 1677287) B1677287
theorem B14516281 : Blo 1323480 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B1491151 : Blo 1323480 1491151 := bstep (se 1 (by rfl) ⟨1118363, by rfl⟩ : syracuseStep 1491151 = 2236727) B2236727
theorem B18120935 : Blo 1323480 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B6701291 : Blo 1323480 6701291 := bstep (se 1 (by rfl) ⟨5025968, by rfl⟩ : syracuseStep 6701291 = 10051937) B10051937
theorem B12722447 : Blo 1323480 12722447 := bstep (se 1 (by rfl) ⟨9541835, by rfl⟩ : syracuseStep 12722447 = 19083671) B19083671
theorem B3350879 : Blo 1323480 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B54403505 : Blo 1323480 54403505 := bstep (se 2 (by rfl) ⟨20401314, by rfl⟩ : syracuseStep 54403505 = 40802629) B40802629
theorem B4244071 : Blo 1323480 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B5661359 : Blo 1323480 5661359 := bstep (se 1 (by rfl) ⟨4246019, by rfl⟩ : syracuseStep 5661359 = 8492039) B8492039
theorem B16106525 : Blo 1323480 16106525 := bstep (se 3 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 16106525 = 6039947) B6039947
theorem B2516015 : Blo 1323480 2516015 := bstep (se 1 (by rfl) ⟨1887011, by rfl⟩ : syracuseStep 2516015 = 3774023) B3774023
theorem B3351719 : Blo 1323480 3351719 := bstep (se 1 (by rfl) ⟨2513789, by rfl⟩ : syracuseStep 3351719 = 5027579) B5027579
theorem B24151247 : Blo 1323480 24151247 := bstep (se 1 (by rfl) ⟨18113435, by rfl⟩ : syracuseStep 24151247 = 36226871) B36226871
theorem B11322989 : Blo 1323480 11322989 := bstep (se 3 (by rfl) ⟨2123060, by rfl⟩ : syracuseStep 11322989 = 4246121) B4246121
theorem B10053395 : Blo 1323480 10053395 := bstep (se 1 (by rfl) ⟨7540046, by rfl⟩ : syracuseStep 10053395 = 15080093) B15080093
theorem B11314991 : Blo 1323480 11314991 := bstep (se 1 (by rfl) ⟨8486243, by rfl⟩ : syracuseStep 11314991 = 16972487) B16972487
theorem B42968879 : Blo 1323480 42968879 := bstep (se 1 (by rfl) ⟨32226659, by rfl⟩ : syracuseStep 42968879 = 64453319) B64453319
theorem B25454735 : Blo 1323480 25454735 := bstep (se 1 (by rfl) ⟨19091051, by rfl⟩ : syracuseStep 25454735 = 38182103) B38182103
theorem B3770651 : Blo 1323480 3770651 := bstep (se 1 (by rfl) ⟨2827988, by rfl⟩ : syracuseStep 3770651 = 5655977) B5655977
theorem B4466987 : Blo 1323480 4466987 := bstep (se 1 (by rfl) ⟨3350240, by rfl⟩ : syracuseStep 4466987 = 6700481) B6700481
theorem B4467257 : Blo 1323480 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B1985321 : Blo 1323480 1985321 := bstep (se 2 (by rfl) ⟨744495, by rfl⟩ : syracuseStep 1985321 = 1488991) B1488991
theorem B11307883 : Blo 1323480 11307883 := bstep (se 1 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 11307883 = 16961825) B16961825
theorem B6359917 : Blo 1323480 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B1985531 : Blo 1323480 1985531 := bstep (se 1 (by rfl) ⟨1489148, by rfl⟩ : syracuseStep 1985531 = 2978297) B2978297
theorem B1985591 : Blo 1323480 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B7547975 : Blo 1323480 7547975 := bstep (se 1 (by rfl) ⟨5660981, by rfl⟩ : syracuseStep 7547975 = 11321963) B11321963
theorem B11308157 : Blo 1323480 11308157 := bstep (se 3 (by rfl) ⟨2120279, by rfl⟩ : syracuseStep 11308157 = 4240559) B4240559
theorem B1985711 : Blo 1323480 1985711 := bstep (se 1 (by rfl) ⟨1489283, by rfl⟩ : syracuseStep 1985711 = 2978567) B2978567
theorem B5098729 : Blo 1323480 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B9547145 : Blo 1323480 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B5025179 : Blo 1323480 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B6368681 : Blo 1323480 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B2829791 : Blo 1323480 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B3771983 : Blo 1323480 3771983 := bstep (se 1 (by rfl) ⟨2828987, by rfl⟩ : syracuseStep 3771983 = 5657975) B5657975
theorem B1986431 : Blo 1323480 1986431 := bstep (se 1 (by rfl) ⟨1489823, by rfl⟩ : syracuseStep 1986431 = 2979647) B2979647
theorem B4468769 : Blo 1323480 4468769 := bstep (se 2 (by rfl) ⟨1675788, by rfl⟩ : syracuseStep 4468769 = 3351577) B3351577
theorem B1986623 : Blo 1323480 1986623 := bstep (se 1 (by rfl) ⟨1489967, by rfl⟩ : syracuseStep 1986623 = 2979935) B2979935
theorem B2977865 : Blo 1323480 2977865 := bstep (se 2 (by rfl) ⟨1116699, by rfl⟩ : syracuseStep 2977865 = 2233399) B2233399
theorem B22622327 : Blo 1323480 22622327 := bstep (se 1 (by rfl) ⟨16966745, by rfl⟩ : syracuseStep 22622327 = 33933491) B33933491
theorem B2977919 : Blo 1323480 2977919 := bstep (se 1 (by rfl) ⟨2233439, by rfl⟩ : syracuseStep 2977919 = 4466879) B4466879
theorem B1986857 : Blo 1323480 1986857 := bstep (se 2 (by rfl) ⟨745071, by rfl⟩ : syracuseStep 1986857 = 1490143) B1490143
theorem B4469147 : Blo 1323480 4469147 := bstep (se 1 (by rfl) ⟨3351860, by rfl⟩ : syracuseStep 4469147 = 6703721) B6703721
theorem B2683343 : Blo 1323480 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B1987127 : Blo 1323480 1987127 := bstep (se 1 (by rfl) ⟨1490345, by rfl⟩ : syracuseStep 1987127 = 2980691) B2980691
theorem B1323771 : Blo 1323480 1323771 := bstep (se 1 (by rfl) ⟨992828, by rfl⟩ : syracuseStep 1323771 = 1985657) B1985657
theorem B8483579 : Blo 1323480 8483579 := bstep (se 1 (by rfl) ⟨6362684, by rfl⟩ : syracuseStep 8483579 = 12725369) B12725369
theorem B5026607 : Blo 1323480 5026607 := bstep (se 1 (by rfl) ⟨3769955, by rfl⟩ : syracuseStep 5026607 = 7539911) B7539911
theorem B1323839 : Blo 1323480 1323839 := bstep (se 1 (by rfl) ⟨992879, by rfl⟩ : syracuseStep 1323839 = 1985759) B1985759
theorem B1323867 : Blo 1323480 1323867 := bstep (se 1 (by rfl) ⟨992900, by rfl⟩ : syracuseStep 1323867 = 1985801) B1985801
theorem B12088207 : Blo 1323480 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B1323935 : Blo 1323480 1323935 := bstep (se 1 (by rfl) ⟨992951, by rfl⟩ : syracuseStep 1323935 = 1985903) B1985903
theorem B1987487 : Blo 1323480 1987487 := bstep (se 1 (by rfl) ⟨1490615, by rfl⟩ : syracuseStep 1987487 = 2981231) B2981231
theorem B1324015 : Blo 1323480 1324015 := bstep (se 1 (by rfl) ⟨993011, by rfl⟩ : syracuseStep 1324015 = 1986023) B1986023
theorem B1324103 : Blo 1323480 1324103 := bstep (se 1 (by rfl) ⟨993077, by rfl⟩ : syracuseStep 1324103 = 1986155) B1986155
theorem B1987679 : Blo 1323480 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B1324187 : Blo 1323480 1324187 := bstep (se 1 (by rfl) ⟨993140, by rfl⟩ : syracuseStep 1324187 = 1986281) B1986281
theorem B1987739 : Blo 1323480 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B2978999 : Blo 1323480 2978999 := bstep (se 1 (by rfl) ⟨2234249, by rfl⟩ : syracuseStep 2978999 = 4468499) B4468499
theorem B1324283 : Blo 1323480 1324283 := bstep (se 1 (by rfl) ⟨993212, by rfl⟩ : syracuseStep 1324283 = 1986425) B1986425
theorem B4470011 : Blo 1323480 4470011 := bstep (se 1 (by rfl) ⟨3352508, by rfl⟩ : syracuseStep 4470011 = 6705017) B6705017
theorem B1324351 : Blo 1323480 1324351 := bstep (se 1 (by rfl) ⟨993263, by rfl⟩ : syracuseStep 1324351 = 1986527) B1986527
theorem B2233831 : Blo 1323480 2233831 := bstep (se 1 (by rfl) ⟨1675373, by rfl⟩ : syracuseStep 2233831 = 3350747) B3350747
theorem B1324519 : Blo 1323480 1324519 := bstep (se 1 (by rfl) ⟨993389, by rfl⟩ : syracuseStep 1324519 = 1986779) B1986779
theorem B1324527 : Blo 1323480 1324527 := bstep (se 1 (by rfl) ⟨993395, by rfl⟩ : syracuseStep 1324527 = 1986791) B1986791
theorem B1324635 : Blo 1323480 1324635 := bstep (se 1 (by rfl) ⟨993476, by rfl⟩ : syracuseStep 1324635 = 1986953) B1986953
theorem B2233993 : Blo 1323480 2233993 := bstep (se 2 (by rfl) ⟨837747, by rfl⟩ : syracuseStep 2233993 = 1675495) B1675495
theorem B19347083 : Blo 1323480 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B3184265 : Blo 1323480 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B1324699 : Blo 1323480 1324699 := bstep (se 1 (by rfl) ⟨993524, by rfl⟩ : syracuseStep 1324699 = 1987049) B1987049
theorem B1324783 : Blo 1323480 1324783 := bstep (se 1 (by rfl) ⟨993587, by rfl⟩ : syracuseStep 1324783 = 1987175) B1987175
theorem B2979575 : Blo 1323480 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B3774215 : Blo 1323480 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B2512711 : Blo 1323480 2512711 := bstep (se 1 (by rfl) ⟨1884533, by rfl⟩ : syracuseStep 2512711 = 3769067) B3769067
theorem B1324871 : Blo 1323480 1324871 := bstep (se 1 (by rfl) ⟨993653, by rfl⟩ : syracuseStep 1324871 = 1987307) B1987307
theorem B1324891 : Blo 1323480 1324891 := bstep (se 1 (by rfl) ⟨993668, by rfl⟩ : syracuseStep 1324891 = 1987337) B1987337
theorem B1324959 : Blo 1323480 1324959 := bstep (se 1 (by rfl) ⟨993719, by rfl⟩ : syracuseStep 1324959 = 1987439) B1987439
theorem B2979755 : Blo 1323480 2979755 := bstep (se 1 (by rfl) ⟨2234816, by rfl⟩ : syracuseStep 2979755 = 4469633) B4469633
theorem B25466885 : Blo 1323480 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B2979881 : Blo 1323480 2979881 := bstep (se 2 (by rfl) ⟨1117455, by rfl⟩ : syracuseStep 2979881 = 2234911) B2234911
theorem B1325127 : Blo 1323480 1325127 := bstep (se 1 (by rfl) ⟨993845, by rfl⟩ : syracuseStep 1325127 = 1987691) B1987691
theorem B10737809 : Blo 1323480 10737809 := bstep (se 2 (by rfl) ⟨4026678, by rfl⟩ : syracuseStep 10737809 = 8053357) B8053357
theorem B21469387 : Blo 1323480 21469387 := bstep (se 1 (by rfl) ⟨16102040, by rfl⟩ : syracuseStep 21469387 = 32204081) B32204081
theorem B2234587 : Blo 1323480 2234587 := bstep (se 1 (by rfl) ⟨1675940, by rfl⟩ : syracuseStep 2234587 = 3351881) B3351881
theorem B1325287 : Blo 1323480 1325287 := bstep (se 1 (by rfl) ⟨993965, by rfl⟩ : syracuseStep 1325287 = 1987931) B1987931
theorem B1415399 : Blo 1323480 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B2234783 : Blo 1323480 2234783 := bstep (se 1 (by rfl) ⟨1676087, by rfl⟩ : syracuseStep 2234783 = 3352175) B3352175
theorem B1325471 : Blo 1323480 1325471 := bstep (se 1 (by rfl) ⟨994103, by rfl⟩ : syracuseStep 1325471 = 1988207) B1988207
theorem B2980295 : Blo 1323480 2980295 := bstep (se 1 (by rfl) ⟨2235221, by rfl⟩ : syracuseStep 2980295 = 4470443) B4470443
theorem B2234857 : Blo 1323480 2234857 := bstep (se 2 (by rfl) ⟨838071, by rfl⟩ : syracuseStep 2234857 = 1676143) B1676143
theorem B2980457 : Blo 1323480 2980457 := bstep (se 2 (by rfl) ⟨1117671, by rfl⟩ : syracuseStep 2980457 = 2235343) B2235343
theorem B1489567 : Blo 1323480 1489567 := bstep (se 1 (by rfl) ⟨1117175, by rfl⟩ : syracuseStep 1489567 = 2234351) B2234351
theorem B2980511 : Blo 1323480 2980511 := bstep (se 1 (by rfl) ⟨2235383, by rfl⟩ : syracuseStep 2980511 = 4470767) B4470767
theorem B2980655 : Blo 1323480 2980655 := bstep (se 1 (by rfl) ⟨2235491, by rfl⟩ : syracuseStep 2980655 = 4470983) B4470983
theorem B38198141 : Blo 1323480 38198141 := bstep (se 3 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 38198141 = 14324303) B14324303
theorem B6454487 : Blo 1323480 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B2981087 : Blo 1323480 2981087 := bstep (se 1 (by rfl) ⟨2235815, by rfl⟩ : syracuseStep 2981087 = 4471631) B4471631
theorem B24173801 : Blo 1323480 24173801 := bstep (se 2 (by rfl) ⟨9065175, by rfl⟩ : syracuseStep 24173801 = 18130351) B18130351
theorem B48323951 : Blo 1323480 48323951 := bstep (se 1 (by rfl) ⟨36242963, by rfl⟩ : syracuseStep 48323951 = 72485927) B72485927
theorem B2981303 : Blo 1323480 2981303 := bstep (se 1 (by rfl) ⟨2235977, by rfl⟩ : syracuseStep 2981303 = 4471955) B4471955
theorem B39239153 : Blo 1323480 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B2981483 : Blo 1323480 2981483 := bstep (se 1 (by rfl) ⟨2236112, by rfl⟩ : syracuseStep 2981483 = 4472225) B4472225
theorem B2236025 : Blo 1323480 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B11321005 : Blo 1323480 11321005 := bstep (se 3 (by rfl) ⟨2122688, by rfl⟩ : syracuseStep 11321005 = 4245377) B4245377
theorem B5660435 : Blo 1323480 5660435 := bstep (se 1 (by rfl) ⟨4245326, by rfl⟩ : syracuseStep 5660435 = 8490653) B8490653
theorem B1490719 : Blo 1323480 1490719 := bstep (se 1 (by rfl) ⟨1118039, by rfl⟩ : syracuseStep 1490719 = 2236079) B2236079
theorem B3022703 : Blo 1323480 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B2981753 : Blo 1323480 2981753 := bstep (se 2 (by rfl) ⟨1118157, by rfl⟩ : syracuseStep 2981753 = 2236315) B2236315
theorem B19103687 : Blo 1323480 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B2981843 : Blo 1323480 2981843 := bstep (se 1 (by rfl) ⟨2236382, by rfl⟩ : syracuseStep 2981843 = 4472765) B4472765
theorem B15081551 : Blo 1323480 15081551 := bstep (se 1 (by rfl) ⟨11311163, by rfl⟩ : syracuseStep 15081551 = 22622327) B22622327
theorem B3351071 : Blo 1323480 3351071 := bstep (se 1 (by rfl) ⟨2513303, by rfl⟩ : syracuseStep 3351071 = 5026607) B5026607
theorem B2122843 : Blo 1323480 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B8479889 : Blo 1323480 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B6702263 : Blo 1323480 6702263 := bstep (se 1 (by rfl) ⟨5026697, by rfl⟩ : syracuseStep 6702263 = 10053395) B10053395
theorem B5031983 : Blo 1323480 5031983 := bstep (se 1 (by rfl) ⟨3773987, by rfl⟩ : syracuseStep 5031983 = 7547975) B7547975
theorem B7538771 : Blo 1323480 7538771 := bstep (se 1 (by rfl) ⟨5654078, by rfl⟩ : syracuseStep 7538771 = 11308157) B11308157
theorem B4302991 : Blo 1323480 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B16115867 : Blo 1323480 16115867 := bstep (se 1 (by rfl) ⟨12086900, by rfl⟩ : syracuseStep 16115867 = 24173801) B24173801
theorem B4245787 : Blo 1323480 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B1886527 : Blo 1323480 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B26159435 : Blo 1323480 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B1985243 : Blo 1323480 1985243 := bstep (se 1 (by rfl) ⟨1488932, by rfl⟩ : syracuseStep 1985243 = 2977865) B2977865
theorem B1985279 : Blo 1323480 1985279 := bstep (se 1 (by rfl) ⟨1488959, by rfl⟩ : syracuseStep 1985279 = 2977919) B2977919
theorem B4467527 : Blo 1323480 4467527 := bstep (se 1 (by rfl) ⟨3350645, by rfl⟩ : syracuseStep 4467527 = 6701291) B6701291
theorem B8481631 : Blo 1323480 8481631 := bstep (se 1 (by rfl) ⟨6361223, by rfl⟩ : syracuseStep 8481631 = 12722447) B12722447
theorem B28625849 : Blo 1323480 28625849 := bstep (se 2 (by rfl) ⟨10734693, by rfl⟩ : syracuseStep 28625849 = 21469387) B21469387
theorem B36269003 : Blo 1323480 36269003 := bstep (se 1 (by rfl) ⟨27201752, by rfl⟩ : syracuseStep 36269003 = 54403505) B54403505
theorem B1788895 : Blo 1323480 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B5655719 : Blo 1323480 5655719 := bstep (se 1 (by rfl) ⟨4241789, by rfl⟩ : syracuseStep 5655719 = 8483579) B8483579
theorem B1985999 : Blo 1323480 1985999 := bstep (se 1 (by rfl) ⟨1489499, by rfl⟩ : syracuseStep 1985999 = 2978999) B2978999
theorem B16100831 : Blo 1323480 16100831 := bstep (se 1 (by rfl) ⟨12075623, by rfl⟩ : syracuseStep 16100831 = 24151247) B24151247
theorem B1986089 : Blo 1323480 1986089 := bstep (se 2 (by rfl) ⟨744783, by rfl⟩ : syracuseStep 1986089 = 1489567) B1489567
theorem B7548659 : Blo 1323480 7548659 := bstep (se 1 (by rfl) ⟨5661494, by rfl⟩ : syracuseStep 7548659 = 11322989) B11322989
theorem B12898055 : Blo 1323480 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B15077177 : Blo 1323480 15077177 := bstep (se 2 (by rfl) ⟨5653941, by rfl⟩ : syracuseStep 15077177 = 11307883) B11307883
theorem B1986383 : Blo 1323480 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B1986503 : Blo 1323480 1986503 := bstep (se 1 (by rfl) ⟨1489877, by rfl⟩ : syracuseStep 1986503 = 2979755) B2979755
theorem B16977923 : Blo 1323480 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B1986587 : Blo 1323480 1986587 := bstep (se 1 (by rfl) ⟨1489940, by rfl⟩ : syracuseStep 1986587 = 2979881) B2979881
theorem B16969823 : Blo 1323480 16969823 := bstep (se 1 (by rfl) ⟨12727367, by rfl⟩ : syracuseStep 16969823 = 25454735) B25454735
theorem B2977991 : Blo 1323480 2977991 := bstep (se 1 (by rfl) ⟨2233493, by rfl⟩ : syracuseStep 2977991 = 4466987) B4466987
theorem B1986863 : Blo 1323480 1986863 := bstep (se 1 (by rfl) ⟨1490147, by rfl⟩ : syracuseStep 1986863 = 2980295) B2980295
theorem B2978171 : Blo 1323480 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B1986971 : Blo 1323480 1986971 := bstep (se 1 (by rfl) ⟨1490228, by rfl⟩ : syracuseStep 1986971 = 2980457) B2980457
theorem B1987007 : Blo 1323480 1987007 := bstep (se 1 (by rfl) ⟨1490255, by rfl⟩ : syracuseStep 1987007 = 2980511) B2980511
theorem B1323547 : Blo 1323480 1323547 := bstep (se 1 (by rfl) ⟨992660, by rfl⟩ : syracuseStep 1323547 = 1985321) B1985321
theorem B1987103 : Blo 1323480 1987103 := bstep (se 1 (by rfl) ⟨1490327, by rfl⟩ : syracuseStep 1987103 = 2980655) B2980655
theorem B25465427 : Blo 1323480 25465427 := bstep (se 1 (by rfl) ⟨19099070, by rfl⟩ : syracuseStep 25465427 = 38198141) B38198141
theorem B2978441 : Blo 1323480 2978441 := bstep (se 2 (by rfl) ⟨1116915, by rfl⟩ : syracuseStep 2978441 = 2233831) B2233831
theorem B1323687 : Blo 1323480 1323687 := bstep (se 1 (by rfl) ⟨992765, by rfl⟩ : syracuseStep 1323687 = 1985531) B1985531
theorem B10064573 : Blo 1323480 10064573 := bstep (se 3 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 10064573 = 3774215) B3774215
theorem B1323727 : Blo 1323480 1323727 := bstep (se 1 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 1323727 = 1985591) B1985591
theorem B1323807 : Blo 1323480 1323807 := bstep (se 1 (by rfl) ⟨992855, by rfl⟩ : syracuseStep 1323807 = 1985711) B1985711
theorem B1987391 : Blo 1323480 1987391 := bstep (se 1 (by rfl) ⟨1490543, by rfl⟩ : syracuseStep 1987391 = 2981087) B2981087
theorem B2978657 : Blo 1323480 2978657 := bstep (se 2 (by rfl) ⟨1116996, by rfl⟩ : syracuseStep 2978657 = 2233993) B2233993
theorem B15094673 : Blo 1323480 15094673 := bstep (se 2 (by rfl) ⟨5660502, by rfl⟩ : syracuseStep 15094673 = 11321005) B11321005
theorem B32215967 : Blo 1323480 32215967 := bstep (se 1 (by rfl) ⟨24161975, by rfl⟩ : syracuseStep 32215967 = 48323951) B48323951
theorem B1987535 : Blo 1323480 1987535 := bstep (se 1 (by rfl) ⟨1490651, by rfl⟩ : syracuseStep 1987535 = 2981303) B2981303
theorem B1987625 : Blo 1323480 1987625 := bstep (se 2 (by rfl) ⟨745359, by rfl⟩ : syracuseStep 1987625 = 1490719) B1490719
theorem B1987655 : Blo 1323480 1987655 := bstep (se 1 (by rfl) ⟨1490741, by rfl⟩ : syracuseStep 1987655 = 2981483) B2981483
theorem B3773623 : Blo 1323480 3773623 := bstep (se 1 (by rfl) ⟨2830217, by rfl⟩ : syracuseStep 3773623 = 5660435) B5660435
theorem B1987835 : Blo 1323480 1987835 := bstep (se 1 (by rfl) ⟨1490876, by rfl⟩ : syracuseStep 1987835 = 2981753) B2981753
theorem B1324287 : Blo 1323480 1324287 := bstep (se 1 (by rfl) ⟨993215, by rfl⟩ : syracuseStep 1324287 = 1986431) B1986431
theorem B12735791 : Blo 1323480 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B1987895 : Blo 1323480 1987895 := bstep (se 1 (by rfl) ⟨1490921, by rfl⟩ : syracuseStep 1987895 = 2981843) B2981843
theorem B2979179 : Blo 1323480 2979179 := bstep (se 1 (by rfl) ⟨2234384, by rfl⟩ : syracuseStep 2979179 = 4468769) B4468769
theorem B1324415 : Blo 1323480 1324415 := bstep (se 1 (by rfl) ⟨993311, by rfl⟩ : syracuseStep 1324415 = 1986623) B1986623
theorem B19355041 : Blo 1323480 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B12080623 : Blo 1323480 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B1324571 : Blo 1323480 1324571 := bstep (se 1 (by rfl) ⟨993428, by rfl⟩ : syracuseStep 1324571 = 1986857) B1986857
theorem B2233919 : Blo 1323480 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B2979431 : Blo 1323480 2979431 := bstep (se 1 (by rfl) ⟨2234573, by rfl⟩ : syracuseStep 2979431 = 4469147) B4469147
theorem B1988201 : Blo 1323480 1988201 := bstep (se 2 (by rfl) ⟨745575, by rfl⟩ : syracuseStep 1988201 = 1491151) B1491151
theorem B2979449 : Blo 1323480 2979449 := bstep (se 2 (by rfl) ⟨1117293, by rfl⟩ : syracuseStep 2979449 = 2234587) B2234587
theorem B1324751 : Blo 1323480 1324751 := bstep (se 1 (by rfl) ⟨993563, by rfl⟩ : syracuseStep 1324751 = 1987127) B1987127
theorem B3774239 : Blo 1323480 3774239 := bstep (se 1 (by rfl) ⟨2830679, by rfl⟩ : syracuseStep 3774239 = 5661359) B5661359
theorem B1324991 : Blo 1323480 1324991 := bstep (se 1 (by rfl) ⟨993743, by rfl⟩ : syracuseStep 1324991 = 1987487) B1987487
theorem B2979809 : Blo 1323480 2979809 := bstep (se 2 (by rfl) ⟨1117428, by rfl⟩ : syracuseStep 2979809 = 2234857) B2234857
theorem B10737683 : Blo 1323480 10737683 := bstep (se 1 (by rfl) ⟨8053262, by rfl⟩ : syracuseStep 10737683 = 16106525) B16106525
theorem B1677343 : Blo 1323480 1677343 := bstep (se 1 (by rfl) ⟨1258007, by rfl⟩ : syracuseStep 1677343 = 2516015) B2516015
theorem B1325119 : Blo 1323480 1325119 := bstep (se 1 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 1325119 = 1987679) B1987679
theorem B1325159 : Blo 1323480 1325159 := bstep (se 1 (by rfl) ⟨993869, by rfl⟩ : syracuseStep 1325159 = 1987739) B1987739
theorem B2234479 : Blo 1323480 2234479 := bstep (se 1 (by rfl) ⟨1675859, by rfl⟩ : syracuseStep 2234479 = 3351719) B3351719
theorem B5658761 : Blo 1323480 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B2980007 : Blo 1323480 2980007 := bstep (se 1 (by rfl) ⟨2235005, by rfl⟩ : syracuseStep 2980007 = 4470011) B4470011
theorem B7543327 : Blo 1323480 7543327 := bstep (se 1 (by rfl) ⟨5657495, by rfl⟩ : syracuseStep 7543327 = 11314991) B11314991
theorem B28645919 : Blo 1323480 28645919 := bstep (se 1 (by rfl) ⟨21484439, by rfl⟩ : syracuseStep 28645919 = 42968879) B42968879
theorem B7158539 : Blo 1323480 7158539 := bstep (se 1 (by rfl) ⟨5368904, by rfl⟩ : syracuseStep 7158539 = 10737809) B10737809
theorem B2513767 : Blo 1323480 2513767 := bstep (se 1 (by rfl) ⟨1885325, by rfl⟩ : syracuseStep 2513767 = 3770651) B3770651
theorem B1489855 : Blo 1323480 1489855 := bstep (se 1 (by rfl) ⟨1117391, by rfl⟩ : syracuseStep 1489855 = 2234783) B2234783
theorem B6798305 : Blo 1323480 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B64470437 : Blo 1323480 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B6364763 : Blo 1323480 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B3350119 : Blo 1323480 3350119 := bstep (se 1 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 3350119 = 5025179) B5025179
theorem B2514655 : Blo 1323480 2514655 := bstep (se 1 (by rfl) ⟨1885991, by rfl⟩ : syracuseStep 2514655 = 3771983) B3771983
theorem B15097589 : Blo 1323480 15097589 := bstep (se 5 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 15097589 = 1415399) B1415399
theorem B1490683 : Blo 1323480 1490683 := bstep (se 1 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 1490683 = 2236025) B2236025
theorem B3350281 : Blo 1323480 3350281 := bstep (se 2 (by rfl) ⟨1256355, by rfl⟩ : syracuseStep 3350281 = 2512711) B2512711
theorem B2015135 : Blo 1323480 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B2236457 : Blo 1323480 2236457 := bstep (se 2 (by rfl) ⟨838671, by rfl⟩ : syracuseStep 2236457 = 1677343) B1677343
theorem B11313215 : Blo 1323480 11313215 := bstep (se 1 (by rfl) ⟨8484911, by rfl⟩ : syracuseStep 11313215 = 16969823) B16969823
theorem B2515369 : Blo 1323480 2515369 := bstep (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) B1886527
theorem B6709715 : Blo 1323480 6709715 := bstep (se 1 (by rfl) ⟨5032286, by rfl⟩ : syracuseStep 6709715 = 10064573) B10064573
theorem B5653259 : Blo 1323480 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B3351689 : Blo 1323480 3351689 := bstep (se 2 (by rfl) ⟨1256883, by rfl⟩ : syracuseStep 3351689 = 2513767) B2513767
theorem B2516159 : Blo 1323480 2516159 := bstep (se 1 (by rfl) ⟨1887119, by rfl⟩ : syracuseStep 2516159 = 3774239) B3774239
theorem B22644197 : Blo 1323480 22644197 := bstep (se 4 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 22644197 = 4245787) B4245787
theorem B5031497 : Blo 1323480 5031497 := bstep (se 2 (by rfl) ⟨1886811, by rfl⟩ : syracuseStep 5031497 = 3773623) B3773623
theorem B19097279 : Blo 1323480 19097279 := bstep (se 1 (by rfl) ⟨14322959, by rfl⟩ : syracuseStep 19097279 = 28645919) B28645919
theorem B25806721 : Blo 1323480 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B16107497 : Blo 1323480 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B4532203 : Blo 1323480 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B3770479 : Blo 1323480 3770479 := bstep (se 1 (by rfl) ⟨2827859, by rfl⟩ : syracuseStep 3770479 = 5655719) B5655719
theorem B4466825 : Blo 1323480 4466825 := bstep (se 2 (by rfl) ⟨1675059, by rfl⟩ : syracuseStep 4466825 = 3350119) B3350119
theorem B3352873 : Blo 1323480 3352873 := bstep (se 2 (by rfl) ⟨1257327, by rfl⟩ : syracuseStep 3352873 = 2514655) B2514655
theorem B10733887 : Blo 1323480 10733887 := bstep (se 1 (by rfl) ⟨8050415, by rfl⟩ : syracuseStep 10733887 = 16100831) B16100831
theorem B4467041 : Blo 1323480 4467041 := bstep (se 2 (by rfl) ⟨1675140, by rfl⟩ : syracuseStep 4467041 = 3350281) B3350281
theorem B5032439 : Blo 1323480 5032439 := bstep (se 1 (by rfl) ⟨3774329, by rfl⟩ : syracuseStep 5032439 = 7548659) B7548659
theorem B96717341 : Blo 1323480 96717341 := bstep (se 3 (by rfl) ⟨18134501, by rfl⟩ : syracuseStep 96717341 = 36269003) B36269003
theorem B10054367 : Blo 1323480 10054367 := bstep (se 1 (by rfl) ⟨7540775, by rfl⟩ : syracuseStep 10054367 = 15081551) B15081551
theorem B1985327 : Blo 1323480 1985327 := bstep (se 1 (by rfl) ⟨1488995, by rfl⟩ : syracuseStep 1985327 = 2977991) B2977991
theorem B5737321 : Blo 1323480 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B1985447 : Blo 1323480 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B16976951 : Blo 1323480 16976951 := bstep (se 1 (by rfl) ⟨12732713, by rfl⟩ : syracuseStep 16976951 = 25465427) B25465427
theorem B1985627 : Blo 1323480 1985627 := bstep (se 1 (by rfl) ⟨1489220, by rfl⟩ : syracuseStep 1985627 = 2978441) B2978441
theorem B1985771 : Blo 1323480 1985771 := bstep (se 1 (by rfl) ⟨1489328, by rfl⟩ : syracuseStep 1985771 = 2978657) B2978657
theorem B10063115 : Blo 1323480 10063115 := bstep (se 1 (by rfl) ⟨7547336, by rfl⟩ : syracuseStep 10063115 = 15094673) B15094673
theorem B4468175 : Blo 1323480 4468175 := bstep (se 1 (by rfl) ⟨3351131, by rfl⟩ : syracuseStep 4468175 = 6702263) B6702263
theorem B8490527 : Blo 1323480 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B1986119 : Blo 1323480 1986119 := bstep (se 1 (by rfl) ⟨1489589, by rfl⟩ : syracuseStep 1986119 = 2979179) B2979179
theorem B1986287 : Blo 1323480 1986287 := bstep (se 1 (by rfl) ⟨1489715, by rfl⟩ : syracuseStep 1986287 = 2979431) B2979431
theorem B1986299 : Blo 1323480 1986299 := bstep (se 1 (by rfl) ⟨1489724, by rfl⟩ : syracuseStep 1986299 = 2979449) B2979449
theorem B11308841 : Blo 1323480 11308841 := bstep (se 2 (by rfl) ⟨4240815, by rfl⟩ : syracuseStep 11308841 = 8481631) B8481631
theorem B1986473 : Blo 1323480 1986473 := bstep (se 2 (by rfl) ⟨744927, by rfl⟩ : syracuseStep 1986473 = 1489855) B1489855
theorem B1986539 : Blo 1323480 1986539 := bstep (se 1 (by rfl) ⟨1489904, by rfl⟩ : syracuseStep 1986539 = 2979809) B2979809
theorem B3354655 : Blo 1323480 3354655 := bstep (se 1 (by rfl) ⟨2515991, by rfl⟩ : syracuseStep 3354655 = 5031983) B5031983
theorem B5025847 : Blo 1323480 5025847 := bstep (se 1 (by rfl) ⟨3769385, by rfl⟩ : syracuseStep 5025847 = 7538771) B7538771
theorem B3772507 : Blo 1323480 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B10743911 : Blo 1323480 10743911 := bstep (se 1 (by rfl) ⟨8057933, by rfl⟩ : syracuseStep 10743911 = 16115867) B16115867
theorem B1986671 : Blo 1323480 1986671 := bstep (se 1 (by rfl) ⟨1490003, by rfl⟩ : syracuseStep 1986671 = 2980007) B2980007
theorem B2830457 : Blo 1323480 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B1323495 : Blo 1323480 1323495 := bstep (se 1 (by rfl) ⟨992621, by rfl⟩ : syracuseStep 1323495 = 1985243) B1985243
theorem B1323519 : Blo 1323480 1323519 := bstep (se 1 (by rfl) ⟨992639, by rfl⟩ : syracuseStep 1323519 = 1985279) B1985279
theorem B4772359 : Blo 1323480 4772359 := bstep (se 1 (by rfl) ⟨3579269, by rfl⟩ : syracuseStep 4772359 = 7158539) B7158539
theorem B2978351 : Blo 1323480 2978351 := bstep (se 1 (by rfl) ⟨2233763, by rfl⟩ : syracuseStep 2978351 = 4467527) B4467527
theorem B19083899 : Blo 1323480 19083899 := bstep (se 1 (by rfl) ⟨14312924, by rfl⟩ : syracuseStep 19083899 = 28625849) B28625849
theorem B34394813 : Blo 1323480 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B42980291 : Blo 1323480 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B1323999 : Blo 1323480 1323999 := bstep (se 1 (by rfl) ⟨992999, by rfl⟩ : syracuseStep 1323999 = 1985999) B1985999
theorem B1987577 : Blo 1323480 1987577 := bstep (se 2 (by rfl) ⟨745341, by rfl⟩ : syracuseStep 1987577 = 1490683) B1490683
theorem B1324059 : Blo 1323480 1324059 := bstep (se 1 (by rfl) ⟨993044, by rfl⟩ : syracuseStep 1324059 = 1986089) B1986089
theorem B9540773 : Blo 1323480 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B10065059 : Blo 1323480 10065059 := bstep (se 1 (by rfl) ⟨7548794, by rfl⟩ : syracuseStep 10065059 = 15097589) B15097589
theorem B1324255 : Blo 1323480 1324255 := bstep (se 1 (by rfl) ⟨993191, by rfl⟩ : syracuseStep 1324255 = 1986383) B1986383
theorem B1324335 : Blo 1323480 1324335 := bstep (se 1 (by rfl) ⟨993251, by rfl⟩ : syracuseStep 1324335 = 1986503) B1986503
theorem B11318615 : Blo 1323480 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B1324391 : Blo 1323480 1324391 := bstep (se 1 (by rfl) ⟨993293, by rfl⟩ : syracuseStep 1324391 = 1986587) B1986587
theorem B2979305 : Blo 1323480 2979305 := bstep (se 2 (by rfl) ⟨1117239, by rfl⟩ : syracuseStep 2979305 = 2234479) B2234479
theorem B1324575 : Blo 1323480 1324575 := bstep (se 1 (by rfl) ⟨993431, by rfl⟩ : syracuseStep 1324575 = 1986863) B1986863
theorem B1324647 : Blo 1323480 1324647 := bstep (se 1 (by rfl) ⟨993485, by rfl⟩ : syracuseStep 1324647 = 1986971) B1986971
theorem B1324671 : Blo 1323480 1324671 := bstep (se 1 (by rfl) ⟨993503, by rfl⟩ : syracuseStep 1324671 = 1987007) B1987007
theorem B2234047 : Blo 1323480 2234047 := bstep (se 1 (by rfl) ⟨1675535, by rfl⟩ : syracuseStep 2234047 = 3351071) B3351071
theorem B1324735 : Blo 1323480 1324735 := bstep (se 1 (by rfl) ⟨993551, by rfl⟩ : syracuseStep 1324735 = 1987103) B1987103
theorem B1324927 : Blo 1323480 1324927 := bstep (se 1 (by rfl) ⟨993695, by rfl⟩ : syracuseStep 1324927 = 1987391) B1987391
theorem B21477311 : Blo 1323480 21477311 := bstep (se 1 (by rfl) ⟨16107983, by rfl⟩ : syracuseStep 21477311 = 32215967) B32215967
theorem B1325023 : Blo 1323480 1325023 := bstep (se 1 (by rfl) ⟨993767, by rfl⟩ : syracuseStep 1325023 = 1987535) B1987535
theorem B1325083 : Blo 1323480 1325083 := bstep (se 1 (by rfl) ⟨993812, by rfl⟩ : syracuseStep 1325083 = 1987625) B1987625
theorem B10057769 : Blo 1323480 10057769 := bstep (se 2 (by rfl) ⟨3771663, by rfl⟩ : syracuseStep 10057769 = 7543327) B7543327
theorem B1325103 : Blo 1323480 1325103 := bstep (se 1 (by rfl) ⟨993827, by rfl⟩ : syracuseStep 1325103 = 1987655) B1987655
theorem B1325223 : Blo 1323480 1325223 := bstep (se 1 (by rfl) ⟨993917, by rfl⟩ : syracuseStep 1325223 = 1987835) B1987835
theorem B1325263 : Blo 1323480 1325263 := bstep (se 1 (by rfl) ⟨993947, by rfl⟩ : syracuseStep 1325263 = 1987895) B1987895
theorem B1489279 : Blo 1323480 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B1325467 : Blo 1323480 1325467 := bstep (se 1 (by rfl) ⟨994100, by rfl⟩ : syracuseStep 1325467 = 1988201) B1988201
theorem B7158455 : Blo 1323480 7158455 := bstep (se 1 (by rfl) ⟨5368841, by rfl⟩ : syracuseStep 7158455 = 10737683) B10737683
theorem B17439623 : Blo 1323480 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B4243175 : Blo 1323480 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B10051451 : Blo 1323480 10051451 := bstep (se 1 (by rfl) ⟨7538588, by rfl⟩ : syracuseStep 10051451 = 15077177) B15077177
theorem B1343423 : Blo 1323480 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B1490971 : Blo 1323480 1490971 := bstep (se 1 (by rfl) ⟨1118228, by rfl⟩ : syracuseStep 1490971 = 2236457) B2236457
theorem B4472873 : Blo 1323480 4472873 := bstep (se 2 (by rfl) ⟨1677327, by rfl⟩ : syracuseStep 4472873 = 3354655) B3354655
theorem B6701129 : Blo 1323480 6701129 := bstep (se 2 (by rfl) ⟨2512923, by rfl⟩ : syracuseStep 6701129 = 5025847) B5025847
theorem B5030009 : Blo 1323480 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B4473143 : Blo 1323480 4473143 := bstep (se 1 (by rfl) ⟨3354857, by rfl⟩ : syracuseStep 4473143 = 6709715) B6709715
theorem B12722599 : Blo 1323480 12722599 := bstep (se 1 (by rfl) ⟨9541949, by rfl⟩ : syracuseStep 12722599 = 19083899) B19083899
theorem B14311849 : Blo 1323480 14311849 := bstep (se 2 (by rfl) ⟨5366943, by rfl⟩ : syracuseStep 14311849 = 10733887) B10733887
theorem B22929875 : Blo 1323480 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B3768839 : Blo 1323480 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B6710039 : Blo 1323480 6710039 := bstep (se 1 (by rfl) ⟨5032529, by rfl⟩ : syracuseStep 6710039 = 10065059) B10065059
theorem B7545743 : Blo 1323480 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B12731519 : Blo 1323480 12731519 := bstep (se 1 (by rfl) ⟨9548639, by rfl⟩ : syracuseStep 12731519 = 19097279) B19097279
theorem B6702911 : Blo 1323480 6702911 := bstep (se 1 (by rfl) ⟨5027183, by rfl⟩ : syracuseStep 6702911 = 10054367) B10054367
theorem B11626415 : Blo 1323480 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B2828783 : Blo 1323480 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B3582461 : Blo 1323480 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B34408961 : Blo 1323480 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B7539227 : Blo 1323480 7539227 := bstep (se 1 (by rfl) ⟨5654420, by rfl⟩ : syracuseStep 7539227 = 11308841) B11308841
theorem B7162607 : Blo 1323480 7162607 := bstep (se 1 (by rfl) ⟨5371955, by rfl⟩ : syracuseStep 7162607 = 10743911) B10743911
theorem B1886971 : Blo 1323480 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B1985567 : Blo 1323480 1985567 := bstep (se 1 (by rfl) ⟨1489175, by rfl⟩ : syracuseStep 1985567 = 2978351) B2978351
theorem B1985705 : Blo 1323480 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B3353825 : Blo 1323480 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B6360515 : Blo 1323480 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B1986203 : Blo 1323480 1986203 := bstep (se 1 (by rfl) ⟨1489652, by rfl⟩ : syracuseStep 1986203 = 2979305) B2979305
theorem B3354331 : Blo 1323480 3354331 := bstep (se 1 (by rfl) ⟨2515748, by rfl⟩ : syracuseStep 3354331 = 5031497) B5031497
theorem B6705179 : Blo 1323480 6705179 := bstep (se 1 (by rfl) ⟨5028884, by rfl⟩ : syracuseStep 6705179 = 10057769) B10057769
theorem B2977883 : Blo 1323480 2977883 := bstep (se 1 (by rfl) ⟨2233412, by rfl⟩ : syracuseStep 2977883 = 4466825) B4466825
theorem B2978027 : Blo 1323480 2978027 := bstep (se 1 (by rfl) ⟨2233520, by rfl⟩ : syracuseStep 2978027 = 4467041) B4467041
theorem B3354959 : Blo 1323480 3354959 := bstep (se 1 (by rfl) ⟨2516219, by rfl⟩ : syracuseStep 3354959 = 5032439) B5032439
theorem B4772303 : Blo 1323480 4772303 := bstep (se 1 (by rfl) ⟨3579227, by rfl⟩ : syracuseStep 4772303 = 7158455) B7158455
theorem B1323551 : Blo 1323480 1323551 := bstep (se 1 (by rfl) ⟨992663, by rfl⟩ : syracuseStep 1323551 = 1985327) B1985327
theorem B1323631 : Blo 1323480 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B11317967 : Blo 1323480 11317967 := bstep (se 1 (by rfl) ⟨8488475, by rfl⟩ : syracuseStep 11317967 = 16976951) B16976951
theorem B1323751 : Blo 1323480 1323751 := bstep (se 1 (by rfl) ⟨992813, by rfl⟩ : syracuseStep 1323751 = 1985627) B1985627
theorem B1323847 : Blo 1323480 1323847 := bstep (se 1 (by rfl) ⟨992885, by rfl⟩ : syracuseStep 1323847 = 1985771) B1985771
theorem B2978729 : Blo 1323480 2978729 := bstep (se 2 (by rfl) ⟨1117023, by rfl⟩ : syracuseStep 2978729 = 2234047) B2234047
theorem B2978783 : Blo 1323480 2978783 := bstep (se 1 (by rfl) ⟨2234087, by rfl⟩ : syracuseStep 2978783 = 4468175) B4468175
theorem B1324079 : Blo 1323480 1324079 := bstep (se 1 (by rfl) ⟨993059, by rfl⟩ : syracuseStep 1324079 = 1986119) B1986119
theorem B1324191 : Blo 1323480 1324191 := bstep (se 1 (by rfl) ⟨993143, by rfl⟩ : syracuseStep 1324191 = 1986287) B1986287
theorem B1324199 : Blo 1323480 1324199 := bstep (se 1 (by rfl) ⟨993149, by rfl⟩ : syracuseStep 1324199 = 1986299) B1986299
theorem B1324315 : Blo 1323480 1324315 := bstep (se 1 (by rfl) ⟨993236, by rfl⟩ : syracuseStep 1324315 = 1986473) B1986473
theorem B6042937 : Blo 1323480 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B1324359 : Blo 1323480 1324359 := bstep (se 1 (by rfl) ⟨993269, by rfl⟩ : syracuseStep 1324359 = 1986539) B1986539
theorem B7542143 : Blo 1323480 7542143 := bstep (se 1 (by rfl) ⟨5656607, by rfl⟩ : syracuseStep 7542143 = 11313215) B11313215
theorem B1324447 : Blo 1323480 1324447 := bstep (se 1 (by rfl) ⟨993335, by rfl⟩ : syracuseStep 1324447 = 1986671) B1986671
theorem B5027305 : Blo 1323480 5027305 := bstep (se 2 (by rfl) ⟨1885239, by rfl⟩ : syracuseStep 5027305 = 3770479) B3770479
theorem B4470497 : Blo 1323480 4470497 := bstep (se 2 (by rfl) ⟨1676436, by rfl⟩ : syracuseStep 4470497 = 3352873) B3352873
theorem B28653527 : Blo 1323480 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B1325051 : Blo 1323480 1325051 := bstep (se 1 (by rfl) ⟨993788, by rfl⟩ : syracuseStep 1325051 = 1987577) B1987577
theorem B6363145 : Blo 1323480 6363145 := bstep (se 2 (by rfl) ⟨2386179, by rfl⟩ : syracuseStep 6363145 = 4772359) B4772359
theorem B2234459 : Blo 1323480 2234459 := bstep (se 1 (by rfl) ⟨1675844, by rfl⟩ : syracuseStep 2234459 = 3351689) B3351689
theorem B1677439 : Blo 1323480 1677439 := bstep (se 1 (by rfl) ⟨1258079, by rfl⟩ : syracuseStep 1677439 = 2516159) B2516159
theorem B15096131 : Blo 1323480 15096131 := bstep (se 1 (by rfl) ⟨11322098, by rfl⟩ : syracuseStep 15096131 = 22644197) B22644197
theorem B7649761 : Blo 1323480 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B14318207 : Blo 1323480 14318207 := bstep (se 1 (by rfl) ⟨10738655, by rfl⟩ : syracuseStep 14318207 = 21477311) B21477311
theorem B10738331 : Blo 1323480 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B64478227 : Blo 1323480 64478227 := bstep (se 1 (by rfl) ⟨48358670, by rfl⟩ : syracuseStep 64478227 = 96717341) B96717341
theorem B6708743 : Blo 1323480 6708743 := bstep (se 1 (by rfl) ⟨5031557, by rfl⟩ : syracuseStep 6708743 = 10063115) B10063115
theorem B5660351 : Blo 1323480 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B6700967 : Blo 1323480 6700967 := bstep (se 1 (by rfl) ⟨5025725, by rfl⟩ : syracuseStep 6700967 = 10051451) B10051451
theorem B2981915 : Blo 1323480 2981915 := bstep (se 1 (by rfl) ⟨2236436, by rfl⟩ : syracuseStep 2981915 = 4472873) B4472873
theorem B2236585 : Blo 1323480 2236585 := bstep (se 2 (by rfl) ⟨838719, by rfl⟩ : syracuseStep 2236585 = 1677439) B1677439
theorem B2982095 : Blo 1323480 2982095 := bstep (se 1 (by rfl) ⟨2236571, by rfl⟩ : syracuseStep 2982095 = 4473143) B4473143
theorem B2236639 : Blo 1323480 2236639 := bstep (se 1 (by rfl) ⟨1677479, by rfl⟩ : syracuseStep 2236639 = 3354959) B3354959
theorem B15286583 : Blo 1323480 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B7545311 : Blo 1323480 7545311 := bstep (se 1 (by rfl) ⟨5658983, by rfl⟩ : syracuseStep 7545311 = 11317967) B11317967
theorem B4473359 : Blo 1323480 4473359 := bstep (se 1 (by rfl) ⟨3355019, by rfl⟩ : syracuseStep 4473359 = 6710039) B6710039
theorem B5030495 : Blo 1323480 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B10199681 : Blo 1323480 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B8487679 : Blo 1323480 8487679 := bstep (se 1 (by rfl) ⟨6365759, by rfl⟩ : syracuseStep 8487679 = 12731519) B12731519
theorem B2515961 : Blo 1323480 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B7750943 : Blo 1323480 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B1885855 : Blo 1323480 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B22939307 : Blo 1323480 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B9545471 : Blo 1323480 9545471 := bstep (se 1 (by rfl) ⟨7159103, by rfl⟩ : syracuseStep 9545471 = 14318207) B14318207
theorem B6703073 : Blo 1323480 6703073 := bstep (se 2 (by rfl) ⟨2513652, by rfl⟩ : syracuseStep 6703073 = 5027305) B5027305
theorem B76409405 : Blo 1323480 76409405 := bstep (se 3 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 76409405 = 28653527) B28653527
theorem B4467311 : Blo 1323480 4467311 := bstep (se 1 (by rfl) ⟨3350483, by rfl⟩ : syracuseStep 4467311 = 6700967) B6700967
theorem B4467419 : Blo 1323480 4467419 := bstep (se 1 (by rfl) ⟨3350564, by rfl⟩ : syracuseStep 4467419 = 6701129) B6701129
theorem B1985255 : Blo 1323480 1985255 := bstep (se 1 (by rfl) ⟨1488941, by rfl⟩ : syracuseStep 1985255 = 2977883) B2977883
theorem B3353339 : Blo 1323480 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B1985351 : Blo 1323480 1985351 := bstep (se 1 (by rfl) ⟨1489013, by rfl⟩ : syracuseStep 1985351 = 2978027) B2978027
theorem B3181535 : Blo 1323480 3181535 := bstep (se 1 (by rfl) ⟨2386151, by rfl⟩ : syracuseStep 3181535 = 4772303) B4772303
theorem B19082465 : Blo 1323480 19082465 := bstep (se 2 (by rfl) ⟨7155924, by rfl⟩ : syracuseStep 19082465 = 14311849) B14311849
theorem B1985819 : Blo 1323480 1985819 := bstep (se 1 (by rfl) ⟨1489364, by rfl⟩ : syracuseStep 1985819 = 2978729) B2978729
theorem B1985855 : Blo 1323480 1985855 := bstep (se 1 (by rfl) ⟨1489391, by rfl⟩ : syracuseStep 1985855 = 2978783) B2978783
theorem B4468607 : Blo 1323480 4468607 := bstep (se 1 (by rfl) ⟨3351455, by rfl⟩ : syracuseStep 4468607 = 6702911) B6702911
theorem B85970969 : Blo 1323480 85970969 := bstep (se 2 (by rfl) ⟨32239113, by rfl⟩ : syracuseStep 85970969 = 64478227) B64478227
theorem B10064087 : Blo 1323480 10064087 := bstep (se 1 (by rfl) ⟨7548065, by rfl⟩ : syracuseStep 10064087 = 15096131) B15096131
theorem B2388307 : Blo 1323480 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B5026151 : Blo 1323480 5026151 := bstep (se 1 (by rfl) ⟨3769613, by rfl⟩ : syracuseStep 5026151 = 7539227) B7539227
theorem B8057249 : Blo 1323480 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1323711 : Blo 1323480 1323711 := bstep (se 1 (by rfl) ⟨992783, by rfl⟩ : syracuseStep 1323711 = 1985567) B1985567
theorem B1323803 : Blo 1323480 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B4240343 : Blo 1323480 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B1324135 : Blo 1323480 1324135 := bstep (se 1 (by rfl) ⟨993101, by rfl⟩ : syracuseStep 1324135 = 1986203) B1986203
theorem B3773567 : Blo 1323480 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B8484193 : Blo 1323480 8484193 := bstep (se 2 (by rfl) ⟨3181572, by rfl⟩ : syracuseStep 8484193 = 6363145) B6363145
theorem B4470119 : Blo 1323480 4470119 := bstep (se 1 (by rfl) ⟨3352589, by rfl⟩ : syracuseStep 4470119 = 6705179) B6705179
theorem B1987961 : Blo 1323480 1987961 := bstep (se 2 (by rfl) ⟨745485, by rfl⟩ : syracuseStep 1987961 = 1490971) B1490971
theorem B2512559 : Blo 1323480 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B16963465 : Blo 1323480 16963465 := bstep (se 2 (by rfl) ⟨6361299, by rfl⟩ : syracuseStep 16963465 = 12722599) B12722599
theorem B5028095 : Blo 1323480 5028095 := bstep (se 1 (by rfl) ⟨3771071, by rfl⟩ : syracuseStep 5028095 = 7542143) B7542143
theorem B2980331 : Blo 1323480 2980331 := bstep (se 1 (by rfl) ⟨2235248, by rfl⟩ : syracuseStep 2980331 = 4470497) B4470497
theorem B1489639 : Blo 1323480 1489639 := bstep (se 1 (by rfl) ⟨1117229, by rfl⟩ : syracuseStep 1489639 = 2234459) B2234459
theorem B7158887 : Blo 1323480 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B4775071 : Blo 1323480 4775071 := bstep (se 1 (by rfl) ⟨3581303, by rfl⟩ : syracuseStep 4775071 = 7162607) B7162607
theorem B2235883 : Blo 1323480 2235883 := bstep (se 1 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 2235883 = 3353825) B3353825
theorem B4472441 : Blo 1323480 4472441 := bstep (se 2 (by rfl) ⟨1677165, by rfl⟩ : syracuseStep 4472441 = 3354331) B3354331
theorem B4472495 : Blo 1323480 4472495 := bstep (se 1 (by rfl) ⟨3354371, by rfl⟩ : syracuseStep 4472495 = 6708743) B6708743
theorem B6709391 : Blo 1323480 6709391 := bstep (se 1 (by rfl) ⟨5032043, by rfl⟩ : syracuseStep 6709391 = 10064087) B10064087
theorem B10191055 : Blo 1323480 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B2982113 : Blo 1323480 2982113 := bstep (se 2 (by rfl) ⟨1118292, by rfl⟩ : syracuseStep 2982113 = 2236585) B2236585
theorem B3350767 : Blo 1323480 3350767 := bstep (se 1 (by rfl) ⟨2513075, by rfl⟩ : syracuseStep 3350767 = 5026151) B5026151
theorem B2982185 : Blo 1323480 2982185 := bstep (se 2 (by rfl) ⟨1118319, by rfl⟩ : syracuseStep 2982185 = 2236639) B2236639
theorem B5030207 : Blo 1323480 5030207 := bstep (se 1 (by rfl) ⟨3772655, by rfl⟩ : syracuseStep 5030207 = 7545311) B7545311
theorem B2982239 : Blo 1323480 2982239 := bstep (se 1 (by rfl) ⟨2236679, by rfl⟩ : syracuseStep 2982239 = 4473359) B4473359
theorem B6799787 : Blo 1323480 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B2826895 : Blo 1323480 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B2515711 : Blo 1323480 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B3352063 : Blo 1323480 3352063 := bstep (se 1 (by rfl) ⟨2514047, by rfl⟩ : syracuseStep 3352063 = 5028095) B5028095
theorem B6366761 : Blo 1323480 6366761 := bstep (se 2 (by rfl) ⟨2387535, by rfl⟩ : syracuseStep 6366761 = 4775071) B4775071
theorem B50939603 : Blo 1323480 50939603 := bstep (se 1 (by rfl) ⟨38204702, by rfl⟩ : syracuseStep 50939603 = 76409405) B76409405
theorem B57313979 : Blo 1323480 57313979 := bstep (se 1 (by rfl) ⟨42985484, by rfl⟩ : syracuseStep 57313979 = 85970969) B85970969
theorem B3353663 : Blo 1323480 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B1986185 : Blo 1323480 1986185 := bstep (se 2 (by rfl) ⟨744819, by rfl⟩ : syracuseStep 1986185 = 1489639) B1489639
theorem B11316905 : Blo 1323480 11316905 := bstep (se 2 (by rfl) ⟨4243839, by rfl⟩ : syracuseStep 11316905 = 8487679) B8487679
theorem B4468715 : Blo 1323480 4468715 := bstep (se 1 (by rfl) ⟨3351536, by rfl⟩ : syracuseStep 4468715 = 6703073) B6703073
theorem B1986887 : Blo 1323480 1986887 := bstep (se 1 (by rfl) ⟨1490165, by rfl⟩ : syracuseStep 1986887 = 2980331) B2980331
theorem B2978207 : Blo 1323480 2978207 := bstep (se 1 (by rfl) ⟨2233655, by rfl⟩ : syracuseStep 2978207 = 4467311) B4467311
theorem B2978279 : Blo 1323480 2978279 := bstep (se 1 (by rfl) ⟨2233709, by rfl⟩ : syracuseStep 2978279 = 4467419) B4467419
theorem B1323503 : Blo 1323480 1323503 := bstep (se 1 (by rfl) ⟨992627, by rfl⟩ : syracuseStep 1323503 = 1985255) B1985255
theorem B1323567 : Blo 1323480 1323567 := bstep (se 1 (by rfl) ⟨992675, by rfl⟩ : syracuseStep 1323567 = 1985351) B1985351
theorem B4772591 : Blo 1323480 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B1323879 : Blo 1323480 1323879 := bstep (se 1 (by rfl) ⟨992909, by rfl⟩ : syracuseStep 1323879 = 1985819) B1985819
theorem B1323903 : Blo 1323480 1323903 := bstep (se 1 (by rfl) ⟨992927, by rfl⟩ : syracuseStep 1323903 = 1985855) B1985855
theorem B2979071 : Blo 1323480 2979071 := bstep (se 1 (by rfl) ⟨2234303, by rfl⟩ : syracuseStep 2979071 = 4468607) B4468607
theorem B1987943 : Blo 1323480 1987943 := bstep (se 1 (by rfl) ⟨1490957, by rfl⟩ : syracuseStep 1987943 = 2981915) B2981915
theorem B1988063 : Blo 1323480 1988063 := bstep (se 1 (by rfl) ⟨1491047, by rfl⟩ : syracuseStep 1988063 = 2982095) B2982095
theorem B5371499 : Blo 1323480 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B3184409 : Blo 1323480 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B5167295 : Blo 1323480 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B2980079 : Blo 1323480 2980079 := bstep (se 1 (by rfl) ⟨2235059, by rfl⟩ : syracuseStep 2980079 = 4470119) B4470119
theorem B1325307 : Blo 1323480 1325307 := bstep (se 1 (by rfl) ⟨993980, by rfl⟩ : syracuseStep 1325307 = 1987961) B1987961
theorem B15292871 : Blo 1323480 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B6363647 : Blo 1323480 6363647 := bstep (se 1 (by rfl) ⟨4772735, by rfl⟩ : syracuseStep 6363647 = 9545471) B9545471
theorem B6700157 : Blo 1323480 6700157 := bstep (se 3 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 6700157 = 2512559) B2512559
theorem B11312257 : Blo 1323480 11312257 := bstep (se 2 (by rfl) ⟨4242096, by rfl⟩ : syracuseStep 11312257 = 8484193) B8484193
theorem B2235559 : Blo 1323480 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B2981177 : Blo 1323480 2981177 := bstep (se 2 (by rfl) ⟨1117941, by rfl⟩ : syracuseStep 2981177 = 2235883) B2235883
theorem B2121023 : Blo 1323480 2121023 := bstep (se 1 (by rfl) ⟨1590767, by rfl⟩ : syracuseStep 2121023 = 3181535) B3181535
theorem B12721643 : Blo 1323480 12721643 := bstep (se 1 (by rfl) ⟨9541232, by rfl⟩ : syracuseStep 12721643 = 19082465) B19082465
theorem B2514473 : Blo 1323480 2514473 := bstep (se 2 (by rfl) ⟨942927, by rfl⟩ : syracuseStep 2514473 = 1885855) B1885855
theorem B2981627 : Blo 1323480 2981627 := bstep (se 1 (by rfl) ⟨2236220, by rfl⟩ : syracuseStep 2981627 = 4472441) B4472441
theorem B2981663 : Blo 1323480 2981663 := bstep (se 1 (by rfl) ⟨2236247, by rfl⟩ : syracuseStep 2981663 = 4472495) B4472495
theorem B22617953 : Blo 1323480 22617953 := bstep (se 2 (by rfl) ⟨8481732, by rfl⟩ : syracuseStep 22617953 = 16963465) B16963465
theorem B6709229 : Blo 1323480 6709229 := bstep (se 3 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 6709229 = 2515961) B2515961
theorem B4472927 : Blo 1323480 4472927 := bstep (se 1 (by rfl) ⟨3354695, by rfl⟩ : syracuseStep 4472927 = 6709391) B6709391
theorem B3769193 : Blo 1323480 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B4244507 : Blo 1323480 4244507 := bstep (se 1 (by rfl) ⟨3183380, by rfl⟩ : syracuseStep 4244507 = 6366761) B6366761
theorem B3580999 : Blo 1323480 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B2122939 : Blo 1323480 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B15083009 : Blo 1323480 15083009 := bstep (se 2 (by rfl) ⟨5656128, by rfl⟩ : syracuseStep 15083009 = 11312257) B11312257
theorem B38209319 : Blo 1323480 38209319 := bstep (se 1 (by rfl) ⟨28656989, by rfl⟩ : syracuseStep 38209319 = 57313979) B57313979
theorem B4466771 : Blo 1323480 4466771 := bstep (se 1 (by rfl) ⟨3350078, by rfl⟩ : syracuseStep 4466771 = 6700157) B6700157
theorem B8481095 : Blo 1323480 8481095 := bstep (se 1 (by rfl) ⟨6360821, by rfl⟩ : syracuseStep 8481095 = 12721643) B12721643
theorem B3353471 : Blo 1323480 3353471 := bstep (se 1 (by rfl) ⟨2515103, by rfl⟩ : syracuseStep 3353471 = 5030207) B5030207
theorem B1985471 : Blo 1323480 1985471 := bstep (se 1 (by rfl) ⟨1489103, by rfl⟩ : syracuseStep 1985471 = 2978207) B2978207
theorem B4533191 : Blo 1323480 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B4467689 : Blo 1323480 4467689 := bstep (se 2 (by rfl) ⟨1675383, by rfl⟩ : syracuseStep 4467689 = 3350767) B3350767
theorem B1985519 : Blo 1323480 1985519 := bstep (se 1 (by rfl) ⟨1489139, by rfl⟩ : syracuseStep 1985519 = 2978279) B2978279
theorem B3181727 : Blo 1323480 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B5656061 : Blo 1323480 5656061 := bstep (se 3 (by rfl) ⟨1060511, by rfl⟩ : syracuseStep 5656061 = 2121023) B2121023
theorem B1986047 : Blo 1323480 1986047 := bstep (se 1 (by rfl) ⟨1489535, by rfl⟩ : syracuseStep 1986047 = 2979071) B2979071
theorem B3354281 : Blo 1323480 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B33959735 : Blo 1323480 33959735 := bstep (se 1 (by rfl) ⟨25469801, by rfl⟩ : syracuseStep 33959735 = 50939603) B50939603
theorem B3444863 : Blo 1323480 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B1986719 : Blo 1323480 1986719 := bstep (se 1 (by rfl) ⟨1490039, by rfl⟩ : syracuseStep 1986719 = 2980079) B2980079
theorem B10195247 : Blo 1323480 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B4469417 : Blo 1323480 4469417 := bstep (se 2 (by rfl) ⟨1676031, by rfl⟩ : syracuseStep 4469417 = 3352063) B3352063
theorem B1987451 : Blo 1323480 1987451 := bstep (se 1 (by rfl) ⟨1490588, by rfl⟩ : syracuseStep 1987451 = 2981177) B2981177
theorem B1676315 : Blo 1323480 1676315 := bstep (se 1 (by rfl) ⟨1257236, by rfl⟩ : syracuseStep 1676315 = 2514473) B2514473
theorem B1324123 : Blo 1323480 1324123 := bstep (se 1 (by rfl) ⟨993092, by rfl⟩ : syracuseStep 1324123 = 1986185) B1986185
theorem B1987751 : Blo 1323480 1987751 := bstep (se 1 (by rfl) ⟨1490813, by rfl⟩ : syracuseStep 1987751 = 2981627) B2981627
theorem B1987775 : Blo 1323480 1987775 := bstep (se 1 (by rfl) ⟨1490831, by rfl⟩ : syracuseStep 1987775 = 2981663) B2981663
theorem B15078635 : Blo 1323480 15078635 := bstep (se 1 (by rfl) ⟨11308976, by rfl⟩ : syracuseStep 15078635 = 22617953) B22617953
theorem B2979143 : Blo 1323480 2979143 := bstep (se 1 (by rfl) ⟨2234357, by rfl⟩ : syracuseStep 2979143 = 4468715) B4468715
theorem B1988075 : Blo 1323480 1988075 := bstep (se 1 (by rfl) ⟨1491056, by rfl⟩ : syracuseStep 1988075 = 2982113) B2982113
theorem B1988123 : Blo 1323480 1988123 := bstep (se 1 (by rfl) ⟨1491092, by rfl⟩ : syracuseStep 1988123 = 2982185) B2982185
theorem B1324591 : Blo 1323480 1324591 := bstep (se 1 (by rfl) ⟨993443, by rfl⟩ : syracuseStep 1324591 = 1986887) B1986887
theorem B1988159 : Blo 1323480 1988159 := bstep (se 1 (by rfl) ⟨1491119, by rfl⟩ : syracuseStep 1988159 = 2982239) B2982239
theorem B13588073 : Blo 1323480 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B1325295 : Blo 1323480 1325295 := bstep (se 1 (by rfl) ⟨993971, by rfl⟩ : syracuseStep 1325295 = 1987943) B1987943
theorem B1325375 : Blo 1323480 1325375 := bstep (se 1 (by rfl) ⟨994031, by rfl⟩ : syracuseStep 1325375 = 1988063) B1988063
theorem B2980745 : Blo 1323480 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B4242431 : Blo 1323480 4242431 := bstep (se 1 (by rfl) ⟨3181823, by rfl⟩ : syracuseStep 4242431 = 6363647) B6363647
theorem B2235775 : Blo 1323480 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B7544603 : Blo 1323480 7544603 := bstep (se 1 (by rfl) ⟨5658452, by rfl⟩ : syracuseStep 7544603 = 11316905) B11316905
theorem B4472819 : Blo 1323480 4472819 := bstep (se 1 (by rfl) ⟨3354614, by rfl⟩ : syracuseStep 4472819 = 6709229) B6709229
theorem B2981951 : Blo 1323480 2981951 := bstep (se 1 (by rfl) ⟨2236463, by rfl⟩ : syracuseStep 2981951 = 4472927) B4472927
theorem B10052423 : Blo 1323480 10052423 := bstep (se 1 (by rfl) ⟨7539317, by rfl⟩ : syracuseStep 10052423 = 15078635) B15078635
theorem B11322341 : Blo 1323480 11322341 := bstep (se 4 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 11322341 = 2122939) B2122939
theorem B5654063 : Blo 1323480 5654063 := bstep (se 1 (by rfl) ⟨4240547, by rfl⟩ : syracuseStep 5654063 = 8481095) B8481095
theorem B2828287 : Blo 1323480 2828287 := bstep (se 1 (by rfl) ⟨2121215, by rfl⟩ : syracuseStep 2828287 = 4242431) B4242431
theorem B3770707 : Blo 1323480 3770707 := bstep (se 1 (by rfl) ⟨2828030, by rfl⟩ : syracuseStep 3770707 = 5656061) B5656061
theorem B2981879 : Blo 1323480 2981879 := bstep (se 1 (by rfl) ⟨2236409, by rfl⟩ : syracuseStep 2981879 = 4472819) B4472819
theorem B9186301 : Blo 1323480 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B19098661 : Blo 1323480 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B2829671 : Blo 1323480 2829671 := bstep (se 1 (by rfl) ⟨2122253, by rfl⟩ : syracuseStep 2829671 = 4244507) B4244507
theorem B1986095 : Blo 1323480 1986095 := bstep (se 1 (by rfl) ⟨1489571, by rfl⟩ : syracuseStep 1986095 = 2979143) B2979143
theorem B10055339 : Blo 1323480 10055339 := bstep (se 1 (by rfl) ⟨7541504, by rfl⟩ : syracuseStep 10055339 = 15083009) B15083009
theorem B25472879 : Blo 1323480 25472879 := bstep (se 1 (by rfl) ⟨19104659, by rfl⟩ : syracuseStep 25472879 = 38209319) B38209319
theorem B2977847 : Blo 1323480 2977847 := bstep (se 1 (by rfl) ⟨2233385, by rfl⟩ : syracuseStep 2977847 = 4466771) B4466771
theorem B1987163 : Blo 1323480 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B1323647 : Blo 1323480 1323647 := bstep (se 1 (by rfl) ⟨992735, by rfl⟩ : syracuseStep 1323647 = 1985471) B1985471
theorem B2978459 : Blo 1323480 2978459 := bstep (se 1 (by rfl) ⟨2233844, by rfl⟩ : syracuseStep 2978459 = 4467689) B4467689
theorem B1323679 : Blo 1323480 1323679 := bstep (se 1 (by rfl) ⟨992759, by rfl⟩ : syracuseStep 1323679 = 1985519) B1985519
theorem B1324031 : Blo 1323480 1324031 := bstep (se 1 (by rfl) ⟨993023, by rfl⟩ : syracuseStep 1324031 = 1986047) B1986047
theorem B22639823 : Blo 1323480 22639823 := bstep (se 1 (by rfl) ⟨16979867, by rfl⟩ : syracuseStep 22639823 = 33959735) B33959735
theorem B4470173 : Blo 1323480 4470173 := bstep (se 3 (by rfl) ⟨838157, by rfl⟩ : syracuseStep 4470173 = 1676315) B1676315
theorem B1324479 : Blo 1323480 1324479 := bstep (se 1 (by rfl) ⟨993359, by rfl⟩ : syracuseStep 1324479 = 1986719) B1986719
theorem B6796831 : Blo 1323480 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B2979611 : Blo 1323480 2979611 := bstep (se 1 (by rfl) ⟨2234708, by rfl⟩ : syracuseStep 2979611 = 4469417) B4469417
theorem B2512795 : Blo 1323480 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B1324967 : Blo 1323480 1324967 := bstep (se 1 (by rfl) ⟨993725, by rfl⟩ : syracuseStep 1324967 = 1987451) B1987451
theorem B1325167 : Blo 1323480 1325167 := bstep (se 1 (by rfl) ⟨993875, by rfl⟩ : syracuseStep 1325167 = 1987751) B1987751
theorem B1325183 : Blo 1323480 1325183 := bstep (se 1 (by rfl) ⟨993887, by rfl⟩ : syracuseStep 1325183 = 1987775) B1987775
theorem B1325383 : Blo 1323480 1325383 := bstep (se 1 (by rfl) ⟨994037, by rfl⟩ : syracuseStep 1325383 = 1988075) B1988075
theorem B1325415 : Blo 1323480 1325415 := bstep (se 1 (by rfl) ⟨994061, by rfl⟩ : syracuseStep 1325415 = 1988123) B1988123
theorem B1325439 : Blo 1323480 1325439 := bstep (se 1 (by rfl) ⟨994079, by rfl⟩ : syracuseStep 1325439 = 1988159) B1988159
theorem B9058715 : Blo 1323480 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B2981033 : Blo 1323480 2981033 := bstep (se 2 (by rfl) ⟨1117887, by rfl⟩ : syracuseStep 2981033 = 2235775) B2235775
theorem B2235647 : Blo 1323480 2235647 := bstep (se 1 (by rfl) ⟨1676735, by rfl⟩ : syracuseStep 2235647 = 3353471) B3353471
theorem B3022127 : Blo 1323480 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2121151 : Blo 1323480 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B2236187 : Blo 1323480 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B5029735 : Blo 1323480 5029735 := bstep (se 1 (by rfl) ⟨3772301, by rfl⟩ : syracuseStep 5029735 = 7544603) B7544603
theorem B6701615 : Blo 1323480 6701615 := bstep (se 1 (by rfl) ⟨5026211, by rfl⟩ : syracuseStep 6701615 = 10052423) B10052423
theorem B3769375 : Blo 1323480 3769375 := bstep (se 1 (by rfl) ⟨2827031, by rfl⟩ : syracuseStep 3769375 = 5654063) B5654063
theorem B12248401 : Blo 1323480 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B6039143 : Blo 1323480 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B2828201 : Blo 1323480 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B9062441 : Blo 1323480 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1886447 : Blo 1323480 1886447 := bstep (se 1 (by rfl) ⟨1414835, by rfl⟩ : syracuseStep 1886447 = 2829671) B2829671
theorem B6703559 : Blo 1323480 6703559 := bstep (se 1 (by rfl) ⟨5027669, by rfl⟩ : syracuseStep 6703559 = 10055339) B10055339
theorem B3771049 : Blo 1323480 3771049 := bstep (se 2 (by rfl) ⟨1414143, by rfl⟩ : syracuseStep 3771049 = 2828287) B2828287
theorem B1985231 : Blo 1323480 1985231 := bstep (se 1 (by rfl) ⟨1488923, by rfl⟩ : syracuseStep 1985231 = 2977847) B2977847
theorem B1985639 : Blo 1323480 1985639 := bstep (se 1 (by rfl) ⟨1489229, by rfl⟩ : syracuseStep 1985639 = 2978459) B2978459
theorem B7548227 : Blo 1323480 7548227 := bstep (se 1 (by rfl) ⟨5661170, by rfl⟩ : syracuseStep 7548227 = 11322341) B11322341
theorem B15093215 : Blo 1323480 15093215 := bstep (se 1 (by rfl) ⟨11319911, by rfl⟩ : syracuseStep 15093215 = 22639823) B22639823
theorem B1986407 : Blo 1323480 1986407 := bstep (se 1 (by rfl) ⟨1489805, by rfl⟩ : syracuseStep 1986407 = 2979611) B2979611
theorem B25464881 : Blo 1323480 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1987355 : Blo 1323480 1987355 := bstep (se 1 (by rfl) ⟨1490516, by rfl⟩ : syracuseStep 1987355 = 2981033) B2981033
theorem B1324063 : Blo 1323480 1324063 := bstep (se 1 (by rfl) ⟨993047, by rfl⟩ : syracuseStep 1324063 = 1986095) B1986095
theorem B6706313 : Blo 1323480 6706313 := bstep (se 2 (by rfl) ⟨2514867, by rfl⟩ : syracuseStep 6706313 = 5029735) B5029735
theorem B1987919 : Blo 1323480 1987919 := bstep (se 1 (by rfl) ⟨1490939, by rfl⟩ : syracuseStep 1987919 = 2981879) B2981879
theorem B1987967 : Blo 1323480 1987967 := bstep (se 1 (by rfl) ⟨1490975, by rfl⟩ : syracuseStep 1987967 = 2981951) B2981951
theorem B1324775 : Blo 1323480 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B5027609 : Blo 1323480 5027609 := bstep (se 2 (by rfl) ⟨1885353, by rfl⟩ : syracuseStep 5027609 = 3770707) B3770707
theorem B2980115 : Blo 1323480 2980115 := bstep (se 1 (by rfl) ⟨2235086, by rfl⟩ : syracuseStep 2980115 = 4470173) B4470173
theorem B1490431 : Blo 1323480 1490431 := bstep (se 1 (by rfl) ⟨1117823, by rfl⟩ : syracuseStep 1490431 = 2235647) B2235647
theorem B2014751 : Blo 1323480 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B1490791 : Blo 1323480 1490791 := bstep (se 1 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 1490791 = 2236187) B2236187
theorem B3350393 : Blo 1323480 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B16981919 : Blo 1323480 16981919 := bstep (se 1 (by rfl) ⟨12736439, by rfl⟩ : syracuseStep 16981919 = 25472879) B25472879
theorem B5030525 : Blo 1323480 5030525 := bstep (se 3 (by rfl) ⟨943223, by rfl⟩ : syracuseStep 5030525 = 1886447) B1886447
theorem B3351739 : Blo 1323480 3351739 := bstep (se 1 (by rfl) ⟨2513804, by rfl⟩ : syracuseStep 3351739 = 5027609) B5027609
theorem B5032151 : Blo 1323480 5032151 := bstep (se 1 (by rfl) ⟨3774113, by rfl⟩ : syracuseStep 5032151 = 7548227) B7548227
theorem B10062143 : Blo 1323480 10062143 := bstep (se 1 (by rfl) ⟨7546607, by rfl⟩ : syracuseStep 10062143 = 15093215) B15093215
theorem B16976587 : Blo 1323480 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B4467743 : Blo 1323480 4467743 := bstep (se 1 (by rfl) ⟨3350807, by rfl⟩ : syracuseStep 4467743 = 6701615) B6701615
theorem B4026095 : Blo 1323480 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B6041627 : Blo 1323480 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B5025833 : Blo 1323480 5025833 := bstep (se 2 (by rfl) ⟨1884687, by rfl⟩ : syracuseStep 5025833 = 3769375) B3769375
theorem B1986743 : Blo 1323480 1986743 := bstep (se 1 (by rfl) ⟨1490057, by rfl⟩ : syracuseStep 1986743 = 2980115) B2980115
theorem B4469039 : Blo 1323480 4469039 := bstep (se 1 (by rfl) ⟨3351779, by rfl⟩ : syracuseStep 4469039 = 6703559) B6703559
theorem B16331201 : Blo 1323480 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B1323487 : Blo 1323480 1323487 := bstep (se 1 (by rfl) ⟨992615, by rfl⟩ : syracuseStep 1323487 = 1985231) B1985231
theorem B1987241 : Blo 1323480 1987241 := bstep (se 2 (by rfl) ⟨745215, by rfl⟩ : syracuseStep 1987241 = 1490431) B1490431
theorem B1323759 : Blo 1323480 1323759 := bstep (se 1 (by rfl) ⟨992819, by rfl⟩ : syracuseStep 1323759 = 1985639) B1985639
theorem B7541869 : Blo 1323480 7541869 := bstep (se 3 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 7541869 = 2828201) B2828201
theorem B1987721 : Blo 1323480 1987721 := bstep (se 2 (by rfl) ⟨745395, by rfl⟩ : syracuseStep 1987721 = 1490791) B1490791
theorem B1324271 : Blo 1323480 1324271 := bstep (se 1 (by rfl) ⟨993203, by rfl⟩ : syracuseStep 1324271 = 1986407) B1986407
theorem B2233595 : Blo 1323480 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B1324903 : Blo 1323480 1324903 := bstep (se 1 (by rfl) ⟨993677, by rfl⟩ : syracuseStep 1324903 = 1987355) B1987355
theorem B4470875 : Blo 1323480 4470875 := bstep (se 1 (by rfl) ⟨3353156, by rfl⟩ : syracuseStep 4470875 = 6706313) B6706313
theorem B1325279 : Blo 1323480 1325279 := bstep (se 1 (by rfl) ⟨993959, by rfl⟩ : syracuseStep 1325279 = 1987919) B1987919
theorem B5028065 : Blo 1323480 5028065 := bstep (se 2 (by rfl) ⟨1885524, by rfl⟩ : syracuseStep 5028065 = 3771049) B3771049
theorem B1325311 : Blo 1323480 1325311 := bstep (se 1 (by rfl) ⟨993983, by rfl⟩ : syracuseStep 1325311 = 1987967) B1987967
theorem B5372669 : Blo 1323480 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B11321279 : Blo 1323480 11321279 := bstep (se 1 (by rfl) ⟨8490959, by rfl⟩ : syracuseStep 11321279 = 16981919) B16981919
theorem B3350555 : Blo 1323480 3350555 := bstep (se 1 (by rfl) ⟨2512916, by rfl⟩ : syracuseStep 3350555 = 5025833) B5025833
theorem B10887467 : Blo 1323480 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B22635449 : Blo 1323480 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B3352043 : Blo 1323480 3352043 := bstep (se 1 (by rfl) ⟨2514032, by rfl⟩ : syracuseStep 3352043 = 5028065) B5028065
theorem B3581779 : Blo 1323480 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B7547519 : Blo 1323480 7547519 := bstep (se 1 (by rfl) ⟨5660639, by rfl⟩ : syracuseStep 7547519 = 11321279) B11321279
theorem B3353683 : Blo 1323480 3353683 := bstep (se 1 (by rfl) ⟨2515262, by rfl⟩ : syracuseStep 3353683 = 5030525) B5030525
theorem B3354767 : Blo 1323480 3354767 := bstep (se 1 (by rfl) ⟨2516075, by rfl⟩ : syracuseStep 3354767 = 5032151) B5032151
theorem B10055825 : Blo 1323480 10055825 := bstep (se 2 (by rfl) ⟨3770934, by rfl⟩ : syracuseStep 10055825 = 7541869) B7541869
theorem B4468985 : Blo 1323480 4468985 := bstep (se 2 (by rfl) ⟨1675869, by rfl⟩ : syracuseStep 4468985 = 3351739) B3351739
theorem B2978495 : Blo 1323480 2978495 := bstep (se 1 (by rfl) ⟨2233871, by rfl⟩ : syracuseStep 2978495 = 4467743) B4467743
theorem B2684063 : Blo 1323480 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B4027751 : Blo 1323480 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B1324495 : Blo 1323480 1324495 := bstep (se 1 (by rfl) ⟨993371, by rfl⟩ : syracuseStep 1324495 = 1986743) B1986743
theorem B2979359 : Blo 1323480 2979359 := bstep (se 1 (by rfl) ⟨2234519, by rfl⟩ : syracuseStep 2979359 = 4469039) B4469039
theorem B1324827 : Blo 1323480 1324827 := bstep (se 1 (by rfl) ⟨993620, by rfl⟩ : syracuseStep 1324827 = 1987241) B1987241
theorem B1325147 : Blo 1323480 1325147 := bstep (se 1 (by rfl) ⟨993860, by rfl⟩ : syracuseStep 1325147 = 1987721) B1987721
theorem B1489063 : Blo 1323480 1489063 := bstep (se 1 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 1489063 = 2233595) B2233595
theorem B2980583 : Blo 1323480 2980583 := bstep (se 1 (by rfl) ⟨2235437, by rfl⟩ : syracuseStep 2980583 = 4470875) B4470875
theorem B6708095 : Blo 1323480 6708095 := bstep (se 1 (by rfl) ⟨5031071, by rfl⟩ : syracuseStep 6708095 = 10062143) B10062143
theorem B2236511 : Blo 1323480 2236511 := bstep (se 1 (by rfl) ⟨1677383, by rfl⟩ : syracuseStep 2236511 = 3354767) B3354767
theorem B15090299 : Blo 1323480 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B29033245 : Blo 1323480 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B5031679 : Blo 1323480 5031679 := bstep (se 1 (by rfl) ⟨3773759, by rfl⟩ : syracuseStep 5031679 = 7547519) B7547519
theorem B6703883 : Blo 1323480 6703883 := bstep (se 1 (by rfl) ⟨5027912, by rfl⟩ : syracuseStep 6703883 = 10055825) B10055825
theorem B1985417 : Blo 1323480 1985417 := bstep (se 2 (by rfl) ⟨744531, by rfl⟩ : syracuseStep 1985417 = 1489063) B1489063
theorem B1985663 : Blo 1323480 1985663 := bstep (se 1 (by rfl) ⟨1489247, by rfl⟩ : syracuseStep 1985663 = 2978495) B2978495
theorem B1986239 : Blo 1323480 1986239 := bstep (se 1 (by rfl) ⟨1489679, by rfl⟩ : syracuseStep 1986239 = 2979359) B2979359
theorem B1987055 : Blo 1323480 1987055 := bstep (se 1 (by rfl) ⟨1490291, by rfl⟩ : syracuseStep 1987055 = 2980583) B2980583
theorem B2233703 : Blo 1323480 2233703 := bstep (se 1 (by rfl) ⟨1675277, by rfl⟩ : syracuseStep 2233703 = 3350555) B3350555
theorem B2979323 : Blo 1323480 2979323 := bstep (se 1 (by rfl) ⟨2234492, by rfl⟩ : syracuseStep 2979323 = 4468985) B4468985
theorem B7157501 : Blo 1323480 7157501 := bstep (se 3 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 7157501 = 2684063) B2684063
theorem B2685167 : Blo 1323480 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B2234695 : Blo 1323480 2234695 := bstep (se 1 (by rfl) ⟨1676021, by rfl⟩ : syracuseStep 2234695 = 3352043) B3352043
theorem B4471577 : Blo 1323480 4471577 := bstep (se 2 (by rfl) ⟨1676841, by rfl⟩ : syracuseStep 4471577 = 3353683) B3353683
theorem B4472063 : Blo 1323480 4472063 := bstep (se 1 (by rfl) ⟨3354047, by rfl⟩ : syracuseStep 4472063 = 6708095) B6708095
theorem B4775705 : Blo 1323480 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B1491007 : Blo 1323480 1491007 := bstep (se 1 (by rfl) ⟨1118255, by rfl⟩ : syracuseStep 1491007 = 2236511) B2236511
theorem B10060199 : Blo 1323480 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B1986215 : Blo 1323480 1986215 := bstep (se 1 (by rfl) ⟨1489661, by rfl⟩ : syracuseStep 1986215 = 2979323) B2979323
theorem B38710993 : Blo 1323480 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B4771667 : Blo 1323480 4771667 := bstep (se 1 (by rfl) ⟨3578750, by rfl⟩ : syracuseStep 4771667 = 7157501) B7157501
theorem B1790111 : Blo 1323480 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B4469255 : Blo 1323480 4469255 := bstep (se 1 (by rfl) ⟨3351941, by rfl⟩ : syracuseStep 4469255 = 6703883) B6703883
theorem B1323611 : Blo 1323480 1323611 := bstep (se 1 (by rfl) ⟨992708, by rfl⟩ : syracuseStep 1323611 = 1985417) B1985417
theorem B1323775 : Blo 1323480 1323775 := bstep (se 1 (by rfl) ⟨992831, by rfl⟩ : syracuseStep 1323775 = 1985663) B1985663
theorem B1324159 : Blo 1323480 1324159 := bstep (se 1 (by rfl) ⟨993119, by rfl⟩ : syracuseStep 1324159 = 1986239) B1986239
theorem B3183803 : Blo 1323480 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B1324703 : Blo 1323480 1324703 := bstep (se 1 (by rfl) ⟨993527, by rfl⟩ : syracuseStep 1324703 = 1987055) B1987055
theorem B2979593 : Blo 1323480 2979593 := bstep (se 2 (by rfl) ⟨1117347, by rfl⟩ : syracuseStep 2979593 = 2234695) B2234695
theorem B1489135 : Blo 1323480 1489135 := bstep (se 1 (by rfl) ⟨1116851, by rfl⟩ : syracuseStep 1489135 = 2233703) B2233703
theorem B2981051 : Blo 1323480 2981051 := bstep (se 1 (by rfl) ⟨2235788, by rfl⟩ : syracuseStep 2981051 = 4471577) B4471577
theorem B2981375 : Blo 1323480 2981375 := bstep (se 1 (by rfl) ⟨2236031, by rfl⟩ : syracuseStep 2981375 = 4472063) B4472063
theorem B6708905 : Blo 1323480 6708905 := bstep (se 2 (by rfl) ⟨2515839, by rfl⟩ : syracuseStep 6708905 = 5031679) B5031679
theorem B2122535 : Blo 1323480 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B12724445 : Blo 1323480 12724445 := bstep (se 3 (by rfl) ⟨2385833, by rfl⟩ : syracuseStep 12724445 = 4771667) B4771667
theorem B1985513 : Blo 1323480 1985513 := bstep (se 2 (by rfl) ⟨744567, by rfl⟩ : syracuseStep 1985513 = 1489135) B1489135
theorem B1986395 : Blo 1323480 1986395 := bstep (se 1 (by rfl) ⟨1489796, by rfl⟩ : syracuseStep 1986395 = 2979593) B2979593
theorem B1987367 : Blo 1323480 1987367 := bstep (se 1 (by rfl) ⟨1490525, by rfl⟩ : syracuseStep 1987367 = 2981051) B2981051
theorem B51614657 : Blo 1323480 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B1987583 : Blo 1323480 1987583 := bstep (se 1 (by rfl) ⟨1490687, by rfl⟩ : syracuseStep 1987583 = 2981375) B2981375
theorem B1324143 : Blo 1323480 1324143 := bstep (se 1 (by rfl) ⟨993107, by rfl⟩ : syracuseStep 1324143 = 1986215) B1986215
theorem B1988009 : Blo 1323480 1988009 := bstep (se 2 (by rfl) ⟨745503, by rfl⟩ : syracuseStep 1988009 = 1491007) B1491007
theorem B6706799 : Blo 1323480 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B2979503 : Blo 1323480 2979503 := bstep (se 1 (by rfl) ⟨2234627, by rfl⟩ : syracuseStep 2979503 = 4469255) B4469255
theorem B4773629 : Blo 1323480 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B4472603 : Blo 1323480 4472603 := bstep (se 1 (by rfl) ⟨3354452, by rfl⟩ : syracuseStep 4472603 = 6708905) B6708905
theorem B34409771 : Blo 1323480 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B1986335 : Blo 1323480 1986335 := bstep (se 1 (by rfl) ⟨1489751, by rfl⟩ : syracuseStep 1986335 = 2979503) B2979503
theorem B3182419 : Blo 1323480 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B8482963 : Blo 1323480 8482963 := bstep (se 1 (by rfl) ⟨6362222, by rfl⟩ : syracuseStep 8482963 = 12724445) B12724445
theorem B1323675 : Blo 1323480 1323675 := bstep (se 1 (by rfl) ⟨992756, by rfl⟩ : syracuseStep 1323675 = 1985513) B1985513
theorem B1324263 : Blo 1323480 1324263 := bstep (se 1 (by rfl) ⟨993197, by rfl⟩ : syracuseStep 1324263 = 1986395) B1986395
theorem B1324911 : Blo 1323480 1324911 := bstep (se 1 (by rfl) ⟨993683, by rfl⟩ : syracuseStep 1324911 = 1987367) B1987367
theorem B1325055 : Blo 1323480 1325055 := bstep (se 1 (by rfl) ⟨993791, by rfl⟩ : syracuseStep 1325055 = 1987583) B1987583
theorem B1325339 : Blo 1323480 1325339 := bstep (se 1 (by rfl) ⟨994004, by rfl⟩ : syracuseStep 1325339 = 1988009) B1988009
theorem B4471199 : Blo 1323480 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B5660093 : Blo 1323480 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B2981735 : Blo 1323480 2981735 := bstep (se 1 (by rfl) ⟨2236301, by rfl⟩ : syracuseStep 2981735 = 4472603) B4472603
theorem B22939847 : Blo 1323480 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B3773395 : Blo 1323480 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B1324223 : Blo 1323480 1324223 := bstep (se 1 (by rfl) ⟨993167, by rfl⟩ : syracuseStep 1324223 = 1986335) B1986335
theorem B1987823 : Blo 1323480 1987823 := bstep (se 1 (by rfl) ⟨1490867, by rfl⟩ : syracuseStep 1987823 = 2981735) B2981735
theorem B11310617 : Blo 1323480 11310617 := bstep (se 2 (by rfl) ⟨4241481, by rfl⟩ : syracuseStep 11310617 = 8482963) B8482963
theorem B2980799 : Blo 1323480 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B4243225 : Blo 1323480 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B5031193 : Blo 1323480 5031193 := bstep (se 2 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 5031193 = 3773395) B3773395
theorem B7540411 : Blo 1323480 7540411 := bstep (se 1 (by rfl) ⟨5655308, by rfl⟩ : syracuseStep 7540411 = 11310617) B11310617
theorem B1987199 : Blo 1323480 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B5657633 : Blo 1323480 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B1325215 : Blo 1323480 1325215 := bstep (se 1 (by rfl) ⟨993911, by rfl⟩ : syracuseStep 1325215 = 1987823) B1987823
theorem B15293231 : Blo 1323480 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B10053881 : Blo 1323480 10053881 := bstep (se 2 (by rfl) ⟨3770205, by rfl⟩ : syracuseStep 10053881 = 7540411) B7540411
theorem B3771755 : Blo 1323480 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B10195487 : Blo 1323480 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B1324799 : Blo 1323480 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B6708257 : Blo 1323480 6708257 := bstep (se 2 (by rfl) ⟨2515596, by rfl⟩ : syracuseStep 6708257 = 5031193) B5031193
theorem B6702587 : Blo 1323480 6702587 := bstep (se 1 (by rfl) ⟨5026940, by rfl⟩ : syracuseStep 6702587 = 10053881) B10053881
theorem B6796991 : Blo 1323480 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B4472171 : Blo 1323480 4472171 := bstep (se 1 (by rfl) ⟨3354128, by rfl⟩ : syracuseStep 4472171 = 6708257) B6708257
theorem B2514503 : Blo 1323480 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B4468391 : Blo 1323480 4468391 := bstep (se 1 (by rfl) ⟨3351293, by rfl⟩ : syracuseStep 4468391 = 6702587) B6702587
theorem B6705341 : Blo 1323480 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B18125309 : Blo 1323480 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B2981447 : Blo 1323480 2981447 := bstep (se 1 (by rfl) ⟨2236085, by rfl⟩ : syracuseStep 2981447 = 4472171) B4472171
theorem B12083539 : Blo 1323480 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B1987631 : Blo 1323480 1987631 := bstep (se 1 (by rfl) ⟨1490723, by rfl⟩ : syracuseStep 1987631 = 2981447) B2981447
theorem B2978927 : Blo 1323480 2978927 := bstep (se 1 (by rfl) ⟨2234195, by rfl⟩ : syracuseStep 2978927 = 4468391) B4468391
theorem B4470227 : Blo 1323480 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B1985951 : Blo 1323480 1985951 := bstep (se 1 (by rfl) ⟨1489463, by rfl⟩ : syracuseStep 1985951 = 2978927) B2978927
theorem B16111385 : Blo 1323480 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B1325087 : Blo 1323480 1325087 := bstep (se 1 (by rfl) ⟨993815, by rfl⟩ : syracuseStep 1325087 = 1987631) B1987631
theorem B2980151 : Blo 1323480 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B10740923 : Blo 1323480 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B1986767 : Blo 1323480 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B1323967 : Blo 1323480 1323967 := bstep (se 1 (by rfl) ⟨992975, by rfl⟩ : syracuseStep 1323967 = 1985951) B1985951
theorem B7160615 : Blo 1323480 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B1324511 : Blo 1323480 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B4773743 : Blo 1323480 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B3182495 : Blo 1323480 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B33946613 : Blo 1323480 33946613 := bstep (se 5 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 33946613 = 3182495) B3182495
theorem B22631075 : Blo 1323480 22631075 := bstep (se 1 (by rfl) ⟨16973306, by rfl⟩ : syracuseStep 22631075 = 33946613) B33946613
theorem B15087383 : Blo 1323480 15087383 := bstep (se 1 (by rfl) ⟨11315537, by rfl⟩ : syracuseStep 15087383 = 22631075) B22631075
theorem B10058255 : Blo 1323480 10058255 := bstep (se 1 (by rfl) ⟨7543691, by rfl⟩ : syracuseStep 10058255 = 15087383) B15087383
theorem B6705503 : Blo 1323480 6705503 := bstep (se 1 (by rfl) ⟨5029127, by rfl⟩ : syracuseStep 6705503 = 10058255) B10058255
theorem B4470335 : Blo 1323480 4470335 := bstep (se 1 (by rfl) ⟨3352751, by rfl⟩ : syracuseStep 4470335 = 6705503) B6705503
theorem B2980223 : Blo 1323480 2980223 := bstep (se 1 (by rfl) ⟨2235167, by rfl⟩ : syracuseStep 2980223 = 4470335) B4470335
theorem B1986815 : Blo 1323480 1986815 := bstep (se 1 (by rfl) ⟨1490111, by rfl⟩ : syracuseStep 1986815 = 2980223) B2980223
theorem B1324543 : Blo 1323480 1324543 := bstep (se 1 (by rfl) ⟨993407, by rfl⟩ : syracuseStep 1324543 = 1986815) B1986815

theorem C0 (j : ℕ) (h1 : 330870 ≤ j) (h2 : j ≤ 331369) : Blo 1323480 (4 * j + 3) := by
  interval_cases j
  · exact B1323483
  · exact B1323487
  · exact B1323491
  · exact B1323495
  · exact B1323499
  · exact B1323503
  · exact B1323507
  · exact B1323511
  · exact B1323515
  · exact B1323519
  · exact B1323523
  · exact B1323527
  · exact B1323531
  · exact B1323535
  · exact B1323539
  · exact B1323543
  · exact B1323547
  · exact B1323551
  · exact B1323555
  · exact B1323559
  · exact B1323563
  · exact B1323567
  · exact B1323571
  · exact B1323575
  · exact B1323579
  · exact B1323583
  · exact B1323587
  · exact B1323591
  · exact B1323595
  · exact B1323599
  · exact B1323603
  · exact B1323607
  · exact B1323611
  · exact B1323615
  · exact B1323619
  · exact B1323623
  · exact B1323627
  · exact B1323631
  · exact B1323635
  · exact B1323639
  · exact B1323643
  · exact B1323647
  · exact B1323651
  · exact B1323655
  · exact B1323659
  · exact B1323663
  · exact B1323667
  · exact B1323671
  · exact B1323675
  · exact B1323679
  · exact B1323683
  · exact B1323687
  · exact B1323691
  · exact B1323695
  · exact B1323699
  · exact B1323703
  · exact B1323707
  · exact B1323711
  · exact B1323715
  · exact B1323719
  · exact B1323723
  · exact B1323727
  · exact B1323731
  · exact B1323735
  · exact B1323739
  · exact B1323743
  · exact B1323747
  · exact B1323751
  · exact B1323755
  · exact B1323759
  · exact B1323763
  · exact B1323767
  · exact B1323771
  · exact B1323775
  · exact B1323779
  · exact B1323783
  · exact B1323787
  · exact B1323791
  · exact B1323795
  · exact B1323799
  · exact B1323803
  · exact B1323807
  · exact B1323811
  · exact B1323815
  · exact B1323819
  · exact B1323823
  · exact B1323827
  · exact B1323831
  · exact B1323835
  · exact B1323839
  · exact B1323843
  · exact B1323847
  · exact B1323851
  · exact B1323855
  · exact B1323859
  · exact B1323863
  · exact B1323867
  · exact B1323871
  · exact B1323875
  · exact B1323879
  · exact B1323883
  · exact B1323887
  · exact B1323891
  · exact B1323895
  · exact B1323899
  · exact B1323903
  · exact B1323907
  · exact B1323911
  · exact B1323915
  · exact B1323919
  · exact B1323923
  · exact B1323927
  · exact B1323931
  · exact B1323935
  · exact B1323939
  · exact B1323943
  · exact B1323947
  · exact B1323951
  · exact B1323955
  · exact B1323959
  · exact B1323963
  · exact B1323967
  · exact B1323971
  · exact B1323975
  · exact B1323979
  · exact B1323983
  · exact B1323987
  · exact B1323991
  · exact B1323995
  · exact B1323999
  · exact B1324003
  · exact B1324007
  · exact B1324011
  · exact B1324015
  · exact B1324019
  · exact B1324023
  · exact B1324027
  · exact B1324031
  · exact B1324035
  · exact B1324039
  · exact B1324043
  · exact B1324047
  · exact B1324051
  · exact B1324055
  · exact B1324059
  · exact B1324063
  · exact B1324067
  · exact B1324071
  · exact B1324075
  · exact B1324079
  · exact B1324083
  · exact B1324087
  · exact B1324091
  · exact B1324095
  · exact B1324099
  · exact B1324103
  · exact B1324107
  · exact B1324111
  · exact B1324115
  · exact B1324119
  · exact B1324123
  · exact B1324127
  · exact B1324131
  · exact B1324135
  · exact B1324139
  · exact B1324143
  · exact B1324147
  · exact B1324151
  · exact B1324155
  · exact B1324159
  · exact B1324163
  · exact B1324167
  · exact B1324171
  · exact B1324175
  · exact B1324179
  · exact B1324183
  · exact B1324187
  · exact B1324191
  · exact B1324195
  · exact B1324199
  · exact B1324203
  · exact B1324207
  · exact B1324211
  · exact B1324215
  · exact B1324219
  · exact B1324223
  · exact B1324227
  · exact B1324231
  · exact B1324235
  · exact B1324239
  · exact B1324243
  · exact B1324247
  · exact B1324251
  · exact B1324255
  · exact B1324259
  · exact B1324263
  · exact B1324267
  · exact B1324271
  · exact B1324275
  · exact B1324279
  · exact B1324283
  · exact B1324287
  · exact B1324291
  · exact B1324295
  · exact B1324299
  · exact B1324303
  · exact B1324307
  · exact B1324311
  · exact B1324315
  · exact B1324319
  · exact B1324323
  · exact B1324327
  · exact B1324331
  · exact B1324335
  · exact B1324339
  · exact B1324343
  · exact B1324347
  · exact B1324351
  · exact B1324355
  · exact B1324359
  · exact B1324363
  · exact B1324367
  · exact B1324371
  · exact B1324375
  · exact B1324379
  · exact B1324383
  · exact B1324387
  · exact B1324391
  · exact B1324395
  · exact B1324399
  · exact B1324403
  · exact B1324407
  · exact B1324411
  · exact B1324415
  · exact B1324419
  · exact B1324423
  · exact B1324427
  · exact B1324431
  · exact B1324435
  · exact B1324439
  · exact B1324443
  · exact B1324447
  · exact B1324451
  · exact B1324455
  · exact B1324459
  · exact B1324463
  · exact B1324467
  · exact B1324471
  · exact B1324475
  · exact B1324479
  · exact B1324483
  · exact B1324487
  · exact B1324491
  · exact B1324495
  · exact B1324499
  · exact B1324503
  · exact B1324507
  · exact B1324511
  · exact B1324515
  · exact B1324519
  · exact B1324523
  · exact B1324527
  · exact B1324531
  · exact B1324535
  · exact B1324539
  · exact B1324543
  · exact B1324547
  · exact B1324551
  · exact B1324555
  · exact B1324559
  · exact B1324563
  · exact B1324567
  · exact B1324571
  · exact B1324575
  · exact B1324579
  · exact B1324583
  · exact B1324587
  · exact B1324591
  · exact B1324595
  · exact B1324599
  · exact B1324603
  · exact B1324607
  · exact B1324611
  · exact B1324615
  · exact B1324619
  · exact B1324623
  · exact B1324627
  · exact B1324631
  · exact B1324635
  · exact B1324639
  · exact B1324643
  · exact B1324647
  · exact B1324651
  · exact B1324655
  · exact B1324659
  · exact B1324663
  · exact B1324667
  · exact B1324671
  · exact B1324675
  · exact B1324679
  · exact B1324683
  · exact B1324687
  · exact B1324691
  · exact B1324695
  · exact B1324699
  · exact B1324703
  · exact B1324707
  · exact B1324711
  · exact B1324715
  · exact B1324719
  · exact B1324723
  · exact B1324727
  · exact B1324731
  · exact B1324735
  · exact B1324739
  · exact B1324743
  · exact B1324747
  · exact B1324751
  · exact B1324755
  · exact B1324759
  · exact B1324763
  · exact B1324767
  · exact B1324771
  · exact B1324775
  · exact B1324779
  · exact B1324783
  · exact B1324787
  · exact B1324791
  · exact B1324795
  · exact B1324799
  · exact B1324803
  · exact B1324807
  · exact B1324811
  · exact B1324815
  · exact B1324819
  · exact B1324823
  · exact B1324827
  · exact B1324831
  · exact B1324835
  · exact B1324839
  · exact B1324843
  · exact B1324847
  · exact B1324851
  · exact B1324855
  · exact B1324859
  · exact B1324863
  · exact B1324867
  · exact B1324871
  · exact B1324875
  · exact B1324879
  · exact B1324883
  · exact B1324887
  · exact B1324891
  · exact B1324895
  · exact B1324899
  · exact B1324903
  · exact B1324907
  · exact B1324911
  · exact B1324915
  · exact B1324919
  · exact B1324923
  · exact B1324927
  · exact B1324931
  · exact B1324935
  · exact B1324939
  · exact B1324943
  · exact B1324947
  · exact B1324951
  · exact B1324955
  · exact B1324959
  · exact B1324963
  · exact B1324967
  · exact B1324971
  · exact B1324975
  · exact B1324979
  · exact B1324983
  · exact B1324987
  · exact B1324991
  · exact B1324995
  · exact B1324999
  · exact B1325003
  · exact B1325007
  · exact B1325011
  · exact B1325015
  · exact B1325019
  · exact B1325023
  · exact B1325027
  · exact B1325031
  · exact B1325035
  · exact B1325039
  · exact B1325043
  · exact B1325047
  · exact B1325051
  · exact B1325055
  · exact B1325059
  · exact B1325063
  · exact B1325067
  · exact B1325071
  · exact B1325075
  · exact B1325079
  · exact B1325083
  · exact B1325087
  · exact B1325091
  · exact B1325095
  · exact B1325099
  · exact B1325103
  · exact B1325107
  · exact B1325111
  · exact B1325115
  · exact B1325119
  · exact B1325123
  · exact B1325127
  · exact B1325131
  · exact B1325135
  · exact B1325139
  · exact B1325143
  · exact B1325147
  · exact B1325151
  · exact B1325155
  · exact B1325159
  · exact B1325163
  · exact B1325167
  · exact B1325171
  · exact B1325175
  · exact B1325179
  · exact B1325183
  · exact B1325187
  · exact B1325191
  · exact B1325195
  · exact B1325199
  · exact B1325203
  · exact B1325207
  · exact B1325211
  · exact B1325215
  · exact B1325219
  · exact B1325223
  · exact B1325227
  · exact B1325231
  · exact B1325235
  · exact B1325239
  · exact B1325243
  · exact B1325247
  · exact B1325251
  · exact B1325255
  · exact B1325259
  · exact B1325263
  · exact B1325267
  · exact B1325271
  · exact B1325275
  · exact B1325279
  · exact B1325283
  · exact B1325287
  · exact B1325291
  · exact B1325295
  · exact B1325299
  · exact B1325303
  · exact B1325307
  · exact B1325311
  · exact B1325315
  · exact B1325319
  · exact B1325323
  · exact B1325327
  · exact B1325331
  · exact B1325335
  · exact B1325339
  · exact B1325343
  · exact B1325347
  · exact B1325351
  · exact B1325355
  · exact B1325359
  · exact B1325363
  · exact B1325367
  · exact B1325371
  · exact B1325375
  · exact B1325379
  · exact B1325383
  · exact B1325387
  · exact B1325391
  · exact B1325395
  · exact B1325399
  · exact B1325403
  · exact B1325407
  · exact B1325411
  · exact B1325415
  · exact B1325419
  · exact B1325423
  · exact B1325427
  · exact B1325431
  · exact B1325435
  · exact B1325439
  · exact B1325443
  · exact B1325447
  · exact B1325451
  · exact B1325455
  · exact B1325459
  · exact B1325463
  · exact B1325467
  · exact B1325471
  · exact B1325475
  · exact B1325479

theorem solution (m : ℕ) (hlo : 1323480 ≤ m) (hhi : m ≤ 1325480) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 330870 ≤ j := by omega
    have hj2 : j ≤ 331369 := by omega
    have hb : Blo 1323480 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
