-- Prove2me | solution 1 for syracuse_descends_range_303832_307832
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:21.068324+00:00
-- url     : https://prove2.me/submissions/49245fdb-f363-441b-bcfd-b7861194e8a4

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


theorem B491525 : Blo 303832 491525 := bbase (se 4 (by rfl) ⟨46080, by rfl⟩ : syracuseStep 491525 = 92161) (by norm_num)
theorem B458765 : Blo 303832 458765 := bbase (se 3 (by rfl) ⟨86018, by rfl⟩ : syracuseStep 458765 = 172037) (by norm_num)
theorem B688157 : Blo 303832 688157 := bbase (se 3 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 688157 = 258059) (by norm_num)
theorem B1540133 : Blo 303832 1540133 := bbase (se 4 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 1540133 = 288775) (by norm_num)
theorem B458789 : Blo 303832 458789 := bbase (se 4 (by rfl) ⟨43011, by rfl⟩ : syracuseStep 458789 = 86023) (by norm_num)
theorem B458813 : Blo 303832 458813 := bbase (se 3 (by rfl) ⟨86027, by rfl⟩ : syracuseStep 458813 = 172055) (by norm_num)
theorem B458837 : Blo 303832 458837 := bbase (se 8 (by rfl) ⟨2688, by rfl⟩ : syracuseStep 458837 = 5377) (by norm_num)
theorem B983125 : Blo 303832 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B327773 : Blo 303832 327773 := bbase (se 3 (by rfl) ⟨61457, by rfl⟩ : syracuseStep 327773 = 122915) (by norm_num)
theorem B688229 : Blo 303832 688229 := bbase (se 4 (by rfl) ⟨64521, by rfl⟩ : syracuseStep 688229 = 129043) (by norm_num)
theorem B458861 : Blo 303832 458861 := bbase (se 3 (by rfl) ⟨86036, by rfl⟩ : syracuseStep 458861 = 172073) (by norm_num)
theorem B458885 : Blo 303832 458885 := bbase (se 4 (by rfl) ⟨43020, by rfl⟩ : syracuseStep 458885 = 86041) (by norm_num)
theorem B458909 : Blo 303832 458909 := bbase (se 3 (by rfl) ⟨86045, by rfl⟩ : syracuseStep 458909 = 172091) (by norm_num)
theorem B327845 : Blo 303832 327845 := bbase (se 4 (by rfl) ⟨30735, by rfl⟩ : syracuseStep 327845 = 61471) (by norm_num)
theorem B688301 : Blo 303832 688301 := bbase (se 3 (by rfl) ⟨129056, by rfl⟩ : syracuseStep 688301 = 258113) (by norm_num)
theorem B458933 : Blo 303832 458933 := bbase (se 5 (by rfl) ⟨21512, by rfl⟩ : syracuseStep 458933 = 43025) (by norm_num)
theorem B491717 : Blo 303832 491717 := bbase (se 4 (by rfl) ⟨46098, by rfl⟩ : syracuseStep 491717 = 92197) (by norm_num)
theorem B458957 : Blo 303832 458957 := bbase (se 3 (by rfl) ⟨86054, by rfl⟩ : syracuseStep 458957 = 172109) (by norm_num)
theorem B458981 : Blo 303832 458981 := bbase (se 4 (by rfl) ⟨43029, by rfl⟩ : syracuseStep 458981 = 86059) (by norm_num)
theorem B688373 : Blo 303832 688373 := bbase (se 5 (by rfl) ⟨32267, by rfl⟩ : syracuseStep 688373 = 64535) (by norm_num)
theorem B459005 : Blo 303832 459005 := bbase (se 3 (by rfl) ⟨86063, by rfl⟩ : syracuseStep 459005 = 172127) (by norm_num)
theorem B459029 : Blo 303832 459029 := bbase (se 6 (by rfl) ⟨10758, by rfl⟩ : syracuseStep 459029 = 21517) (by norm_num)
theorem B459053 : Blo 303832 459053 := bbase (se 3 (by rfl) ⟨86072, by rfl⟩ : syracuseStep 459053 = 172145) (by norm_num)
theorem B688445 : Blo 303832 688445 := bbase (se 3 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 688445 = 258167) (by norm_num)
theorem B459077 : Blo 303832 459077 := bbase (se 4 (by rfl) ⟨43038, by rfl⟩ : syracuseStep 459077 = 86077) (by norm_num)
theorem B491845 : Blo 303832 491845 := bbase (se 4 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 491845 = 92221) (by norm_num)
theorem B459101 : Blo 303832 459101 := bbase (se 3 (by rfl) ⟨86081, by rfl⟩ : syracuseStep 459101 = 172163) (by norm_num)
theorem B328033 : Blo 303832 328033 := bbase (se 2 (by rfl) ⟨123012, by rfl⟩ : syracuseStep 328033 = 246025) (by norm_num)
theorem B459125 : Blo 303832 459125 := bbase (se 5 (by rfl) ⟨21521, by rfl⟩ : syracuseStep 459125 = 43043) (by norm_num)
theorem B688517 : Blo 303832 688517 := bbase (se 4 (by rfl) ⟨64548, by rfl⟩ : syracuseStep 688517 = 129097) (by norm_num)
theorem B459149 : Blo 303832 459149 := bbase (se 3 (by rfl) ⟨86090, by rfl⟩ : syracuseStep 459149 = 172181) (by norm_num)
theorem B459173 : Blo 303832 459173 := bbase (se 4 (by rfl) ⟨43047, by rfl⟩ : syracuseStep 459173 = 86095) (by norm_num)
theorem B459197 : Blo 303832 459197 := bbase (se 3 (by rfl) ⟨86099, by rfl⟩ : syracuseStep 459197 = 172199) (by norm_num)
theorem B688589 : Blo 303832 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B459221 : Blo 303832 459221 := bbase (se 7 (by rfl) ⟨5381, by rfl⟩ : syracuseStep 459221 = 10763) (by norm_num)
theorem B459245 : Blo 303832 459245 := bbase (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) (by norm_num)
theorem B459269 : Blo 303832 459269 := bbase (se 4 (by rfl) ⟨43056, by rfl⟩ : syracuseStep 459269 = 86113) (by norm_num)
theorem B688661 : Blo 303832 688661 := bbase (se 6 (by rfl) ⟨16140, by rfl⟩ : syracuseStep 688661 = 32281) (by norm_num)
theorem B328217 : Blo 303832 328217 := bbase (se 2 (by rfl) ⟨123081, by rfl⟩ : syracuseStep 328217 = 246163) (by norm_num)
theorem B459293 : Blo 303832 459293 := bbase (se 3 (by rfl) ⟨86117, by rfl⟩ : syracuseStep 459293 = 172235) (by norm_num)
theorem B459317 : Blo 303832 459317 := bbase (se 5 (by rfl) ⟨21530, by rfl⟩ : syracuseStep 459317 = 43061) (by norm_num)
theorem B459341 : Blo 303832 459341 := bbase (se 3 (by rfl) ⟨86126, by rfl⟩ : syracuseStep 459341 = 172253) (by norm_num)
theorem B688733 : Blo 303832 688733 := bbase (se 3 (by rfl) ⟨129137, by rfl⟩ : syracuseStep 688733 = 258275) (by norm_num)
theorem B459365 : Blo 303832 459365 := bbase (se 4 (by rfl) ⟨43065, by rfl⟩ : syracuseStep 459365 = 86131) (by norm_num)
theorem B459389 : Blo 303832 459389 := bbase (se 3 (by rfl) ⟨86135, by rfl⟩ : syracuseStep 459389 = 172271) (by norm_num)
theorem B459413 : Blo 303832 459413 := bbase (se 6 (by rfl) ⟨10767, by rfl⟩ : syracuseStep 459413 = 21535) (by norm_num)
theorem B688805 : Blo 303832 688805 := bbase (se 4 (by rfl) ⟨64575, by rfl⟩ : syracuseStep 688805 = 129151) (by norm_num)
theorem B459437 : Blo 303832 459437 := bbase (se 3 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 459437 = 172289) (by norm_num)
theorem B459461 : Blo 303832 459461 := bbase (se 4 (by rfl) ⟨43074, by rfl⟩ : syracuseStep 459461 = 86149) (by norm_num)
theorem B459485 : Blo 303832 459485 := bbase (se 3 (by rfl) ⟨86153, by rfl⟩ : syracuseStep 459485 = 172307) (by norm_num)
theorem B656093 : Blo 303832 656093 := bbase (se 3 (by rfl) ⟨123017, by rfl⟩ : syracuseStep 656093 = 246035) (by norm_num)
theorem B688877 : Blo 303832 688877 := bbase (se 3 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 688877 = 258329) (by norm_num)
theorem B459509 : Blo 303832 459509 := bbase (se 5 (by rfl) ⟨21539, by rfl⟩ : syracuseStep 459509 = 43079) (by norm_num)
theorem B459533 : Blo 303832 459533 := bbase (se 3 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 459533 = 172325) (by norm_num)
theorem B459557 : Blo 303832 459557 := bbase (se 4 (by rfl) ⟨43083, by rfl⟩ : syracuseStep 459557 = 86167) (by norm_num)
theorem B688949 : Blo 303832 688949 := bbase (se 5 (by rfl) ⟨32294, by rfl⟩ : syracuseStep 688949 = 64589) (by norm_num)
theorem B459581 : Blo 303832 459581 := bbase (se 3 (by rfl) ⟨86171, by rfl⟩ : syracuseStep 459581 = 172343) (by norm_num)
theorem B459605 : Blo 303832 459605 := bbase (se 9 (by rfl) ⟨1346, by rfl⟩ : syracuseStep 459605 = 2693) (by norm_num)
theorem B459629 : Blo 303832 459629 := bbase (se 3 (by rfl) ⟨86180, by rfl⟩ : syracuseStep 459629 = 172361) (by norm_num)
theorem B656237 : Blo 303832 656237 := bbase (se 3 (by rfl) ⟨123044, by rfl⟩ : syracuseStep 656237 = 246089) (by norm_num)
theorem B689021 : Blo 303832 689021 := bbase (se 3 (by rfl) ⟨129191, by rfl⟩ : syracuseStep 689021 = 258383) (by norm_num)
theorem B459653 : Blo 303832 459653 := bbase (se 4 (by rfl) ⟨43092, by rfl⟩ : syracuseStep 459653 = 86185) (by norm_num)
theorem B459677 : Blo 303832 459677 := bbase (se 3 (by rfl) ⟨86189, by rfl⟩ : syracuseStep 459677 = 172379) (by norm_num)
theorem B1311653 : Blo 303832 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B459701 : Blo 303832 459701 := bbase (se 5 (by rfl) ⟨21548, by rfl⟩ : syracuseStep 459701 = 43097) (by norm_num)
theorem B689093 : Blo 303832 689093 := bbase (se 4 (by rfl) ⟨64602, by rfl⟩ : syracuseStep 689093 = 129205) (by norm_num)
theorem B492485 : Blo 303832 492485 := bbase (se 4 (by rfl) ⟨46170, by rfl⟩ : syracuseStep 492485 = 92341) (by norm_num)
theorem B459725 : Blo 303832 459725 := bbase (se 3 (by rfl) ⟨86198, by rfl⟩ : syracuseStep 459725 = 172397) (by norm_num)
theorem B459749 : Blo 303832 459749 := bbase (se 4 (by rfl) ⟨43101, by rfl⟩ : syracuseStep 459749 = 86203) (by norm_num)
theorem B459773 : Blo 303832 459773 := bbase (se 3 (by rfl) ⟨86207, by rfl⟩ : syracuseStep 459773 = 172415) (by norm_num)
theorem B689165 : Blo 303832 689165 := bbase (se 3 (by rfl) ⟨129218, by rfl⟩ : syracuseStep 689165 = 258437) (by norm_num)
theorem B459797 : Blo 303832 459797 := bbase (se 6 (by rfl) ⟨10776, by rfl⟩ : syracuseStep 459797 = 21553) (by norm_num)
theorem B459821 : Blo 303832 459821 := bbase (se 3 (by rfl) ⟨86216, by rfl⟩ : syracuseStep 459821 = 172433) (by norm_num)
theorem B459845 : Blo 303832 459845 := bbase (se 4 (by rfl) ⟨43110, by rfl⟩ : syracuseStep 459845 = 86221) (by norm_num)
theorem B689237 : Blo 303832 689237 := bbase (se 8 (by rfl) ⟨4038, by rfl⟩ : syracuseStep 689237 = 8077) (by norm_num)
theorem B459869 : Blo 303832 459869 := bbase (se 3 (by rfl) ⟨86225, by rfl⟩ : syracuseStep 459869 = 172451) (by norm_num)
theorem B1737845 : Blo 303832 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B459893 : Blo 303832 459893 := bbase (se 5 (by rfl) ⟨21557, by rfl⟩ : syracuseStep 459893 = 43115) (by norm_num)
theorem B459917 : Blo 303832 459917 := bbase (se 3 (by rfl) ⟨86234, by rfl⟩ : syracuseStep 459917 = 172469) (by norm_num)
theorem B689309 : Blo 303832 689309 := bbase (se 3 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 689309 = 258491) (by norm_num)
theorem B459941 : Blo 303832 459941 := bbase (se 4 (by rfl) ⟨43119, by rfl⟩ : syracuseStep 459941 = 86239) (by norm_num)
theorem B623789 : Blo 303832 623789 := bbase (se 3 (by rfl) ⟨116960, by rfl⟩ : syracuseStep 623789 = 233921) (by norm_num)
theorem B1475765 : Blo 303832 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B459965 : Blo 303832 459965 := bbase (se 3 (by rfl) ⟨86243, by rfl⟩ : syracuseStep 459965 = 172487) (by norm_num)
theorem B623821 : Blo 303832 623821 := bbase (se 3 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 623821 = 233933) (by norm_num)
theorem B459989 : Blo 303832 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B689381 : Blo 303832 689381 := bbase (se 4 (by rfl) ⟨64629, by rfl⟩ : syracuseStep 689381 = 129259) (by norm_num)
theorem B460013 : Blo 303832 460013 := bbase (se 3 (by rfl) ⟨86252, by rfl⟩ : syracuseStep 460013 = 172505) (by norm_num)
theorem B460037 : Blo 303832 460037 := bbase (se 4 (by rfl) ⟨43128, by rfl⟩ : syracuseStep 460037 = 86257) (by norm_num)
theorem B460061 : Blo 303832 460061 := bbase (se 3 (by rfl) ⟨86261, by rfl⟩ : syracuseStep 460061 = 172523) (by norm_num)
theorem B689453 : Blo 303832 689453 := bbase (se 3 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 689453 = 258545) (by norm_num)
theorem B1541429 : Blo 303832 1541429 := bbase (se 5 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 1541429 = 144509) (by norm_num)
theorem B460085 : Blo 303832 460085 := bbase (se 5 (by rfl) ⟨21566, by rfl⟩ : syracuseStep 460085 = 43133) (by norm_num)
theorem B591157 : Blo 303832 591157 := bbase (se 5 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 591157 = 55421) (by norm_num)
theorem B460109 : Blo 303832 460109 := bbase (se 3 (by rfl) ⟨86270, by rfl⟩ : syracuseStep 460109 = 172541) (by norm_num)
theorem B460133 : Blo 303832 460133 := bbase (se 4 (by rfl) ⟨43137, by rfl⟩ : syracuseStep 460133 = 86275) (by norm_num)
theorem B689525 : Blo 303832 689525 := bbase (se 5 (by rfl) ⟨32321, by rfl⟩ : syracuseStep 689525 = 64643) (by norm_num)
theorem B460157 : Blo 303832 460157 := bbase (se 3 (by rfl) ⟨86279, by rfl⟩ : syracuseStep 460157 = 172559) (by norm_num)
theorem B755077 : Blo 303832 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B492941 : Blo 303832 492941 := bbase (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) (by norm_num)
theorem B460181 : Blo 303832 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B460205 : Blo 303832 460205 := bbase (se 3 (by rfl) ⟨86288, by rfl⟩ : syracuseStep 460205 = 172577) (by norm_num)
theorem B689597 : Blo 303832 689597 := bbase (se 3 (by rfl) ⟨129299, by rfl⟩ : syracuseStep 689597 = 258599) (by norm_num)
theorem B460229 : Blo 303832 460229 := bbase (se 4 (by rfl) ⟨43146, by rfl⟩ : syracuseStep 460229 = 86293) (by norm_num)
theorem B460253 : Blo 303832 460253 := bbase (se 3 (by rfl) ⟨86297, by rfl⟩ : syracuseStep 460253 = 172595) (by norm_num)
theorem B394733 : Blo 303832 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B460277 : Blo 303832 460277 := bbase (se 5 (by rfl) ⟨21575, by rfl⟩ : syracuseStep 460277 = 43151) (by norm_num)
theorem B689669 : Blo 303832 689669 := bbase (se 4 (by rfl) ⟨64656, by rfl⟩ : syracuseStep 689669 = 129313) (by norm_num)
theorem B460301 : Blo 303832 460301 := bbase (se 3 (by rfl) ⟨86306, by rfl⟩ : syracuseStep 460301 = 172613) (by norm_num)
theorem B460325 : Blo 303832 460325 := bbase (se 4 (by rfl) ⟨43155, by rfl⟩ : syracuseStep 460325 = 86311) (by norm_num)
theorem B460349 : Blo 303832 460349 := bbase (se 3 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 460349 = 172631) (by norm_num)
theorem B689741 : Blo 303832 689741 := bbase (se 3 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 689741 = 258653) (by norm_num)
theorem B460373 : Blo 303832 460373 := bbase (se 8 (by rfl) ⟨2697, by rfl⟩ : syracuseStep 460373 = 5395) (by norm_num)
theorem B656981 : Blo 303832 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B460397 : Blo 303832 460397 := bbase (se 3 (by rfl) ⟨86324, by rfl⟩ : syracuseStep 460397 = 172649) (by norm_num)
theorem B460421 : Blo 303832 460421 := bbase (se 4 (by rfl) ⟨43164, by rfl⟩ : syracuseStep 460421 = 86329) (by norm_num)
theorem B689813 : Blo 303832 689813 := bbase (se 6 (by rfl) ⟨16167, by rfl⟩ : syracuseStep 689813 = 32335) (by norm_num)
theorem B460445 : Blo 303832 460445 := bbase (se 3 (by rfl) ⟨86333, by rfl⟩ : syracuseStep 460445 = 172667) (by norm_num)
theorem B460469 : Blo 303832 460469 := bbase (se 5 (by rfl) ⟨21584, by rfl⟩ : syracuseStep 460469 = 43169) (by norm_num)
theorem B460493 : Blo 303832 460493 := bbase (se 3 (by rfl) ⟨86342, by rfl⟩ : syracuseStep 460493 = 172685) (by norm_num)
theorem B689885 : Blo 303832 689885 := bbase (se 3 (by rfl) ⟨129353, by rfl⟩ : syracuseStep 689885 = 258707) (by norm_num)
theorem B460517 : Blo 303832 460517 := bbase (se 4 (by rfl) ⟨43173, by rfl⟩ : syracuseStep 460517 = 86347) (by norm_num)
theorem B460541 : Blo 303832 460541 := bbase (se 3 (by rfl) ⟨86351, by rfl⟩ : syracuseStep 460541 = 172703) (by norm_num)
theorem B460565 : Blo 303832 460565 := bbase (se 6 (by rfl) ⟨10794, by rfl⟩ : syracuseStep 460565 = 21589) (by norm_num)
theorem B689957 : Blo 303832 689957 := bbase (se 4 (by rfl) ⟨64683, by rfl⟩ : syracuseStep 689957 = 129367) (by norm_num)
theorem B984869 : Blo 303832 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B460589 : Blo 303832 460589 := bbase (se 3 (by rfl) ⟨86360, by rfl⟩ : syracuseStep 460589 = 172721) (by norm_num)
theorem B460613 : Blo 303832 460613 := bbase (se 4 (by rfl) ⟨43182, by rfl⟩ : syracuseStep 460613 = 86365) (by norm_num)
theorem B460637 : Blo 303832 460637 := bbase (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) (by norm_num)
theorem B690029 : Blo 303832 690029 := bbase (se 3 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 690029 = 258761) (by norm_num)
theorem B460661 : Blo 303832 460661 := bbase (se 5 (by rfl) ⟨21593, by rfl⟩ : syracuseStep 460661 = 43187) (by norm_num)
theorem B1312645 : Blo 303832 1312645 := bbase (se 4 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 1312645 = 246121) (by norm_num)
theorem B460685 : Blo 303832 460685 := bbase (se 3 (by rfl) ⟨86378, by rfl⟩ : syracuseStep 460685 = 172757) (by norm_num)
theorem B460709 : Blo 303832 460709 := bbase (se 4 (by rfl) ⟨43191, by rfl⟩ : syracuseStep 460709 = 86383) (by norm_num)
theorem B690101 : Blo 303832 690101 := bbase (se 5 (by rfl) ⟨32348, by rfl⟩ : syracuseStep 690101 = 64697) (by norm_num)
theorem B460733 : Blo 303832 460733 := bbase (se 3 (by rfl) ⟨86387, by rfl⟩ : syracuseStep 460733 = 172775) (by norm_num)
theorem B460757 : Blo 303832 460757 := bbase (se 7 (by rfl) ⟨5399, by rfl⟩ : syracuseStep 460757 = 10799) (by norm_num)
theorem B985061 : Blo 303832 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B460781 : Blo 303832 460781 := bbase (se 3 (by rfl) ⟨86396, by rfl⟩ : syracuseStep 460781 = 172793) (by norm_num)
theorem B690173 : Blo 303832 690173 := bbase (se 3 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 690173 = 258815) (by norm_num)
theorem B460805 : Blo 303832 460805 := bbase (se 4 (by rfl) ⟨43200, by rfl⟩ : syracuseStep 460805 = 86401) (by norm_num)
theorem B460829 : Blo 303832 460829 := bbase (se 3 (by rfl) ⟨86405, by rfl⟩ : syracuseStep 460829 = 172811) (by norm_num)
theorem B460853 : Blo 303832 460853 := bbase (se 5 (by rfl) ⟨21602, by rfl⟩ : syracuseStep 460853 = 43205) (by norm_num)
theorem B690245 : Blo 303832 690245 := bbase (se 4 (by rfl) ⟨64710, by rfl⟩ : syracuseStep 690245 = 129421) (by norm_num)
theorem B460877 : Blo 303832 460877 := bbase (se 3 (by rfl) ⟨86414, by rfl⟩ : syracuseStep 460877 = 172829) (by norm_num)
theorem B460901 : Blo 303832 460901 := bbase (se 4 (by rfl) ⟨43209, by rfl⟩ : syracuseStep 460901 = 86419) (by norm_num)
theorem B460925 : Blo 303832 460925 := bbase (se 3 (by rfl) ⟨86423, by rfl⟩ : syracuseStep 460925 = 172847) (by norm_num)
theorem B821381 : Blo 303832 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B329869 : Blo 303832 329869 := bbase (se 3 (by rfl) ⟨61850, by rfl⟩ : syracuseStep 329869 = 123701) (by norm_num)
theorem B690317 : Blo 303832 690317 := bbase (se 3 (by rfl) ⟨129434, by rfl⟩ : syracuseStep 690317 = 258869) (by norm_num)
theorem B460949 : Blo 303832 460949 := bbase (se 6 (by rfl) ⟨10803, by rfl⟩ : syracuseStep 460949 = 21607) (by norm_num)
theorem B460973 : Blo 303832 460973 := bbase (se 3 (by rfl) ⟨86432, by rfl⟩ : syracuseStep 460973 = 172865) (by norm_num)
theorem B1411253 : Blo 303832 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B460997 : Blo 303832 460997 := bbase (se 4 (by rfl) ⟨43218, by rfl⟩ : syracuseStep 460997 = 86437) (by norm_num)
theorem B690389 : Blo 303832 690389 := bbase (se 7 (by rfl) ⟨8090, by rfl⟩ : syracuseStep 690389 = 16181) (by norm_num)
theorem B461021 : Blo 303832 461021 := bbase (se 3 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 461021 = 172883) (by norm_num)
theorem B395489 : Blo 303832 395489 := bbase (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) (by norm_num)
theorem B461045 : Blo 303832 461045 := bbase (se 5 (by rfl) ⟨21611, by rfl⟩ : syracuseStep 461045 = 43223) (by norm_num)
theorem B461069 : Blo 303832 461069 := bbase (se 3 (by rfl) ⟨86450, by rfl⟩ : syracuseStep 461069 = 172901) (by norm_num)
theorem B1739029 : Blo 303832 1739029 := bbase (se 6 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 1739029 = 81517) (by norm_num)
theorem B2787605 : Blo 303832 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2492693 : Blo 303832 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B690461 : Blo 303832 690461 := bbase (se 3 (by rfl) ⟨129461, by rfl⟩ : syracuseStep 690461 = 258923) (by norm_num)
theorem B461093 : Blo 303832 461093 := bbase (se 4 (by rfl) ⟨43227, by rfl⟩ : syracuseStep 461093 = 86455) (by norm_num)
theorem B461117 : Blo 303832 461117 := bbase (se 3 (by rfl) ⟨86459, by rfl⟩ : syracuseStep 461117 = 172919) (by norm_num)
theorem B3705173 : Blo 303832 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B461141 : Blo 303832 461141 := bbase (se 10 (by rfl) ⟨675, by rfl⟩ : syracuseStep 461141 = 1351) (by norm_num)
theorem B690533 : Blo 303832 690533 := bbase (se 4 (by rfl) ⟨64737, by rfl⟩ : syracuseStep 690533 = 129475) (by norm_num)
theorem B461165 : Blo 303832 461165 := bbase (se 3 (by rfl) ⟨86468, by rfl⟩ : syracuseStep 461165 = 172937) (by norm_num)
theorem B461189 : Blo 303832 461189 := bbase (se 4 (by rfl) ⟨43236, by rfl⟩ : syracuseStep 461189 = 86473) (by norm_num)
theorem B461213 : Blo 303832 461213 := bbase (se 3 (by rfl) ⟨86477, by rfl⟩ : syracuseStep 461213 = 172955) (by norm_num)
theorem B690605 : Blo 303832 690605 := bbase (se 3 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 690605 = 258977) (by norm_num)
theorem B461237 : Blo 303832 461237 := bbase (se 5 (by rfl) ⟨21620, by rfl⟩ : syracuseStep 461237 = 43241) (by norm_num)
theorem B461261 : Blo 303832 461261 := bbase (se 3 (by rfl) ⟨86486, by rfl⟩ : syracuseStep 461261 = 172973) (by norm_num)
theorem B461285 : Blo 303832 461285 := bbase (se 4 (by rfl) ⟨43245, by rfl⟩ : syracuseStep 461285 = 86491) (by norm_num)
theorem B690677 : Blo 303832 690677 := bbase (se 5 (by rfl) ⟨32375, by rfl⟩ : syracuseStep 690677 = 64751) (by norm_num)
theorem B461309 : Blo 303832 461309 := bbase (se 3 (by rfl) ⟨86495, by rfl⟩ : syracuseStep 461309 = 172991) (by norm_num)
theorem B461333 : Blo 303832 461333 := bbase (se 6 (by rfl) ⟨10812, by rfl⟩ : syracuseStep 461333 = 21625) (by norm_num)
theorem B461357 : Blo 303832 461357 := bbase (se 3 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 461357 = 173009) (by norm_num)
theorem B690749 : Blo 303832 690749 := bbase (se 3 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 690749 = 259031) (by norm_num)
theorem B1542725 : Blo 303832 1542725 := bbase (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) (by norm_num)
theorem B461381 : Blo 303832 461381 := bbase (se 4 (by rfl) ⟨43254, by rfl⟩ : syracuseStep 461381 = 86509) (by norm_num)
theorem B461405 : Blo 303832 461405 := bbase (se 3 (by rfl) ⟨86513, by rfl⟩ : syracuseStep 461405 = 173027) (by norm_num)
theorem B461429 : Blo 303832 461429 := bbase (se 5 (by rfl) ⟨21629, by rfl⟩ : syracuseStep 461429 = 43259) (by norm_num)
theorem B690821 : Blo 303832 690821 := bbase (se 4 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 690821 = 129529) (by norm_num)
theorem B461453 : Blo 303832 461453 := bbase (se 3 (by rfl) ⟨86522, by rfl⟩ : syracuseStep 461453 = 173045) (by norm_num)
theorem B461477 : Blo 303832 461477 := bbase (se 4 (by rfl) ⟨43263, by rfl⟩ : syracuseStep 461477 = 86527) (by norm_num)
theorem B461501 : Blo 303832 461501 := bbase (se 3 (by rfl) ⟨86531, by rfl⟩ : syracuseStep 461501 = 173063) (by norm_num)
theorem B690893 : Blo 303832 690893 := bbase (se 3 (by rfl) ⟨129542, by rfl⟩ : syracuseStep 690893 = 259085) (by norm_num)
theorem B461525 : Blo 303832 461525 := bbase (se 7 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 461525 = 10817) (by norm_num)
theorem B461549 : Blo 303832 461549 := bbase (se 3 (by rfl) ⟨86540, by rfl⟩ : syracuseStep 461549 = 173081) (by norm_num)
theorem B461573 : Blo 303832 461573 := bbase (se 4 (by rfl) ⟨43272, by rfl⟩ : syracuseStep 461573 = 86545) (by norm_num)
theorem B690965 : Blo 303832 690965 := bbase (se 6 (by rfl) ⟨16194, by rfl⟩ : syracuseStep 690965 = 32389) (by norm_num)
theorem B461597 : Blo 303832 461597 := bbase (se 3 (by rfl) ⟨86549, by rfl⟩ : syracuseStep 461597 = 173099) (by norm_num)
theorem B2329397 : Blo 303832 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B461621 : Blo 303832 461621 := bbase (se 5 (by rfl) ⟨21638, by rfl⟩ : syracuseStep 461621 = 43277) (by norm_num)
theorem B461645 : Blo 303832 461645 := bbase (se 3 (by rfl) ⟨86558, by rfl⟩ : syracuseStep 461645 = 173117) (by norm_num)
theorem B691037 : Blo 303832 691037 := bbase (se 3 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 691037 = 259139) (by norm_num)
theorem B461669 : Blo 303832 461669 := bbase (se 4 (by rfl) ⟨43281, by rfl⟩ : syracuseStep 461669 = 86563) (by norm_num)
theorem B461693 : Blo 303832 461693 := bbase (se 3 (by rfl) ⟨86567, by rfl⟩ : syracuseStep 461693 = 173135) (by norm_num)
theorem B461717 : Blo 303832 461717 := bbase (se 6 (by rfl) ⟨10821, by rfl⟩ : syracuseStep 461717 = 21643) (by norm_num)
theorem B691109 : Blo 303832 691109 := bbase (se 4 (by rfl) ⟨64791, by rfl⟩ : syracuseStep 691109 = 129583) (by norm_num)
theorem B461741 : Blo 303832 461741 := bbase (se 3 (by rfl) ⟨86576, by rfl⟩ : syracuseStep 461741 = 173153) (by norm_num)
theorem B691181 : Blo 303832 691181 := bbase (se 3 (by rfl) ⟨129596, by rfl⟩ : syracuseStep 691181 = 259193) (by norm_num)
theorem B1575973 : Blo 303832 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B691253 : Blo 303832 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B691325 : Blo 303832 691325 := bbase (se 3 (by rfl) ⟨129623, by rfl⟩ : syracuseStep 691325 = 259247) (by norm_num)
theorem B691397 : Blo 303832 691397 := bbase (se 4 (by rfl) ⟨64818, by rfl⟩ : syracuseStep 691397 = 129637) (by norm_num)
theorem B691469 : Blo 303832 691469 := bbase (se 3 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 691469 = 259301) (by norm_num)
theorem B593173 : Blo 303832 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B691541 : Blo 303832 691541 := bbase (se 11 (by rfl) ⟨506, by rfl⟩ : syracuseStep 691541 = 1013) (by norm_num)
theorem B691613 : Blo 303832 691613 := bbase (se 3 (by rfl) ⟨129677, by rfl⟩ : syracuseStep 691613 = 259355) (by norm_num)
theorem B331177 : Blo 303832 331177 := bbase (se 2 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 331177 = 248383) (by norm_num)
theorem B822757 : Blo 303832 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B691685 : Blo 303832 691685 := bbase (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) (by norm_num)
theorem B691757 : Blo 303832 691757 := bbase (se 3 (by rfl) ⟨129704, by rfl⟩ : syracuseStep 691757 = 259409) (by norm_num)
theorem B691829 : Blo 303832 691829 := bbase (se 5 (by rfl) ⟨32429, by rfl⟩ : syracuseStep 691829 = 64859) (by norm_num)
theorem B691901 : Blo 303832 691901 := bbase (se 3 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 691901 = 259463) (by norm_num)
theorem B560861 : Blo 303832 560861 := bbase (se 3 (by rfl) ⟨105161, by rfl⟩ : syracuseStep 560861 = 210323) (by norm_num)
theorem B691973 : Blo 303832 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B692045 : Blo 303832 692045 := bbase (se 3 (by rfl) ⟨129758, by rfl⟩ : syracuseStep 692045 = 259517) (by norm_num)
theorem B1544021 : Blo 303832 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B397153 : Blo 303832 397153 := bbase (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) (by norm_num)
theorem B1118069 : Blo 303832 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B1478533 : Blo 303832 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B692117 : Blo 303832 692117 := bbase (se 6 (by rfl) ⟨16221, by rfl⟩ : syracuseStep 692117 = 32443) (by norm_num)
theorem B2625493 : Blo 303832 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B692189 : Blo 303832 692189 := bbase (se 3 (by rfl) ⟨129785, by rfl⟩ : syracuseStep 692189 = 259571) (by norm_num)
theorem B692261 : Blo 303832 692261 := bbase (se 4 (by rfl) ⟨64899, by rfl⟩ : syracuseStep 692261 = 129799) (by norm_num)
theorem B462917 : Blo 303832 462917 := bbase (se 4 (by rfl) ⟨43398, by rfl⟩ : syracuseStep 462917 = 86797) (by norm_num)
theorem B692333 : Blo 303832 692333 := bbase (se 3 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 692333 = 259625) (by norm_num)
theorem B692405 : Blo 303832 692405 := bbase (se 5 (by rfl) ⟨32456, by rfl⟩ : syracuseStep 692405 = 64913) (by norm_num)
theorem B1741013 : Blo 303832 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B2396405 : Blo 303832 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B692477 : Blo 303832 692477 := bbase (se 3 (by rfl) ⟨129839, by rfl⟩ : syracuseStep 692477 = 259679) (by norm_num)
theorem B692549 : Blo 303832 692549 := bbase (se 4 (by rfl) ⟨64926, by rfl⟩ : syracuseStep 692549 = 129853) (by norm_num)
theorem B692621 : Blo 303832 692621 := bbase (se 3 (by rfl) ⟨129866, by rfl⟩ : syracuseStep 692621 = 259733) (by norm_num)
theorem B332249 : Blo 303832 332249 := bbase (se 2 (by rfl) ⟨124593, by rfl⟩ : syracuseStep 332249 = 249187) (by norm_num)
theorem B824021 : Blo 303832 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B332605 : Blo 303832 332605 := bbase (se 3 (by rfl) ⟨62363, by rfl⟩ : syracuseStep 332605 = 124727) (by norm_num)
theorem B824149 : Blo 303832 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B2954069 : Blo 303832 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B365477 : Blo 303832 365477 := bbase (se 4 (by rfl) ⟨34263, by rfl⟩ : syracuseStep 365477 = 68527) (by norm_num)
theorem B332753 : Blo 303832 332753 := bbase (se 2 (by rfl) ⟨124782, by rfl⟩ : syracuseStep 332753 = 249565) (by norm_num)
theorem B365645 : Blo 303832 365645 := bbase (se 3 (by rfl) ⟨68558, by rfl⟩ : syracuseStep 365645 = 137117) (by norm_num)
theorem B1545317 : Blo 303832 1545317 := bbase (se 4 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 1545317 = 289747) (by norm_num)
theorem B365953 : Blo 303832 365953 := bbase (se 2 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 365953 = 274465) (by norm_num)
theorem B366169 : Blo 303832 366169 := bbase (se 2 (by rfl) ⟨137313, by rfl⟩ : syracuseStep 366169 = 274627) (by norm_num)
theorem B464717 : Blo 303832 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B366481 : Blo 303832 366481 := bbase (se 2 (by rfl) ⟨137430, by rfl⟩ : syracuseStep 366481 = 274861) (by norm_num)
theorem B2627477 : Blo 303832 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B1546613 : Blo 303832 1546613 := bbase (se 5 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 1546613 = 144995) (by norm_num)
theorem B1743221 : Blo 303832 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B498221 : Blo 303832 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B662069 : Blo 303832 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B432821 : Blo 303832 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B432901 : Blo 303832 432901 := bbase (se 4 (by rfl) ⟨40584, by rfl⟩ : syracuseStep 432901 = 81169) (by norm_num)
theorem B433021 : Blo 303832 433021 := bbase (se 3 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 433021 = 162383) (by norm_num)
theorem B433117 : Blo 303832 433117 := bbase (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) (by norm_num)
theorem B695341 : Blo 303832 695341 := bbase (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) (by norm_num)
theorem B2202805 : Blo 303832 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1252565 : Blo 303832 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1154357 : Blo 303832 1154357 := bbase (se 5 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 1154357 = 108221) (by norm_num)
theorem B367961 : Blo 303832 367961 := bbase (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) (by norm_num)
theorem B466285 : Blo 303832 466285 := bbase (se 3 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 466285 = 174857) (by norm_num)
theorem B826789 : Blo 303832 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B368057 : Blo 303832 368057 := bbase (se 2 (by rfl) ⟨138021, by rfl⟩ : syracuseStep 368057 = 276043) (by norm_num)
theorem B433613 : Blo 303832 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B368077 : Blo 303832 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B826853 : Blo 303832 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B1154645 : Blo 303832 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B368221 : Blo 303832 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B1547909 : Blo 303832 1547909 := bbase (se 4 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 1547909 = 290233) (by norm_num)
theorem B2989781 : Blo 303832 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B466741 : Blo 303832 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B434165 : Blo 303832 434165 := bbase (se 5 (by rfl) ⟨20351, by rfl⟩ : syracuseStep 434165 = 40703) (by norm_num)
theorem B696325 : Blo 303832 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B696509 : Blo 303832 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B3285269 : Blo 303832 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B467453 : Blo 303832 467453 := bbase (se 3 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 467453 = 175295) (by norm_num)
theorem B1319429 : Blo 303832 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B434917 : Blo 303832 434917 := bbase (se 4 (by rfl) ⟨40773, by rfl⟩ : syracuseStep 434917 = 81547) (by norm_num)
theorem B1155829 : Blo 303832 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B303949 : Blo 303832 303949 := bbase (se 3 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 303949 = 113981) (by norm_num)
theorem B992101 : Blo 303832 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B1549205 : Blo 303832 1549205 := bbase (se 6 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 1549205 = 72619) (by norm_num)
theorem B730109 : Blo 303832 730109 := bbase (se 3 (by rfl) ⟨136895, by rfl⟩ : syracuseStep 730109 = 273791) (by norm_num)
theorem B1156133 : Blo 303832 1156133 := bbase (se 4 (by rfl) ⟨108387, by rfl⟩ : syracuseStep 1156133 = 216775) (by norm_num)
theorem B370021 : Blo 303832 370021 := bbase (se 4 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 370021 = 69379) (by norm_num)
theorem B435709 : Blo 303832 435709 := bbase (se 3 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 435709 = 163391) (by norm_num)
theorem B1025621 : Blo 303832 1025621 := bbase (se 8 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 1025621 = 12019) (by norm_num)
theorem B436045 : Blo 303832 436045 := bbase (se 3 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 436045 = 163517) (by norm_num)
theorem B1026053 : Blo 303832 1026053 := bbase (se 4 (by rfl) ⟨96192, by rfl⟩ : syracuseStep 1026053 = 192385) (by norm_num)
theorem B436261 : Blo 303832 436261 := bbase (se 4 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 436261 = 81799) (by norm_num)
theorem B1550501 : Blo 303832 1550501 := bbase (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) (by norm_num)
theorem B698533 : Blo 303832 698533 := bbase (se 4 (by rfl) ⟨65487, by rfl⟩ : syracuseStep 698533 = 130975) (by norm_num)
theorem B469165 : Blo 303832 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B698653 : Blo 303832 698653 := bbase (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) (by norm_num)
theorem B731501 : Blo 303832 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B2337173 : Blo 303832 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B436637 : Blo 303832 436637 := bbase (se 3 (by rfl) ⟨81869, by rfl⟩ : syracuseStep 436637 = 163739) (by norm_num)
theorem B1026485 : Blo 303832 1026485 := bbase (se 5 (by rfl) ⟨48116, by rfl⟩ : syracuseStep 1026485 = 96233) (by norm_num)
theorem B731597 : Blo 303832 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B1026917 : Blo 303832 1026917 := bbase (se 4 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 1026917 = 192547) (by norm_num)
theorem B1158245 : Blo 303832 1158245 := bbase (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) (by norm_num)
theorem B1027349 : Blo 303832 1027349 := bbase (se 6 (by rfl) ⟨24078, by rfl⟩ : syracuseStep 1027349 = 48157) (by norm_num)
theorem B1158533 : Blo 303832 1158533 := bbase (se 4 (by rfl) ⟨108612, by rfl⟩ : syracuseStep 1158533 = 217225) (by norm_num)
theorem B1551797 : Blo 303832 1551797 := bbase (se 5 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 1551797 = 145481) (by norm_num)
theorem B2207189 : Blo 303832 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B994805 : Blo 303832 994805 := bbase (se 5 (by rfl) ⟨46631, by rfl⟩ : syracuseStep 994805 = 93263) (by norm_num)
theorem B1027781 : Blo 303832 1027781 := bbase (se 4 (by rfl) ⟨96354, by rfl⟩ : syracuseStep 1027781 = 192709) (by norm_num)
theorem B438061 : Blo 303832 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B929893 : Blo 303832 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B1028213 : Blo 303832 1028213 := bbase (se 5 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 1028213 = 96395) (by norm_num)
theorem B1323317 : Blo 303832 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B733693 : Blo 303832 733693 := bbase (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) (by norm_num)
theorem B1028645 : Blo 303832 1028645 := bbase (se 4 (by rfl) ⟨96435, by rfl⟩ : syracuseStep 1028645 = 192871) (by norm_num)
theorem B1159717 : Blo 303832 1159717 := bbase (se 4 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 1159717 = 217447) (by norm_num)
theorem B2142773 : Blo 303832 2142773 := bbase (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) (by norm_num)
theorem B1553093 : Blo 303832 1553093 := bbase (se 4 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 1553093 = 291205) (by norm_num)
theorem B373469 : Blo 303832 373469 := bbase (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) (by norm_num)
theorem B1160021 : Blo 303832 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1029077 : Blo 303832 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B373753 : Blo 303832 373753 := bbase (se 2 (by rfl) ⟨140157, by rfl⟩ : syracuseStep 373753 = 280315) (by norm_num)
theorem B734309 : Blo 303832 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B701581 : Blo 303832 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B308521 : Blo 303832 308521 := bbase (se 2 (by rfl) ⟨115695, by rfl⟩ : syracuseStep 308521 = 231391) (by norm_num)
theorem B1029509 : Blo 303832 1029509 := bbase (se 4 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 1029509 = 193033) (by norm_num)
theorem B734645 : Blo 303832 734645 := bbase (se 5 (by rfl) ⟨34436, by rfl⟩ : syracuseStep 734645 = 68873) (by norm_num)
theorem B472717 : Blo 303832 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B3127061 : Blo 303832 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1029941 : Blo 303832 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B735037 : Blo 303832 735037 := bbase (se 3 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 735037 = 275639) (by norm_num)
theorem B341833 : Blo 303832 341833 := bbase (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) (by norm_num)
theorem B341869 : Blo 303832 341869 := bbase (se 3 (by rfl) ⟨64100, by rfl⟩ : syracuseStep 341869 = 128201) (by norm_num)
theorem B341905 : Blo 303832 341905 := bbase (se 2 (by rfl) ⟨128214, by rfl⟩ : syracuseStep 341905 = 256429) (by norm_num)
theorem B341941 : Blo 303832 341941 := bbase (se 5 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 341941 = 32057) (by norm_num)
theorem B1554389 : Blo 303832 1554389 := bbase (se 7 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 1554389 = 36431) (by norm_num)
theorem B341977 : Blo 303832 341977 := bbase (se 2 (by rfl) ⟨128241, by rfl⟩ : syracuseStep 341977 = 256483) (by norm_num)
theorem B931829 : Blo 303832 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B342013 : Blo 303832 342013 := bbase (se 3 (by rfl) ⟨64127, by rfl⟩ : syracuseStep 342013 = 128255) (by norm_num)
theorem B342049 : Blo 303832 342049 := bbase (se 2 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 342049 = 256537) (by norm_num)
theorem B342085 : Blo 303832 342085 := bbase (se 4 (by rfl) ⟨32070, by rfl⟩ : syracuseStep 342085 = 64141) (by norm_num)
theorem B342121 : Blo 303832 342121 := bbase (se 2 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 342121 = 256591) (by norm_num)
theorem B342157 : Blo 303832 342157 := bbase (se 3 (by rfl) ⟨64154, by rfl⟩ : syracuseStep 342157 = 128309) (by norm_num)
theorem B1947797 : Blo 303832 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B342193 : Blo 303832 342193 := bbase (se 2 (by rfl) ⟨128322, by rfl⟩ : syracuseStep 342193 = 256645) (by norm_num)
theorem B342229 : Blo 303832 342229 := bbase (se 7 (by rfl) ⟨4010, by rfl⟩ : syracuseStep 342229 = 8021) (by norm_num)
theorem B1030373 : Blo 303832 1030373 := bbase (se 4 (by rfl) ⟨96597, by rfl⟩ : syracuseStep 1030373 = 193195) (by norm_num)
theorem B342265 : Blo 303832 342265 := bbase (se 2 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 342265 = 256699) (by norm_num)
theorem B342301 : Blo 303832 342301 := bbase (se 3 (by rfl) ⟨64181, by rfl⟩ : syracuseStep 342301 = 128363) (by norm_num)
theorem B342337 : Blo 303832 342337 := bbase (se 2 (by rfl) ⟨128376, by rfl⟩ : syracuseStep 342337 = 256753) (by norm_num)
theorem B866645 : Blo 303832 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B342373 : Blo 303832 342373 := bbase (se 4 (by rfl) ⟨32097, by rfl⟩ : syracuseStep 342373 = 64195) (by norm_num)
theorem B342409 : Blo 303832 342409 := bbase (se 2 (by rfl) ⟨128403, by rfl⟩ : syracuseStep 342409 = 256807) (by norm_num)
theorem B342445 : Blo 303832 342445 := bbase (se 3 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 342445 = 128417) (by norm_num)
theorem B440749 : Blo 303832 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B342481 : Blo 303832 342481 := bbase (se 2 (by rfl) ⟨128430, by rfl⟩ : syracuseStep 342481 = 256861) (by norm_num)
theorem B342517 : Blo 303832 342517 := bbase (se 5 (by rfl) ⟨16055, by rfl⟩ : syracuseStep 342517 = 32111) (by norm_num)
theorem B342553 : Blo 303832 342553 := bbase (se 2 (by rfl) ⟨128457, by rfl⟩ : syracuseStep 342553 = 256915) (by norm_num)
theorem B1325605 : Blo 303832 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B342589 : Blo 303832 342589 := bbase (se 3 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 342589 = 128471) (by norm_num)
theorem B342625 : Blo 303832 342625 := bbase (se 2 (by rfl) ⟨128484, by rfl⟩ : syracuseStep 342625 = 256969) (by norm_num)
theorem B342661 : Blo 303832 342661 := bbase (se 4 (by rfl) ⟨32124, by rfl⟩ : syracuseStep 342661 = 64249) (by norm_num)
theorem B1030805 : Blo 303832 1030805 := bbase (se 6 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 1030805 = 48319) (by norm_num)
theorem B342697 : Blo 303832 342697 := bbase (se 2 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 342697 = 257023) (by norm_num)
theorem B342733 : Blo 303832 342733 := bbase (se 3 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 342733 = 128525) (by norm_num)
theorem B309997 : Blo 303832 309997 := bbase (se 3 (by rfl) ⟨58124, by rfl⟩ : syracuseStep 309997 = 116249) (by norm_num)
theorem B342769 : Blo 303832 342769 := bbase (se 2 (by rfl) ⟨128538, by rfl⟩ : syracuseStep 342769 = 257077) (by norm_num)
theorem B342805 : Blo 303832 342805 := bbase (se 6 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 342805 = 16069) (by norm_num)
theorem B342841 : Blo 303832 342841 := bbase (se 2 (by rfl) ⟨128565, by rfl⟩ : syracuseStep 342841 = 257131) (by norm_num)
theorem B22362965 : Blo 303832 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B342877 : Blo 303832 342877 := bbase (se 3 (by rfl) ⟨64289, by rfl⟩ : syracuseStep 342877 = 128579) (by norm_num)
theorem B342913 : Blo 303832 342913 := bbase (se 2 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 342913 = 257185) (by norm_num)
theorem B1162133 : Blo 303832 1162133 := bbase (se 6 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 1162133 = 54475) (by norm_num)
theorem B342949 : Blo 303832 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B1391525 : Blo 303832 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B342985 : Blo 303832 342985 := bbase (se 2 (by rfl) ⟨128619, by rfl⟩ : syracuseStep 342985 = 257239) (by norm_num)
theorem B343021 : Blo 303832 343021 := bbase (se 3 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 343021 = 128633) (by norm_num)
theorem B1653749 : Blo 303832 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B343057 : Blo 303832 343057 := bbase (se 2 (by rfl) ⟨128646, by rfl⟩ : syracuseStep 343057 = 257293) (by norm_num)
theorem B343093 : Blo 303832 343093 := bbase (se 5 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 343093 = 32165) (by norm_num)
theorem B769085 : Blo 303832 769085 := bbase (se 3 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 769085 = 288407) (by norm_num)
theorem B1031237 : Blo 303832 1031237 := bbase (se 4 (by rfl) ⟨96678, by rfl⟩ : syracuseStep 1031237 = 193357) (by norm_num)
theorem B343129 : Blo 303832 343129 := bbase (se 2 (by rfl) ⟨128673, by rfl⟩ : syracuseStep 343129 = 257347) (by norm_num)
theorem B343165 : Blo 303832 343165 := bbase (se 3 (by rfl) ⟨64343, by rfl⟩ : syracuseStep 343165 = 128687) (by norm_num)
theorem B343201 : Blo 303832 343201 := bbase (se 2 (by rfl) ⟨128700, by rfl⟩ : syracuseStep 343201 = 257401) (by norm_num)
theorem B441517 : Blo 303832 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B1162421 : Blo 303832 1162421 := bbase (se 5 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 1162421 = 108977) (by norm_num)
theorem B343237 : Blo 303832 343237 := bbase (se 4 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 343237 = 64357) (by norm_num)
theorem B1555685 : Blo 303832 1555685 := bbase (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) (by norm_num)
theorem B343273 : Blo 303832 343273 := bbase (se 2 (by rfl) ⟨128727, by rfl⟩ : syracuseStep 343273 = 257455) (by norm_num)
theorem B769277 : Blo 303832 769277 := bbase (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) (by norm_num)
theorem B343309 : Blo 303832 343309 := bbase (se 3 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 343309 = 128741) (by norm_num)
theorem B343345 : Blo 303832 343345 := bbase (se 2 (by rfl) ⟨128754, by rfl⟩ : syracuseStep 343345 = 257509) (by norm_num)
theorem B343381 : Blo 303832 343381 := bbase (se 11 (by rfl) ⟨251, by rfl⟩ : syracuseStep 343381 = 503) (by norm_num)
theorem B310613 : Blo 303832 310613 := bbase (se 11 (by rfl) ⟨227, by rfl⟩ : syracuseStep 310613 = 455) (by norm_num)
theorem B343417 : Blo 303832 343417 := bbase (se 2 (by rfl) ⟨128781, by rfl⟩ : syracuseStep 343417 = 257563) (by norm_num)
theorem B343453 : Blo 303832 343453 := bbase (se 3 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 343453 = 128795) (by norm_num)
theorem B343489 : Blo 303832 343489 := bbase (se 2 (by rfl) ⟨128808, by rfl⟩ : syracuseStep 343489 = 257617) (by norm_num)
theorem B343525 : Blo 303832 343525 := bbase (se 4 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 343525 = 64411) (by norm_num)
theorem B867829 : Blo 303832 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B1031669 : Blo 303832 1031669 := bbase (se 5 (by rfl) ⟨48359, by rfl⟩ : syracuseStep 1031669 = 96719) (by norm_num)
theorem B343561 : Blo 303832 343561 := bbase (se 2 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 343561 = 257671) (by norm_num)
theorem B4439573 : Blo 303832 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B310825 : Blo 303832 310825 := bbase (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) (by norm_num)
theorem B343597 : Blo 303832 343597 := bbase (se 3 (by rfl) ⟨64424, by rfl⟩ : syracuseStep 343597 = 128849) (by norm_num)
theorem B343633 : Blo 303832 343633 := bbase (se 2 (by rfl) ⟨128862, by rfl⟩ : syracuseStep 343633 = 257725) (by norm_num)
theorem B769621 : Blo 303832 769621 := bbase (se 8 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 769621 = 9019) (by norm_num)
theorem B343669 : Blo 303832 343669 := bbase (se 5 (by rfl) ⟨16109, by rfl⟩ : syracuseStep 343669 = 32219) (by norm_num)
theorem B867989 : Blo 303832 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B343705 : Blo 303832 343705 := bbase (se 2 (by rfl) ⟨128889, by rfl⟩ : syracuseStep 343705 = 257779) (by norm_num)
theorem B343741 : Blo 303832 343741 := bbase (se 3 (by rfl) ⟨64451, by rfl⟩ : syracuseStep 343741 = 128903) (by norm_num)
theorem B769733 : Blo 303832 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B343777 : Blo 303832 343777 := bbase (se 2 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 343777 = 257833) (by norm_num)
theorem B343813 : Blo 303832 343813 := bbase (se 4 (by rfl) ⟨32232, by rfl⟩ : syracuseStep 343813 = 64465) (by norm_num)
theorem B343849 : Blo 303832 343849 := bbase (se 2 (by rfl) ⟨128943, by rfl⟩ : syracuseStep 343849 = 257887) (by norm_num)
theorem B343885 : Blo 303832 343885 := bbase (se 3 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 343885 = 128957) (by norm_num)
theorem B343921 : Blo 303832 343921 := bbase (se 2 (by rfl) ⟨128970, by rfl⟩ : syracuseStep 343921 = 257941) (by norm_num)
theorem B409469 : Blo 303832 409469 := bbase (se 3 (by rfl) ⟨76775, by rfl⟩ : syracuseStep 409469 = 153551) (by norm_num)
theorem B769925 : Blo 303832 769925 := bbase (se 4 (by rfl) ⟨72180, by rfl⟩ : syracuseStep 769925 = 144361) (by norm_num)
theorem B868229 : Blo 303832 868229 := bbase (se 4 (by rfl) ⟨81396, by rfl⟩ : syracuseStep 868229 = 162793) (by norm_num)
theorem B343957 : Blo 303832 343957 := bbase (se 6 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 343957 = 16123) (by norm_num)
theorem B1032101 : Blo 303832 1032101 := bbase (se 4 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 1032101 = 193519) (by norm_num)
theorem B343993 : Blo 303832 343993 := bbase (se 2 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 343993 = 257995) (by norm_num)
theorem B344029 : Blo 303832 344029 := bbase (se 3 (by rfl) ⟨64505, by rfl⟩ : syracuseStep 344029 = 129011) (by norm_num)
theorem B344065 : Blo 303832 344065 := bbase (se 2 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 344065 = 258049) (by norm_num)
theorem B1753109 : Blo 303832 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B344101 : Blo 303832 344101 := bbase (se 4 (by rfl) ⟨32259, by rfl⟩ : syracuseStep 344101 = 64519) (by norm_num)
theorem B868421 : Blo 303832 868421 := bbase (se 4 (by rfl) ⟨81414, by rfl⟩ : syracuseStep 868421 = 162829) (by norm_num)
theorem B344137 : Blo 303832 344137 := bbase (se 2 (by rfl) ⟨129051, by rfl⟩ : syracuseStep 344137 = 258103) (by norm_num)
theorem B344173 : Blo 303832 344173 := bbase (se 3 (by rfl) ⟨64532, by rfl⟩ : syracuseStep 344173 = 129065) (by norm_num)
theorem B344209 : Blo 303832 344209 := bbase (se 2 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 344209 = 258157) (by norm_num)
theorem B344245 : Blo 303832 344245 := bbase (se 5 (by rfl) ⟨16136, by rfl⟩ : syracuseStep 344245 = 32273) (by norm_num)
theorem B344281 : Blo 303832 344281 := bbase (se 2 (by rfl) ⟨129105, by rfl⟩ : syracuseStep 344281 = 258211) (by norm_num)
theorem B770269 : Blo 303832 770269 := bbase (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) (by norm_num)
theorem B344317 : Blo 303832 344317 := bbase (se 3 (by rfl) ⟨64559, by rfl⟩ : syracuseStep 344317 = 129119) (by norm_num)
theorem B344353 : Blo 303832 344353 := bbase (se 2 (by rfl) ⟨129132, by rfl⟩ : syracuseStep 344353 = 258265) (by norm_num)
theorem B344389 : Blo 303832 344389 := bbase (se 4 (by rfl) ⟨32286, by rfl⟩ : syracuseStep 344389 = 64573) (by norm_num)
theorem B770381 : Blo 303832 770381 := bbase (se 3 (by rfl) ⟨144446, by rfl⟩ : syracuseStep 770381 = 288893) (by norm_num)
theorem B1032533 : Blo 303832 1032533 := bbase (se 10 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 1032533 = 3025) (by norm_num)
theorem B1163605 : Blo 303832 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B344425 : Blo 303832 344425 := bbase (se 2 (by rfl) ⟨129159, by rfl⟩ : syracuseStep 344425 = 258319) (by norm_num)
theorem B344461 : Blo 303832 344461 := bbase (se 3 (by rfl) ⟨64586, by rfl⟩ : syracuseStep 344461 = 129173) (by norm_num)
theorem B311725 : Blo 303832 311725 := bbase (se 3 (by rfl) ⟨58448, by rfl⟩ : syracuseStep 311725 = 116897) (by norm_num)
theorem B344497 : Blo 303832 344497 := bbase (se 2 (by rfl) ⟨129186, by rfl⟩ : syracuseStep 344497 = 258373) (by norm_num)
theorem B344533 : Blo 303832 344533 := bbase (se 7 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 344533 = 8075) (by norm_num)
theorem B1556981 : Blo 303832 1556981 := bbase (se 5 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 1556981 = 145967) (by norm_num)
theorem B344569 : Blo 303832 344569 := bbase (se 2 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 344569 = 258427) (by norm_num)
theorem B770573 : Blo 303832 770573 := bbase (se 3 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 770573 = 288965) (by norm_num)
theorem B344605 : Blo 303832 344605 := bbase (se 3 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 344605 = 129227) (by norm_num)
theorem B344641 : Blo 303832 344641 := bbase (se 2 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 344641 = 258481) (by norm_num)
theorem B344677 : Blo 303832 344677 := bbase (se 4 (by rfl) ⟨32313, by rfl⟩ : syracuseStep 344677 = 64627) (by norm_num)
theorem B1163909 : Blo 303832 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B344713 : Blo 303832 344713 := bbase (se 2 (by rfl) ⟨129267, by rfl⟩ : syracuseStep 344713 = 258535) (by norm_num)
theorem B344749 : Blo 303832 344749 := bbase (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) (by norm_num)
theorem B344785 : Blo 303832 344785 := bbase (se 2 (by rfl) ⟨129294, by rfl⟩ : syracuseStep 344785 = 258589) (by norm_num)
theorem B344821 : Blo 303832 344821 := bbase (se 5 (by rfl) ⟨16163, by rfl⟩ : syracuseStep 344821 = 32327) (by norm_num)
theorem B1032965 : Blo 303832 1032965 := bbase (se 4 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 1032965 = 193681) (by norm_num)
theorem B344857 : Blo 303832 344857 := bbase (se 2 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 344857 = 258643) (by norm_num)
theorem B344893 : Blo 303832 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B344929 : Blo 303832 344929 := bbase (se 2 (by rfl) ⟨129348, by rfl⟩ : syracuseStep 344929 = 258697) (by norm_num)
theorem B770917 : Blo 303832 770917 := bbase (se 4 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 770917 = 144547) (by norm_num)
theorem B344965 : Blo 303832 344965 := bbase (se 4 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 344965 = 64681) (by norm_num)
theorem B738181 : Blo 303832 738181 := bbase (se 4 (by rfl) ⟨69204, by rfl⟩ : syracuseStep 738181 = 138409) (by norm_num)
theorem B345001 : Blo 303832 345001 := bbase (se 2 (by rfl) ⟨129375, by rfl⟩ : syracuseStep 345001 = 258751) (by norm_num)
theorem B738229 : Blo 303832 738229 := bbase (se 5 (by rfl) ⟨34604, by rfl⟩ : syracuseStep 738229 = 69209) (by norm_num)
theorem B345037 : Blo 303832 345037 := bbase (se 3 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 345037 = 129389) (by norm_num)
theorem B771029 : Blo 303832 771029 := bbase (se 7 (by rfl) ⟨9035, by rfl⟩ : syracuseStep 771029 = 18071) (by norm_num)
theorem B345073 : Blo 303832 345073 := bbase (se 2 (by rfl) ⟨129402, by rfl⟩ : syracuseStep 345073 = 258805) (by norm_num)
theorem B345109 : Blo 303832 345109 := bbase (se 6 (by rfl) ⟨8088, by rfl⟩ : syracuseStep 345109 = 16177) (by norm_num)
theorem B869413 : Blo 303832 869413 := bbase (se 4 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 869413 = 163015) (by norm_num)
theorem B345145 : Blo 303832 345145 := bbase (se 2 (by rfl) ⟨129429, by rfl⟩ : syracuseStep 345145 = 258859) (by norm_num)
theorem B345181 : Blo 303832 345181 := bbase (se 3 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 345181 = 129443) (by norm_num)
theorem B345217 : Blo 303832 345217 := bbase (se 2 (by rfl) ⟨129456, by rfl⟩ : syracuseStep 345217 = 258913) (by norm_num)
theorem B771221 : Blo 303832 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B410789 : Blo 303832 410789 := bbase (se 4 (by rfl) ⟨38511, by rfl⟩ : syracuseStep 410789 = 77023) (by norm_num)
theorem B345253 : Blo 303832 345253 := bbase (se 4 (by rfl) ⟨32367, by rfl⟩ : syracuseStep 345253 = 64735) (by norm_num)
theorem B1033397 : Blo 303832 1033397 := bbase (se 5 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 1033397 = 96881) (by norm_num)
theorem B345289 : Blo 303832 345289 := bbase (se 2 (by rfl) ⟨129483, by rfl⟩ : syracuseStep 345289 = 258967) (by norm_num)
theorem B345325 : Blo 303832 345325 := bbase (se 3 (by rfl) ⟨64748, by rfl⟩ : syracuseStep 345325 = 129497) (by norm_num)
theorem B345361 : Blo 303832 345361 := bbase (se 2 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 345361 = 259021) (by norm_num)
theorem B2606357 : Blo 303832 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B4179221 : Blo 303832 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B345397 : Blo 303832 345397 := bbase (se 5 (by rfl) ⟨16190, by rfl⟩ : syracuseStep 345397 = 32381) (by norm_num)
theorem B345433 : Blo 303832 345433 := bbase (se 2 (by rfl) ⟨129537, by rfl⟩ : syracuseStep 345433 = 259075) (by norm_num)
theorem B345469 : Blo 303832 345469 := bbase (se 3 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 345469 = 129551) (by norm_num)
theorem B345505 : Blo 303832 345505 := bbase (se 2 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 345505 = 259129) (by norm_num)
theorem B345541 : Blo 303832 345541 := bbase (se 4 (by rfl) ⟨32394, by rfl⟩ : syracuseStep 345541 = 64789) (by norm_num)
theorem B345577 : Blo 303832 345577 := bbase (se 2 (by rfl) ⟨129591, by rfl⟩ : syracuseStep 345577 = 259183) (by norm_num)
theorem B771565 : Blo 303832 771565 := bbase (se 3 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 771565 = 289337) (by norm_num)
theorem B345613 : Blo 303832 345613 := bbase (se 3 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 345613 = 129605) (by norm_num)
theorem B738845 : Blo 303832 738845 := bbase (se 3 (by rfl) ⟨138533, by rfl⟩ : syracuseStep 738845 = 277067) (by norm_num)
theorem B1590821 : Blo 303832 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B345649 : Blo 303832 345649 := bbase (se 2 (by rfl) ⟨129618, by rfl⟩ : syracuseStep 345649 = 259237) (by norm_num)
theorem B345685 : Blo 303832 345685 := bbase (se 8 (by rfl) ⟨2025, by rfl⟩ : syracuseStep 345685 = 4051) (by norm_num)
theorem B771677 : Blo 303832 771677 := bbase (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) (by norm_num)
theorem B1033829 : Blo 303832 1033829 := bbase (se 4 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 1033829 = 193843) (by norm_num)
theorem B1263221 : Blo 303832 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B345721 : Blo 303832 345721 := bbase (se 2 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 345721 = 259291) (by norm_num)
theorem B345757 : Blo 303832 345757 := bbase (se 3 (by rfl) ⟨64829, by rfl⟩ : syracuseStep 345757 = 129659) (by norm_num)
theorem B345793 : Blo 303832 345793 := bbase (se 2 (by rfl) ⟨129672, by rfl⟩ : syracuseStep 345793 = 259345) (by norm_num)
theorem B345829 : Blo 303832 345829 := bbase (se 4 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 345829 = 64843) (by norm_num)
theorem B1558277 : Blo 303832 1558277 := bbase (se 4 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 1558277 = 292177) (by norm_num)
theorem B345865 : Blo 303832 345865 := bbase (se 2 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 345865 = 259399) (by norm_num)
theorem B771869 : Blo 303832 771869 := bbase (se 3 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 771869 = 289451) (by norm_num)
theorem B345901 : Blo 303832 345901 := bbase (se 3 (by rfl) ⟨64856, by rfl⟩ : syracuseStep 345901 = 129713) (by norm_num)
theorem B345937 : Blo 303832 345937 := bbase (se 2 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 345937 = 259453) (by norm_num)
theorem B345973 : Blo 303832 345973 := bbase (se 5 (by rfl) ⟨16217, by rfl⟩ : syracuseStep 345973 = 32435) (by norm_num)
theorem B739189 : Blo 303832 739189 := bbase (se 5 (by rfl) ⟨34649, by rfl⟩ : syracuseStep 739189 = 69299) (by norm_num)
theorem B346009 : Blo 303832 346009 := bbase (se 2 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 346009 = 259507) (by norm_num)
theorem B346045 : Blo 303832 346045 := bbase (se 3 (by rfl) ⟨64883, by rfl⟩ : syracuseStep 346045 = 129767) (by norm_num)
theorem B346081 : Blo 303832 346081 := bbase (se 2 (by rfl) ⟨129780, by rfl⟩ : syracuseStep 346081 = 259561) (by norm_num)
theorem B346117 : Blo 303832 346117 := bbase (se 4 (by rfl) ⟨32448, by rfl⟩ : syracuseStep 346117 = 64897) (by norm_num)
theorem B4769813 : Blo 303832 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034261 : Blo 303832 1034261 := bbase (se 6 (by rfl) ⟨24240, by rfl⟩ : syracuseStep 1034261 = 48481) (by norm_num)
theorem B313381 : Blo 303832 313381 := bbase (se 4 (by rfl) ⟨29379, by rfl⟩ : syracuseStep 313381 = 58759) (by norm_num)
theorem B346153 : Blo 303832 346153 := bbase (se 2 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 346153 = 259615) (by norm_num)
theorem B346189 : Blo 303832 346189 := bbase (se 3 (by rfl) ⟨64910, by rfl⟩ : syracuseStep 346189 = 129821) (by norm_num)
theorem B739421 : Blo 303832 739421 := bbase (se 3 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 739421 = 277283) (by norm_num)
theorem B346225 : Blo 303832 346225 := bbase (se 2 (by rfl) ⟨129834, by rfl⟩ : syracuseStep 346225 = 259669) (by norm_num)
theorem B772213 : Blo 303832 772213 := bbase (se 5 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 772213 = 72395) (by norm_num)
theorem B870517 : Blo 303832 870517 := bbase (se 5 (by rfl) ⟨40805, by rfl⟩ : syracuseStep 870517 = 81611) (by norm_num)
theorem B1656949 : Blo 303832 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B346261 : Blo 303832 346261 := bbase (se 6 (by rfl) ⟨8115, by rfl⟩ : syracuseStep 346261 = 16231) (by norm_num)
theorem B346297 : Blo 303832 346297 := bbase (se 2 (by rfl) ⟨129861, by rfl⟩ : syracuseStep 346297 = 259723) (by norm_num)
theorem B772325 : Blo 303832 772325 := bbase (se 4 (by rfl) ⟨72405, by rfl⟩ : syracuseStep 772325 = 144811) (by norm_num)
theorem B739613 : Blo 303832 739613 := bbase (se 3 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 739613 = 277355) (by norm_num)
theorem B772517 : Blo 303832 772517 := bbase (se 4 (by rfl) ⟨72423, by rfl⟩ : syracuseStep 772517 = 144847) (by norm_num)
theorem B1034693 : Blo 303832 1034693 := bbase (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) (by norm_num)
theorem B1166021 : Blo 303832 1166021 := bbase (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) (by norm_num)
theorem B9358037 : Blo 303832 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B772861 : Blo 303832 772861 := bbase (se 3 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 772861 = 289823) (by norm_num)
theorem B772973 : Blo 303832 772973 := bbase (se 3 (by rfl) ⟨144932, by rfl⟩ : syracuseStep 772973 = 289865) (by norm_num)
theorem B1035125 : Blo 303832 1035125 := bbase (se 5 (by rfl) ⟨48521, by rfl⟩ : syracuseStep 1035125 = 97043) (by norm_num)
theorem B1166309 : Blo 303832 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B773165 : Blo 303832 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B2935925 : Blo 303832 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B1035557 : Blo 303832 1035557 := bbase (se 4 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 1035557 = 194167) (by norm_num)
theorem B576821 : Blo 303832 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B773509 : Blo 303832 773509 := bbase (se 4 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 773509 = 145033) (by norm_num)
theorem B576973 : Blo 303832 576973 := bbase (se 3 (by rfl) ⟨108182, by rfl⟩ : syracuseStep 576973 = 216365) (by norm_num)
theorem B773621 : Blo 303832 773621 := bbase (se 5 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 773621 = 72527) (by norm_num)
theorem B872021 : Blo 303832 872021 := bbase (se 8 (by rfl) ⟨5109, by rfl⟩ : syracuseStep 872021 = 10219) (by norm_num)
theorem B2313845 : Blo 303832 2313845 := bbase (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) (by norm_num)
theorem B773813 : Blo 303832 773813 := bbase (se 5 (by rfl) ⟨36272, by rfl⟩ : syracuseStep 773813 = 72545) (by norm_num)
theorem B1035989 : Blo 303832 1035989 := bbase (se 7 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 1035989 = 24281) (by norm_num)
theorem B577277 : Blo 303832 577277 := bbase (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) (by norm_num)
theorem B347977 : Blo 303832 347977 := bbase (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) (by norm_num)
theorem B774157 : Blo 303832 774157 := bbase (se 3 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 774157 = 290309) (by norm_num)
theorem B774269 : Blo 303832 774269 := bbase (se 3 (by rfl) ⟨145175, by rfl⟩ : syracuseStep 774269 = 290351) (by norm_num)
theorem B1036421 : Blo 303832 1036421 := bbase (se 4 (by rfl) ⟨97164, by rfl⟩ : syracuseStep 1036421 = 194329) (by norm_num)
theorem B1167493 : Blo 303832 1167493 := bbase (se 4 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 1167493 = 218905) (by norm_num)
theorem B2609333 : Blo 303832 2609333 := bbase (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) (by norm_num)
theorem B774461 : Blo 303832 774461 := bbase (se 3 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 774461 = 290423) (by norm_num)
theorem B1462693 : Blo 303832 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B1167797 : Blo 303832 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B578029 : Blo 303832 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B1036853 : Blo 303832 1036853 := bbase (se 5 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 1036853 = 97205) (by norm_num)
theorem B578173 : Blo 303832 578173 := bbase (se 3 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 578173 = 216815) (by norm_num)
theorem B774805 : Blo 303832 774805 := bbase (se 6 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 774805 = 36319) (by norm_num)
theorem B348889 : Blo 303832 348889 := bbase (se 2 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 348889 = 261667) (by norm_num)
theorem B348929 : Blo 303832 348929 := bbase (se 2 (by rfl) ⟨130848, by rfl⟩ : syracuseStep 348929 = 261697) (by norm_num)
theorem B774917 : Blo 303832 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B512797 : Blo 303832 512797 := bbase (se 3 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 512797 = 192299) (by norm_num)
theorem B578333 : Blo 303832 578333 := bbase (se 3 (by rfl) ⟨108437, by rfl⟩ : syracuseStep 578333 = 216875) (by norm_num)
theorem B512885 : Blo 303832 512885 := bbase (se 5 (by rfl) ⟨24041, by rfl⟩ : syracuseStep 512885 = 48083) (by norm_num)
theorem B349049 : Blo 303832 349049 := bbase (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) (by norm_num)
theorem B578477 : Blo 303832 578477 := bbase (se 3 (by rfl) ⟨108464, by rfl⟩ : syracuseStep 578477 = 216929) (by norm_num)
theorem B775109 : Blo 303832 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B1037285 : Blo 303832 1037285 := bbase (se 4 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 1037285 = 194491) (by norm_num)
theorem B513013 : Blo 303832 513013 := bbase (se 5 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 513013 = 48095) (by norm_num)
theorem B513101 : Blo 303832 513101 := bbase (se 3 (by rfl) ⟨96206, by rfl⟩ : syracuseStep 513101 = 192413) (by norm_num)
theorem B1299557 : Blo 303832 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B873605 : Blo 303832 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B513229 : Blo 303832 513229 := bbase (se 3 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 513229 = 192461) (by norm_num)
theorem B578765 : Blo 303832 578765 := bbase (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) (by norm_num)
theorem B775453 : Blo 303832 775453 := bbase (se 3 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 775453 = 290795) (by norm_num)
theorem B513317 : Blo 303832 513317 := bbase (se 4 (by rfl) ⟨48123, by rfl⟩ : syracuseStep 513317 = 96247) (by norm_num)
theorem B1299797 : Blo 303832 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B578917 : Blo 303832 578917 := bbase (se 4 (by rfl) ⟨54273, by rfl⟩ : syracuseStep 578917 = 108547) (by norm_num)
theorem B775565 : Blo 303832 775565 := bbase (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) (by norm_num)
theorem B1037717 : Blo 303832 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B513445 : Blo 303832 513445 := bbase (se 4 (by rfl) ⟨48135, by rfl⟩ : syracuseStep 513445 = 96271) (by norm_num)
theorem B513533 : Blo 303832 513533 := bbase (se 3 (by rfl) ⟨96287, by rfl⟩ : syracuseStep 513533 = 192575) (by norm_num)
theorem B349705 : Blo 303832 349705 := bbase (se 2 (by rfl) ⟨131139, by rfl⟩ : syracuseStep 349705 = 262279) (by norm_num)
theorem B775757 : Blo 303832 775757 := bbase (se 3 (by rfl) ⟨145454, by rfl⟩ : syracuseStep 775757 = 290909) (by norm_num)
theorem B513661 : Blo 303832 513661 := bbase (se 3 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 513661 = 192623) (by norm_num)
theorem B579221 : Blo 303832 579221 := bbase (se 6 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 579221 = 27151) (by norm_num)
theorem B349861 : Blo 303832 349861 := bbase (se 4 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 349861 = 65599) (by norm_num)
theorem B513749 : Blo 303832 513749 := bbase (se 7 (by rfl) ⟨6020, by rfl⟩ : syracuseStep 513749 = 12041) (by norm_num)
theorem B710405 : Blo 303832 710405 := bbase (se 4 (by rfl) ⟨66600, by rfl⟩ : syracuseStep 710405 = 133201) (by norm_num)
theorem B874277 : Blo 303832 874277 := bbase (se 4 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 874277 = 163927) (by norm_num)
theorem B1038149 : Blo 303832 1038149 := bbase (se 4 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 1038149 = 194653) (by norm_num)
theorem B513877 : Blo 303832 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B776101 : Blo 303832 776101 := bbase (se 4 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 776101 = 145519) (by norm_num)
theorem B513965 : Blo 303832 513965 := bbase (se 3 (by rfl) ⟨96368, by rfl⟩ : syracuseStep 513965 = 192737) (by norm_num)
theorem B1103813 : Blo 303832 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B776213 : Blo 303832 776213 := bbase (se 6 (by rfl) ⟨18192, by rfl⟩ : syracuseStep 776213 = 36385) (by norm_num)
theorem B514093 : Blo 303832 514093 := bbase (se 3 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 514093 = 192785) (by norm_num)
theorem B514181 : Blo 303832 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B350353 : Blo 303832 350353 := bbase (se 2 (by rfl) ⟨131382, by rfl⟩ : syracuseStep 350353 = 262765) (by norm_num)
theorem B776405 : Blo 303832 776405 := bbase (se 7 (by rfl) ⟨9098, by rfl⟩ : syracuseStep 776405 = 18197) (by norm_num)
theorem B874709 : Blo 303832 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B1038581 : Blo 303832 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B514309 : Blo 303832 514309 := bbase (se 4 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 514309 = 96433) (by norm_num)
theorem B514397 : Blo 303832 514397 := bbase (se 3 (by rfl) ⟨96449, by rfl⟩ : syracuseStep 514397 = 192899) (by norm_num)
theorem B579973 : Blo 303832 579973 := bbase (se 4 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 579973 = 108745) (by norm_num)
theorem B514525 : Blo 303832 514525 := bbase (se 3 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 514525 = 192947) (by norm_num)
theorem B580117 : Blo 303832 580117 := bbase (se 6 (by rfl) ⟨13596, by rfl⟩ : syracuseStep 580117 = 27193) (by norm_num)
theorem B776749 : Blo 303832 776749 := bbase (se 3 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 776749 = 291281) (by norm_num)
theorem B514613 : Blo 303832 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B776861 : Blo 303832 776861 := bbase (se 3 (by rfl) ⟨145661, by rfl⟩ : syracuseStep 776861 = 291323) (by norm_num)
theorem B514741 : Blo 303832 514741 := bbase (se 5 (by rfl) ⟨24128, by rfl⟩ : syracuseStep 514741 = 48257) (by norm_num)
theorem B580277 : Blo 303832 580277 := bbase (se 5 (by rfl) ⟨27200, by rfl⟩ : syracuseStep 580277 = 54401) (by norm_num)
theorem B514829 : Blo 303832 514829 := bbase (se 3 (by rfl) ⟨96530, by rfl⟩ : syracuseStep 514829 = 193061) (by norm_num)
theorem B351005 : Blo 303832 351005 := bbase (se 3 (by rfl) ⟨65813, by rfl⟩ : syracuseStep 351005 = 131627) (by norm_num)
theorem B1170245 : Blo 303832 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B580421 : Blo 303832 580421 := bbase (se 4 (by rfl) ⟨54414, by rfl⟩ : syracuseStep 580421 = 108829) (by norm_num)
theorem B777053 : Blo 303832 777053 := bbase (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) (by norm_num)
theorem B514957 : Blo 303832 514957 := bbase (se 3 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 514957 = 193109) (by norm_num)
theorem B875461 : Blo 303832 875461 := bbase (se 4 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 875461 = 164149) (by norm_num)
theorem B515045 : Blo 303832 515045 := bbase (se 4 (by rfl) ⟨48285, by rfl⟩ : syracuseStep 515045 = 96571) (by norm_num)
theorem B547877 : Blo 303832 547877 := bbase (se 4 (by rfl) ⟨51363, by rfl⟩ : syracuseStep 547877 = 102727) (by norm_num)
theorem B515173 : Blo 303832 515173 := bbase (se 4 (by rfl) ⟨48297, by rfl⟩ : syracuseStep 515173 = 96595) (by norm_num)
theorem B580709 : Blo 303832 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B548021 : Blo 303832 548021 := bbase (se 5 (by rfl) ⟨25688, by rfl⟩ : syracuseStep 548021 = 51377) (by norm_num)
theorem B777397 : Blo 303832 777397 := bbase (se 5 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 777397 = 72881) (by norm_num)
theorem B515261 : Blo 303832 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B1105093 : Blo 303832 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B580861 : Blo 303832 580861 := bbase (se 3 (by rfl) ⟨108911, by rfl⟩ : syracuseStep 580861 = 217823) (by norm_num)
theorem B777509 : Blo 303832 777509 := bbase (se 4 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 777509 = 145783) (by norm_num)
theorem B515389 : Blo 303832 515389 := bbase (se 3 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 515389 = 193271) (by norm_num)
theorem B351577 : Blo 303832 351577 := bbase (se 2 (by rfl) ⟨131841, by rfl⟩ : syracuseStep 351577 = 263683) (by norm_num)
theorem B548237 : Blo 303832 548237 := bbase (se 3 (by rfl) ⟨102794, by rfl⟩ : syracuseStep 548237 = 205589) (by norm_num)
theorem B515477 : Blo 303832 515477 := bbase (se 6 (by rfl) ⟨12081, by rfl⟩ : syracuseStep 515477 = 24163) (by norm_num)
theorem B777701 : Blo 303832 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B515605 : Blo 303832 515605 := bbase (se 6 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 515605 = 24169) (by norm_num)
theorem B581165 : Blo 303832 581165 := bbase (se 3 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 581165 = 217937) (by norm_num)
theorem B1302085 : Blo 303832 1302085 := bbase (se 4 (by rfl) ⟨122070, by rfl⟩ : syracuseStep 1302085 = 244141) (by norm_num)
theorem B515693 : Blo 303832 515693 := bbase (se 3 (by rfl) ⟨96692, by rfl⟩ : syracuseStep 515693 = 193385) (by norm_num)
theorem B384689 : Blo 303832 384689 := bbase (se 2 (by rfl) ⟨144258, by rfl⟩ : syracuseStep 384689 = 288517) (by norm_num)
theorem B384745 : Blo 303832 384745 := bbase (se 2 (by rfl) ⟨144279, by rfl⟩ : syracuseStep 384745 = 288559) (by norm_num)
theorem B515821 : Blo 303832 515821 := bbase (se 3 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 515821 = 193433) (by norm_num)
theorem B778045 : Blo 303832 778045 := bbase (se 3 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 778045 = 291767) (by norm_num)
theorem B515909 : Blo 303832 515909 := bbase (se 4 (by rfl) ⟨48366, by rfl⟩ : syracuseStep 515909 = 96733) (by norm_num)
theorem B384841 : Blo 303832 384841 := bbase (se 2 (by rfl) ⟨144315, by rfl⟩ : syracuseStep 384841 = 288631) (by norm_num)
theorem B548741 : Blo 303832 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B778157 : Blo 303832 778157 := bbase (se 3 (by rfl) ⟨145904, by rfl⟩ : syracuseStep 778157 = 291809) (by norm_num)
theorem B516037 : Blo 303832 516037 := bbase (se 4 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 516037 = 96757) (by norm_num)
theorem B385013 : Blo 303832 385013 := bbase (se 5 (by rfl) ⟨18047, by rfl⟩ : syracuseStep 385013 = 36095) (by norm_num)
theorem B516125 : Blo 303832 516125 := bbase (se 3 (by rfl) ⟨96773, by rfl⟩ : syracuseStep 516125 = 193547) (by norm_num)
theorem B385069 : Blo 303832 385069 := bbase (se 3 (by rfl) ⟨72200, by rfl⟩ : syracuseStep 385069 = 144401) (by norm_num)
theorem B1564741 : Blo 303832 1564741 := bbase (se 4 (by rfl) ⟨146694, by rfl⟩ : syracuseStep 1564741 = 293389) (by norm_num)
theorem B778349 : Blo 303832 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B385165 : Blo 303832 385165 := bbase (se 3 (by rfl) ⟨72218, by rfl⟩ : syracuseStep 385165 = 144437) (by norm_num)
theorem B516253 : Blo 303832 516253 := bbase (se 3 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 516253 = 193595) (by norm_num)
theorem B516341 : Blo 303832 516341 := bbase (se 5 (by rfl) ⟨24203, by rfl⟩ : syracuseStep 516341 = 48407) (by norm_num)
theorem B581917 : Blo 303832 581917 := bbase (se 3 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 581917 = 218219) (by norm_num)
theorem B385337 : Blo 303832 385337 := bbase (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) (by norm_num)
theorem B1466693 : Blo 303832 1466693 := bbase (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) (by norm_num)
theorem B385393 : Blo 303832 385393 := bbase (se 2 (by rfl) ⟨144522, by rfl⟩ : syracuseStep 385393 = 289045) (by norm_num)
theorem B516469 : Blo 303832 516469 := bbase (se 5 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 516469 = 48419) (by norm_num)
theorem B582061 : Blo 303832 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B778693 : Blo 303832 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B516557 : Blo 303832 516557 := bbase (se 3 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 516557 = 193709) (by norm_num)
theorem B385489 : Blo 303832 385489 := bbase (se 2 (by rfl) ⟨144558, by rfl⟩ : syracuseStep 385489 = 289117) (by norm_num)
theorem B1958357 : Blo 303832 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B1466885 : Blo 303832 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B778805 : Blo 303832 778805 := bbase (se 5 (by rfl) ⟨36506, by rfl⟩ : syracuseStep 778805 = 73013) (by norm_num)
theorem B516685 : Blo 303832 516685 := bbase (se 3 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 516685 = 193757) (by norm_num)
theorem B582221 : Blo 303832 582221 := bbase (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) (by norm_num)
theorem B385661 : Blo 303832 385661 := bbase (se 3 (by rfl) ⟨72311, by rfl⟩ : syracuseStep 385661 = 144623) (by norm_num)
theorem B1237637 : Blo 303832 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B1106581 : Blo 303832 1106581 := bbase (se 6 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 1106581 = 51871) (by norm_num)
theorem B516773 : Blo 303832 516773 := bbase (se 4 (by rfl) ⟨48447, by rfl⟩ : syracuseStep 516773 = 96895) (by norm_num)
theorem B385717 : Blo 303832 385717 := bbase (se 5 (by rfl) ⟨18080, by rfl⟩ : syracuseStep 385717 = 36161) (by norm_num)
theorem B1237717 : Blo 303832 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B582365 : Blo 303832 582365 := bbase (se 3 (by rfl) ⟨109193, by rfl⟩ : syracuseStep 582365 = 218387) (by norm_num)
theorem B778997 : Blo 303832 778997 := bbase (se 5 (by rfl) ⟨36515, by rfl⟩ : syracuseStep 778997 = 73031) (by norm_num)
theorem B385813 : Blo 303832 385813 := bbase (se 6 (by rfl) ⟨9042, by rfl⟩ : syracuseStep 385813 = 18085) (by norm_num)
theorem B1237781 : Blo 303832 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B516901 : Blo 303832 516901 := bbase (se 4 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 516901 = 96919) (by norm_num)
theorem B516989 : Blo 303832 516989 := bbase (se 3 (by rfl) ⟨96935, by rfl⟩ : syracuseStep 516989 = 193871) (by norm_num)
theorem B975797 : Blo 303832 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B385985 : Blo 303832 385985 := bbase (se 2 (by rfl) ⟨144744, by rfl⟩ : syracuseStep 385985 = 289489) (by norm_num)
theorem B386041 : Blo 303832 386041 := bbase (se 2 (by rfl) ⟨144765, by rfl⟩ : syracuseStep 386041 = 289531) (by norm_num)
theorem B517117 : Blo 303832 517117 := bbase (se 3 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 517117 = 193919) (by norm_num)
theorem B582653 : Blo 303832 582653 := bbase (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) (by norm_num)
theorem B1303573 : Blo 303832 1303573 := bbase (se 6 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 1303573 = 61105) (by norm_num)
theorem B1303589 : Blo 303832 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B517205 : Blo 303832 517205 := bbase (se 8 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 517205 = 6061) (by norm_num)
theorem B386137 : Blo 303832 386137 := bbase (se 2 (by rfl) ⟨144801, by rfl⟩ : syracuseStep 386137 = 289603) (by norm_num)
theorem B582805 : Blo 303832 582805 := bbase (se 6 (by rfl) ⟨13659, by rfl⟩ : syracuseStep 582805 = 27319) (by norm_num)
theorem B517333 : Blo 303832 517333 := bbase (se 7 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 517333 = 12125) (by norm_num)
theorem B386309 : Blo 303832 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B517421 : Blo 303832 517421 := bbase (se 3 (by rfl) ⟨97016, by rfl⟩ : syracuseStep 517421 = 194033) (by norm_num)
theorem B386365 : Blo 303832 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B386461 : Blo 303832 386461 := bbase (se 3 (by rfl) ⟨72461, by rfl⟩ : syracuseStep 386461 = 144923) (by norm_num)
theorem B517549 : Blo 303832 517549 := bbase (se 3 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 517549 = 194081) (by norm_num)
theorem B583109 : Blo 303832 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B517637 : Blo 303832 517637 := bbase (se 4 (by rfl) ⟨48528, by rfl⟩ : syracuseStep 517637 = 97057) (by norm_num)
theorem B386633 : Blo 303832 386633 := bbase (se 2 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 386633 = 289975) (by norm_num)
theorem B386689 : Blo 303832 386689 := bbase (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) (by norm_num)
theorem B517765 : Blo 303832 517765 := bbase (se 4 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 517765 = 97081) (by norm_num)
theorem B517853 : Blo 303832 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B386785 : Blo 303832 386785 := bbase (se 2 (by rfl) ⟨145044, by rfl⟩ : syracuseStep 386785 = 290089) (by norm_num)
theorem B354061 : Blo 303832 354061 := bbase (se 3 (by rfl) ⟨66386, by rfl⟩ : syracuseStep 354061 = 132773) (by norm_num)
theorem B976693 : Blo 303832 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B517981 : Blo 303832 517981 := bbase (se 3 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 517981 = 194243) (by norm_num)
theorem B649061 : Blo 303832 649061 := bbase (se 4 (by rfl) ⟨60849, by rfl⟩ : syracuseStep 649061 = 121699) (by norm_num)
theorem B386957 : Blo 303832 386957 := bbase (se 3 (by rfl) ⟨72554, by rfl⟩ : syracuseStep 386957 = 145109) (by norm_num)
theorem B518069 : Blo 303832 518069 := bbase (se 5 (by rfl) ⟨24284, by rfl⟩ : syracuseStep 518069 = 48569) (by norm_num)
theorem B387013 : Blo 303832 387013 := bbase (se 4 (by rfl) ⟨36282, by rfl⟩ : syracuseStep 387013 = 72565) (by norm_num)
theorem B387109 : Blo 303832 387109 := bbase (se 4 (by rfl) ⟨36291, by rfl⟩ : syracuseStep 387109 = 72583) (by norm_num)
theorem B518197 : Blo 303832 518197 := bbase (se 5 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 518197 = 48581) (by norm_num)
theorem B4384853 : Blo 303832 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B944261 : Blo 303832 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B518285 : Blo 303832 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B583861 : Blo 303832 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B387281 : Blo 303832 387281 := bbase (se 2 (by rfl) ⟨145230, by rfl⟩ : syracuseStep 387281 = 290461) (by norm_num)
theorem B1009925 : Blo 303832 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B387337 : Blo 303832 387337 := bbase (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) (by norm_num)
theorem B518413 : Blo 303832 518413 := bbase (se 3 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 518413 = 194405) (by norm_num)
theorem B584005 : Blo 303832 584005 := bbase (se 4 (by rfl) ⟨54750, by rfl⟩ : syracuseStep 584005 = 109501) (by norm_num)
theorem B518501 : Blo 303832 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B387433 : Blo 303832 387433 := bbase (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) (by norm_num)
theorem B1173941 : Blo 303832 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B354781 : Blo 303832 354781 := bbase (se 3 (by rfl) ⟨66521, by rfl⟩ : syracuseStep 354781 = 133043) (by norm_num)
theorem B518629 : Blo 303832 518629 := bbase (se 4 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 518629 = 97243) (by norm_num)
theorem B584165 : Blo 303832 584165 := bbase (se 4 (by rfl) ⟨54765, by rfl⟩ : syracuseStep 584165 = 109531) (by norm_num)
theorem B387605 : Blo 303832 387605 := bbase (se 6 (by rfl) ⟨9084, by rfl⟩ : syracuseStep 387605 = 18169) (by norm_num)
theorem B518717 : Blo 303832 518717 := bbase (se 3 (by rfl) ⟨97259, by rfl⟩ : syracuseStep 518717 = 194519) (by norm_num)
theorem B387661 : Blo 303832 387661 := bbase (se 3 (by rfl) ⟨72686, by rfl⟩ : syracuseStep 387661 = 145373) (by norm_num)
theorem B584309 : Blo 303832 584309 := bbase (se 5 (by rfl) ⟨27389, by rfl⟩ : syracuseStep 584309 = 54779) (by norm_num)
theorem B387757 : Blo 303832 387757 := bbase (se 3 (by rfl) ⟨72704, by rfl⟩ : syracuseStep 387757 = 145409) (by norm_num)
theorem B518845 : Blo 303832 518845 := bbase (se 3 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 518845 = 194567) (by norm_num)
theorem B649949 : Blo 303832 649949 := bbase (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) (by norm_num)
theorem B879349 : Blo 303832 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B518933 : Blo 303832 518933 := bbase (se 6 (by rfl) ⟨12162, by rfl⟩ : syracuseStep 518933 = 24325) (by norm_num)
theorem B387929 : Blo 303832 387929 := bbase (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) (by norm_num)
theorem B387985 : Blo 303832 387985 := bbase (se 2 (by rfl) ⟨145494, by rfl⟩ : syracuseStep 387985 = 290989) (by norm_num)
theorem B519061 : Blo 303832 519061 := bbase (se 6 (by rfl) ⟨12165, by rfl⟩ : syracuseStep 519061 = 24331) (by norm_num)
theorem B650189 : Blo 303832 650189 := bbase (se 3 (by rfl) ⟨121910, by rfl⟩ : syracuseStep 650189 = 243821) (by norm_num)
theorem B519149 : Blo 303832 519149 := bbase (se 3 (by rfl) ⟨97340, by rfl⟩ : syracuseStep 519149 = 194681) (by norm_num)
theorem B388081 : Blo 303832 388081 := bbase (se 2 (by rfl) ⟨145530, by rfl⟩ : syracuseStep 388081 = 291061) (by norm_num)
theorem B781397 : Blo 303832 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B519277 : Blo 303832 519277 := bbase (se 3 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 519277 = 194729) (by norm_num)
theorem B388253 : Blo 303832 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B1109189 : Blo 303832 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B519365 : Blo 303832 519365 := bbase (se 4 (by rfl) ⟨48690, by rfl⟩ : syracuseStep 519365 = 97381) (by norm_num)
theorem B2321621 : Blo 303832 2321621 := bbase (se 7 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 2321621 = 54413) (by norm_num)
theorem B388309 : Blo 303832 388309 := bbase (se 7 (by rfl) ⟨4550, by rfl⟩ : syracuseStep 388309 = 9101) (by norm_num)
theorem B1305845 : Blo 303832 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B388405 : Blo 303832 388405 := bbase (se 5 (by rfl) ⟨18206, by rfl⟩ : syracuseStep 388405 = 36413) (by norm_num)
theorem B650693 : Blo 303832 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B650701 : Blo 303832 650701 := bbase (se 3 (by rfl) ⟨122006, by rfl⟩ : syracuseStep 650701 = 244013) (by norm_num)
theorem B388577 : Blo 303832 388577 := bbase (se 2 (by rfl) ⟨145716, by rfl⟩ : syracuseStep 388577 = 291433) (by norm_num)
theorem B486893 : Blo 303832 486893 := bbase (se 3 (by rfl) ⟨91292, by rfl⟩ : syracuseStep 486893 = 182585) (by norm_num)
theorem B388633 : Blo 303832 388633 := bbase (se 2 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 388633 = 291475) (by norm_num)
theorem B388729 : Blo 303832 388729 := bbase (se 2 (by rfl) ⟨145773, by rfl⟩ : syracuseStep 388729 = 291547) (by norm_num)
theorem B683693 : Blo 303832 683693 := bbase (se 3 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 683693 = 256385) (by norm_num)
theorem B1044149 : Blo 303832 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B683765 : Blo 303832 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B388901 : Blo 303832 388901 := bbase (se 4 (by rfl) ⟨36459, by rfl⟩ : syracuseStep 388901 = 72919) (by norm_num)
theorem B552749 : Blo 303832 552749 := bbase (se 3 (by rfl) ⟨103640, by rfl⟩ : syracuseStep 552749 = 207281) (by norm_num)
theorem B683837 : Blo 303832 683837 := bbase (se 3 (by rfl) ⟨128219, by rfl⟩ : syracuseStep 683837 = 256439) (by norm_num)
theorem B388957 : Blo 303832 388957 := bbase (se 3 (by rfl) ⟨72929, by rfl⟩ : syracuseStep 388957 = 145859) (by norm_num)
theorem B683909 : Blo 303832 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B389053 : Blo 303832 389053 := bbase (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) (by norm_num)
theorem B683981 : Blo 303832 683981 := bbase (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) (by norm_num)
theorem B487405 : Blo 303832 487405 := bbase (se 3 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 487405 = 182777) (by norm_num)
theorem B684053 : Blo 303832 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B1044517 : Blo 303832 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B684125 : Blo 303832 684125 := bbase (se 3 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 684125 = 256547) (by norm_num)
theorem B389225 : Blo 303832 389225 := bbase (se 2 (by rfl) ⟨145959, by rfl⟩ : syracuseStep 389225 = 291919) (by norm_num)
theorem B389281 : Blo 303832 389281 := bbase (se 2 (by rfl) ⟨145980, by rfl⟩ : syracuseStep 389281 = 291961) (by norm_num)
theorem B684197 : Blo 303832 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B684269 : Blo 303832 684269 := bbase (se 3 (by rfl) ⟨128300, by rfl⟩ : syracuseStep 684269 = 256601) (by norm_num)
theorem B389377 : Blo 303832 389377 := bbase (se 2 (by rfl) ⟨146016, by rfl⟩ : syracuseStep 389377 = 292033) (by norm_num)
theorem B684341 : Blo 303832 684341 := bbase (se 5 (by rfl) ⟨32078, by rfl⟩ : syracuseStep 684341 = 64157) (by norm_num)
theorem B1241413 : Blo 303832 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B684413 : Blo 303832 684413 := bbase (se 3 (by rfl) ⟨128327, by rfl⟩ : syracuseStep 684413 = 256655) (by norm_num)
theorem B389549 : Blo 303832 389549 := bbase (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) (by norm_num)
theorem B684485 : Blo 303832 684485 := bbase (se 4 (by rfl) ⟨64170, by rfl⟩ : syracuseStep 684485 = 128341) (by norm_num)
theorem B684557 : Blo 303832 684557 := bbase (se 3 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 684557 = 256709) (by norm_num)
theorem B487949 : Blo 303832 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B1470997 : Blo 303832 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B651829 : Blo 303832 651829 := bbase (se 5 (by rfl) ⟨30554, by rfl⟩ : syracuseStep 651829 = 61109) (by norm_num)
theorem B684629 : Blo 303832 684629 := bbase (se 8 (by rfl) ⟨4011, by rfl⟩ : syracuseStep 684629 = 8023) (by norm_num)
theorem B422509 : Blo 303832 422509 := bbase (se 3 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 422509 = 158441) (by norm_num)
theorem B979589 : Blo 303832 979589 := bbase (se 4 (by rfl) ⟨91836, by rfl⟩ : syracuseStep 979589 = 183673) (by norm_num)
theorem B684701 : Blo 303832 684701 := bbase (se 3 (by rfl) ⟨128381, by rfl⟩ : syracuseStep 684701 = 256763) (by norm_num)
theorem B684773 : Blo 303832 684773 := bbase (se 4 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 684773 = 128395) (by norm_num)
theorem B389873 : Blo 303832 389873 := bbase (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) (by norm_num)
theorem B684845 : Blo 303832 684845 := bbase (se 3 (by rfl) ⟨128408, by rfl⟩ : syracuseStep 684845 = 256817) (by norm_num)
theorem B389969 : Blo 303832 389969 := bbase (se 2 (by rfl) ⟨146238, by rfl⟩ : syracuseStep 389969 = 292477) (by norm_num)
theorem B684917 : Blo 303832 684917 := bbase (se 5 (by rfl) ⟨32105, by rfl⟩ : syracuseStep 684917 = 64211) (by norm_num)
theorem B652205 : Blo 303832 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B684989 : Blo 303832 684989 := bbase (se 3 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 684989 = 256871) (by norm_num)
theorem B685061 : Blo 303832 685061 := bbase (se 4 (by rfl) ⟨64224, by rfl⟩ : syracuseStep 685061 = 128449) (by norm_num)
theorem B488501 : Blo 303832 488501 := bbase (se 5 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 488501 = 45797) (by norm_num)
theorem B685133 : Blo 303832 685133 := bbase (se 3 (by rfl) ⟨128462, by rfl⟩ : syracuseStep 685133 = 256925) (by norm_num)
theorem B455765 : Blo 303832 455765 := bbase (se 8 (by rfl) ⟨2670, by rfl⟩ : syracuseStep 455765 = 5341) (by norm_num)
theorem B488533 : Blo 303832 488533 := bbase (se 8 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 488533 = 5725) (by norm_num)
theorem B455789 : Blo 303832 455789 := bbase (se 3 (by rfl) ⟨85460, by rfl⟩ : syracuseStep 455789 = 170921) (by norm_num)
theorem B455813 : Blo 303832 455813 := bbase (se 4 (by rfl) ⟨42732, by rfl⟩ : syracuseStep 455813 = 85465) (by norm_num)
theorem B685205 : Blo 303832 685205 := bbase (se 6 (by rfl) ⟨16059, by rfl⟩ : syracuseStep 685205 = 32119) (by norm_num)
theorem B455837 : Blo 303832 455837 := bbase (se 3 (by rfl) ⟨85469, by rfl⟩ : syracuseStep 455837 = 170939) (by norm_num)
theorem B455861 : Blo 303832 455861 := bbase (se 5 (by rfl) ⟨21368, by rfl⟩ : syracuseStep 455861 = 42737) (by norm_num)
theorem B455885 : Blo 303832 455885 := bbase (se 3 (by rfl) ⟨85478, by rfl⟩ : syracuseStep 455885 = 170957) (by norm_num)
theorem B324821 : Blo 303832 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B685277 : Blo 303832 685277 := bbase (se 3 (by rfl) ⟨128489, by rfl⟩ : syracuseStep 685277 = 256979) (by norm_num)
theorem B455909 : Blo 303832 455909 := bbase (se 4 (by rfl) ⟨42741, by rfl⟩ : syracuseStep 455909 = 85483) (by norm_num)
theorem B455933 : Blo 303832 455933 := bbase (se 3 (by rfl) ⟨85487, by rfl⟩ : syracuseStep 455933 = 170975) (by norm_num)
theorem B455957 : Blo 303832 455957 := bbase (se 6 (by rfl) ⟨10686, by rfl⟩ : syracuseStep 455957 = 21373) (by norm_num)
theorem B685349 : Blo 303832 685349 := bbase (se 4 (by rfl) ⟨64251, by rfl⟩ : syracuseStep 685349 = 128503) (by norm_num)
theorem B455981 : Blo 303832 455981 := bbase (se 3 (by rfl) ⟨85496, by rfl⟩ : syracuseStep 455981 = 170993) (by norm_num)
theorem B456005 : Blo 303832 456005 := bbase (se 4 (by rfl) ⟨42750, by rfl⟩ : syracuseStep 456005 = 85501) (by norm_num)
theorem B456029 : Blo 303832 456029 := bbase (se 3 (by rfl) ⟨85505, by rfl⟩ : syracuseStep 456029 = 171011) (by norm_num)
theorem B685421 : Blo 303832 685421 := bbase (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) (by norm_num)
theorem B456053 : Blo 303832 456053 := bbase (se 5 (by rfl) ⟨21377, by rfl⟩ : syracuseStep 456053 = 42755) (by norm_num)
theorem B456077 : Blo 303832 456077 := bbase (se 3 (by rfl) ⟨85514, by rfl⟩ : syracuseStep 456077 = 171029) (by norm_num)
theorem B325009 : Blo 303832 325009 := bbase (se 2 (by rfl) ⟨121878, by rfl⟩ : syracuseStep 325009 = 243757) (by norm_num)
theorem B456101 : Blo 303832 456101 := bbase (se 4 (by rfl) ⟨42759, by rfl⟩ : syracuseStep 456101 = 85519) (by norm_num)
theorem B685493 : Blo 303832 685493 := bbase (se 5 (by rfl) ⟨32132, by rfl⟩ : syracuseStep 685493 = 64265) (by norm_num)
theorem B456125 : Blo 303832 456125 := bbase (se 3 (by rfl) ⟨85523, by rfl⟩ : syracuseStep 456125 = 171047) (by norm_num)
theorem B456149 : Blo 303832 456149 := bbase (se 7 (by rfl) ⟨5345, by rfl⟩ : syracuseStep 456149 = 10691) (by norm_num)
theorem B3503573 : Blo 303832 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B456173 : Blo 303832 456173 := bbase (se 3 (by rfl) ⟨85532, by rfl⟩ : syracuseStep 456173 = 171065) (by norm_num)
theorem B685565 : Blo 303832 685565 := bbase (se 3 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 685565 = 257087) (by norm_num)
theorem B521725 : Blo 303832 521725 := bbase (se 3 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 521725 = 195647) (by norm_num)
theorem B456197 : Blo 303832 456197 := bbase (se 4 (by rfl) ⟨42768, by rfl⟩ : syracuseStep 456197 = 85537) (by norm_num)
theorem B456221 : Blo 303832 456221 := bbase (se 3 (by rfl) ⟨85541, by rfl⟩ : syracuseStep 456221 = 171083) (by norm_num)
theorem B456245 : Blo 303832 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B685637 : Blo 303832 685637 := bbase (se 4 (by rfl) ⟨64278, by rfl⟩ : syracuseStep 685637 = 128557) (by norm_num)
theorem B456269 : Blo 303832 456269 := bbase (se 3 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 456269 = 171101) (by norm_num)
theorem B456293 : Blo 303832 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B456317 : Blo 303832 456317 := bbase (se 3 (by rfl) ⟨85559, by rfl⟩ : syracuseStep 456317 = 171119) (by norm_num)
theorem B685709 : Blo 303832 685709 := bbase (se 3 (by rfl) ⟨128570, by rfl⟩ : syracuseStep 685709 = 257141) (by norm_num)
theorem B456341 : Blo 303832 456341 := bbase (se 6 (by rfl) ⟨10695, by rfl⟩ : syracuseStep 456341 = 21391) (by norm_num)
theorem B456365 : Blo 303832 456365 := bbase (se 3 (by rfl) ⟨85568, by rfl⟩ : syracuseStep 456365 = 171137) (by norm_num)
theorem B456389 : Blo 303832 456389 := bbase (se 4 (by rfl) ⟨42786, by rfl⟩ : syracuseStep 456389 = 85573) (by norm_num)
theorem B685781 : Blo 303832 685781 := bbase (se 7 (by rfl) ⟨8036, by rfl⟩ : syracuseStep 685781 = 16073) (by norm_num)
theorem B456413 : Blo 303832 456413 := bbase (se 3 (by rfl) ⟨85577, by rfl⟩ : syracuseStep 456413 = 171155) (by norm_num)
theorem B456437 : Blo 303832 456437 := bbase (se 5 (by rfl) ⟨21395, by rfl⟩ : syracuseStep 456437 = 42791) (by norm_num)
theorem B456461 : Blo 303832 456461 := bbase (se 3 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 456461 = 171173) (by norm_num)
theorem B685853 : Blo 303832 685853 := bbase (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) (by norm_num)
theorem B456485 : Blo 303832 456485 := bbase (se 4 (by rfl) ⟨42795, by rfl⟩ : syracuseStep 456485 = 85591) (by norm_num)
theorem B456509 : Blo 303832 456509 := bbase (se 3 (by rfl) ⟨85595, by rfl⟩ : syracuseStep 456509 = 171191) (by norm_num)
theorem B456533 : Blo 303832 456533 := bbase (se 9 (by rfl) ⟨1337, by rfl⟩ : syracuseStep 456533 = 2675) (by norm_num)
theorem B685925 : Blo 303832 685925 := bbase (se 4 (by rfl) ⟨64305, by rfl⟩ : syracuseStep 685925 = 128611) (by norm_num)
theorem B456557 : Blo 303832 456557 := bbase (se 3 (by rfl) ⟨85604, by rfl⟩ : syracuseStep 456557 = 171209) (by norm_num)
theorem B456581 : Blo 303832 456581 := bbase (se 4 (by rfl) ⟨42804, by rfl⟩ : syracuseStep 456581 = 85609) (by norm_num)
theorem B456605 : Blo 303832 456605 := bbase (se 3 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 456605 = 171227) (by norm_num)
theorem B685997 : Blo 303832 685997 := bbase (se 3 (by rfl) ⟨128624, by rfl⟩ : syracuseStep 685997 = 257249) (by norm_num)
theorem B456629 : Blo 303832 456629 := bbase (se 5 (by rfl) ⟨21404, by rfl⟩ : syracuseStep 456629 = 42809) (by norm_num)
theorem B456653 : Blo 303832 456653 := bbase (se 3 (by rfl) ⟨85622, by rfl⟩ : syracuseStep 456653 = 171245) (by norm_num)
theorem B456677 : Blo 303832 456677 := bbase (se 4 (by rfl) ⟨42813, by rfl⟩ : syracuseStep 456677 = 85627) (by norm_num)
theorem B686069 : Blo 303832 686069 := bbase (se 5 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 686069 = 64319) (by norm_num)
theorem B489461 : Blo 303832 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B456701 : Blo 303832 456701 := bbase (se 3 (by rfl) ⟨85631, by rfl⟩ : syracuseStep 456701 = 171263) (by norm_num)
theorem B456725 : Blo 303832 456725 := bbase (se 6 (by rfl) ⟨10704, by rfl⟩ : syracuseStep 456725 = 21409) (by norm_num)
theorem B456749 : Blo 303832 456749 := bbase (se 3 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 456749 = 171281) (by norm_num)
theorem B686141 : Blo 303832 686141 := bbase (se 3 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 686141 = 257303) (by norm_num)
theorem B456773 : Blo 303832 456773 := bbase (se 4 (by rfl) ⟨42822, by rfl⟩ : syracuseStep 456773 = 85645) (by norm_num)
theorem B456797 : Blo 303832 456797 := bbase (se 3 (by rfl) ⟨85649, by rfl⟩ : syracuseStep 456797 = 171299) (by norm_num)
theorem B456821 : Blo 303832 456821 := bbase (se 5 (by rfl) ⟨21413, by rfl⟩ : syracuseStep 456821 = 42827) (by norm_num)
theorem B686213 : Blo 303832 686213 := bbase (se 4 (by rfl) ⟨64332, by rfl⟩ : syracuseStep 686213 = 128665) (by norm_num)
theorem B456845 : Blo 303832 456845 := bbase (se 3 (by rfl) ⟨85658, by rfl⟩ : syracuseStep 456845 = 171317) (by norm_num)
theorem B456869 : Blo 303832 456869 := bbase (se 4 (by rfl) ⟨42831, by rfl⟩ : syracuseStep 456869 = 85663) (by norm_num)
theorem B456893 : Blo 303832 456893 := bbase (se 3 (by rfl) ⟨85667, by rfl⟩ : syracuseStep 456893 = 171335) (by norm_num)
theorem B325829 : Blo 303832 325829 := bbase (se 4 (by rfl) ⟨30546, by rfl⟩ : syracuseStep 325829 = 61093) (by norm_num)
theorem B686285 : Blo 303832 686285 := bbase (se 3 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 686285 = 257357) (by norm_num)
theorem B456917 : Blo 303832 456917 := bbase (se 7 (by rfl) ⟨5354, by rfl⟩ : syracuseStep 456917 = 10709) (by norm_num)
theorem B620765 : Blo 303832 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B456941 : Blo 303832 456941 := bbase (se 3 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 456941 = 171353) (by norm_num)
theorem B456965 : Blo 303832 456965 := bbase (se 4 (by rfl) ⟨42840, by rfl⟩ : syracuseStep 456965 = 85681) (by norm_num)
theorem B686357 : Blo 303832 686357 := bbase (se 6 (by rfl) ⟨16086, by rfl⟩ : syracuseStep 686357 = 32173) (by norm_num)
theorem B456989 : Blo 303832 456989 := bbase (se 3 (by rfl) ⟨85685, by rfl⟩ : syracuseStep 456989 = 171371) (by norm_num)
theorem B457013 : Blo 303832 457013 := bbase (se 5 (by rfl) ⟨21422, by rfl⟩ : syracuseStep 457013 = 42845) (by norm_num)
theorem B457037 : Blo 303832 457037 := bbase (se 3 (by rfl) ⟨85694, by rfl⟩ : syracuseStep 457037 = 171389) (by norm_num)
theorem B1603925 : Blo 303832 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B686429 : Blo 303832 686429 := bbase (se 3 (by rfl) ⟨128705, by rfl⟩ : syracuseStep 686429 = 257411) (by norm_num)
theorem B457061 : Blo 303832 457061 := bbase (se 4 (by rfl) ⟨42849, by rfl⟩ : syracuseStep 457061 = 85699) (by norm_num)
theorem B1964405 : Blo 303832 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B457085 : Blo 303832 457085 := bbase (se 3 (by rfl) ⟨85703, by rfl⟩ : syracuseStep 457085 = 171407) (by norm_num)
theorem B457109 : Blo 303832 457109 := bbase (se 6 (by rfl) ⟨10713, by rfl⟩ : syracuseStep 457109 = 21427) (by norm_num)
theorem B686501 : Blo 303832 686501 := bbase (se 4 (by rfl) ⟨64359, by rfl⟩ : syracuseStep 686501 = 128719) (by norm_num)
theorem B457133 : Blo 303832 457133 := bbase (se 3 (by rfl) ⟨85712, by rfl⟩ : syracuseStep 457133 = 171425) (by norm_num)
theorem B1997237 : Blo 303832 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B457157 : Blo 303832 457157 := bbase (se 4 (by rfl) ⟨42858, by rfl⟩ : syracuseStep 457157 = 85717) (by norm_num)
theorem B457181 : Blo 303832 457181 := bbase (se 3 (by rfl) ⟨85721, by rfl⟩ : syracuseStep 457181 = 171443) (by norm_num)
theorem B686573 : Blo 303832 686573 := bbase (se 3 (by rfl) ⟨128732, by rfl⟩ : syracuseStep 686573 = 257465) (by norm_num)
theorem B457205 : Blo 303832 457205 := bbase (se 5 (by rfl) ⟨21431, by rfl⟩ : syracuseStep 457205 = 42863) (by norm_num)
theorem B457229 : Blo 303832 457229 := bbase (se 3 (by rfl) ⟨85730, by rfl⟩ : syracuseStep 457229 = 171461) (by norm_num)
theorem B653845 : Blo 303832 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B457253 : Blo 303832 457253 := bbase (se 4 (by rfl) ⟨42867, by rfl⟩ : syracuseStep 457253 = 85735) (by norm_num)
theorem B686645 : Blo 303832 686645 := bbase (se 5 (by rfl) ⟨32186, by rfl⟩ : syracuseStep 686645 = 64373) (by norm_num)
theorem B457277 : Blo 303832 457277 := bbase (se 3 (by rfl) ⟨85739, by rfl⟩ : syracuseStep 457277 = 171479) (by norm_num)
theorem B457301 : Blo 303832 457301 := bbase (se 8 (by rfl) ⟨2679, by rfl⟩ : syracuseStep 457301 = 5359) (by norm_num)
theorem B457325 : Blo 303832 457325 := bbase (se 3 (by rfl) ⟨85748, by rfl⟩ : syracuseStep 457325 = 171497) (by norm_num)
theorem B686717 : Blo 303832 686717 := bbase (se 3 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 686717 = 257519) (by norm_num)
theorem B326273 : Blo 303832 326273 := bbase (se 2 (by rfl) ⟨122352, by rfl⟩ : syracuseStep 326273 = 244705) (by norm_num)
theorem B457349 : Blo 303832 457349 := bbase (se 4 (by rfl) ⟨42876, by rfl⟩ : syracuseStep 457349 = 85753) (by norm_num)
theorem B457373 : Blo 303832 457373 := bbase (se 3 (by rfl) ⟨85757, by rfl⟩ : syracuseStep 457373 = 171515) (by norm_num)
theorem B490141 : Blo 303832 490141 := bbase (se 3 (by rfl) ⟨91901, by rfl⟩ : syracuseStep 490141 = 183803) (by norm_num)
theorem B457397 : Blo 303832 457397 := bbase (se 5 (by rfl) ⟨21440, by rfl⟩ : syracuseStep 457397 = 42881) (by norm_num)
theorem B686789 : Blo 303832 686789 := bbase (se 4 (by rfl) ⟨64386, by rfl⟩ : syracuseStep 686789 = 128773) (by norm_num)
theorem B457421 : Blo 303832 457421 := bbase (se 3 (by rfl) ⟨85766, by rfl⟩ : syracuseStep 457421 = 171533) (by norm_num)
theorem B391889 : Blo 303832 391889 := bbase (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) (by norm_num)
theorem B490205 : Blo 303832 490205 := bbase (se 3 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 490205 = 183827) (by norm_num)
theorem B457445 : Blo 303832 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B457469 : Blo 303832 457469 := bbase (se 3 (by rfl) ⟨85775, by rfl⟩ : syracuseStep 457469 = 171551) (by norm_num)
theorem B686861 : Blo 303832 686861 := bbase (se 3 (by rfl) ⟨128786, by rfl⟩ : syracuseStep 686861 = 257573) (by norm_num)
theorem B1538837 : Blo 303832 1538837 := bbase (se 6 (by rfl) ⟨36066, by rfl⟩ : syracuseStep 1538837 = 72133) (by norm_num)
theorem B457493 : Blo 303832 457493 := bbase (se 6 (by rfl) ⟨10722, by rfl⟩ : syracuseStep 457493 = 21445) (by norm_num)
theorem B457517 : Blo 303832 457517 := bbase (se 3 (by rfl) ⟨85784, by rfl⟩ : syracuseStep 457517 = 171569) (by norm_num)
theorem B457541 : Blo 303832 457541 := bbase (se 4 (by rfl) ⟨42894, by rfl⟩ : syracuseStep 457541 = 85789) (by norm_num)
theorem B686933 : Blo 303832 686933 := bbase (se 9 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 686933 = 4025) (by norm_num)
theorem B981845 : Blo 303832 981845 := bbase (se 9 (by rfl) ⟨2876, by rfl⟩ : syracuseStep 981845 = 5753) (by norm_num)
theorem B457565 : Blo 303832 457565 := bbase (se 3 (by rfl) ⟨85793, by rfl⟩ : syracuseStep 457565 = 171587) (by norm_num)
theorem B457589 : Blo 303832 457589 := bbase (se 5 (by rfl) ⟨21449, by rfl⟩ : syracuseStep 457589 = 42899) (by norm_num)
theorem B326521 : Blo 303832 326521 := bbase (se 2 (by rfl) ⟨122445, by rfl⟩ : syracuseStep 326521 = 244891) (by norm_num)
theorem B621437 : Blo 303832 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B457613 : Blo 303832 457613 := bbase (se 3 (by rfl) ⟨85802, by rfl⟩ : syracuseStep 457613 = 171605) (by norm_num)
theorem B687005 : Blo 303832 687005 := bbase (se 3 (by rfl) ⟨128813, by rfl⟩ : syracuseStep 687005 = 257627) (by norm_num)
theorem B457637 : Blo 303832 457637 := bbase (se 4 (by rfl) ⟨42903, by rfl⟩ : syracuseStep 457637 = 85807) (by norm_num)
theorem B457661 : Blo 303832 457661 := bbase (se 3 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 457661 = 171623) (by norm_num)
theorem B457685 : Blo 303832 457685 := bbase (se 7 (by rfl) ⟨5363, by rfl⟩ : syracuseStep 457685 = 10727) (by norm_num)
theorem B687077 : Blo 303832 687077 := bbase (se 4 (by rfl) ⟨64413, by rfl⟩ : syracuseStep 687077 = 128827) (by norm_num)
theorem B457709 : Blo 303832 457709 := bbase (se 3 (by rfl) ⟨85820, by rfl⟩ : syracuseStep 457709 = 171641) (by norm_num)
theorem B457733 : Blo 303832 457733 := bbase (se 4 (by rfl) ⟨42912, by rfl⟩ : syracuseStep 457733 = 85825) (by norm_num)
theorem B457757 : Blo 303832 457757 := bbase (se 3 (by rfl) ⟨85829, by rfl⟩ : syracuseStep 457757 = 171659) (by norm_num)
theorem B687149 : Blo 303832 687149 := bbase (se 3 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 687149 = 257681) (by norm_num)
theorem B457781 : Blo 303832 457781 := bbase (se 5 (by rfl) ⟨21458, by rfl⟩ : syracuseStep 457781 = 42917) (by norm_num)
theorem B457805 : Blo 303832 457805 := bbase (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) (by norm_num)
theorem B457829 : Blo 303832 457829 := bbase (se 4 (by rfl) ⟨42921, by rfl⟩ : syracuseStep 457829 = 85843) (by norm_num)
theorem B687221 : Blo 303832 687221 := bbase (se 5 (by rfl) ⟨32213, by rfl⟩ : syracuseStep 687221 = 64427) (by norm_num)
theorem B457853 : Blo 303832 457853 := bbase (se 3 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 457853 = 171695) (by norm_num)
theorem B457877 : Blo 303832 457877 := bbase (se 6 (by rfl) ⟨10731, by rfl⟩ : syracuseStep 457877 = 21463) (by norm_num)
theorem B457901 : Blo 303832 457901 := bbase (se 3 (by rfl) ⟨85856, by rfl⟩ : syracuseStep 457901 = 171713) (by norm_num)
theorem B1309877 : Blo 303832 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B687293 : Blo 303832 687293 := bbase (se 3 (by rfl) ⟨128867, by rfl⟩ : syracuseStep 687293 = 257735) (by norm_num)
theorem B457925 : Blo 303832 457925 := bbase (se 4 (by rfl) ⟨42930, by rfl⟩ : syracuseStep 457925 = 85861) (by norm_num)
theorem B457949 : Blo 303832 457949 := bbase (se 3 (by rfl) ⟨85865, by rfl⟩ : syracuseStep 457949 = 171731) (by norm_num)
theorem B457973 : Blo 303832 457973 := bbase (se 5 (by rfl) ⟨21467, by rfl⟩ : syracuseStep 457973 = 42935) (by norm_num)
theorem B687365 : Blo 303832 687365 := bbase (se 4 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 687365 = 128881) (by norm_num)
theorem B457997 : Blo 303832 457997 := bbase (se 3 (by rfl) ⟨85874, by rfl⟩ : syracuseStep 457997 = 171749) (by norm_num)
theorem B458021 : Blo 303832 458021 := bbase (se 4 (by rfl) ⟨42939, by rfl⟩ : syracuseStep 458021 = 85879) (by norm_num)
theorem B326953 : Blo 303832 326953 := bbase (se 2 (by rfl) ⟨122607, by rfl⟩ : syracuseStep 326953 = 245215) (by norm_num)
theorem B458045 : Blo 303832 458045 := bbase (se 3 (by rfl) ⟨85883, by rfl⟩ : syracuseStep 458045 = 171767) (by norm_num)
theorem B687437 : Blo 303832 687437 := bbase (se 3 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 687437 = 257789) (by norm_num)
theorem B7142741 : Blo 303832 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B458069 : Blo 303832 458069 := bbase (se 11 (by rfl) ⟨335, by rfl⟩ : syracuseStep 458069 = 671) (by norm_num)
theorem B458093 : Blo 303832 458093 := bbase (se 3 (by rfl) ⟨85892, by rfl⟩ : syracuseStep 458093 = 171785) (by norm_num)
theorem B327025 : Blo 303832 327025 := bbase (se 2 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 327025 = 245269) (by norm_num)
theorem B458117 : Blo 303832 458117 := bbase (se 4 (by rfl) ⟨42948, by rfl⟩ : syracuseStep 458117 = 85897) (by norm_num)
theorem B654733 : Blo 303832 654733 := bbase (se 3 (by rfl) ⟨122762, by rfl⟩ : syracuseStep 654733 = 245525) (by norm_num)
theorem B687509 : Blo 303832 687509 := bbase (se 6 (by rfl) ⟨16113, by rfl⟩ : syracuseStep 687509 = 32227) (by norm_num)
theorem B458141 : Blo 303832 458141 := bbase (se 3 (by rfl) ⟨85901, by rfl⟩ : syracuseStep 458141 = 171803) (by norm_num)
theorem B458165 : Blo 303832 458165 := bbase (se 5 (by rfl) ⟨21476, by rfl⟩ : syracuseStep 458165 = 42953) (by norm_num)
theorem B458189 : Blo 303832 458189 := bbase (se 3 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 458189 = 171821) (by norm_num)
theorem B687581 : Blo 303832 687581 := bbase (se 3 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 687581 = 257843) (by norm_num)
theorem B458213 : Blo 303832 458213 := bbase (se 4 (by rfl) ⟨42957, by rfl⟩ : syracuseStep 458213 = 85915) (by norm_num)
theorem B458237 : Blo 303832 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B458261 : Blo 303832 458261 := bbase (se 6 (by rfl) ⟨10740, by rfl⟩ : syracuseStep 458261 = 21481) (by norm_num)
theorem B687653 : Blo 303832 687653 := bbase (se 4 (by rfl) ⟨64467, by rfl⟩ : syracuseStep 687653 = 128935) (by norm_num)
theorem B458285 : Blo 303832 458285 := bbase (se 3 (by rfl) ⟨85928, by rfl⟩ : syracuseStep 458285 = 171857) (by norm_num)
theorem B458309 : Blo 303832 458309 := bbase (se 4 (by rfl) ⟨42966, by rfl⟩ : syracuseStep 458309 = 85933) (by norm_num)
theorem B982613 : Blo 303832 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B458333 : Blo 303832 458333 := bbase (se 3 (by rfl) ⟨85937, by rfl⟩ : syracuseStep 458333 = 171875) (by norm_num)
theorem B687725 : Blo 303832 687725 := bbase (se 3 (by rfl) ⟨128948, by rfl⟩ : syracuseStep 687725 = 257897) (by norm_num)
theorem B458357 : Blo 303832 458357 := bbase (se 5 (by rfl) ⟨21485, by rfl⟩ : syracuseStep 458357 = 42971) (by norm_num)
theorem B458381 : Blo 303832 458381 := bbase (se 3 (by rfl) ⟨85946, by rfl⟩ : syracuseStep 458381 = 171893) (by norm_num)
theorem B458405 : Blo 303832 458405 := bbase (se 4 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 458405 = 85951) (by norm_num)
theorem B687797 : Blo 303832 687797 := bbase (se 5 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 687797 = 64481) (by norm_num)
theorem B458429 : Blo 303832 458429 := bbase (se 3 (by rfl) ⟨85955, by rfl⟩ : syracuseStep 458429 = 171911) (by norm_num)
theorem B458453 : Blo 303832 458453 := bbase (se 7 (by rfl) ⟨5372, by rfl⟩ : syracuseStep 458453 = 10745) (by norm_num)
theorem B327397 : Blo 303832 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B458477 : Blo 303832 458477 := bbase (se 3 (by rfl) ⟨85964, by rfl⟩ : syracuseStep 458477 = 171929) (by norm_num)
theorem B687869 : Blo 303832 687869 := bbase (se 3 (by rfl) ⟨128975, by rfl⟩ : syracuseStep 687869 = 257951) (by norm_num)
theorem B458501 : Blo 303832 458501 := bbase (se 4 (by rfl) ⟨42984, by rfl⟩ : syracuseStep 458501 = 85969) (by norm_num)
theorem B786181 : Blo 303832 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B458525 : Blo 303832 458525 := bbase (se 3 (by rfl) ⟨85973, by rfl⟩ : syracuseStep 458525 = 171947) (by norm_num)
theorem B458549 : Blo 303832 458549 := bbase (se 5 (by rfl) ⟨21494, by rfl⟩ : syracuseStep 458549 = 42989) (by norm_num)
theorem B687941 : Blo 303832 687941 := bbase (se 4 (by rfl) ⟨64494, by rfl⟩ : syracuseStep 687941 = 128989) (by norm_num)
theorem B458573 : Blo 303832 458573 := bbase (se 3 (by rfl) ⟨85982, by rfl⟩ : syracuseStep 458573 = 171965) (by norm_num)
theorem B458597 : Blo 303832 458597 := bbase (se 4 (by rfl) ⟨42993, by rfl⟩ : syracuseStep 458597 = 85987) (by norm_num)
theorem B655229 : Blo 303832 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B458621 : Blo 303832 458621 := bbase (se 3 (by rfl) ⟨85991, by rfl⟩ : syracuseStep 458621 = 171983) (by norm_num)
theorem B688013 : Blo 303832 688013 := bbase (se 3 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 688013 = 258005) (by norm_num)
theorem B3899285 : Blo 303832 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B458645 : Blo 303832 458645 := bbase (se 6 (by rfl) ⟨10749, by rfl⟩ : syracuseStep 458645 = 21499) (by norm_num)
theorem B458669 : Blo 303832 458669 := bbase (se 3 (by rfl) ⟨86000, by rfl⟩ : syracuseStep 458669 = 172001) (by norm_num)
theorem B458693 : Blo 303832 458693 := bbase (se 4 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 458693 = 86005) (by norm_num)
theorem B688085 : Blo 303832 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B1474517 : Blo 303832 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B458717 : Blo 303832 458717 := bbase (se 3 (by rfl) ⟨86009, by rfl⟩ : syracuseStep 458717 = 172019) (by norm_num)
theorem B458741 : Blo 303832 458741 := bbase (se 5 (by rfl) ⟨21503, by rfl⟩ : syracuseStep 458741 = 43007) (by norm_num)
theorem B458753 : Blo 303832 458753 := bstep (se 2 (by rfl) ⟨172032, by rfl⟩ : syracuseStep 458753 = 344065) B344065
theorem B327683 : Blo 303832 327683 := bstep (se 1 (by rfl) ⟨245762, by rfl⟩ : syracuseStep 327683 = 491525) B491525
theorem B458771 : Blo 303832 458771 := bstep (se 1 (by rfl) ⟨344078, by rfl⟩ : syracuseStep 458771 = 688157) B688157
theorem B458801 : Blo 303832 458801 := bstep (se 2 (by rfl) ⟨172050, by rfl⟩ : syracuseStep 458801 = 344101) B344101
theorem B458819 : Blo 303832 458819 := bstep (se 1 (by rfl) ⟨344114, by rfl⟩ : syracuseStep 458819 = 688229) B688229
theorem B458849 : Blo 303832 458849 := bstep (se 2 (by rfl) ⟨172068, by rfl⟩ : syracuseStep 458849 = 344137) B344137
theorem B1310833 : Blo 303832 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B458867 : Blo 303832 458867 := bstep (se 1 (by rfl) ⟨344150, by rfl⟩ : syracuseStep 458867 = 688301) B688301
theorem B327811 : Blo 303832 327811 := bstep (se 1 (by rfl) ⟨245858, by rfl⟩ : syracuseStep 327811 = 491717) B491717
theorem B458897 : Blo 303832 458897 := bstep (se 2 (by rfl) ⟨172086, by rfl⟩ : syracuseStep 458897 = 344173) B344173
theorem B458915 : Blo 303832 458915 := bstep (se 1 (by rfl) ⟨344186, by rfl⟩ : syracuseStep 458915 = 688373) B688373
theorem B458945 : Blo 303832 458945 := bstep (se 2 (by rfl) ⟨172104, by rfl⟩ : syracuseStep 458945 = 344209) B344209
theorem B688337 : Blo 303832 688337 := bstep (se 2 (by rfl) ⟨258126, by rfl⟩ : syracuseStep 688337 = 516253) B516253
theorem B458963 : Blo 303832 458963 := bstep (se 1 (by rfl) ⟨344222, by rfl⟩ : syracuseStep 458963 = 688445) B688445
theorem B688355 : Blo 303832 688355 := bstep (se 1 (by rfl) ⟨516266, by rfl⟩ : syracuseStep 688355 = 1032533) B1032533
theorem B458993 : Blo 303832 458993 := bstep (se 2 (by rfl) ⟨172122, by rfl⟩ : syracuseStep 458993 = 344245) B344245
theorem B459011 : Blo 303832 459011 := bstep (se 1 (by rfl) ⟨344258, by rfl⟩ : syracuseStep 459011 = 688517) B688517
theorem B459041 : Blo 303832 459041 := bstep (se 2 (by rfl) ⟨172140, by rfl⟩ : syracuseStep 459041 = 344281) B344281
theorem B459059 : Blo 303832 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B459089 : Blo 303832 459089 := bstep (se 2 (by rfl) ⟨172158, by rfl⟩ : syracuseStep 459089 = 344317) B344317
theorem B459107 : Blo 303832 459107 := bstep (se 1 (by rfl) ⟨344330, by rfl⟩ : syracuseStep 459107 = 688661) B688661
theorem B459137 : Blo 303832 459137 := bstep (se 2 (by rfl) ⟨172176, by rfl⟩ : syracuseStep 459137 = 344353) B344353
theorem B459155 : Blo 303832 459155 := bstep (se 1 (by rfl) ⟨344366, by rfl⟩ : syracuseStep 459155 = 688733) B688733
theorem B459185 : Blo 303832 459185 := bstep (se 2 (by rfl) ⟨172194, by rfl⟩ : syracuseStep 459185 = 344389) B344389
theorem B655793 : Blo 303832 655793 := bstep (se 2 (by rfl) ⟨245922, by rfl⟩ : syracuseStep 655793 = 491845) B491845
theorem B459203 : Blo 303832 459203 := bstep (se 1 (by rfl) ⟨344402, by rfl⟩ : syracuseStep 459203 = 688805) B688805
theorem B459233 : Blo 303832 459233 := bstep (se 2 (by rfl) ⟨172212, by rfl⟩ : syracuseStep 459233 = 344425) B344425
theorem B688625 : Blo 303832 688625 := bstep (se 2 (by rfl) ⟨258234, by rfl⟩ : syracuseStep 688625 = 516469) B516469
theorem B459251 : Blo 303832 459251 := bstep (se 1 (by rfl) ⟨344438, by rfl⟩ : syracuseStep 459251 = 688877) B688877
theorem B688643 : Blo 303832 688643 := bstep (se 1 (by rfl) ⟨516482, by rfl⟩ : syracuseStep 688643 = 1032965) B1032965
theorem B459281 : Blo 303832 459281 := bstep (se 2 (by rfl) ⟨172230, by rfl⟩ : syracuseStep 459281 = 344461) B344461
theorem B459299 : Blo 303832 459299 := bstep (se 1 (by rfl) ⟨344474, by rfl⟩ : syracuseStep 459299 = 688949) B688949
theorem B459329 : Blo 303832 459329 := bstep (se 2 (by rfl) ⟨172248, by rfl⟩ : syracuseStep 459329 = 344497) B344497
theorem B459347 : Blo 303832 459347 := bstep (se 1 (by rfl) ⟨344510, by rfl⟩ : syracuseStep 459347 = 689021) B689021
theorem B459377 : Blo 303832 459377 := bstep (se 2 (by rfl) ⟨172266, by rfl⟩ : syracuseStep 459377 = 344533) B344533
theorem B459395 : Blo 303832 459395 := bstep (se 1 (by rfl) ⟨344546, by rfl⟩ : syracuseStep 459395 = 689093) B689093
theorem B6390413 : Blo 303832 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B459425 : Blo 303832 459425 := bstep (se 2 (by rfl) ⟨172284, by rfl⟩ : syracuseStep 459425 = 344569) B344569
theorem B459443 : Blo 303832 459443 := bstep (se 1 (by rfl) ⟨344582, by rfl⟩ : syracuseStep 459443 = 689165) B689165
theorem B459473 : Blo 303832 459473 := bstep (se 2 (by rfl) ⟨172302, by rfl⟩ : syracuseStep 459473 = 344605) B344605
theorem B459491 : Blo 303832 459491 := bstep (se 1 (by rfl) ⟨344618, by rfl⟩ : syracuseStep 459491 = 689237) B689237
theorem B459521 : Blo 303832 459521 := bstep (se 2 (by rfl) ⟨172320, by rfl⟩ : syracuseStep 459521 = 344641) B344641
theorem B688913 : Blo 303832 688913 := bstep (se 2 (by rfl) ⟨258342, by rfl⟩ : syracuseStep 688913 = 516685) B516685
theorem B459539 : Blo 303832 459539 := bstep (se 1 (by rfl) ⟨344654, by rfl⟩ : syracuseStep 459539 = 689309) B689309
theorem B688931 : Blo 303832 688931 := bstep (se 1 (by rfl) ⟨516698, by rfl⟩ : syracuseStep 688931 = 1033397) B1033397
theorem B983843 : Blo 303832 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B459569 : Blo 303832 459569 := bstep (se 2 (by rfl) ⟨172338, by rfl⟩ : syracuseStep 459569 = 344677) B344677
theorem B459587 : Blo 303832 459587 := bstep (se 1 (by rfl) ⟨344690, by rfl⟩ : syracuseStep 459587 = 689381) B689381
theorem B459617 : Blo 303832 459617 := bstep (se 2 (by rfl) ⟨172356, by rfl⟩ : syracuseStep 459617 = 344713) B344713
theorem B1737571 : Blo 303832 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B2786147 : Blo 303832 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1475441 : Blo 303832 1475441 := bstep (se 2 (by rfl) ⟨553290, by rfl⟩ : syracuseStep 1475441 = 1106581) B1106581
theorem B459635 : Blo 303832 459635 := bstep (se 1 (by rfl) ⟨344726, by rfl⟩ : syracuseStep 459635 = 689453) B689453
theorem B459665 : Blo 303832 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B459683 : Blo 303832 459683 := bstep (se 1 (by rfl) ⟨344762, by rfl⟩ : syracuseStep 459683 = 689525) B689525
theorem B328627 : Blo 303832 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B459713 : Blo 303832 459713 := bstep (se 2 (by rfl) ⟨172392, by rfl⟩ : syracuseStep 459713 = 344785) B344785
theorem B459731 : Blo 303832 459731 := bstep (se 1 (by rfl) ⟨344798, by rfl⟩ : syracuseStep 459731 = 689597) B689597
theorem B1541105 : Blo 303832 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B459761 : Blo 303832 459761 := bstep (se 2 (by rfl) ⟨172410, by rfl⟩ : syracuseStep 459761 = 344821) B344821
theorem B459779 : Blo 303832 459779 := bstep (se 1 (by rfl) ⟨344834, by rfl⟩ : syracuseStep 459779 = 689669) B689669
theorem B492563 : Blo 303832 492563 := bstep (se 1 (by rfl) ⟨369422, by rfl⟩ : syracuseStep 492563 = 738845) B738845
theorem B459809 : Blo 303832 459809 := bstep (se 2 (by rfl) ⟨172428, by rfl⟩ : syracuseStep 459809 = 344857) B344857
theorem B689201 : Blo 303832 689201 := bstep (se 2 (by rfl) ⟨258450, by rfl⟩ : syracuseStep 689201 = 516901) B516901
theorem B459827 : Blo 303832 459827 := bstep (se 1 (by rfl) ⟨344870, by rfl⟩ : syracuseStep 459827 = 689741) B689741
theorem B689219 : Blo 303832 689219 := bstep (se 1 (by rfl) ⟨516914, by rfl⟩ : syracuseStep 689219 = 1033829) B1033829
theorem B459857 : Blo 303832 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B459875 : Blo 303832 459875 := bstep (se 1 (by rfl) ⟨344906, by rfl⟩ : syracuseStep 459875 = 689813) B689813
theorem B459905 : Blo 303832 459905 := bstep (se 2 (by rfl) ⟨172464, by rfl⟩ : syracuseStep 459905 = 344929) B344929
theorem B459923 : Blo 303832 459923 := bstep (se 1 (by rfl) ⟨344942, by rfl⟩ : syracuseStep 459923 = 689885) B689885
theorem B459953 : Blo 303832 459953 := bstep (se 2 (by rfl) ⟨172482, by rfl⟩ : syracuseStep 459953 = 344965) B344965
theorem B984241 : Blo 303832 984241 := bstep (se 2 (by rfl) ⟨369090, by rfl⟩ : syracuseStep 984241 = 738181) B738181
theorem B459971 : Blo 303832 459971 := bstep (se 1 (by rfl) ⟨344978, by rfl⟩ : syracuseStep 459971 = 689957) B689957
theorem B656579 : Blo 303832 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B460001 : Blo 303832 460001 := bstep (se 2 (by rfl) ⟨172500, by rfl⟩ : syracuseStep 460001 = 345001) B345001
theorem B885997 : Blo 303832 885997 := bstep (se 3 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 885997 = 332249) B332249
theorem B984305 : Blo 303832 984305 := bstep (se 2 (by rfl) ⟨369114, by rfl⟩ : syracuseStep 984305 = 738229) B738229
theorem B460019 : Blo 303832 460019 := bstep (se 1 (by rfl) ⟨345014, by rfl⟩ : syracuseStep 460019 = 690029) B690029
theorem B460049 : Blo 303832 460049 := bstep (se 2 (by rfl) ⟨172518, by rfl⟩ : syracuseStep 460049 = 345037) B345037
theorem B460067 : Blo 303832 460067 := bstep (se 1 (by rfl) ⟨345050, by rfl⟩ : syracuseStep 460067 = 690101) B690101
theorem B460097 : Blo 303832 460097 := bstep (se 2 (by rfl) ⟨172536, by rfl⟩ : syracuseStep 460097 = 345073) B345073
theorem B689489 : Blo 303832 689489 := bstep (se 2 (by rfl) ⟨258558, by rfl⟩ : syracuseStep 689489 = 517117) B517117
theorem B460115 : Blo 303832 460115 := bstep (se 1 (by rfl) ⟨345086, by rfl⟩ : syracuseStep 460115 = 690173) B690173
theorem B689507 : Blo 303832 689507 := bstep (se 1 (by rfl) ⟨517130, by rfl⟩ : syracuseStep 689507 = 1034261) B1034261
theorem B1738097 : Blo 303832 1738097 := bstep (se 2 (by rfl) ⟨651786, by rfl⟩ : syracuseStep 1738097 = 1303573) B1303573
theorem B460145 : Blo 303832 460145 := bstep (se 2 (by rfl) ⟨172554, by rfl⟩ : syracuseStep 460145 = 345109) B345109
theorem B460163 : Blo 303832 460163 := bstep (se 1 (by rfl) ⟨345122, by rfl⟩ : syracuseStep 460163 = 690245) B690245
theorem B492947 : Blo 303832 492947 := bstep (se 1 (by rfl) ⟨369710, by rfl⟩ : syracuseStep 492947 = 739421) B739421
theorem B460193 : Blo 303832 460193 := bstep (se 2 (by rfl) ⟨172572, by rfl⟩ : syracuseStep 460193 = 345145) B345145
theorem B460211 : Blo 303832 460211 := bstep (se 1 (by rfl) ⟨345158, by rfl⟩ : syracuseStep 460211 = 690317) B690317
theorem B460241 : Blo 303832 460241 := bstep (se 2 (by rfl) ⟨172590, by rfl⟩ : syracuseStep 460241 = 345181) B345181
theorem B460259 : Blo 303832 460259 := bstep (se 1 (by rfl) ⟨345194, by rfl⟩ : syracuseStep 460259 = 690389) B690389
theorem B460289 : Blo 303832 460289 := bstep (se 2 (by rfl) ⟨172608, by rfl⟩ : syracuseStep 460289 = 345217) B345217
theorem B460307 : Blo 303832 460307 := bstep (se 1 (by rfl) ⟨345230, by rfl⟩ : syracuseStep 460307 = 690461) B690461
theorem B493075 : Blo 303832 493075 := bstep (se 1 (by rfl) ⟨369806, by rfl⟩ : syracuseStep 493075 = 739613) B739613
theorem B460337 : Blo 303832 460337 := bstep (se 2 (by rfl) ⟨172626, by rfl⟩ : syracuseStep 460337 = 345253) B345253
theorem B460355 : Blo 303832 460355 := bstep (se 1 (by rfl) ⟨345266, by rfl⟩ : syracuseStep 460355 = 690533) B690533
theorem B460385 : Blo 303832 460385 := bstep (se 2 (by rfl) ⟨172644, by rfl⟩ : syracuseStep 460385 = 345289) B345289
theorem B689777 : Blo 303832 689777 := bstep (se 2 (by rfl) ⟨258666, by rfl⟩ : syracuseStep 689777 = 517333) B517333
theorem B460403 : Blo 303832 460403 := bstep (se 1 (by rfl) ⟨345302, by rfl⟩ : syracuseStep 460403 = 690605) B690605
theorem B689795 : Blo 303832 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B460433 : Blo 303832 460433 := bstep (se 2 (by rfl) ⟨172662, by rfl⟩ : syracuseStep 460433 = 345325) B345325
theorem B460451 : Blo 303832 460451 := bstep (se 1 (by rfl) ⟨345338, by rfl⟩ : syracuseStep 460451 = 690677) B690677
theorem B460481 : Blo 303832 460481 := bstep (se 2 (by rfl) ⟨172680, by rfl⟩ : syracuseStep 460481 = 345361) B345361
theorem B6620869 : Blo 303832 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B460499 : Blo 303832 460499 := bstep (se 1 (by rfl) ⟨345374, by rfl⟩ : syracuseStep 460499 = 690749) B690749
theorem B460529 : Blo 303832 460529 := bstep (se 2 (by rfl) ⟨172698, by rfl⟩ : syracuseStep 460529 = 345397) B345397
theorem B460547 : Blo 303832 460547 := bstep (se 1 (by rfl) ⟨345410, by rfl⟩ : syracuseStep 460547 = 690821) B690821
theorem B460577 : Blo 303832 460577 := bstep (se 2 (by rfl) ⟨172716, by rfl⟩ : syracuseStep 460577 = 345433) B345433
theorem B493361 : Blo 303832 493361 := bstep (se 2 (by rfl) ⟨185010, by rfl⟩ : syracuseStep 493361 = 370021) B370021
theorem B460595 : Blo 303832 460595 := bstep (se 1 (by rfl) ⟨345446, by rfl⟩ : syracuseStep 460595 = 690893) B690893
theorem B460625 : Blo 303832 460625 := bstep (se 2 (by rfl) ⟨172734, by rfl⟩ : syracuseStep 460625 = 345469) B345469
theorem B460643 : Blo 303832 460643 := bstep (se 1 (by rfl) ⟨345482, by rfl⟩ : syracuseStep 460643 = 690965) B690965
theorem B460673 : Blo 303832 460673 := bstep (se 2 (by rfl) ⟨172752, by rfl⟩ : syracuseStep 460673 = 345505) B345505
theorem B690065 : Blo 303832 690065 := bstep (se 2 (by rfl) ⟨258774, by rfl⟩ : syracuseStep 690065 = 517549) B517549
theorem B460691 : Blo 303832 460691 := bstep (se 1 (by rfl) ⟨345518, by rfl⟩ : syracuseStep 460691 = 691037) B691037
theorem B690083 : Blo 303832 690083 := bstep (se 1 (by rfl) ⟨517562, by rfl⟩ : syracuseStep 690083 = 1035125) B1035125
theorem B460721 : Blo 303832 460721 := bstep (se 2 (by rfl) ⟨172770, by rfl⟩ : syracuseStep 460721 = 345541) B345541
theorem B460739 : Blo 303832 460739 := bstep (se 1 (by rfl) ⟨345554, by rfl⟩ : syracuseStep 460739 = 691109) B691109
theorem B460769 : Blo 303832 460769 := bstep (se 2 (by rfl) ⟨172788, by rfl⟩ : syracuseStep 460769 = 345577) B345577
theorem B460787 : Blo 303832 460787 := bstep (se 1 (by rfl) ⟨345590, by rfl⟩ : syracuseStep 460787 = 691181) B691181
theorem B460817 : Blo 303832 460817 := bstep (se 2 (by rfl) ⟨172806, by rfl⟩ : syracuseStep 460817 = 345613) B345613
theorem B460835 : Blo 303832 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B460865 : Blo 303832 460865 := bstep (se 2 (by rfl) ⟨172824, by rfl⟩ : syracuseStep 460865 = 345649) B345649
theorem B460883 : Blo 303832 460883 := bstep (se 1 (by rfl) ⟨345662, by rfl⟩ : syracuseStep 460883 = 691325) B691325
theorem B460913 : Blo 303832 460913 := bstep (se 2 (by rfl) ⟨172842, by rfl⟩ : syracuseStep 460913 = 345685) B345685
theorem B460931 : Blo 303832 460931 := bstep (se 1 (by rfl) ⟨345698, by rfl⟩ : syracuseStep 460931 = 691397) B691397
theorem B460961 : Blo 303832 460961 := bstep (se 2 (by rfl) ⟨172860, by rfl⟩ : syracuseStep 460961 = 345721) B345721
theorem B690353 : Blo 303832 690353 := bstep (se 2 (by rfl) ⟨258882, by rfl⟩ : syracuseStep 690353 = 517765) B517765
theorem B460979 : Blo 303832 460979 := bstep (se 1 (by rfl) ⟨345734, by rfl⟩ : syracuseStep 460979 = 691469) B691469
theorem B690371 : Blo 303832 690371 := bstep (se 1 (by rfl) ⟨517778, by rfl⟩ : syracuseStep 690371 = 1035557) B1035557
theorem B461009 : Blo 303832 461009 := bstep (se 2 (by rfl) ⟨172878, by rfl⟩ : syracuseStep 461009 = 345757) B345757
theorem B461027 : Blo 303832 461027 := bstep (se 1 (by rfl) ⟨345770, by rfl⟩ : syracuseStep 461027 = 691541) B691541
theorem B461057 : Blo 303832 461057 := bstep (se 2 (by rfl) ⟨172896, by rfl⟩ : syracuseStep 461057 = 345793) B345793
theorem B461075 : Blo 303832 461075 := bstep (se 1 (by rfl) ⟨345806, by rfl⟩ : syracuseStep 461075 = 691613) B691613
theorem B461105 : Blo 303832 461105 := bstep (se 2 (by rfl) ⟨172914, by rfl⟩ : syracuseStep 461105 = 345829) B345829
theorem B461123 : Blo 303832 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B461153 : Blo 303832 461153 := bstep (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) B345865
theorem B461171 : Blo 303832 461171 := bstep (se 1 (by rfl) ⟨345878, by rfl⟩ : syracuseStep 461171 = 691757) B691757
theorem B461201 : Blo 303832 461201 := bstep (se 2 (by rfl) ⟨172950, by rfl⟩ : syracuseStep 461201 = 345901) B345901
theorem B1542563 : Blo 303832 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B461219 : Blo 303832 461219 := bstep (se 1 (by rfl) ⟨345914, by rfl⟩ : syracuseStep 461219 = 691829) B691829
theorem B461249 : Blo 303832 461249 := bstep (se 2 (by rfl) ⟨172968, by rfl⟩ : syracuseStep 461249 = 345937) B345937
theorem B690641 : Blo 303832 690641 := bstep (se 2 (by rfl) ⟨258990, by rfl⟩ : syracuseStep 690641 = 517981) B517981
theorem B461267 : Blo 303832 461267 := bstep (se 1 (by rfl) ⟨345950, by rfl⟩ : syracuseStep 461267 = 691901) B691901
theorem B690659 : Blo 303832 690659 := bstep (se 1 (by rfl) ⟨517994, by rfl⟩ : syracuseStep 690659 = 1035989) B1035989
theorem B461297 : Blo 303832 461297 := bstep (se 2 (by rfl) ⟨172986, by rfl⟩ : syracuseStep 461297 = 345973) B345973
theorem B461315 : Blo 303832 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B461345 : Blo 303832 461345 := bstep (se 2 (by rfl) ⟨173004, by rfl⟩ : syracuseStep 461345 = 346009) B346009
theorem B461363 : Blo 303832 461363 := bstep (se 1 (by rfl) ⟨346022, by rfl⟩ : syracuseStep 461363 = 692045) B692045
theorem B461393 : Blo 303832 461393 := bstep (se 2 (by rfl) ⟨173022, by rfl⟩ : syracuseStep 461393 = 346045) B346045
theorem B461411 : Blo 303832 461411 := bstep (se 1 (by rfl) ⟨346058, by rfl⟩ : syracuseStep 461411 = 692117) B692117
theorem B461441 : Blo 303832 461441 := bstep (se 2 (by rfl) ⟨173040, by rfl⟩ : syracuseStep 461441 = 346081) B346081
theorem B461459 : Blo 303832 461459 := bstep (se 1 (by rfl) ⟨346094, by rfl⟩ : syracuseStep 461459 = 692189) B692189
theorem B461489 : Blo 303832 461489 := bstep (se 2 (by rfl) ⟨173058, by rfl⟩ : syracuseStep 461489 = 346117) B346117
theorem B461507 : Blo 303832 461507 := bstep (se 1 (by rfl) ⟨346130, by rfl⟩ : syracuseStep 461507 = 692261) B692261
theorem B461537 : Blo 303832 461537 := bstep (se 2 (by rfl) ⟨173076, by rfl⟩ : syracuseStep 461537 = 346153) B346153
theorem B690929 : Blo 303832 690929 := bstep (se 2 (by rfl) ⟨259098, by rfl⟩ : syracuseStep 690929 = 518197) B518197
theorem B461555 : Blo 303832 461555 := bstep (se 1 (by rfl) ⟨346166, by rfl⟩ : syracuseStep 461555 = 692333) B692333
theorem B690947 : Blo 303832 690947 := bstep (se 1 (by rfl) ⟨518210, by rfl⟩ : syracuseStep 690947 = 1036421) B1036421
theorem B461585 : Blo 303832 461585 := bstep (se 2 (by rfl) ⟨173094, by rfl⟩ : syracuseStep 461585 = 346189) B346189
theorem B1739555 : Blo 303832 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B461603 : Blo 303832 461603 := bstep (se 1 (by rfl) ⟨346202, by rfl⟩ : syracuseStep 461603 = 692405) B692405
theorem B461633 : Blo 303832 461633 := bstep (se 2 (by rfl) ⟨173112, by rfl⟩ : syracuseStep 461633 = 346225) B346225
theorem B461651 : Blo 303832 461651 := bstep (se 1 (by rfl) ⟨346238, by rfl⟩ : syracuseStep 461651 = 692477) B692477
theorem B461681 : Blo 303832 461681 := bstep (se 2 (by rfl) ⟨173130, by rfl⟩ : syracuseStep 461681 = 346261) B346261
theorem B461699 : Blo 303832 461699 := bstep (se 1 (by rfl) ⟨346274, by rfl⟩ : syracuseStep 461699 = 692549) B692549
theorem B625553 : Blo 303832 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B461729 : Blo 303832 461729 := bstep (se 2 (by rfl) ⟨173148, by rfl⟩ : syracuseStep 461729 = 346297) B346297
theorem B461747 : Blo 303832 461747 := bstep (se 1 (by rfl) ⟨346310, by rfl⟩ : syracuseStep 461747 = 692621) B692621
theorem B691217 : Blo 303832 691217 := bstep (se 2 (by rfl) ⟨259206, by rfl⟩ : syracuseStep 691217 = 518413) B518413
theorem B691235 : Blo 303832 691235 := bstep (se 1 (by rfl) ⟨518426, by rfl⟩ : syracuseStep 691235 = 1036853) B1036853
theorem B1543373 : Blo 303832 1543373 := bstep (se 3 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 1543373 = 578765) B578765
theorem B1969379 : Blo 303832 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B691505 : Blo 303832 691505 := bstep (se 2 (by rfl) ⟨259314, by rfl⟩ : syracuseStep 691505 = 518629) B518629
theorem B691523 : Blo 303832 691523 := bstep (se 1 (by rfl) ⟨518642, by rfl⟩ : syracuseStep 691523 = 1037285) B1037285
theorem B691793 : Blo 303832 691793 := bstep (se 2 (by rfl) ⟨259422, by rfl⟩ : syracuseStep 691793 = 518845) B518845
theorem B691811 : Blo 303832 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B692081 : Blo 303832 692081 := bstep (se 2 (by rfl) ⟨259530, by rfl⟩ : syracuseStep 692081 = 519061) B519061
theorem B692099 : Blo 303832 692099 := bstep (se 1 (by rfl) ⟨519074, by rfl⟩ : syracuseStep 692099 = 1038149) B1038149
theorem B1052621 : Blo 303832 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B2101297 : Blo 303832 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B692369 : Blo 303832 692369 := bstep (se 2 (by rfl) ⟨259638, by rfl⟩ : syracuseStep 692369 = 519277) B519277
theorem B692387 : Blo 303832 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B1773893 : Blo 303832 1773893 := bstep (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) B332605
theorem B790897 : Blo 303832 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B332147 : Blo 303832 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B1741445 : Blo 303832 1741445 := bstep (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) B326521
theorem B365251 : Blo 303832 365251 := bstep (se 1 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 365251 = 547877) B547877
theorem B365347 : Blo 303832 365347 := bstep (se 1 (by rfl) ⟨274010, by rfl⟩ : syracuseStep 365347 = 548021) B548021
theorem B365491 : Blo 303832 365491 := bstep (se 1 (by rfl) ⟨274118, by rfl⟩ : syracuseStep 365491 = 548237) B548237
theorem B463969 : Blo 303832 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B1971377 : Blo 303832 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B2626829 : Blo 303832 2626829 := bstep (se 3 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 2626829 = 985061) B985061
theorem B12719501 : Blo 303832 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B464339 : Blo 303832 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B1054637 : Blo 303832 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B1546289 : Blo 303832 1546289 := bstep (se 2 (by rfl) ⟨579858, by rfl⟩ : syracuseStep 1546289 = 1159717) B1159717
theorem B563345 : Blo 303832 563345 := bstep (se 2 (by rfl) ⟨211254, by rfl⟩ : syracuseStep 563345 = 422509) B422509
theorem B465185 : Blo 303832 465185 := bstep (se 2 (by rfl) ⟨174444, by rfl⟩ : syracuseStep 465185 = 348889) B348889
theorem B432707 : Blo 303832 432707 := bstep (se 1 (by rfl) ⟨324530, by rfl⟩ : syracuseStep 432707 = 649061) B649061
theorem B3480245 : Blo 303832 3480245 := bstep (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) B326273
theorem B2923235 : Blo 303832 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B629507 : Blo 303832 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B3152837 : Blo 303832 3152837 := bstep (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) B591157
theorem B1875077 : Blo 303832 1875077 := bstep (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) B351577
theorem B1154189 : Blo 303832 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B433345 : Blo 303832 433345 := bstep (se 2 (by rfl) ⟨162504, by rfl⟩ : syracuseStep 433345 = 325009) B325009
theorem B433459 : Blo 303832 433459 := bstep (se 1 (by rfl) ⟨325094, by rfl⟩ : syracuseStep 433459 = 650189) B650189
theorem B695633 : Blo 303832 695633 := bstep (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) B521725
theorem B466273 : Blo 303832 466273 := bstep (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) B349705
theorem B1547747 : Blo 303832 1547747 := bstep (se 1 (by rfl) ⟨1160810, by rfl⟩ : syracuseStep 1547747 = 2321621) B2321621
theorem B3120653 : Blo 303832 3120653 := bstep (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) B1170245
theorem B630289 : Blo 303832 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B466481 : Blo 303832 466481 := bstep (se 2 (by rfl) ⟨174930, by rfl⟩ : syracuseStep 466481 = 349861) B349861
theorem B663203 : Blo 303832 663203 := bstep (se 1 (by rfl) ⟨497402, by rfl⟩ : syracuseStep 663203 = 994805) B994805
theorem B467137 : Blo 303832 467137 := bstep (se 2 (by rfl) ⟨175176, by rfl⟩ : syracuseStep 467137 = 350353) B350353
theorem B1548557 : Blo 303832 1548557 := bstep (se 3 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 1548557 = 580709) B580709
theorem B3744053 : Blo 303832 3744053 := bstep (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) B351005
theorem B434803 : Blo 303832 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B303843 : Blo 303832 303843 := bstep (se 1 (by rfl) ⟨227882, by rfl⟩ : syracuseStep 303843 = 455765) B455765
theorem B303859 : Blo 303832 303859 := bstep (se 1 (by rfl) ⟨227894, by rfl⟩ : syracuseStep 303859 = 455789) B455789
theorem B303875 : Blo 303832 303875 := bstep (se 1 (by rfl) ⟨227906, by rfl⟩ : syracuseStep 303875 = 455813) B455813
theorem B303891 : Blo 303832 303891 := bstep (se 1 (by rfl) ⟨227918, by rfl⟩ : syracuseStep 303891 = 455837) B455837
theorem B303907 : Blo 303832 303907 := bstep (se 1 (by rfl) ⟨227930, by rfl⟩ : syracuseStep 303907 = 455861) B455861
theorem B303923 : Blo 303832 303923 := bstep (se 1 (by rfl) ⟨227942, by rfl⟩ : syracuseStep 303923 = 455885) B455885
theorem B303939 : Blo 303832 303939 := bstep (se 1 (by rfl) ⟨227954, by rfl⟩ : syracuseStep 303939 = 455909) B455909
theorem B303955 : Blo 303832 303955 := bstep (se 1 (by rfl) ⟨227966, by rfl⟩ : syracuseStep 303955 = 455933) B455933
theorem B303971 : Blo 303832 303971 := bstep (se 1 (by rfl) ⟨227978, by rfl⟩ : syracuseStep 303971 = 455957) B455957
theorem B303987 : Blo 303832 303987 := bstep (se 1 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 303987 = 455981) B455981
theorem B304003 : Blo 303832 304003 := bstep (se 1 (by rfl) ⟨228002, by rfl⟩ : syracuseStep 304003 = 456005) B456005
theorem B828301 : Blo 303832 828301 := bstep (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) B310613
theorem B304019 : Blo 303832 304019 := bstep (se 1 (by rfl) ⟨228014, by rfl⟩ : syracuseStep 304019 = 456029) B456029
theorem B304035 : Blo 303832 304035 := bstep (se 1 (by rfl) ⟨228026, by rfl⟩ : syracuseStep 304035 = 456053) B456053
theorem B304051 : Blo 303832 304051 := bstep (se 1 (by rfl) ⟨228038, by rfl⟩ : syracuseStep 304051 = 456077) B456077
theorem B304067 : Blo 303832 304067 := bstep (se 1 (by rfl) ⟨228050, by rfl⟩ : syracuseStep 304067 = 456101) B456101
theorem B304083 : Blo 303832 304083 := bstep (se 1 (by rfl) ⟨228062, by rfl⟩ : syracuseStep 304083 = 456125) B456125
theorem B304099 : Blo 303832 304099 := bstep (se 1 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 304099 = 456149) B456149
theorem B2335715 : Blo 303832 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B304115 : Blo 303832 304115 := bstep (se 1 (by rfl) ⟨228086, by rfl⟩ : syracuseStep 304115 = 456173) B456173
theorem B304131 : Blo 303832 304131 := bstep (se 1 (by rfl) ⟨228098, by rfl⟩ : syracuseStep 304131 = 456197) B456197
theorem B304147 : Blo 303832 304147 := bstep (se 1 (by rfl) ⟨228110, by rfl⟩ : syracuseStep 304147 = 456221) B456221
theorem B304163 : Blo 303832 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B304179 : Blo 303832 304179 := bstep (se 1 (by rfl) ⟨228134, by rfl⟩ : syracuseStep 304179 = 456269) B456269
theorem B304195 : Blo 303832 304195 := bstep (se 1 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 304195 = 456293) B456293
theorem B304211 : Blo 303832 304211 := bstep (se 1 (by rfl) ⟨228158, by rfl⟩ : syracuseStep 304211 = 456317) B456317
theorem B304227 : Blo 303832 304227 := bstep (se 1 (by rfl) ⟨228170, by rfl⟩ : syracuseStep 304227 = 456341) B456341
theorem B304243 : Blo 303832 304243 := bstep (se 1 (by rfl) ⟨228182, by rfl⟩ : syracuseStep 304243 = 456365) B456365
theorem B304259 : Blo 303832 304259 := bstep (se 1 (by rfl) ⟨228194, by rfl⟩ : syracuseStep 304259 = 456389) B456389
theorem B304275 : Blo 303832 304275 := bstep (se 1 (by rfl) ⟨228206, by rfl⟩ : syracuseStep 304275 = 456413) B456413
theorem B304291 : Blo 303832 304291 := bstep (se 1 (by rfl) ⟨228218, by rfl⟩ : syracuseStep 304291 = 456437) B456437
theorem B304307 : Blo 303832 304307 := bstep (se 1 (by rfl) ⟨228230, by rfl⟩ : syracuseStep 304307 = 456461) B456461
theorem B304323 : Blo 303832 304323 := bstep (se 1 (by rfl) ⟨228242, by rfl⟩ : syracuseStep 304323 = 456485) B456485
theorem B1156301 : Blo 303832 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B304339 : Blo 303832 304339 := bstep (se 1 (by rfl) ⟨228254, by rfl⟩ : syracuseStep 304339 = 456509) B456509
theorem B304355 : Blo 303832 304355 := bstep (se 1 (by rfl) ⟨228266, by rfl⟩ : syracuseStep 304355 = 456533) B456533
theorem B304371 : Blo 303832 304371 := bstep (se 1 (by rfl) ⟨228278, by rfl⟩ : syracuseStep 304371 = 456557) B456557
theorem B304387 : Blo 303832 304387 := bstep (se 1 (by rfl) ⟨228290, by rfl⟩ : syracuseStep 304387 = 456581) B456581
theorem B2204941 : Blo 303832 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B304403 : Blo 303832 304403 := bstep (se 1 (by rfl) ⟨228302, by rfl⟩ : syracuseStep 304403 = 456605) B456605
theorem B304419 : Blo 303832 304419 := bstep (se 1 (by rfl) ⟨228314, by rfl⟩ : syracuseStep 304419 = 456629) B456629
theorem B304435 : Blo 303832 304435 := bstep (se 1 (by rfl) ⟨228326, by rfl⟩ : syracuseStep 304435 = 456653) B456653
theorem B6628661 : Blo 303832 6628661 := bstep (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) B621437
theorem B304451 : Blo 303832 304451 := bstep (se 1 (by rfl) ⟨228338, by rfl⟩ : syracuseStep 304451 = 456677) B456677
theorem B304467 : Blo 303832 304467 := bstep (se 1 (by rfl) ⟨228350, by rfl⟩ : syracuseStep 304467 = 456701) B456701
theorem B304483 : Blo 303832 304483 := bstep (se 1 (by rfl) ⟨228362, by rfl⟩ : syracuseStep 304483 = 456725) B456725
theorem B304499 : Blo 303832 304499 := bstep (se 1 (by rfl) ⟨228374, by rfl⟩ : syracuseStep 304499 = 456749) B456749
theorem B304515 : Blo 303832 304515 := bstep (se 1 (by rfl) ⟨228386, by rfl⟩ : syracuseStep 304515 = 456773) B456773
theorem B927121 : Blo 303832 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B304531 : Blo 303832 304531 := bstep (se 1 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 304531 = 456797) B456797
theorem B304547 : Blo 303832 304547 := bstep (se 1 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 304547 = 456821) B456821
theorem B304563 : Blo 303832 304563 := bstep (se 1 (by rfl) ⟨228422, by rfl⟩ : syracuseStep 304563 = 456845) B456845
theorem B304579 : Blo 303832 304579 := bstep (se 1 (by rfl) ⟨228434, by rfl⟩ : syracuseStep 304579 = 456869) B456869
theorem B304595 : Blo 303832 304595 := bstep (se 1 (by rfl) ⟨228446, by rfl⟩ : syracuseStep 304595 = 456893) B456893
theorem B304611 : Blo 303832 304611 := bstep (se 1 (by rfl) ⟨228458, by rfl⟩ : syracuseStep 304611 = 456917) B456917
theorem B304627 : Blo 303832 304627 := bstep (se 1 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 304627 = 456941) B456941
theorem B304643 : Blo 303832 304643 := bstep (se 1 (by rfl) ⟨228482, by rfl⟩ : syracuseStep 304643 = 456965) B456965
theorem B304659 : Blo 303832 304659 := bstep (se 1 (by rfl) ⟨228494, by rfl⟩ : syracuseStep 304659 = 456989) B456989
theorem B304675 : Blo 303832 304675 := bstep (se 1 (by rfl) ⟨228506, by rfl⟩ : syracuseStep 304675 = 457013) B457013
theorem B304691 : Blo 303832 304691 := bstep (se 1 (by rfl) ⟨228518, by rfl⟩ : syracuseStep 304691 = 457037) B457037
theorem B304707 : Blo 303832 304707 := bstep (se 1 (by rfl) ⟨228530, by rfl⟩ : syracuseStep 304707 = 457061) B457061
theorem B304723 : Blo 303832 304723 := bstep (se 1 (by rfl) ⟨228542, by rfl⟩ : syracuseStep 304723 = 457085) B457085
theorem B304739 : Blo 303832 304739 := bstep (se 1 (by rfl) ⟨228554, by rfl⟩ : syracuseStep 304739 = 457109) B457109
theorem B304755 : Blo 303832 304755 := bstep (se 1 (by rfl) ⟨228566, by rfl⟩ : syracuseStep 304755 = 457133) B457133
theorem B304771 : Blo 303832 304771 := bstep (se 1 (by rfl) ⟨228578, by rfl⟩ : syracuseStep 304771 = 457157) B457157
theorem B304787 : Blo 303832 304787 := bstep (se 1 (by rfl) ⟨228590, by rfl⟩ : syracuseStep 304787 = 457181) B457181
theorem B304803 : Blo 303832 304803 := bstep (se 1 (by rfl) ⟨228602, by rfl⟩ : syracuseStep 304803 = 457205) B457205
theorem B304819 : Blo 303832 304819 := bstep (se 1 (by rfl) ⟨228614, by rfl⟩ : syracuseStep 304819 = 457229) B457229
theorem B304835 : Blo 303832 304835 := bstep (se 1 (by rfl) ⟨228626, by rfl⟩ : syracuseStep 304835 = 457253) B457253
theorem B304851 : Blo 303832 304851 := bstep (se 1 (by rfl) ⟨228638, by rfl⟩ : syracuseStep 304851 = 457277) B457277
theorem B435937 : Blo 303832 435937 := bstep (se 2 (by rfl) ⟨163476, by rfl⟩ : syracuseStep 435937 = 326953) B326953
theorem B304867 : Blo 303832 304867 := bstep (se 1 (by rfl) ⟨228650, by rfl⟩ : syracuseStep 304867 = 457301) B457301
theorem B304883 : Blo 303832 304883 := bstep (se 1 (by rfl) ⟨228662, by rfl⟩ : syracuseStep 304883 = 457325) B457325
theorem B304899 : Blo 303832 304899 := bstep (se 1 (by rfl) ⟨228674, by rfl⟩ : syracuseStep 304899 = 457349) B457349
theorem B304915 : Blo 303832 304915 := bstep (se 1 (by rfl) ⟨228686, by rfl⟩ : syracuseStep 304915 = 457373) B457373
theorem B304931 : Blo 303832 304931 := bstep (se 1 (by rfl) ⟨228698, by rfl⟩ : syracuseStep 304931 = 457397) B457397
theorem B1025837 : Blo 303832 1025837 := bstep (se 3 (by rfl) ⟨192344, by rfl⟩ : syracuseStep 1025837 = 384689) B384689
theorem B304947 : Blo 303832 304947 := bstep (se 1 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 304947 = 457421) B457421
theorem B436033 : Blo 303832 436033 := bstep (se 2 (by rfl) ⟨163512, by rfl⟩ : syracuseStep 436033 = 327025) B327025
theorem B304963 : Blo 303832 304963 := bstep (se 1 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 304963 = 457445) B457445
theorem B304979 : Blo 303832 304979 := bstep (se 1 (by rfl) ⟨228734, by rfl⟩ : syracuseStep 304979 = 457469) B457469
theorem B1025891 : Blo 303832 1025891 := bstep (se 1 (by rfl) ⟨769418, by rfl⟩ : syracuseStep 1025891 = 1538837) B1538837
theorem B304995 : Blo 303832 304995 := bstep (se 1 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 304995 = 457493) B457493
theorem B305011 : Blo 303832 305011 := bstep (se 1 (by rfl) ⟨228758, by rfl⟩ : syracuseStep 305011 = 457517) B457517
theorem B305027 : Blo 303832 305027 := bstep (se 1 (by rfl) ⟨228770, by rfl⟩ : syracuseStep 305027 = 457541) B457541
theorem B305043 : Blo 303832 305043 := bstep (se 1 (by rfl) ⟨228782, by rfl⟩ : syracuseStep 305043 = 457565) B457565
theorem B305059 : Blo 303832 305059 := bstep (se 1 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 305059 = 457589) B457589
theorem B305075 : Blo 303832 305075 := bstep (se 1 (by rfl) ⟨228806, by rfl⟩ : syracuseStep 305075 = 457613) B457613
theorem B927683 : Blo 303832 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B305091 : Blo 303832 305091 := bstep (se 1 (by rfl) ⟨228818, by rfl⟩ : syracuseStep 305091 = 457637) B457637
theorem B3942341 : Blo 303832 3942341 := bstep (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) B739189
theorem B305107 : Blo 303832 305107 := bstep (se 1 (by rfl) ⟨228830, by rfl⟩ : syracuseStep 305107 = 457661) B457661
theorem B305123 : Blo 303832 305123 := bstep (se 1 (by rfl) ⟨228842, by rfl⟩ : syracuseStep 305123 = 457685) B457685
theorem B1157105 : Blo 303832 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B305139 : Blo 303832 305139 := bstep (se 1 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 305139 = 457709) B457709
theorem B305155 : Blo 303832 305155 := bstep (se 1 (by rfl) ⟨228866, by rfl⟩ : syracuseStep 305155 = 457733) B457733
theorem B305171 : Blo 303832 305171 := bstep (se 1 (by rfl) ⟨228878, by rfl⟩ : syracuseStep 305171 = 457757) B457757
theorem B305187 : Blo 303832 305187 := bstep (se 1 (by rfl) ⟨228890, by rfl⟩ : syracuseStep 305187 = 457781) B457781
theorem B305203 : Blo 303832 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B5253173 : Blo 303832 5253173 := bstep (se 5 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 5253173 = 492485) B492485
theorem B305219 : Blo 303832 305219 := bstep (se 1 (by rfl) ⟨228914, by rfl⟩ : syracuseStep 305219 = 457829) B457829
theorem B305235 : Blo 303832 305235 := bstep (se 1 (by rfl) ⟨228926, by rfl⟩ : syracuseStep 305235 = 457853) B457853
theorem B305251 : Blo 303832 305251 := bstep (se 1 (by rfl) ⟨228938, by rfl⟩ : syracuseStep 305251 = 457877) B457877
theorem B1026161 : Blo 303832 1026161 := bstep (se 2 (by rfl) ⟨384810, by rfl⟩ : syracuseStep 1026161 = 769621) B769621
theorem B305267 : Blo 303832 305267 := bstep (se 1 (by rfl) ⟨228950, by rfl⟩ : syracuseStep 305267 = 457901) B457901
theorem B305283 : Blo 303832 305283 := bstep (se 1 (by rfl) ⟨228962, by rfl⟩ : syracuseStep 305283 = 457925) B457925
theorem B305299 : Blo 303832 305299 := bstep (se 1 (by rfl) ⟨228974, by rfl⟩ : syracuseStep 305299 = 457949) B457949
theorem B305315 : Blo 303832 305315 := bstep (se 1 (by rfl) ⟨228986, by rfl⟩ : syracuseStep 305315 = 457973) B457973
theorem B305331 : Blo 303832 305331 := bstep (se 1 (by rfl) ⟨228998, by rfl⟩ : syracuseStep 305331 = 457997) B457997
theorem B3549365 : Blo 303832 3549365 := bstep (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) B332753
theorem B305347 : Blo 303832 305347 := bstep (se 1 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 305347 = 458021) B458021
theorem B305363 : Blo 303832 305363 := bstep (se 1 (by rfl) ⟨229022, by rfl⟩ : syracuseStep 305363 = 458045) B458045
theorem B4761827 : Blo 303832 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B305379 : Blo 303832 305379 := bstep (se 1 (by rfl) ⟨229034, by rfl⟩ : syracuseStep 305379 = 458069) B458069
theorem B305395 : Blo 303832 305395 := bstep (se 1 (by rfl) ⟨229046, by rfl⟩ : syracuseStep 305395 = 458093) B458093
theorem B305411 : Blo 303832 305411 := bstep (se 1 (by rfl) ⟨229058, by rfl⟩ : syracuseStep 305411 = 458117) B458117
theorem B305427 : Blo 303832 305427 := bstep (se 1 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 305427 = 458141) B458141
theorem B305443 : Blo 303832 305443 := bstep (se 1 (by rfl) ⟨229082, by rfl⟩ : syracuseStep 305443 = 458165) B458165
theorem B436529 : Blo 303832 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B305459 : Blo 303832 305459 := bstep (se 1 (by rfl) ⟨229094, by rfl⟩ : syracuseStep 305459 = 458189) B458189
theorem B305475 : Blo 303832 305475 := bstep (se 1 (by rfl) ⟨229106, by rfl⟩ : syracuseStep 305475 = 458213) B458213
theorem B1091917 : Blo 303832 1091917 := bstep (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) B409469
theorem B1747277 : Blo 303832 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B305491 : Blo 303832 305491 := bstep (se 1 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 305491 = 458237) B458237
theorem B305507 : Blo 303832 305507 := bstep (se 1 (by rfl) ⟨229130, by rfl⟩ : syracuseStep 305507 = 458261) B458261
theorem B2959715 : Blo 303832 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B305523 : Blo 303832 305523 := bstep (se 1 (by rfl) ⟨229142, by rfl⟩ : syracuseStep 305523 = 458285) B458285
theorem B305539 : Blo 303832 305539 := bstep (se 1 (by rfl) ⟨229154, by rfl⟩ : syracuseStep 305539 = 458309) B458309
theorem B305555 : Blo 303832 305555 := bstep (se 1 (by rfl) ⟨229166, by rfl⟩ : syracuseStep 305555 = 458333) B458333
theorem B305571 : Blo 303832 305571 := bstep (se 1 (by rfl) ⟨229178, by rfl⟩ : syracuseStep 305571 = 458357) B458357
theorem B305587 : Blo 303832 305587 := bstep (se 1 (by rfl) ⟨229190, by rfl⟩ : syracuseStep 305587 = 458381) B458381
theorem B305603 : Blo 303832 305603 := bstep (se 1 (by rfl) ⟨229202, by rfl⟩ : syracuseStep 305603 = 458405) B458405
theorem B305619 : Blo 303832 305619 := bstep (se 1 (by rfl) ⟨229214, by rfl⟩ : syracuseStep 305619 = 458429) B458429
theorem B305635 : Blo 303832 305635 := bstep (se 1 (by rfl) ⟨229226, by rfl⟩ : syracuseStep 305635 = 458453) B458453
theorem B305651 : Blo 303832 305651 := bstep (se 1 (by rfl) ⟨229238, by rfl⟩ : syracuseStep 305651 = 458477) B458477
theorem B305667 : Blo 303832 305667 := bstep (se 1 (by rfl) ⟨229250, by rfl⟩ : syracuseStep 305667 = 458501) B458501
theorem B305683 : Blo 303832 305683 := bstep (se 1 (by rfl) ⟨229262, by rfl⟩ : syracuseStep 305683 = 458525) B458525
theorem B305699 : Blo 303832 305699 := bstep (se 1 (by rfl) ⟨229274, by rfl⟩ : syracuseStep 305699 = 458549) B458549
theorem B305715 : Blo 303832 305715 := bstep (se 1 (by rfl) ⟨229286, by rfl⟩ : syracuseStep 305715 = 458573) B458573
theorem B305731 : Blo 303832 305731 := bstep (se 1 (by rfl) ⟨229298, by rfl⟩ : syracuseStep 305731 = 458597) B458597
theorem B305747 : Blo 303832 305747 := bstep (se 1 (by rfl) ⟨229310, by rfl⟩ : syracuseStep 305747 = 458621) B458621
theorem B2599523 : Blo 303832 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B305763 : Blo 303832 305763 := bstep (se 1 (by rfl) ⟨229322, by rfl⟩ : syracuseStep 305763 = 458645) B458645
theorem B305779 : Blo 303832 305779 := bstep (se 1 (by rfl) ⟨229334, by rfl⟩ : syracuseStep 305779 = 458669) B458669
theorem B305795 : Blo 303832 305795 := bstep (se 1 (by rfl) ⟨229346, by rfl⟩ : syracuseStep 305795 = 458693) B458693
theorem B1026701 : Blo 303832 1026701 := bstep (se 3 (by rfl) ⟨192506, by rfl⟩ : syracuseStep 1026701 = 385013) B385013
theorem B1157773 : Blo 303832 1157773 := bstep (se 3 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 1157773 = 434165) B434165
theorem B305811 : Blo 303832 305811 := bstep (se 1 (by rfl) ⟨229358, by rfl⟩ : syracuseStep 305811 = 458717) B458717
theorem B305827 : Blo 303832 305827 := bstep (se 1 (by rfl) ⟨229370, by rfl⟩ : syracuseStep 305827 = 458741) B458741
theorem B928433 : Blo 303832 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B305843 : Blo 303832 305843 := bstep (se 1 (by rfl) ⟨229382, by rfl⟩ : syracuseStep 305843 = 458765) B458765
theorem B1026755 : Blo 303832 1026755 := bstep (se 1 (by rfl) ⟨770066, by rfl⟩ : syracuseStep 1026755 = 1540133) B1540133
theorem B305859 : Blo 303832 305859 := bstep (se 1 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 305859 = 458789) B458789
theorem B305875 : Blo 303832 305875 := bstep (se 1 (by rfl) ⟨229406, by rfl⟩ : syracuseStep 305875 = 458813) B458813
theorem B305891 : Blo 303832 305891 := bstep (se 1 (by rfl) ⟨229418, by rfl⟩ : syracuseStep 305891 = 458837) B458837
theorem B305907 : Blo 303832 305907 := bstep (se 1 (by rfl) ⟨229430, by rfl⟩ : syracuseStep 305907 = 458861) B458861
theorem B305923 : Blo 303832 305923 := bstep (se 1 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 305923 = 458885) B458885
theorem B305939 : Blo 303832 305939 := bstep (se 1 (by rfl) ⟨229454, by rfl⟩ : syracuseStep 305939 = 458909) B458909
theorem B305955 : Blo 303832 305955 := bstep (se 1 (by rfl) ⟨229466, by rfl⟩ : syracuseStep 305955 = 458933) B458933
theorem B305971 : Blo 303832 305971 := bstep (se 1 (by rfl) ⟨229478, by rfl⟩ : syracuseStep 305971 = 458957) B458957
theorem B305987 : Blo 303832 305987 := bstep (se 1 (by rfl) ⟨229490, by rfl⟩ : syracuseStep 305987 = 458981) B458981
theorem B306003 : Blo 303832 306003 := bstep (se 1 (by rfl) ⟨229502, by rfl⟩ : syracuseStep 306003 = 459005) B459005
theorem B306019 : Blo 303832 306019 := bstep (se 1 (by rfl) ⟨229514, by rfl⟩ : syracuseStep 306019 = 459029) B459029
theorem B306035 : Blo 303832 306035 := bstep (se 1 (by rfl) ⟨229526, by rfl⟩ : syracuseStep 306035 = 459053) B459053
theorem B306051 : Blo 303832 306051 := bstep (se 1 (by rfl) ⟨229538, by rfl⟩ : syracuseStep 306051 = 459077) B459077
theorem B306067 : Blo 303832 306067 := bstep (se 1 (by rfl) ⟨229550, by rfl⟩ : syracuseStep 306067 = 459101) B459101
theorem B306083 : Blo 303832 306083 := bstep (se 1 (by rfl) ⟨229562, by rfl⟩ : syracuseStep 306083 = 459125) B459125
theorem B306099 : Blo 303832 306099 := bstep (se 1 (by rfl) ⟨229574, by rfl⟩ : syracuseStep 306099 = 459149) B459149
theorem B306115 : Blo 303832 306115 := bstep (se 1 (by rfl) ⟨229586, by rfl⟩ : syracuseStep 306115 = 459173) B459173
theorem B1027025 : Blo 303832 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B306131 : Blo 303832 306131 := bstep (se 1 (by rfl) ⟨229598, by rfl⟩ : syracuseStep 306131 = 459197) B459197
theorem B306147 : Blo 303832 306147 := bstep (se 1 (by rfl) ⟨229610, by rfl⟩ : syracuseStep 306147 = 459221) B459221
theorem B306163 : Blo 303832 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B306179 : Blo 303832 306179 := bstep (se 1 (by rfl) ⟨229634, by rfl⟩ : syracuseStep 306179 = 459269) B459269
theorem B306195 : Blo 303832 306195 := bstep (se 1 (by rfl) ⟨229646, by rfl⟩ : syracuseStep 306195 = 459293) B459293
theorem B306211 : Blo 303832 306211 := bstep (se 1 (by rfl) ⟨229658, by rfl⟩ : syracuseStep 306211 = 459317) B459317
theorem B306227 : Blo 303832 306227 := bstep (se 1 (by rfl) ⟨229670, by rfl⟩ : syracuseStep 306227 = 459341) B459341
theorem B306243 : Blo 303832 306243 := bstep (se 1 (by rfl) ⟨229682, by rfl⟩ : syracuseStep 306243 = 459365) B459365
theorem B306259 : Blo 303832 306259 := bstep (se 1 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 306259 = 459389) B459389
theorem B306275 : Blo 303832 306275 := bstep (se 1 (by rfl) ⟨229706, by rfl⟩ : syracuseStep 306275 = 459413) B459413
theorem B1551473 : Blo 303832 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B306291 : Blo 303832 306291 := bstep (se 1 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 306291 = 459437) B459437
theorem B306307 : Blo 303832 306307 := bstep (se 1 (by rfl) ⟨229730, by rfl⟩ : syracuseStep 306307 = 459461) B459461
theorem B306323 : Blo 303832 306323 := bstep (se 1 (by rfl) ⟨229742, by rfl⟩ : syracuseStep 306323 = 459485) B459485
theorem B437395 : Blo 303832 437395 := bstep (se 1 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 437395 = 656093) B656093
theorem B306339 : Blo 303832 306339 := bstep (se 1 (by rfl) ⟨229754, by rfl⟩ : syracuseStep 306339 = 459509) B459509
theorem B306355 : Blo 303832 306355 := bstep (se 1 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 306355 = 459533) B459533
theorem B306371 : Blo 303832 306371 := bstep (se 1 (by rfl) ⟨229778, by rfl⟩ : syracuseStep 306371 = 459557) B459557
theorem B306387 : Blo 303832 306387 := bstep (se 1 (by rfl) ⟨229790, by rfl⟩ : syracuseStep 306387 = 459581) B459581
theorem B306403 : Blo 303832 306403 := bstep (se 1 (by rfl) ⟨229802, by rfl⟩ : syracuseStep 306403 = 459605) B459605
theorem B306419 : Blo 303832 306419 := bstep (se 1 (by rfl) ⟨229814, by rfl⟩ : syracuseStep 306419 = 459629) B459629
theorem B437491 : Blo 303832 437491 := bstep (se 1 (by rfl) ⟨328118, by rfl⟩ : syracuseStep 437491 = 656237) B656237
theorem B306435 : Blo 303832 306435 := bstep (se 1 (by rfl) ⟨229826, by rfl⟩ : syracuseStep 306435 = 459653) B459653
theorem B306451 : Blo 303832 306451 := bstep (se 1 (by rfl) ⟨229838, by rfl⟩ : syracuseStep 306451 = 459677) B459677
theorem B306467 : Blo 303832 306467 := bstep (se 1 (by rfl) ⟨229850, by rfl⟩ : syracuseStep 306467 = 459701) B459701
theorem B306483 : Blo 303832 306483 := bstep (se 1 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 306483 = 459725) B459725
theorem B306499 : Blo 303832 306499 := bstep (se 1 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 306499 = 459749) B459749
theorem B306515 : Blo 303832 306515 := bstep (se 1 (by rfl) ⟨229886, by rfl⟩ : syracuseStep 306515 = 459773) B459773
theorem B306531 : Blo 303832 306531 := bstep (se 1 (by rfl) ⟨229898, by rfl⟩ : syracuseStep 306531 = 459797) B459797
theorem B306547 : Blo 303832 306547 := bstep (se 1 (by rfl) ⟨229910, by rfl⟩ : syracuseStep 306547 = 459821) B459821
theorem B306563 : Blo 303832 306563 := bstep (se 1 (by rfl) ⟨229922, by rfl⟩ : syracuseStep 306563 = 459845) B459845
theorem B306579 : Blo 303832 306579 := bstep (se 1 (by rfl) ⟨229934, by rfl⟩ : syracuseStep 306579 = 459869) B459869
theorem B1158563 : Blo 303832 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B306595 : Blo 303832 306595 := bstep (se 1 (by rfl) ⟨229946, by rfl⟩ : syracuseStep 306595 = 459893) B459893
theorem B306611 : Blo 303832 306611 := bstep (se 1 (by rfl) ⟨229958, by rfl⟩ : syracuseStep 306611 = 459917) B459917
theorem B306627 : Blo 303832 306627 := bstep (se 1 (by rfl) ⟨229970, by rfl⟩ : syracuseStep 306627 = 459941) B459941
theorem B306643 : Blo 303832 306643 := bstep (se 1 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 306643 = 459965) B459965
theorem B306659 : Blo 303832 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B1027565 : Blo 303832 1027565 := bstep (se 3 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 1027565 = 385337) B385337
theorem B306675 : Blo 303832 306675 := bstep (se 1 (by rfl) ⟨230006, by rfl⟩ : syracuseStep 306675 = 460013) B460013
theorem B306691 : Blo 303832 306691 := bstep (se 1 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 306691 = 460037) B460037
theorem B306707 : Blo 303832 306707 := bstep (se 1 (by rfl) ⟨230030, by rfl⟩ : syracuseStep 306707 = 460061) B460061
theorem B1027619 : Blo 303832 1027619 := bstep (se 1 (by rfl) ⟨770714, by rfl⟩ : syracuseStep 1027619 = 1541429) B1541429
theorem B306723 : Blo 303832 306723 := bstep (se 1 (by rfl) ⟨230042, by rfl⟩ : syracuseStep 306723 = 460085) B460085
theorem B306739 : Blo 303832 306739 := bstep (se 1 (by rfl) ⟨230054, by rfl⟩ : syracuseStep 306739 = 460109) B460109
theorem B306755 : Blo 303832 306755 := bstep (se 1 (by rfl) ⟨230066, by rfl⟩ : syracuseStep 306755 = 460133) B460133
theorem B306771 : Blo 303832 306771 := bstep (se 1 (by rfl) ⟨230078, by rfl⟩ : syracuseStep 306771 = 460157) B460157
theorem B306787 : Blo 303832 306787 := bstep (se 1 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 306787 = 460181) B460181
theorem B1650289 : Blo 303832 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B306803 : Blo 303832 306803 := bstep (se 1 (by rfl) ⟨230102, by rfl⟩ : syracuseStep 306803 = 460205) B460205
theorem B306819 : Blo 303832 306819 := bstep (se 1 (by rfl) ⟨230114, by rfl⟩ : syracuseStep 306819 = 460229) B460229
theorem B306835 : Blo 303832 306835 := bstep (se 1 (by rfl) ⟨230126, by rfl⟩ : syracuseStep 306835 = 460253) B460253
theorem B306851 : Blo 303832 306851 := bstep (se 1 (by rfl) ⟨230138, by rfl⟩ : syracuseStep 306851 = 460277) B460277
theorem B306867 : Blo 303832 306867 := bstep (se 1 (by rfl) ⟨230150, by rfl⟩ : syracuseStep 306867 = 460301) B460301
theorem B1060547 : Blo 303832 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B306883 : Blo 303832 306883 := bstep (se 1 (by rfl) ⟨230162, by rfl⟩ : syracuseStep 306883 = 460325) B460325
theorem B306899 : Blo 303832 306899 := bstep (se 1 (by rfl) ⟨230174, by rfl⟩ : syracuseStep 306899 = 460349) B460349
theorem B306915 : Blo 303832 306915 := bstep (se 1 (by rfl) ⟨230186, by rfl⟩ : syracuseStep 306915 = 460373) B460373
theorem B437987 : Blo 303832 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B306931 : Blo 303832 306931 := bstep (se 1 (by rfl) ⟨230198, by rfl⟩ : syracuseStep 306931 = 460397) B460397
theorem B306947 : Blo 303832 306947 := bstep (se 1 (by rfl) ⟨230210, by rfl⟩ : syracuseStep 306947 = 460421) B460421
theorem B306963 : Blo 303832 306963 := bstep (se 1 (by rfl) ⟨230222, by rfl⟩ : syracuseStep 306963 = 460445) B460445
theorem B306979 : Blo 303832 306979 := bstep (se 1 (by rfl) ⟨230234, by rfl⟩ : syracuseStep 306979 = 460469) B460469
theorem B1027889 : Blo 303832 1027889 := bstep (se 2 (by rfl) ⟨385458, by rfl⟩ : syracuseStep 1027889 = 770917) B770917
theorem B1322801 : Blo 303832 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B306995 : Blo 303832 306995 := bstep (se 1 (by rfl) ⟨230246, by rfl⟩ : syracuseStep 306995 = 460493) B460493
theorem B307011 : Blo 303832 307011 := bstep (se 1 (by rfl) ⟨230258, by rfl⟩ : syracuseStep 307011 = 460517) B460517
theorem B307027 : Blo 303832 307027 := bstep (se 1 (by rfl) ⟨230270, by rfl⟩ : syracuseStep 307027 = 460541) B460541
theorem B307043 : Blo 303832 307043 := bstep (se 1 (by rfl) ⟨230282, by rfl⟩ : syracuseStep 307043 = 460565) B460565
theorem B307059 : Blo 303832 307059 := bstep (se 1 (by rfl) ⟨230294, by rfl⟩ : syracuseStep 307059 = 460589) B460589
theorem B307075 : Blo 303832 307075 := bstep (se 1 (by rfl) ⟨230306, by rfl⟩ : syracuseStep 307075 = 460613) B460613
theorem B307091 : Blo 303832 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B307107 : Blo 303832 307107 := bstep (se 1 (by rfl) ⟨230330, by rfl⟩ : syracuseStep 307107 = 460661) B460661
theorem B307123 : Blo 303832 307123 := bstep (se 1 (by rfl) ⟨230342, by rfl⟩ : syracuseStep 307123 = 460685) B460685
theorem B307139 : Blo 303832 307139 := bstep (se 1 (by rfl) ⟨230354, by rfl⟩ : syracuseStep 307139 = 460709) B460709
theorem B307155 : Blo 303832 307155 := bstep (se 1 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 307155 = 460733) B460733
theorem B307171 : Blo 303832 307171 := bstep (se 1 (by rfl) ⟨230378, by rfl⟩ : syracuseStep 307171 = 460757) B460757
theorem B307187 : Blo 303832 307187 := bstep (se 1 (by rfl) ⟨230390, by rfl⟩ : syracuseStep 307187 = 460781) B460781
theorem B307203 : Blo 303832 307203 := bstep (se 1 (by rfl) ⟨230402, by rfl⟩ : syracuseStep 307203 = 460805) B460805
theorem B307219 : Blo 303832 307219 := bstep (se 1 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 307219 = 460829) B460829
theorem B307235 : Blo 303832 307235 := bstep (se 1 (by rfl) ⟨230426, by rfl⟩ : syracuseStep 307235 = 460853) B460853
theorem B1159217 : Blo 303832 1159217 := bstep (se 2 (by rfl) ⟨434706, by rfl⟩ : syracuseStep 1159217 = 869413) B869413
theorem B307251 : Blo 303832 307251 := bstep (se 1 (by rfl) ⟨230438, by rfl⟩ : syracuseStep 307251 = 460877) B460877
theorem B307267 : Blo 303832 307267 := bstep (se 1 (by rfl) ⟨230450, by rfl⟩ : syracuseStep 307267 = 460901) B460901
theorem B307283 : Blo 303832 307283 := bstep (se 1 (by rfl) ⟨230462, by rfl⟩ : syracuseStep 307283 = 460925) B460925
theorem B307299 : Blo 303832 307299 := bstep (se 1 (by rfl) ⟨230474, by rfl⟩ : syracuseStep 307299 = 460949) B460949
theorem B307315 : Blo 303832 307315 := bstep (se 1 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 307315 = 460973) B460973
theorem B307331 : Blo 303832 307331 := bstep (se 1 (by rfl) ⟨230498, by rfl⟩ : syracuseStep 307331 = 460997) B460997
theorem B307347 : Blo 303832 307347 := bstep (se 1 (by rfl) ⟨230510, by rfl⟩ : syracuseStep 307347 = 461021) B461021
theorem B307363 : Blo 303832 307363 := bstep (se 1 (by rfl) ⟨230522, by rfl⟩ : syracuseStep 307363 = 461045) B461045
theorem B307379 : Blo 303832 307379 := bstep (se 1 (by rfl) ⟨230534, by rfl⟩ : syracuseStep 307379 = 461069) B461069
theorem B307395 : Blo 303832 307395 := bstep (se 1 (by rfl) ⟨230546, by rfl⟩ : syracuseStep 307395 = 461093) B461093
theorem B307411 : Blo 303832 307411 := bstep (se 1 (by rfl) ⟨230558, by rfl⟩ : syracuseStep 307411 = 461117) B461117
theorem B2470115 : Blo 303832 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B307427 : Blo 303832 307427 := bstep (se 1 (by rfl) ⟨230570, by rfl⟩ : syracuseStep 307427 = 461141) B461141
theorem B307443 : Blo 303832 307443 := bstep (se 1 (by rfl) ⟨230582, by rfl⟩ : syracuseStep 307443 = 461165) B461165
theorem B307459 : Blo 303832 307459 := bstep (se 1 (by rfl) ⟨230594, by rfl⟩ : syracuseStep 307459 = 461189) B461189
theorem B831761 : Blo 303832 831761 := bstep (se 2 (by rfl) ⟨311910, by rfl⟩ : syracuseStep 831761 = 623821) B623821
theorem B307475 : Blo 303832 307475 := bstep (se 1 (by rfl) ⟨230606, by rfl⟩ : syracuseStep 307475 = 461213) B461213
theorem B307491 : Blo 303832 307491 := bstep (se 1 (by rfl) ⟨230618, by rfl⟩ : syracuseStep 307491 = 461237) B461237
theorem B307507 : Blo 303832 307507 := bstep (se 1 (by rfl) ⟨230630, by rfl⟩ : syracuseStep 307507 = 461261) B461261
theorem B307523 : Blo 303832 307523 := bstep (se 1 (by rfl) ⟨230642, by rfl⟩ : syracuseStep 307523 = 461285) B461285
theorem B1028429 : Blo 303832 1028429 := bstep (se 3 (by rfl) ⟨192830, by rfl⟩ : syracuseStep 1028429 = 385661) B385661
theorem B307539 : Blo 303832 307539 := bstep (se 1 (by rfl) ⟨230654, by rfl⟩ : syracuseStep 307539 = 461309) B461309
theorem B307555 : Blo 303832 307555 := bstep (se 1 (by rfl) ⟨230666, by rfl⟩ : syracuseStep 307555 = 461333) B461333
theorem B307571 : Blo 303832 307571 := bstep (se 1 (by rfl) ⟨230678, by rfl⟩ : syracuseStep 307571 = 461357) B461357
theorem B1028483 : Blo 303832 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B307587 : Blo 303832 307587 := bstep (se 1 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 307587 = 461381) B461381
theorem B307603 : Blo 303832 307603 := bstep (se 1 (by rfl) ⟨230702, by rfl⟩ : syracuseStep 307603 = 461405) B461405
theorem B307619 : Blo 303832 307619 := bstep (se 1 (by rfl) ⟨230714, by rfl⟩ : syracuseStep 307619 = 461429) B461429
theorem B307635 : Blo 303832 307635 := bstep (se 1 (by rfl) ⟨230726, by rfl⟩ : syracuseStep 307635 = 461453) B461453
theorem B307651 : Blo 303832 307651 := bstep (se 1 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 307651 = 461477) B461477
theorem B307667 : Blo 303832 307667 := bstep (se 1 (by rfl) ⟨230750, by rfl⟩ : syracuseStep 307667 = 461501) B461501
theorem B6238691 : Blo 303832 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B307683 : Blo 303832 307683 := bstep (se 1 (by rfl) ⟨230762, by rfl⟩ : syracuseStep 307683 = 461525) B461525
theorem B307699 : Blo 303832 307699 := bstep (se 1 (by rfl) ⟨230774, by rfl⟩ : syracuseStep 307699 = 461549) B461549
theorem B307715 : Blo 303832 307715 := bstep (se 1 (by rfl) ⟨230786, by rfl⟩ : syracuseStep 307715 = 461573) B461573
theorem B1749509 : Blo 303832 1749509 := bstep (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) B328033
theorem B307731 : Blo 303832 307731 := bstep (se 1 (by rfl) ⟨230798, by rfl⟩ : syracuseStep 307731 = 461597) B461597
theorem B1552931 : Blo 303832 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B307747 : Blo 303832 307747 := bstep (se 1 (by rfl) ⟨230810, by rfl⟩ : syracuseStep 307747 = 461621) B461621
theorem B307763 : Blo 303832 307763 := bstep (se 1 (by rfl) ⟨230822, by rfl⟩ : syracuseStep 307763 = 461645) B461645
theorem B307779 : Blo 303832 307779 := bstep (se 1 (by rfl) ⟨230834, by rfl⟩ : syracuseStep 307779 = 461669) B461669
theorem B995917 : Blo 303832 995917 := bstep (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) B373469
theorem B307795 : Blo 303832 307795 := bstep (se 1 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 307795 = 461693) B461693
theorem B307811 : Blo 303832 307811 := bstep (se 1 (by rfl) ⟨230858, by rfl⟩ : syracuseStep 307811 = 461717) B461717
theorem B307827 : Blo 303832 307827 := bstep (se 1 (by rfl) ⟨230870, by rfl⟩ : syracuseStep 307827 = 461741) B461741
theorem B1028753 : Blo 303832 1028753 := bstep (se 2 (by rfl) ⟨385782, by rfl⟩ : syracuseStep 1028753 = 771565) B771565
theorem B930797 : Blo 303832 930797 := bstep (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) B349049
theorem B472081 : Blo 303832 472081 := bstep (se 2 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 472081 = 354061) B354061
theorem B373907 : Blo 303832 373907 := bstep (se 1 (by rfl) ⟨280430, by rfl⟩ : syracuseStep 373907 = 560861) B560861
theorem B1029293 : Blo 303832 1029293 := bstep (se 3 (by rfl) ⟨192992, by rfl⟩ : syracuseStep 1029293 = 385985) B385985
theorem B1750193 : Blo 303832 1750193 := bstep (se 2 (by rfl) ⟨656322, by rfl⟩ : syracuseStep 1750193 = 1312645) B1312645
theorem B1029347 : Blo 303832 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B1553741 : Blo 303832 1553741 := bstep (se 3 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 1553741 = 582653) B582653
theorem B308611 : Blo 303832 308611 := bstep (se 1 (by rfl) ⟨231458, by rfl⟩ : syracuseStep 308611 = 462917) B462917
theorem B1160675 : Blo 303832 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B1029617 : Blo 303832 1029617 := bstep (se 2 (by rfl) ⟨386106, by rfl⟩ : syracuseStep 1029617 = 772213) B772213
theorem B1160689 : Blo 303832 1160689 := bstep (se 2 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 1160689 = 870517) B870517
theorem B2209265 : Blo 303832 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B439825 : Blo 303832 439825 := bstep (se 2 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 439825 = 329869) B329869
theorem B931537 : Blo 303832 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B1095437 : Blo 303832 1095437 := bstep (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) B410789
theorem B866189 : Blo 303832 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B341923 : Blo 303832 341923 := bstep (se 1 (by rfl) ⟨256442, by rfl⟩ : syracuseStep 341923 = 512885) B512885
theorem B1030157 : Blo 303832 1030157 := bstep (se 3 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 1030157 = 386309) B386309
theorem B342067 : Blo 303832 342067 := bstep (se 1 (by rfl) ⟨256550, by rfl⟩ : syracuseStep 342067 = 513101) B513101
theorem B866371 : Blo 303832 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B1030211 : Blo 303832 1030211 := bstep (se 1 (by rfl) ⟨772658, by rfl⟩ : syracuseStep 1030211 = 1545317) B1545317
theorem B342211 : Blo 303832 342211 := bstep (se 1 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 342211 = 513317) B513317
theorem B866531 : Blo 303832 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B1030481 : Blo 303832 1030481 := bstep (se 2 (by rfl) ⟨386430, by rfl⟩ : syracuseStep 1030481 = 772861) B772861
theorem B342355 : Blo 303832 342355 := bstep (se 1 (by rfl) ⟨256766, by rfl⟩ : syracuseStep 342355 = 513533) B513533
theorem B342499 : Blo 303832 342499 := bstep (se 1 (by rfl) ⟨256874, by rfl⟩ : syracuseStep 342499 = 513749) B513749
theorem B473603 : Blo 303832 473603 := bstep (se 1 (by rfl) ⟨355202, by rfl⟩ : syracuseStep 473603 = 710405) B710405
theorem B1653317 : Blo 303832 1653317 := bstep (se 4 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 1653317 = 309997) B309997
theorem B1751651 : Blo 303832 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B342643 : Blo 303832 342643 := bstep (se 1 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 342643 = 513965) B513965
theorem B735875 : Blo 303832 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B342787 : Blo 303832 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B1031021 : Blo 303832 1031021 := bstep (se 3 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 1031021 = 386633) B386633
theorem B342931 : Blo 303832 342931 := bstep (se 1 (by rfl) ⟨257198, by rfl⟩ : syracuseStep 342931 = 514397) B514397
theorem B1031075 : Blo 303832 1031075 := bstep (se 1 (by rfl) ⟨773306, by rfl⟩ : syracuseStep 1031075 = 1546613) B1546613
theorem B1162147 : Blo 303832 1162147 := bstep (se 1 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 1162147 = 1743221) B1743221
theorem B343075 : Blo 303832 343075 := bstep (se 1 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 343075 = 514613) B514613
theorem B441379 : Blo 303832 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B1621061 : Blo 303832 1621061 := bstep (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) B303949
theorem B1031345 : Blo 303832 1031345 := bstep (se 2 (by rfl) ⟨386754, by rfl⟩ : syracuseStep 1031345 = 773509) B773509
theorem B343219 : Blo 303832 343219 := bstep (se 1 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 343219 = 514829) B514829
theorem B441569 : Blo 303832 441569 := bstep (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) B331177
theorem B769297 : Blo 303832 769297 := bstep (se 2 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 769297 = 576973) B576973
theorem B867601 : Blo 303832 867601 := bstep (se 2 (by rfl) ⟨325350, by rfl⟩ : syracuseStep 867601 = 650701) B650701
theorem B1097009 : Blo 303832 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B343363 : Blo 303832 343363 := bstep (se 1 (by rfl) ⟨257522, by rfl⟩ : syracuseStep 343363 = 515045) B515045
theorem B343507 : Blo 303832 343507 := bstep (se 1 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 343507 = 515261) B515261
theorem B835043 : Blo 303832 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B769571 : Blo 303832 769571 := bstep (se 1 (by rfl) ⟨577178, by rfl⟩ : syracuseStep 769571 = 1154357) B1154357
theorem B343651 : Blo 303832 343651 := bstep (se 1 (by rfl) ⟨257738, by rfl⟩ : syracuseStep 343651 = 515477) B515477
theorem B1031885 : Blo 303832 1031885 := bstep (se 3 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 1031885 = 386957) B386957
theorem B769763 : Blo 303832 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B343795 : Blo 303832 343795 := bstep (se 1 (by rfl) ⟨257846, by rfl⟩ : syracuseStep 343795 = 515693) B515693
theorem B1031939 : Blo 303832 1031939 := bstep (se 1 (by rfl) ⟨773954, by rfl⟩ : syracuseStep 1031939 = 1547909) B1547909
theorem B2309957 : Blo 303832 2309957 := bstep (se 4 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 2309957 = 433117) B433117
theorem B343939 : Blo 303832 343939 := bstep (se 1 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 343939 = 515909) B515909
theorem B1032209 : Blo 303832 1032209 := bstep (se 2 (by rfl) ⟨387078, by rfl⟩ : syracuseStep 1032209 = 774157) B774157
theorem B344083 : Blo 303832 344083 := bstep (se 1 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 344083 = 516125) B516125
theorem B1392689 : Blo 303832 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B344227 : Blo 303832 344227 := bstep (se 1 (by rfl) ⟨258170, by rfl⟩ : syracuseStep 344227 = 516341) B516341
theorem B1556657 : Blo 303832 1556657 := bstep (se 2 (by rfl) ⟨583746, by rfl⟩ : syracuseStep 1556657 = 1167493) B1167493
theorem B344371 : Blo 303832 344371 := bstep (se 1 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 344371 = 516557) B516557
theorem B311635 : Blo 303832 311635 := bstep (se 1 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 311635 = 467453) B467453
theorem B344515 : Blo 303832 344515 := bstep (se 1 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 344515 = 516773) B516773
theorem B868877 : Blo 303832 868877 := bstep (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) B325829
theorem B1032749 : Blo 303832 1032749 := bstep (se 3 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 1032749 = 387281) B387281
theorem B1950257 : Blo 303832 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B344659 : Blo 303832 344659 := bstep (se 1 (by rfl) ⟨258494, by rfl⟩ : syracuseStep 344659 = 516989) B516989
theorem B1032803 : Blo 303832 1032803 := bstep (se 1 (by rfl) ⟨774602, by rfl⟩ : syracuseStep 1032803 = 1549205) B1549205
theorem B770705 : Blo 303832 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B770755 : Blo 303832 770755 := bstep (se 1 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 770755 = 1156133) B1156133
theorem B869059 : Blo 303832 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B344803 : Blo 303832 344803 := bstep (se 1 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 344803 = 517205) B517205
theorem B869105 : Blo 303832 869105 := bstep (se 2 (by rfl) ⟨325914, by rfl⟩ : syracuseStep 869105 = 651829) B651829
theorem B770897 : Blo 303832 770897 := bstep (se 2 (by rfl) ⟨289086, by rfl⟩ : syracuseStep 770897 = 578173) B578173
theorem B1033073 : Blo 303832 1033073 := bstep (se 2 (by rfl) ⟨387402, by rfl⟩ : syracuseStep 1033073 = 774805) B774805
theorem B344947 : Blo 303832 344947 := bstep (se 1 (by rfl) ⟨258710, by rfl⟩ : syracuseStep 344947 = 517421) B517421
theorem B345091 : Blo 303832 345091 := bstep (se 1 (by rfl) ⟨258818, by rfl⟩ : syracuseStep 345091 = 517637) B517637
theorem B1164365 : Blo 303832 1164365 := bstep (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) B436637
theorem B1098865 : Blo 303832 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B345235 : Blo 303832 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B1950925 : Blo 303832 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B345379 : Blo 303832 345379 := bstep (se 1 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 345379 = 518069) B518069
theorem B1033613 : Blo 303832 1033613 := bstep (se 3 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 1033613 = 387605) B387605
theorem B345523 : Blo 303832 345523 := bstep (se 1 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 345523 = 518285) B518285
theorem B1033667 : Blo 303832 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B673283 : Blo 303832 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B935441 : Blo 303832 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B345667 : Blo 303832 345667 := bstep (se 1 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 345667 = 518501) B518501
theorem B1558115 : Blo 303832 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B1033937 : Blo 303832 1033937 := bstep (se 2 (by rfl) ⟨387726, by rfl⟩ : syracuseStep 1033937 = 775453) B775453
theorem B345811 : Blo 303832 345811 := bstep (se 1 (by rfl) ⟨259358, by rfl⟩ : syracuseStep 345811 = 518717) B518717
theorem B411361 : Blo 303832 411361 := bstep (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) B308521
theorem B771889 : Blo 303832 771889 := bstep (se 2 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 771889 = 578917) B578917
theorem B345955 : Blo 303832 345955 := bstep (se 1 (by rfl) ⟨259466, by rfl⟩ : syracuseStep 345955 = 518933) B518933
theorem B346099 : Blo 303832 346099 := bstep (se 1 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 346099 = 519149) B519149
theorem B772163 : Blo 303832 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B3491909 : Blo 303832 3491909 := bstep (se 4 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 3491909 = 654733) B654733
theorem B739459 : Blo 303832 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B346243 : Blo 303832 346243 := bstep (se 1 (by rfl) ⟨259682, by rfl⟩ : syracuseStep 346243 = 519365) B519365
theorem B870563 : Blo 303832 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B1034477 : Blo 303832 1034477 := bstep (se 3 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 1034477 = 387929) B387929
theorem B772355 : Blo 303832 772355 := bstep (se 1 (by rfl) ⟨579266, by rfl⟩ : syracuseStep 772355 = 1158533) B1158533
theorem B1034531 : Blo 303832 1034531 := bstep (se 1 (by rfl) ⟨775898, by rfl⟩ : syracuseStep 1034531 = 1551797) B1551797
theorem B1034801 : Blo 303832 1034801 := bstep (se 2 (by rfl) ⟨388050, by rfl⟩ : syracuseStep 1034801 = 776101) B776101
theorem B3721909 : Blo 303832 3721909 := bstep (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) B348929
theorem B1428515 : Blo 303832 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B1035341 : Blo 303832 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B1035395 : Blo 303832 1035395 := bstep (se 1 (by rfl) ⟨776546, by rfl⟩ : syracuseStep 1035395 = 1553093) B1553093
theorem B773297 : Blo 303832 773297 := bstep (se 2 (by rfl) ⟨289986, by rfl⟩ : syracuseStep 773297 = 579973) B579973
theorem B773347 : Blo 303832 773347 := bstep (se 1 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 773347 = 1160021) B1160021
theorem B773489 : Blo 303832 773489 := bstep (se 2 (by rfl) ⟨290058, by rfl⟩ : syracuseStep 773489 = 580117) B580117
theorem B871793 : Blo 303832 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B1035665 : Blo 303832 1035665 := bstep (se 2 (by rfl) ⟨388374, by rfl⟩ : syracuseStep 1035665 = 776749) B776749
theorem B577201 : Blo 303832 577201 := bstep (se 2 (by rfl) ⟨216450, by rfl⟩ : syracuseStep 577201 = 432901) B432901
theorem B577361 : Blo 303832 577361 := bstep (se 2 (by rfl) ⟨216510, by rfl⟩ : syracuseStep 577361 = 433021) B433021
theorem B2084707 : Blo 303832 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B1036205 : Blo 303832 1036205 := bstep (se 3 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 1036205 = 388577) B388577
theorem B1167281 : Blo 303832 1167281 := bstep (se 2 (by rfl) ⟨437730, by rfl⟩ : syracuseStep 1167281 = 875461) B875461
theorem B1036259 : Blo 303832 1036259 := bstep (se 1 (by rfl) ⟨777194, by rfl⟩ : syracuseStep 1036259 = 1554389) B1554389
theorem B1298531 : Blo 303832 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B413843 : Blo 303832 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B1069283 : Blo 303832 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B577763 : Blo 303832 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B2937073 : Blo 303832 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B1036529 : Blo 303832 1036529 := bstep (se 2 (by rfl) ⟨388698, by rfl⟩ : syracuseStep 1036529 = 777397) B777397
theorem B1331491 : Blo 303832 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B3920197 : Blo 303832 3920197 := bstep (se 4 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 3920197 = 735037) B735037
theorem B774481 : Blo 303832 774481 := bstep (se 2 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 774481 = 580861) B580861
theorem B2118149 : Blo 303832 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B1102385 : Blo 303832 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B774755 : Blo 303832 774755 := bstep (se 1 (by rfl) ⟨581066, by rfl⟩ : syracuseStep 774755 = 1162133) B1162133
theorem B1102499 : Blo 303832 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B512723 : Blo 303832 512723 := bstep (se 1 (by rfl) ⟨384542, by rfl⟩ : syracuseStep 512723 = 769085) B769085
theorem B414433 : Blo 303832 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B1037069 : Blo 303832 1037069 := bstep (se 3 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 1037069 = 388901) B388901
theorem B774947 : Blo 303832 774947 := bstep (se 1 (by rfl) ⟨581210, by rfl⟩ : syracuseStep 774947 = 1162421) B1162421
theorem B873251 : Blo 303832 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B1037123 : Blo 303832 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B512851 : Blo 303832 512851 := bstep (se 1 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 512851 = 769277) B769277
theorem B512993 : Blo 303832 512993 := bstep (se 2 (by rfl) ⟨192372, by rfl⟩ : syracuseStep 512993 = 384745) B384745
theorem B1463309 : Blo 303832 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B1037393 : Blo 303832 1037393 := bstep (se 2 (by rfl) ⟨389022, by rfl⟩ : syracuseStep 1037393 = 778045) B778045
theorem B513121 : Blo 303832 513121 := bstep (se 2 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 513121 = 384841) B384841
theorem B578659 : Blo 303832 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B513155 : Blo 303832 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B513283 : Blo 303832 513283 := bstep (se 1 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 513283 = 769925) B769925
theorem B578819 : Blo 303832 578819 := bstep (se 1 (by rfl) ⟨434114, by rfl⟩ : syracuseStep 578819 = 868229) B868229
theorem B1168739 : Blo 303832 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B513425 : Blo 303832 513425 := bstep (se 2 (by rfl) ⟨192534, by rfl⟩ : syracuseStep 513425 = 385069) B385069
theorem B2315789 : Blo 303832 2315789 := bstep (se 3 (by rfl) ⟨434210, by rfl⟩ : syracuseStep 2315789 = 868421) B868421
theorem B513553 : Blo 303832 513553 := bstep (se 2 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 513553 = 385165) B385165
theorem B513587 : Blo 303832 513587 := bstep (se 1 (by rfl) ⟨385190, by rfl⟩ : syracuseStep 513587 = 770381) B770381
theorem B874061 : Blo 303832 874061 := bstep (se 3 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 874061 = 327773) B327773
theorem B1037933 : Blo 303832 1037933 := bstep (se 3 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 1037933 = 389225) B389225
theorem B1037987 : Blo 303832 1037987 := bstep (se 1 (by rfl) ⟨778490, by rfl⟩ : syracuseStep 1037987 = 1556981) B1556981
theorem B513715 : Blo 303832 513715 := bstep (se 1 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 513715 = 770573) B770573
theorem B8345285 : Blo 303832 8345285 := bstep (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) B1564741
theorem B775889 : Blo 303832 775889 := bstep (se 2 (by rfl) ⟨290958, by rfl⟩ : syracuseStep 775889 = 581917) B581917
theorem B775939 : Blo 303832 775939 := bstep (se 1 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 775939 = 1163909) B1163909
theorem B874253 : Blo 303832 874253 := bstep (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) B327845
theorem B513857 : Blo 303832 513857 := bstep (se 2 (by rfl) ⟨192696, by rfl⟩ : syracuseStep 513857 = 385393) B385393
theorem B776081 : Blo 303832 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B415633 : Blo 303832 415633 := bstep (se 2 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 415633 = 311725) B311725
theorem B1038257 : Blo 303832 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B513985 : Blo 303832 513985 := bstep (se 2 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 513985 = 385489) B385489
theorem B514019 : Blo 303832 514019 := bstep (se 1 (by rfl) ⟨385514, by rfl⟩ : syracuseStep 514019 = 771029) B771029
theorem B514147 : Blo 303832 514147 := bstep (se 1 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 514147 = 771221) B771221
theorem B415859 : Blo 303832 415859 := bstep (se 1 (by rfl) ⟨311894, by rfl⟩ : syracuseStep 415859 = 623789) B623789
theorem B3528845 : Blo 303832 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B3725509 : Blo 303832 3725509 := bstep (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) B698533
theorem B514289 : Blo 303832 514289 := bstep (se 2 (by rfl) ⟨192858, by rfl⟩ : syracuseStep 514289 = 385717) B385717
theorem B579889 : Blo 303832 579889 := bstep (se 2 (by rfl) ⟨217458, by rfl⟩ : syracuseStep 579889 = 434917) B434917
theorem B514417 : Blo 303832 514417 := bstep (se 2 (by rfl) ⟨192906, by rfl⟩ : syracuseStep 514417 = 385813) B385813
theorem B514451 : Blo 303832 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B842147 : Blo 303832 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B1038797 : Blo 303832 1038797 := bstep (se 3 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 1038797 = 389549) B389549
theorem B1038851 : Blo 303832 1038851 := bstep (se 1 (by rfl) ⟨779138, by rfl⟩ : syracuseStep 1038851 = 1558277) B1558277
theorem B514579 : Blo 303832 514579 := bstep (se 1 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 514579 = 771869) B771869
theorem B514721 : Blo 303832 514721 := bstep (se 2 (by rfl) ⟨193020, by rfl⟩ : syracuseStep 514721 = 386041) B386041
theorem B1301197 : Blo 303832 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B875245 : Blo 303832 875245 := bstep (se 3 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 875245 = 328217) B328217
theorem B514849 : Blo 303832 514849 := bstep (se 2 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 514849 = 386137) B386137
theorem B940835 : Blo 303832 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B514883 : Blo 303832 514883 := bstep (se 1 (by rfl) ⟨386162, by rfl⟩ : syracuseStep 514883 = 772325) B772325
theorem B1858403 : Blo 303832 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B1661795 : Blo 303832 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B777073 : Blo 303832 777073 := bstep (se 2 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 777073 = 582805) B582805
theorem B515011 : Blo 303832 515011 := bstep (se 1 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 515011 = 772517) B772517
theorem B3300365 : Blo 303832 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B515153 : Blo 303832 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B777347 : Blo 303832 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B1006769 : Blo 303832 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B515281 : Blo 303832 515281 := bstep (se 2 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 515281 = 386461) B386461
theorem B515315 : Blo 303832 515315 := bstep (se 1 (by rfl) ⟨386486, by rfl⟩ : syracuseStep 515315 = 772973) B772973
theorem B1039661 : Blo 303832 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B777539 : Blo 303832 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B580945 : Blo 303832 580945 := bstep (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) B435709
theorem B515443 : Blo 303832 515443 := bstep (se 1 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 515443 = 773165) B773165
theorem B3300749 : Blo 303832 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B1957283 : Blo 303832 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B515585 : Blo 303832 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B515713 : Blo 303832 515713 := bstep (se 2 (by rfl) ⟨193392, by rfl⟩ : syracuseStep 515713 = 386785) B386785
theorem B515747 : Blo 303832 515747 := bstep (se 1 (by rfl) ⟨386810, by rfl⟩ : syracuseStep 515747 = 773621) B773621
theorem B581347 : Blo 303832 581347 := bstep (se 1 (by rfl) ⟨436010, by rfl⟩ : syracuseStep 581347 = 872021) B872021
theorem B1302257 : Blo 303832 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B974605 : Blo 303832 974605 := bstep (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) B365477
theorem B3497741 : Blo 303832 3497741 := bstep (se 3 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 3497741 = 1311653) B1311653
theorem B581393 : Blo 303832 581393 := bstep (se 2 (by rfl) ⟨218022, by rfl⟩ : syracuseStep 581393 = 436045) B436045
theorem B515875 : Blo 303832 515875 := bstep (se 1 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 515875 = 773813) B773813
theorem B1892165 : Blo 303832 1892165 := bstep (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) B354781
theorem B384851 : Blo 303832 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B745379 : Blo 303832 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B516017 : Blo 303832 516017 := bstep (se 2 (by rfl) ⟨193506, by rfl⟩ : syracuseStep 516017 = 387013) B387013
theorem B417841 : Blo 303832 417841 := bstep (se 2 (by rfl) ⟨156690, by rfl⟩ : syracuseStep 417841 = 313381) B313381
theorem B516145 : Blo 303832 516145 := bstep (se 2 (by rfl) ⟨193554, by rfl⟩ : syracuseStep 516145 = 387109) B387109
theorem B581681 : Blo 303832 581681 := bstep (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) B436261
theorem B516179 : Blo 303832 516179 := bstep (se 1 (by rfl) ⟨387134, by rfl⟩ : syracuseStep 516179 = 774269) B774269
theorem B975053 : Blo 303832 975053 := bstep (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) B365645
theorem B516307 : Blo 303832 516307 := bstep (se 1 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 516307 = 774461) B774461
theorem B778481 : Blo 303832 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B778531 : Blo 303832 778531 := bstep (se 1 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 778531 = 1167797) B1167797
theorem B516449 : Blo 303832 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B2318705 : Blo 303832 2318705 := bstep (se 2 (by rfl) ⟨869514, by rfl⟩ : syracuseStep 2318705 = 1739029) B1739029
theorem B778673 : Blo 303832 778673 := bstep (se 2 (by rfl) ⟨292002, by rfl⟩ : syracuseStep 778673 = 584005) B584005
theorem B516577 : Blo 303832 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B549347 : Blo 303832 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B516611 : Blo 303832 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B385555 : Blo 303832 385555 := bstep (se 1 (by rfl) ⟨289166, by rfl⟩ : syracuseStep 385555 = 578333) B578333
theorem B385651 : Blo 303832 385651 := bstep (se 1 (by rfl) ⟨289238, by rfl⟩ : syracuseStep 385651 = 578477) B578477
theorem B516739 : Blo 303832 516739 := bstep (se 1 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 516739 = 775109) B775109
theorem B582403 : Blo 303832 582403 := bstep (se 1 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 582403 = 873605) B873605
theorem B516881 : Blo 303832 516881 := bstep (se 2 (by rfl) ⟨193830, by rfl⟩ : syracuseStep 516881 = 387661) B387661
theorem B517009 : Blo 303832 517009 := bstep (se 2 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 517009 = 387757) B387757
theorem B517043 : Blo 303832 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B1172465 : Blo 303832 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B517171 : Blo 303832 517171 := bstep (se 1 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 517171 = 775757) B775757
theorem B386147 : Blo 303832 386147 := bstep (se 1 (by rfl) ⟨289610, by rfl⟩ : syracuseStep 386147 = 579221) B579221
theorem B517313 : Blo 303832 517313 := bstep (se 2 (by rfl) ⟨193992, by rfl⟩ : syracuseStep 517313 = 387985) B387985
theorem B582851 : Blo 303832 582851 := bstep (se 1 (by rfl) ⟨437138, by rfl⟩ : syracuseStep 582851 = 874277) B874277
theorem B517441 : Blo 303832 517441 := bstep (se 2 (by rfl) ⟨194040, by rfl⟩ : syracuseStep 517441 = 388081) B388081
theorem B517475 : Blo 303832 517475 := bstep (se 1 (by rfl) ⟨388106, by rfl⟩ : syracuseStep 517475 = 776213) B776213
theorem B517603 : Blo 303832 517603 := bstep (se 1 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 517603 = 776405) B776405
theorem B583139 : Blo 303832 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B517745 : Blo 303832 517745 := bstep (se 2 (by rfl) ⟨194154, by rfl⟩ : syracuseStep 517745 = 388309) B388309
theorem B517873 : Blo 303832 517873 := bstep (se 2 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 517873 = 388405) B388405
theorem B517907 : Blo 303832 517907 := bstep (se 1 (by rfl) ⟨388430, by rfl⟩ : syracuseStep 517907 = 776861) B776861
theorem B386851 : Blo 303832 386851 := bstep (se 1 (by rfl) ⟨290138, by rfl⟩ : syracuseStep 386851 = 580277) B580277
theorem B386947 : Blo 303832 386947 := bstep (se 1 (by rfl) ⟨290210, by rfl⟩ : syracuseStep 386947 = 580421) B580421
theorem B518035 : Blo 303832 518035 := bstep (se 1 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 518035 = 777053) B777053
theorem B518177 : Blo 303832 518177 := bstep (se 2 (by rfl) ⟨194316, by rfl⟩ : syracuseStep 518177 = 388633) B388633
theorem B518305 : Blo 303832 518305 := bstep (se 2 (by rfl) ⟨194364, by rfl⟩ : syracuseStep 518305 = 388729) B388729
theorem B518339 : Blo 303832 518339 := bstep (se 1 (by rfl) ⟨388754, by rfl⟩ : syracuseStep 518339 = 777509) B777509
theorem B1239245 : Blo 303832 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B518467 : Blo 303832 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B387443 : Blo 303832 387443 := bstep (se 1 (by rfl) ⟨290582, by rfl⟩ : syracuseStep 387443 = 581165) B581165
theorem B584081 : Blo 303832 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B518609 : Blo 303832 518609 := bstep (se 2 (by rfl) ⟨194478, by rfl⟩ : syracuseStep 518609 = 388957) B388957
theorem B1993187 : Blo 303832 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B518737 : Blo 303832 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B3500657 : Blo 303832 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B518771 : Blo 303832 518771 := bstep (se 1 (by rfl) ⟨389078, by rfl⟩ : syracuseStep 518771 = 778157) B778157
theorem B1993349 : Blo 303832 1993349 := bstep (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) B373753
theorem B1305229 : Blo 303832 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B2484877 : Blo 303832 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B649873 : Blo 303832 649873 := bstep (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) B487405
theorem B518899 : Blo 303832 518899 := bstep (se 1 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 518899 = 778349) B778349
theorem B1239857 : Blo 303832 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B2190179 : Blo 303832 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B519041 : Blo 303832 519041 := bstep (se 2 (by rfl) ⟨194640, by rfl⟩ : syracuseStep 519041 = 389281) B389281
theorem B977795 : Blo 303832 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B1305571 : Blo 303832 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B519169 : Blo 303832 519169 := bstep (se 2 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 519169 = 389377) B389377
theorem B879619 : Blo 303832 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B977923 : Blo 303832 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B2190349 : Blo 303832 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B519203 : Blo 303832 519203 := bstep (se 1 (by rfl) ⟨389402, by rfl⟩ : syracuseStep 519203 = 778805) B778805
theorem B388147 : Blo 303832 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B388243 : Blo 303832 388243 := bstep (se 1 (by rfl) ⟨291182, by rfl⟩ : syracuseStep 388243 = 582365) B582365
theorem B519331 : Blo 303832 519331 := bstep (se 1 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 519331 = 778997) B778997
theorem B650531 : Blo 303832 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B978257 : Blo 303832 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B486739 : Blo 303832 486739 := bstep (se 1 (by rfl) ⟨365054, by rfl⟩ : syracuseStep 486739 = 730109) B730109
theorem B1961329 : Blo 303832 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B388739 : Blo 303832 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B5893829 : Blo 303832 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B683729 : Blo 303832 683729 := bstep (se 2 (by rfl) ⟨256398, by rfl⟩ : syracuseStep 683729 = 512797) B512797
theorem B683747 : Blo 303832 683747 := bstep (se 1 (by rfl) ⟨512810, by rfl⟩ : syracuseStep 683747 = 1025621) B1025621
theorem B684017 : Blo 303832 684017 := bstep (se 2 (by rfl) ⟨256506, by rfl⟩ : syracuseStep 684017 = 513013) B513013
theorem B684035 : Blo 303832 684035 := bstep (se 1 (by rfl) ⟨513026, by rfl⟩ : syracuseStep 684035 = 1026053) B1026053
theorem B651377 : Blo 303832 651377 := bstep (se 2 (by rfl) ⟨244266, by rfl⟩ : syracuseStep 651377 = 488533) B488533
theorem B487667 : Blo 303832 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B684305 : Blo 303832 684305 := bstep (se 2 (by rfl) ⟨256614, by rfl⟩ : syracuseStep 684305 = 513229) B513229
theorem B684323 : Blo 303832 684323 := bstep (se 1 (by rfl) ⟨513242, by rfl⟩ : syracuseStep 684323 = 1026485) B1026485
theorem B782627 : Blo 303832 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B389443 : Blo 303832 389443 := bstep (se 1 (by rfl) ⟨292082, by rfl⟩ : syracuseStep 389443 = 584165) B584165
theorem B389539 : Blo 303832 389539 := bstep (se 1 (by rfl) ⟨292154, by rfl⟩ : syracuseStep 389539 = 584309) B584309
theorem B487937 : Blo 303832 487937 := bstep (se 2 (by rfl) ⟨182976, by rfl⟩ : syracuseStep 487937 = 365953) B365953
theorem B1045037 : Blo 303832 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B684593 : Blo 303832 684593 := bstep (se 2 (by rfl) ⟨256722, by rfl⟩ : syracuseStep 684593 = 513445) B513445
theorem B684611 : Blo 303832 684611 := bstep (se 1 (by rfl) ⟨513458, by rfl⟩ : syracuseStep 684611 = 1026917) B1026917
theorem B1733197 : Blo 303832 1733197 := bstep (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) B649949
theorem B520931 : Blo 303832 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B488225 : Blo 303832 488225 := bstep (se 2 (by rfl) ⟨183084, by rfl⟩ : syracuseStep 488225 = 366169) B366169
theorem B684881 : Blo 303832 684881 := bstep (se 2 (by rfl) ⟨256830, by rfl⟩ : syracuseStep 684881 = 513661) B513661
theorem B684899 : Blo 303832 684899 := bstep (se 1 (by rfl) ⟨513674, by rfl⟩ : syracuseStep 684899 = 1027349) B1027349
theorem B1471459 : Blo 303832 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B324595 : Blo 303832 324595 := bstep (se 1 (by rfl) ⟨243446, by rfl⟩ : syracuseStep 324595 = 486893) B486893
theorem B455777 : Blo 303832 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B685169 : Blo 303832 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B455795 : Blo 303832 455795 := bstep (se 1 (by rfl) ⟨341846, by rfl⟩ : syracuseStep 455795 = 683693) B683693
theorem B685187 : Blo 303832 685187 := bstep (se 1 (by rfl) ⟨513890, by rfl⟩ : syracuseStep 685187 = 1027781) B1027781
theorem B455825 : Blo 303832 455825 := bstep (se 2 (by rfl) ⟨170934, by rfl⟩ : syracuseStep 455825 = 341869) B341869
theorem B455843 : Blo 303832 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B455873 : Blo 303832 455873 := bstep (se 2 (by rfl) ⟨170952, by rfl⟩ : syracuseStep 455873 = 341905) B341905
theorem B488641 : Blo 303832 488641 := bstep (se 2 (by rfl) ⟨183240, by rfl⟩ : syracuseStep 488641 = 366481) B366481
theorem B455891 : Blo 303832 455891 := bstep (se 1 (by rfl) ⟨341918, by rfl⟩ : syracuseStep 455891 = 683837) B683837
theorem B455921 : Blo 303832 455921 := bstep (se 2 (by rfl) ⟨170970, by rfl⟩ : syracuseStep 455921 = 341941) B341941
theorem B455939 : Blo 303832 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B455969 : Blo 303832 455969 := bstep (se 2 (by rfl) ⟨170988, by rfl⟩ : syracuseStep 455969 = 341977) B341977
theorem B455987 : Blo 303832 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B456017 : Blo 303832 456017 := bstep (se 2 (by rfl) ⟨171006, by rfl⟩ : syracuseStep 456017 = 342013) B342013
theorem B456035 : Blo 303832 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B456065 : Blo 303832 456065 := bstep (se 2 (by rfl) ⟨171024, by rfl⟩ : syracuseStep 456065 = 342049) B342049
theorem B685457 : Blo 303832 685457 := bstep (se 2 (by rfl) ⟨257046, by rfl⟩ : syracuseStep 685457 = 514093) B514093
theorem B456083 : Blo 303832 456083 := bstep (se 1 (by rfl) ⟨342062, by rfl⟩ : syracuseStep 456083 = 684125) B684125
theorem B685475 : Blo 303832 685475 := bstep (se 1 (by rfl) ⟨514106, by rfl⟩ : syracuseStep 685475 = 1028213) B1028213
theorem B456113 : Blo 303832 456113 := bstep (se 2 (by rfl) ⟨171042, by rfl⟩ : syracuseStep 456113 = 342085) B342085
theorem B456131 : Blo 303832 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B456161 : Blo 303832 456161 := bstep (se 2 (by rfl) ⟨171060, by rfl⟩ : syracuseStep 456161 = 342121) B342121
theorem B456179 : Blo 303832 456179 := bstep (se 1 (by rfl) ⟨342134, by rfl⟩ : syracuseStep 456179 = 684269) B684269
theorem B456209 : Blo 303832 456209 := bstep (se 2 (by rfl) ⟨171078, by rfl⟩ : syracuseStep 456209 = 342157) B342157
theorem B456227 : Blo 303832 456227 := bstep (se 1 (by rfl) ⟨342170, by rfl⟩ : syracuseStep 456227 = 684341) B684341
theorem B456257 : Blo 303832 456257 := bstep (se 2 (by rfl) ⟨171096, by rfl⟩ : syracuseStep 456257 = 342193) B342193
theorem B456275 : Blo 303832 456275 := bstep (se 1 (by rfl) ⟨342206, by rfl⟩ : syracuseStep 456275 = 684413) B684413
theorem B456305 : Blo 303832 456305 := bstep (se 2 (by rfl) ⟨171114, by rfl⟩ : syracuseStep 456305 = 342229) B342229
theorem B456323 : Blo 303832 456323 := bstep (se 1 (by rfl) ⟨342242, by rfl⟩ : syracuseStep 456323 = 684485) B684485
theorem B456353 : Blo 303832 456353 := bstep (se 2 (by rfl) ⟨171132, by rfl⟩ : syracuseStep 456353 = 342265) B342265
theorem B685745 : Blo 303832 685745 := bstep (se 2 (by rfl) ⟨257154, by rfl⟩ : syracuseStep 685745 = 514309) B514309
theorem B456371 : Blo 303832 456371 := bstep (se 1 (by rfl) ⟨342278, by rfl⟩ : syracuseStep 456371 = 684557) B684557
theorem B685763 : Blo 303832 685763 := bstep (se 1 (by rfl) ⟨514322, by rfl⟩ : syracuseStep 685763 = 1028645) B1028645
theorem B456401 : Blo 303832 456401 := bstep (se 2 (by rfl) ⟨171150, by rfl⟩ : syracuseStep 456401 = 342301) B342301
theorem B456419 : Blo 303832 456419 := bstep (se 1 (by rfl) ⟨342314, by rfl⟩ : syracuseStep 456419 = 684629) B684629
theorem B456449 : Blo 303832 456449 := bstep (se 2 (by rfl) ⟨171168, by rfl⟩ : syracuseStep 456449 = 342337) B342337
theorem B653059 : Blo 303832 653059 := bstep (se 1 (by rfl) ⟨489794, by rfl⟩ : syracuseStep 653059 = 979589) B979589
theorem B456467 : Blo 303832 456467 := bstep (se 1 (by rfl) ⟨342350, by rfl⟩ : syracuseStep 456467 = 684701) B684701
theorem B456497 : Blo 303832 456497 := bstep (se 2 (by rfl) ⟨171186, by rfl⟩ : syracuseStep 456497 = 342373) B342373
theorem B456515 : Blo 303832 456515 := bstep (se 1 (by rfl) ⟨342386, by rfl⟩ : syracuseStep 456515 = 684773) B684773
theorem B456545 : Blo 303832 456545 := bstep (se 2 (by rfl) ⟨171204, by rfl⟩ : syracuseStep 456545 = 342409) B342409
theorem B456563 : Blo 303832 456563 := bstep (se 1 (by rfl) ⟨342422, by rfl⟩ : syracuseStep 456563 = 684845) B684845
theorem B456593 : Blo 303832 456593 := bstep (se 2 (by rfl) ⟨171222, by rfl⟩ : syracuseStep 456593 = 342445) B342445
theorem B587665 : Blo 303832 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B456611 : Blo 303832 456611 := bstep (se 1 (by rfl) ⟨342458, by rfl⟩ : syracuseStep 456611 = 684917) B684917
theorem B456641 : Blo 303832 456641 := bstep (se 2 (by rfl) ⟨171240, by rfl⟩ : syracuseStep 456641 = 342481) B342481
theorem B686033 : Blo 303832 686033 := bstep (se 2 (by rfl) ⟨257262, by rfl⟩ : syracuseStep 686033 = 514525) B514525
theorem B456659 : Blo 303832 456659 := bstep (se 1 (by rfl) ⟨342494, by rfl⟩ : syracuseStep 456659 = 684989) B684989
theorem B686051 : Blo 303832 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B456689 : Blo 303832 456689 := bstep (se 2 (by rfl) ⟨171258, by rfl⟩ : syracuseStep 456689 = 342517) B342517
theorem B456707 : Blo 303832 456707 := bstep (se 1 (by rfl) ⟨342530, by rfl⟩ : syracuseStep 456707 = 685061) B685061
theorem B456737 : Blo 303832 456737 := bstep (se 2 (by rfl) ⟨171276, by rfl⟩ : syracuseStep 456737 = 342553) B342553
theorem B325667 : Blo 303832 325667 := bstep (se 1 (by rfl) ⟨244250, by rfl⟩ : syracuseStep 325667 = 488501) B488501
theorem B1767473 : Blo 303832 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B456755 : Blo 303832 456755 := bstep (se 1 (by rfl) ⟨342566, by rfl⟩ : syracuseStep 456755 = 685133) B685133
theorem B489539 : Blo 303832 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B456785 : Blo 303832 456785 := bstep (se 2 (by rfl) ⟨171294, by rfl⟩ : syracuseStep 456785 = 342589) B342589
theorem B456803 : Blo 303832 456803 := bstep (se 1 (by rfl) ⟨342602, by rfl⟩ : syracuseStep 456803 = 685205) B685205
theorem B456833 : Blo 303832 456833 := bstep (se 2 (by rfl) ⟨171312, by rfl⟩ : syracuseStep 456833 = 342625) B342625
theorem B1538189 : Blo 303832 1538189 := bstep (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) B576821
theorem B456851 : Blo 303832 456851 := bstep (se 1 (by rfl) ⟨342638, by rfl⟩ : syracuseStep 456851 = 685277) B685277
theorem B456881 : Blo 303832 456881 := bstep (se 2 (by rfl) ⟨171330, by rfl⟩ : syracuseStep 456881 = 342661) B342661
theorem B4159669 : Blo 303832 4159669 := bstep (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) B389969
theorem B456899 : Blo 303832 456899 := bstep (se 1 (by rfl) ⟨342674, by rfl⟩ : syracuseStep 456899 = 685349) B685349
theorem B653521 : Blo 303832 653521 := bstep (se 2 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 653521 = 490141) B490141
theorem B456929 : Blo 303832 456929 := bstep (se 2 (by rfl) ⟨171348, by rfl⟩ : syracuseStep 456929 = 342697) B342697
theorem B981229 : Blo 303832 981229 := bstep (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) B367961
theorem B686321 : Blo 303832 686321 := bstep (se 2 (by rfl) ⟨257370, by rfl⟩ : syracuseStep 686321 = 514741) B514741
theorem B456947 : Blo 303832 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B686339 : Blo 303832 686339 := bstep (se 1 (by rfl) ⟨514754, by rfl⟩ : syracuseStep 686339 = 1029509) B1029509
theorem B456977 : Blo 303832 456977 := bstep (se 2 (by rfl) ⟨171366, by rfl⟩ : syracuseStep 456977 = 342733) B342733
theorem B456995 : Blo 303832 456995 := bstep (se 1 (by rfl) ⟨342746, by rfl⟩ : syracuseStep 456995 = 685493) B685493
theorem B489763 : Blo 303832 489763 := bstep (se 1 (by rfl) ⟨367322, by rfl⟩ : syracuseStep 489763 = 734645) B734645
theorem B457025 : Blo 303832 457025 := bstep (se 2 (by rfl) ⟨171384, by rfl⟩ : syracuseStep 457025 = 342769) B342769
theorem B457043 : Blo 303832 457043 := bstep (se 1 (by rfl) ⟨342782, by rfl⟩ : syracuseStep 457043 = 685565) B685565
theorem B457073 : Blo 303832 457073 := bstep (se 2 (by rfl) ⟨171402, by rfl⟩ : syracuseStep 457073 = 342805) B342805
theorem B457091 : Blo 303832 457091 := bstep (se 1 (by rfl) ⟨342818, by rfl⟩ : syracuseStep 457091 = 685637) B685637
theorem B457121 : Blo 303832 457121 := bstep (se 2 (by rfl) ⟨171420, by rfl⟩ : syracuseStep 457121 = 342841) B342841
theorem B457139 : Blo 303832 457139 := bstep (se 1 (by rfl) ⟨342854, by rfl⟩ : syracuseStep 457139 = 685709) B685709
theorem B457169 : Blo 303832 457169 := bstep (se 2 (by rfl) ⟨171438, by rfl⟩ : syracuseStep 457169 = 342877) B342877
theorem B457187 : Blo 303832 457187 := bstep (se 1 (by rfl) ⟨342890, by rfl⟩ : syracuseStep 457187 = 685781) B685781
theorem B981485 : Blo 303832 981485 := bstep (se 3 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 981485 = 368057) B368057
theorem B457217 : Blo 303832 457217 := bstep (se 2 (by rfl) ⟨171456, by rfl⟩ : syracuseStep 457217 = 342913) B342913
theorem B1735181 : Blo 303832 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B686609 : Blo 303832 686609 := bstep (se 2 (by rfl) ⟨257478, by rfl⟩ : syracuseStep 686609 = 514957) B514957
theorem B457235 : Blo 303832 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B686627 : Blo 303832 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B457265 : Blo 303832 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B457283 : Blo 303832 457283 := bstep (se 1 (by rfl) ⟨342962, by rfl⟩ : syracuseStep 457283 = 685925) B685925
theorem B457313 : Blo 303832 457313 := bstep (se 2 (by rfl) ⟨171492, by rfl⟩ : syracuseStep 457313 = 342985) B342985
theorem B457331 : Blo 303832 457331 := bstep (se 1 (by rfl) ⟨342998, by rfl⟩ : syracuseStep 457331 = 685997) B685997
theorem B457361 : Blo 303832 457361 := bstep (se 2 (by rfl) ⟨171510, by rfl⟩ : syracuseStep 457361 = 343021) B343021
theorem B457379 : Blo 303832 457379 := bstep (se 1 (by rfl) ⟨343034, by rfl⟩ : syracuseStep 457379 = 686069) B686069
theorem B457409 : Blo 303832 457409 := bstep (se 2 (by rfl) ⟨171528, by rfl⟩ : syracuseStep 457409 = 343057) B343057
theorem B457427 : Blo 303832 457427 := bstep (se 1 (by rfl) ⟨343070, by rfl⟩ : syracuseStep 457427 = 686141) B686141
theorem B457457 : Blo 303832 457457 := bstep (se 2 (by rfl) ⟨171546, by rfl⟩ : syracuseStep 457457 = 343093) B343093
theorem B457475 : Blo 303832 457475 := bstep (se 1 (by rfl) ⟨343106, by rfl⟩ : syracuseStep 457475 = 686213) B686213
theorem B457505 : Blo 303832 457505 := bstep (se 2 (by rfl) ⟨171564, by rfl⟩ : syracuseStep 457505 = 343129) B343129
theorem B686897 : Blo 303832 686897 := bstep (se 2 (by rfl) ⟨257586, by rfl⟩ : syracuseStep 686897 = 515173) B515173
theorem B457523 : Blo 303832 457523 := bstep (se 1 (by rfl) ⟨343142, by rfl⟩ : syracuseStep 457523 = 686285) B686285
theorem B686915 : Blo 303832 686915 := bstep (se 1 (by rfl) ⟨515186, by rfl⟩ : syracuseStep 686915 = 1030373) B1030373
theorem B457553 : Blo 303832 457553 := bstep (se 2 (by rfl) ⟨171582, by rfl⟩ : syracuseStep 457553 = 343165) B343165
theorem B457571 : Blo 303832 457571 := bstep (se 1 (by rfl) ⟨343178, by rfl⟩ : syracuseStep 457571 = 686357) B686357
theorem B457601 : Blo 303832 457601 := bstep (se 2 (by rfl) ⟨171600, by rfl⟩ : syracuseStep 457601 = 343201) B343201
theorem B588689 : Blo 303832 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B457619 : Blo 303832 457619 := bstep (se 1 (by rfl) ⟨343214, by rfl⟩ : syracuseStep 457619 = 686429) B686429
theorem B1309603 : Blo 303832 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B457649 : Blo 303832 457649 := bstep (se 2 (by rfl) ⟨171618, by rfl⟩ : syracuseStep 457649 = 343237) B343237
theorem B457667 : Blo 303832 457667 := bstep (se 1 (by rfl) ⟨343250, by rfl⟩ : syracuseStep 457667 = 686501) B686501
theorem B2489285 : Blo 303832 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B457697 : Blo 303832 457697 := bstep (se 2 (by rfl) ⟨171636, by rfl⟩ : syracuseStep 457697 = 343273) B343273
theorem B457715 : Blo 303832 457715 := bstep (se 1 (by rfl) ⟨343286, by rfl⟩ : syracuseStep 457715 = 686573) B686573
theorem B457745 : Blo 303832 457745 := bstep (se 2 (by rfl) ⟨171654, by rfl⟩ : syracuseStep 457745 = 343309) B343309
theorem B457763 : Blo 303832 457763 := bstep (se 1 (by rfl) ⟨343322, by rfl⟩ : syracuseStep 457763 = 686645) B686645
theorem B457793 : Blo 303832 457793 := bstep (se 2 (by rfl) ⟨171672, by rfl⟩ : syracuseStep 457793 = 343345) B343345
theorem B687185 : Blo 303832 687185 := bstep (se 2 (by rfl) ⟨257694, by rfl⟩ : syracuseStep 687185 = 515389) B515389
theorem B457811 : Blo 303832 457811 := bstep (se 1 (by rfl) ⟨343358, by rfl⟩ : syracuseStep 457811 = 686717) B686717
theorem B687203 : Blo 303832 687203 := bstep (se 1 (by rfl) ⟨515402, by rfl⟩ : syracuseStep 687203 = 1030805) B1030805
theorem B457841 : Blo 303832 457841 := bstep (se 2 (by rfl) ⟨171690, by rfl⟩ : syracuseStep 457841 = 343381) B343381
theorem B457859 : Blo 303832 457859 := bstep (se 1 (by rfl) ⟨343394, by rfl⟩ : syracuseStep 457859 = 686789) B686789
theorem B2784397 : Blo 303832 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B621713 : Blo 303832 621713 := bstep (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) B466285
theorem B326803 : Blo 303832 326803 := bstep (se 1 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 326803 = 490205) B490205
theorem B457889 : Blo 303832 457889 := bstep (se 2 (by rfl) ⟨171708, by rfl⟩ : syracuseStep 457889 = 343417) B343417
theorem B457907 : Blo 303832 457907 := bstep (se 1 (by rfl) ⟨343430, by rfl⟩ : syracuseStep 457907 = 686861) B686861
theorem B457937 : Blo 303832 457937 := bstep (se 2 (by rfl) ⟨171726, by rfl⟩ : syracuseStep 457937 = 343453) B343453
theorem B457955 : Blo 303832 457955 := bstep (se 1 (by rfl) ⟨343466, by rfl⟩ : syracuseStep 457955 = 686933) B686933
theorem B14908643 : Blo 303832 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B654563 : Blo 303832 654563 := bstep (se 1 (by rfl) ⟨490922, by rfl⟩ : syracuseStep 654563 = 981845) B981845
theorem B457985 : Blo 303832 457985 := bstep (se 2 (by rfl) ⟨171744, by rfl⟩ : syracuseStep 457985 = 343489) B343489
theorem B490769 : Blo 303832 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B458003 : Blo 303832 458003 := bstep (se 1 (by rfl) ⟨343502, by rfl⟩ : syracuseStep 458003 = 687005) B687005
theorem B458033 : Blo 303832 458033 := bstep (se 2 (by rfl) ⟨171762, by rfl⟩ : syracuseStep 458033 = 343525) B343525
theorem B458051 : Blo 303832 458051 := bstep (se 1 (by rfl) ⟨343538, by rfl⟩ : syracuseStep 458051 = 687077) B687077
theorem B458081 : Blo 303832 458081 := bstep (se 2 (by rfl) ⟨171780, by rfl⟩ : syracuseStep 458081 = 343561) B343561
theorem B687473 : Blo 303832 687473 := bstep (se 2 (by rfl) ⟨257802, by rfl⟩ : syracuseStep 687473 = 515605) B515605
theorem B458099 : Blo 303832 458099 := bstep (se 1 (by rfl) ⟨343574, by rfl⟩ : syracuseStep 458099 = 687149) B687149
theorem B687491 : Blo 303832 687491 := bstep (se 1 (by rfl) ⟨515618, by rfl⟩ : syracuseStep 687491 = 1031237) B1031237
theorem B458129 : Blo 303832 458129 := bstep (se 2 (by rfl) ⟨171798, by rfl⟩ : syracuseStep 458129 = 343597) B343597
theorem B458147 : Blo 303832 458147 := bstep (se 1 (by rfl) ⟨343610, by rfl⟩ : syracuseStep 458147 = 687221) B687221
theorem B1736113 : Blo 303832 1736113 := bstep (se 2 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 1736113 = 1302085) B1302085
theorem B458177 : Blo 303832 458177 := bstep (se 2 (by rfl) ⟨171816, by rfl⟩ : syracuseStep 458177 = 343633) B343633
theorem B1473997 : Blo 303832 1473997 := bstep (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) B552749
theorem B490961 : Blo 303832 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B458195 : Blo 303832 458195 := bstep (se 1 (by rfl) ⟨343646, by rfl⟩ : syracuseStep 458195 = 687293) B687293
theorem B458225 : Blo 303832 458225 := bstep (se 2 (by rfl) ⟨171834, by rfl⟩ : syracuseStep 458225 = 343669) B343669
theorem B458243 : Blo 303832 458243 := bstep (se 1 (by rfl) ⟨343682, by rfl⟩ : syracuseStep 458243 = 687365) B687365
theorem B458273 : Blo 303832 458273 := bstep (se 2 (by rfl) ⟨171852, by rfl⟩ : syracuseStep 458273 = 343705) B343705
theorem B458291 : Blo 303832 458291 := bstep (se 1 (by rfl) ⟨343718, by rfl⟩ : syracuseStep 458291 = 687437) B687437
theorem B458321 : Blo 303832 458321 := bstep (se 2 (by rfl) ⟨171870, by rfl⟩ : syracuseStep 458321 = 343741) B343741
theorem B458339 : Blo 303832 458339 := bstep (se 1 (by rfl) ⟨343754, by rfl⟩ : syracuseStep 458339 = 687509) B687509
theorem B458369 : Blo 303832 458369 := bstep (se 2 (by rfl) ⟨171888, by rfl⟩ : syracuseStep 458369 = 343777) B343777
theorem B687761 : Blo 303832 687761 := bstep (se 2 (by rfl) ⟨257910, by rfl⟩ : syracuseStep 687761 = 515821) B515821
theorem B458387 : Blo 303832 458387 := bstep (se 1 (by rfl) ⟨343790, by rfl⟩ : syracuseStep 458387 = 687581) B687581
theorem B687779 : Blo 303832 687779 := bstep (se 1 (by rfl) ⟨515834, by rfl⟩ : syracuseStep 687779 = 1031669) B1031669
theorem B458417 : Blo 303832 458417 := bstep (se 2 (by rfl) ⟨171906, by rfl⟩ : syracuseStep 458417 = 343813) B343813
theorem B1048241 : Blo 303832 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B458435 : Blo 303832 458435 := bstep (se 1 (by rfl) ⟨343826, by rfl⟩ : syracuseStep 458435 = 687653) B687653
theorem B458465 : Blo 303832 458465 := bstep (se 2 (by rfl) ⟨171924, by rfl⟩ : syracuseStep 458465 = 343849) B343849
theorem B655075 : Blo 303832 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B458483 : Blo 303832 458483 := bstep (se 1 (by rfl) ⟨343862, by rfl⟩ : syracuseStep 458483 = 687725) B687725
theorem B458513 : Blo 303832 458513 := bstep (se 2 (by rfl) ⟨171942, by rfl⟩ : syracuseStep 458513 = 343885) B343885
theorem B458531 : Blo 303832 458531 := bstep (se 1 (by rfl) ⟨343898, by rfl⟩ : syracuseStep 458531 = 687797) B687797
theorem B458561 : Blo 303832 458561 := bstep (se 2 (by rfl) ⟨171960, by rfl⟩ : syracuseStep 458561 = 343921) B343921
theorem B458579 : Blo 303832 458579 := bstep (se 1 (by rfl) ⟨343934, by rfl⟩ : syracuseStep 458579 = 687869) B687869
theorem B458609 : Blo 303832 458609 := bstep (se 2 (by rfl) ⟨171978, by rfl⟩ : syracuseStep 458609 = 343957) B343957
theorem B458627 : Blo 303832 458627 := bstep (se 1 (by rfl) ⟨343970, by rfl⟩ : syracuseStep 458627 = 687941) B687941
theorem B458657 : Blo 303832 458657 := bstep (se 2 (by rfl) ⟨171996, by rfl⟩ : syracuseStep 458657 = 343993) B343993
theorem B688049 : Blo 303832 688049 := bstep (se 2 (by rfl) ⟨258018, by rfl⟩ : syracuseStep 688049 = 516037) B516037
theorem B458675 : Blo 303832 458675 := bstep (se 1 (by rfl) ⟨344006, by rfl⟩ : syracuseStep 458675 = 688013) B688013
theorem B688067 : Blo 303832 688067 := bstep (se 1 (by rfl) ⟨516050, by rfl⟩ : syracuseStep 688067 = 1032101) B1032101
theorem B458705 : Blo 303832 458705 := bstep (se 2 (by rfl) ⟨172014, by rfl⟩ : syracuseStep 458705 = 344029) B344029
theorem B458723 : Blo 303832 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B983011 : Blo 303832 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B688139 : Blo 303832 688139 := bstep (se 1 (by rfl) ⟨516104, by rfl⟩ : syracuseStep 688139 = 1032209) B1032209
theorem B458777 : Blo 303832 458777 := bstep (se 2 (by rfl) ⟨172041, by rfl⟩ : syracuseStep 458777 = 344083) B344083
theorem B688193 : Blo 303832 688193 := bstep (se 2 (by rfl) ⟨258072, by rfl⟩ : syracuseStep 688193 = 516145) B516145
theorem B458891 : Blo 303832 458891 := bstep (se 1 (by rfl) ⟨344168, by rfl⟩ : syracuseStep 458891 = 688337) B688337
theorem B458903 : Blo 303832 458903 := bstep (se 1 (by rfl) ⟨344177, by rfl⟩ : syracuseStep 458903 = 688355) B688355
theorem B458969 : Blo 303832 458969 := bstep (se 2 (by rfl) ⟨172113, by rfl⟩ : syracuseStep 458969 = 344227) B344227
theorem B622849 : Blo 303832 622849 := bstep (se 2 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 622849 = 467137) B467137
theorem B2228485 : Blo 303832 2228485 := bstep (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) B417841
theorem B688409 : Blo 303832 688409 := bstep (se 2 (by rfl) ⟨258153, by rfl⟩ : syracuseStep 688409 = 516307) B516307
theorem B459083 : Blo 303832 459083 := bstep (se 1 (by rfl) ⟨344312, by rfl⟩ : syracuseStep 459083 = 688625) B688625
theorem B459095 : Blo 303832 459095 := bstep (se 1 (by rfl) ⟨344321, by rfl⟩ : syracuseStep 459095 = 688643) B688643
theorem B688499 : Blo 303832 688499 := bstep (se 1 (by rfl) ⟨516374, by rfl⟩ : syracuseStep 688499 = 1032749) B1032749
theorem B688535 : Blo 303832 688535 := bstep (se 1 (by rfl) ⟨516401, by rfl⟩ : syracuseStep 688535 = 1032803) B1032803
theorem B459161 : Blo 303832 459161 := bstep (se 2 (by rfl) ⟨172185, by rfl⟩ : syracuseStep 459161 = 344371) B344371
theorem B4260275 : Blo 303832 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B459275 : Blo 303832 459275 := bstep (se 1 (by rfl) ⟨344456, by rfl⟩ : syracuseStep 459275 = 688913) B688913
theorem B459287 : Blo 303832 459287 := bstep (se 1 (by rfl) ⟨344465, by rfl⟩ : syracuseStep 459287 = 688931) B688931
theorem B655895 : Blo 303832 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B688715 : Blo 303832 688715 := bstep (se 1 (by rfl) ⟨516536, by rfl⟩ : syracuseStep 688715 = 1033073) B1033073
theorem B983627 : Blo 303832 983627 := bstep (se 1 (by rfl) ⟨737720, by rfl⟩ : syracuseStep 983627 = 1475441) B1475441
theorem B459353 : Blo 303832 459353 := bstep (se 2 (by rfl) ⟨172257, by rfl⟩ : syracuseStep 459353 = 344515) B344515
theorem B2851421 : Blo 303832 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B688769 : Blo 303832 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B328375 : Blo 303832 328375 := bstep (se 1 (by rfl) ⟨246281, by rfl⟩ : syracuseStep 328375 = 492563) B492563
theorem B459467 : Blo 303832 459467 := bstep (se 1 (by rfl) ⟨344600, by rfl⟩ : syracuseStep 459467 = 689201) B689201
theorem B459479 : Blo 303832 459479 := bstep (se 1 (by rfl) ⟨344609, by rfl⟩ : syracuseStep 459479 = 689219) B689219
theorem B459545 : Blo 303832 459545 := bstep (se 2 (by rfl) ⟨172329, by rfl⟩ : syracuseStep 459545 = 344659) B344659
theorem B656203 : Blo 303832 656203 := bstep (se 1 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 656203 = 984305) B984305
theorem B688985 : Blo 303832 688985 := bstep (se 2 (by rfl) ⟨258369, by rfl⟩ : syracuseStep 688985 = 516739) B516739
theorem B459659 : Blo 303832 459659 := bstep (se 1 (by rfl) ⟨344744, by rfl⟩ : syracuseStep 459659 = 689489) B689489
theorem B459671 : Blo 303832 459671 := bstep (se 1 (by rfl) ⟨344753, by rfl⟩ : syracuseStep 459671 = 689507) B689507
theorem B689075 : Blo 303832 689075 := bstep (se 1 (by rfl) ⟨516806, by rfl⟩ : syracuseStep 689075 = 1033613) B1033613
theorem B328631 : Blo 303832 328631 := bstep (se 1 (by rfl) ⟨246473, by rfl⟩ : syracuseStep 328631 = 492947) B492947
theorem B689111 : Blo 303832 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B459737 : Blo 303832 459737 := bstep (se 2 (by rfl) ⟨172401, by rfl⟩ : syracuseStep 459737 = 344803) B344803
theorem B885725 : Blo 303832 885725 := bstep (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) B332147
theorem B623627 : Blo 303832 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B459851 : Blo 303832 459851 := bstep (se 1 (by rfl) ⟨344888, by rfl⟩ : syracuseStep 459851 = 689777) B689777
theorem B459863 : Blo 303832 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B689291 : Blo 303832 689291 := bstep (se 1 (by rfl) ⟨516968, by rfl⟩ : syracuseStep 689291 = 1033937) B1033937
theorem B459929 : Blo 303832 459929 := bstep (se 2 (by rfl) ⟨172473, by rfl⟩ : syracuseStep 459929 = 344947) B344947
theorem B689345 : Blo 303832 689345 := bstep (se 2 (by rfl) ⟨258504, by rfl⟩ : syracuseStep 689345 = 517009) B517009
theorem B328907 : Blo 303832 328907 := bstep (se 1 (by rfl) ⟨246680, by rfl⟩ : syracuseStep 328907 = 493361) B493361
theorem B460043 : Blo 303832 460043 := bstep (se 1 (by rfl) ⟨345032, by rfl⟩ : syracuseStep 460043 = 690065) B690065
theorem B460055 : Blo 303832 460055 := bstep (se 1 (by rfl) ⟨345041, by rfl⟩ : syracuseStep 460055 = 690083) B690083
theorem B460121 : Blo 303832 460121 := bstep (se 2 (by rfl) ⟨172545, by rfl⟩ : syracuseStep 460121 = 345091) B345091
theorem B2327939 : Blo 303832 2327939 := bstep (se 1 (by rfl) ⟨1745954, by rfl⟩ : syracuseStep 2327939 = 3491909) B3491909
theorem B689561 : Blo 303832 689561 := bstep (se 2 (by rfl) ⟨258585, by rfl⟩ : syracuseStep 689561 = 517171) B517171
theorem B460235 : Blo 303832 460235 := bstep (se 1 (by rfl) ⟨345176, by rfl⟩ : syracuseStep 460235 = 690353) B690353
theorem B460247 : Blo 303832 460247 := bstep (se 1 (by rfl) ⟨345185, by rfl⟩ : syracuseStep 460247 = 690371) B690371
theorem B689651 : Blo 303832 689651 := bstep (se 1 (by rfl) ⟨517238, by rfl⟩ : syracuseStep 689651 = 1034477) B1034477
theorem B689687 : Blo 303832 689687 := bstep (se 1 (by rfl) ⟨517265, by rfl⟩ : syracuseStep 689687 = 1034531) B1034531
theorem B460313 : Blo 303832 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B1312321 : Blo 303832 1312321 := bstep (se 2 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 1312321 = 984241) B984241
theorem B460427 : Blo 303832 460427 := bstep (se 1 (by rfl) ⟨345320, by rfl⟩ : syracuseStep 460427 = 690641) B690641
theorem B460439 : Blo 303832 460439 := bstep (se 1 (by rfl) ⟨345329, by rfl⟩ : syracuseStep 460439 = 690659) B690659
theorem B689867 : Blo 303832 689867 := bstep (se 1 (by rfl) ⟨517400, by rfl⟩ : syracuseStep 689867 = 1034801) B1034801
theorem B460505 : Blo 303832 460505 := bstep (se 2 (by rfl) ⟨172689, by rfl⟩ : syracuseStep 460505 = 345379) B345379
theorem B689921 : Blo 303832 689921 := bstep (se 2 (by rfl) ⟨258720, by rfl⟩ : syracuseStep 689921 = 517441) B517441
theorem B460619 : Blo 303832 460619 := bstep (se 1 (by rfl) ⟨345464, by rfl⟩ : syracuseStep 460619 = 690929) B690929
theorem B460631 : Blo 303832 460631 := bstep (se 1 (by rfl) ⟨345473, by rfl⟩ : syracuseStep 460631 = 690947) B690947
theorem B460697 : Blo 303832 460697 := bstep (se 2 (by rfl) ⟨172761, by rfl⟩ : syracuseStep 460697 = 345523) B345523
theorem B690137 : Blo 303832 690137 := bstep (se 2 (by rfl) ⟨258801, by rfl⟩ : syracuseStep 690137 = 517603) B517603
theorem B460811 : Blo 303832 460811 := bstep (se 1 (by rfl) ⟨345608, by rfl⟩ : syracuseStep 460811 = 691217) B691217
theorem B952343 : Blo 303832 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B460823 : Blo 303832 460823 := bstep (se 1 (by rfl) ⟨345617, by rfl⟩ : syracuseStep 460823 = 691235) B691235
theorem B657433 : Blo 303832 657433 := bstep (se 2 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 657433 = 493075) B493075
theorem B690227 : Blo 303832 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B690263 : Blo 303832 690263 := bstep (se 1 (by rfl) ⟨517697, by rfl⟩ : syracuseStep 690263 = 1035395) B1035395
theorem B460889 : Blo 303832 460889 := bstep (se 2 (by rfl) ⟨172833, by rfl⟩ : syracuseStep 460889 = 345667) B345667
theorem B1312919 : Blo 303832 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B461003 : Blo 303832 461003 := bstep (se 1 (by rfl) ⟨345752, by rfl⟩ : syracuseStep 461003 = 691505) B691505
theorem B461015 : Blo 303832 461015 := bstep (se 1 (by rfl) ⟨345761, by rfl⟩ : syracuseStep 461015 = 691523) B691523
theorem B690443 : Blo 303832 690443 := bstep (se 1 (by rfl) ⟨517832, by rfl⟩ : syracuseStep 690443 = 1035665) B1035665
theorem B461081 : Blo 303832 461081 := bstep (se 2 (by rfl) ⟨172905, by rfl⟩ : syracuseStep 461081 = 345811) B345811
theorem B690497 : Blo 303832 690497 := bstep (se 2 (by rfl) ⟨258936, by rfl⟩ : syracuseStep 690497 = 517873) B517873
theorem B461195 : Blo 303832 461195 := bstep (se 1 (by rfl) ⟨345896, by rfl⟩ : syracuseStep 461195 = 691793) B691793
theorem B461207 : Blo 303832 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B461273 : Blo 303832 461273 := bstep (se 2 (by rfl) ⟨172977, by rfl⟩ : syracuseStep 461273 = 345955) B345955
theorem B690713 : Blo 303832 690713 := bstep (se 2 (by rfl) ⟨259017, by rfl⟩ : syracuseStep 690713 = 518035) B518035
theorem B461387 : Blo 303832 461387 := bstep (se 1 (by rfl) ⟨346040, by rfl⟩ : syracuseStep 461387 = 692081) B692081
theorem B461399 : Blo 303832 461399 := bstep (se 1 (by rfl) ⟨346049, by rfl⟩ : syracuseStep 461399 = 692099) B692099
theorem B690803 : Blo 303832 690803 := bstep (se 1 (by rfl) ⟨518102, by rfl⟩ : syracuseStep 690803 = 1036205) B1036205
theorem B690839 : Blo 303832 690839 := bstep (se 1 (by rfl) ⟨518129, by rfl⟩ : syracuseStep 690839 = 1036259) B1036259
theorem B461465 : Blo 303832 461465 := bstep (se 2 (by rfl) ⟨173049, by rfl⟩ : syracuseStep 461465 = 346099) B346099
theorem B461579 : Blo 303832 461579 := bstep (se 1 (by rfl) ⟨346184, by rfl⟩ : syracuseStep 461579 = 692369) B692369
theorem B461591 : Blo 303832 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B691019 : Blo 303832 691019 := bstep (se 1 (by rfl) ⟨518264, by rfl⟩ : syracuseStep 691019 = 1036529) B1036529
theorem B985945 : Blo 303832 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B461657 : Blo 303832 461657 := bstep (se 2 (by rfl) ⟨173121, by rfl⟩ : syracuseStep 461657 = 346243) B346243
theorem B691073 : Blo 303832 691073 := bstep (se 2 (by rfl) ⟨259152, by rfl⟩ : syracuseStep 691073 = 518305) B518305
theorem B1182595 : Blo 303832 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B1412099 : Blo 303832 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B691289 : Blo 303832 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B691379 : Blo 303832 691379 := bstep (se 1 (by rfl) ⟨518534, by rfl⟩ : syracuseStep 691379 = 1037069) B1037069
theorem B691415 : Blo 303832 691415 := bstep (se 1 (by rfl) ⟨518561, by rfl⟩ : syracuseStep 691415 = 1037123) B1037123
theorem B691595 : Blo 303832 691595 := bstep (se 1 (by rfl) ⟨518696, by rfl⟩ : syracuseStep 691595 = 1037393) B1037393
theorem B691649 : Blo 303832 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B1314251 : Blo 303832 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1543697 : Blo 303832 1543697 := bstep (se 2 (by rfl) ⟨578886, by rfl⟩ : syracuseStep 1543697 = 1157773) B1157773
theorem B1740305 : Blo 303832 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B3313169 : Blo 303832 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B691865 : Blo 303832 691865 := bstep (se 2 (by rfl) ⟨259449, by rfl⟩ : syracuseStep 691865 = 518899) B518899
theorem B1543859 : Blo 303832 1543859 := bstep (se 1 (by rfl) ⟨1157894, by rfl⟩ : syracuseStep 1543859 = 2315789) B2315789
theorem B691955 : Blo 303832 691955 := bstep (se 1 (by rfl) ⟨518966, by rfl⟩ : syracuseStep 691955 = 1037933) B1037933
theorem B691991 : Blo 303832 691991 := bstep (se 1 (by rfl) ⟨518993, by rfl⟩ : syracuseStep 691991 = 1037987) B1037987
theorem B692171 : Blo 303832 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B1740761 : Blo 303832 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B692225 : Blo 303832 692225 := bstep (se 2 (by rfl) ⟨259584, by rfl⟩ : syracuseStep 692225 = 519169) B519169
theorem B2920465 : Blo 303832 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B692441 : Blo 303832 692441 := bstep (se 2 (by rfl) ⟨259665, by rfl⟩ : syracuseStep 692441 = 519331) B519331
theorem B561431 : Blo 303832 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B692531 : Blo 303832 692531 := bstep (se 1 (by rfl) ⟨519398, by rfl⟩ : syracuseStep 692531 = 1038797) B1038797
theorem B692567 : Blo 303832 692567 := bstep (se 1 (by rfl) ⟨519425, by rfl⟩ : syracuseStep 692567 = 1038851) B1038851
theorem B2101891 : Blo 303832 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B2200243 : Blo 303832 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B2331341 : Blo 303832 2331341 := bstep (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) B874253
theorem B1250051 : Blo 303832 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B2200385 : Blo 303832 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B693107 : Blo 303832 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B2200499 : Blo 303832 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B2331827 : Blo 303832 2331827 := bstep (se 1 (by rfl) ⟨1748870, by rfl⟩ : syracuseStep 2331827 = 3497741) B3497741
theorem B496919 : Blo 303832 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B5051765 : Blo 303832 5051765 := bstep (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) B473603
theorem B2496035 : Blo 303832 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1545803 : Blo 303832 1545803 := bstep (se 1 (by rfl) ⟨1159352, by rfl⟩ : syracuseStep 1545803 = 2318705) B2318705
theorem B1775321 : Blo 303832 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B1054529 : Blo 303832 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B4725317 : Blo 303832 4725317 := bstep (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) B885997
theorem B2333285 : Blo 303832 2333285 := bstep (se 4 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 2333285 = 437491) B437491
theorem B2628227 : Blo 303832 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B432793 : Blo 303832 432793 := bstep (se 2 (by rfl) ⟨162297, by rfl⟩ : syracuseStep 432793 = 324595) B324595
theorem B629441 : Blo 303832 629441 := bstep (se 2 (by rfl) ⟨236040, by rfl⟩ : syracuseStep 629441 = 472081) B472081
theorem B2366243 : Blo 303832 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B826163 : Blo 303832 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B1153885 : Blo 303832 1153885 := bstep (se 3 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 1153885 = 432707) B432707
theorem B1973143 : Blo 303832 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B2333771 : Blo 303832 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B826571 : Blo 303832 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B1547585 : Blo 303832 1547585 := bstep (se 2 (by rfl) ⟨580344, by rfl⟩ : syracuseStep 1547585 = 1160689) B1160689
theorem B433687 : Blo 303832 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B4955741 : Blo 303832 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B434251 : Blo 303832 434251 := bstep (se 1 (by rfl) ⟨325688, by rfl⟩ : syracuseStep 434251 = 651377) B651377
theorem B1155161 : Blo 303832 1155161 := bstep (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) B866371
theorem B1646743 : Blo 303832 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B5546225 : Blo 303832 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B696691 : Blo 303832 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B303851 : Blo 303832 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B303863 : Blo 303832 303863 := bstep (se 1 (by rfl) ⟨227897, by rfl⟩ : syracuseStep 303863 = 455795) B455795
theorem B303883 : Blo 303832 303883 := bstep (se 1 (by rfl) ⟨227912, by rfl⟩ : syracuseStep 303883 = 455825) B455825
theorem B303895 : Blo 303832 303895 := bstep (se 1 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 303895 = 455843) B455843
theorem B303915 : Blo 303832 303915 := bstep (se 1 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 303915 = 455873) B455873
theorem B303927 : Blo 303832 303927 := bstep (se 1 (by rfl) ⟨227945, by rfl⟩ : syracuseStep 303927 = 455891) B455891
theorem B303947 : Blo 303832 303947 := bstep (se 1 (by rfl) ⟨227960, by rfl⟩ : syracuseStep 303947 = 455921) B455921
theorem B303959 : Blo 303832 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B303979 : Blo 303832 303979 := bstep (se 1 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 303979 = 455969) B455969
theorem B303991 : Blo 303832 303991 := bstep (se 1 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 303991 = 455987) B455987
theorem B304011 : Blo 303832 304011 := bstep (se 1 (by rfl) ⟨228008, by rfl⟩ : syracuseStep 304011 = 456017) B456017
theorem B304023 : Blo 303832 304023 := bstep (se 1 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 304023 = 456035) B456035
theorem B304043 : Blo 303832 304043 := bstep (se 1 (by rfl) ⟨228032, by rfl⟩ : syracuseStep 304043 = 456065) B456065
theorem B304055 : Blo 303832 304055 := bstep (se 1 (by rfl) ⟨228041, by rfl⟩ : syracuseStep 304055 = 456083) B456083
theorem B304075 : Blo 303832 304075 := bstep (se 1 (by rfl) ⟨228056, by rfl⟩ : syracuseStep 304075 = 456113) B456113
theorem B304087 : Blo 303832 304087 := bstep (se 1 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 304087 = 456131) B456131
theorem B304107 : Blo 303832 304107 := bstep (se 1 (by rfl) ⟨228080, by rfl⟩ : syracuseStep 304107 = 456161) B456161
theorem B304119 : Blo 303832 304119 := bstep (se 1 (by rfl) ⟨228089, by rfl⟩ : syracuseStep 304119 = 456179) B456179
theorem B304139 : Blo 303832 304139 := bstep (se 1 (by rfl) ⟨228104, by rfl⟩ : syracuseStep 304139 = 456209) B456209
theorem B304151 : Blo 303832 304151 := bstep (se 1 (by rfl) ⟨228113, by rfl⟩ : syracuseStep 304151 = 456227) B456227
theorem B304171 : Blo 303832 304171 := bstep (se 1 (by rfl) ⟨228128, by rfl⟩ : syracuseStep 304171 = 456257) B456257
theorem B304183 : Blo 303832 304183 := bstep (se 1 (by rfl) ⟨228137, by rfl⟩ : syracuseStep 304183 = 456275) B456275
theorem B304203 : Blo 303832 304203 := bstep (se 1 (by rfl) ⟨228152, by rfl⟩ : syracuseStep 304203 = 456305) B456305
theorem B304215 : Blo 303832 304215 := bstep (se 1 (by rfl) ⟨228161, by rfl⟩ : syracuseStep 304215 = 456323) B456323
theorem B304235 : Blo 303832 304235 := bstep (se 1 (by rfl) ⟨228176, by rfl⟩ : syracuseStep 304235 = 456353) B456353
theorem B304247 : Blo 303832 304247 := bstep (se 1 (by rfl) ⟨228185, by rfl⟩ : syracuseStep 304247 = 456371) B456371
theorem B304267 : Blo 303832 304267 := bstep (se 1 (by rfl) ⟨228200, by rfl⟩ : syracuseStep 304267 = 456401) B456401
theorem B304279 : Blo 303832 304279 := bstep (se 1 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 304279 = 456419) B456419
theorem B304299 : Blo 303832 304299 := bstep (se 1 (by rfl) ⟨228224, by rfl⟩ : syracuseStep 304299 = 456449) B456449
theorem B730291 : Blo 303832 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B304311 : Blo 303832 304311 := bstep (se 1 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 304311 = 456467) B456467
theorem B304331 : Blo 303832 304331 := bstep (se 1 (by rfl) ⟨228248, by rfl⟩ : syracuseStep 304331 = 456497) B456497
theorem B304343 : Blo 303832 304343 := bstep (se 1 (by rfl) ⟨228257, by rfl⟩ : syracuseStep 304343 = 456515) B456515
theorem B1549529 : Blo 303832 1549529 := bstep (se 2 (by rfl) ⟨581073, by rfl⟩ : syracuseStep 1549529 = 1162147) B1162147
theorem B1746137 : Blo 303832 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B304363 : Blo 303832 304363 := bstep (se 1 (by rfl) ⟨228272, by rfl⟩ : syracuseStep 304363 = 456545) B456545
theorem B304375 : Blo 303832 304375 := bstep (se 1 (by rfl) ⟨228281, by rfl⟩ : syracuseStep 304375 = 456563) B456563
theorem B304395 : Blo 303832 304395 := bstep (se 1 (by rfl) ⟨228296, by rfl⟩ : syracuseStep 304395 = 456593) B456593
theorem B304407 : Blo 303832 304407 := bstep (se 1 (by rfl) ⟨228305, by rfl⟩ : syracuseStep 304407 = 456611) B456611
theorem B304427 : Blo 303832 304427 := bstep (se 1 (by rfl) ⟨228320, by rfl⟩ : syracuseStep 304427 = 456641) B456641
theorem B304439 : Blo 303832 304439 := bstep (se 1 (by rfl) ⟨228329, by rfl⟩ : syracuseStep 304439 = 456659) B456659
theorem B304459 : Blo 303832 304459 := bstep (se 1 (by rfl) ⟨228344, by rfl⟩ : syracuseStep 304459 = 456689) B456689
theorem B304471 : Blo 303832 304471 := bstep (se 1 (by rfl) ⟨228353, by rfl⟩ : syracuseStep 304471 = 456707) B456707
theorem B304491 : Blo 303832 304491 := bstep (se 1 (by rfl) ⟨228368, by rfl⟩ : syracuseStep 304491 = 456737) B456737
theorem B304503 : Blo 303832 304503 := bstep (se 1 (by rfl) ⟨228377, by rfl⟩ : syracuseStep 304503 = 456755) B456755
theorem B304523 : Blo 303832 304523 := bstep (se 1 (by rfl) ⟨228392, by rfl⟩ : syracuseStep 304523 = 456785) B456785
theorem B304535 : Blo 303832 304535 := bstep (se 1 (by rfl) ⟨228401, by rfl⟩ : syracuseStep 304535 = 456803) B456803
theorem B304555 : Blo 303832 304555 := bstep (se 1 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 304555 = 456833) B456833
theorem B1025459 : Blo 303832 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B304567 : Blo 303832 304567 := bstep (se 1 (by rfl) ⟨228425, by rfl⟩ : syracuseStep 304567 = 456851) B456851
theorem B304587 : Blo 303832 304587 := bstep (se 1 (by rfl) ⟨228440, by rfl⟩ : syracuseStep 304587 = 456881) B456881
theorem B304599 : Blo 303832 304599 := bstep (se 1 (by rfl) ⟨228449, by rfl⟩ : syracuseStep 304599 = 456899) B456899
theorem B304619 : Blo 303832 304619 := bstep (se 1 (by rfl) ⟨228464, by rfl⟩ : syracuseStep 304619 = 456929) B456929
theorem B304631 : Blo 303832 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B304651 : Blo 303832 304651 := bstep (se 1 (by rfl) ⟨228488, by rfl⟩ : syracuseStep 304651 = 456977) B456977
theorem B3712529 : Blo 303832 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B304663 : Blo 303832 304663 := bstep (se 1 (by rfl) ⟨228497, by rfl⟩ : syracuseStep 304663 = 456995) B456995
theorem B435737 : Blo 303832 435737 := bstep (se 2 (by rfl) ⟨163401, by rfl⟩ : syracuseStep 435737 = 326803) B326803
theorem B304683 : Blo 303832 304683 := bstep (se 1 (by rfl) ⟨228512, by rfl⟩ : syracuseStep 304683 = 457025) B457025
theorem B304695 : Blo 303832 304695 := bstep (se 1 (by rfl) ⟨228521, by rfl⟩ : syracuseStep 304695 = 457043) B457043
theorem B304715 : Blo 303832 304715 := bstep (se 1 (by rfl) ⟨228536, by rfl⟩ : syracuseStep 304715 = 457073) B457073
theorem B304727 : Blo 303832 304727 := bstep (se 1 (by rfl) ⟨228545, by rfl⟩ : syracuseStep 304727 = 457091) B457091
theorem B304747 : Blo 303832 304747 := bstep (se 1 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 304747 = 457121) B457121
theorem B304759 : Blo 303832 304759 := bstep (se 1 (by rfl) ⟨228569, by rfl⟩ : syracuseStep 304759 = 457139) B457139
theorem B304779 : Blo 303832 304779 := bstep (se 1 (by rfl) ⟨228584, by rfl⟩ : syracuseStep 304779 = 457169) B457169
theorem B304791 : Blo 303832 304791 := bstep (se 1 (by rfl) ⟨228593, by rfl⟩ : syracuseStep 304791 = 457187) B457187
theorem B304811 : Blo 303832 304811 := bstep (se 1 (by rfl) ⟨228608, by rfl⟩ : syracuseStep 304811 = 457217) B457217
theorem B1156787 : Blo 303832 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B304823 : Blo 303832 304823 := bstep (se 1 (by rfl) ⟨228617, by rfl⟩ : syracuseStep 304823 = 457235) B457235
theorem B1025729 : Blo 303832 1025729 := bstep (se 2 (by rfl) ⟨384648, by rfl⟩ : syracuseStep 1025729 = 769297) B769297
theorem B1156801 : Blo 303832 1156801 := bstep (se 2 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 1156801 = 867601) B867601
theorem B304843 : Blo 303832 304843 := bstep (se 1 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 304843 = 457265) B457265
theorem B304855 : Blo 303832 304855 := bstep (se 1 (by rfl) ⟨228641, by rfl⟩ : syracuseStep 304855 = 457283) B457283
theorem B304875 : Blo 303832 304875 := bstep (se 1 (by rfl) ⟨228656, by rfl⟩ : syracuseStep 304875 = 457313) B457313
theorem B304887 : Blo 303832 304887 := bstep (se 1 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 304887 = 457331) B457331
theorem B304907 : Blo 303832 304907 := bstep (se 1 (by rfl) ⟨228680, by rfl⟩ : syracuseStep 304907 = 457361) B457361
theorem B304919 : Blo 303832 304919 := bstep (se 1 (by rfl) ⟨228689, by rfl⟩ : syracuseStep 304919 = 457379) B457379
theorem B304939 : Blo 303832 304939 := bstep (se 1 (by rfl) ⟨228704, by rfl⟩ : syracuseStep 304939 = 457409) B457409
theorem B304951 : Blo 303832 304951 := bstep (se 1 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 304951 = 457427) B457427
theorem B304971 : Blo 303832 304971 := bstep (se 1 (by rfl) ⟨228728, by rfl⟩ : syracuseStep 304971 = 457457) B457457
theorem B304983 : Blo 303832 304983 := bstep (se 1 (by rfl) ⟨228737, by rfl⟩ : syracuseStep 304983 = 457475) B457475
theorem B2828125 : Blo 303832 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B305003 : Blo 303832 305003 := bstep (se 1 (by rfl) ⟨228752, by rfl⟩ : syracuseStep 305003 = 457505) B457505
theorem B305015 : Blo 303832 305015 := bstep (se 1 (by rfl) ⟨228761, by rfl⟩ : syracuseStep 305015 = 457523) B457523
theorem B305035 : Blo 303832 305035 := bstep (se 1 (by rfl) ⟨228776, by rfl⟩ : syracuseStep 305035 = 457553) B457553
theorem B305047 : Blo 303832 305047 := bstep (se 1 (by rfl) ⟨228785, by rfl⟩ : syracuseStep 305047 = 457571) B457571
theorem B305067 : Blo 303832 305067 := bstep (se 1 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 305067 = 457601) B457601
theorem B305079 : Blo 303832 305079 := bstep (se 1 (by rfl) ⟨228809, by rfl⟩ : syracuseStep 305079 = 457619) B457619
theorem B305099 : Blo 303832 305099 := bstep (se 1 (by rfl) ⟨228824, by rfl⟩ : syracuseStep 305099 = 457649) B457649
theorem B305111 : Blo 303832 305111 := bstep (se 1 (by rfl) ⟨228833, by rfl⟩ : syracuseStep 305111 = 457667) B457667
theorem B305131 : Blo 303832 305131 := bstep (se 1 (by rfl) ⟨228848, by rfl⟩ : syracuseStep 305131 = 457697) B457697
theorem B305143 : Blo 303832 305143 := bstep (se 1 (by rfl) ⟨228857, by rfl⟩ : syracuseStep 305143 = 457715) B457715
theorem B305163 : Blo 303832 305163 := bstep (se 1 (by rfl) ⟨228872, by rfl⟩ : syracuseStep 305163 = 457745) B457745
theorem B305175 : Blo 303832 305175 := bstep (se 1 (by rfl) ⟨228881, by rfl⟩ : syracuseStep 305175 = 457763) B457763
theorem B305195 : Blo 303832 305195 := bstep (se 1 (by rfl) ⟨228896, by rfl⟩ : syracuseStep 305195 = 457793) B457793
theorem B305207 : Blo 303832 305207 := bstep (se 1 (by rfl) ⟨228905, by rfl⟩ : syracuseStep 305207 = 457811) B457811
theorem B305227 : Blo 303832 305227 := bstep (se 1 (by rfl) ⟨228920, by rfl⟩ : syracuseStep 305227 = 457841) B457841
theorem B305239 : Blo 303832 305239 := bstep (se 1 (by rfl) ⟨228929, by rfl⟩ : syracuseStep 305239 = 457859) B457859
theorem B305259 : Blo 303832 305259 := bstep (se 1 (by rfl) ⟨228944, by rfl⟩ : syracuseStep 305259 = 457889) B457889
theorem B305271 : Blo 303832 305271 := bstep (se 1 (by rfl) ⟨228953, by rfl⟩ : syracuseStep 305271 = 457907) B457907
theorem B305291 : Blo 303832 305291 := bstep (se 1 (by rfl) ⟨228968, by rfl⟩ : syracuseStep 305291 = 457937) B457937
theorem B305303 : Blo 303832 305303 := bstep (se 1 (by rfl) ⟨228977, by rfl⟩ : syracuseStep 305303 = 457955) B457955
theorem B9939095 : Blo 303832 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B436375 : Blo 303832 436375 := bstep (se 1 (by rfl) ⟨327281, by rfl⟩ : syracuseStep 436375 = 654563) B654563
theorem B305323 : Blo 303832 305323 := bstep (se 1 (by rfl) ⟨228992, by rfl⟩ : syracuseStep 305323 = 457985) B457985
theorem B305335 : Blo 303832 305335 := bstep (se 1 (by rfl) ⟨229001, by rfl⟩ : syracuseStep 305335 = 458003) B458003
theorem B731339 : Blo 303832 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B305355 : Blo 303832 305355 := bstep (se 1 (by rfl) ⟨229016, by rfl⟩ : syracuseStep 305355 = 458033) B458033
theorem B305367 : Blo 303832 305367 := bstep (se 1 (by rfl) ⟨229025, by rfl⟩ : syracuseStep 305367 = 458051) B458051
theorem B1026269 : Blo 303832 1026269 := bstep (se 3 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 1026269 = 384851) B384851
theorem B305387 : Blo 303832 305387 := bstep (se 1 (by rfl) ⟨229040, by rfl⟩ : syracuseStep 305387 = 458081) B458081
theorem B305399 : Blo 303832 305399 := bstep (se 1 (by rfl) ⟨229049, by rfl⟩ : syracuseStep 305399 = 458099) B458099
theorem B305419 : Blo 303832 305419 := bstep (se 1 (by rfl) ⟨229064, by rfl⟩ : syracuseStep 305419 = 458129) B458129
theorem B305431 : Blo 303832 305431 := bstep (se 1 (by rfl) ⟨229073, by rfl⟩ : syracuseStep 305431 = 458147) B458147
theorem B305451 : Blo 303832 305451 := bstep (se 1 (by rfl) ⟨229088, by rfl⟩ : syracuseStep 305451 = 458177) B458177
theorem B305463 : Blo 303832 305463 := bstep (se 1 (by rfl) ⟨229097, by rfl⟩ : syracuseStep 305463 = 458195) B458195
theorem B305483 : Blo 303832 305483 := bstep (se 1 (by rfl) ⟨229112, by rfl⟩ : syracuseStep 305483 = 458225) B458225
theorem B305495 : Blo 303832 305495 := bstep (se 1 (by rfl) ⟨229121, by rfl⟩ : syracuseStep 305495 = 458243) B458243
theorem B305515 : Blo 303832 305515 := bstep (se 1 (by rfl) ⟨229136, by rfl⟩ : syracuseStep 305515 = 458273) B458273
theorem B305527 : Blo 303832 305527 := bstep (se 1 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 305527 = 458291) B458291
theorem B305547 : Blo 303832 305547 := bstep (se 1 (by rfl) ⟨229160, by rfl⟩ : syracuseStep 305547 = 458321) B458321
theorem B305559 : Blo 303832 305559 := bstep (se 1 (by rfl) ⟨229169, by rfl⟩ : syracuseStep 305559 = 458339) B458339
theorem B305579 : Blo 303832 305579 := bstep (se 1 (by rfl) ⟨229184, by rfl⟩ : syracuseStep 305579 = 458369) B458369
theorem B305591 : Blo 303832 305591 := bstep (se 1 (by rfl) ⟨229193, by rfl⟩ : syracuseStep 305591 = 458387) B458387
theorem B305611 : Blo 303832 305611 := bstep (se 1 (by rfl) ⟨229208, by rfl⟩ : syracuseStep 305611 = 458417) B458417
theorem B698827 : Blo 303832 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B305623 : Blo 303832 305623 := bstep (se 1 (by rfl) ⟨229217, by rfl⟩ : syracuseStep 305623 = 458435) B458435
theorem B305643 : Blo 303832 305643 := bstep (se 1 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 305643 = 458465) B458465
theorem B305655 : Blo 303832 305655 := bstep (se 1 (by rfl) ⟨229241, by rfl⟩ : syracuseStep 305655 = 458483) B458483
theorem B305675 : Blo 303832 305675 := bstep (se 1 (by rfl) ⟨229256, by rfl⟩ : syracuseStep 305675 = 458513) B458513
theorem B305687 : Blo 303832 305687 := bstep (se 1 (by rfl) ⟨229265, by rfl⟩ : syracuseStep 305687 = 458531) B458531
theorem B305707 : Blo 303832 305707 := bstep (se 1 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 305707 = 458561) B458561
theorem B305719 : Blo 303832 305719 := bstep (se 1 (by rfl) ⟨229289, by rfl⟩ : syracuseStep 305719 = 458579) B458579
theorem B305739 : Blo 303832 305739 := bstep (se 1 (by rfl) ⟨229304, by rfl⟩ : syracuseStep 305739 = 458609) B458609
theorem B305751 : Blo 303832 305751 := bstep (se 1 (by rfl) ⟨229313, by rfl⟩ : syracuseStep 305751 = 458627) B458627
theorem B305771 : Blo 303832 305771 := bstep (se 1 (by rfl) ⟨229328, by rfl⟩ : syracuseStep 305771 = 458657) B458657
theorem B305783 : Blo 303832 305783 := bstep (se 1 (by rfl) ⟨229337, by rfl⟩ : syracuseStep 305783 = 458675) B458675
theorem B305803 : Blo 303832 305803 := bstep (se 1 (by rfl) ⟨229352, by rfl⟩ : syracuseStep 305803 = 458705) B458705
theorem B305815 : Blo 303832 305815 := bstep (se 1 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 305815 = 458723) B458723
theorem B305835 : Blo 303832 305835 := bstep (se 1 (by rfl) ⟨229376, by rfl⟩ : syracuseStep 305835 = 458753) B458753
theorem B305847 : Blo 303832 305847 := bstep (se 1 (by rfl) ⟨229385, by rfl⟩ : syracuseStep 305847 = 458771) B458771
theorem B928459 : Blo 303832 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B305867 : Blo 303832 305867 := bstep (se 1 (by rfl) ⟨229400, by rfl⟩ : syracuseStep 305867 = 458801) B458801
theorem B305879 : Blo 303832 305879 := bstep (se 1 (by rfl) ⟨229409, by rfl⟩ : syracuseStep 305879 = 458819) B458819
theorem B305899 : Blo 303832 305899 := bstep (se 1 (by rfl) ⟨229424, by rfl⟩ : syracuseStep 305899 = 458849) B458849
theorem B305911 : Blo 303832 305911 := bstep (se 1 (by rfl) ⟨229433, by rfl⟩ : syracuseStep 305911 = 458867) B458867
theorem B305931 : Blo 303832 305931 := bstep (se 1 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 305931 = 458897) B458897
theorem B305943 : Blo 303832 305943 := bstep (se 1 (by rfl) ⟨229457, by rfl⟩ : syracuseStep 305943 = 458915) B458915
theorem B305963 : Blo 303832 305963 := bstep (se 1 (by rfl) ⟨229472, by rfl⟩ : syracuseStep 305963 = 458945) B458945
theorem B1551149 : Blo 303832 1551149 := bstep (se 3 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 1551149 = 581681) B581681
theorem B305975 : Blo 303832 305975 := bstep (se 1 (by rfl) ⟨229481, by rfl⟩ : syracuseStep 305975 = 458963) B458963
theorem B1747777 : Blo 303832 1747777 := bstep (se 2 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 1747777 = 1310833) B1310833
theorem B305995 : Blo 303832 305995 := bstep (se 1 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 305995 = 458993) B458993
theorem B306007 : Blo 303832 306007 := bstep (se 1 (by rfl) ⟨229505, by rfl⟩ : syracuseStep 306007 = 459011) B459011
theorem B437081 : Blo 303832 437081 := bstep (se 2 (by rfl) ⟨163905, by rfl⟩ : syracuseStep 437081 = 327811) B327811
theorem B306027 : Blo 303832 306027 := bstep (se 1 (by rfl) ⟨229520, by rfl⟩ : syracuseStep 306027 = 459041) B459041
theorem B306039 : Blo 303832 306039 := bstep (se 1 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 306039 = 459059) B459059
theorem B306059 : Blo 303832 306059 := bstep (se 1 (by rfl) ⟨229544, by rfl⟩ : syracuseStep 306059 = 459089) B459089
theorem B306071 : Blo 303832 306071 := bstep (se 1 (by rfl) ⟨229553, by rfl⟩ : syracuseStep 306071 = 459107) B459107
theorem B306091 : Blo 303832 306091 := bstep (se 1 (by rfl) ⟨229568, by rfl⟩ : syracuseStep 306091 = 459137) B459137
theorem B306103 : Blo 303832 306103 := bstep (se 1 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 306103 = 459155) B459155
theorem B306123 : Blo 303832 306123 := bstep (se 1 (by rfl) ⟨229592, by rfl⟩ : syracuseStep 306123 = 459185) B459185
theorem B437195 : Blo 303832 437195 := bstep (se 1 (by rfl) ⟨327896, by rfl⟩ : syracuseStep 437195 = 655793) B655793
theorem B306135 : Blo 303832 306135 := bstep (se 1 (by rfl) ⟨229601, by rfl⟩ : syracuseStep 306135 = 459203) B459203
theorem B306155 : Blo 303832 306155 := bstep (se 1 (by rfl) ⟨229616, by rfl⟩ : syracuseStep 306155 = 459233) B459233
theorem B306167 : Blo 303832 306167 := bstep (se 1 (by rfl) ⟨229625, by rfl⟩ : syracuseStep 306167 = 459251) B459251
theorem B306187 : Blo 303832 306187 := bstep (se 1 (by rfl) ⟨229640, by rfl⟩ : syracuseStep 306187 = 459281) B459281
theorem B306199 : Blo 303832 306199 := bstep (se 1 (by rfl) ⟨229649, by rfl⟩ : syracuseStep 306199 = 459299) B459299
theorem B306219 : Blo 303832 306219 := bstep (se 1 (by rfl) ⟨229664, by rfl⟩ : syracuseStep 306219 = 459329) B459329
theorem B306231 : Blo 303832 306231 := bstep (se 1 (by rfl) ⟨229673, by rfl⟩ : syracuseStep 306231 = 459347) B459347
theorem B306251 : Blo 303832 306251 := bstep (se 1 (by rfl) ⟨229688, by rfl⟩ : syracuseStep 306251 = 459377) B459377
theorem B306263 : Blo 303832 306263 := bstep (se 1 (by rfl) ⟨229697, by rfl⟩ : syracuseStep 306263 = 459395) B459395
theorem B306283 : Blo 303832 306283 := bstep (se 1 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 306283 = 459425) B459425
theorem B306295 : Blo 303832 306295 := bstep (se 1 (by rfl) ⟨229721, by rfl⟩ : syracuseStep 306295 = 459443) B459443
theorem B306315 : Blo 303832 306315 := bstep (se 1 (by rfl) ⟨229736, by rfl⟩ : syracuseStep 306315 = 459473) B459473
theorem B306327 : Blo 303832 306327 := bstep (se 1 (by rfl) ⟨229745, by rfl⟩ : syracuseStep 306327 = 459491) B459491
theorem B306347 : Blo 303832 306347 := bstep (se 1 (by rfl) ⟨229760, by rfl⟩ : syracuseStep 306347 = 459521) B459521
theorem B306359 : Blo 303832 306359 := bstep (se 1 (by rfl) ⟨229769, by rfl⟩ : syracuseStep 306359 = 459539) B459539
theorem B306379 : Blo 303832 306379 := bstep (se 1 (by rfl) ⟨229784, by rfl⟩ : syracuseStep 306379 = 459569) B459569
theorem B306391 : Blo 303832 306391 := bstep (se 1 (by rfl) ⟨229793, by rfl⟩ : syracuseStep 306391 = 459587) B459587
theorem B306411 : Blo 303832 306411 := bstep (se 1 (by rfl) ⟨229808, by rfl⟩ : syracuseStep 306411 = 459617) B459617
theorem B306423 : Blo 303832 306423 := bstep (se 1 (by rfl) ⟨229817, by rfl⟩ : syracuseStep 306423 = 459635) B459635
theorem B306443 : Blo 303832 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B306455 : Blo 303832 306455 := bstep (se 1 (by rfl) ⟨229841, by rfl⟩ : syracuseStep 306455 = 459683) B459683
theorem B306475 : Blo 303832 306475 := bstep (se 1 (by rfl) ⟨229856, by rfl⟩ : syracuseStep 306475 = 459713) B459713
theorem B306487 : Blo 303832 306487 := bstep (se 1 (by rfl) ⟨229865, by rfl⟩ : syracuseStep 306487 = 459731) B459731
theorem B1027403 : Blo 303832 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B306507 : Blo 303832 306507 := bstep (se 1 (by rfl) ⟨229880, by rfl⟩ : syracuseStep 306507 = 459761) B459761
theorem B306519 : Blo 303832 306519 := bstep (se 1 (by rfl) ⟨229889, by rfl⟩ : syracuseStep 306519 = 459779) B459779
theorem B306539 : Blo 303832 306539 := bstep (se 1 (by rfl) ⟨229904, by rfl⟩ : syracuseStep 306539 = 459809) B459809
theorem B306551 : Blo 303832 306551 := bstep (se 1 (by rfl) ⟨229913, by rfl⟩ : syracuseStep 306551 = 459827) B459827
theorem B306571 : Blo 303832 306571 := bstep (se 1 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 306571 = 459857) B459857
theorem B306583 : Blo 303832 306583 := bstep (se 1 (by rfl) ⟨229937, by rfl⟩ : syracuseStep 306583 = 459875) B459875
theorem B306603 : Blo 303832 306603 := bstep (se 1 (by rfl) ⟨229952, by rfl⟩ : syracuseStep 306603 = 459905) B459905
theorem B306615 : Blo 303832 306615 := bstep (se 1 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 306615 = 459923) B459923
theorem B306635 : Blo 303832 306635 := bstep (se 1 (by rfl) ⟨229976, by rfl⟩ : syracuseStep 306635 = 459953) B459953
theorem B306647 : Blo 303832 306647 := bstep (se 1 (by rfl) ⟨229985, by rfl⟩ : syracuseStep 306647 = 459971) B459971
theorem B437719 : Blo 303832 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B306667 : Blo 303832 306667 := bstep (se 1 (by rfl) ⟨230000, by rfl⟩ : syracuseStep 306667 = 460001) B460001
theorem B306679 : Blo 303832 306679 := bstep (se 1 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 306679 = 460019) B460019
theorem B306699 : Blo 303832 306699 := bstep (se 1 (by rfl) ⟨230024, by rfl⟩ : syracuseStep 306699 = 460049) B460049
theorem B306711 : Blo 303832 306711 := bstep (se 1 (by rfl) ⟨230033, by rfl⟩ : syracuseStep 306711 = 460067) B460067
theorem B306731 : Blo 303832 306731 := bstep (se 1 (by rfl) ⟨230048, by rfl⟩ : syracuseStep 306731 = 460097) B460097
theorem B306743 : Blo 303832 306743 := bstep (se 1 (by rfl) ⟨230057, by rfl⟩ : syracuseStep 306743 = 460115) B460115
theorem B1158731 : Blo 303832 1158731 := bstep (se 1 (by rfl) ⟨869048, by rfl⟩ : syracuseStep 1158731 = 1738097) B1738097
theorem B306763 : Blo 303832 306763 := bstep (se 1 (by rfl) ⟨230072, by rfl⟩ : syracuseStep 306763 = 460145) B460145
theorem B306775 : Blo 303832 306775 := bstep (se 1 (by rfl) ⟨230081, by rfl⟩ : syracuseStep 306775 = 460163) B460163
theorem B1027673 : Blo 303832 1027673 := bstep (se 2 (by rfl) ⟨385377, by rfl⟩ : syracuseStep 1027673 = 770755) B770755
theorem B1158745 : Blo 303832 1158745 := bstep (se 2 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 1158745 = 869059) B869059
theorem B306795 : Blo 303832 306795 := bstep (se 1 (by rfl) ⟨230096, by rfl⟩ : syracuseStep 306795 = 460193) B460193
theorem B306807 : Blo 303832 306807 := bstep (se 1 (by rfl) ⟨230105, by rfl⟩ : syracuseStep 306807 = 460211) B460211
theorem B306827 : Blo 303832 306827 := bstep (se 1 (by rfl) ⟨230120, by rfl⟩ : syracuseStep 306827 = 460241) B460241
theorem B306839 : Blo 303832 306839 := bstep (se 1 (by rfl) ⟨230129, by rfl⟩ : syracuseStep 306839 = 460259) B460259
theorem B306859 : Blo 303832 306859 := bstep (se 1 (by rfl) ⟨230144, by rfl⟩ : syracuseStep 306859 = 460289) B460289
theorem B306871 : Blo 303832 306871 := bstep (se 1 (by rfl) ⟨230153, by rfl⟩ : syracuseStep 306871 = 460307) B460307
theorem B306891 : Blo 303832 306891 := bstep (se 1 (by rfl) ⟨230168, by rfl⟩ : syracuseStep 306891 = 460337) B460337
theorem B306903 : Blo 303832 306903 := bstep (se 1 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 306903 = 460355) B460355
theorem B306923 : Blo 303832 306923 := bstep (se 1 (by rfl) ⟨230192, by rfl⟩ : syracuseStep 306923 = 460385) B460385
theorem B306935 : Blo 303832 306935 := bstep (se 1 (by rfl) ⟨230201, by rfl⟩ : syracuseStep 306935 = 460403) B460403
theorem B306955 : Blo 303832 306955 := bstep (se 1 (by rfl) ⟨230216, by rfl⟩ : syracuseStep 306955 = 460433) B460433
theorem B306967 : Blo 303832 306967 := bstep (se 1 (by rfl) ⟨230225, by rfl⟩ : syracuseStep 306967 = 460451) B460451
theorem B306987 : Blo 303832 306987 := bstep (se 1 (by rfl) ⟨230240, by rfl⟩ : syracuseStep 306987 = 460481) B460481
theorem B306999 : Blo 303832 306999 := bstep (se 1 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 306999 = 460499) B460499
theorem B307019 : Blo 303832 307019 := bstep (se 1 (by rfl) ⟨230264, by rfl⟩ : syracuseStep 307019 = 460529) B460529
theorem B307031 : Blo 303832 307031 := bstep (se 1 (by rfl) ⟨230273, by rfl⟩ : syracuseStep 307031 = 460547) B460547
theorem B307051 : Blo 303832 307051 := bstep (se 1 (by rfl) ⟨230288, by rfl⟩ : syracuseStep 307051 = 460577) B460577
theorem B4435829 : Blo 303832 4435829 := bstep (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) B415859
theorem B307063 : Blo 303832 307063 := bstep (se 1 (by rfl) ⟨230297, by rfl⟩ : syracuseStep 307063 = 460595) B460595
theorem B307083 : Blo 303832 307083 := bstep (se 1 (by rfl) ⟨230312, by rfl⟩ : syracuseStep 307083 = 460625) B460625
theorem B307095 : Blo 303832 307095 := bstep (se 1 (by rfl) ⟨230321, by rfl⟩ : syracuseStep 307095 = 460643) B460643
theorem B307115 : Blo 303832 307115 := bstep (se 1 (by rfl) ⟨230336, by rfl⟩ : syracuseStep 307115 = 460673) B460673
theorem B307127 : Blo 303832 307127 := bstep (se 1 (by rfl) ⟨230345, by rfl⟩ : syracuseStep 307127 = 460691) B460691
theorem B307147 : Blo 303832 307147 := bstep (se 1 (by rfl) ⟨230360, by rfl⟩ : syracuseStep 307147 = 460721) B460721
theorem B307159 : Blo 303832 307159 := bstep (se 1 (by rfl) ⟨230369, by rfl⟩ : syracuseStep 307159 = 460739) B460739
theorem B307179 : Blo 303832 307179 := bstep (se 1 (by rfl) ⟨230384, by rfl⟩ : syracuseStep 307179 = 460769) B460769
theorem B307191 : Blo 303832 307191 := bstep (se 1 (by rfl) ⟨230393, by rfl⟩ : syracuseStep 307191 = 460787) B460787
theorem B307211 : Blo 303832 307211 := bstep (se 1 (by rfl) ⟨230408, by rfl⟩ : syracuseStep 307211 = 460817) B460817
theorem B307223 : Blo 303832 307223 := bstep (se 1 (by rfl) ⟨230417, by rfl⟩ : syracuseStep 307223 = 460835) B460835
theorem B307243 : Blo 303832 307243 := bstep (se 1 (by rfl) ⟨230432, by rfl⟩ : syracuseStep 307243 = 460865) B460865
theorem B307255 : Blo 303832 307255 := bstep (se 1 (by rfl) ⟨230441, by rfl⟩ : syracuseStep 307255 = 460883) B460883
theorem B307275 : Blo 303832 307275 := bstep (se 1 (by rfl) ⟨230456, by rfl⟩ : syracuseStep 307275 = 460913) B460913
theorem B307287 : Blo 303832 307287 := bstep (se 1 (by rfl) ⟨230465, by rfl⟩ : syracuseStep 307287 = 460931) B460931
theorem B307307 : Blo 303832 307307 := bstep (se 1 (by rfl) ⟨230480, by rfl⟩ : syracuseStep 307307 = 460961) B460961
theorem B307319 : Blo 303832 307319 := bstep (se 1 (by rfl) ⟨230489, by rfl⟩ : syracuseStep 307319 = 460979) B460979
theorem B307339 : Blo 303832 307339 := bstep (se 1 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 307339 = 461009) B461009
theorem B307351 : Blo 303832 307351 := bstep (se 1 (by rfl) ⟨230513, by rfl⟩ : syracuseStep 307351 = 461027) B461027
theorem B307371 : Blo 303832 307371 := bstep (se 1 (by rfl) ⟨230528, by rfl⟩ : syracuseStep 307371 = 461057) B461057
theorem B307383 : Blo 303832 307383 := bstep (se 1 (by rfl) ⟨230537, by rfl⟩ : syracuseStep 307383 = 461075) B461075
theorem B307403 : Blo 303832 307403 := bstep (se 1 (by rfl) ⟨230552, by rfl⟩ : syracuseStep 307403 = 461105) B461105
theorem B307415 : Blo 303832 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B307435 : Blo 303832 307435 := bstep (se 1 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 307435 = 461153) B461153
theorem B307447 : Blo 303832 307447 := bstep (se 1 (by rfl) ⟨230585, by rfl⟩ : syracuseStep 307447 = 461171) B461171
theorem B307467 : Blo 303832 307467 := bstep (se 1 (by rfl) ⟨230600, by rfl⟩ : syracuseStep 307467 = 461201) B461201
theorem B2601233 : Blo 303832 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B1028375 : Blo 303832 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B307479 : Blo 303832 307479 := bstep (se 1 (by rfl) ⟨230609, by rfl⟩ : syracuseStep 307479 = 461219) B461219
theorem B307499 : Blo 303832 307499 := bstep (se 1 (by rfl) ⟨230624, by rfl⟩ : syracuseStep 307499 = 461249) B461249
theorem B307511 : Blo 303832 307511 := bstep (se 1 (by rfl) ⟨230633, by rfl⟩ : syracuseStep 307511 = 461267) B461267
theorem B307531 : Blo 303832 307531 := bstep (se 1 (by rfl) ⟨230648, by rfl⟩ : syracuseStep 307531 = 461297) B461297
theorem B307543 : Blo 303832 307543 := bstep (se 1 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 307543 = 461315) B461315
theorem B307563 : Blo 303832 307563 := bstep (se 1 (by rfl) ⟨230672, by rfl⟩ : syracuseStep 307563 = 461345) B461345
theorem B307575 : Blo 303832 307575 := bstep (se 1 (by rfl) ⟨230681, by rfl⟩ : syracuseStep 307575 = 461363) B461363
theorem B307595 : Blo 303832 307595 := bstep (se 1 (by rfl) ⟨230696, by rfl⟩ : syracuseStep 307595 = 461393) B461393
theorem B307607 : Blo 303832 307607 := bstep (se 1 (by rfl) ⟨230705, by rfl⟩ : syracuseStep 307607 = 461411) B461411
theorem B307627 : Blo 303832 307627 := bstep (se 1 (by rfl) ⟨230720, by rfl⟩ : syracuseStep 307627 = 461441) B461441
theorem B307639 : Blo 303832 307639 := bstep (se 1 (by rfl) ⟨230729, by rfl⟩ : syracuseStep 307639 = 461459) B461459
theorem B307659 : Blo 303832 307659 := bstep (se 1 (by rfl) ⟨230744, by rfl⟩ : syracuseStep 307659 = 461489) B461489
theorem B307671 : Blo 303832 307671 := bstep (se 1 (by rfl) ⟨230753, by rfl⟩ : syracuseStep 307671 = 461507) B461507
theorem B307691 : Blo 303832 307691 := bstep (se 1 (by rfl) ⟨230768, by rfl⟩ : syracuseStep 307691 = 461537) B461537
theorem B307703 : Blo 303832 307703 := bstep (se 1 (by rfl) ⟨230777, by rfl⟩ : syracuseStep 307703 = 461555) B461555
theorem B307723 : Blo 303832 307723 := bstep (se 1 (by rfl) ⟨230792, by rfl⟩ : syracuseStep 307723 = 461585) B461585
theorem B1159703 : Blo 303832 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B307735 : Blo 303832 307735 := bstep (se 1 (by rfl) ⟨230801, by rfl⟩ : syracuseStep 307735 = 461603) B461603
theorem B307755 : Blo 303832 307755 := bstep (se 1 (by rfl) ⟨230816, by rfl⟩ : syracuseStep 307755 = 461633) B461633
theorem B307767 : Blo 303832 307767 := bstep (se 1 (by rfl) ⟨230825, by rfl⟩ : syracuseStep 307767 = 461651) B461651
theorem B307787 : Blo 303832 307787 := bstep (se 1 (by rfl) ⟨230840, by rfl⟩ : syracuseStep 307787 = 461681) B461681
theorem B307799 : Blo 303832 307799 := bstep (se 1 (by rfl) ⟨230849, by rfl⟩ : syracuseStep 307799 = 461699) B461699
theorem B1389149 : Blo 303832 1389149 := bstep (se 3 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 1389149 = 520931) B520931
theorem B307819 : Blo 303832 307819 := bstep (se 1 (by rfl) ⟨230864, by rfl⟩ : syracuseStep 307819 = 461729) B461729
theorem B307831 : Blo 303832 307831 := bstep (se 1 (by rfl) ⟨230873, by rfl⟩ : syracuseStep 307831 = 461747) B461747
theorem B1028915 : Blo 303832 1028915 := bstep (se 1 (by rfl) ⟨771686, by rfl⟩ : syracuseStep 1028915 = 1543373) B1543373
theorem B8827825 : Blo 303832 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B1029185 : Blo 303832 1029185 := bstep (se 2 (by rfl) ⟨385944, by rfl⟩ : syracuseStep 1029185 = 771889) B771889
theorem B701747 : Blo 303832 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B1029725 : Blo 303832 1029725 := bstep (se 3 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 1029725 = 386147) B386147
theorem B734923 : Blo 303832 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B997085 : Blo 303832 997085 := bstep (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) B373907
theorem B1160963 : Blo 303832 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1455889 : Blo 303832 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B734999 : Blo 303832 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B341815 : Blo 303832 341815 := bstep (se 1 (by rfl) ⟨256361, by rfl⟩ : syracuseStep 341815 = 512723) B512723
theorem B341995 : Blo 303832 341995 := bstep (se 1 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 341995 = 512993) B512993
theorem B342103 : Blo 303832 342103 := bstep (se 1 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 342103 = 513155) B513155
theorem B1751219 : Blo 303832 1751219 := bstep (se 1 (by rfl) ⟨1313414, by rfl⟩ : syracuseStep 1751219 = 2626829) B2626829
theorem B866497 : Blo 303832 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B4962545 : Blo 303832 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B342283 : Blo 303832 342283 := bstep (se 1 (by rfl) ⟨256712, by rfl⟩ : syracuseStep 342283 = 513425) B513425
theorem B309559 : Blo 303832 309559 := bstep (se 1 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 309559 = 464339) B464339
theorem B342391 : Blo 303832 342391 := bstep (se 1 (by rfl) ⟨256793, by rfl⟩ : syracuseStep 342391 = 513587) B513587
theorem B342571 : Blo 303832 342571 := bstep (se 1 (by rfl) ⟨256928, by rfl⟩ : syracuseStep 342571 = 513857) B513857
theorem B1555037 : Blo 303832 1555037 := bstep (se 3 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 1555037 = 583139) B583139
theorem B703091 : Blo 303832 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B342679 : Blo 303832 342679 := bstep (se 1 (by rfl) ⟨257009, by rfl⟩ : syracuseStep 342679 = 514019) B514019
theorem B1030859 : Blo 303832 1030859 := bstep (se 1 (by rfl) ⟨773144, by rfl⟩ : syracuseStep 1030859 = 1546289) B1546289
theorem B375563 : Blo 303832 375563 := bstep (se 1 (by rfl) ⟨281672, by rfl⟩ : syracuseStep 375563 = 563345) B563345
theorem B342859 : Blo 303832 342859 := bstep (se 1 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 342859 = 514289) B514289
theorem B310123 : Blo 303832 310123 := bstep (se 1 (by rfl) ⟨232592, by rfl⟩ : syracuseStep 310123 = 465185) B465185
theorem B342967 : Blo 303832 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B1031129 : Blo 303832 1031129 := bstep (se 2 (by rfl) ⟨386673, by rfl⟩ : syracuseStep 1031129 = 773347) B773347
theorem B343147 : Blo 303832 343147 := bstep (se 1 (by rfl) ⟨257360, by rfl⟩ : syracuseStep 343147 = 514721) B514721
theorem B1948823 : Blo 303832 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B343255 : Blo 303832 343255 := bstep (se 1 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 343255 = 514883) B514883
theorem B343435 : Blo 303832 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B769459 : Blo 303832 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B671179 : Blo 303832 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B343543 : Blo 303832 343543 := bstep (se 1 (by rfl) ⟨257657, by rfl⟩ : syracuseStep 343543 = 515315) B515315
theorem B769601 : Blo 303832 769601 := bstep (se 2 (by rfl) ⟨288600, by rfl⟩ : syracuseStep 769601 = 577201) B577201
theorem B1949285 : Blo 303832 1949285 := bstep (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) B365491
theorem B1752677 : Blo 303832 1752677 := bstep (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) B328627
theorem B1031831 : Blo 303832 1031831 := bstep (se 1 (by rfl) ⟨773873, by rfl⟩ : syracuseStep 1031831 = 1547747) B1547747
theorem B343723 : Blo 303832 343723 := bstep (se 1 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 343723 = 515585) B515585
theorem B310987 : Blo 303832 310987 := bstep (se 1 (by rfl) ⟨233240, by rfl⟩ : syracuseStep 310987 = 466481) B466481
theorem B343831 : Blo 303832 343831 := bstep (se 1 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 343831 = 515747) B515747
theorem B442135 : Blo 303832 442135 := bstep (se 1 (by rfl) ⟨331601, by rfl⟩ : syracuseStep 442135 = 663203) B663203
theorem B868171 : Blo 303832 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B344011 : Blo 303832 344011 := bstep (se 1 (by rfl) ⟨258008, by rfl⟩ : syracuseStep 344011 = 516017) B516017
theorem B344119 : Blo 303832 344119 := bstep (se 1 (by rfl) ⟨258089, by rfl⟩ : syracuseStep 344119 = 516179) B516179
theorem B2801729 : Blo 303832 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B868445 : Blo 303832 868445 := bstep (se 3 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 868445 = 325667) B325667
theorem B1032371 : Blo 303832 1032371 := bstep (se 1 (by rfl) ⟨774278, by rfl⟩ : syracuseStep 1032371 = 1548557) B1548557
theorem B344299 : Blo 303832 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B3916097 : Blo 303832 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B344407 : Blo 303832 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B5226929 : Blo 303832 5226929 := bstep (se 2 (by rfl) ⟨1960098, by rfl⟩ : syracuseStep 5226929 = 3920197) B3920197
theorem B1032641 : Blo 303832 1032641 := bstep (se 2 (by rfl) ⟨387240, by rfl⟩ : syracuseStep 1032641 = 774481) B774481
theorem B344587 : Blo 303832 344587 := bstep (se 1 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 344587 = 516881) B516881
theorem B344695 : Blo 303832 344695 := bstep (se 1 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 344695 = 517043) B517043
theorem B1557143 : Blo 303832 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B2310929 : Blo 303832 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B1327889 : Blo 303832 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B344875 : Blo 303832 344875 := bstep (se 1 (by rfl) ⟨258656, by rfl⟩ : syracuseStep 344875 = 517313) B517313
theorem B1164077 : Blo 303832 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B770867 : Blo 303832 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B344983 : Blo 303832 344983 := bstep (se 1 (by rfl) ⟨258737, by rfl⟩ : syracuseStep 344983 = 517475) B517475
theorem B1033181 : Blo 303832 1033181 := bstep (se 3 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 1033181 = 387443) B387443
theorem B345163 : Blo 303832 345163 := bstep (se 1 (by rfl) ⟨258872, by rfl⟩ : syracuseStep 345163 = 517745) B517745
theorem B345271 : Blo 303832 345271 := bstep (se 1 (by rfl) ⟨258953, by rfl⟩ : syracuseStep 345271 = 517907) B517907
theorem B771403 : Blo 303832 771403 := bstep (se 1 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 771403 = 1157105) B1157105
theorem B345451 : Blo 303832 345451 := bstep (se 1 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 345451 = 518177) B518177
theorem B345559 : Blo 303832 345559 := bstep (se 1 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 345559 = 518339) B518339
theorem B771545 : Blo 303832 771545 := bstep (se 2 (by rfl) ⟨289329, by rfl⟩ : syracuseStep 771545 = 578659) B578659
theorem B1164851 : Blo 303832 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B345739 : Blo 303832 345739 := bstep (se 1 (by rfl) ⟨259304, by rfl⟩ : syracuseStep 345739 = 518609) B518609
theorem B1328791 : Blo 303832 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B345847 : Blo 303832 345847 := bstep (se 1 (by rfl) ⟨259385, by rfl⟩ : syracuseStep 345847 = 518771) B518771
theorem B1328899 : Blo 303832 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B2475821 : Blo 303832 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B411481 : Blo 303832 411481 := bstep (se 2 (by rfl) ⟨154305, by rfl⟩ : syracuseStep 411481 = 308611) B308611
theorem B1460119 : Blo 303832 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B346027 : Blo 303832 346027 := bstep (se 1 (by rfl) ⟨259520, by rfl⟩ : syracuseStep 346027 = 519041) B519041
theorem B346135 : Blo 303832 346135 := bstep (se 1 (by rfl) ⟨259601, by rfl⟩ : syracuseStep 346135 = 519203) B519203
theorem B1034315 : Blo 303832 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B2508893 : Blo 303832 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B772375 : Blo 303832 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B870745 : Blo 303832 870745 := bstep (se 2 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 870745 = 653059) B653059
theorem B1034585 : Blo 303832 1034585 := bstep (se 2 (by rfl) ⟨387969, by rfl⟩ : syracuseStep 1034585 = 775939) B775939
theorem B772811 : Blo 303832 772811 := bstep (se 1 (by rfl) ⟨579608, by rfl⟩ : syracuseStep 772811 = 1159217) B1159217
theorem B4967345 : Blo 303832 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B871361 : Blo 303832 871361 := bstep (se 2 (by rfl) ⟨326760, by rfl⟩ : syracuseStep 871361 = 653521) B653521
theorem B1166339 : Blo 303832 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1035287 : Blo 303832 1035287 := bstep (se 1 (by rfl) ⟨776465, by rfl⟩ : syracuseStep 1035287 = 1552931) B1552931
theorem B1657901 : Blo 303832 1657901 := bstep (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) B621713
theorem B773185 : Blo 303832 773185 := bstep (se 2 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 773185 = 579889) B579889
theorem B1166795 : Blo 303832 1166795 := bstep (se 1 (by rfl) ⟨875096, by rfl⟩ : syracuseStep 1166795 = 1750193) B1750193
theorem B1855021 : Blo 303832 1855021 := bstep (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) B695633
theorem B1035827 : Blo 303832 1035827 := bstep (se 1 (by rfl) ⟨776870, by rfl⟩ : syracuseStep 1035827 = 1553741) B1553741
theorem B1166993 : Blo 303832 1166993 := bstep (se 2 (by rfl) ⟨437622, by rfl⟩ : syracuseStep 1166993 = 875245) B875245
theorem B773783 : Blo 303832 773783 := bstep (se 1 (by rfl) ⟨580337, by rfl⟩ : syracuseStep 773783 = 1160675) B1160675
theorem B1036097 : Blo 303832 1036097 := bstep (se 2 (by rfl) ⟨388536, by rfl⟩ : syracuseStep 1036097 = 777073) B777073
theorem B577459 : Blo 303832 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B577687 : Blo 303832 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B577793 : Blo 303832 577793 := bstep (se 2 (by rfl) ⟨216672, by rfl⟩ : syracuseStep 577793 = 433345) B433345
theorem B1036637 : Blo 303832 1036637 := bstep (se 3 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 1036637 = 388739) B388739
theorem B1102211 : Blo 303832 1102211 := bstep (se 1 (by rfl) ⟨826658, by rfl⟩ : syracuseStep 1102211 = 1653317) B1653317
theorem B1167767 : Blo 303832 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B577945 : Blo 303832 577945 := bstep (se 2 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 577945 = 433459) B433459
theorem B774593 : Blo 303832 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B2314817 : Blo 303832 2314817 := bstep (se 2 (by rfl) ⟨868056, by rfl⟩ : syracuseStep 2314817 = 1736113) B1736113
theorem B1167965 : Blo 303832 1167965 := bstep (se 3 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 1167965 = 437987) B437987
theorem B1659523 : Blo 303832 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B840385 : Blo 303832 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B3134213 : Blo 303832 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B775129 : Blo 303832 775129 := bstep (se 2 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 775129 = 581347) B581347
theorem B873433 : Blo 303832 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B1299473 : Blo 303832 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B513047 : Blo 303832 513047 := bstep (se 1 (by rfl) ⟨384785, by rfl⟩ : syracuseStep 513047 = 769571) B769571
theorem B513175 : Blo 303832 513175 := bstep (se 1 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 513175 = 769763) B769763
theorem B873821 : Blo 303832 873821 := bstep (se 3 (by rfl) ⟨163841, by rfl⟩ : syracuseStep 873821 = 327683) B327683
theorem B1037771 : Blo 303832 1037771 := bstep (se 1 (by rfl) ⟨778328, by rfl⟩ : syracuseStep 1037771 = 1556657) B1556657
theorem B3462749 : Blo 303832 3462749 := bstep (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) B1298531
theorem B579251 : Blo 303832 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B1038041 : Blo 303832 1038041 := bstep (se 2 (by rfl) ⟨389265, by rfl⟩ : syracuseStep 1038041 = 778531) B778531
theorem B1103581 : Blo 303832 1103581 := bstep (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) B413843
theorem B513803 : Blo 303832 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B415513 : Blo 303832 415513 := bstep (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) B311635
theorem B579403 : Blo 303832 579403 := bstep (se 1 (by rfl) ⟨434552, by rfl⟩ : syracuseStep 579403 = 869105) B869105
theorem B513931 : Blo 303832 513931 := bstep (se 1 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 513931 = 770897) B770897
theorem B1857431 : Blo 303832 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1300445 : Blo 303832 1300445 := bstep (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) B487667
theorem B514073 : Blo 303832 514073 := bstep (se 2 (by rfl) ⟨192777, by rfl⟩ : syracuseStep 514073 = 385555) B385555
theorem B776243 : Blo 303832 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B514201 : Blo 303832 514201 := bstep (se 2 (by rfl) ⟨192825, by rfl⟩ : syracuseStep 514201 = 385651) B385651
theorem B579737 : Blo 303832 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B776537 : Blo 303832 776537 := bstep (se 2 (by rfl) ⟨291201, by rfl⟩ : syracuseStep 776537 = 582403) B582403
theorem B1038743 : Blo 303832 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B2316761 : Blo 303832 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B1104401 : Blo 303832 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B1464925 : Blo 303832 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B514775 : Blo 303832 514775 := bstep (se 1 (by rfl) ⟨386081, by rfl⟩ : syracuseStep 514775 = 772163) B772163
theorem B580375 : Blo 303832 580375 := bstep (se 1 (by rfl) ⟨435281, by rfl⟩ : syracuseStep 580375 = 870563) B870563
theorem B5200685 : Blo 303832 5200685 := bstep (se 3 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 5200685 = 1950257) B1950257
theorem B514903 : Blo 303832 514903 := bstep (se 1 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 514903 = 772355) B772355
theorem B2939921 : Blo 303832 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B1236161 : Blo 303832 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B417035 : Blo 303832 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B1301933 : Blo 303832 1301933 := bstep (se 3 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 1301933 = 488225) B488225
theorem B515531 : Blo 303832 515531 := bstep (se 1 (by rfl) ⟨386648, by rfl⟩ : syracuseStep 515531 = 773297) B773297
theorem B515659 : Blo 303832 515659 := bstep (se 1 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 515659 = 773489) B773489
theorem B581195 : Blo 303832 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B581249 : Blo 303832 581249 := bstep (se 2 (by rfl) ⟨217968, by rfl⟩ : syracuseStep 581249 = 435937) B435937
theorem B515801 : Blo 303832 515801 := bstep (se 2 (by rfl) ⟨193425, by rfl⟩ : syracuseStep 515801 = 386851) B386851
theorem B515929 : Blo 303832 515929 := bstep (se 2 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 515929 = 386947) B386947
theorem B384907 : Blo 303832 384907 := bstep (se 1 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 384907 = 577361) B577361
theorem B778187 : Blo 303832 778187 := bstep (se 1 (by rfl) ⟨583640, by rfl⟩ : syracuseStep 778187 = 1167281) B1167281
theorem B385175 : Blo 303832 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B8348021 : Blo 303832 8348021 := bstep (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) B782627
theorem B516503 : Blo 303832 516503 := bstep (se 1 (by rfl) ⟨387377, by rfl⟩ : syracuseStep 516503 = 774755) B774755
theorem B516631 : Blo 303832 516631 := bstep (se 1 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 516631 = 774947) B774947
theorem B582167 : Blo 303832 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B975539 : Blo 303832 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B385879 : Blo 303832 385879 := bstep (se 1 (by rfl) ⟨289409, by rfl⟩ : syracuseStep 385879 = 578819) B578819
theorem B779159 : Blo 303832 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B8479667 : Blo 303832 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B582707 : Blo 303832 582707 := bstep (se 1 (by rfl) ⟨437030, by rfl⟩ : syracuseStep 582707 = 874061) B874061
theorem B5563523 : Blo 303832 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B517259 : Blo 303832 517259 := bstep (se 1 (by rfl) ⟨387944, by rfl⟩ : syracuseStep 517259 = 775889) B775889
theorem B517387 : Blo 303832 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B1172825 : Blo 303832 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B1303897 : Blo 303832 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B1795421 : Blo 303832 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B517529 : Blo 303832 517529 := bstep (se 2 (by rfl) ⟨194073, by rfl⟩ : syracuseStep 517529 = 388147) B388147
theorem B2352563 : Blo 303832 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B517657 : Blo 303832 517657 := bstep (se 2 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 517657 = 388243) B388243
theorem B583193 : Blo 303832 583193 := bstep (se 2 (by rfl) ⟨218697, by rfl⟩ : syracuseStep 583193 = 437395) B437395
theorem B648985 : Blo 303832 648985 := bstep (se 2 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 648985 = 486739) B486739
theorem B2320163 : Blo 303832 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B2615105 : Blo 303832 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B419671 : Blo 303832 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B1107863 : Blo 303832 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B8775701 : Blo 303832 8775701 := bstep (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) B411361
theorem B518231 : Blo 303832 518231 := bstep (se 1 (by rfl) ⟨388673, by rfl⟩ : syracuseStep 518231 = 777347) B777347
theorem B518359 : Blo 303832 518359 := bstep (se 1 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 518359 = 777539) B777539
theorem B1304855 : Blo 303832 1304855 := bstep (se 1 (by rfl) ⟨978641, by rfl⟩ : syracuseStep 1304855 = 1957283) B1957283
theorem B2779609 : Blo 303832 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B387595 : Blo 303832 387595 := bstep (se 1 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 387595 = 581393) B581393
theorem B650035 : Blo 303832 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B518987 : Blo 303832 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B519115 : Blo 303832 519115 := bstep (se 1 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 519115 = 778673) B778673
theorem B519257 : Blo 303832 519257 := bstep (se 2 (by rfl) ⟨194721, by rfl⟩ : syracuseStep 519257 = 389443) B389443
theorem B519385 : Blo 303832 519385 := bstep (se 2 (by rfl) ⟨194769, by rfl⟩ : syracuseStep 519385 = 389539) B389539
theorem B5860613 : Blo 303832 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B781643 : Blo 303832 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B388567 : Blo 303832 388567 := bstep (se 1 (by rfl) ⟨291425, by rfl⟩ : syracuseStep 388567 = 582851) B582851
theorem B4419107 : Blo 303832 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B487001 : Blo 303832 487001 := bstep (se 2 (by rfl) ⟨182625, by rfl⟩ : syracuseStep 487001 = 365251) B365251
theorem B552577 : Blo 303832 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B487129 : Blo 303832 487129 := bstep (se 2 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 487129 = 365347) B365347
theorem B683801 : Blo 303832 683801 := bstep (se 2 (by rfl) ⟨256425, by rfl⟩ : syracuseStep 683801 = 512851) B512851
theorem B683891 : Blo 303832 683891 := bstep (se 1 (by rfl) ⟨512918, by rfl⟩ : syracuseStep 683891 = 1025837) B1025837
theorem B683927 : Blo 303832 683927 := bstep (se 1 (by rfl) ⟨512945, by rfl⟩ : syracuseStep 683927 = 1025891) B1025891
theorem B618455 : Blo 303832 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B1961945 : Blo 303832 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B3502115 : Blo 303832 3502115 := bstep (se 1 (by rfl) ⟨2626586, by rfl⟩ : syracuseStep 3502115 = 5253173) B5253173
theorem B684107 : Blo 303832 684107 := bstep (se 1 (by rfl) ⟨513080, by rfl⟩ : syracuseStep 684107 = 1026161) B1026161
theorem B684161 : Blo 303832 684161 := bstep (se 2 (by rfl) ⟨256560, by rfl⟩ : syracuseStep 684161 = 513121) B513121
theorem B618625 : Blo 303832 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B3174551 : Blo 303832 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B651521 : Blo 303832 651521 := bstep (se 2 (by rfl) ⟨244320, by rfl⟩ : syracuseStep 651521 = 488641) B488641
theorem B389387 : Blo 303832 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B684377 : Blo 303832 684377 := bstep (se 2 (by rfl) ⟨256641, by rfl⟩ : syracuseStep 684377 = 513283) B513283
theorem B1733015 : Blo 303832 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B684467 : Blo 303832 684467 := bstep (se 1 (by rfl) ⟨513350, by rfl⟩ : syracuseStep 684467 = 1026701) B1026701
theorem B684503 : Blo 303832 684503 := bstep (se 1 (by rfl) ⟨513377, by rfl⟩ : syracuseStep 684503 = 1026755) B1026755
theorem B651863 : Blo 303832 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B684683 : Blo 303832 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B684737 : Blo 303832 684737 := bstep (se 2 (by rfl) ⟨256776, by rfl⟩ : syracuseStep 684737 = 513553) B513553
theorem B586433 : Blo 303832 586433 := bstep (se 2 (by rfl) ⟨219912, by rfl⟩ : syracuseStep 586433 = 439825) B439825
theorem B652171 : Blo 303832 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B684953 : Blo 303832 684953 := bstep (se 2 (by rfl) ⟨256857, by rfl⟩ : syracuseStep 684953 = 513715) B513715
theorem B1242049 : Blo 303832 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B685043 : Blo 303832 685043 := bstep (se 1 (by rfl) ⟨513782, by rfl⟩ : syracuseStep 685043 = 1027565) B1027565
theorem B685079 : Blo 303832 685079 := bstep (se 1 (by rfl) ⟨513809, by rfl⟩ : syracuseStep 685079 = 1027619) B1027619
theorem B3929219 : Blo 303832 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B455819 : Blo 303832 455819 := bstep (se 1 (by rfl) ⟨341864, by rfl⟩ : syracuseStep 455819 = 683729) B683729
theorem B455831 : Blo 303832 455831 := bstep (se 1 (by rfl) ⟨341873, by rfl⟩ : syracuseStep 455831 = 683747) B683747
theorem B554177 : Blo 303832 554177 := bstep (se 2 (by rfl) ⟨207816, by rfl⟩ : syracuseStep 554177 = 415633) B415633
theorem B685259 : Blo 303832 685259 := bstep (se 1 (by rfl) ⟨513944, by rfl⟩ : syracuseStep 685259 = 1027889) B1027889
theorem B881867 : Blo 303832 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B455897 : Blo 303832 455897 := bstep (se 2 (by rfl) ⟨170961, by rfl⟩ : syracuseStep 455897 = 341923) B341923
theorem B685313 : Blo 303832 685313 := bstep (se 2 (by rfl) ⟨256992, by rfl⟩ : syracuseStep 685313 = 513985) B513985
theorem B456011 : Blo 303832 456011 := bstep (se 1 (by rfl) ⟨342008, by rfl⟩ : syracuseStep 456011 = 684017) B684017
theorem B456023 : Blo 303832 456023 := bstep (se 1 (by rfl) ⟨342017, by rfl⟩ : syracuseStep 456023 = 684035) B684035
theorem B456089 : Blo 303832 456089 := bstep (se 2 (by rfl) ⟨171033, by rfl⟩ : syracuseStep 456089 = 342067) B342067
theorem B685529 : Blo 303832 685529 := bstep (se 2 (by rfl) ⟨257073, by rfl⟩ : syracuseStep 685529 = 514147) B514147
theorem B456203 : Blo 303832 456203 := bstep (se 1 (by rfl) ⟨342152, by rfl⟩ : syracuseStep 456203 = 684305) B684305
theorem B554507 : Blo 303832 554507 := bstep (se 1 (by rfl) ⟨415880, by rfl⟩ : syracuseStep 554507 = 831761) B831761
theorem B456215 : Blo 303832 456215 := bstep (se 1 (by rfl) ⟨342161, by rfl⟩ : syracuseStep 456215 = 684323) B684323
theorem B685619 : Blo 303832 685619 := bstep (se 1 (by rfl) ⟨514214, by rfl⟩ : syracuseStep 685619 = 1028429) B1028429
theorem B685655 : Blo 303832 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B456281 : Blo 303832 456281 := bstep (se 2 (by rfl) ⟨171105, by rfl⟩ : syracuseStep 456281 = 342211) B342211
theorem B1308305 : Blo 303832 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B4159127 : Blo 303832 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B325291 : Blo 303832 325291 := bstep (se 1 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 325291 = 487937) B487937
theorem B456395 : Blo 303832 456395 := bstep (se 1 (by rfl) ⟨342296, by rfl⟩ : syracuseStep 456395 = 684593) B684593
theorem B456407 : Blo 303832 456407 := bstep (se 1 (by rfl) ⟨342305, by rfl⟩ : syracuseStep 456407 = 684611) B684611
theorem B653017 : Blo 303832 653017 := bstep (se 2 (by rfl) ⟨244881, by rfl⟩ : syracuseStep 653017 = 489763) B489763
theorem B685835 : Blo 303832 685835 := bstep (se 1 (by rfl) ⟨514376, by rfl⟩ : syracuseStep 685835 = 1028753) B1028753
theorem B456473 : Blo 303832 456473 := bstep (se 2 (by rfl) ⟨171177, by rfl⟩ : syracuseStep 456473 = 342355) B342355
theorem B685889 : Blo 303832 685889 := bstep (se 2 (by rfl) ⟨257208, by rfl⟩ : syracuseStep 685889 = 514417) B514417
theorem B456587 : Blo 303832 456587 := bstep (se 1 (by rfl) ⟨342440, by rfl⟩ : syracuseStep 456587 = 684881) B684881
theorem B456599 : Blo 303832 456599 := bstep (se 1 (by rfl) ⟨342449, by rfl⟩ : syracuseStep 456599 = 684899) B684899
theorem B1177517 : Blo 303832 1177517 := bstep (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) B441569
theorem B456665 : Blo 303832 456665 := bstep (se 2 (by rfl) ⟨171249, by rfl⟩ : syracuseStep 456665 = 342499) B342499
theorem B620531 : Blo 303832 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B686105 : Blo 303832 686105 := bstep (se 2 (by rfl) ⟨257289, by rfl⟩ : syracuseStep 686105 = 514579) B514579
theorem B20183093 : Blo 303832 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B456779 : Blo 303832 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B456791 : Blo 303832 456791 := bstep (se 1 (by rfl) ⟨342593, by rfl⟩ : syracuseStep 456791 = 685187) B685187
theorem B686195 : Blo 303832 686195 := bstep (se 1 (by rfl) ⟨514646, by rfl⟩ : syracuseStep 686195 = 1029293) B1029293
theorem B686231 : Blo 303832 686231 := bstep (se 1 (by rfl) ⟨514673, by rfl⟩ : syracuseStep 686231 = 1029347) B1029347
theorem B456857 : Blo 303832 456857 := bstep (se 2 (by rfl) ⟨171321, by rfl⟩ : syracuseStep 456857 = 342643) B342643
theorem B456971 : Blo 303832 456971 := bstep (se 1 (by rfl) ⟨342728, by rfl⟩ : syracuseStep 456971 = 685457) B685457
theorem B1734929 : Blo 303832 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B456983 : Blo 303832 456983 := bstep (se 1 (by rfl) ⟨342737, by rfl⟩ : syracuseStep 456983 = 685475) B685475
theorem B686411 : Blo 303832 686411 := bstep (se 1 (by rfl) ⟨514808, by rfl⟩ : syracuseStep 686411 = 1029617) B1029617
theorem B1472843 : Blo 303832 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B457049 : Blo 303832 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B686465 : Blo 303832 686465 := bstep (se 2 (by rfl) ⟨257424, by rfl⟩ : syracuseStep 686465 = 514849) B514849
theorem B457163 : Blo 303832 457163 := bstep (se 1 (by rfl) ⟨342872, by rfl⟩ : syracuseStep 457163 = 685745) B685745
theorem B457175 : Blo 303832 457175 := bstep (se 1 (by rfl) ⟨342881, by rfl⟩ : syracuseStep 457175 = 685763) B685763
theorem B457241 : Blo 303832 457241 := bstep (se 2 (by rfl) ⟨171465, by rfl⟩ : syracuseStep 457241 = 342931) B342931
theorem B1309229 : Blo 303832 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B686681 : Blo 303832 686681 := bstep (se 2 (by rfl) ⟨257505, by rfl⟩ : syracuseStep 686681 = 515011) B515011
theorem B2226781 : Blo 303832 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B457355 : Blo 303832 457355 := bstep (se 1 (by rfl) ⟨343016, by rfl⟩ : syracuseStep 457355 = 686033) B686033
theorem B457367 : Blo 303832 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B686771 : Blo 303832 686771 := bstep (se 1 (by rfl) ⟨515078, by rfl⟩ : syracuseStep 686771 = 1030157) B1030157
theorem B1178315 : Blo 303832 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B8321741 : Blo 303832 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B686807 : Blo 303832 686807 := bstep (se 1 (by rfl) ⟨515105, by rfl⟩ : syracuseStep 686807 = 1030211) B1030211
theorem B326359 : Blo 303832 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B457433 : Blo 303832 457433 := bstep (se 2 (by rfl) ⟨171537, by rfl⟩ : syracuseStep 457433 = 343075) B343075
theorem B588505 : Blo 303832 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B457547 : Blo 303832 457547 := bstep (se 1 (by rfl) ⟨343160, by rfl⟩ : syracuseStep 457547 = 686321) B686321
theorem B457559 : Blo 303832 457559 := bstep (se 1 (by rfl) ⟨343169, by rfl⟩ : syracuseStep 457559 = 686339) B686339
theorem B686987 : Blo 303832 686987 := bstep (se 1 (by rfl) ⟨515240, by rfl⟩ : syracuseStep 686987 = 1030481) B1030481
theorem B457625 : Blo 303832 457625 := bstep (se 2 (by rfl) ⟨171609, by rfl⟩ : syracuseStep 457625 = 343219) B343219
theorem B687041 : Blo 303832 687041 := bstep (se 2 (by rfl) ⟨257640, by rfl⟩ : syracuseStep 687041 = 515281) B515281
theorem B654323 : Blo 303832 654323 := bstep (se 1 (by rfl) ⟨490742, by rfl⟩ : syracuseStep 654323 = 981485) B981485
theorem B2325509 : Blo 303832 2325509 := bstep (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) B436033
theorem B457739 : Blo 303832 457739 := bstep (se 1 (by rfl) ⟨343304, by rfl⟩ : syracuseStep 457739 = 686609) B686609
theorem B457751 : Blo 303832 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B490583 : Blo 303832 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B457817 : Blo 303832 457817 := bstep (se 2 (by rfl) ⟨171681, by rfl⟩ : syracuseStep 457817 = 343363) B343363
theorem B621697 : Blo 303832 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B687257 : Blo 303832 687257 := bstep (se 2 (by rfl) ⟨257721, by rfl⟩ : syracuseStep 687257 = 515443) B515443
theorem B457931 : Blo 303832 457931 := bstep (se 1 (by rfl) ⟨343448, by rfl⟩ : syracuseStep 457931 = 686897) B686897
theorem B457943 : Blo 303832 457943 := bstep (se 1 (by rfl) ⟨343457, by rfl⟩ : syracuseStep 457943 = 686915) B686915
theorem B687347 : Blo 303832 687347 := bstep (se 1 (by rfl) ⟨515510, by rfl⟩ : syracuseStep 687347 = 1031021) B1031021
theorem B392459 : Blo 303832 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B1965329 : Blo 303832 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B687383 : Blo 303832 687383 := bstep (se 1 (by rfl) ⟨515537, by rfl⟩ : syracuseStep 687383 = 1031075) B1031075
theorem B458009 : Blo 303832 458009 := bstep (se 2 (by rfl) ⟨171753, by rfl⟩ : syracuseStep 458009 = 343507) B343507
theorem B1080707 : Blo 303832 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B458123 : Blo 303832 458123 := bstep (se 1 (by rfl) ⟨343592, by rfl⟩ : syracuseStep 458123 = 687185) B687185
theorem B458135 : Blo 303832 458135 := bstep (se 1 (by rfl) ⟨343601, by rfl⟩ : syracuseStep 458135 = 687203) B687203
theorem B687563 : Blo 303832 687563 := bstep (se 1 (by rfl) ⟨515672, by rfl⟩ : syracuseStep 687563 = 1031345) B1031345
theorem B458201 : Blo 303832 458201 := bstep (se 2 (by rfl) ⟨171825, by rfl⟩ : syracuseStep 458201 = 343651) B343651
theorem B687617 : Blo 303832 687617 := bstep (se 2 (by rfl) ⟨257856, by rfl⟩ : syracuseStep 687617 = 515713) B515713
theorem B327179 : Blo 303832 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B458315 : Blo 303832 458315 := bstep (se 1 (by rfl) ⟨343736, by rfl⟩ : syracuseStep 458315 = 687473) B687473
theorem B458327 : Blo 303832 458327 := bstep (se 1 (by rfl) ⟨343745, by rfl⟩ : syracuseStep 458327 = 687491) B687491
theorem B458393 : Blo 303832 458393 := bstep (se 2 (by rfl) ⟨171897, by rfl⟩ : syracuseStep 458393 = 343795) B343795
theorem B687833 : Blo 303832 687833 := bstep (se 2 (by rfl) ⟨257937, by rfl⟩ : syracuseStep 687833 = 515875) B515875
theorem B458507 : Blo 303832 458507 := bstep (se 1 (by rfl) ⟨343880, by rfl⟩ : syracuseStep 458507 = 687761) B687761
theorem B458519 : Blo 303832 458519 := bstep (se 1 (by rfl) ⟨343889, by rfl⟩ : syracuseStep 458519 = 687779) B687779
theorem B687923 : Blo 303832 687923 := bstep (se 1 (by rfl) ⟨515942, by rfl⟩ : syracuseStep 687923 = 1031885) B1031885
theorem B687959 : Blo 303832 687959 := bstep (se 1 (by rfl) ⟨515969, by rfl⟩ : syracuseStep 687959 = 1031939) B1031939
theorem B458585 : Blo 303832 458585 := bstep (se 2 (by rfl) ⟨171969, by rfl⟩ : syracuseStep 458585 = 343939) B343939
theorem B1539971 : Blo 303832 1539971 := bstep (se 1 (by rfl) ⟨1154978, by rfl⟩ : syracuseStep 1539971 = 2309957) B2309957
theorem B458699 : Blo 303832 458699 := bstep (se 1 (by rfl) ⟨344024, by rfl⟩ : syracuseStep 458699 = 688049) B688049
theorem B458711 : Blo 303832 458711 := bstep (se 1 (by rfl) ⟨344033, by rfl⟩ : syracuseStep 458711 = 688067) B688067
theorem B1310681 : Blo 303832 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B458759 : Blo 303832 458759 := bstep (se 1 (by rfl) ⟨344069, by rfl⟩ : syracuseStep 458759 = 688139) B688139
theorem B458795 : Blo 303832 458795 := bstep (se 1 (by rfl) ⟨344096, by rfl⟩ : syracuseStep 458795 = 688193) B688193
theorem B1867819 : Blo 303832 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B458825 : Blo 303832 458825 := bstep (se 2 (by rfl) ⟨172059, by rfl⟩ : syracuseStep 458825 = 344119) B344119
theorem B688247 : Blo 303832 688247 := bstep (se 1 (by rfl) ⟨516185, by rfl⟩ : syracuseStep 688247 = 1032371) B1032371
theorem B458939 : Blo 303832 458939 := bstep (se 1 (by rfl) ⟨344204, by rfl⟩ : syracuseStep 458939 = 688409) B688409
theorem B2195657 : Blo 303832 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B458999 : Blo 303832 458999 := bstep (se 1 (by rfl) ⟨344249, by rfl⟩ : syracuseStep 458999 = 688499) B688499
theorem B459023 : Blo 303832 459023 := bstep (se 1 (by rfl) ⟨344267, by rfl⟩ : syracuseStep 459023 = 688535) B688535
theorem B688427 : Blo 303832 688427 := bstep (se 1 (by rfl) ⟨516320, by rfl⟩ : syracuseStep 688427 = 1032641) B1032641
theorem B459065 : Blo 303832 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B459143 : Blo 303832 459143 := bstep (se 1 (by rfl) ⟨344357, by rfl⟩ : syracuseStep 459143 = 688715) B688715
theorem B655751 : Blo 303832 655751 := bstep (se 1 (by rfl) ⟨491813, by rfl⟩ : syracuseStep 655751 = 983627) B983627
theorem B459179 : Blo 303832 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B459209 : Blo 303832 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B1540619 : Blo 303832 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B885259 : Blo 303832 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B459323 : Blo 303832 459323 := bstep (se 1 (by rfl) ⟨344492, by rfl⟩ : syracuseStep 459323 = 688985) B688985
theorem B459383 : Blo 303832 459383 := bstep (se 1 (by rfl) ⟨344537, by rfl⟩ : syracuseStep 459383 = 689075) B689075
theorem B459407 : Blo 303832 459407 := bstep (se 1 (by rfl) ⟨344555, by rfl⟩ : syracuseStep 459407 = 689111) B689111
theorem B688787 : Blo 303832 688787 := bstep (se 1 (by rfl) ⟨516590, by rfl⟩ : syracuseStep 688787 = 1033181) B1033181
theorem B590483 : Blo 303832 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B1540781 : Blo 303832 1540781 := bstep (se 3 (by rfl) ⟨288896, by rfl⟩ : syracuseStep 1540781 = 577793) B577793
theorem B1737389 : Blo 303832 1737389 := bstep (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) B651521
theorem B459449 : Blo 303832 459449 := bstep (se 2 (by rfl) ⟨172293, by rfl⟩ : syracuseStep 459449 = 344587) B344587
theorem B688841 : Blo 303832 688841 := bstep (se 2 (by rfl) ⟨258315, by rfl⟩ : syracuseStep 688841 = 516631) B516631
theorem B459527 : Blo 303832 459527 := bstep (se 1 (by rfl) ⟨344645, by rfl⟩ : syracuseStep 459527 = 689291) B689291
theorem B459563 : Blo 303832 459563 := bstep (se 1 (by rfl) ⟨344672, by rfl⟩ : syracuseStep 459563 = 689345) B689345
theorem B459593 : Blo 303832 459593 := bstep (se 2 (by rfl) ⟨172347, by rfl⟩ : syracuseStep 459593 = 344695) B344695
theorem B459707 : Blo 303832 459707 := bstep (se 1 (by rfl) ⟨344780, by rfl⟩ : syracuseStep 459707 = 689561) B689561
theorem B459767 : Blo 303832 459767 := bstep (se 1 (by rfl) ⟨344825, by rfl⟩ : syracuseStep 459767 = 689651) B689651
theorem B459791 : Blo 303832 459791 := bstep (se 1 (by rfl) ⟨344843, by rfl⟩ : syracuseStep 459791 = 689687) B689687
theorem B459833 : Blo 303832 459833 := bstep (se 2 (by rfl) ⟨172437, by rfl⟩ : syracuseStep 459833 = 344875) B344875
theorem B459911 : Blo 303832 459911 := bstep (se 1 (by rfl) ⟨344933, by rfl⟩ : syracuseStep 459911 = 689867) B689867
theorem B459947 : Blo 303832 459947 := bstep (se 1 (by rfl) ⟨344960, by rfl⟩ : syracuseStep 459947 = 689921) B689921
theorem B459977 : Blo 303832 459977 := bstep (se 2 (by rfl) ⟨172491, by rfl⟩ : syracuseStep 459977 = 344983) B344983
theorem B460091 : Blo 303832 460091 := bstep (se 1 (by rfl) ⟨345068, by rfl⟩ : syracuseStep 460091 = 690137) B690137
theorem B460151 : Blo 303832 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B689543 : Blo 303832 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B460175 : Blo 303832 460175 := bstep (se 1 (by rfl) ⟨345131, by rfl⟩ : syracuseStep 460175 = 690263) B690263
theorem B1672595 : Blo 303832 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B460217 : Blo 303832 460217 := bstep (se 2 (by rfl) ⟨172581, by rfl⟩ : syracuseStep 460217 = 345163) B345163
theorem B460295 : Blo 303832 460295 := bstep (se 1 (by rfl) ⟨345221, by rfl⟩ : syracuseStep 460295 = 690443) B690443
theorem B460331 : Blo 303832 460331 := bstep (se 1 (by rfl) ⟨345248, by rfl⟩ : syracuseStep 460331 = 690497) B690497
theorem B689723 : Blo 303832 689723 := bstep (se 1 (by rfl) ⟨517292, by rfl⟩ : syracuseStep 689723 = 1034585) B1034585
theorem B460361 : Blo 303832 460361 := bstep (se 2 (by rfl) ⟨172635, by rfl⟩ : syracuseStep 460361 = 345271) B345271
theorem B7603789 : Blo 303832 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B689849 : Blo 303832 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B460475 : Blo 303832 460475 := bstep (se 1 (by rfl) ⟨345356, by rfl⟩ : syracuseStep 460475 = 690713) B690713
theorem B460535 : Blo 303832 460535 := bstep (se 1 (by rfl) ⟨345401, by rfl⟩ : syracuseStep 460535 = 690803) B690803
theorem B460559 : Blo 303832 460559 := bstep (se 1 (by rfl) ⟨345419, by rfl⟩ : syracuseStep 460559 = 690839) B690839
theorem B1738529 : Blo 303832 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B460601 : Blo 303832 460601 := bstep (se 2 (by rfl) ⟨172725, by rfl⟩ : syracuseStep 460601 = 345451) B345451
theorem B460679 : Blo 303832 460679 := bstep (se 1 (by rfl) ⟨345509, by rfl⟩ : syracuseStep 460679 = 691019) B691019
theorem B460715 : Blo 303832 460715 := bstep (se 1 (by rfl) ⟨345536, by rfl⟩ : syracuseStep 460715 = 691073) B691073
theorem B460745 : Blo 303832 460745 := bstep (se 2 (by rfl) ⟨172779, by rfl⟩ : syracuseStep 460745 = 345559) B345559
theorem B3311563 : Blo 303832 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B690191 : Blo 303832 690191 := bstep (se 1 (by rfl) ⟨517643, by rfl⟩ : syracuseStep 690191 = 1035287) B1035287
theorem B690209 : Blo 303832 690209 := bstep (se 2 (by rfl) ⟨258828, by rfl⟩ : syracuseStep 690209 = 517657) B517657
theorem B460859 : Blo 303832 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B460919 : Blo 303832 460919 := bstep (se 1 (by rfl) ⟨345689, by rfl⟩ : syracuseStep 460919 = 691379) B691379
theorem B460943 : Blo 303832 460943 := bstep (se 1 (by rfl) ⟨345707, by rfl⟩ : syracuseStep 460943 = 691415) B691415
theorem B460985 : Blo 303832 460985 := bstep (se 2 (by rfl) ⟨172869, by rfl⟩ : syracuseStep 460985 = 345739) B345739
theorem B1771721 : Blo 303832 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1542401 : Blo 303832 1542401 := bstep (se 2 (by rfl) ⟨578400, by rfl⟩ : syracuseStep 1542401 = 1156801) B1156801
theorem B461063 : Blo 303832 461063 := bstep (se 1 (by rfl) ⟨345797, by rfl⟩ : syracuseStep 461063 = 691595) B691595
theorem B461099 : Blo 303832 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B461129 : Blo 303832 461129 := bstep (se 2 (by rfl) ⟨172923, by rfl⟩ : syracuseStep 461129 = 345847) B345847
theorem B1771865 : Blo 303832 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B690551 : Blo 303832 690551 := bstep (se 1 (by rfl) ⟨517913, by rfl⟩ : syracuseStep 690551 = 1035827) B1035827
theorem B461243 : Blo 303832 461243 := bstep (se 1 (by rfl) ⟨345932, by rfl⟩ : syracuseStep 461243 = 691865) B691865
theorem B559561 : Blo 303832 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B3770833 : Blo 303832 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B461303 : Blo 303832 461303 := bstep (se 1 (by rfl) ⟨345977, by rfl⟩ : syracuseStep 461303 = 691955) B691955
theorem B461327 : Blo 303832 461327 := bstep (se 1 (by rfl) ⟨345995, by rfl⟩ : syracuseStep 461327 = 691991) B691991
theorem B690731 : Blo 303832 690731 := bstep (se 1 (by rfl) ⟨518048, by rfl⟩ : syracuseStep 690731 = 1036097) B1036097
theorem B461369 : Blo 303832 461369 := bstep (se 2 (by rfl) ⟨173013, by rfl⟩ : syracuseStep 461369 = 346027) B346027
theorem B461447 : Blo 303832 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B461483 : Blo 303832 461483 := bstep (se 1 (by rfl) ⟨346112, by rfl⟩ : syracuseStep 461483 = 692225) B692225
theorem B461513 : Blo 303832 461513 := bstep (se 2 (by rfl) ⟨173067, by rfl⟩ : syracuseStep 461513 = 346135) B346135
theorem B461627 : Blo 303832 461627 := bstep (se 1 (by rfl) ⟨346220, by rfl⟩ : syracuseStep 461627 = 692441) B692441
theorem B461687 : Blo 303832 461687 := bstep (se 1 (by rfl) ⟨346265, by rfl⟩ : syracuseStep 461687 = 692531) B692531
theorem B461711 : Blo 303832 461711 := bstep (se 1 (by rfl) ⟨346283, by rfl⟩ : syracuseStep 461711 = 692567) B692567
theorem B691091 : Blo 303832 691091 := bstep (se 1 (by rfl) ⟨518318, by rfl⟩ : syracuseStep 691091 = 1036637) B1036637
theorem B691145 : Blo 303832 691145 := bstep (se 2 (by rfl) ⟨259179, by rfl⟩ : syracuseStep 691145 = 518359) B518359
theorem B1543211 : Blo 303832 1543211 := bstep (se 1 (by rfl) ⟨1157408, by rfl⟩ : syracuseStep 1543211 = 2314817) B2314817
theorem B462071 : Blo 303832 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B3706145 : Blo 303832 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B691847 : Blo 303832 691847 := bstep (se 1 (by rfl) ⟨518885, by rfl⟩ : syracuseStep 691847 = 1037771) B1037771
theorem B13471373 : Blo 303832 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2330369 : Blo 303832 2330369 := bstep (se 2 (by rfl) ⟨873888, by rfl⟩ : syracuseStep 2330369 = 1747777) B1747777
theorem B1314593 : Blo 303832 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B1183547 : Blo 303832 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B692027 : Blo 303832 692027 := bstep (se 1 (by rfl) ⟨519020, by rfl⟩ : syracuseStep 692027 = 1038041) B1038041
theorem B1576793 : Blo 303832 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B692153 : Blo 303832 692153 := bstep (se 2 (by rfl) ⟨259557, by rfl⟩ : syracuseStep 692153 = 519115) B519115
theorem B692495 : Blo 303832 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B692513 : Blo 303832 692513 := bstep (se 2 (by rfl) ⟨259692, by rfl⟩ : syracuseStep 692513 = 519385) B519385
theorem B1544507 : Blo 303832 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B3150211 : Blo 303832 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B1544669 : Blo 303832 1544669 := bstep (se 3 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 1544669 = 579251) B579251
theorem B1577495 : Blo 303832 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1544993 : Blo 303832 1544993 := bstep (se 2 (by rfl) ⟨579372, by rfl⟩ : syracuseStep 1544993 = 1158745) B1158745
theorem B10523429 : Blo 303832 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B824107 : Blo 303832 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B824833 : Blo 303832 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1545965 : Blo 303832 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B1546775 : Blo 303832 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1743403 : Blo 303832 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B11770433 : Blo 303832 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B6626063 : Blo 303832 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B1874909 : Blo 303832 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B3907075 : Blo 303832 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B433721 : Blo 303832 433721 := bstep (se 2 (by rfl) ⟨162645, by rfl⟩ : syracuseStep 433721 = 325291) B325291
theorem B1941185 : Blo 303832 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B2957219 : Blo 303832 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B1744861 : Blo 303832 1744861 := bstep (se 3 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 1744861 = 654323) B654323
theorem B2334743 : Blo 303832 2334743 := bstep (se 1 (by rfl) ⟨1751057, by rfl⟩ : syracuseStep 2334743 = 3502115) B3502115
theorem B1155329 : Blo 303832 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B1155343 : Blo 303832 1155343 := bstep (se 1 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 1155343 = 1733015) B1733015
theorem B434575 : Blo 303832 434575 := bstep (se 1 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 434575 = 651863) B651863
theorem B926099 : Blo 303832 926099 := bstep (se 1 (by rfl) ⟨694574, by rfl⟩ : syracuseStep 926099 = 1389149) B1389149
theorem B2204189 : Blo 303832 2204189 := bstep (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) B826571
theorem B303879 : Blo 303832 303879 := bstep (se 1 (by rfl) ⟨227909, by rfl⟩ : syracuseStep 303879 = 455819) B455819
theorem B303887 : Blo 303832 303887 := bstep (se 1 (by rfl) ⟨227915, by rfl⟩ : syracuseStep 303887 = 455831) B455831
theorem B369451 : Blo 303832 369451 := bstep (se 1 (by rfl) ⟨277088, by rfl⟩ : syracuseStep 369451 = 554177) B554177
theorem B303931 : Blo 303832 303931 := bstep (se 1 (by rfl) ⟨227948, by rfl⟩ : syracuseStep 303931 = 455897) B455897
theorem B467831 : Blo 303832 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B304007 : Blo 303832 304007 := bstep (se 1 (by rfl) ⟨228005, by rfl⟩ : syracuseStep 304007 = 456011) B456011
theorem B304015 : Blo 303832 304015 := bstep (se 1 (by rfl) ⟨228011, by rfl⟩ : syracuseStep 304015 = 456023) B456023
theorem B304059 : Blo 303832 304059 := bstep (se 1 (by rfl) ⟨228044, by rfl⟩ : syracuseStep 304059 = 456089) B456089
theorem B435145 : Blo 303832 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B304135 : Blo 303832 304135 := bstep (se 1 (by rfl) ⟨228101, by rfl⟩ : syracuseStep 304135 = 456203) B456203
theorem B304143 : Blo 303832 304143 := bstep (se 1 (by rfl) ⟨228107, by rfl⟩ : syracuseStep 304143 = 456215) B456215
theorem B304187 : Blo 303832 304187 := bstep (se 1 (by rfl) ⟨228140, by rfl⟩ : syracuseStep 304187 = 456281) B456281
theorem B304263 : Blo 303832 304263 := bstep (se 1 (by rfl) ⟨228197, by rfl⟩ : syracuseStep 304263 = 456395) B456395
theorem B304271 : Blo 303832 304271 := bstep (se 1 (by rfl) ⟨228203, by rfl⟩ : syracuseStep 304271 = 456407) B456407
theorem B664723 : Blo 303832 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B304315 : Blo 303832 304315 := bstep (se 1 (by rfl) ⟨228236, by rfl⟩ : syracuseStep 304315 = 456473) B456473
theorem B304391 : Blo 303832 304391 := bstep (se 1 (by rfl) ⟨228293, by rfl⟩ : syracuseStep 304391 = 456587) B456587
theorem B304399 : Blo 303832 304399 := bstep (se 1 (by rfl) ⟨228299, by rfl⟩ : syracuseStep 304399 = 456599) B456599
theorem B304443 : Blo 303832 304443 := bstep (se 1 (by rfl) ⟨228332, by rfl⟩ : syracuseStep 304443 = 456665) B456665
theorem B304519 : Blo 303832 304519 := bstep (se 1 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 304519 = 456779) B456779
theorem B304527 : Blo 303832 304527 := bstep (se 1 (by rfl) ⟨228395, by rfl⟩ : syracuseStep 304527 = 456791) B456791
theorem B304571 : Blo 303832 304571 := bstep (se 1 (by rfl) ⟨228428, by rfl⟩ : syracuseStep 304571 = 456857) B456857
theorem B828929 : Blo 303832 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B304647 : Blo 303832 304647 := bstep (se 1 (by rfl) ⟨228485, by rfl⟩ : syracuseStep 304647 = 456971) B456971
theorem B1156619 : Blo 303832 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B304655 : Blo 303832 304655 := bstep (se 1 (by rfl) ⟨228491, by rfl⟩ : syracuseStep 304655 = 456983) B456983
theorem B1549853 : Blo 303832 1549853 := bstep (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) B581195
theorem B304699 : Blo 303832 304699 := bstep (se 1 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 304699 = 457049) B457049
theorem B304775 : Blo 303832 304775 := bstep (se 1 (by rfl) ⟨228581, by rfl⟩ : syracuseStep 304775 = 457163) B457163
theorem B304783 : Blo 303832 304783 := bstep (se 1 (by rfl) ⟨228587, by rfl⟩ : syracuseStep 304783 = 457175) B457175
theorem B304827 : Blo 303832 304827 := bstep (se 1 (by rfl) ⟨228620, by rfl⟩ : syracuseStep 304827 = 457241) B457241
theorem B304903 : Blo 303832 304903 := bstep (se 1 (by rfl) ⟨228677, by rfl⟩ : syracuseStep 304903 = 457355) B457355
theorem B304911 : Blo 303832 304911 := bstep (se 1 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 304911 = 457367) B457367
theorem B5547827 : Blo 303832 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B304955 : Blo 303832 304955 := bstep (se 1 (by rfl) ⟨228716, by rfl⟩ : syracuseStep 304955 = 457433) B457433
theorem B305031 : Blo 303832 305031 := bstep (se 1 (by rfl) ⟨228773, by rfl⟩ : syracuseStep 305031 = 457547) B457547
theorem B305039 : Blo 303832 305039 := bstep (se 1 (by rfl) ⟨228779, by rfl⟩ : syracuseStep 305039 = 457559) B457559
theorem B1025945 : Blo 303832 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B894905 : Blo 303832 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B305083 : Blo 303832 305083 := bstep (se 1 (by rfl) ⟨228812, by rfl⟩ : syracuseStep 305083 = 457625) B457625
theorem B1550339 : Blo 303832 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B305159 : Blo 303832 305159 := bstep (se 1 (by rfl) ⟨228869, by rfl⟩ : syracuseStep 305159 = 457739) B457739
theorem B305167 : Blo 303832 305167 := bstep (se 1 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 305167 = 457751) B457751
theorem B305211 : Blo 303832 305211 := bstep (se 1 (by rfl) ⟨228908, by rfl⟩ : syracuseStep 305211 = 457817) B457817
theorem B305287 : Blo 303832 305287 := bstep (se 1 (by rfl) ⟨228965, by rfl⟩ : syracuseStep 305287 = 457931) B457931
theorem B305295 : Blo 303832 305295 := bstep (se 1 (by rfl) ⟨228971, by rfl⟩ : syracuseStep 305295 = 457943) B457943
theorem B305339 : Blo 303832 305339 := bstep (se 1 (by rfl) ⟨229004, by rfl⟩ : syracuseStep 305339 = 458009) B458009
theorem B305415 : Blo 303832 305415 := bstep (se 1 (by rfl) ⟨229061, by rfl⟩ : syracuseStep 305415 = 458123) B458123
theorem B305423 : Blo 303832 305423 := bstep (se 1 (by rfl) ⟨229067, by rfl⟩ : syracuseStep 305423 = 458135) B458135
theorem B305467 : Blo 303832 305467 := bstep (se 1 (by rfl) ⟨229100, by rfl⟩ : syracuseStep 305467 = 458201) B458201
theorem B305543 : Blo 303832 305543 := bstep (se 1 (by rfl) ⟨229157, by rfl⟩ : syracuseStep 305543 = 458315) B458315
theorem B305551 : Blo 303832 305551 := bstep (se 1 (by rfl) ⟨229163, by rfl⟩ : syracuseStep 305551 = 458327) B458327
theorem B1157561 : Blo 303832 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B305595 : Blo 303832 305595 := bstep (se 1 (by rfl) ⟨229196, by rfl⟩ : syracuseStep 305595 = 458393) B458393
theorem B305671 : Blo 303832 305671 := bstep (se 1 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 305671 = 458507) B458507
theorem B305679 : Blo 303832 305679 := bstep (se 1 (by rfl) ⟨229259, by rfl⟩ : syracuseStep 305679 = 458519) B458519
theorem B305723 : Blo 303832 305723 := bstep (se 1 (by rfl) ⟨229292, by rfl⟩ : syracuseStep 305723 = 458585) B458585
theorem B1026647 : Blo 303832 1026647 := bstep (se 1 (by rfl) ⟨769985, by rfl⟩ : syracuseStep 1026647 = 1539971) B1539971
theorem B305799 : Blo 303832 305799 := bstep (se 1 (by rfl) ⟨229349, by rfl⟩ : syracuseStep 305799 = 458699) B458699
theorem B305807 : Blo 303832 305807 := bstep (se 1 (by rfl) ⟨229355, by rfl⟩ : syracuseStep 305807 = 458711) B458711
theorem B305851 : Blo 303832 305851 := bstep (se 1 (by rfl) ⟨229388, by rfl⟩ : syracuseStep 305851 = 458777) B458777
theorem B305927 : Blo 303832 305927 := bstep (se 1 (by rfl) ⟨229445, by rfl⟩ : syracuseStep 305927 = 458891) B458891
theorem B305935 : Blo 303832 305935 := bstep (se 1 (by rfl) ⟨229451, by rfl⟩ : syracuseStep 305935 = 458903) B458903
theorem B305979 : Blo 303832 305979 := bstep (se 1 (by rfl) ⟨229484, by rfl⟩ : syracuseStep 305979 = 458969) B458969
theorem B306055 : Blo 303832 306055 := bstep (se 1 (by rfl) ⟨229541, by rfl⟩ : syracuseStep 306055 = 459083) B459083
theorem B306063 : Blo 303832 306063 := bstep (se 1 (by rfl) ⟨229547, by rfl⟩ : syracuseStep 306063 = 459095) B459095
theorem B306107 : Blo 303832 306107 := bstep (se 1 (by rfl) ⟨229580, by rfl⟩ : syracuseStep 306107 = 459161) B459161
theorem B3484619 : Blo 303832 3484619 := bstep (se 1 (by rfl) ⟨2613464, by rfl⟩ : syracuseStep 3484619 = 5226929) B5226929
theorem B830465 : Blo 303832 830465 := bstep (se 2 (by rfl) ⟨311424, by rfl⟩ : syracuseStep 830465 = 622849) B622849
theorem B306183 : Blo 303832 306183 := bstep (se 1 (by rfl) ⟨229637, by rfl⟩ : syracuseStep 306183 = 459275) B459275
theorem B306191 : Blo 303832 306191 := bstep (se 1 (by rfl) ⟨229643, by rfl⟩ : syracuseStep 306191 = 459287) B459287
theorem B306235 : Blo 303832 306235 := bstep (se 1 (by rfl) ⟨229676, by rfl⟩ : syracuseStep 306235 = 459353) B459353
theorem B1027133 : Blo 303832 1027133 := bstep (se 3 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 1027133 = 385175) B385175
theorem B306311 : Blo 303832 306311 := bstep (se 1 (by rfl) ⟨229733, by rfl⟩ : syracuseStep 306311 = 459467) B459467
theorem B306319 : Blo 303832 306319 := bstep (se 1 (by rfl) ⟨229739, by rfl⟩ : syracuseStep 306319 = 459479) B459479
theorem B928921 : Blo 303832 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B306363 : Blo 303832 306363 := bstep (se 1 (by rfl) ⟨229772, by rfl⟩ : syracuseStep 306363 = 459545) B459545
theorem B306439 : Blo 303832 306439 := bstep (se 1 (by rfl) ⟨229829, by rfl⟩ : syracuseStep 306439 = 459659) B459659
theorem B306447 : Blo 303832 306447 := bstep (se 1 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 306447 = 459671) B459671
theorem B306491 : Blo 303832 306491 := bstep (se 1 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 306491 = 459737) B459737
theorem B306567 : Blo 303832 306567 := bstep (se 1 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 306567 = 459851) B459851
theorem B306575 : Blo 303832 306575 := bstep (se 1 (by rfl) ⟨229931, by rfl⟩ : syracuseStep 306575 = 459863) B459863
theorem B306619 : Blo 303832 306619 := bstep (se 1 (by rfl) ⟨229964, by rfl⟩ : syracuseStep 306619 = 459929) B459929
theorem B306695 : Blo 303832 306695 := bstep (se 1 (by rfl) ⟨230021, by rfl⟩ : syracuseStep 306695 = 460043) B460043
theorem B306703 : Blo 303832 306703 := bstep (se 1 (by rfl) ⟨230027, by rfl⟩ : syracuseStep 306703 = 460055) B460055
theorem B306747 : Blo 303832 306747 := bstep (se 1 (by rfl) ⟨230060, by rfl⟩ : syracuseStep 306747 = 460121) B460121
theorem B437833 : Blo 303832 437833 := bstep (se 2 (by rfl) ⟨164187, by rfl⟩ : syracuseStep 437833 = 328375) B328375
theorem B1551959 : Blo 303832 1551959 := bstep (se 1 (by rfl) ⟨1163969, by rfl⟩ : syracuseStep 1551959 = 2327939) B2327939
theorem B306823 : Blo 303832 306823 := bstep (se 1 (by rfl) ⟨230117, by rfl⟩ : syracuseStep 306823 = 460235) B460235
theorem B306831 : Blo 303832 306831 := bstep (se 1 (by rfl) ⟨230123, by rfl⟩ : syracuseStep 306831 = 460247) B460247
theorem B306875 : Blo 303832 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B306951 : Blo 303832 306951 := bstep (se 1 (by rfl) ⟨230213, by rfl⟩ : syracuseStep 306951 = 460427) B460427
theorem B306959 : Blo 303832 306959 := bstep (se 1 (by rfl) ⟨230219, by rfl⟩ : syracuseStep 306959 = 460439) B460439
theorem B307003 : Blo 303832 307003 := bstep (se 1 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 307003 = 460505) B460505
theorem B1650547 : Blo 303832 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B307079 : Blo 303832 307079 := bstep (se 1 (by rfl) ⟨230309, by rfl⟩ : syracuseStep 307079 = 460619) B460619
theorem B307087 : Blo 303832 307087 := bstep (se 1 (by rfl) ⟨230315, by rfl⟩ : syracuseStep 307087 = 460631) B460631
theorem B307131 : Blo 303832 307131 := bstep (se 1 (by rfl) ⟨230348, by rfl⟩ : syracuseStep 307131 = 460697) B460697
theorem B307207 : Blo 303832 307207 := bstep (se 1 (by rfl) ⟨230405, by rfl⟩ : syracuseStep 307207 = 460811) B460811
theorem B634895 : Blo 303832 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B307215 : Blo 303832 307215 := bstep (se 1 (by rfl) ⟨230411, by rfl⟩ : syracuseStep 307215 = 460823) B460823
theorem B307259 : Blo 303832 307259 := bstep (se 1 (by rfl) ⟨230444, by rfl⟩ : syracuseStep 307259 = 460889) B460889
theorem B1552445 : Blo 303832 1552445 := bstep (se 3 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 1552445 = 582167) B582167
theorem B1749053 : Blo 303832 1749053 := bstep (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) B655895
theorem B307335 : Blo 303832 307335 := bstep (se 1 (by rfl) ⟨230501, by rfl⟩ : syracuseStep 307335 = 461003) B461003
theorem B307343 : Blo 303832 307343 := bstep (se 1 (by rfl) ⟨230507, by rfl⟩ : syracuseStep 307343 = 461015) B461015
theorem B307387 : Blo 303832 307387 := bstep (se 1 (by rfl) ⟨230540, by rfl⟩ : syracuseStep 307387 = 461081) B461081
theorem B307463 : Blo 303832 307463 := bstep (se 1 (by rfl) ⟨230597, by rfl⟩ : syracuseStep 307463 = 461195) B461195
theorem B307471 : Blo 303832 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B307515 : Blo 303832 307515 := bstep (se 1 (by rfl) ⟨230636, by rfl⟩ : syracuseStep 307515 = 461273) B461273
theorem B307591 : Blo 303832 307591 := bstep (se 1 (by rfl) ⟨230693, by rfl⟩ : syracuseStep 307591 = 461387) B461387
theorem B307599 : Blo 303832 307599 := bstep (se 1 (by rfl) ⟨230699, by rfl⟩ : syracuseStep 307599 = 461399) B461399
theorem B1028537 : Blo 303832 1028537 := bstep (se 2 (by rfl) ⟨385701, by rfl⟩ : syracuseStep 1028537 = 771403) B771403
theorem B307643 : Blo 303832 307643 := bstep (se 1 (by rfl) ⟨230732, by rfl⟩ : syracuseStep 307643 = 461465) B461465
theorem B307719 : Blo 303832 307719 := bstep (se 1 (by rfl) ⟨230789, by rfl⟩ : syracuseStep 307719 = 461579) B461579
theorem B307727 : Blo 303832 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B307771 : Blo 303832 307771 := bstep (se 1 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 307771 = 461657) B461657
theorem B1749761 : Blo 303832 1749761 := bstep (se 2 (by rfl) ⟨656160, by rfl⟩ : syracuseStep 1749761 = 1312321) B1312321
theorem B1029131 : Blo 303832 1029131 := bstep (se 1 (by rfl) ⟨771848, by rfl⟩ : syracuseStep 1029131 = 1543697) B1543697
theorem B1160203 : Blo 303832 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B2208779 : Blo 303832 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B865313 : Blo 303832 865313 := bstep (se 2 (by rfl) ⟨324492, by rfl⟩ : syracuseStep 865313 = 648985) B648985
theorem B1029239 : Blo 303832 1029239 := bstep (se 1 (by rfl) ⟨771929, by rfl⟩ : syracuseStep 1029239 = 1543859) B1543859
theorem B1946825 : Blo 303832 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B1160507 : Blo 303832 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B734807 : Blo 303832 734807 := bstep (se 1 (by rfl) ⟨551105, by rfl⟩ : syracuseStep 734807 = 1102211) B1102211
theorem B1029833 : Blo 303832 1029833 := bstep (se 2 (by rfl) ⟨386187, by rfl⟩ : syracuseStep 1029833 = 772375) B772375
theorem B1160993 : Blo 303832 1160993 := bstep (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) B870745
theorem B1554227 : Blo 303832 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B931769 : Blo 303832 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B866315 : Blo 303832 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B342031 : Blo 303832 342031 := bstep (se 1 (by rfl) ⟨256523, by rfl⟩ : syracuseStep 342031 = 513047) B513047
theorem B1325117 : Blo 303832 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B1554551 : Blo 303832 1554551 := bstep (se 1 (by rfl) ⟨1165913, by rfl⟩ : syracuseStep 1554551 = 2331827) B2331827
theorem B1030535 : Blo 303832 1030535 := bstep (se 1 (by rfl) ⟨772901, by rfl⟩ : syracuseStep 1030535 = 1545803) B1545803
theorem B2308499 : Blo 303832 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B866713 : Blo 303832 866713 := bstep (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) B650035
theorem B342535 : Blo 303832 342535 := bstep (se 1 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 342535 = 513803) B513803
theorem B703019 : Blo 303832 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B866963 : Blo 303832 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B342715 : Blo 303832 342715 := bstep (se 1 (by rfl) ⟨257036, by rfl⟩ : syracuseStep 342715 = 514073) B514073
theorem B1161965 : Blo 303832 1161965 := bstep (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) B435737
theorem B1030913 : Blo 303832 1030913 := bstep (se 2 (by rfl) ⟨386592, by rfl⟩ : syracuseStep 1030913 = 773185) B773185
theorem B1555523 : Blo 303832 1555523 := bstep (se 1 (by rfl) ⟨1166642, by rfl⟩ : syracuseStep 1555523 = 2333285) B2333285
theorem B1752151 : Blo 303832 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B343183 : Blo 303832 343183 := bstep (se 1 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 343183 = 514775) B514775
theorem B1555847 : Blo 303832 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B2473361 : Blo 303832 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B736769 : Blo 303832 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B1031723 : Blo 303832 1031723 := bstep (se 1 (by rfl) ⟨773792, by rfl⟩ : syracuseStep 1031723 = 1547585) B1547585
theorem B867955 : Blo 303832 867955 := bstep (se 1 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 867955 = 1301933) B1301933
theorem B343687 : Blo 303832 343687 := bstep (se 1 (by rfl) ⟨257765, by rfl⟩ : syracuseStep 343687 = 515531) B515531
theorem B343867 : Blo 303832 343867 := bstep (se 1 (by rfl) ⟨257900, by rfl⟩ : syracuseStep 343867 = 515801) B515801
theorem B769945 : Blo 303832 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B770107 : Blo 303832 770107 := bstep (se 1 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 770107 = 1155161) B1155161
theorem B5914741 : Blo 303832 5914741 := bstep (se 5 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 5914741 = 554507) B554507
theorem B770249 : Blo 303832 770249 := bstep (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) B577687
theorem B344335 : Blo 303832 344335 := bstep (se 1 (by rfl) ⟨258251, by rfl⟩ : syracuseStep 344335 = 516503) B516503
theorem B770593 : Blo 303832 770593 := bstep (se 2 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 770593 = 577945) B577945
theorem B5653111 : Blo 303832 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B344839 : Blo 303832 344839 := bstep (se 1 (by rfl) ⟨258629, by rfl⟩ : syracuseStep 344839 = 517259) B517259
theorem B1033019 : Blo 303832 1033019 := bstep (se 1 (by rfl) ⟨774764, by rfl⟩ : syracuseStep 1033019 = 1549529) B1549529
theorem B1164091 : Blo 303832 1164091 := bstep (se 1 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 1164091 = 1746137) B1746137
theorem B2212697 : Blo 303832 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B2802521 : Blo 303832 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1196947 : Blo 303832 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B2933657 : Blo 303832 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B345019 : Blo 303832 345019 := bstep (se 1 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 345019 = 517529) B517529
theorem B2475019 : Blo 303832 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B771191 : Blo 303832 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B869561 : Blo 303832 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B1656065 : Blo 303832 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B738575 : Blo 303832 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B1033505 : Blo 303832 1033505 := bstep (se 2 (by rfl) ⟨387564, by rfl⟩ : syracuseStep 1033505 = 775129) B775129
theorem B1164577 : Blo 303832 1164577 := bstep (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) B873433
theorem B5850467 : Blo 303832 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B345487 : Blo 303832 345487 := bstep (se 1 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 345487 = 518231) B518231
theorem B869903 : Blo 303832 869903 := bstep (se 1 (by rfl) ⟨652427, by rfl⟩ : syracuseStep 869903 = 1304855) B1304855
theorem B1034099 : Blo 303832 1034099 := bstep (se 1 (by rfl) ⟨775574, by rfl⟩ : syracuseStep 1034099 = 1551149) B1551149
theorem B345991 : Blo 303832 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B1001501 : Blo 303832 1001501 := bstep (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) B375563
theorem B346171 : Blo 303832 346171 := bstep (se 1 (by rfl) ⟨259628, by rfl⟩ : syracuseStep 346171 = 519257) B519257
theorem B1165549 : Blo 303832 1165549 := bstep (se 3 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 1165549 = 437081) B437081
theorem B870689 : Blo 303832 870689 := bstep (se 2 (by rfl) ⟨326508, by rfl⟩ : syracuseStep 870689 = 653017) B653017
theorem B772487 : Blo 303832 772487 := bstep (se 1 (by rfl) ⟨579365, by rfl⟩ : syracuseStep 772487 = 1158731) B1158731
theorem B772537 : Blo 303832 772537 := bstep (se 2 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 772537 = 579403) B579403
theorem B1165853 : Blo 303832 1165853 := bstep (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) B437195
theorem B412303 : Blo 303832 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B2116367 : Blo 303832 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B773135 : Blo 303832 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B412745 : Blo 303832 412745 := bstep (se 2 (by rfl) ⟨154779, by rfl⟩ : syracuseStep 412745 = 309559) B309559
theorem B2969041 : Blo 303832 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B1953233 : Blo 303832 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B577057 : Blo 303832 577057 := bstep (se 2 (by rfl) ⟨216396, by rfl⟩ : syracuseStep 577057 = 432793) B432793
theorem B773833 : Blo 303832 773833 := bstep (se 2 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 773833 = 580375) B580375
theorem B872203 : Blo 303832 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B2772751 : Blo 303832 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B413497 : Blo 303832 413497 := bstep (se 2 (by rfl) ⟨155061, by rfl⟩ : syracuseStep 413497 = 310123) B310123
theorem B773975 : Blo 303832 773975 := bstep (se 1 (by rfl) ⟨580481, by rfl⟩ : syracuseStep 773975 = 1160963) B1160963
theorem B413687 : Blo 303832 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B872477 : Blo 303832 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B13455395 : Blo 303832 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B1167479 : Blo 303832 1167479 := bstep (se 1 (by rfl) ⟨875609, by rfl⟩ : syracuseStep 1167479 = 1751219) B1751219
theorem B2216069 : Blo 303832 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B872819 : Blo 303832 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B1036691 : Blo 303832 1036691 := bstep (se 1 (by rfl) ⟨777518, by rfl⟩ : syracuseStep 1036691 = 1555037) B1555037
theorem B578249 : Blo 303832 578249 := bstep (se 2 (by rfl) ⟨216843, by rfl⟩ : syracuseStep 578249 = 433687) B433687
theorem B1299215 : Blo 303832 1299215 := bstep (se 1 (by rfl) ⟨974411, by rfl⟩ : syracuseStep 1299215 = 1948823) B1948823
theorem B414649 : Blo 303832 414649 := bstep (se 2 (by rfl) ⟨155493, by rfl⟩ : syracuseStep 414649 = 310987) B310987
theorem B513067 : Blo 303832 513067 := bstep (se 1 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 513067 = 769601) B769601
theorem B1299523 : Blo 303832 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B1168451 : Blo 303832 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B513209 : Blo 303832 513209 := bstep (se 2 (by rfl) ⟨192453, by rfl⟩ : syracuseStep 513209 = 384907) B384907
theorem B873787 : Blo 303832 873787 := bstep (se 1 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 873787 = 1310681) B1310681
theorem B578963 : Blo 303832 578963 := bstep (se 1 (by rfl) ⟨434222, by rfl⟩ : syracuseStep 578963 = 868445) B868445
theorem B579001 : Blo 303832 579001 := bstep (se 2 (by rfl) ⟨217125, by rfl⟩ : syracuseStep 579001 = 434251) B434251
theorem B2610731 : Blo 303832 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B2840183 : Blo 303832 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B2971313 : Blo 303832 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1038095 : Blo 303832 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B776051 : Blo 303832 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B513911 : Blo 303832 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B415751 : Blo 303832 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B1038365 : Blo 303832 1038365 := bstep (se 3 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 1038365 = 389387) B389387
theorem B1497149 : Blo 303832 1497149 := bstep (se 3 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 1497149 = 561431) B561431
theorem B514363 : Blo 303832 514363 := bstep (se 1 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 514363 = 771545) B771545
theorem B776567 : Blo 303832 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B874937 : Blo 303832 874937 := bstep (se 2 (by rfl) ⟨328101, by rfl⟩ : syracuseStep 874937 = 656203) B656203
theorem B514505 : Blo 303832 514505 := bstep (se 2 (by rfl) ⟨192939, by rfl⟩ : syracuseStep 514505 = 385879) B385879
theorem B875279 : Blo 303832 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B973721 : Blo 303832 973721 := bstep (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) B730291
theorem B515207 : Blo 303832 515207 := bstep (se 1 (by rfl) ⟨386405, by rfl⟩ : syracuseStep 515207 = 772811) B772811
theorem B580907 : Blo 303832 580907 := bstep (se 1 (by rfl) ⟨435680, by rfl⟩ : syracuseStep 580907 = 871361) B871361
theorem B941399 : Blo 303832 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B777559 : Blo 303832 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B3333469 : Blo 303832 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B1105267 : Blo 303832 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B777863 : Blo 303832 777863 := bstep (se 1 (by rfl) ⟨583397, by rfl⟩ : syracuseStep 777863 = 1166795) B1166795
theorem B876167 : Blo 303832 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B777995 : Blo 303832 777995 := bstep (se 1 (by rfl) ⟨583496, by rfl⟩ : syracuseStep 777995 = 1166993) B1166993
theorem B515855 : Blo 303832 515855 := bstep (se 1 (by rfl) ⟨386891, by rfl⟩ : syracuseStep 515855 = 773783) B773783
theorem B548641 : Blo 303832 548641 := bstep (se 2 (by rfl) ⟨205740, by rfl⟩ : syracuseStep 548641 = 411481) B411481
theorem B876349 : Blo 303832 876349 := bstep (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) B328631
theorem B876577 : Blo 303832 876577 := bstep (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) B657433
theorem B581833 : Blo 303832 581833 := bstep (se 2 (by rfl) ⟨218187, by rfl⟩ : syracuseStep 581833 = 436375) B436375
theorem B778511 : Blo 303832 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B516395 : Blo 303832 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B14836061 : Blo 303832 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B778643 : Blo 303832 778643 := bstep (se 1 (by rfl) ⟨583982, by rfl⟩ : syracuseStep 778643 = 1167965) B1167965
theorem B2089475 : Blo 303832 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B877085 : Blo 303832 877085 := bstep (se 3 (by rfl) ⟨164453, by rfl⟩ : syracuseStep 877085 = 328907) B328907
theorem B1466923 : Blo 303832 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B1466999 : Blo 303832 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B516793 : Blo 303832 516793 := bstep (se 2 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 516793 = 387595) B387595
theorem B582547 : Blo 303832 582547 := bstep (se 1 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 582547 = 873821) B873821
theorem B1237945 : Blo 303832 1237945 := bstep (se 2 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 1237945 = 928459) B928459
theorem B4482053 : Blo 303832 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B1664023 : Blo 303832 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B1238287 : Blo 303832 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B517495 : Blo 303832 517495 := bstep (se 1 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 517495 = 776243) B776243
theorem B517691 : Blo 303832 517691 := bstep (se 1 (by rfl) ⟨388268, by rfl⟩ : syracuseStep 517691 = 776537) B776537
theorem B419627 : Blo 303832 419627 := bstep (se 1 (by rfl) ⟨314720, by rfl⟩ : syracuseStep 419627 = 629441) B629441
theorem B3467123 : Blo 303832 3467123 := bstep (se 1 (by rfl) ⟨2600342, by rfl⟩ : syracuseStep 3467123 = 5200685) B5200685
theorem B550775 : Blo 303832 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B518089 : Blo 303832 518089 := bstep (se 2 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 518089 = 388567) B388567
theorem B583625 : Blo 303832 583625 := bstep (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) B437719
theorem B1959947 : Blo 303832 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B1959997 : Blo 303832 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B649505 : Blo 303832 649505 := bstep (se 2 (by rfl) ⟨243564, by rfl⟩ : syracuseStep 649505 = 487129) B487129
theorem B3303827 : Blo 303832 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B387499 : Blo 303832 387499 := bstep (se 1 (by rfl) ⟨290624, by rfl⟩ : syracuseStep 387499 = 581249) B581249
theorem B518791 : Blo 303832 518791 := bstep (se 1 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 518791 = 778187) B778187
theorem B3893953 : Blo 303832 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B3697483 : Blo 303832 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B5565347 : Blo 303832 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B650359 : Blo 303832 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B519439 : Blo 303832 519439 := bstep (se 1 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 519439 = 779159) B779159
theorem B388471 : Blo 303832 388471 := bstep (se 1 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 388471 = 582707) B582707
theorem B781883 : Blo 303832 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B683639 : Blo 303832 683639 := bstep (se 1 (by rfl) ⟨512729, by rfl⟩ : syracuseStep 683639 = 1025459) B1025459
theorem B1568375 : Blo 303832 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B388795 : Blo 303832 388795 := bstep (se 1 (by rfl) ⟨291596, by rfl⟩ : syracuseStep 388795 = 583193) B583193
theorem B683819 : Blo 303832 683819 := bstep (se 1 (by rfl) ⟨512864, by rfl⟩ : syracuseStep 683819 = 1025729) B1025729
theorem B2945069 : Blo 303832 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B487559 : Blo 303832 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B684179 : Blo 303832 684179 := bstep (se 1 (by rfl) ⟨513134, by rfl⟩ : syracuseStep 684179 = 1026269) B1026269
theorem B684233 : Blo 303832 684233 := bstep (se 2 (by rfl) ⟨256587, by rfl⟩ : syracuseStep 684233 = 513175) B513175
theorem B684935 : Blo 303832 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B521095 : Blo 303832 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B979897 : Blo 303832 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B1471441 : Blo 303832 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B2946071 : Blo 303832 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B324667 : Blo 303832 324667 := bstep (se 1 (by rfl) ⟨243500, by rfl⟩ : syracuseStep 324667 = 487001) B487001
theorem B685115 : Blo 303832 685115 := bstep (se 1 (by rfl) ⟨513836, by rfl⟩ : syracuseStep 685115 = 1027673) B1027673
theorem B455753 : Blo 303832 455753 := bstep (se 2 (by rfl) ⟨170907, by rfl⟩ : syracuseStep 455753 = 341815) B341815
theorem B685241 : Blo 303832 685241 := bstep (se 2 (by rfl) ⟨256965, by rfl⟩ : syracuseStep 685241 = 513931) B513931
theorem B455867 : Blo 303832 455867 := bstep (se 1 (by rfl) ⟨341900, by rfl⟩ : syracuseStep 455867 = 683801) B683801
theorem B455927 : Blo 303832 455927 := bstep (se 1 (by rfl) ⟨341945, by rfl⟩ : syracuseStep 455927 = 683891) B683891
theorem B455951 : Blo 303832 455951 := bstep (se 1 (by rfl) ⟨341963, by rfl⟩ : syracuseStep 455951 = 683927) B683927
theorem B455993 : Blo 303832 455993 := bstep (se 2 (by rfl) ⟨170997, by rfl⟩ : syracuseStep 455993 = 341995) B341995
theorem B1307963 : Blo 303832 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B456071 : Blo 303832 456071 := bstep (se 1 (by rfl) ⟨342053, by rfl⟩ : syracuseStep 456071 = 684107) B684107
theorem B456107 : Blo 303832 456107 := bstep (se 1 (by rfl) ⟨342080, by rfl⟩ : syracuseStep 456107 = 684161) B684161
theorem B456137 : Blo 303832 456137 := bstep (se 2 (by rfl) ⟨171051, by rfl⟩ : syracuseStep 456137 = 342103) B342103
theorem B1734155 : Blo 303832 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B685583 : Blo 303832 685583 := bstep (se 1 (by rfl) ⟨514187, by rfl⟩ : syracuseStep 685583 = 1028375) B1028375
theorem B685601 : Blo 303832 685601 := bstep (se 2 (by rfl) ⟨257100, by rfl⟩ : syracuseStep 685601 = 514201) B514201
theorem B456251 : Blo 303832 456251 := bstep (se 1 (by rfl) ⟨342188, by rfl⟩ : syracuseStep 456251 = 684377) B684377
theorem B1308221 : Blo 303832 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B456311 : Blo 303832 456311 := bstep (se 1 (by rfl) ⟨342233, by rfl⟩ : syracuseStep 456311 = 684467) B684467
theorem B456335 : Blo 303832 456335 := bstep (se 1 (by rfl) ⟨342251, by rfl⟩ : syracuseStep 456335 = 684503) B684503
theorem B456377 : Blo 303832 456377 := bstep (se 2 (by rfl) ⟨171141, by rfl⟩ : syracuseStep 456377 = 342283) B342283
theorem B456455 : Blo 303832 456455 := bstep (se 1 (by rfl) ⟨342341, by rfl⟩ : syracuseStep 456455 = 684683) B684683
theorem B456491 : Blo 303832 456491 := bstep (se 1 (by rfl) ⟨342368, by rfl⟩ : syracuseStep 456491 = 684737) B684737
theorem B390955 : Blo 303832 390955 := bstep (se 1 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 390955 = 586433) B586433
theorem B456521 : Blo 303832 456521 := bstep (se 2 (by rfl) ⟨171195, by rfl⟩ : syracuseStep 456521 = 342391) B342391
theorem B685943 : Blo 303832 685943 := bstep (se 1 (by rfl) ⟨514457, by rfl⟩ : syracuseStep 685943 = 1028915) B1028915
theorem B456635 : Blo 303832 456635 := bstep (se 1 (by rfl) ⟨342476, by rfl⟩ : syracuseStep 456635 = 684953) B684953
theorem B456695 : Blo 303832 456695 := bstep (se 1 (by rfl) ⟨342521, by rfl⟩ : syracuseStep 456695 = 685043) B685043
theorem B456719 : Blo 303832 456719 := bstep (se 1 (by rfl) ⟨342539, by rfl⟩ : syracuseStep 456719 = 685079) B685079
theorem B1112093 : Blo 303832 1112093 := bstep (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) B417035
theorem B1046557 : Blo 303832 1046557 := bstep (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) B392459
theorem B686123 : Blo 303832 686123 := bstep (se 1 (by rfl) ⟨514592, by rfl⟩ : syracuseStep 686123 = 1029185) B1029185
theorem B456761 : Blo 303832 456761 := bstep (se 2 (by rfl) ⟨171285, by rfl⟩ : syracuseStep 456761 = 342571) B342571
theorem B2619479 : Blo 303832 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B456839 : Blo 303832 456839 := bstep (se 1 (by rfl) ⟨342629, by rfl⟩ : syracuseStep 456839 = 685259) B685259
theorem B587911 : Blo 303832 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B456875 : Blo 303832 456875 := bstep (se 1 (by rfl) ⟨342656, by rfl⟩ : syracuseStep 456875 = 685313) B685313
theorem B456905 : Blo 303832 456905 := bstep (se 2 (by rfl) ⟨171339, by rfl⟩ : syracuseStep 456905 = 342679) B342679
theorem B784673 : Blo 303832 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B457019 : Blo 303832 457019 := bstep (se 1 (by rfl) ⟨342764, by rfl⟩ : syracuseStep 457019 = 685529) B685529
theorem B2881885 : Blo 303832 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B457079 : Blo 303832 457079 := bstep (se 1 (by rfl) ⟨342809, by rfl⟩ : syracuseStep 457079 = 685619) B685619
theorem B457103 : Blo 303832 457103 := bstep (se 1 (by rfl) ⟨342827, by rfl⟩ : syracuseStep 457103 = 685655) B685655
theorem B686483 : Blo 303832 686483 := bstep (se 1 (by rfl) ⟨514862, by rfl⟩ : syracuseStep 686483 = 1029725) B1029725
theorem B457145 : Blo 303832 457145 := bstep (se 2 (by rfl) ⟨171429, by rfl⟩ : syracuseStep 457145 = 342859) B342859
theorem B686537 : Blo 303832 686537 := bstep (se 2 (by rfl) ⟨257451, by rfl⟩ : syracuseStep 686537 = 514903) B514903
theorem B1538513 : Blo 303832 1538513 := bstep (se 2 (by rfl) ⟨576942, by rfl⟩ : syracuseStep 1538513 = 1153885) B1153885
theorem B457223 : Blo 303832 457223 := bstep (se 1 (by rfl) ⟨342917, by rfl⟩ : syracuseStep 457223 = 685835) B685835
theorem B457259 : Blo 303832 457259 := bstep (se 1 (by rfl) ⟨342944, by rfl⟩ : syracuseStep 457259 = 685889) B685889
theorem B457289 : Blo 303832 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B785011 : Blo 303832 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B457403 : Blo 303832 457403 := bstep (se 1 (by rfl) ⟨343052, by rfl⟩ : syracuseStep 457403 = 686105) B686105
theorem B457463 : Blo 303832 457463 := bstep (se 1 (by rfl) ⟨343097, by rfl⟩ : syracuseStep 457463 = 686195) B686195
theorem B457487 : Blo 303832 457487 := bstep (se 1 (by rfl) ⟨343115, by rfl⟩ : syracuseStep 457487 = 686231) B686231
theorem B457529 : Blo 303832 457529 := bstep (se 2 (by rfl) ⟨171573, by rfl⟩ : syracuseStep 457529 = 343147) B343147
theorem B3308363 : Blo 303832 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B457607 : Blo 303832 457607 := bstep (se 1 (by rfl) ⟨343205, by rfl⟩ : syracuseStep 457607 = 686411) B686411
theorem B981895 : Blo 303832 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B457643 : Blo 303832 457643 := bstep (se 1 (by rfl) ⟨343232, by rfl⟩ : syracuseStep 457643 = 686465) B686465
theorem B457673 : Blo 303832 457673 := bstep (se 2 (by rfl) ⟨171627, by rfl⟩ : syracuseStep 457673 = 343255) B343255
theorem B457787 : Blo 303832 457787 := bstep (se 1 (by rfl) ⟨343340, by rfl⟩ : syracuseStep 457787 = 686681) B686681
theorem B457847 : Blo 303832 457847 := bstep (se 1 (by rfl) ⟨343385, by rfl⟩ : syracuseStep 457847 = 686771) B686771
theorem B687239 : Blo 303832 687239 := bstep (se 1 (by rfl) ⟨515429, by rfl⟩ : syracuseStep 687239 = 1030859) B1030859
theorem B785543 : Blo 303832 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B457871 : Blo 303832 457871 := bstep (se 1 (by rfl) ⟨343403, by rfl⟩ : syracuseStep 457871 = 686807) B686807
theorem B457913 : Blo 303832 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B457991 : Blo 303832 457991 := bstep (se 1 (by rfl) ⟨343493, by rfl⟩ : syracuseStep 457991 = 686987) B686987
theorem B458027 : Blo 303832 458027 := bstep (se 1 (by rfl) ⟨343520, by rfl⟩ : syracuseStep 458027 = 687041) B687041
theorem B687419 : Blo 303832 687419 := bstep (se 1 (by rfl) ⟨515564, by rfl⟩ : syracuseStep 687419 = 1031129) B1031129
theorem B458057 : Blo 303832 458057 := bstep (se 2 (by rfl) ⟨171771, by rfl⟩ : syracuseStep 458057 = 343543) B343543
theorem B687545 : Blo 303832 687545 := bstep (se 2 (by rfl) ⟨257829, by rfl⟩ : syracuseStep 687545 = 515659) B515659
theorem B458171 : Blo 303832 458171 := bstep (se 1 (by rfl) ⟨343628, by rfl⟩ : syracuseStep 458171 = 687257) B687257
theorem B458231 : Blo 303832 458231 := bstep (se 1 (by rfl) ⟨343673, by rfl⟩ : syracuseStep 458231 = 687347) B687347
theorem B1310219 : Blo 303832 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B458255 : Blo 303832 458255 := bstep (se 1 (by rfl) ⟨343691, by rfl⟩ : syracuseStep 458255 = 687383) B687383
theorem B458297 : Blo 303832 458297 := bstep (se 2 (by rfl) ⟨171861, by rfl⟩ : syracuseStep 458297 = 343723) B343723
theorem B458375 : Blo 303832 458375 := bstep (se 1 (by rfl) ⟨343781, by rfl⟩ : syracuseStep 458375 = 687563) B687563
theorem B458411 : Blo 303832 458411 := bstep (se 1 (by rfl) ⟨343808, by rfl⟩ : syracuseStep 458411 = 687617) B687617
theorem B458441 : Blo 303832 458441 := bstep (se 2 (by rfl) ⟨171915, by rfl⟩ : syracuseStep 458441 = 343831) B343831
theorem B589513 : Blo 303832 589513 := bstep (se 2 (by rfl) ⟨221067, by rfl⟩ : syracuseStep 589513 = 442135) B442135
theorem B687887 : Blo 303832 687887 := bstep (se 1 (by rfl) ⟨515915, by rfl⟩ : syracuseStep 687887 = 1031831) B1031831
theorem B687905 : Blo 303832 687905 := bstep (se 2 (by rfl) ⟨257964, by rfl⟩ : syracuseStep 687905 = 515929) B515929
theorem B458555 : Blo 303832 458555 := bstep (se 1 (by rfl) ⟨343916, by rfl⟩ : syracuseStep 458555 = 687833) B687833
theorem B458615 : Blo 303832 458615 := bstep (se 1 (by rfl) ⟨343961, by rfl⟩ : syracuseStep 458615 = 687923) B687923
theorem B458639 : Blo 303832 458639 := bstep (se 1 (by rfl) ⟨343979, by rfl⟩ : syracuseStep 458639 = 687959) B687959
theorem B458681 : Blo 303832 458681 := bstep (se 2 (by rfl) ⟨172005, by rfl⟩ : syracuseStep 458681 = 344011) B344011
theorem B2490425 : Blo 303832 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B458831 : Blo 303832 458831 := bstep (se 1 (by rfl) ⟨344123, by rfl⟩ : syracuseStep 458831 = 688247) B688247
theorem B458951 : Blo 303832 458951 := bstep (se 1 (by rfl) ⟨344213, by rfl⟩ : syracuseStep 458951 = 688427) B688427
theorem B1540457 : Blo 303832 1540457 := bstep (se 2 (by rfl) ⟨577671, by rfl⟩ : syracuseStep 1540457 = 1155343) B1155343
theorem B459113 : Blo 303832 459113 := bstep (se 2 (by rfl) ⟨172167, by rfl⟩ : syracuseStep 459113 = 344335) B344335
theorem B459191 : Blo 303832 459191 := bstep (se 1 (by rfl) ⟨344393, by rfl⟩ : syracuseStep 459191 = 688787) B688787
theorem B393655 : Blo 303832 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B459227 : Blo 303832 459227 := bstep (se 1 (by rfl) ⟨344420, by rfl⟩ : syracuseStep 459227 = 688841) B688841
theorem B688679 : Blo 303832 688679 := bstep (se 1 (by rfl) ⟨516509, by rfl⟩ : syracuseStep 688679 = 1033019) B1033019
theorem B1180345 : Blo 303832 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B7537481 : Blo 303832 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B492383 : Blo 303832 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B689003 : Blo 303832 689003 := bstep (se 1 (by rfl) ⟨516752, by rfl⟩ : syracuseStep 689003 = 1033505) B1033505
theorem B3900311 : Blo 303832 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B689057 : Blo 303832 689057 := bstep (se 2 (by rfl) ⟨258396, by rfl⟩ : syracuseStep 689057 = 516793) B516793
theorem B459695 : Blo 303832 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B1115063 : Blo 303832 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B459785 : Blo 303832 459785 := bstep (se 2 (by rfl) ⟨172419, by rfl⟩ : syracuseStep 459785 = 344839) B344839
theorem B459815 : Blo 303832 459815 := bstep (se 1 (by rfl) ⟨344861, by rfl⟩ : syracuseStep 459815 = 689723) B689723
theorem B459899 : Blo 303832 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B689399 : Blo 303832 689399 := bstep (se 1 (by rfl) ⟨517049, by rfl⟩ : syracuseStep 689399 = 1034099) B1034099
theorem B460025 : Blo 303832 460025 := bstep (se 2 (by rfl) ⟨172509, by rfl⟩ : syracuseStep 460025 = 345019) B345019
theorem B460127 : Blo 303832 460127 := bstep (se 1 (by rfl) ⟨345095, by rfl⟩ : syracuseStep 460127 = 690191) B690191
theorem B460139 : Blo 303832 460139 := bstep (se 1 (by rfl) ⟨345104, by rfl⟩ : syracuseStep 460139 = 690209) B690209
theorem B1181147 : Blo 303832 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B1181243 : Blo 303832 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B460367 : Blo 303832 460367 := bstep (se 1 (by rfl) ⟨345275, by rfl⟩ : syracuseStep 460367 = 690551) B690551
theorem B460487 : Blo 303832 460487 := bstep (se 1 (by rfl) ⟨345365, by rfl⟩ : syracuseStep 460487 = 690731) B690731
theorem B689993 : Blo 303832 689993 := bstep (se 2 (by rfl) ⟨258747, by rfl⟩ : syracuseStep 689993 = 517495) B517495
theorem B1410911 : Blo 303832 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B460649 : Blo 303832 460649 := bstep (se 2 (by rfl) ⟨172743, by rfl⟩ : syracuseStep 460649 = 345487) B345487
theorem B460727 : Blo 303832 460727 := bstep (se 1 (by rfl) ⟨345545, by rfl⟩ : syracuseStep 460727 = 691091) B691091
theorem B460763 : Blo 303832 460763 := bstep (se 1 (by rfl) ⟨345572, by rfl⟩ : syracuseStep 460763 = 691145) B691145
theorem B5900525 : Blo 303832 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B7473389 : Blo 303832 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B461231 : Blo 303832 461231 := bstep (se 1 (by rfl) ⟨345923, by rfl⟩ : syracuseStep 461231 = 691847) B691847
theorem B461321 : Blo 303832 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B789031 : Blo 303832 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B461351 : Blo 303832 461351 := bstep (se 1 (by rfl) ⟨346013, by rfl⟩ : syracuseStep 461351 = 692027) B692027
theorem B690785 : Blo 303832 690785 := bstep (se 2 (by rfl) ⟨259044, by rfl⟩ : syracuseStep 690785 = 518089) B518089
theorem B461435 : Blo 303832 461435 := bstep (se 1 (by rfl) ⟨346076, by rfl⟩ : syracuseStep 461435 = 692153) B692153
theorem B461561 : Blo 303832 461561 := bstep (se 2 (by rfl) ⟨173085, by rfl⟩ : syracuseStep 461561 = 346171) B346171
theorem B1477379 : Blo 303832 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B461663 : Blo 303832 461663 := bstep (se 1 (by rfl) ⟨346247, by rfl⟩ : syracuseStep 461663 = 692495) B692495
theorem B461675 : Blo 303832 461675 := bstep (se 1 (by rfl) ⟨346256, by rfl⟩ : syracuseStep 461675 = 692513) B692513
theorem B691127 : Blo 303832 691127 := bstep (se 1 (by rfl) ⟨518345, by rfl⟩ : syracuseStep 691127 = 1036691) B1036691
theorem B1051663 : Blo 303832 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B7015619 : Blo 303832 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B691721 : Blo 303832 691721 := bstep (se 2 (by rfl) ⟨259395, by rfl⟩ : syracuseStep 691721 = 518791) B518791
theorem B1740487 : Blo 303832 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B692063 : Blo 303832 692063 := bstep (se 1 (by rfl) ⟨519047, by rfl⟩ : syracuseStep 692063 = 1038095) B1038095
theorem B692243 : Blo 303832 692243 := bstep (se 1 (by rfl) ⟨519182, by rfl⟩ : syracuseStep 692243 = 1038365) B1038365
theorem B1970405 : Blo 303832 1970405 := bstep (se 4 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 1970405 = 369451) B369451
theorem B692585 : Blo 303832 692585 := bstep (se 2 (by rfl) ⟨259719, by rfl⟩ : syracuseStep 692585 = 519439) B519439
theorem B1249939 : Blo 303832 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1119005 : Blo 303832 1119005 := bstep (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) B419627
theorem B627599 : Blo 303832 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B1971479 : Blo 303832 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B4200281 : Blo 303832 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B2988035 : Blo 303832 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B3545189 : Blo 303832 3545189 := bstep (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) B664723
theorem B694793 : Blo 303832 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B367183 : Blo 303832 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B596603 : Blo 303832 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B1546937 : Blo 303832 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B2202551 : Blo 303832 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B3710231 : Blo 303832 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B3842513 : Blo 303832 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B1155617 : Blo 303832 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B303835 : Blo 303832 303835 := bstep (se 1 (by rfl) ⟨227876, by rfl⟩ : syracuseStep 303835 = 455753) B455753
theorem B303911 : Blo 303832 303911 := bstep (se 1 (by rfl) ⟨227933, by rfl⟩ : syracuseStep 303911 = 455867) B455867
theorem B303951 : Blo 303832 303951 := bstep (se 1 (by rfl) ⟨227963, by rfl⟩ : syracuseStep 303951 = 455927) B455927
theorem B303967 : Blo 303832 303967 := bstep (se 1 (by rfl) ⟨227975, by rfl⟩ : syracuseStep 303967 = 455951) B455951
theorem B303995 : Blo 303832 303995 := bstep (se 1 (by rfl) ⟨227996, by rfl⟩ : syracuseStep 303995 = 455993) B455993
theorem B304047 : Blo 303832 304047 := bstep (se 1 (by rfl) ⟨228035, by rfl⟩ : syracuseStep 304047 = 456071) B456071
theorem B304071 : Blo 303832 304071 := bstep (se 1 (by rfl) ⟨228053, by rfl⟩ : syracuseStep 304071 = 456107) B456107
theorem B304091 : Blo 303832 304091 := bstep (se 1 (by rfl) ⟨228068, by rfl⟩ : syracuseStep 304091 = 456137) B456137
theorem B1156103 : Blo 303832 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B304167 : Blo 303832 304167 := bstep (se 1 (by rfl) ⟨228125, by rfl⟩ : syracuseStep 304167 = 456251) B456251
theorem B304207 : Blo 303832 304207 := bstep (se 1 (by rfl) ⟨228155, by rfl⟩ : syracuseStep 304207 = 456311) B456311
theorem B304223 : Blo 303832 304223 := bstep (se 1 (by rfl) ⟨228167, by rfl⟩ : syracuseStep 304223 = 456335) B456335
theorem B304251 : Blo 303832 304251 := bstep (se 1 (by rfl) ⟨228188, by rfl⟩ : syracuseStep 304251 = 456377) B456377
theorem B304303 : Blo 303832 304303 := bstep (se 1 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 304303 = 456455) B456455
theorem B304327 : Blo 303832 304327 := bstep (se 1 (by rfl) ⟨228245, by rfl⟩ : syracuseStep 304327 = 456491) B456491
theorem B304347 : Blo 303832 304347 := bstep (se 1 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 304347 = 456521) B456521
theorem B304423 : Blo 303832 304423 := bstep (se 1 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 304423 = 456635) B456635
theorem B304463 : Blo 303832 304463 := bstep (se 1 (by rfl) ⟨228347, by rfl⟩ : syracuseStep 304463 = 456695) B456695
theorem B304479 : Blo 303832 304479 := bstep (se 1 (by rfl) ⟨228359, by rfl⟩ : syracuseStep 304479 = 456719) B456719
theorem B304507 : Blo 303832 304507 := bstep (se 1 (by rfl) ⟨228380, by rfl⟩ : syracuseStep 304507 = 456761) B456761
theorem B1746319 : Blo 303832 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B304559 : Blo 303832 304559 := bstep (se 1 (by rfl) ⟨228419, by rfl⟩ : syracuseStep 304559 = 456839) B456839
theorem B304583 : Blo 303832 304583 := bstep (se 1 (by rfl) ⟨228437, by rfl⟩ : syracuseStep 304583 = 456875) B456875
theorem B2336201 : Blo 303832 2336201 := bstep (se 2 (by rfl) ⟨876075, by rfl⟩ : syracuseStep 2336201 = 1752151) B1752151
theorem B304603 : Blo 303832 304603 := bstep (se 1 (by rfl) ⟨228452, by rfl⟩ : syracuseStep 304603 = 456905) B456905
theorem B1156589 : Blo 303832 1156589 := bstep (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) B433721
theorem B304679 : Blo 303832 304679 := bstep (se 1 (by rfl) ⟨228509, by rfl⟩ : syracuseStep 304679 = 457019) B457019
theorem B304719 : Blo 303832 304719 := bstep (se 1 (by rfl) ⟨228539, by rfl⟩ : syracuseStep 304719 = 457079) B457079
theorem B304735 : Blo 303832 304735 := bstep (se 1 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 304735 = 457103) B457103
theorem B304763 : Blo 303832 304763 := bstep (se 1 (by rfl) ⟨228572, by rfl⟩ : syracuseStep 304763 = 457145) B457145
theorem B1025675 : Blo 303832 1025675 := bstep (se 1 (by rfl) ⟨769256, by rfl⟩ : syracuseStep 1025675 = 1538513) B1538513
theorem B304815 : Blo 303832 304815 := bstep (se 1 (by rfl) ⟨228611, by rfl⟩ : syracuseStep 304815 = 457223) B457223
theorem B468679 : Blo 303832 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B304839 : Blo 303832 304839 := bstep (se 1 (by rfl) ⟨228629, by rfl⟩ : syracuseStep 304839 = 457259) B457259
theorem B35923661 : Blo 303832 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B304859 : Blo 303832 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B304935 : Blo 303832 304935 := bstep (se 1 (by rfl) ⟨228701, by rfl⟩ : syracuseStep 304935 = 457403) B457403
theorem B304975 : Blo 303832 304975 := bstep (se 1 (by rfl) ⟨228731, by rfl⟩ : syracuseStep 304975 = 457463) B457463
theorem B304991 : Blo 303832 304991 := bstep (se 1 (by rfl) ⟨228743, by rfl⟩ : syracuseStep 304991 = 457487) B457487
theorem B305019 : Blo 303832 305019 := bstep (se 1 (by rfl) ⟨228764, by rfl⟩ : syracuseStep 305019 = 457529) B457529
theorem B2205575 : Blo 303832 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B305071 : Blo 303832 305071 := bstep (se 1 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 305071 = 457607) B457607
theorem B305095 : Blo 303832 305095 := bstep (se 1 (by rfl) ⟨228821, by rfl⟩ : syracuseStep 305095 = 457643) B457643
theorem B305115 : Blo 303832 305115 := bstep (se 1 (by rfl) ⟨228836, by rfl⟩ : syracuseStep 305115 = 457673) B457673
theorem B305191 : Blo 303832 305191 := bstep (se 1 (by rfl) ⟨228893, by rfl⟩ : syracuseStep 305191 = 457787) B457787
theorem B305231 : Blo 303832 305231 := bstep (se 1 (by rfl) ⟨228923, by rfl⟩ : syracuseStep 305231 = 457847) B457847
theorem B305247 : Blo 303832 305247 := bstep (se 1 (by rfl) ⟨228935, by rfl⟩ : syracuseStep 305247 = 457871) B457871
theorem B305275 : Blo 303832 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B1157273 : Blo 303832 1157273 := bstep (se 2 (by rfl) ⟨433977, by rfl⟩ : syracuseStep 1157273 = 867955) B867955
theorem B305327 : Blo 303832 305327 := bstep (se 1 (by rfl) ⟨228995, by rfl⟩ : syracuseStep 305327 = 457991) B457991
theorem B305351 : Blo 303832 305351 := bstep (se 1 (by rfl) ⟨229013, by rfl⟩ : syracuseStep 305351 = 458027) B458027
theorem B305371 : Blo 303832 305371 := bstep (se 1 (by rfl) ⟨229028, by rfl⟩ : syracuseStep 305371 = 458057) B458057
theorem B4204781 : Blo 303832 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B1648907 : Blo 303832 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B305447 : Blo 303832 305447 := bstep (se 1 (by rfl) ⟨229085, by rfl⟩ : syracuseStep 305447 = 458171) B458171
theorem B305487 : Blo 303832 305487 := bstep (se 1 (by rfl) ⟨229115, by rfl⟩ : syracuseStep 305487 = 458231) B458231
theorem B305503 : Blo 303832 305503 := bstep (se 1 (by rfl) ⟨229127, by rfl⟩ : syracuseStep 305503 = 458255) B458255
theorem B305531 : Blo 303832 305531 := bstep (se 1 (by rfl) ⟨229148, by rfl⟩ : syracuseStep 305531 = 458297) B458297
theorem B731521 : Blo 303832 731521 := bstep (se 2 (by rfl) ⟨274320, by rfl⟩ : syracuseStep 731521 = 548641) B548641
theorem B305583 : Blo 303832 305583 := bstep (se 1 (by rfl) ⟨229187, by rfl⟩ : syracuseStep 305583 = 458375) B458375
theorem B305607 : Blo 303832 305607 := bstep (se 1 (by rfl) ⟨229205, by rfl⟩ : syracuseStep 305607 = 458411) B458411
theorem B305627 : Blo 303832 305627 := bstep (se 1 (by rfl) ⟨229220, by rfl⟩ : syracuseStep 305627 = 458441) B458441
theorem B1026593 : Blo 303832 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B305703 : Blo 303832 305703 := bstep (se 1 (by rfl) ⟨229277, by rfl⟩ : syracuseStep 305703 = 458555) B458555
theorem B305743 : Blo 303832 305743 := bstep (se 1 (by rfl) ⟨229307, by rfl⟩ : syracuseStep 305743 = 458615) B458615
theorem B305759 : Blo 303832 305759 := bstep (se 1 (by rfl) ⟨229319, by rfl⟩ : syracuseStep 305759 = 458639) B458639
theorem B305787 : Blo 303832 305787 := bstep (se 1 (by rfl) ⟨229340, by rfl⟩ : syracuseStep 305787 = 458681) B458681
theorem B305839 : Blo 303832 305839 := bstep (se 1 (by rfl) ⟨229379, by rfl⟩ : syracuseStep 305839 = 458759) B458759
theorem B305863 : Blo 303832 305863 := bstep (se 1 (by rfl) ⟨229397, by rfl⟩ : syracuseStep 305863 = 458795) B458795
theorem B305883 : Blo 303832 305883 := bstep (se 1 (by rfl) ⟨229412, by rfl⟩ : syracuseStep 305883 = 458825) B458825
theorem B1026809 : Blo 303832 1026809 := bstep (se 2 (by rfl) ⟨385053, by rfl⟩ : syracuseStep 1026809 = 770107) B770107
theorem B305959 : Blo 303832 305959 := bstep (se 1 (by rfl) ⟨229469, by rfl⟩ : syracuseStep 305959 = 458939) B458939
theorem B305999 : Blo 303832 305999 := bstep (se 1 (by rfl) ⟨229499, by rfl⟩ : syracuseStep 305999 = 458999) B458999
theorem B306015 : Blo 303832 306015 := bstep (se 1 (by rfl) ⟨229511, by rfl⟩ : syracuseStep 306015 = 459023) B459023
theorem B306043 : Blo 303832 306043 := bstep (se 1 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 306043 = 459065) B459065
theorem B306095 : Blo 303832 306095 := bstep (se 1 (by rfl) ⟨229571, by rfl⟩ : syracuseStep 306095 = 459143) B459143
theorem B437167 : Blo 303832 437167 := bstep (se 1 (by rfl) ⟨327875, by rfl⟩ : syracuseStep 437167 = 655751) B655751
theorem B306119 : Blo 303832 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B306139 : Blo 303832 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B1027079 : Blo 303832 1027079 := bstep (se 1 (by rfl) ⟨770309, by rfl⟩ : syracuseStep 1027079 = 1540619) B1540619
theorem B306215 : Blo 303832 306215 := bstep (se 1 (by rfl) ⟨229661, by rfl⟩ : syracuseStep 306215 = 459323) B459323
theorem B306255 : Blo 303832 306255 := bstep (se 1 (by rfl) ⟨229691, by rfl⟩ : syracuseStep 306255 = 459383) B459383
theorem B306271 : Blo 303832 306271 := bstep (se 1 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 306271 = 459407) B459407
theorem B1027187 : Blo 303832 1027187 := bstep (se 1 (by rfl) ⟨770390, by rfl⟩ : syracuseStep 1027187 = 1540781) B1540781
theorem B1158259 : Blo 303832 1158259 := bstep (se 1 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 1158259 = 1737389) B1737389
theorem B306299 : Blo 303832 306299 := bstep (se 1 (by rfl) ⟨229724, by rfl⟩ : syracuseStep 306299 = 459449) B459449
theorem B306351 : Blo 303832 306351 := bstep (se 1 (by rfl) ⟨229763, by rfl⟩ : syracuseStep 306351 = 459527) B459527
theorem B306375 : Blo 303832 306375 := bstep (se 1 (by rfl) ⟨229781, by rfl⟩ : syracuseStep 306375 = 459563) B459563
theorem B306395 : Blo 303832 306395 := bstep (se 1 (by rfl) ⟨229796, by rfl⟩ : syracuseStep 306395 = 459593) B459593
theorem B306471 : Blo 303832 306471 := bstep (se 1 (by rfl) ⟨229853, by rfl⟩ : syracuseStep 306471 = 459707) B459707
theorem B306511 : Blo 303832 306511 := bstep (se 1 (by rfl) ⟨229883, by rfl⟩ : syracuseStep 306511 = 459767) B459767
theorem B306527 : Blo 303832 306527 := bstep (se 1 (by rfl) ⟨229895, by rfl⟩ : syracuseStep 306527 = 459791) B459791
theorem B306555 : Blo 303832 306555 := bstep (se 1 (by rfl) ⟨229916, by rfl⟩ : syracuseStep 306555 = 459833) B459833
theorem B1027457 : Blo 303832 1027457 := bstep (se 2 (by rfl) ⟨385296, by rfl⟩ : syracuseStep 1027457 = 770593) B770593
theorem B306607 : Blo 303832 306607 := bstep (se 1 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 306607 = 459911) B459911
theorem B4402613 : Blo 303832 4402613 := bstep (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) B412745
theorem B306631 : Blo 303832 306631 := bstep (se 1 (by rfl) ⟨229973, by rfl⟩ : syracuseStep 306631 = 459947) B459947
theorem B306651 : Blo 303832 306651 := bstep (se 1 (by rfl) ⟨229988, by rfl⟩ : syracuseStep 306651 = 459977) B459977
theorem B306727 : Blo 303832 306727 := bstep (se 1 (by rfl) ⟨230045, by rfl⟩ : syracuseStep 306727 = 460091) B460091
theorem B306767 : Blo 303832 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B306783 : Blo 303832 306783 := bstep (se 1 (by rfl) ⟨230087, by rfl⟩ : syracuseStep 306783 = 460175) B460175
theorem B306811 : Blo 303832 306811 := bstep (se 1 (by rfl) ⟨230108, by rfl⟩ : syracuseStep 306811 = 460217) B460217
theorem B306863 : Blo 303832 306863 := bstep (se 1 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 306863 = 460295) B460295
theorem B306887 : Blo 303832 306887 := bstep (se 1 (by rfl) ⟨230165, by rfl⟩ : syracuseStep 306887 = 460331) B460331
theorem B306907 : Blo 303832 306907 := bstep (se 1 (by rfl) ⟨230180, by rfl⟩ : syracuseStep 306907 = 460361) B460361
theorem B1552121 : Blo 303832 1552121 := bstep (se 2 (by rfl) ⟨582045, by rfl⟩ : syracuseStep 1552121 = 1164091) B1164091
theorem B306983 : Blo 303832 306983 := bstep (se 1 (by rfl) ⟨230237, by rfl⟩ : syracuseStep 306983 = 460475) B460475
theorem B307023 : Blo 303832 307023 := bstep (se 1 (by rfl) ⟨230267, by rfl⟩ : syracuseStep 307023 = 460535) B460535
theorem B307039 : Blo 303832 307039 := bstep (se 1 (by rfl) ⟨230279, by rfl⟩ : syracuseStep 307039 = 460559) B460559
theorem B1159019 : Blo 303832 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B307067 : Blo 303832 307067 := bstep (se 1 (by rfl) ⟨230300, by rfl⟩ : syracuseStep 307067 = 460601) B460601
theorem B1650593 : Blo 303832 1650593 := bstep (se 2 (by rfl) ⟨618972, by rfl⟩ : syracuseStep 1650593 = 1237945) B1237945
theorem B307119 : Blo 303832 307119 := bstep (se 1 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 307119 = 460679) B460679
theorem B307143 : Blo 303832 307143 := bstep (se 1 (by rfl) ⟨230357, by rfl⟩ : syracuseStep 307143 = 460715) B460715
theorem B307163 : Blo 303832 307163 := bstep (se 1 (by rfl) ⟨230372, by rfl⟩ : syracuseStep 307163 = 460745) B460745
theorem B667667 : Blo 303832 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B307239 : Blo 303832 307239 := bstep (se 1 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 307239 = 460859) B460859
theorem B307279 : Blo 303832 307279 := bstep (se 1 (by rfl) ⟨230459, by rfl⟩ : syracuseStep 307279 = 460919) B460919
theorem B307295 : Blo 303832 307295 := bstep (se 1 (by rfl) ⟨230471, by rfl⟩ : syracuseStep 307295 = 460943) B460943
theorem B307323 : Blo 303832 307323 := bstep (se 1 (by rfl) ⟨230492, by rfl⟩ : syracuseStep 307323 = 460985) B460985
theorem B1028267 : Blo 303832 1028267 := bstep (se 1 (by rfl) ⟨771200, by rfl⟩ : syracuseStep 1028267 = 1542401) B1542401
theorem B307375 : Blo 303832 307375 := bstep (se 1 (by rfl) ⟨230531, by rfl⟩ : syracuseStep 307375 = 461063) B461063
theorem B307399 : Blo 303832 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B307419 : Blo 303832 307419 := bstep (se 1 (by rfl) ⟨230564, by rfl⟩ : syracuseStep 307419 = 461129) B461129
theorem B307495 : Blo 303832 307495 := bstep (se 1 (by rfl) ⟨230621, by rfl⟩ : syracuseStep 307495 = 461243) B461243
theorem B307535 : Blo 303832 307535 := bstep (se 1 (by rfl) ⟨230651, by rfl⟩ : syracuseStep 307535 = 461303) B461303
theorem B307551 : Blo 303832 307551 := bstep (se 1 (by rfl) ⟨230663, by rfl⟩ : syracuseStep 307551 = 461327) B461327
theorem B1651049 : Blo 303832 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B307579 : Blo 303832 307579 := bstep (se 1 (by rfl) ⟨230684, by rfl⟩ : syracuseStep 307579 = 461369) B461369
theorem B1552769 : Blo 303832 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B307631 : Blo 303832 307631 := bstep (se 1 (by rfl) ⟨230723, by rfl⟩ : syracuseStep 307631 = 461447) B461447
theorem B307655 : Blo 303832 307655 := bstep (se 1 (by rfl) ⟨230741, by rfl⟩ : syracuseStep 307655 = 461483) B461483
theorem B307675 : Blo 303832 307675 := bstep (se 1 (by rfl) ⟨230756, by rfl⟩ : syracuseStep 307675 = 461513) B461513
theorem B307751 : Blo 303832 307751 := bstep (se 1 (by rfl) ⟨230813, by rfl⟩ : syracuseStep 307751 = 461627) B461627
theorem B307791 : Blo 303832 307791 := bstep (se 1 (by rfl) ⟨230843, by rfl⟩ : syracuseStep 307791 = 461687) B461687
theorem B307807 : Blo 303832 307807 := bstep (se 1 (by rfl) ⟨230855, by rfl⟩ : syracuseStep 307807 = 461711) B461711
theorem B1028807 : Blo 303832 1028807 := bstep (se 1 (by rfl) ⟨771605, by rfl⟩ : syracuseStep 1028807 = 1543211) B1543211
theorem B10138385 : Blo 303832 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B308047 : Blo 303832 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B2470763 : Blo 303832 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B1553579 : Blo 303832 1553579 := bstep (se 1 (by rfl) ⟨1165184, by rfl⟩ : syracuseStep 1553579 = 2330369) B2330369
theorem B1029671 : Blo 303832 1029671 := bstep (se 1 (by rfl) ⟨772253, by rfl⟩ : syracuseStep 1029671 = 1544507) B1544507
theorem B1554065 : Blo 303832 1554065 := bstep (se 2 (by rfl) ⟨582774, by rfl⟩ : syracuseStep 1554065 = 1165549) B1165549
theorem B1029779 : Blo 303832 1029779 := bstep (se 1 (by rfl) ⟨772334, by rfl⟩ : syracuseStep 1029779 = 1544669) B1544669
theorem B866143 : Blo 303832 866143 := bstep (se 1 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 866143 = 1299215) B1299215
theorem B1029995 : Blo 303832 1029995 := bstep (se 1 (by rfl) ⟨772496, by rfl⟩ : syracuseStep 1029995 = 1544993) B1544993
theorem B1030049 : Blo 303832 1030049 := bstep (se 2 (by rfl) ⟨386268, by rfl⟩ : syracuseStep 1030049 = 772537) B772537
theorem B5027777 : Blo 303832 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B342139 : Blo 303832 342139 := bstep (se 1 (by rfl) ⟨256604, by rfl⟩ : syracuseStep 342139 = 513209) B513209
theorem B5191937 : Blo 303832 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B4929977 : Blo 303832 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B1980875 : Blo 303832 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B1030643 : Blo 303832 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B342607 : Blo 303832 342607 := bstep (se 1 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 342607 = 513911) B513911
theorem B998099 : Blo 303832 998099 := bstep (se 1 (by rfl) ⟨748574, by rfl⟩ : syracuseStep 998099 = 1497149) B1497149
theorem B343003 : Blo 303832 343003 := bstep (se 1 (by rfl) ⟨257252, by rfl⟩ : syracuseStep 343003 = 514505) B514505
theorem B1031183 : Blo 303832 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B7846955 : Blo 303832 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B769409 : Blo 303832 769409 := bstep (se 2 (by rfl) ⟨288528, by rfl⟩ : syracuseStep 769409 = 577057) B577057
theorem B343471 : Blo 303832 343471 := bstep (se 1 (by rfl) ⟨257603, by rfl⟩ : syracuseStep 343471 = 515207) B515207
theorem B1031777 : Blo 303832 1031777 := bstep (se 2 (by rfl) ⟨386916, by rfl⟩ : syracuseStep 1031777 = 773833) B773833
theorem B1162937 : Blo 303832 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B1294123 : Blo 303832 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B343903 : Blo 303832 343903 := bstep (se 1 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 343903 = 515855) B515855
theorem B1556333 : Blo 303832 1556333 := bstep (se 3 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 1556333 = 583625) B583625
theorem B1556495 : Blo 303832 1556495 := bstep (se 1 (by rfl) ⟨1167371, by rfl⟩ : syracuseStep 1556495 = 2334743) B2334743
theorem B770219 : Blo 303832 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B344263 : Blo 303832 344263 := bstep (se 1 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 344263 = 516395) B516395
theorem B1392983 : Blo 303832 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B311887 : Blo 303832 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B771079 : Blo 303832 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B1033235 : Blo 303832 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B345127 : Blo 303832 345127 := bstep (se 1 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 345127 = 517691) B517691
theorem B1098809 : Blo 303832 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B2311415 : Blo 303832 2311415 := bstep (se 1 (by rfl) ⟨1733561, by rfl⟩ : syracuseStep 2311415 = 3467123) B3467123
theorem B1033559 : Blo 303832 1033559 := bstep (se 1 (by rfl) ⟨775169, by rfl⟩ : syracuseStep 1033559 = 1550339) B1550339
theorem B771707 : Blo 303832 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B2311901 : Blo 303832 2311901 := bstep (se 3 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 2311901 = 866963) B866963
theorem B1165049 : Blo 303832 1165049 := bstep (se 2 (by rfl) ⟨436893, by rfl⟩ : syracuseStep 1165049 = 873787) B873787
theorem B772001 : Blo 303832 772001 := bstep (se 2 (by rfl) ⟨289500, by rfl⟩ : syracuseStep 772001 = 579001) B579001
theorem B1099777 : Blo 303832 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B1034639 : Blo 303832 1034639 := bstep (se 1 (by rfl) ⟨775979, by rfl⟩ : syracuseStep 1034639 = 1551959) B1551959
theorem B1395409 : Blo 303832 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B1034963 : Blo 303832 1034963 := bstep (se 1 (by rfl) ⟨776222, by rfl⟩ : syracuseStep 1034963 = 1552445) B1552445
theorem B1166035 : Blo 303832 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B1166507 : Blo 303832 1166507 := bstep (se 1 (by rfl) ⟨874880, by rfl⟩ : syracuseStep 1166507 = 1749761) B1749761
theorem B576875 : Blo 303832 576875 := bstep (se 1 (by rfl) ⟨432656, by rfl⟩ : syracuseStep 576875 = 865313) B865313
theorem B1297883 : Blo 303832 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B773671 : Blo 303832 773671 := bstep (se 1 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 773671 = 1160507) B1160507
theorem B871975 : Blo 303832 871975 := bstep (se 1 (by rfl) ⟨653981, by rfl⟩ : syracuseStep 871975 = 1307963) B1307963
theorem B872147 : Blo 303832 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B773995 : Blo 303832 773995 := bstep (se 1 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 773995 = 1160993) B1160993
theorem B1036151 : Blo 303832 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B577543 : Blo 303832 577543 := bstep (se 1 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 577543 = 866315) B866315
theorem B741395 : Blo 303832 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B1036367 : Blo 303832 1036367 := bstep (se 1 (by rfl) ⟨777275, by rfl⟩ : syracuseStep 1036367 = 1554551) B1554551
theorem B1036745 : Blo 303832 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B4444625 : Blo 303832 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B774643 : Blo 303832 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B8802917 : Blo 303832 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B1037015 : Blo 303832 1037015 := bstep (se 1 (by rfl) ⟨777761, by rfl⟩ : syracuseStep 1037015 = 1555523) B1555523
theorem B1037231 : Blo 303832 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B873479 : Blo 303832 873479 := bstep (se 1 (by rfl) ⟨655109, by rfl⟩ : syracuseStep 873479 = 1310219) B1310219
theorem B1168465 : Blo 303832 1168465 := bstep (se 2 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 1168465 = 876349) B876349
theorem B1103165 : Blo 303832 1103165 := bstep (se 3 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 1103165 = 413687) B413687
theorem B1168769 : Blo 303832 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B513499 : Blo 303832 513499 := bstep (se 1 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 513499 = 770249) B770249
theorem B1463771 : Blo 303832 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B7886321 : Blo 303832 7886321 := bstep (se 2 (by rfl) ⟨2957370, by rfl⟩ : syracuseStep 7886321 = 5914741) B5914741
theorem B775777 : Blo 303832 775777 := bstep (se 2 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 775777 = 581833) B581833
theorem B1300157 : Blo 303832 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B1955771 : Blo 303832 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B1955897 : Blo 303832 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B514127 : Blo 303832 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B579707 : Blo 303832 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B1104043 : Blo 303832 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B579935 : Blo 303832 579935 := bstep (se 1 (by rfl) ⟨434951, by rfl⟩ : syracuseStep 579935 = 869903) B869903
theorem B776729 : Blo 303832 776729 := bstep (se 2 (by rfl) ⟨291273, by rfl⟩ : syracuseStep 776729 = 582547) B582547
theorem B580193 : Blo 303832 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B2218697 : Blo 303832 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B580459 : Blo 303832 580459 := bstep (se 1 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 580459 = 870689) B870689
theorem B514991 : Blo 303832 514991 := bstep (se 1 (by rfl) ⟨386243, by rfl⟩ : syracuseStep 514991 = 772487) B772487
theorem B777235 : Blo 303832 777235 := bstep (se 1 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 777235 = 1165853) B1165853
theorem B515423 : Blo 303832 515423 := bstep (se 1 (by rfl) ⟨386567, by rfl⟩ : syracuseStep 515423 = 773135) B773135
theorem B2317733 : Blo 303832 2317733 := bstep (se 4 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 2317733 = 434575) B434575
theorem B1302155 : Blo 303832 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B876395 : Blo 303832 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B515983 : Blo 303832 515983 := bstep (se 1 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 515983 = 773975) B773975
theorem B4415417 : Blo 303832 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B581651 : Blo 303832 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B8970263 : Blo 303832 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B778319 : Blo 303832 778319 := bstep (se 1 (by rfl) ⟨583739, by rfl⟩ : syracuseStep 778319 = 1167479) B1167479
theorem B2613329 : Blo 303832 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B581879 : Blo 303832 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B385499 : Blo 303832 385499 := bstep (se 1 (by rfl) ⟨289124, by rfl⟩ : syracuseStep 385499 = 578249) B578249
theorem B516665 : Blo 303832 516665 := bstep (se 2 (by rfl) ⟨193749, by rfl⟩ : syracuseStep 516665 = 387499) B387499
theorem B746081 : Blo 303832 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B778967 : Blo 303832 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B549737 : Blo 303832 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B385975 : Blo 303832 385975 := bstep (se 1 (by rfl) ⟨289481, by rfl⟩ : syracuseStep 385975 = 578963) B578963
theorem B1893455 : Blo 303832 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B517367 : Blo 303832 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B1238561 : Blo 303832 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B517711 : Blo 303832 517711 := bstep (se 1 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 517711 = 776567) B776567
theorem B583291 : Blo 303832 583291 := bstep (se 1 (by rfl) ⟨437468, by rfl⟩ : syracuseStep 583291 = 874937) B874937
theorem B517961 : Blo 303832 517961 := bstep (se 2 (by rfl) ⟨194235, by rfl⟩ : syracuseStep 517961 = 388471) B388471
theorem B4417375 : Blo 303832 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B583519 : Blo 303832 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B649147 : Blo 303832 649147 := bstep (se 1 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 649147 = 973721) B973721
theorem B3958721 : Blo 303832 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B583777 : Blo 303832 583777 := bstep (se 2 (by rfl) ⟨218916, by rfl⟩ : syracuseStep 583777 = 437833) B437833
theorem B6383717 : Blo 303832 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B387271 : Blo 303832 387271 := bstep (se 1 (by rfl) ⟨290453, by rfl⟩ : syracuseStep 387271 = 580907) B580907
theorem B518393 : Blo 303832 518393 := bstep (se 2 (by rfl) ⟨194397, by rfl⟩ : syracuseStep 518393 = 388795) B388795
theorem B3697001 : Blo 303832 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B551329 : Blo 303832 551329 := bstep (se 2 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 551329 = 413497) B413497
theorem B518575 : Blo 303832 518575 := bstep (se 1 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 518575 = 777863) B777863
theorem B584111 : Blo 303832 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B518663 : Blo 303832 518663 := bstep (se 1 (by rfl) ⟨388997, by rfl⟩ : syracuseStep 518663 = 777995) B777995
theorem B1108669 : Blo 303832 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B13200101 : Blo 303832 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B3533645 : Blo 303832 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B519007 : Blo 303832 519007 := bstep (se 1 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 519007 = 778511) B778511
theorem B9890707 : Blo 303832 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B617399 : Blo 303832 617399 := bstep (se 1 (by rfl) ⟨463049, by rfl⟩ : syracuseStep 617399 = 926099) B926099
theorem B519095 : Blo 303832 519095 := bstep (se 1 (by rfl) ⟨389321, by rfl⟩ : syracuseStep 519095 = 778643) B778643
theorem B1731557 : Blo 303832 1731557 := bstep (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) B324667
theorem B584723 : Blo 303832 584723 := bstep (se 1 (by rfl) ⟨438542, by rfl⟩ : syracuseStep 584723 = 877085) B877085
theorem B1469459 : Blo 303832 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B977999 : Blo 303832 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B3468581 : Blo 303832 3468581 := bstep (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) B650359
theorem B1732013 : Blo 303832 1732013 := bstep (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) B649505
theorem B552619 : Blo 303832 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B3698551 : Blo 303832 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B1306529 : Blo 303832 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B552865 : Blo 303832 552865 := bstep (se 2 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 552865 = 414649) B414649
theorem B683963 : Blo 303832 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B1961921 : Blo 303832 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1306631 : Blo 303832 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B684089 : Blo 303832 684089 := bstep (se 2 (by rfl) ⟨256533, by rfl⟩ : syracuseStep 684089 = 513067) B513067
theorem B1732697 : Blo 303832 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B684431 : Blo 303832 684431 := bstep (se 1 (by rfl) ⟨513323, by rfl⟩ : syracuseStep 684431 = 1026647) B1026647
theorem B2323079 : Blo 303832 2323079 := bstep (se 1 (by rfl) ⟨1742309, by rfl⟩ : syracuseStep 2323079 = 3484619) B3484619
theorem B553643 : Blo 303832 553643 := bstep (se 1 (by rfl) ⟨415232, by rfl⟩ : syracuseStep 553643 = 830465) B830465
theorem B684755 : Blo 303832 684755 := bstep (se 1 (by rfl) ⟨513566, by rfl⟩ : syracuseStep 684755 = 1027133) B1027133
theorem B521255 : Blo 303832 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B521273 : Blo 303832 521273 := bstep (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) B390955
theorem B455759 : Blo 303832 455759 := bstep (se 1 (by rfl) ⟨341819, by rfl⟩ : syracuseStep 455759 = 683639) B683639
theorem B1045583 : Blo 303832 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B455879 : Blo 303832 455879 := bstep (se 1 (by rfl) ⟨341909, by rfl⟩ : syracuseStep 455879 = 683819) B683819
theorem B423263 : Blo 303832 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B456041 : Blo 303832 456041 := bstep (se 2 (by rfl) ⟨171015, by rfl⟩ : syracuseStep 456041 = 342031) B342031
theorem B1963379 : Blo 303832 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B456119 : Blo 303832 456119 := bstep (se 1 (by rfl) ⟨342089, by rfl⟩ : syracuseStep 456119 = 684179) B684179
theorem B456155 : Blo 303832 456155 := bstep (se 1 (by rfl) ⟨342116, by rfl⟩ : syracuseStep 456155 = 684233) B684233
theorem B783881 : Blo 303832 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B685691 : Blo 303832 685691 := bstep (se 1 (by rfl) ⟨514268, by rfl⟩ : syracuseStep 685691 = 1028537) B1028537
theorem B2094781 : Blo 303832 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B685817 : Blo 303832 685817 := bstep (se 2 (by rfl) ⟨257181, by rfl⟩ : syracuseStep 685817 = 514363) B514363
theorem B456623 : Blo 303832 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B686087 : Blo 303832 686087 := bstep (se 1 (by rfl) ⟨514565, by rfl⟩ : syracuseStep 686087 = 1029131) B1029131
theorem B1472519 : Blo 303832 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B456713 : Blo 303832 456713 := bstep (se 2 (by rfl) ⟨171267, by rfl⟩ : syracuseStep 456713 = 342535) B342535
theorem B1964047 : Blo 303832 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B456743 : Blo 303832 456743 := bstep (se 1 (by rfl) ⟨342557, by rfl⟩ : syracuseStep 456743 = 685115) B685115
theorem B2324537 : Blo 303832 2324537 := bstep (se 2 (by rfl) ⟨871701, by rfl⟩ : syracuseStep 2324537 = 1743403) B1743403
theorem B686159 : Blo 303832 686159 := bstep (se 1 (by rfl) ⟨514619, by rfl⟩ : syracuseStep 686159 = 1029239) B1029239
theorem B456827 : Blo 303832 456827 := bstep (se 1 (by rfl) ⟨342620, by rfl⟩ : syracuseStep 456827 = 685241) B685241
theorem B1046681 : Blo 303832 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B456953 : Blo 303832 456953 := bstep (se 2 (by rfl) ⟨171357, by rfl⟩ : syracuseStep 456953 = 342715) B342715
theorem B457055 : Blo 303832 457055 := bstep (se 1 (by rfl) ⟨342791, by rfl⟩ : syracuseStep 457055 = 685583) B685583
theorem B457067 : Blo 303832 457067 := bstep (se 1 (by rfl) ⟨342800, by rfl⟩ : syracuseStep 457067 = 685601) B685601
theorem B489871 : Blo 303832 489871 := bstep (se 1 (by rfl) ⟨367403, by rfl⟩ : syracuseStep 489871 = 734807) B734807
theorem B686555 : Blo 303832 686555 := bstep (se 1 (by rfl) ⟨514916, by rfl⟩ : syracuseStep 686555 = 1029833) B1029833
theorem B1309193 : Blo 303832 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B457295 : Blo 303832 457295 := bstep (se 1 (by rfl) ⟨342971, by rfl⟩ : syracuseStep 457295 = 685943) B685943
theorem B621179 : Blo 303832 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B457415 : Blo 303832 457415 := bstep (se 1 (by rfl) ⟨343061, by rfl⟩ : syracuseStep 457415 = 686123) B686123
theorem B457577 : Blo 303832 457577 := bstep (se 2 (by rfl) ⟨171591, by rfl⟩ : syracuseStep 457577 = 343183) B343183
theorem B523115 : Blo 303832 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B687023 : Blo 303832 687023 := bstep (se 1 (by rfl) ⟨515267, by rfl⟩ : syracuseStep 687023 = 1030535) B1030535
theorem B1538999 : Blo 303832 1538999 := bstep (se 1 (by rfl) ⟨1154249, by rfl⟩ : syracuseStep 1538999 = 2308499) B2308499
theorem B457655 : Blo 303832 457655 := bstep (se 1 (by rfl) ⟨343241, by rfl⟩ : syracuseStep 457655 = 686483) B686483
theorem B457691 : Blo 303832 457691 := bstep (se 1 (by rfl) ⟨343268, by rfl⟩ : syracuseStep 457691 = 686537) B686537
theorem B1473689 : Blo 303832 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B687275 : Blo 303832 687275 := bstep (se 1 (by rfl) ⟨515456, by rfl⟩ : syracuseStep 687275 = 1030913) B1030913
theorem B5209433 : Blo 303832 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B458159 : Blo 303832 458159 := bstep (se 1 (by rfl) ⟨343619, by rfl⟩ : syracuseStep 458159 = 687239) B687239
theorem B458249 : Blo 303832 458249 := bstep (se 2 (by rfl) ⟨171843, by rfl⟩ : syracuseStep 458249 = 343687) B343687
theorem B458279 : Blo 303832 458279 := bstep (se 1 (by rfl) ⟨343709, by rfl⟩ : syracuseStep 458279 = 687419) B687419
theorem B786017 : Blo 303832 786017 := bstep (se 2 (by rfl) ⟨294756, by rfl⟩ : syracuseStep 786017 = 589513) B589513
theorem B458363 : Blo 303832 458363 := bstep (se 1 (by rfl) ⟨343772, by rfl⟩ : syracuseStep 458363 = 687545) B687545
theorem B491179 : Blo 303832 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B687815 : Blo 303832 687815 := bstep (se 1 (by rfl) ⟨515861, by rfl⟩ : syracuseStep 687815 = 1031723) B1031723
theorem B458489 : Blo 303832 458489 := bstep (se 2 (by rfl) ⟨171933, by rfl⟩ : syracuseStep 458489 = 343867) B343867
theorem B458591 : Blo 303832 458591 := bstep (se 1 (by rfl) ⟨343943, by rfl⟩ : syracuseStep 458591 = 687887) B687887
theorem B458603 : Blo 303832 458603 := bstep (se 1 (by rfl) ⟨343952, by rfl⟩ : syracuseStep 458603 = 687905) B687905
theorem B2326481 : Blo 303832 2326481 := bstep (se 2 (by rfl) ⟨872430, by rfl⟩ : syracuseStep 2326481 = 1744861) B1744861
theorem B459017 : Blo 303832 459017 := bstep (se 2 (by rfl) ⟨172131, by rfl⟩ : syracuseStep 459017 = 344263) B344263
theorem B459119 : Blo 303832 459119 := bstep (se 1 (by rfl) ⟨344339, by rfl⟩ : syracuseStep 459119 = 688679) B688679
theorem B328255 : Blo 303832 328255 := bstep (se 1 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 328255 = 492383) B492383
theorem B459335 : Blo 303832 459335 := bstep (se 1 (by rfl) ⟨344501, by rfl⟩ : syracuseStep 459335 = 689003) B689003
theorem B524873 : Blo 303832 524873 := bstep (se 2 (by rfl) ⟨196827, by rfl⟩ : syracuseStep 524873 = 393655) B393655
theorem B459371 : Blo 303832 459371 := bstep (se 1 (by rfl) ⟨344528, by rfl⟩ : syracuseStep 459371 = 689057) B689057
theorem B688823 : Blo 303832 688823 := bstep (se 1 (by rfl) ⟨516617, by rfl⟩ : syracuseStep 688823 = 1033235) B1033235
theorem B1540943 : Blo 303832 1540943 := bstep (se 1 (by rfl) ⟨1155707, by rfl⟩ : syracuseStep 1540943 = 2311415) B2311415
theorem B459599 : Blo 303832 459599 := bstep (se 1 (by rfl) ⟨344699, by rfl⟩ : syracuseStep 459599 = 689399) B689399
theorem B689039 : Blo 303832 689039 := bstep (se 1 (by rfl) ⟨516779, by rfl⟩ : syracuseStep 689039 = 1033559) B1033559
theorem B1573793 : Blo 303832 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B787495 : Blo 303832 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B37815349 : Blo 303832 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B1541267 : Blo 303832 1541267 := bstep (se 1 (by rfl) ⟨1155950, by rfl⟩ : syracuseStep 1541267 = 2311901) B2311901
theorem B459995 : Blo 303832 459995 := bstep (se 1 (by rfl) ⟨344996, by rfl⟩ : syracuseStep 459995 = 689993) B689993
theorem B460169 : Blo 303832 460169 := bstep (se 2 (by rfl) ⟨172563, by rfl⟩ : syracuseStep 460169 = 345127) B345127
theorem B3933683 : Blo 303832 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B689759 : Blo 303832 689759 := bstep (se 1 (by rfl) ⟨517319, by rfl⟩ : syracuseStep 689759 = 1034639) B1034639
theorem B460523 : Blo 303832 460523 := bstep (se 1 (by rfl) ⟨345392, by rfl⟩ : syracuseStep 460523 = 690785) B690785
theorem B689975 : Blo 303832 689975 := bstep (se 1 (by rfl) ⟨517481, by rfl⟩ : syracuseStep 689975 = 1034963) B1034963
theorem B2328425 : Blo 303832 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B460751 : Blo 303832 460751 := bstep (se 1 (by rfl) ⟨345563, by rfl⟩ : syracuseStep 460751 = 691127) B691127
theorem B690281 : Blo 303832 690281 := bstep (se 2 (by rfl) ⟨258855, by rfl⟩ : syracuseStep 690281 = 517711) B517711
theorem B624905 : Blo 303832 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B6588701 : Blo 303832 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B461147 : Blo 303832 461147 := bstep (se 1 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 461147 = 691721) B691721
theorem B1673597 : Blo 303832 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B461375 : Blo 303832 461375 := bstep (se 1 (by rfl) ⟨346031, by rfl⟩ : syracuseStep 461375 = 692063) B692063
theorem B690767 : Blo 303832 690767 := bstep (se 1 (by rfl) ⟨518075, by rfl⟩ : syracuseStep 690767 = 1036151) B1036151
theorem B494263 : Blo 303832 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B461495 : Blo 303832 461495 := bstep (se 1 (by rfl) ⟨346121, by rfl⟩ : syracuseStep 461495 = 692243) B692243
theorem B690911 : Blo 303832 690911 := bstep (se 1 (by rfl) ⟨518183, by rfl⟩ : syracuseStep 690911 = 1036367) B1036367
theorem B1313603 : Blo 303832 1313603 := bstep (se 1 (by rfl) ⟨985202, by rfl⟩ : syracuseStep 1313603 = 1970405) B1970405
theorem B461723 : Blo 303832 461723 := bstep (se 1 (by rfl) ⟨346292, by rfl⟩ : syracuseStep 461723 = 692585) B692585
theorem B691163 : Blo 303832 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B5868611 : Blo 303832 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B691343 : Blo 303832 691343 := bstep (se 1 (by rfl) ⟨518507, by rfl⟩ : syracuseStep 691343 = 1037015) B1037015
theorem B691433 : Blo 303832 691433 := bstep (se 2 (by rfl) ⟨259287, by rfl⟩ : syracuseStep 691433 = 518575) B518575
theorem B691487 : Blo 303832 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B1314319 : Blo 303832 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B1478225 : Blo 303832 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B692009 : Blo 303832 692009 := bstep (se 2 (by rfl) ⟨259503, by rfl⟩ : syracuseStep 692009 = 519007) B519007
theorem B3149725 : Blo 303832 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B1544345 : Blo 303832 1544345 := bstep (se 2 (by rfl) ⟨579129, by rfl⟩ : syracuseStep 1544345 = 1158259) B1158259
theorem B463195 : Blo 303832 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B397735 : Blo 303832 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B1479131 : Blo 303832 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B1545155 : Blo 303832 1545155 := bstep (se 1 (by rfl) ⟨1158866, by rfl⟩ : syracuseStep 1545155 = 2317733) B2317733
theorem B1742219 : Blo 303832 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B2561675 : Blo 303832 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B497387 : Blo 303832 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B366491 : Blo 303832 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B19929037 : Blo 303832 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B825707 : Blo 303832 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B2464667 : Blo 303832 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B1154371 : Blo 303832 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B3939677 : Blo 303832 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B2793041 : Blo 303832 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B1154675 : Blo 303832 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B1154857 : Blo 303832 1154857 := bstep (se 2 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 1154857 = 866143) B866143
theorem B1155131 : Blo 303832 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B1548719 : Blo 303832 1548719 := bstep (se 1 (by rfl) ⟨1161539, by rfl⟩ : syracuseStep 1548719 = 2323079) B2323079
theorem B369095 : Blo 303832 369095 := bstep (se 1 (by rfl) ⟨276821, by rfl⟩ : syracuseStep 369095 = 553643) B553643
theorem B6758923 : Blo 303832 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B303839 : Blo 303832 303839 := bstep (se 1 (by rfl) ⟨227879, by rfl⟩ : syracuseStep 303839 = 455759) B455759
theorem B697055 : Blo 303832 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B303919 : Blo 303832 303919 := bstep (se 1 (by rfl) ⟨227939, by rfl⟩ : syracuseStep 303919 = 455879) B455879
theorem B304027 : Blo 303832 304027 := bstep (se 1 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 304027 = 456041) B456041
theorem B304079 : Blo 303832 304079 := bstep (se 1 (by rfl) ⟨228059, by rfl⟩ : syracuseStep 304079 = 456119) B456119
theorem B304103 : Blo 303832 304103 := bstep (se 1 (by rfl) ⟨228077, by rfl⟩ : syracuseStep 304103 = 456155) B456155
theorem B304415 : Blo 303832 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B3351851 : Blo 303832 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B304475 : Blo 303832 304475 := bstep (se 1 (by rfl) ⟨228356, by rfl⟩ : syracuseStep 304475 = 456713) B456713
theorem B304495 : Blo 303832 304495 := bstep (se 1 (by rfl) ⟨228371, by rfl⟩ : syracuseStep 304495 = 456743) B456743
theorem B1549691 : Blo 303832 1549691 := bstep (se 1 (by rfl) ⟨1162268, by rfl⟩ : syracuseStep 1549691 = 2324537) B2324537
theorem B304551 : Blo 303832 304551 := bstep (se 1 (by rfl) ⟨228413, by rfl⟩ : syracuseStep 304551 = 456827) B456827
theorem B697787 : Blo 303832 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B304635 : Blo 303832 304635 := bstep (se 1 (by rfl) ⟨228476, by rfl⟩ : syracuseStep 304635 = 456953) B456953
theorem B304703 : Blo 303832 304703 := bstep (se 1 (by rfl) ⟨228527, by rfl⟩ : syracuseStep 304703 = 457055) B457055
theorem B304711 : Blo 303832 304711 := bstep (se 1 (by rfl) ⟨228533, by rfl⟩ : syracuseStep 304711 = 457067) B457067
theorem B3286651 : Blo 303832 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B1320583 : Blo 303832 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B304863 : Blo 303832 304863 := bstep (se 1 (by rfl) ⟨228647, by rfl⟩ : syracuseStep 304863 = 457295) B457295
theorem B304943 : Blo 303832 304943 := bstep (se 1 (by rfl) ⟨228707, by rfl⟩ : syracuseStep 304943 = 457415) B457415
theorem B665399 : Blo 303832 665399 := bstep (se 1 (by rfl) ⟨499049, by rfl⟩ : syracuseStep 665399 = 998099) B998099
theorem B305051 : Blo 303832 305051 := bstep (se 1 (by rfl) ⟨228788, by rfl⟩ : syracuseStep 305051 = 457577) B457577
theorem B1025999 : Blo 303832 1025999 := bstep (se 1 (by rfl) ⟨769499, by rfl⟩ : syracuseStep 1025999 = 1538999) B1538999
theorem B305103 : Blo 303832 305103 := bstep (se 1 (by rfl) ⟨228827, by rfl⟩ : syracuseStep 305103 = 457655) B457655
theorem B305127 : Blo 303832 305127 := bstep (se 1 (by rfl) ⟨228845, by rfl⟩ : syracuseStep 305127 = 457691) B457691
theorem B305439 : Blo 303832 305439 := bstep (se 1 (by rfl) ⟨229079, by rfl⟩ : syracuseStep 305439 = 458159) B458159
theorem B305499 : Blo 303832 305499 := bstep (se 1 (by rfl) ⟨229124, by rfl⟩ : syracuseStep 305499 = 458249) B458249
theorem B305519 : Blo 303832 305519 := bstep (se 1 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 305519 = 458279) B458279
theorem B305575 : Blo 303832 305575 := bstep (se 1 (by rfl) ⟨229181, by rfl⟩ : syracuseStep 305575 = 458363) B458363
theorem B305659 : Blo 303832 305659 := bstep (se 1 (by rfl) ⟨229244, by rfl⟩ : syracuseStep 305659 = 458489) B458489
theorem B305727 : Blo 303832 305727 := bstep (se 1 (by rfl) ⟨229295, by rfl⟩ : syracuseStep 305727 = 458591) B458591
theorem B305735 : Blo 303832 305735 := bstep (se 1 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 305735 = 458603) B458603
theorem B1550987 : Blo 303832 1550987 := bstep (se 1 (by rfl) ⟨1163240, by rfl⟩ : syracuseStep 1550987 = 2326481) B2326481
theorem B1780445 : Blo 303832 1780445 := bstep (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) B667667
theorem B305887 : Blo 303832 305887 := bstep (se 1 (by rfl) ⟨229415, by rfl⟩ : syracuseStep 305887 = 458831) B458831
theorem B305967 : Blo 303832 305967 := bstep (se 1 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 305967 = 458951) B458951
theorem B928655 : Blo 303832 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B1026971 : Blo 303832 1026971 := bstep (se 1 (by rfl) ⟨770228, by rfl⟩ : syracuseStep 1026971 = 1540457) B1540457
theorem B306075 : Blo 303832 306075 := bstep (se 1 (by rfl) ⟨229556, by rfl⟩ : syracuseStep 306075 = 459113) B459113
theorem B306127 : Blo 303832 306127 := bstep (se 1 (by rfl) ⟨229595, by rfl⟩ : syracuseStep 306127 = 459191) B459191
theorem B306151 : Blo 303832 306151 := bstep (se 1 (by rfl) ⟨229613, by rfl⟩ : syracuseStep 306151 = 459227) B459227
theorem B5024987 : Blo 303832 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B2600207 : Blo 303832 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B306463 : Blo 303832 306463 := bstep (se 1 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 306463 = 459695) B459695
theorem B306523 : Blo 303832 306523 := bstep (se 1 (by rfl) ⟨229892, by rfl⟩ : syracuseStep 306523 = 459785) B459785
theorem B306543 : Blo 303832 306543 := bstep (se 1 (by rfl) ⟨229907, by rfl⟩ : syracuseStep 306543 = 459815) B459815
theorem B732539 : Blo 303832 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B306599 : Blo 303832 306599 := bstep (se 1 (by rfl) ⟨229949, by rfl⟩ : syracuseStep 306599 = 459899) B459899
theorem B306683 : Blo 303832 306683 := bstep (se 1 (by rfl) ⟨230012, by rfl⟩ : syracuseStep 306683 = 460025) B460025
theorem B306751 : Blo 303832 306751 := bstep (se 1 (by rfl) ⟨230063, by rfl⟩ : syracuseStep 306751 = 460127) B460127
theorem B306759 : Blo 303832 306759 := bstep (se 1 (by rfl) ⟨230069, by rfl⟩ : syracuseStep 306759 = 460139) B460139
theorem B306911 : Blo 303832 306911 := bstep (se 1 (by rfl) ⟨230183, by rfl⟩ : syracuseStep 306911 = 460367) B460367
theorem B306991 : Blo 303832 306991 := bstep (se 1 (by rfl) ⟨230243, by rfl⟩ : syracuseStep 306991 = 460487) B460487
theorem B307099 : Blo 303832 307099 := bstep (se 1 (by rfl) ⟨230324, by rfl⟩ : syracuseStep 307099 = 460649) B460649
theorem B1027997 : Blo 303832 1027997 := bstep (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) B385499
theorem B307151 : Blo 303832 307151 := bstep (se 1 (by rfl) ⟨230363, by rfl⟩ : syracuseStep 307151 = 460727) B460727
theorem B307175 : Blo 303832 307175 := bstep (se 1 (by rfl) ⟨230381, by rfl⟩ : syracuseStep 307175 = 460763) B460763
theorem B1028105 : Blo 303832 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B307487 : Blo 303832 307487 := bstep (se 1 (by rfl) ⟨230615, by rfl⟩ : syracuseStep 307487 = 461231) B461231
theorem B307547 : Blo 303832 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B307567 : Blo 303832 307567 := bstep (se 1 (by rfl) ⟨230675, by rfl⟩ : syracuseStep 307567 = 461351) B461351
theorem B307623 : Blo 303832 307623 := bstep (se 1 (by rfl) ⟨230717, by rfl⟩ : syracuseStep 307623 = 461435) B461435
theorem B307707 : Blo 303832 307707 := bstep (se 1 (by rfl) ⟨230780, by rfl⟩ : syracuseStep 307707 = 461561) B461561
theorem B307775 : Blo 303832 307775 := bstep (se 1 (by rfl) ⟨230831, by rfl⟩ : syracuseStep 307775 = 461663) B461663
theorem B307783 : Blo 303832 307783 := bstep (se 1 (by rfl) ⟨230837, by rfl⟩ : syracuseStep 307783 = 461675) B461675
theorem B865255 : Blo 303832 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B865529 : Blo 303832 865529 := bstep (se 2 (by rfl) ⟨324573, by rfl⟩ : syracuseStep 865529 = 649147) B649147
theorem B1390061 : Blo 303832 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B4208165 : Blo 303832 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B2963083 : Blo 303832 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B735443 : Blo 303832 735443 := bstep (se 1 (by rfl) ⟨551582, by rfl⟩ : syracuseStep 735443 = 1103165) B1103165
theorem B1128701 : Blo 303832 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B1554713 : Blo 303832 1554713 := bstep (se 2 (by rfl) ⟨583017, by rfl⟩ : syracuseStep 1554713 = 1166035) B1166035
theorem B5257547 : Blo 303832 5257547 := bstep (se 1 (by rfl) ⟨3943160, by rfl⟩ : syracuseStep 5257547 = 7886321) B7886321
theorem B188627285 : Blo 303832 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B866771 : Blo 303832 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B13187609 : Blo 303832 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B2800187 : Blo 303832 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B342751 : Blo 303832 342751 := bstep (se 1 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 342751 = 514127) B514127
theorem B1031291 : Blo 303832 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B343327 : Blo 303832 343327 := bstep (se 1 (by rfl) ⟨257495, by rfl⟩ : syracuseStep 343327 = 514991) B514991
theorem B1031561 : Blo 303832 1031561 := bstep (se 2 (by rfl) ⟨386835, by rfl⟩ : syracuseStep 1031561 = 773671) B773671
theorem B1162633 : Blo 303832 1162633 := bstep (se 2 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 1162633 = 871975) B871975
theorem B2473487 : Blo 303832 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B343615 : Blo 303832 343615 := bstep (se 1 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 343615 = 515423) B515423
theorem B868103 : Blo 303832 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B1031993 : Blo 303832 1031993 := bstep (se 2 (by rfl) ⟨386997, by rfl⟩ : syracuseStep 1031993 = 773995) B773995
theorem B4931401 : Blo 303832 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B737153 : Blo 303832 737153 := bstep (se 2 (by rfl) ⟨276432, by rfl⟩ : syracuseStep 737153 = 552865) B552865
theorem B770057 : Blo 303832 770057 := bstep (se 2 (by rfl) ⟨288771, by rfl⟩ : syracuseStep 770057 = 577543) B577543
theorem B5980175 : Blo 303832 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B770411 : Blo 303832 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B344443 : Blo 303832 344443 := bstep (se 1 (by rfl) ⟨258332, by rfl⟩ : syracuseStep 344443 = 516665) B516665
theorem B1032857 : Blo 303832 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B770735 : Blo 303832 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B1262303 : Blo 303832 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B344911 : Blo 303832 344911 := bstep (se 1 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 344911 = 517367) B517367
theorem B1557467 : Blo 303832 1557467 := bstep (se 1 (by rfl) ⟨1168100, by rfl⟩ : syracuseStep 1557467 = 2336201) B2336201
theorem B771059 : Blo 303832 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B410729 : Blo 303832 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B1557629 : Blo 303832 1557629 := bstep (se 3 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 1557629 = 584111) B584111
theorem B345307 : Blo 303832 345307 := bstep (se 1 (by rfl) ⟨258980, by rfl⟩ : syracuseStep 345307 = 517961) B517961
theorem B2639147 : Blo 303832 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B771515 : Blo 303832 771515 := bstep (se 1 (by rfl) ⟨578636, by rfl⟩ : syracuseStep 771515 = 1157273) B1157273
theorem B1557953 : Blo 303832 1557953 := bstep (se 2 (by rfl) ⟨584232, by rfl⟩ : syracuseStep 1557953 = 1168465) B1168465
theorem B2803187 : Blo 303832 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B345595 : Blo 303832 345595 := bstep (se 1 (by rfl) ⟨259196, by rfl⟩ : syracuseStep 345595 = 518393) B518393
theorem B1099271 : Blo 303832 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B345775 : Blo 303832 345775 := bstep (se 1 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 345775 = 518663) B518663
theorem B8800067 : Blo 303832 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B411599 : Blo 303832 411599 := bstep (se 1 (by rfl) ⟨308699, by rfl⟩ : syracuseStep 411599 = 617399) B617399
theorem B346063 : Blo 303832 346063 := bstep (se 1 (by rfl) ⟨259547, by rfl⟩ : syracuseStep 346063 = 519095) B519095
theorem B1034369 : Blo 303832 1034369 := bstep (se 2 (by rfl) ⟨387888, by rfl⟩ : syracuseStep 1034369 = 775777) B775777
theorem B2312387 : Blo 303832 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B9423053 : Blo 303832 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B2935075 : Blo 303832 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B1034747 : Blo 303832 1034747 := bstep (se 1 (by rfl) ⟨776060, by rfl⟩ : syracuseStep 1034747 = 1552121) B1552121
theorem B772679 : Blo 303832 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B1100395 : Blo 303832 1100395 := bstep (se 1 (by rfl) ⟨825296, by rfl⟩ : syracuseStep 1100395 = 1650593) B1650593
theorem B871019 : Blo 303832 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B871087 : Blo 303832 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B3918557 : Blo 303832 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B2607997 : Blo 303832 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B1100699 : Blo 303832 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B1035179 : Blo 303832 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B347503 : Blo 303832 347503 := bstep (se 1 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 347503 = 521255) B521255
theorem B1035719 : Blo 303832 1035719 := bstep (se 1 (by rfl) ⟨776789, by rfl⟩ : syracuseStep 1035719 = 1553579) B1553579
theorem B1036043 : Blo 303832 1036043 := bstep (se 1 (by rfl) ⟨777032, by rfl⟩ : syracuseStep 1036043 = 1554065) B1554065
theorem B773945 : Blo 303832 773945 := bstep (se 2 (by rfl) ⟨290229, by rfl⟩ : syracuseStep 773945 = 580459) B580459
theorem B1036313 : Blo 303832 1036313 := bstep (se 2 (by rfl) ⟨388617, by rfl⟩ : syracuseStep 1036313 = 777235) B777235
theorem B3461291 : Blo 303832 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B872795 : Blo 303832 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B414119 : Blo 303832 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B348743 : Blo 303832 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B5231303 : Blo 303832 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B512939 : Blo 303832 512939 := bstep (se 1 (by rfl) ⟨384704, by rfl⟩ : syracuseStep 512939 = 769409) B769409
theorem B1725497 : Blo 303832 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B775291 : Blo 303832 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B1037555 : Blo 303832 1037555 := bstep (se 1 (by rfl) ⟨778166, by rfl⟩ : syracuseStep 1037555 = 1556333) B1556333
theorem B1037663 : Blo 303832 1037663 := bstep (se 1 (by rfl) ⟨778247, by rfl⟩ : syracuseStep 1037663 = 1556495) B1556495
theorem B1660283 : Blo 303832 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B513479 : Blo 303832 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B743375 : Blo 303832 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B415849 : Blo 303832 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B514471 : Blo 303832 514471 := bstep (se 1 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 514471 = 771707) B771707
theorem B776699 : Blo 303832 776699 := bstep (se 1 (by rfl) ⟨582524, by rfl⟩ : syracuseStep 776699 = 1165049) B1165049
theorem B940607 : Blo 303832 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B514633 : Blo 303832 514633 := bstep (se 2 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 514633 = 385975) B385975
theorem B514667 : Blo 303832 514667 := bstep (se 1 (by rfl) ⟨386000, by rfl⟩ : syracuseStep 514667 = 772001) B772001
theorem B2612645 : Blo 303832 2612645 := bstep (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) B489871
theorem B777671 : Blo 303832 777671 := bstep (se 1 (by rfl) ⟨583253, by rfl⟩ : syracuseStep 777671 = 1166507) B1166507
theorem B777721 : Blo 303832 777721 := bstep (se 2 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 777721 = 583291) B583291
theorem B2940421 : Blo 303832 2940421 := bstep (se 4 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 2940421 = 551329) B551329
theorem B384583 : Blo 303832 384583 := bstep (se 1 (by rfl) ⟨288437, by rfl⟩ : syracuseStep 384583 = 576875) B576875
theorem B5889833 : Blo 303832 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B778025 : Blo 303832 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B581431 : Blo 303832 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B1466369 : Blo 303832 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B778369 : Blo 303832 778369 := bstep (se 2 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 778369 = 583777) B583777
theorem B516361 : Blo 303832 516361 := bstep (se 2 (by rfl) ⟨193635, by rfl⟩ : syracuseStep 516361 = 387271) B387271
theorem B975361 : Blo 303832 975361 := bstep (se 2 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 975361 = 731521) B731521
theorem B746003 : Blo 303832 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B582319 : Blo 303832 582319 := bstep (se 1 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 582319 = 873479) B873479
theorem B779179 : Blo 303832 779179 := bstep (se 1 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 779179 = 1168769) B1168769
theorem B1860545 : Blo 303832 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B5235677 : Blo 303832 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B975847 : Blo 303832 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B582889 : Blo 303832 582889 := bstep (se 2 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 582889 = 437167) B437167
theorem B1303847 : Blo 303832 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1992023 : Blo 303832 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1402217 : Blo 303832 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B1303931 : Blo 303832 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B386471 : Blo 303832 386471 := bstep (se 1 (by rfl) ⟨289853, by rfl⟩ : syracuseStep 386471 = 579707) B579707
theorem B386623 : Blo 303832 386623 := bstep (se 1 (by rfl) ⟨289967, by rfl⟩ : syracuseStep 386623 = 579935) B579935
theorem B517819 : Blo 303832 517819 := bstep (se 1 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 517819 = 776729) B776729
theorem B386795 : Blo 303832 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B1468367 : Blo 303832 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B2320649 : Blo 303832 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B584263 : Blo 303832 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B2943611 : Blo 303832 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B387767 : Blo 303832 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B518879 : Blo 303832 518879 := bstep (se 1 (by rfl) ⟨389159, by rfl⟩ : syracuseStep 518879 = 778319) B778319
theorem B387919 : Blo 303832 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B519311 : Blo 303832 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B1666585 : Blo 303832 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B683783 : Blo 303832 683783 := bstep (se 1 (by rfl) ⟨512837, by rfl⟩ : syracuseStep 683783 = 1025675) B1025675
theorem B23949107 : Blo 303832 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1470383 : Blo 303832 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B4255811 : Blo 303832 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B684395 : Blo 303832 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B684539 : Blo 303832 684539 := bstep (se 1 (by rfl) ⟨513404, by rfl⟩ : syracuseStep 684539 = 1026809) B1026809
theorem B684665 : Blo 303832 684665 := bstep (se 2 (by rfl) ⟨256749, by rfl⟩ : syracuseStep 684665 = 513499) B513499
theorem B684719 : Blo 303832 684719 := bstep (se 1 (by rfl) ⟨513539, by rfl⟩ : syracuseStep 684719 = 1027079) B1027079
theorem B389815 : Blo 303832 389815 := bstep (se 1 (by rfl) ⟨292361, by rfl⟩ : syracuseStep 389815 = 584723) B584723
theorem B684791 : Blo 303832 684791 := bstep (se 1 (by rfl) ⟨513593, by rfl⟩ : syracuseStep 684791 = 1027187) B1027187
theorem B684971 : Blo 303832 684971 := bstep (se 1 (by rfl) ⟨513728, by rfl⟩ : syracuseStep 684971 = 1027457) B1027457
theorem B455975 : Blo 303832 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B1307947 : Blo 303832 1307947 := bstep (se 1 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 1307947 = 1961921) B1961921
theorem B2618729 : Blo 303832 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B456059 : Blo 303832 456059 := bstep (se 1 (by rfl) ⟨342044, by rfl⟩ : syracuseStep 456059 = 684089) B684089
theorem B685511 : Blo 303832 685511 := bstep (se 1 (by rfl) ⟨514133, by rfl⟩ : syracuseStep 685511 = 1028267) B1028267
theorem B456185 : Blo 303832 456185 := bstep (se 2 (by rfl) ⟨171069, by rfl⟩ : syracuseStep 456185 = 342139) B342139
theorem B1472057 : Blo 303832 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B456287 : Blo 303832 456287 := bstep (se 1 (by rfl) ⟨342215, by rfl⟩ : syracuseStep 456287 = 684431) B684431
theorem B685871 : Blo 303832 685871 := bstep (se 1 (by rfl) ⟨514403, by rfl⟩ : syracuseStep 685871 = 1028807) B1028807
theorem B456503 : Blo 303832 456503 := bstep (se 1 (by rfl) ⟨342377, by rfl⟩ : syracuseStep 456503 = 684755) B684755
theorem B18708317 : Blo 303832 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B456809 : Blo 303832 456809 := bstep (se 2 (by rfl) ⟨171303, by rfl⟩ : syracuseStep 456809 = 342607) B342607
theorem B489577 : Blo 303832 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B522587 : Blo 303832 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B686447 : Blo 303832 686447 := bstep (se 1 (by rfl) ⟨514835, by rfl⟩ : syracuseStep 686447 = 1029671) B1029671
theorem B457127 : Blo 303832 457127 := bstep (se 1 (by rfl) ⟨342845, by rfl⟩ : syracuseStep 457127 = 685691) B685691
theorem B686519 : Blo 303832 686519 := bstep (se 1 (by rfl) ⟨514889, by rfl⟩ : syracuseStep 686519 = 1029779) B1029779
theorem B457211 : Blo 303832 457211 := bstep (se 1 (by rfl) ⟨342908, by rfl⟩ : syracuseStep 457211 = 685817) B685817
theorem B686663 : Blo 303832 686663 := bstep (se 1 (by rfl) ⟨514997, by rfl⟩ : syracuseStep 686663 = 1029995) B1029995
theorem B686699 : Blo 303832 686699 := bstep (se 1 (by rfl) ⟨515024, by rfl⟩ : syracuseStep 686699 = 1030049) B1030049
theorem B457337 : Blo 303832 457337 := bstep (se 2 (by rfl) ⟨171501, by rfl⟩ : syracuseStep 457337 = 343003) B343003
theorem B457391 : Blo 303832 457391 := bstep (se 1 (by rfl) ⟨343043, by rfl⟩ : syracuseStep 457391 = 686087) B686087
theorem B981679 : Blo 303832 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B457439 : Blo 303832 457439 := bstep (se 1 (by rfl) ⟨343079, by rfl⟩ : syracuseStep 457439 = 686159) B686159
theorem B457703 : Blo 303832 457703 := bstep (se 1 (by rfl) ⟨343277, by rfl⟩ : syracuseStep 457703 = 686555) B686555
theorem B687095 : Blo 303832 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B457961 : Blo 303832 457961 := bstep (se 2 (by rfl) ⟨171735, by rfl⟩ : syracuseStep 457961 = 343471) B343471
theorem B458015 : Blo 303832 458015 := bstep (se 1 (by rfl) ⟨343511, by rfl⟩ : syracuseStep 458015 = 687023) B687023
theorem B687455 : Blo 303832 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B982459 : Blo 303832 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B458183 : Blo 303832 458183 := bstep (se 1 (by rfl) ⟨343637, by rfl⟩ : syracuseStep 458183 = 687275) B687275
theorem B654905 : Blo 303832 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B3472955 : Blo 303832 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B687851 : Blo 303832 687851 := bstep (se 1 (by rfl) ⟨515888, by rfl⟩ : syracuseStep 687851 = 1031777) B1031777
theorem B524011 : Blo 303832 524011 := bstep (se 1 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 524011 = 786017) B786017
theorem B458537 : Blo 303832 458537 := bstep (se 2 (by rfl) ⟨171951, by rfl⟩ : syracuseStep 458537 = 343903) B343903
theorem B458543 : Blo 303832 458543 := bstep (se 1 (by rfl) ⟨343907, by rfl⟩ : syracuseStep 458543 = 687815) B687815
theorem B687977 : Blo 303832 687977 := bstep (se 2 (by rfl) ⟨257991, by rfl⟩ : syracuseStep 687977 = 515983) B515983
theorem B688481 : Blo 303832 688481 := bstep (se 2 (by rfl) ⟨258180, by rfl⟩ : syracuseStep 688481 = 516361) B516361
theorem B688571 : Blo 303832 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B459215 : Blo 303832 459215 := bstep (se 1 (by rfl) ⟨344411, by rfl⟩ : syracuseStep 459215 = 688823) B688823
theorem B459257 : Blo 303832 459257 := bstep (se 2 (by rfl) ⟨172221, by rfl⟩ : syracuseStep 459257 = 344443) B344443
theorem B459359 : Blo 303832 459359 := bstep (se 1 (by rfl) ⟨344519, by rfl⟩ : syracuseStep 459359 = 689039) B689039
theorem B1049195 : Blo 303832 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B9011897 : Blo 303832 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B2327453 : Blo 303832 2327453 := bstep (se 3 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 2327453 = 872795) B872795
theorem B2622455 : Blo 303832 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B459839 : Blo 303832 459839 := bstep (se 1 (by rfl) ⟨344879, by rfl⟩ : syracuseStep 459839 = 689759) B689759
theorem B459881 : Blo 303832 459881 := bstep (se 2 (by rfl) ⟨172455, by rfl⟩ : syracuseStep 459881 = 344911) B344911
theorem B984253 : Blo 303832 984253 := bstep (se 3 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 984253 = 369095) B369095
theorem B459983 : Blo 303832 459983 := bstep (se 1 (by rfl) ⟨344987, by rfl⟩ : syracuseStep 459983 = 689975) B689975
theorem B5866711 : Blo 303832 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B1049993 : Blo 303832 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B460187 : Blo 303832 460187 := bstep (se 1 (by rfl) ⟨345140, by rfl⟩ : syracuseStep 460187 = 690281) B690281
theorem B689579 : Blo 303832 689579 := bstep (se 1 (by rfl) ⟨517184, by rfl⟩ : syracuseStep 689579 = 1034369) B1034369
theorem B1541591 : Blo 303832 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B4392467 : Blo 303832 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B1115731 : Blo 303832 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B460409 : Blo 303832 460409 := bstep (se 2 (by rfl) ⟨172653, by rfl⟩ : syracuseStep 460409 = 345307) B345307
theorem B689831 : Blo 303832 689831 := bstep (se 1 (by rfl) ⟨517373, by rfl⟩ : syracuseStep 689831 = 1034747) B1034747
theorem B460511 : Blo 303832 460511 := bstep (se 1 (by rfl) ⟨345383, by rfl⟩ : syracuseStep 460511 = 690767) B690767
theorem B460607 : Blo 303832 460607 := bstep (se 1 (by rfl) ⟨345455, by rfl⟩ : syracuseStep 460607 = 690911) B690911
theorem B690119 : Blo 303832 690119 := bstep (se 1 (by rfl) ⟨517589, by rfl⟩ : syracuseStep 690119 = 1035179) B1035179
theorem B460775 : Blo 303832 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B460793 : Blo 303832 460793 := bstep (se 2 (by rfl) ⟨172797, by rfl⟩ : syracuseStep 460793 = 345595) B345595
theorem B460895 : Blo 303832 460895 := bstep (se 1 (by rfl) ⟨345671, by rfl⟩ : syracuseStep 460895 = 691343) B691343
theorem B460955 : Blo 303832 460955 := bstep (se 1 (by rfl) ⟨345716, by rfl⟩ : syracuseStep 460955 = 691433) B691433
theorem B460991 : Blo 303832 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B461033 : Blo 303832 461033 := bstep (se 2 (by rfl) ⟨172887, by rfl⟩ : syracuseStep 461033 = 345775) B345775
theorem B690425 : Blo 303832 690425 := bstep (se 2 (by rfl) ⟨258909, by rfl⟩ : syracuseStep 690425 = 517819) B517819
theorem B690479 : Blo 303832 690479 := bstep (se 1 (by rfl) ⟨517859, by rfl⟩ : syracuseStep 690479 = 1035719) B1035719
theorem B985483 : Blo 303832 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B690695 : Blo 303832 690695 := bstep (se 1 (by rfl) ⟨518021, by rfl⟩ : syracuseStep 690695 = 1036043) B1036043
theorem B461339 : Blo 303832 461339 := bstep (se 1 (by rfl) ⟨346004, by rfl⟩ : syracuseStep 461339 = 692009) B692009
theorem B461417 : Blo 303832 461417 := bstep (se 2 (by rfl) ⟨173031, by rfl⟩ : syracuseStep 461417 = 346063) B346063
theorem B690875 : Blo 303832 690875 := bstep (se 1 (by rfl) ⟨518156, by rfl⟩ : syracuseStep 690875 = 1036313) B1036313
theorem B986087 : Blo 303832 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B1150331 : Blo 303832 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B691703 : Blo 303832 691703 := bstep (se 1 (by rfl) ⟨518777, by rfl⟩ : syracuseStep 691703 = 1037555) B1037555
theorem B691775 : Blo 303832 691775 := bstep (se 1 (by rfl) ⟨518831, by rfl⟩ : syracuseStep 691775 = 1037663) B1037663
theorem B659017 : Blo 303832 659017 := bstep (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) B494263
theorem B3477329 : Blo 303832 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B3706829 : Blo 303832 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B7475165 : Blo 303832 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B627071 : Blo 303832 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B463337 : Blo 303832 463337 := bstep (se 2 (by rfl) ⟨173751, by rfl⟩ : syracuseStep 463337 = 347503) B347503
theorem B1643111 : Blo 303832 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B2626451 : Blo 303832 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B1741763 : Blo 303832 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B4199633 : Blo 303832 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B497335 : Blo 303832 497335 := bstep (se 1 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 497335 = 746003) B746003
theorem B2234567 : Blo 303832 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B465191 : Blo 303832 465191 := bstep (se 1 (by rfl) ⟨348893, by rfl⟩ : syracuseStep 465191 = 697787) B697787
theorem B1153673 : Blo 303832 1153673 := bstep (se 2 (by rfl) ⟨432627, by rfl⟩ : syracuseStep 1153673 = 865255) B865255
theorem B1547099 : Blo 303832 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1743929 : Blo 303832 1743929 := bstep (se 2 (by rfl) ⟨653973, by rfl⟩ : syracuseStep 1743929 = 1307947) B1307947
theorem B1186963 : Blo 303832 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B3349991 : Blo 303832 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B15966071 : Blo 303832 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B303983 : Blo 303832 303983 := bstep (se 1 (by rfl) ⟨227987, by rfl⟩ : syracuseStep 303983 = 455975) B455975
theorem B1745819 : Blo 303832 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B304039 : Blo 303832 304039 := bstep (se 1 (by rfl) ⟨228029, by rfl⟩ : syracuseStep 304039 = 456059) B456059
theorem B304123 : Blo 303832 304123 := bstep (se 1 (by rfl) ⟨228092, by rfl⟩ : syracuseStep 304123 = 456185) B456185
theorem B304191 : Blo 303832 304191 := bstep (se 1 (by rfl) ⟨228143, by rfl⟩ : syracuseStep 304191 = 456287) B456287
theorem B304335 : Blo 303832 304335 := bstep (se 1 (by rfl) ⟨228251, by rfl⟩ : syracuseStep 304335 = 456503) B456503
theorem B304539 : Blo 303832 304539 := bstep (se 1 (by rfl) ⟨228404, by rfl⟩ : syracuseStep 304539 = 456809) B456809
theorem B304751 : Blo 303832 304751 := bstep (se 1 (by rfl) ⟨228563, by rfl⟩ : syracuseStep 304751 = 457127) B457127
theorem B304807 : Blo 303832 304807 := bstep (se 1 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 304807 = 457211) B457211
theorem B8791739 : Blo 303832 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B304891 : Blo 303832 304891 := bstep (se 1 (by rfl) ⟨228668, by rfl⟩ : syracuseStep 304891 = 457337) B457337
theorem B304927 : Blo 303832 304927 := bstep (se 1 (by rfl) ⟨228695, by rfl⟩ : syracuseStep 304927 = 457391) B457391
theorem B304959 : Blo 303832 304959 := bstep (se 1 (by rfl) ⟨228719, by rfl⟩ : syracuseStep 304959 = 457439) B457439
theorem B1550177 : Blo 303832 1550177 := bstep (se 2 (by rfl) ⟨581316, by rfl⟩ : syracuseStep 1550177 = 1162633) B1162633
theorem B305135 : Blo 303832 305135 := bstep (se 1 (by rfl) ⟨228851, by rfl⟩ : syracuseStep 305135 = 457703) B457703
theorem B305307 : Blo 303832 305307 := bstep (se 1 (by rfl) ⟨228980, by rfl⟩ : syracuseStep 305307 = 457961) B457961
theorem B305343 : Blo 303832 305343 := bstep (se 1 (by rfl) ⟨229007, by rfl⟩ : syracuseStep 305343 = 458015) B458015
theorem B305455 : Blo 303832 305455 := bstep (se 1 (by rfl) ⟨229091, by rfl⟩ : syracuseStep 305455 = 458183) B458183
theorem B698681 : Blo 303832 698681 := bstep (se 2 (by rfl) ⟨262005, by rfl⟩ : syracuseStep 698681 = 524011) B524011
theorem B1648991 : Blo 303832 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B436603 : Blo 303832 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B305691 : Blo 303832 305691 := bstep (se 1 (by rfl) ⟨229268, by rfl⟩ : syracuseStep 305691 = 458537) B458537
theorem B305695 : Blo 303832 305695 := bstep (se 1 (by rfl) ⟨229271, by rfl⟩ : syracuseStep 305695 = 458543) B458543
theorem B306011 : Blo 303832 306011 := bstep (se 1 (by rfl) ⟨229508, by rfl⟩ : syracuseStep 306011 = 459017) B459017
theorem B306079 : Blo 303832 306079 := bstep (se 1 (by rfl) ⟨229559, by rfl⟩ : syracuseStep 306079 = 459119) B459119
theorem B306223 : Blo 303832 306223 := bstep (se 1 (by rfl) ⟨229667, by rfl⟩ : syracuseStep 306223 = 459335) B459335
theorem B306247 : Blo 303832 306247 := bstep (se 1 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 306247 = 459371) B459371
theorem B1027295 : Blo 303832 1027295 := bstep (se 1 (by rfl) ⟨770471, by rfl⟩ : syracuseStep 1027295 = 1540943) B1540943
theorem B306399 : Blo 303832 306399 := bstep (se 1 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 306399 = 459599) B459599
theorem B1027511 : Blo 303832 1027511 := bstep (se 1 (by rfl) ⟨770633, by rfl⟩ : syracuseStep 1027511 = 1541267) B1541267
theorem B306663 : Blo 303832 306663 := bstep (se 1 (by rfl) ⟨229997, by rfl⟩ : syracuseStep 306663 = 459995) B459995
theorem B306779 : Blo 303832 306779 := bstep (se 1 (by rfl) ⟨230084, by rfl⟩ : syracuseStep 306779 = 460169) B460169
theorem B732847 : Blo 303832 732847 := bstep (se 1 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 732847 = 1099271) B1099271
theorem B307015 : Blo 303832 307015 := bstep (se 1 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 307015 = 460523) B460523
theorem B1552283 : Blo 303832 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B307167 : Blo 303832 307167 := bstep (se 1 (by rfl) ⟨230375, by rfl⟩ : syracuseStep 307167 = 460751) B460751
theorem B929981 : Blo 303832 929981 := bstep (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) B348743
theorem B307431 : Blo 303832 307431 := bstep (se 1 (by rfl) ⟨230573, by rfl⟩ : syracuseStep 307431 = 461147) B461147
theorem B307583 : Blo 303832 307583 := bstep (se 1 (by rfl) ⟨230687, by rfl⟩ : syracuseStep 307583 = 461375) B461375
theorem B307663 : Blo 303832 307663 := bstep (se 1 (by rfl) ⟨230747, by rfl⟩ : syracuseStep 307663 = 461495) B461495
theorem B733799 : Blo 303832 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B307815 : Blo 303832 307815 := bstep (se 1 (by rfl) ⟨230861, by rfl⟩ : syracuseStep 307815 = 461723) B461723
theorem B3912407 : Blo 303832 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1029563 : Blo 303832 1029563 := bstep (se 1 (by rfl) ⟨772172, by rfl⟩ : syracuseStep 1029563 = 1544345) B1544345
theorem B2307527 : Blo 303832 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B1095277 : Blo 303832 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B1750693 : Blo 303832 1750693 := bstep (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) B328255
theorem B3913433 : Blo 303832 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B3487535 : Blo 303832 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B341959 : Blo 303832 341959 := bstep (se 1 (by rfl) ⟨256469, by rfl⟩ : syracuseStep 341959 = 512939) B512939
theorem B1030103 : Blo 303832 1030103 := bstep (se 1 (by rfl) ⟨772577, by rfl⟩ : syracuseStep 1030103 = 1545155) B1545155
theorem B1161449 : Blo 303832 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B1161479 : Blo 303832 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B342319 : Blo 303832 342319 := bstep (se 1 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 342319 = 513479) B513479
theorem B1030589 : Blo 303832 1030589 := bstep (se 3 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 1030589 = 386471) B386471
theorem B343111 : Blo 303832 343111 := bstep (se 1 (by rfl) ⟨257333, by rfl⟩ : syracuseStep 343111 = 514667) B514667
theorem B1031453 : Blo 303832 1031453 := bstep (se 3 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 1031453 = 386795) B386795
theorem B1326365 : Blo 303832 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B1752425 : Blo 303832 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B769783 : Blo 303832 769783 := bstep (se 1 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 769783 = 1154675) B1154675
theorem B1097597 : Blo 303832 1097597 := bstep (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) B411599
theorem B1982333 : Blo 303832 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B770087 : Blo 303832 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B1032479 : Blo 303832 1032479 := bstep (se 1 (by rfl) ⟨774359, by rfl⟩ : syracuseStep 1032479 = 1548719) B1548719
theorem B3490451 : Blo 303832 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B869231 : Blo 303832 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B1328015 : Blo 303832 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B934811 : Blo 303832 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B869287 : Blo 303832 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B1033127 : Blo 303832 1033127 := bstep (se 1 (by rfl) ⟨774845, by rfl⟩ : syracuseStep 1033127 = 1549691) B1549691
theorem B443599 : Blo 303832 443599 := bstep (se 1 (by rfl) ⟨332699, by rfl⟩ : syracuseStep 443599 = 665399) B665399
theorem B1033721 : Blo 303832 1033721 := bstep (se 2 (by rfl) ⟨387645, by rfl⟩ : syracuseStep 1033721 = 775291) B775291
theorem B1033991 : Blo 303832 1033991 := bstep (se 1 (by rfl) ⟨775493, by rfl⟩ : syracuseStep 1033991 = 1550987) B1550987
theorem B1034045 : Blo 303832 1034045 := bstep (se 3 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 1034045 = 387767) B387767
theorem B345919 : Blo 303832 345919 := bstep (se 1 (by rfl) ⟨259439, by rfl⟩ : syracuseStep 345919 = 518879) B518879
theorem B346207 : Blo 303832 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B3950777 : Blo 303832 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B2837207 : Blo 303832 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B577019 : Blo 303832 577019 := bstep (se 1 (by rfl) ⟨432764, by rfl⟩ : syracuseStep 577019 = 865529) B865529
theorem B2805443 : Blo 303832 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B12472211 : Blo 303832 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B1036475 : Blo 303832 1036475 := bstep (se 1 (by rfl) ⟨777356, by rfl⟩ : syracuseStep 1036475 = 1554713) B1554713
theorem B125751523 : Blo 303832 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B348391 : Blo 303832 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B577847 : Blo 303832 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B1036961 : Blo 303832 1036961 := bstep (se 2 (by rfl) ⟨388860, by rfl⟩ : syracuseStep 1036961 = 777721) B777721
theorem B3920561 : Blo 303832 3920561 := bstep (se 2 (by rfl) ⟨1470210, by rfl⟩ : syracuseStep 3920561 = 2940421) B2940421
theorem B512777 : Blo 303832 512777 := bstep (se 2 (by rfl) ⟨192291, by rfl⟩ : syracuseStep 512777 = 384583) B384583
theorem B2315303 : Blo 303832 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B775241 : Blo 303832 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B6575201 : Blo 303832 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B578735 : Blo 303832 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B513371 : Blo 303832 513371 := bstep (se 1 (by rfl) ⟨385028, by rfl⟩ : syracuseStep 513371 = 770057) B770057
theorem B3986783 : Blo 303832 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B1037825 : Blo 303832 1037825 := bstep (se 2 (by rfl) ⟨389184, by rfl⟩ : syracuseStep 1037825 = 778369) B778369
theorem B513607 : Blo 303832 513607 := bstep (se 1 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 513607 = 770411) B770411
theorem B349915 : Blo 303832 349915 := bstep (se 1 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 349915 = 524873) B524873
theorem B513823 : Blo 303832 513823 := bstep (se 1 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 513823 = 770735) B770735
theorem B841535 : Blo 303832 841535 := bstep (se 1 (by rfl) ⟨631151, by rfl⟩ : syracuseStep 841535 = 1262303) B1262303
theorem B1038311 : Blo 303832 1038311 := bstep (se 1 (by rfl) ⟨778733, by rfl⟩ : syracuseStep 1038311 = 1557467) B1557467
theorem B514039 : Blo 303832 514039 := bstep (se 1 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 514039 = 771059) B771059
theorem B1300481 : Blo 303832 1300481 := bstep (se 2 (by rfl) ⟨487680, by rfl⟩ : syracuseStep 1300481 = 975361) B975361
theorem B1038419 : Blo 303832 1038419 := bstep (se 1 (by rfl) ⟨778814, by rfl⟩ : syracuseStep 1038419 = 1557629) B1557629
theorem B776425 : Blo 303832 776425 := bstep (se 2 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 776425 = 582319) B582319
theorem B514343 : Blo 303832 514343 := bstep (se 1 (by rfl) ⟨385757, by rfl⟩ : syracuseStep 514343 = 771515) B771515
theorem B1038635 : Blo 303832 1038635 := bstep (se 1 (by rfl) ⟨778976, by rfl⟩ : syracuseStep 1038635 = 1557953) B1557953
theorem B1104317 : Blo 303832 1104317 := bstep (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) B414119
theorem B1038905 : Blo 303832 1038905 := bstep (se 2 (by rfl) ⟨389589, by rfl⟩ : syracuseStep 1038905 = 779179) B779179
theorem B1301129 : Blo 303832 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B50420465 : Blo 303832 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B6282035 : Blo 303832 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B416603 : Blo 303832 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B777185 : Blo 303832 777185 := bstep (se 2 (by rfl) ⟨291444, by rfl⟩ : syracuseStep 777185 = 582889) B582889
theorem B515119 : Blo 303832 515119 := bstep (se 1 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 515119 = 772679) B772679
theorem B580679 : Blo 303832 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B2612371 : Blo 303832 2612371 := bstep (se 1 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 2612371 = 3918557) B3918557
theorem B875735 : Blo 303832 875735 := bstep (se 1 (by rfl) ⟨656801, by rfl⟩ : syracuseStep 875735 = 1313603) B1313603
theorem B515497 : Blo 303832 515497 := bstep (se 2 (by rfl) ⟨193311, by rfl⟩ : syracuseStep 515497 = 386623) B386623
theorem B4382201 : Blo 303832 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B1760777 : Blo 303832 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B515963 : Blo 303832 515963 := bstep (se 1 (by rfl) ⟨386972, by rfl⟩ : syracuseStep 515963 = 773945) B773945
theorem B779017 : Blo 303832 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B7037725 : Blo 303832 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B1467193 : Blo 303832 1467193 := bstep (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) B1100395
theorem B1106855 : Blo 303832 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B517225 : Blo 303832 517225 := bstep (se 2 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 517225 = 387919) B387919
theorem B8316053 : Blo 303832 8316053 := bstep (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) B389815
theorem B550471 : Blo 303832 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B517799 : Blo 303832 517799 := bstep (se 1 (by rfl) ⟨388349, by rfl⟩ : syracuseStep 517799 = 776699) B776699
theorem B2222113 : Blo 303832 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B518447 : Blo 303832 518447 := bstep (se 1 (by rfl) ⟨388835, by rfl⟩ : syracuseStep 518447 = 777671) B777671
theorem B1862027 : Blo 303832 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B977309 : Blo 303832 977309 := bstep (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) B366491
theorem B3926555 : Blo 303832 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B518683 : Blo 303832 518683 := bstep (se 1 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 518683 = 778025) B778025
theorem B977579 : Blo 303832 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B617593 : Blo 303832 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B1240363 : Blo 303832 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B3009869 : Blo 303832 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B683999 : Blo 303832 683999 := bstep (se 1 (by rfl) ⟨512999, by rfl⟩ : syracuseStep 683999 = 1025999) B1025999
theorem B978911 : Blo 303832 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B27324533 : Blo 303832 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B1962407 : Blo 303832 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B619103 : Blo 303832 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B684647 : Blo 303832 684647 := bstep (se 1 (by rfl) ⟨513485, by rfl⟩ : syracuseStep 684647 = 1026971) B1026971
theorem B1733471 : Blo 303832 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B488359 : Blo 303832 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B7435253 : Blo 303832 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B455855 : Blo 303832 455855 := bstep (se 1 (by rfl) ⟨341891, by rfl⟩ : syracuseStep 455855 = 683783) B683783
theorem B26572049 : Blo 303832 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B685331 : Blo 303832 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B980255 : Blo 303832 980255 := bstep (se 1 (by rfl) ⟨735191, by rfl⟩ : syracuseStep 980255 = 1470383) B1470383
theorem B685403 : Blo 303832 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B652769 : Blo 303832 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B554465 : Blo 303832 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B456263 : Blo 303832 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B456359 : Blo 303832 456359 := bstep (se 1 (by rfl) ⟨342269, by rfl⟩ : syracuseStep 456359 = 684539) B684539
theorem B456443 : Blo 303832 456443 := bstep (se 1 (by rfl) ⟨342332, by rfl⟩ : syracuseStep 456443 = 684665) B684665
theorem B456479 : Blo 303832 456479 := bstep (se 1 (by rfl) ⟨342359, by rfl⟩ : syracuseStep 456479 = 684719) B684719
theorem B456527 : Blo 303832 456527 := bstep (se 1 (by rfl) ⟨342395, by rfl⟩ : syracuseStep 456527 = 684791) B684791
theorem B685961 : Blo 303832 685961 := bstep (se 2 (by rfl) ⟨257235, by rfl⟩ : syracuseStep 685961 = 514471) B514471
theorem B456647 : Blo 303832 456647 := bstep (se 1 (by rfl) ⟨342485, by rfl⟩ : syracuseStep 456647 = 684971) B684971
theorem B686177 : Blo 303832 686177 := bstep (se 2 (by rfl) ⟨257316, by rfl⟩ : syracuseStep 686177 = 514633) B514633
theorem B8485013 : Blo 303832 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B1308905 : Blo 303832 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B457001 : Blo 303832 457001 := bstep (se 2 (by rfl) ⟨171375, by rfl⟩ : syracuseStep 457001 = 342751) B342751
theorem B457007 : Blo 303832 457007 := bstep (se 1 (by rfl) ⟨342755, by rfl⟩ : syracuseStep 457007 = 685511) B685511
theorem B981371 : Blo 303832 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B457247 : Blo 303832 457247 := bstep (se 1 (by rfl) ⟨342935, by rfl⟩ : syracuseStep 457247 = 685871) B685871
theorem B490295 : Blo 303832 490295 := bstep (se 1 (by rfl) ⟨367721, by rfl⟩ : syracuseStep 490295 = 735443) B735443
theorem B3505031 : Blo 303832 3505031 := bstep (se 1 (by rfl) ⟨2628773, by rfl⟩ : syracuseStep 3505031 = 5257547) B5257547
theorem B457631 : Blo 303832 457631 := bstep (se 1 (by rfl) ⟨343223, by rfl⟩ : syracuseStep 457631 = 686447) B686447
theorem B457679 : Blo 303832 457679 := bstep (se 1 (by rfl) ⟨343259, by rfl⟩ : syracuseStep 457679 = 686519) B686519
theorem B1866791 : Blo 303832 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B457769 : Blo 303832 457769 := bstep (se 2 (by rfl) ⟨171663, by rfl⟩ : syracuseStep 457769 = 343327) B343327
theorem B457775 : Blo 303832 457775 := bstep (se 1 (by rfl) ⟨343331, by rfl⟩ : syracuseStep 457775 = 686663) B686663
theorem B457799 : Blo 303832 457799 := bstep (se 1 (by rfl) ⟨343349, by rfl⟩ : syracuseStep 457799 = 686699) B686699
theorem B1539161 : Blo 303832 1539161 := bstep (se 2 (by rfl) ⟨577185, by rfl⟩ : syracuseStep 1539161 = 1154371) B1154371
theorem B1309945 : Blo 303832 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B458063 : Blo 303832 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B687527 : Blo 303832 687527 := bstep (se 1 (by rfl) ⟨515645, by rfl⟩ : syracuseStep 687527 = 1031291) B1031291
theorem B458153 : Blo 303832 458153 := bstep (se 2 (by rfl) ⟨171807, by rfl⟩ : syracuseStep 458153 = 343615) B343615
theorem B458303 : Blo 303832 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B687707 : Blo 303832 687707 := bstep (se 1 (by rfl) ⟨515780, by rfl⟩ : syracuseStep 687707 = 1031561) B1031561
theorem B1539809 : Blo 303832 1539809 := bstep (se 2 (by rfl) ⟨577428, by rfl⟩ : syracuseStep 1539809 = 1154857) B1154857
theorem B458567 : Blo 303832 458567 := bstep (se 1 (by rfl) ⟨343925, by rfl⟩ : syracuseStep 458567 = 687851) B687851
theorem B687995 : Blo 303832 687995 := bstep (se 1 (by rfl) ⟨515996, by rfl⟩ : syracuseStep 687995 = 1031993) B1031993
theorem B458651 : Blo 303832 458651 := bstep (se 1 (by rfl) ⟨343988, by rfl⟩ : syracuseStep 458651 = 687977) B687977
theorem B491435 : Blo 303832 491435 := bstep (se 1 (by rfl) ⟨368576, by rfl⟩ : syracuseStep 491435 = 737153) B737153
theorem B688319 : Blo 303832 688319 := bstep (se 1 (by rfl) ⟨516239, by rfl⟩ : syracuseStep 688319 = 1032479) B1032479
theorem B458987 : Blo 303832 458987 := bstep (se 1 (by rfl) ⟨344240, by rfl⟩ : syracuseStep 458987 = 688481) B688481
theorem B459047 : Blo 303832 459047 := bstep (se 1 (by rfl) ⟨344285, by rfl⟩ : syracuseStep 459047 = 688571) B688571
theorem B2326967 : Blo 303832 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B885343 : Blo 303832 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B623207 : Blo 303832 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B688751 : Blo 303832 688751 := bstep (se 1 (by rfl) ⟨516563, by rfl⟩ : syracuseStep 688751 = 1033127) B1033127
theorem B459719 : Blo 303832 459719 := bstep (se 1 (by rfl) ⟨344789, by rfl⟩ : syracuseStep 459719 = 689579) B689579
theorem B689147 : Blo 303832 689147 := bstep (se 1 (by rfl) ⟨516860, by rfl⟩ : syracuseStep 689147 = 1033721) B1033721
theorem B459887 : Blo 303832 459887 := bstep (se 1 (by rfl) ⟨344915, by rfl⟩ : syracuseStep 459887 = 689831) B689831
theorem B689327 : Blo 303832 689327 := bstep (se 1 (by rfl) ⟨516995, by rfl⟩ : syracuseStep 689327 = 1033991) B1033991
theorem B689363 : Blo 303832 689363 := bstep (se 1 (by rfl) ⟨517022, by rfl⟩ : syracuseStep 689363 = 1034045) B1034045
theorem B460079 : Blo 303832 460079 := bstep (se 1 (by rfl) ⟨345059, by rfl⟩ : syracuseStep 460079 = 690119) B690119
theorem B689633 : Blo 303832 689633 := bstep (se 2 (by rfl) ⟨258612, by rfl⟩ : syracuseStep 689633 = 517225) B517225
theorem B460283 : Blo 303832 460283 := bstep (se 1 (by rfl) ⟨345212, by rfl⟩ : syracuseStep 460283 = 690425) B690425
theorem B460319 : Blo 303832 460319 := bstep (se 1 (by rfl) ⟨345239, by rfl⟩ : syracuseStep 460319 = 690479) B690479
theorem B1312337 : Blo 303832 1312337 := bstep (se 2 (by rfl) ⟨492126, by rfl⟩ : syracuseStep 1312337 = 984253) B984253
theorem B460463 : Blo 303832 460463 := bstep (se 1 (by rfl) ⟨345347, by rfl⟩ : syracuseStep 460463 = 690695) B690695
theorem B460583 : Blo 303832 460583 := bstep (se 1 (by rfl) ⟨345437, by rfl⟩ : syracuseStep 460583 = 690875) B690875
theorem B657391 : Blo 303832 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B461135 : Blo 303832 461135 := bstep (se 1 (by rfl) ⟨345851, by rfl⟩ : syracuseStep 461135 = 691703) B691703
theorem B461183 : Blo 303832 461183 := bstep (se 1 (by rfl) ⟨345887, by rfl⟩ : syracuseStep 461183 = 691775) B691775
theorem B461225 : Blo 303832 461225 := bstep (se 2 (by rfl) ⟨172959, by rfl⟩ : syracuseStep 461225 = 345919) B345919
theorem B1870295 : Blo 303832 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B4983443 : Blo 303832 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B690983 : Blo 303832 690983 := bstep (se 1 (by rfl) ⟨518237, by rfl⟩ : syracuseStep 690983 = 1036475) B1036475
theorem B461609 : Blo 303832 461609 := bstep (se 2 (by rfl) ⟨173103, by rfl⟩ : syracuseStep 461609 = 346207) B346207
theorem B691307 : Blo 303832 691307 := bstep (se 1 (by rfl) ⟨518480, by rfl⟩ : syracuseStep 691307 = 1036961) B1036961
theorem B1313977 : Blo 303832 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B1543535 : Blo 303832 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B691577 : Blo 303832 691577 := bstep (se 2 (by rfl) ⟨259341, by rfl⟩ : syracuseStep 691577 = 518683) B518683
theorem B2657855 : Blo 303832 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B691883 : Blo 303832 691883 := bstep (se 1 (by rfl) ⟨518912, by rfl⟩ : syracuseStep 691883 = 1037825) B1037825
theorem B561023 : Blo 303832 561023 := bstep (se 1 (by rfl) ⟨420767, by rfl⟩ : syracuseStep 561023 = 841535) B841535
theorem B1478573 : Blo 303832 1478573 := bstep (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) B554465
theorem B692207 : Blo 303832 692207 := bstep (se 1 (by rfl) ⟨519155, by rfl⟩ : syracuseStep 692207 = 1038311) B1038311
theorem B6688757 : Blo 303832 6688757 := bstep (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) B627071
theorem B692279 : Blo 303832 692279 := bstep (se 1 (by rfl) ⟨519209, by rfl⟩ : syracuseStep 692279 = 1038419) B1038419
theorem B823457 : Blo 303832 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B692423 : Blo 303832 692423 := bstep (se 1 (by rfl) ⟨519317, by rfl⟩ : syracuseStep 692423 = 1038635) B1038635
theorem B692603 : Blo 303832 692603 := bstep (se 1 (by rfl) ⟨519452, by rfl⟩ : syracuseStep 692603 = 1038905) B1038905
theorem B2233327 : Blo 303832 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2921467 : Blo 303832 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B5544035 : Blo 303832 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B6330469 : Blo 303832 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B2365861 : Blo 303832 2365861 := bstep (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) B443599
theorem B465787 : Blo 303832 465787 := bstep (se 1 (by rfl) ⟨349340, by rfl⟩ : syracuseStep 465787 = 698681) B698681
theorem B2334257 : Blo 303832 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B2006579 : Blo 303832 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B663113 : Blo 303832 663113 := bstep (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) B497335
theorem B466553 : Blo 303832 466553 := bstep (se 2 (by rfl) ⟨174957, by rfl⟩ : syracuseStep 466553 = 349915) B349915
theorem B3514757 : Blo 303832 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B1155647 : Blo 303832 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B4956835 : Blo 303832 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B303903 : Blo 303832 303903 := bstep (se 1 (by rfl) ⟨227927, by rfl⟩ : syracuseStep 303903 = 455855) B455855
theorem B435179 : Blo 303832 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B304175 : Blo 303832 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B304239 : Blo 303832 304239 := bstep (se 1 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 304239 = 456359) B456359
theorem B304295 : Blo 303832 304295 := bstep (se 1 (by rfl) ⟨228221, by rfl⟩ : syracuseStep 304295 = 456443) B456443
theorem B304319 : Blo 303832 304319 := bstep (se 1 (by rfl) ⟨228239, by rfl⟩ : syracuseStep 304319 = 456479) B456479
theorem B304351 : Blo 303832 304351 := bstep (se 1 (by rfl) ⟨228263, by rfl⟩ : syracuseStep 304351 = 456527) B456527
theorem B304431 : Blo 303832 304431 := bstep (se 1 (by rfl) ⟨228323, by rfl⟩ : syracuseStep 304431 = 456647) B456647
theorem B3483161 : Blo 303832 3483161 := bstep (se 2 (by rfl) ⟨1306185, by rfl⟩ : syracuseStep 3483161 = 2612371) B2612371
theorem B304667 : Blo 303832 304667 := bstep (se 1 (by rfl) ⟨228500, by rfl⟩ : syracuseStep 304667 = 457001) B457001
theorem B304671 : Blo 303832 304671 := bstep (se 1 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 304671 = 457007) B457007
theorem B1746593 : Blo 303832 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B304831 : Blo 303832 304831 := bstep (se 1 (by rfl) ⟨228623, by rfl⟩ : syracuseStep 304831 = 457247) B457247
theorem B2336687 : Blo 303832 2336687 := bstep (se 1 (by rfl) ⟨1752515, by rfl⟩ : syracuseStep 2336687 = 3505031) B3505031
theorem B305087 : Blo 303832 305087 := bstep (se 1 (by rfl) ⟨228815, by rfl⟩ : syracuseStep 305087 = 457631) B457631
theorem B305119 : Blo 303832 305119 := bstep (se 1 (by rfl) ⟨228839, by rfl⟩ : syracuseStep 305119 = 457679) B457679
theorem B305179 : Blo 303832 305179 := bstep (se 1 (by rfl) ⟨228884, by rfl⟩ : syracuseStep 305179 = 457769) B457769
theorem B305183 : Blo 303832 305183 := bstep (se 1 (by rfl) ⟨228887, by rfl⟩ : syracuseStep 305183 = 457775) B457775
theorem B305199 : Blo 303832 305199 := bstep (se 1 (by rfl) ⟨228899, by rfl⟩ : syracuseStep 305199 = 457799) B457799
theorem B1026107 : Blo 303832 1026107 := bstep (se 1 (by rfl) ⟨769580, by rfl⟩ : syracuseStep 1026107 = 1539161) B1539161
theorem B305375 : Blo 303832 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B305435 : Blo 303832 305435 := bstep (se 1 (by rfl) ⟨229076, by rfl⟩ : syracuseStep 305435 = 458153) B458153
theorem B1026377 : Blo 303832 1026377 := bstep (se 2 (by rfl) ⟨384891, by rfl⟩ : syracuseStep 1026377 = 769783) B769783
theorem B2926925 : Blo 303832 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B5286221 : Blo 303832 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B305535 : Blo 303832 305535 := bstep (se 1 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 305535 = 458303) B458303
theorem B1026539 : Blo 303832 1026539 := bstep (se 1 (by rfl) ⟨769904, by rfl⟩ : syracuseStep 1026539 = 1539809) B1539809
theorem B305711 : Blo 303832 305711 := bstep (se 1 (by rfl) ⟨229283, by rfl⟩ : syracuseStep 305711 = 458567) B458567
theorem B305767 : Blo 303832 305767 := bstep (se 1 (by rfl) ⟨229325, by rfl⟩ : syracuseStep 305767 = 458651) B458651
theorem B306143 : Blo 303832 306143 := bstep (se 1 (by rfl) ⟨229607, by rfl⟩ : syracuseStep 306143 = 459215) B459215
theorem B306171 : Blo 303832 306171 := bstep (se 1 (by rfl) ⟨229628, by rfl⟩ : syracuseStep 306171 = 459257) B459257
theorem B306239 : Blo 303832 306239 := bstep (se 1 (by rfl) ⟨229679, by rfl⟩ : syracuseStep 306239 = 459359) B459359
theorem B699463 : Blo 303832 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B6007931 : Blo 303832 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1551635 : Blo 303832 1551635 := bstep (se 1 (by rfl) ⟨1163726, by rfl⟩ : syracuseStep 1551635 = 2327453) B2327453
theorem B1748303 : Blo 303832 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B306559 : Blo 303832 306559 := bstep (se 1 (by rfl) ⟨229919, by rfl⟩ : syracuseStep 306559 = 459839) B459839
theorem B306587 : Blo 303832 306587 := bstep (se 1 (by rfl) ⟨229940, by rfl⟩ : syracuseStep 306587 = 459881) B459881
theorem B306655 : Blo 303832 306655 := bstep (se 1 (by rfl) ⟨229991, by rfl⟩ : syracuseStep 306655 = 459983) B459983
theorem B699995 : Blo 303832 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B306791 : Blo 303832 306791 := bstep (se 1 (by rfl) ⟨230093, by rfl⟩ : syracuseStep 306791 = 460187) B460187
theorem B1027727 : Blo 303832 1027727 := bstep (se 1 (by rfl) ⟨770795, by rfl⟩ : syracuseStep 1027727 = 1541591) B1541591
theorem B2928311 : Blo 303832 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B9383633 : Blo 303832 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B306939 : Blo 303832 306939 := bstep (se 1 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 306939 = 460409) B460409
theorem B307007 : Blo 303832 307007 := bstep (se 1 (by rfl) ⟨230255, by rfl⟩ : syracuseStep 307007 = 460511) B460511
theorem B307071 : Blo 303832 307071 := bstep (se 1 (by rfl) ⟨230303, by rfl⟩ : syracuseStep 307071 = 460607) B460607
theorem B1159049 : Blo 303832 1159049 := bstep (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) B869287
theorem B307183 : Blo 303832 307183 := bstep (se 1 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 307183 = 460775) B460775
theorem B307195 : Blo 303832 307195 := bstep (se 1 (by rfl) ⟨230396, by rfl⟩ : syracuseStep 307195 = 460793) B460793
theorem B307263 : Blo 303832 307263 := bstep (se 1 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 307263 = 460895) B460895
theorem B307303 : Blo 303832 307303 := bstep (se 1 (by rfl) ⟨230477, by rfl⟩ : syracuseStep 307303 = 460955) B460955
theorem B2633851 : Blo 303832 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B307327 : Blo 303832 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B307355 : Blo 303832 307355 := bstep (se 1 (by rfl) ⟨230516, by rfl⟩ : syracuseStep 307355 = 461033) B461033
theorem B1650941 : Blo 303832 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B307559 : Blo 303832 307559 := bstep (se 1 (by rfl) ⟨230669, by rfl⟩ : syracuseStep 307559 = 461339) B461339
theorem B307611 : Blo 303832 307611 := bstep (se 1 (by rfl) ⟨230708, by rfl⟩ : syracuseStep 307611 = 461417) B461417
theorem B733961 : Blo 303832 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1487641 : Blo 303832 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B2471219 : Blo 303832 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B2962817 : Blo 303832 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B308891 : Blo 303832 308891 := bstep (se 1 (by rfl) ⟨231668, by rfl⟩ : syracuseStep 308891 = 463337) B463337
theorem B1095407 : Blo 303832 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B341851 : Blo 303832 341851 := bstep (se 1 (by rfl) ⟨256388, by rfl⟩ : syracuseStep 341851 = 512777) B512777
theorem B1750967 : Blo 303832 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B1161175 : Blo 303832 1161175 := bstep (se 1 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 1161175 = 1741763) B1741763
theorem B2799755 : Blo 303832 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B342247 : Blo 303832 342247 := bstep (se 1 (by rfl) ⟨256685, by rfl⟩ : syracuseStep 342247 = 513371) B513371
theorem B12270197 : Blo 303832 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B866987 : Blo 303832 866987 := bstep (se 1 (by rfl) ⟨650240, by rfl⟩ : syracuseStep 866987 = 1300481) B1300481
theorem B342895 : Blo 303832 342895 := bstep (se 1 (by rfl) ⟨257171, by rfl⟩ : syracuseStep 342895 = 514343) B514343
theorem B310127 : Blo 303832 310127 := bstep (se 1 (by rfl) ⟨232595, by rfl⟩ : syracuseStep 310127 = 465191) B465191
theorem B736211 : Blo 303832 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B1653817 : Blo 303832 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B867419 : Blo 303832 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B769115 : Blo 303832 769115 := bstep (se 1 (by rfl) ⟨576836, by rfl⟩ : syracuseStep 769115 = 1153673) B1153673
theorem B1031399 : Blo 303832 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1162619 : Blo 303832 1162619 := bstep (se 1 (by rfl) ⟨871964, by rfl⟩ : syracuseStep 1162619 = 1743929) B1743929
theorem B2604581 : Blo 303832 2604581 := bstep (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) B488359
theorem B343975 : Blo 303832 343975 := bstep (se 1 (by rfl) ⟨257981, by rfl⟩ : syracuseStep 343975 = 515963) B515963
theorem B1163879 : Blo 303832 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B737903 : Blo 303832 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B345199 : Blo 303832 345199 := bstep (se 1 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 345199 = 517799) B517799
theorem B1033451 : Blo 303832 1033451 := bstep (se 1 (by rfl) ⟨775088, by rfl⟩ : syracuseStep 1033451 = 1550177) B1550177
theorem B345631 : Blo 303832 345631 := bstep (se 1 (by rfl) ⟨259223, by rfl⟩ : syracuseStep 345631 = 518447) B518447
theorem B1099327 : Blo 303832 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B1460369 : Blo 303832 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B1034855 : Blo 303832 1034855 := bstep (se 1 (by rfl) ⟨776141, by rfl⟩ : syracuseStep 1034855 = 1552283) B1552283
theorem B1035233 : Blo 303832 1035233 := bstep (se 2 (by rfl) ⟨388212, by rfl⟩ : syracuseStep 1035233 = 776425) B776425
theorem B2608271 : Blo 303832 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B17714699 : Blo 303832 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B2608955 : Blo 303832 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B5656675 : Blo 303832 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B774299 : Blo 303832 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B872603 : Blo 303832 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B774319 : Blo 303832 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B1168283 : Blo 303832 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B513391 : Blo 303832 513391 := bstep (se 1 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 513391 = 770087) B770087
theorem B579487 : Blo 303832 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B1038689 : Blo 303832 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B1956257 : Blo 303832 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B1858085 : Blo 303832 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B1956797 : Blo 303832 1956797 := bstep (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) B733799
theorem B384679 : Blo 303832 384679 := bstep (se 1 (by rfl) ⟨288509, by rfl⟩ : syracuseStep 384679 = 577019) B577019
theorem B2318219 : Blo 303832 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B8314807 : Blo 303832 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B385231 : Blo 303832 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B2613707 : Blo 303832 2613707 := bstep (se 1 (by rfl) ⟨1960280, by rfl⟩ : syracuseStep 2613707 = 3920561) B3920561
theorem B582137 : Blo 303832 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B516827 : Blo 303832 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B4383467 : Blo 303832 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B385823 : Blo 303832 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B33613643 : Blo 303832 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B4188023 : Blo 303832 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B518123 : Blo 303832 518123 := bstep (se 1 (by rfl) ⟨388592, by rfl⟩ : syracuseStep 518123 = 777185) B777185
theorem B387119 : Blo 303832 387119 := bstep (se 1 (by rfl) ⟨290339, by rfl⟩ : syracuseStep 387119 = 580679) B580679
theorem B583823 : Blo 303832 583823 := bstep (se 1 (by rfl) ⟨437867, by rfl⟩ : syracuseStep 583823 = 875735) B875735
theorem B977129 : Blo 303832 977129 := bstep (se 2 (by rfl) ⟨366423, by rfl⟩ : syracuseStep 977129 = 732847) B732847
theorem B1173851 : Blo 303832 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B10644047 : Blo 303832 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B167668697 : Blo 303832 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B5958845 : Blo 303832 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B31289125 : Blo 303832 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B5861159 : Blo 303832 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B1241351 : Blo 303832 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B651539 : Blo 303832 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B2617703 : Blo 303832 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B651719 : Blo 303832 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B7565885 : Blo 303832 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B684809 : Blo 303832 684809 := bstep (se 2 (by rfl) ⟨256803, by rfl⟩ : syracuseStep 684809 = 513607) B513607
theorem B684863 : Blo 303832 684863 := bstep (se 1 (by rfl) ⟨513647, by rfl⟩ : syracuseStep 684863 = 1027295) B1027295
theorem B1110941 : Blo 303832 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B685007 : Blo 303832 685007 := bstep (se 1 (by rfl) ⟨513755, by rfl⟩ : syracuseStep 685007 = 1027511) B1027511
theorem B685097 : Blo 303832 685097 := bstep (se 2 (by rfl) ⟨256911, by rfl⟩ : syracuseStep 685097 = 513823) B513823
theorem B455945 : Blo 303832 455945 := bstep (se 2 (by rfl) ⟨170979, by rfl⟩ : syracuseStep 455945 = 341959) B341959
theorem B455999 : Blo 303832 455999 := bstep (se 1 (by rfl) ⟨341999, by rfl⟩ : syracuseStep 455999 = 683999) B683999
theorem B652607 : Blo 303832 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B685385 : Blo 303832 685385 := bstep (se 2 (by rfl) ⟨257019, by rfl⟩ : syracuseStep 685385 = 514039) B514039
theorem B18216355 : Blo 303832 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B619987 : Blo 303832 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B1308271 : Blo 303832 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B456425 : Blo 303832 456425 := bstep (se 2 (by rfl) ⟨171159, by rfl⟩ : syracuseStep 456425 = 342319) B342319
theorem B456431 : Blo 303832 456431 := bstep (se 1 (by rfl) ⟨342323, by rfl⟩ : syracuseStep 456431 = 684647) B684647
theorem B456887 : Blo 303832 456887 := bstep (se 1 (by rfl) ⟨342665, by rfl⟩ : syracuseStep 456887 = 685331) B685331
theorem B653503 : Blo 303832 653503 := bstep (se 1 (by rfl) ⟨490127, by rfl⟩ : syracuseStep 653503 = 980255) B980255
theorem B456935 : Blo 303832 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B686375 : Blo 303832 686375 := bstep (se 1 (by rfl) ⟨514781, by rfl⟩ : syracuseStep 686375 = 1029563) B1029563
theorem B1538351 : Blo 303832 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B2325023 : Blo 303832 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B457307 : Blo 303832 457307 := bstep (se 1 (by rfl) ⟨342980, by rfl⟩ : syracuseStep 457307 = 685961) B685961
theorem B686735 : Blo 303832 686735 := bstep (se 1 (by rfl) ⟨515051, by rfl⟩ : syracuseStep 686735 = 1030103) B1030103
theorem B686825 : Blo 303832 686825 := bstep (se 2 (by rfl) ⟨257559, by rfl⟩ : syracuseStep 686825 = 515119) B515119
theorem B457451 : Blo 303832 457451 := bstep (se 1 (by rfl) ⟨343088, by rfl⟩ : syracuseStep 457451 = 686177) B686177
theorem B457481 : Blo 303832 457481 := bstep (se 2 (by rfl) ⟨171555, by rfl⟩ : syracuseStep 457481 = 343111) B343111
theorem B654247 : Blo 303832 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B687059 : Blo 303832 687059 := bstep (se 1 (by rfl) ⟨515294, by rfl⟩ : syracuseStep 687059 = 1030589) B1030589
theorem B326863 : Blo 303832 326863 := bstep (se 1 (by rfl) ⟨245147, by rfl⟩ : syracuseStep 326863 = 490295) B490295
theorem B687329 : Blo 303832 687329 := bstep (se 2 (by rfl) ⟨257748, by rfl⟩ : syracuseStep 687329 = 515497) B515497
theorem B1244527 : Blo 303832 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B687635 : Blo 303832 687635 := bstep (se 1 (by rfl) ⟨515726, by rfl⟩ : syracuseStep 687635 = 1031453) B1031453
theorem B884243 : Blo 303832 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B458351 : Blo 303832 458351 := bstep (se 1 (by rfl) ⟨343763, by rfl⟩ : syracuseStep 458351 = 687527) B687527
theorem B458471 : Blo 303832 458471 := bstep (se 1 (by rfl) ⟨343853, by rfl⟩ : syracuseStep 458471 = 687707) B687707
theorem B458663 : Blo 303832 458663 := bstep (se 1 (by rfl) ⟨343997, by rfl⟩ : syracuseStep 458663 = 687995) B687995
theorem B327623 : Blo 303832 327623 := bstep (se 1 (by rfl) ⟨245717, by rfl⟩ : syracuseStep 327623 = 491435) B491435
theorem B458879 : Blo 303832 458879 := bstep (se 1 (by rfl) ⟨344159, by rfl⟩ : syracuseStep 458879 = 688319) B688319
theorem B459167 : Blo 303832 459167 := bstep (se 1 (by rfl) ⟨344375, by rfl⟩ : syracuseStep 459167 = 688751) B688751
theorem B491935 : Blo 303832 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B2195885 : Blo 303832 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B459431 : Blo 303832 459431 := bstep (se 1 (by rfl) ⟨344573, by rfl⟩ : syracuseStep 459431 = 689147) B689147
theorem B459551 : Blo 303832 459551 := bstep (se 1 (by rfl) ⟨344663, by rfl⟩ : syracuseStep 459551 = 689327) B689327
theorem B1180457 : Blo 303832 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B459575 : Blo 303832 459575 := bstep (se 1 (by rfl) ⟨344681, by rfl⟩ : syracuseStep 459575 = 689363) B689363
theorem B688967 : Blo 303832 688967 := bstep (se 1 (by rfl) ⟨516725, by rfl⟩ : syracuseStep 688967 = 1033451) B1033451
theorem B459755 : Blo 303832 459755 := bstep (se 1 (by rfl) ⟨344816, by rfl⟩ : syracuseStep 459755 = 689633) B689633
theorem B9372685 : Blo 303832 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B460265 : Blo 303832 460265 := bstep (se 2 (by rfl) ⟨172599, by rfl⟩ : syracuseStep 460265 = 345199) B345199
theorem B689903 : Blo 303832 689903 := bstep (se 1 (by rfl) ⟨517427, by rfl⟩ : syracuseStep 689903 = 1034855) B1034855
theorem B460655 : Blo 303832 460655 := bstep (se 1 (by rfl) ⟨345491, by rfl⟩ : syracuseStep 460655 = 690983) B690983
theorem B690155 : Blo 303832 690155 := bstep (se 1 (by rfl) ⟨517616, by rfl⟩ : syracuseStep 690155 = 1035233) B1035233
theorem B460841 : Blo 303832 460841 := bstep (se 2 (by rfl) ⟨172815, by rfl⟩ : syracuseStep 460841 = 345631) B345631
theorem B460871 : Blo 303832 460871 := bstep (se 1 (by rfl) ⟨345653, by rfl⟩ : syracuseStep 460871 = 691307) B691307
theorem B1738847 : Blo 303832 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B461051 : Blo 303832 461051 := bstep (se 1 (by rfl) ⟨345788, by rfl⟩ : syracuseStep 461051 = 691577) B691577
theorem B1771903 : Blo 303832 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B461255 : Blo 303832 461255 := bstep (se 1 (by rfl) ⟨345941, by rfl⟩ : syracuseStep 461255 = 691883) B691883
theorem B1739303 : Blo 303832 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B985715 : Blo 303832 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B461471 : Blo 303832 461471 := bstep (se 1 (by rfl) ⟨346103, by rfl⟩ : syracuseStep 461471 = 692207) B692207
theorem B461519 : Blo 303832 461519 := bstep (se 1 (by rfl) ⟨346139, by rfl⟩ : syracuseStep 461519 = 692279) B692279
theorem B461615 : Blo 303832 461615 := bstep (se 1 (by rfl) ⟨346211, by rfl⟩ : syracuseStep 461615 = 692423) B692423
theorem B461735 : Blo 303832 461735 := bstep (se 1 (by rfl) ⟨346301, by rfl⟩ : syracuseStep 461735 = 692603) B692603
theorem B692459 : Blo 303832 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B823709 : Blo 303832 823709 := bstep (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) B308891
theorem B41718833 : Blo 303832 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B1545479 : Blo 303832 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B7542233 : Blo 303832 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B3511801 : Blo 303832 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B1742471 : Blo 303832 1742471 := bstep (se 1 (by rfl) ⟨1306853, by rfl⟩ : syracuseStep 1742471 = 2613707) B2613707
theorem B2922311 : Blo 303832 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B4987453 : Blo 303832 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B2792015 : Blo 303832 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B24288473 : Blo 303832 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B826649 : Blo 303832 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B111779131 : Blo 303832 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B4005287 : Blo 303832 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B3972563 : Blo 303832 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B1744361 : Blo 303832 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B827005 : Blo 303832 827005 := bstep (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) B310127
theorem B466663 : Blo 303832 466663 := bstep (se 1 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 466663 = 699995) B699995
theorem B3907439 : Blo 303832 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B1548233 : Blo 303832 1548233 := bstep (se 2 (by rfl) ⟨580587, by rfl⟩ : syracuseStep 1548233 = 1161175) B1161175
theorem B827567 : Blo 303832 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B434359 : Blo 303832 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B1745135 : Blo 303832 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B434479 : Blo 303832 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B3154481 : Blo 303832 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B303963 : Blo 303832 303963 := bstep (se 1 (by rfl) ⟨227972, by rfl⟩ : syracuseStep 303963 = 455945) B455945
theorem B1647479 : Blo 303832 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B303999 : Blo 303832 303999 := bstep (se 1 (by rfl) ⟨227999, by rfl⟩ : syracuseStep 303999 = 455999) B455999
theorem B435071 : Blo 303832 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B1975211 : Blo 303832 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B304283 : Blo 303832 304283 := bstep (se 1 (by rfl) ⟨228212, by rfl⟩ : syracuseStep 304283 = 456425) B456425
theorem B730271 : Blo 303832 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B304287 : Blo 303832 304287 := bstep (se 1 (by rfl) ⟨228215, by rfl⟩ : syracuseStep 304287 = 456431) B456431
theorem B2205089 : Blo 303832 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B304591 : Blo 303832 304591 := bstep (se 1 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 304591 = 456887) B456887
theorem B304623 : Blo 303832 304623 := bstep (se 1 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 304623 = 456935) B456935
theorem B1025567 : Blo 303832 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B435817 : Blo 303832 435817 := bstep (se 2 (by rfl) ⟨163431, by rfl⟩ : syracuseStep 435817 = 326863) B326863
theorem B1550015 : Blo 303832 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B304871 : Blo 303832 304871 := bstep (se 1 (by rfl) ⟨228653, by rfl⟩ : syracuseStep 304871 = 457307) B457307
theorem B304967 : Blo 303832 304967 := bstep (se 1 (by rfl) ⟨228725, by rfl⟩ : syracuseStep 304967 = 457451) B457451
theorem B304987 : Blo 303832 304987 := bstep (se 1 (by rfl) ⟨228740, by rfl⟩ : syracuseStep 304987 = 457481) B457481
theorem B305567 : Blo 303832 305567 := bstep (se 1 (by rfl) ⟨229175, by rfl⟩ : syracuseStep 305567 = 458351) B458351
theorem B305647 : Blo 303832 305647 := bstep (se 1 (by rfl) ⟨229235, by rfl⟩ : syracuseStep 305647 = 458471) B458471
theorem B11086409 : Blo 303832 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B305775 : Blo 303832 305775 := bstep (se 1 (by rfl) ⟨229331, by rfl⟩ : syracuseStep 305775 = 458663) B458663
theorem B17836685 : Blo 303832 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B305991 : Blo 303832 305991 := bstep (se 1 (by rfl) ⟨229493, by rfl⟩ : syracuseStep 305991 = 458987) B458987
theorem B306031 : Blo 303832 306031 := bstep (se 1 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 306031 = 459047) B459047
theorem B1551311 : Blo 303832 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B306479 : Blo 303832 306479 := bstep (se 1 (by rfl) ⟨229859, by rfl⟩ : syracuseStep 306479 = 459719) B459719
theorem B306591 : Blo 303832 306591 := bstep (se 1 (by rfl) ⟨229943, by rfl⟩ : syracuseStep 306591 = 459887) B459887
theorem B306719 : Blo 303832 306719 := bstep (se 1 (by rfl) ⟨230039, by rfl⟩ : syracuseStep 306719 = 460079) B460079
theorem B306855 : Blo 303832 306855 := bstep (se 1 (by rfl) ⟨230141, by rfl⟩ : syracuseStep 306855 = 460283) B460283
theorem B306879 : Blo 303832 306879 := bstep (se 1 (by rfl) ⟨230159, by rfl⟩ : syracuseStep 306879 = 460319) B460319
theorem B306975 : Blo 303832 306975 := bstep (se 1 (by rfl) ⟨230231, by rfl⟩ : syracuseStep 306975 = 460463) B460463
theorem B307055 : Blo 303832 307055 := bstep (se 1 (by rfl) ⟨230291, by rfl⟩ : syracuseStep 307055 = 460583) B460583
theorem B307423 : Blo 303832 307423 := bstep (se 1 (by rfl) ⟨230567, by rfl⟩ : syracuseStep 307423 = 461135) B461135
theorem B307455 : Blo 303832 307455 := bstep (se 1 (by rfl) ⟨230591, by rfl⟩ : syracuseStep 307455 = 461183) B461183
theorem B307483 : Blo 303832 307483 := bstep (se 1 (by rfl) ⟨230612, by rfl⟩ : syracuseStep 307483 = 461225) B461225
theorem B3322295 : Blo 303832 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B307739 : Blo 303832 307739 := bstep (se 1 (by rfl) ⟨230804, by rfl⟩ : syracuseStep 307739 = 461609) B461609
theorem B1028861 : Blo 303832 1028861 := bstep (se 3 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 1028861 = 385823) B385823
theorem B1029023 : Blo 303832 1029023 := bstep (se 1 (by rfl) ⟨771767, by rfl⟩ : syracuseStep 1029023 = 1543535) B1543535
theorem B11809799 : Blo 303832 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B374015 : Blo 303832 374015 := bstep (se 1 (by rfl) ⟨280511, by rfl⟩ : syracuseStep 374015 = 561023) B561023
theorem B1160477 : Blo 303832 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B932617 : Blo 303832 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B1751969 : Blo 303832 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1556171 : Blo 303832 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B311035 : Blo 303832 311035 := bstep (se 1 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 311035 = 466553) B466553
theorem B1032317 : Blo 303832 1032317 := bstep (se 3 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 1032317 = 387119) B387119
theorem B1032425 : Blo 303832 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B770431 : Blo 303832 770431 := bstep (se 1 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 770431 = 1155647) B1155647
theorem B344551 : Blo 303832 344551 := bstep (se 1 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 344551 = 516827) B516827
theorem B1983521 : Blo 303832 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B1164395 : Blo 303832 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1557791 : Blo 303832 1557791 := bstep (se 1 (by rfl) ⟨1168343, by rfl⟩ : syracuseStep 1557791 = 2336687) B2336687
theorem B345415 : Blo 303832 345415 := bstep (se 1 (by rfl) ⟨259061, by rfl⟩ : syracuseStep 345415 = 518123) B518123
theorem B1951283 : Blo 303832 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B3524147 : Blo 303832 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B32720525 : Blo 303832 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B7096031 : Blo 303832 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B6637477 : Blo 303832 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B1034423 : Blo 303832 1034423 := bstep (se 1 (by rfl) ⟨775817, by rfl⟩ : syracuseStep 1034423 = 1551635) B1551635
theorem B1165535 : Blo 303832 1165535 := bstep (se 1 (by rfl) ⟨874151, by rfl⟩ : syracuseStep 1165535 = 1748303) B1748303
theorem B1952207 : Blo 303832 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B772649 : Blo 303832 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B772699 : Blo 303832 772699 := bstep (se 1 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 772699 = 1159049) B1159049
theorem B8440625 : Blo 303832 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B1100627 : Blo 303832 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B871337 : Blo 303832 871337 := bstep (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) B653503
theorem B740627 : Blo 303832 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B872329 : Blo 303832 872329 := bstep (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) B654247
theorem B1167311 : Blo 303832 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B577991 : Blo 303832 577991 := bstep (se 1 (by rfl) ⟨433493, by rfl⟩ : syracuseStep 577991 = 866987) B866987
theorem B512743 : Blo 303832 512743 := bstep (se 1 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 512743 = 769115) B769115
theorem B578279 : Blo 303832 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B512905 : Blo 303832 512905 := bstep (se 2 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 512905 = 384679) B384679
theorem B775079 : Blo 303832 775079 := bstep (se 1 (by rfl) ⟨581309, by rfl⟩ : syracuseStep 775079 = 1162619) B1162619
theorem B873661 : Blo 303832 873661 := bstep (se 3 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 873661 = 327623) B327623
theorem B513641 : Blo 303832 513641 := bstep (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) B385231
theorem B775919 : Blo 303832 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B415471 : Blo 303832 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B6609113 : Blo 303832 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B874891 : Blo 303832 874891 := bstep (se 1 (by rfl) ⟨656168, by rfl⟩ : syracuseStep 874891 = 1312337) B1312337
theorem B1957229 : Blo 303832 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B1465769 : Blo 303832 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B876521 : Blo 303832 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B516199 : Blo 303832 516199 := bstep (se 1 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 516199 = 774299) B774299
theorem B581735 : Blo 303832 581735 := bstep (se 1 (by rfl) ⟨436301, by rfl⟩ : syracuseStep 581735 = 872603) B872603
theorem B778855 : Blo 303832 778855 := bstep (se 1 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 778855 = 1168283) B1168283
theorem B3696023 : Blo 303832 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B1304171 : Blo 303832 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B1238723 : Blo 303832 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1304531 : Blo 303832 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B1337719 : Blo 303832 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B388091 : Blo 303832 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B3894317 : Blo 303832 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B2322107 : Blo 303832 2322107 := bstep (se 1 (by rfl) ⟨1741580, by rfl⟩ : syracuseStep 2322107 = 3483161) B3483161
theorem B22409095 : Blo 303832 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B2977769 : Blo 303832 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B3895289 : Blo 303832 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B684071 : Blo 303832 684071 := bstep (se 1 (by rfl) ⟨513053, by rfl⟩ : syracuseStep 684071 = 1026107) B1026107
theorem B389215 : Blo 303832 389215 := bstep (se 1 (by rfl) ⟨291911, by rfl⟩ : syracuseStep 389215 = 583823) B583823
theorem B651419 : Blo 303832 651419 := bstep (se 1 (by rfl) ⟨488564, by rfl⟩ : syracuseStep 651419 = 977129) B977129
theorem B684251 : Blo 303832 684251 := bstep (se 1 (by rfl) ⟨513188, by rfl⟩ : syracuseStep 684251 = 1026377) B1026377
theorem B782567 : Blo 303832 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B684359 : Blo 303832 684359 := bstep (se 1 (by rfl) ⟨513269, by rfl⟩ : syracuseStep 684359 = 1026539) B1026539
theorem B684521 : Blo 303832 684521 := bstep (se 2 (by rfl) ⟨256695, by rfl⟩ : syracuseStep 684521 = 513391) B513391
theorem B685151 : Blo 303832 685151 := bstep (se 1 (by rfl) ⟨513863, by rfl⟩ : syracuseStep 685151 = 1027727) B1027727
theorem B455801 : Blo 303832 455801 := bstep (se 2 (by rfl) ⟨170925, by rfl⟩ : syracuseStep 455801 = 341851) B341851
theorem B6255755 : Blo 303832 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B456329 : Blo 303832 456329 := bstep (se 2 (by rfl) ⟨171123, by rfl⟩ : syracuseStep 456329 = 342247) B342247
theorem B5043923 : Blo 303832 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B456539 : Blo 303832 456539 := bstep (se 1 (by rfl) ⟨342404, by rfl⟩ : syracuseStep 456539 = 684809) B684809
theorem B456575 : Blo 303832 456575 := bstep (se 1 (by rfl) ⟨342431, by rfl⟩ : syracuseStep 456575 = 684863) B684863
theorem B456671 : Blo 303832 456671 := bstep (se 1 (by rfl) ⟨342503, by rfl⟩ : syracuseStep 456671 = 685007) B685007
theorem B456731 : Blo 303832 456731 := bstep (se 1 (by rfl) ⟨342548, by rfl⟩ : syracuseStep 456731 = 685097) B685097
theorem B456923 : Blo 303832 456923 := bstep (se 1 (by rfl) ⟨342692, by rfl⟩ : syracuseStep 456923 = 685385) B685385
theorem B457193 : Blo 303832 457193 := bstep (se 2 (by rfl) ⟨171447, by rfl⟩ : syracuseStep 457193 = 342895) B342895
theorem B621049 : Blo 303832 621049 := bstep (se 2 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 621049 = 465787) B465787
theorem B2357981 : Blo 303832 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B1866503 : Blo 303832 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1768301 : Blo 303832 1768301 := bstep (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) B663113
theorem B457583 : Blo 303832 457583 := bstep (se 1 (by rfl) ⟨343187, by rfl⟩ : syracuseStep 457583 = 686375) B686375
theorem B457823 : Blo 303832 457823 := bstep (se 1 (by rfl) ⟨343367, by rfl⟩ : syracuseStep 457823 = 686735) B686735
theorem B457883 : Blo 303832 457883 := bstep (se 1 (by rfl) ⟨343412, by rfl⟩ : syracuseStep 457883 = 686825) B686825
theorem B458039 : Blo 303832 458039 := bstep (se 1 (by rfl) ⟨343529, by rfl⟩ : syracuseStep 458039 = 687059) B687059
theorem B490807 : Blo 303832 490807 := bstep (se 1 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 490807 = 736211) B736211
theorem B458219 : Blo 303832 458219 := bstep (se 1 (by rfl) ⟨343664, by rfl⟩ : syracuseStep 458219 = 687329) B687329
theorem B687599 : Blo 303832 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B458423 : Blo 303832 458423 := bstep (se 1 (by rfl) ⟨343817, by rfl⟩ : syracuseStep 458423 = 687635) B687635
theorem B1736387 : Blo 303832 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B458633 : Blo 303832 458633 := bstep (se 2 (by rfl) ⟨171987, by rfl⟩ : syracuseStep 458633 = 343975) B343975
theorem B688211 : Blo 303832 688211 := bstep (se 1 (by rfl) ⟨516158, by rfl⟩ : syracuseStep 688211 = 1032317) B1032317
theorem B688265 : Blo 303832 688265 := bstep (se 2 (by rfl) ⟨258099, by rfl⟩ : syracuseStep 688265 = 516199) B516199
theorem B688283 : Blo 303832 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B786971 : Blo 303832 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B655913 : Blo 303832 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B459311 : Blo 303832 459311 := bstep (se 1 (by rfl) ⟨344483, by rfl⟩ : syracuseStep 459311 = 688967) B688967
theorem B459401 : Blo 303832 459401 := bstep (se 2 (by rfl) ⟨172275, by rfl⟩ : syracuseStep 459401 = 344551) B344551
theorem B459935 : Blo 303832 459935 := bstep (se 1 (by rfl) ⟨344951, by rfl⟩ : syracuseStep 459935 = 689903) B689903
theorem B460103 : Blo 303832 460103 := bstep (se 1 (by rfl) ⟨345077, by rfl⟩ : syracuseStep 460103 = 690155) B690155
theorem B689615 : Blo 303832 689615 := bstep (se 1 (by rfl) ⟨517211, by rfl⟩ : syracuseStep 689615 = 1034423) B1034423
theorem B657143 : Blo 303832 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B460553 : Blo 303832 460553 := bstep (se 2 (by rfl) ⟨172707, by rfl⟩ : syracuseStep 460553 = 345415) B345415
theorem B1542077 : Blo 303832 1542077 := bstep (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) B578279
theorem B493751 : Blo 303832 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B8849969 : Blo 303832 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B461639 : Blo 303832 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B2362537 : Blo 303832 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B16192315 : Blo 303832 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B2102987 : Blo 303832 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B1316807 : Blo 303832 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B2464015 : Blo 303832 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B825815 : Blo 303832 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2596211 : Blo 303832 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1548071 : Blo 303832 1548071 := bstep (se 1 (by rfl) ⟨1161053, by rfl⟩ : syracuseStep 1548071 = 2322107) B2322107
theorem B2596859 : Blo 303832 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B434279 : Blo 303832 434279 := bstep (se 1 (by rfl) ⟨325709, by rfl⟩ : syracuseStep 434279 = 651419) B651419
theorem B828065 : Blo 303832 828065 := bstep (se 2 (by rfl) ⟨310524, by rfl⟩ : syracuseStep 828065 = 621049) B621049
theorem B7873199 : Blo 303832 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B303867 : Blo 303832 303867 := bstep (se 1 (by rfl) ⟨227900, by rfl⟩ : syracuseStep 303867 = 455801) B455801
theorem B4170503 : Blo 303832 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B304219 : Blo 303832 304219 := bstep (se 1 (by rfl) ⟨228164, by rfl⟩ : syracuseStep 304219 = 456329) B456329
theorem B304359 : Blo 303832 304359 := bstep (se 1 (by rfl) ⟨228269, by rfl⟩ : syracuseStep 304359 = 456539) B456539
theorem B304383 : Blo 303832 304383 := bstep (se 1 (by rfl) ⟨228287, by rfl⟩ : syracuseStep 304383 = 456575) B456575
theorem B304447 : Blo 303832 304447 := bstep (se 1 (by rfl) ⟨228335, by rfl⟩ : syracuseStep 304447 = 456671) B456671
theorem B304487 : Blo 303832 304487 := bstep (se 1 (by rfl) ⟨228365, by rfl⟩ : syracuseStep 304487 = 456731) B456731
theorem B304615 : Blo 303832 304615 := bstep (se 1 (by rfl) ⟨228461, by rfl⟩ : syracuseStep 304615 = 456923) B456923
theorem B304795 : Blo 303832 304795 := bstep (se 1 (by rfl) ⟨228596, by rfl⟩ : syracuseStep 304795 = 457193) B457193
theorem B149038841 : Blo 303832 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B305055 : Blo 303832 305055 := bstep (se 1 (by rfl) ⟨228791, by rfl⟩ : syracuseStep 305055 = 457583) B457583
theorem B305215 : Blo 303832 305215 := bstep (se 1 (by rfl) ⟨228911, by rfl⟩ : syracuseStep 305215 = 457823) B457823
theorem B305255 : Blo 303832 305255 := bstep (se 1 (by rfl) ⟨228941, by rfl⟩ : syracuseStep 305255 = 457883) B457883
theorem B305359 : Blo 303832 305359 := bstep (se 1 (by rfl) ⟨229019, by rfl⟩ : syracuseStep 305359 = 458039) B458039
theorem B305479 : Blo 303832 305479 := bstep (se 1 (by rfl) ⟨229109, by rfl⟩ : syracuseStep 305479 = 458219) B458219
theorem B305615 : Blo 303832 305615 := bstep (se 1 (by rfl) ⟨229211, by rfl⟩ : syracuseStep 305615 = 458423) B458423
theorem B1157591 : Blo 303832 1157591 := bstep (se 1 (by rfl) ⟨868193, by rfl⟩ : syracuseStep 1157591 = 1736387) B1736387
theorem B305755 : Blo 303832 305755 := bstep (se 1 (by rfl) ⟨229316, by rfl⟩ : syracuseStep 305755 = 458633) B458633
theorem B7940717 : Blo 303832 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B305919 : Blo 303832 305919 := bstep (se 1 (by rfl) ⟨229439, by rfl⟩ : syracuseStep 305919 = 458879) B458879
theorem B306111 : Blo 303832 306111 := bstep (se 1 (by rfl) ⟨229583, by rfl⟩ : syracuseStep 306111 = 459167) B459167
theorem B306287 : Blo 303832 306287 := bstep (se 1 (by rfl) ⟨229715, by rfl⟩ : syracuseStep 306287 = 459431) B459431
theorem B1027241 : Blo 303832 1027241 := bstep (se 2 (by rfl) ⟨385215, by rfl⟩ : syracuseStep 1027241 = 770431) B770431
theorem B306367 : Blo 303832 306367 := bstep (se 1 (by rfl) ⟨229775, by rfl⟩ : syracuseStep 306367 = 459551) B459551
theorem B306383 : Blo 303832 306383 := bstep (se 1 (by rfl) ⟨229787, by rfl⟩ : syracuseStep 306383 = 459575) B459575
theorem B306503 : Blo 303832 306503 := bstep (se 1 (by rfl) ⟨229877, by rfl⟩ : syracuseStep 306503 = 459755) B459755
theorem B1322347 : Blo 303832 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B306843 : Blo 303832 306843 := bstep (se 1 (by rfl) ⟨230132, by rfl⟩ : syracuseStep 306843 = 460265) B460265
theorem B4730687 : Blo 303832 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B307103 : Blo 303832 307103 := bstep (se 1 (by rfl) ⟨230327, by rfl⟩ : syracuseStep 307103 = 460655) B460655
theorem B12496913 : Blo 303832 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B307227 : Blo 303832 307227 := bstep (se 1 (by rfl) ⟨230420, by rfl⟩ : syracuseStep 307227 = 460841) B460841
theorem B307247 : Blo 303832 307247 := bstep (se 1 (by rfl) ⟨230435, by rfl⟩ : syracuseStep 307247 = 460871) B460871
theorem B1159231 : Blo 303832 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B307367 : Blo 303832 307367 := bstep (se 1 (by rfl) ⟨230525, by rfl⟩ : syracuseStep 307367 = 461051) B461051
theorem B307503 : Blo 303832 307503 := bstep (se 1 (by rfl) ⟨230627, by rfl⟩ : syracuseStep 307503 = 461255) B461255
theorem B1159535 : Blo 303832 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B307647 : Blo 303832 307647 := bstep (se 1 (by rfl) ⟨230735, by rfl⟩ : syracuseStep 307647 = 461471) B461471
theorem B307679 : Blo 303832 307679 := bstep (se 1 (by rfl) ⟨230759, by rfl⟩ : syracuseStep 307679 = 461519) B461519
theorem B307743 : Blo 303832 307743 := bstep (se 1 (by rfl) ⟨230807, by rfl⟩ : syracuseStep 307743 = 461615) B461615
theorem B733751 : Blo 303832 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B307823 : Blo 303832 307823 := bstep (se 1 (by rfl) ⟨230867, by rfl⟩ : syracuseStep 307823 = 461735) B461735
theorem B1160189 : Blo 303832 1160189 := bstep (se 3 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 1160189 = 435071) B435071
theorem B1783625 : Blo 303832 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B997373 : Blo 303832 997373 := bstep (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) B374015
theorem B1030265 : Blo 303832 1030265 := bstep (se 2 (by rfl) ⟨386349, by rfl⟩ : syracuseStep 1030265 = 772699) B772699
theorem B1030319 : Blo 303832 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B5028155 : Blo 303832 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B342427 : Blo 303832 342427 := bstep (se 1 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 342427 = 513641) B513641
theorem B1161647 : Blo 303832 1161647 := bstep (se 1 (by rfl) ⟨871235, by rfl⟩ : syracuseStep 1161647 = 1742471) B1742471
theorem B1948207 : Blo 303832 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B4406075 : Blo 303832 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B2670191 : Blo 303832 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B1162907 : Blo 303832 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1163105 : Blo 303832 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B2604959 : Blo 303832 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B1032155 : Blo 303832 1032155 := bstep (se 1 (by rfl) ⟨774116, by rfl⟩ : syracuseStep 1032155 = 1548233) B1548233
theorem B1163423 : Blo 303832 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B1098319 : Blo 303832 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B869447 : Blo 303832 869447 := bstep (se 1 (by rfl) ⟨652085, by rfl⟩ : syracuseStep 869447 = 1304171) B1304171
theorem B1033343 : Blo 303832 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B869687 : Blo 303832 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B1164881 : Blo 303832 1164881 := bstep (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) B873661
theorem B7390939 : Blo 303832 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B1034207 : Blo 303832 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B18729605 : Blo 303832 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B1034909 : Blo 303832 1034909 := bstep (se 3 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 1034909 = 388091) B388091
theorem B2214863 : Blo 303832 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B1166521 : Blo 303832 1166521 := bstep (se 2 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 1166521 = 874891) B874891
theorem B773651 : Blo 303832 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B3362615 : Blo 303832 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1167979 : Blo 303832 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1102673 : Blo 303832 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B414713 : Blo 303832 414713 := bstep (se 2 (by rfl) ⟨155517, by rfl⟩ : syracuseStep 414713 = 311035) B311035
theorem B1037447 : Blo 303832 1037447 := bstep (se 1 (by rfl) ⟨778085, by rfl⟩ : syracuseStep 1037447 = 1556171) B1556171
theorem B579145 : Blo 303832 579145 := bstep (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) B434359
theorem B1463923 : Blo 303832 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B579305 : Blo 303832 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B776263 : Blo 303832 776263 := bstep (se 1 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 776263 = 1164395) B1164395
theorem B1038473 : Blo 303832 1038473 := bstep (se 2 (by rfl) ⟨389427, by rfl⟩ : syracuseStep 1038473 = 778855) B778855
theorem B1038527 : Blo 303832 1038527 := bstep (se 1 (by rfl) ⟨778895, by rfl⟩ : syracuseStep 1038527 = 1557791) B1557791
theorem B1300855 : Blo 303832 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B2349431 : Blo 303832 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B21813683 : Blo 303832 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B777023 : Blo 303832 777023 := bstep (se 1 (by rfl) ⟨582767, by rfl⟩ : syracuseStep 777023 = 1165535) B1165535
theorem B1301471 : Blo 303832 1301471 := bstep (se 1 (by rfl) ⟨976103, by rfl⟩ : syracuseStep 1301471 = 1952207) B1952207
theorem B515099 : Blo 303832 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B5627083 : Blo 303832 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B581089 : Blo 303832 581089 := bstep (se 2 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 581089 = 435817) B435817
theorem B778207 : Blo 303832 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B549139 : Blo 303832 549139 := bstep (se 1 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 549139 = 823709) B823709
theorem B385327 : Blo 303832 385327 := bstep (se 1 (by rfl) ⟨288995, by rfl⟩ : syracuseStep 385327 = 577991) B577991
theorem B516719 : Blo 303832 516719 := bstep (se 1 (by rfl) ⟨387539, by rfl⟩ : syracuseStep 516719 = 775079) B775079
theorem B27812555 : Blo 303832 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B517279 : Blo 303832 517279 := bstep (se 1 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 517279 = 775919) B775919
theorem B4973957 : Blo 303832 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B1861343 : Blo 303832 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B551099 : Blo 303832 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B1304819 : Blo 303832 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B977179 : Blo 303832 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B2648375 : Blo 303832 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B29878793 : Blo 303832 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B584347 : Blo 303832 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B387823 : Blo 303832 387823 := bstep (se 1 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 387823 = 581735) B581735
theorem B551711 : Blo 303832 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B518953 : Blo 303832 518953 := bstep (se 2 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 518953 = 389215) B389215
theorem B486847 : Blo 303832 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B1470059 : Blo 303832 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B683657 : Blo 303832 683657 := bstep (se 2 (by rfl) ⟨256371, by rfl⟩ : syracuseStep 683657 = 512743) B512743
theorem B683711 : Blo 303832 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B683873 : Blo 303832 683873 := bstep (se 2 (by rfl) ⟨256452, by rfl⟩ : syracuseStep 683873 = 512905) B512905
theorem B11891123 : Blo 303832 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B553961 : Blo 303832 553961 := bstep (se 2 (by rfl) ⟨207735, by rfl⟩ : syracuseStep 553961 = 415471) B415471
theorem B2323565 : Blo 303832 2323565 := bstep (se 3 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 2323565 = 871337) B871337
theorem B456047 : Blo 303832 456047 := bstep (se 1 (by rfl) ⟨342035, by rfl⟩ : syracuseStep 456047 = 684071) B684071
theorem B456167 : Blo 303832 456167 := bstep (se 1 (by rfl) ⟨342125, by rfl⟩ : syracuseStep 456167 = 684251) B684251
theorem B521711 : Blo 303832 521711 := bstep (se 1 (by rfl) ⟨391283, by rfl⟩ : syracuseStep 521711 = 782567) B782567
theorem B456239 : Blo 303832 456239 := bstep (se 1 (by rfl) ⟨342179, by rfl⟩ : syracuseStep 456239 = 684359) B684359
theorem B456347 : Blo 303832 456347 := bstep (se 1 (by rfl) ⟨342260, by rfl⟩ : syracuseStep 456347 = 684521) B684521
theorem B685907 : Blo 303832 685907 := bstep (se 1 (by rfl) ⟨514430, by rfl⟩ : syracuseStep 685907 = 1028861) B1028861
theorem B686015 : Blo 303832 686015 := bstep (se 1 (by rfl) ⟨514511, by rfl⟩ : syracuseStep 686015 = 1029023) B1029023
theorem B456767 : Blo 303832 456767 := bstep (se 1 (by rfl) ⟨342575, by rfl⟩ : syracuseStep 456767 = 685151) B685151
theorem B6649937 : Blo 303832 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B654409 : Blo 303832 654409 := bstep (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) B490807
theorem B1571987 : Blo 303832 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B1244335 : Blo 303832 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1178867 : Blo 303832 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B622217 : Blo 303832 622217 := bstep (se 2 (by rfl) ⟨233331, by rfl⟩ : syracuseStep 622217 = 466663) B466663
theorem B458399 : Blo 303832 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B458807 : Blo 303832 458807 := bstep (se 1 (by rfl) ⟨344105, by rfl⟩ : syracuseStep 458807 = 688211) B688211
theorem B458843 : Blo 303832 458843 := bstep (se 1 (by rfl) ⟨344132, by rfl⟩ : syracuseStep 458843 = 688265) B688265
theorem B458855 : Blo 303832 458855 := bstep (se 1 (by rfl) ⟨344141, by rfl⟩ : syracuseStep 458855 = 688283) B688283
theorem B524647 : Blo 303832 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B688895 : Blo 303832 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B459743 : Blo 303832 459743 := bstep (se 1 (by rfl) ⟨344807, by rfl⟩ : syracuseStep 459743 = 689615) B689615
theorem B689471 : Blo 303832 689471 := bstep (se 1 (by rfl) ⟨517103, by rfl⟩ : syracuseStep 689471 = 1034207) B1034207
theorem B329167 : Blo 303832 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B689705 : Blo 303832 689705 := bstep (se 2 (by rfl) ⟨258639, by rfl⟩ : syracuseStep 689705 = 517279) B517279
theorem B5899979 : Blo 303832 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B12486403 : Blo 303832 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B689939 : Blo 303832 689939 := bstep (se 1 (by rfl) ⟨517454, by rfl⟩ : syracuseStep 689939 = 1034909) B1034909
theorem B1476575 : Blo 303832 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B691631 : Blo 303832 691631 := bstep (se 1 (by rfl) ⟨518723, by rfl⟩ : syracuseStep 691631 = 1037447) B1037447
theorem B691937 : Blo 303832 691937 := bstep (se 2 (by rfl) ⟨259476, by rfl⟩ : syracuseStep 691937 = 518953) B518953
theorem B692315 : Blo 303832 692315 := bstep (se 1 (by rfl) ⟨519236, by rfl⟩ : syracuseStep 692315 = 1038473) B1038473
theorem B692351 : Blo 303832 692351 := bstep (se 1 (by rfl) ⟨519263, by rfl⟩ : syracuseStep 692351 = 1038527) B1038527
theorem B4756333 : Blo 303832 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1545641 : Blo 303832 1545641 := bstep (se 2 (by rfl) ⟨579615, by rfl⟩ : syracuseStep 1545641 = 1159231) B1159231
theorem B5248799 : Blo 303832 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B3315971 : Blo 303832 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B58169821 : Blo 303832 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B99359227 : Blo 303832 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B2202173 : Blo 303832 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B367399 : Blo 303832 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B3153791 : Blo 303832 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B8331275 : Blo 303832 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B3285353 : Blo 303832 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B7807589 : Blo 303832 7807589 := bstep (se 4 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 7807589 = 1463923) B1463923
theorem B369307 : Blo 303832 369307 := bstep (se 1 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 369307 = 553961) B553961
theorem B2597609 : Blo 303832 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B1549043 : Blo 303832 1549043 := bstep (se 1 (by rfl) ⟨1161782, by rfl⟩ : syracuseStep 1549043 = 2323565) B2323565
theorem B304031 : Blo 303832 304031 := bstep (se 1 (by rfl) ⟨228023, by rfl⟩ : syracuseStep 304031 = 456047) B456047
theorem B304111 : Blo 303832 304111 := bstep (se 1 (by rfl) ⟨228083, by rfl⟩ : syracuseStep 304111 = 456167) B456167
theorem B304159 : Blo 303832 304159 := bstep (se 1 (by rfl) ⟨228119, by rfl⟩ : syracuseStep 304159 = 456239) B456239
theorem B304231 : Blo 303832 304231 := bstep (se 1 (by rfl) ⟨228173, by rfl⟩ : syracuseStep 304231 = 456347) B456347
theorem B664915 : Blo 303832 664915 := bstep (se 1 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 664915 = 997373) B997373
theorem B304511 : Blo 303832 304511 := bstep (se 1 (by rfl) ⟨228383, by rfl⟩ : syracuseStep 304511 = 456767) B456767
theorem B4433291 : Blo 303832 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B3352103 : Blo 303832 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B1780127 : Blo 303832 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B305599 : Blo 303832 305599 := bstep (se 1 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 305599 = 458399) B458399
theorem B1158077 : Blo 303832 1158077 := bstep (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) B434279
theorem B732185 : Blo 303832 732185 := bstep (se 2 (by rfl) ⟨274569, by rfl⟩ : syracuseStep 732185 = 549139) B549139
theorem B437275 : Blo 303832 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B306207 : Blo 303832 306207 := bstep (se 1 (by rfl) ⟨229655, by rfl⟩ : syracuseStep 306207 = 459311) B459311
theorem B306267 : Blo 303832 306267 := bstep (se 1 (by rfl) ⟨229700, by rfl⟩ : syracuseStep 306267 = 459401) B459401
theorem B306623 : Blo 303832 306623 := bstep (se 1 (by rfl) ⟨229967, by rfl⟩ : syracuseStep 306623 = 459935) B459935
theorem B306735 : Blo 303832 306735 := bstep (se 1 (by rfl) ⟨230051, by rfl⟩ : syracuseStep 306735 = 460103) B460103
theorem B438095 : Blo 303832 438095 := bstep (se 1 (by rfl) ⟨328571, by rfl⟩ : syracuseStep 438095 = 657143) B657143
theorem B307035 : Blo 303832 307035 := bstep (se 1 (by rfl) ⟨230276, by rfl⟩ : syracuseStep 307035 = 460553) B460553
theorem B1028051 : Blo 303832 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B307759 : Blo 303832 307759 := bstep (se 1 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 307759 = 461639) B461639
theorem B143471573 : Blo 303832 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B735115 : Blo 303832 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B1555361 : Blo 303832 1555361 := bstep (se 2 (by rfl) ⟨583260, by rfl⟩ : syracuseStep 1555361 = 1166521) B1166521
theorem B867647 : Blo 303832 867647 := bstep (se 1 (by rfl) ⟨650735, by rfl⟩ : syracuseStep 867647 = 1301471) B1301471
theorem B343399 : Blo 303832 343399 := bstep (se 1 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 343399 = 515099) B515099
theorem B1032047 : Blo 303832 1032047 := bstep (se 1 (by rfl) ⟨774035, by rfl⟩ : syracuseStep 1032047 = 1548071) B1548071
theorem B344479 : Blo 303832 344479 := bstep (se 1 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 344479 = 516719) B516719
theorem B1557305 : Blo 303832 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B12600197 : Blo 303832 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B869879 : Blo 303832 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B771727 : Blo 303832 771727 := bstep (se 1 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 771727 = 1157591) B1157591
theorem B5293811 : Blo 303832 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B772193 : Blo 303832 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B1035017 : Blo 303832 1035017 := bstep (se 2 (by rfl) ⟨388131, by rfl⟩ : syracuseStep 1035017 = 776263) B776263
theorem B773023 : Blo 303832 773023 := bstep (se 1 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 773023 = 1159535) B1159535
theorem B773459 : Blo 303832 773459 := bstep (se 1 (by rfl) ⟨580094, by rfl⟩ : syracuseStep 773459 = 1160189) B1160189
theorem B347807 : Blo 303832 347807 := bstep (se 1 (by rfl) ⟨260855, by rfl⟩ : syracuseStep 347807 = 521711) B521711
theorem B872545 : Blo 303832 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B1659113 : Blo 303832 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B774431 : Blo 303832 774431 := bstep (se 1 (by rfl) ⟨580823, by rfl⟩ : syracuseStep 774431 = 1161647) B1161647
theorem B2937383 : Blo 303832 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B774785 : Blo 303832 774785 := bstep (se 2 (by rfl) ⟨290544, by rfl⟩ : syracuseStep 774785 = 581089) B581089
theorem B414811 : Blo 303832 414811 := bstep (se 1 (by rfl) ⟨311108, by rfl⟩ : syracuseStep 414811 = 622217) B622217
theorem B775271 : Blo 303832 775271 := bstep (se 1 (by rfl) ⟨581453, by rfl⟩ : syracuseStep 775271 = 1162907) B1162907
theorem B775403 : Blo 303832 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B1037609 : Blo 303832 1037609 := bstep (se 2 (by rfl) ⟨389103, by rfl⟩ : syracuseStep 1037609 = 778207) B778207
theorem B775615 : Blo 303832 775615 := bstep (se 1 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 775615 = 1163423) B1163423
theorem B513769 : Blo 303832 513769 := bstep (se 2 (by rfl) ⟨192663, by rfl⟩ : syracuseStep 513769 = 385327) B385327
theorem B579631 : Blo 303832 579631 := bstep (se 1 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 579631 = 869447) B869447
theorem B1464425 : Blo 303832 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B579791 : Blo 303832 579791 := bstep (se 1 (by rfl) ⟨434843, by rfl⟩ : syracuseStep 579791 = 869687) B869687
theorem B776587 : Blo 303832 776587 := bstep (se 1 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 776587 = 1164881) B1164881
theorem B9854585 : Blo 303832 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B515767 : Blo 303832 515767 := bstep (se 1 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 515767 = 773651) B773651
theorem B1105901 : Blo 303832 1105901 := bstep (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) B414713
theorem B1302905 : Blo 303832 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B779129 : Blo 303832 779129 := bstep (se 2 (by rfl) ⟨292173, by rfl⟩ : syracuseStep 779129 = 584347) B584347
theorem B517097 : Blo 303832 517097 := bstep (se 2 (by rfl) ⟨193911, by rfl⟩ : syracuseStep 517097 = 387823) B387823
theorem B1401991 : Blo 303832 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B386203 : Blo 303832 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B877871 : Blo 303832 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B1566287 : Blo 303832 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1763129 : Blo 303832 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B518015 : Blo 303832 518015 := bstep (se 1 (by rfl) ⟨388511, by rfl⟩ : syracuseStep 518015 = 777023) B777023
theorem B649129 : Blo 303832 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B1730807 : Blo 303832 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1731239 : Blo 303832 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B552043 : Blo 303832 552043 := bstep (se 1 (by rfl) ⟨414032, by rfl⟩ : syracuseStep 552043 = 828065) B828065
theorem B18541703 : Blo 303832 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B2780335 : Blo 303832 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B21589753 : Blo 303832 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B1240895 : Blo 303832 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B1765583 : Blo 303832 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B19919195 : Blo 303832 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1471229 : Blo 303832 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B684827 : Blo 303832 684827 := bstep (se 1 (by rfl) ⟨513620, by rfl⟩ : syracuseStep 684827 = 1027241) B1027241
theorem B980039 : Blo 303832 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B455771 : Blo 303832 455771 := bstep (se 1 (by rfl) ⟨341828, by rfl⟩ : syracuseStep 455771 = 683657) B683657
theorem B455807 : Blo 303832 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B455915 : Blo 303832 455915 := bstep (se 1 (by rfl) ⟨341936, by rfl⟩ : syracuseStep 455915 = 683873) B683873
theorem B7927415 : Blo 303832 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B489167 : Blo 303832 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B1734473 : Blo 303832 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B456569 : Blo 303832 456569 := bstep (se 2 (by rfl) ⟨171213, by rfl⟩ : syracuseStep 456569 = 342427) B342427
theorem B457271 : Blo 303832 457271 := bstep (se 1 (by rfl) ⟨342953, by rfl⟩ : syracuseStep 457271 = 685907) B685907
theorem B457343 : Blo 303832 457343 := bstep (se 1 (by rfl) ⟨343007, by rfl⟩ : syracuseStep 457343 = 686015) B686015
theorem B686843 : Blo 303832 686843 := bstep (se 1 (by rfl) ⟨515132, by rfl⟩ : syracuseStep 686843 = 1030265) B1030265
theorem B686879 : Blo 303832 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B7502777 : Blo 303832 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B1047991 : Blo 303832 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B785911 : Blo 303832 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B1736639 : Blo 303832 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B688103 : Blo 303832 688103 := bstep (se 1 (by rfl) ⟨516077, by rfl⟩ : syracuseStep 688103 = 1032155) B1032155
theorem B459263 : Blo 303832 459263 := bstep (se 1 (by rfl) ⟨344447, by rfl⟩ : syracuseStep 459263 = 688895) B688895
theorem B459305 : Blo 303832 459305 := bstep (se 2 (by rfl) ⟨172239, by rfl⟩ : syracuseStep 459305 = 344479) B344479
theorem B492409 : Blo 303832 492409 := bstep (se 2 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 492409 = 369307) B369307
theorem B459647 : Blo 303832 459647 := bstep (se 1 (by rfl) ⟨344735, by rfl⟩ : syracuseStep 459647 = 689471) B689471
theorem B3474413 : Blo 303832 3474413 := bstep (se 3 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 3474413 = 1302905) B1302905
theorem B459803 : Blo 303832 459803 := bstep (se 1 (by rfl) ⟨344852, by rfl⟩ : syracuseStep 459803 = 689705) B689705
theorem B3933319 : Blo 303832 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B459959 : Blo 303832 459959 := bstep (se 1 (by rfl) ⟨344969, by rfl⟩ : syracuseStep 459959 = 689939) B689939
theorem B984383 : Blo 303832 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B886553 : Blo 303832 886553 := bstep (se 2 (by rfl) ⟨332457, by rfl⟩ : syracuseStep 886553 = 664915) B664915
theorem B690011 : Blo 303832 690011 := bstep (se 1 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 690011 = 1035017) B1035017
theorem B461087 : Blo 303832 461087 := bstep (se 1 (by rfl) ⟨345815, by rfl⟩ : syracuseStep 461087 = 691631) B691631
theorem B16648537 : Blo 303832 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B461291 : Blo 303832 461291 := bstep (se 1 (by rfl) ⟨345968, by rfl⟩ : syracuseStep 461291 = 691937) B691937
theorem B461543 : Blo 303832 461543 := bstep (se 1 (by rfl) ⟨346157, by rfl⟩ : syracuseStep 461543 = 692315) B692315
theorem B461567 : Blo 303832 461567 := bstep (se 1 (by rfl) ⟨346175, by rfl⟩ : syracuseStep 461567 = 692351) B692351
theorem B691739 : Blo 303832 691739 := bstep (se 1 (by rfl) ⟨518804, by rfl⟩ : syracuseStep 691739 = 1037609) B1037609
theorem B2102527 : Blo 303832 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B7477285 : Blo 303832 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B2955527 : Blo 303832 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B2234735 : Blo 303832 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B1153871 : Blo 303832 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B1186751 : Blo 303832 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B1154159 : Blo 303832 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B12361135 : Blo 303832 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B827263 : Blo 303832 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B13279463 : Blo 303832 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B303847 : Blo 303832 303847 := bstep (se 1 (by rfl) ⟨227885, by rfl⟩ : syracuseStep 303847 = 455771) B455771
theorem B303871 : Blo 303832 303871 := bstep (se 1 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 303871 = 455807) B455807
theorem B303943 : Blo 303832 303943 := bstep (se 1 (by rfl) ⟨227957, by rfl⟩ : syracuseStep 303943 = 455915) B455915
theorem B5284943 : Blo 303832 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B1156315 : Blo 303832 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B304379 : Blo 303832 304379 := bstep (se 1 (by rfl) ⟨228284, by rfl⟩ : syracuseStep 304379 = 456569) B456569
theorem B304847 : Blo 303832 304847 := bstep (se 1 (by rfl) ⟨228635, by rfl⟩ : syracuseStep 304847 = 457271) B457271
theorem B927485 : Blo 303832 927485 := bstep (se 3 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 927485 = 347807) B347807
theorem B304895 : Blo 303832 304895 := bstep (se 1 (by rfl) ⟨228671, by rfl⟩ : syracuseStep 304895 = 457343) B457343
theorem B1157759 : Blo 303832 1157759 := bstep (se 1 (by rfl) ⟨868319, by rfl⟩ : syracuseStep 1157759 = 1736639) B1736639
theorem B305871 : Blo 303832 305871 := bstep (se 1 (by rfl) ⟨229403, by rfl⟩ : syracuseStep 305871 = 458807) B458807
theorem B305895 : Blo 303832 305895 := bstep (se 1 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 305895 = 458843) B458843
theorem B305903 : Blo 303832 305903 := bstep (se 1 (by rfl) ⟨229427, by rfl⟩ : syracuseStep 305903 = 458855) B458855
theorem B699529 : Blo 303832 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B8400131 : Blo 303832 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B306495 : Blo 303832 306495 := bstep (se 1 (by rfl) ⟨229871, by rfl⟩ : syracuseStep 306495 = 459743) B459743
theorem B438889 : Blo 303832 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B1028969 : Blo 303832 1028969 := bstep (se 2 (by rfl) ⟨385863, by rfl⟩ : syracuseStep 1028969 = 771727) B771727
theorem B865505 : Blo 303832 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B1030427 : Blo 303832 1030427 := bstep (se 1 (by rfl) ⟨772820, by rfl⟩ : syracuseStep 1030427 = 1545641) B1545641
theorem B1030697 : Blo 303832 1030697 := bstep (se 2 (by rfl) ⟨386511, by rfl⟩ : syracuseStep 1030697 = 773023) B773023
theorem B736057 : Blo 303832 736057 := bstep (se 2 (by rfl) ⟨276021, by rfl⟩ : syracuseStep 736057 = 552043) B552043
theorem B2210647 : Blo 303832 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B28786337 : Blo 303832 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B6569723 : Blo 303832 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B737267 : Blo 303832 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B5554183 : Blo 303832 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B1163393 : Blo 303832 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B1032695 : Blo 303832 1032695 := bstep (se 1 (by rfl) ⟨774521, by rfl⟩ : syracuseStep 1032695 = 1549043) B1549043
theorem B344731 : Blo 303832 344731 := bstep (se 1 (by rfl) ⟨258548, by rfl⟩ : syracuseStep 344731 = 517097) B517097
theorem B14828453 : Blo 303832 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B6341777 : Blo 303832 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B345343 : Blo 303832 345343 := bstep (se 1 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 345343 = 518015) B518015
theorem B1034153 : Blo 303832 1034153 := bstep (se 2 (by rfl) ⟨387807, by rfl⟩ : syracuseStep 1034153 = 775615) B775615
theorem B772051 : Blo 303832 772051 := bstep (se 1 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 772051 = 1158077) B1158077
theorem B772841 : Blo 303832 772841 := bstep (se 2 (by rfl) ⟨289815, by rfl⟩ : syracuseStep 772841 = 579631) B579631
theorem B1035449 : Blo 303832 1035449 := bstep (se 2 (by rfl) ⟨388293, by rfl⟩ : syracuseStep 1035449 = 776587) B776587
theorem B1397321 : Blo 303832 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B1036907 : Blo 303832 1036907 := bstep (se 1 (by rfl) ⟨777680, by rfl⟩ : syracuseStep 1036907 = 1555361) B1555361
theorem B5001851 : Blo 303832 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B1168253 : Blo 303832 1168253 := bstep (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) B438095
theorem B578431 : Blo 303832 578431 := bstep (se 1 (by rfl) ⟨433823, by rfl⟩ : syracuseStep 578431 = 867647) B867647
theorem B1038203 : Blo 303832 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B3529207 : Blo 303832 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B514795 : Blo 303832 514795 := bstep (se 1 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 514795 = 772193) B772193
theorem B514937 : Blo 303832 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B515639 : Blo 303832 515639 := bstep (se 1 (by rfl) ⟨386729, by rfl⟩ : syracuseStep 515639 = 773459) B773459
theorem B529915877 : Blo 303832 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B1106075 : Blo 303832 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B516287 : Blo 303832 516287 := bstep (se 1 (by rfl) ⟨387215, by rfl⟩ : syracuseStep 516287 = 774431) B774431
theorem B1958255 : Blo 303832 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B516523 : Blo 303832 516523 := bstep (se 1 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 516523 = 774785) B774785
theorem B516847 : Blo 303832 516847 := bstep (se 1 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 516847 = 775271) B775271
theorem B516935 : Blo 303832 516935 := bstep (se 1 (by rfl) ⟨387701, by rfl⟩ : syracuseStep 516935 = 775403) B775403
theorem B3499199 : Blo 303832 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B2319677 : Blo 303832 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B583033 : Blo 303832 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B976283 : Blo 303832 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B386527 : Blo 303832 386527 := bstep (se 1 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 386527 = 579791) B579791
theorem B1959461 : Blo 303832 1959461 := bstep (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) B367399
theorem B1468115 : Blo 303832 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B2190235 : Blo 303832 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B5205059 : Blo 303832 5205059 := bstep (se 1 (by rfl) ⟨3903794, by rfl⟩ : syracuseStep 5205059 = 7807589) B7807589
theorem B1731739 : Blo 303832 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B519419 : Blo 303832 519419 := bstep (se 1 (by rfl) ⟨389564, by rfl⟩ : syracuseStep 519419 = 779129) B779129
theorem B585247 : Blo 303832 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B1044191 : Blo 303832 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B1175419 : Blo 303832 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B553081 : Blo 303832 553081 := bstep (se 2 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 553081 = 414811) B414811
theorem B488123 : Blo 303832 488123 := bstep (se 1 (by rfl) ⟨366092, by rfl⟩ : syracuseStep 488123 = 732185) B732185
theorem B685025 : Blo 303832 685025 := bstep (se 2 (by rfl) ⟨256884, by rfl⟩ : syracuseStep 685025 = 513769) B513769
theorem B980153 : Blo 303832 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B685367 : Blo 303832 685367 := bstep (se 1 (by rfl) ⟨514025, by rfl⟩ : syracuseStep 685367 = 1028051) B1028051
theorem B1177055 : Blo 303832 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B980819 : Blo 303832 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B456551 : Blo 303832 456551 := bstep (se 1 (by rfl) ⟨342413, by rfl⟩ : syracuseStep 456551 = 684827) B684827
theorem B77559761 : Blo 303832 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B95647715 : Blo 303832 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B653359 : Blo 303832 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B326111 : Blo 303832 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B457865 : Blo 303832 457865 := bstep (se 2 (by rfl) ⟨171699, by rfl⟩ : syracuseStep 457865 = 343399) B343399
theorem B457895 : Blo 303832 457895 := bstep (se 1 (by rfl) ⟨343421, by rfl⟩ : syracuseStep 457895 = 686843) B686843
theorem B457919 : Blo 303832 457919 := bstep (se 1 (by rfl) ⟨343439, by rfl⟩ : syracuseStep 457919 = 686879) B686879
theorem B1047881 : Blo 303832 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B687689 : Blo 303832 687689 := bstep (se 2 (by rfl) ⟨257883, by rfl⟩ : syracuseStep 687689 = 515767) B515767
theorem B688031 : Blo 303832 688031 := bstep (se 1 (by rfl) ⟨516023, by rfl⟩ : syracuseStep 688031 = 1032047) B1032047
theorem B458735 : Blo 303832 458735 := bstep (se 1 (by rfl) ⟨344051, by rfl⟩ : syracuseStep 458735 = 688103) B688103
theorem B7405577 : Blo 303832 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B688463 : Blo 303832 688463 := bstep (se 1 (by rfl) ⟨516347, by rfl⟩ : syracuseStep 688463 = 1032695) B1032695
theorem B2949533 : Blo 303832 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B688697 : Blo 303832 688697 := bstep (se 2 (by rfl) ⟨258261, by rfl⟩ : syracuseStep 688697 = 516523) B516523
theorem B4227851 : Blo 303832 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B459641 : Blo 303832 459641 := bstep (se 2 (by rfl) ⟨172365, by rfl⟩ : syracuseStep 459641 = 344731) B344731
theorem B656255 : Blo 303832 656255 := bstep (se 1 (by rfl) ⟨492191, by rfl⟩ : syracuseStep 656255 = 984383) B984383
theorem B689129 : Blo 303832 689129 := bstep (se 2 (by rfl) ⟨258423, by rfl⟩ : syracuseStep 689129 = 516847) B516847
theorem B656545 : Blo 303832 656545 := bstep (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) B492409
theorem B591035 : Blo 303832 591035 := bstep (se 1 (by rfl) ⟨443276, by rfl⟩ : syracuseStep 591035 = 886553) B886553
theorem B460007 : Blo 303832 460007 := bstep (se 1 (by rfl) ⟨345005, by rfl⟩ : syracuseStep 460007 = 690011) B690011
theorem B689435 : Blo 303832 689435 := bstep (se 1 (by rfl) ⟨517076, by rfl⟩ : syracuseStep 689435 = 1034153) B1034153
theorem B5244425 : Blo 303832 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B1541753 : Blo 303832 1541753 := bstep (se 2 (by rfl) ⟨578157, by rfl⟩ : syracuseStep 1541753 = 1156315) B1156315
theorem B460457 : Blo 303832 460457 := bstep (se 2 (by rfl) ⟨172671, by rfl⟩ : syracuseStep 460457 = 345343) B345343
theorem B690299 : Blo 303832 690299 := bstep (se 1 (by rfl) ⟨517724, by rfl⟩ : syracuseStep 690299 = 1035449) B1035449
theorem B461159 : Blo 303832 461159 := bstep (se 1 (by rfl) ⟨345869, by rfl⟩ : syracuseStep 461159 = 691739) B691739
theorem B691271 : Blo 303832 691271 := bstep (se 1 (by rfl) ⟨518453, by rfl⟩ : syracuseStep 691271 = 1036907) B1036907
theorem B2920313 : Blo 303832 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B692135 : Blo 303832 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B1970351 : Blo 303832 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B791167 : Blo 303832 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B353277251 : Blo 303832 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B8852975 : Blo 303832 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B2332799 : Blo 303832 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B1546451 : Blo 303832 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B696127 : Blo 303832 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B9969713 : Blo 303832 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B304367 : Blo 303832 304367 := bstep (se 1 (by rfl) ⟨228275, by rfl⟩ : syracuseStep 304367 = 456551) B456551
theorem B305243 : Blo 303832 305243 := bstep (se 1 (by rfl) ⟨228932, by rfl⟩ : syracuseStep 305243 = 457865) B457865
theorem B305263 : Blo 303832 305263 := bstep (se 1 (by rfl) ⟨228947, by rfl⟩ : syracuseStep 305263 = 457895) B457895
theorem B305279 : Blo 303832 305279 := bstep (se 1 (by rfl) ⟨228959, by rfl⟩ : syracuseStep 305279 = 457919) B457919
theorem B698587 : Blo 303832 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B305823 : Blo 303832 305823 := bstep (se 1 (by rfl) ⟨229367, by rfl⟩ : syracuseStep 305823 = 458735) B458735
theorem B306175 : Blo 303832 306175 := bstep (se 1 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 306175 = 459263) B459263
theorem B306203 : Blo 303832 306203 := bstep (se 1 (by rfl) ⟨229652, by rfl⟩ : syracuseStep 306203 = 459305) B459305
theorem B306431 : Blo 303832 306431 := bstep (se 1 (by rfl) ⟨229823, by rfl⟩ : syracuseStep 306431 = 459647) B459647
theorem B306535 : Blo 303832 306535 := bstep (se 1 (by rfl) ⟨229901, by rfl⟩ : syracuseStep 306535 = 459803) B459803
theorem B306639 : Blo 303832 306639 := bstep (se 1 (by rfl) ⟨229979, by rfl⟩ : syracuseStep 306639 = 459959) B459959
theorem B307391 : Blo 303832 307391 := bstep (se 1 (by rfl) ⟨230543, by rfl⟩ : syracuseStep 307391 = 461087) B461087
theorem B307527 : Blo 303832 307527 := bstep (se 1 (by rfl) ⟨230645, by rfl⟩ : syracuseStep 307527 = 461291) B461291
theorem B307695 : Blo 303832 307695 := bstep (se 1 (by rfl) ⟨230771, by rfl⟩ : syracuseStep 307695 = 461543) B461543
theorem B307711 : Blo 303832 307711 := bstep (se 1 (by rfl) ⟨230783, by rfl⟩ : syracuseStep 307711 = 461567) B461567
theorem B1029401 : Blo 303832 1029401 := bstep (se 2 (by rfl) ⟨386025, by rfl⟩ : syracuseStep 1029401 = 772051) B772051
theorem B931547 : Blo 303832 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B22198049 : Blo 303832 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B2308013 : Blo 303832 2308013 := bstep (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) B865505
theorem B932705 : Blo 303832 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B2308985 : Blo 303832 2308985 := bstep (se 2 (by rfl) ⟨865869, by rfl⟩ : syracuseStep 2308985 = 1731739) B1731739
theorem B1489823 : Blo 303832 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B769247 : Blo 303832 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B343291 : Blo 303832 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B769439 : Blo 303832 769439 := bstep (se 1 (by rfl) ⟨577079, by rfl⟩ : syracuseStep 769439 = 1154159) B1154159
theorem B343759 : Blo 303832 343759 := bstep (se 1 (by rfl) ⟨257819, by rfl⟩ : syracuseStep 343759 = 515639) B515639
theorem B344191 : Blo 303832 344191 := bstep (se 1 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 344191 = 516287) B516287
theorem B737441 : Blo 303832 737441 := bstep (se 2 (by rfl) ⟨276540, by rfl⟩ : syracuseStep 737441 = 553081) B553081
theorem B344623 : Blo 303832 344623 := bstep (se 1 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 344623 = 516935) B516935
theorem B3523295 : Blo 303832 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B771241 : Blo 303832 771241 := bstep (se 2 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 771241 = 578431) B578431
theorem B869629 : Blo 303832 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B2803369 : Blo 303832 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B771839 : Blo 303832 771839 := bstep (se 1 (by rfl) ⟨578879, by rfl⟩ : syracuseStep 771839 = 1157759) B1157759
theorem B346279 : Blo 303832 346279 := bstep (se 1 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 346279 = 519419) B519419
theorem B871145 : Blo 303832 871145 := bstep (se 2 (by rfl) ⟨326679, by rfl⟩ : syracuseStep 871145 = 653359) B653359
theorem B4705609 : Blo 303832 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B4412069 : Blo 303832 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B19190891 : Blo 303832 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B4379815 : Blo 303832 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B775595 : Blo 303832 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B9885635 : Blo 303832 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B2316275 : Blo 303832 2316275 := bstep (se 1 (by rfl) ⟨1737206, by rfl⟩ : syracuseStep 2316275 = 3474413) B3474413
theorem B515227 : Blo 303832 515227 := bstep (se 1 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 515227 = 772841) B772841
theorem B777377 : Blo 303832 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B515369 : Blo 303832 515369 := bstep (se 2 (by rfl) ⟨193263, by rfl⟩ : syracuseStep 515369 = 386527) B386527
theorem B3334567 : Blo 303832 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B778835 : Blo 303832 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B780329 : Blo 303832 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1567225 : Blo 303832 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B1305503 : Blo 303832 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B585185 : Blo 303832 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B650855 : Blo 303832 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B1306307 : Blo 303832 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B978743 : Blo 303832 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B618323 : Blo 303832 618323 := bstep (se 1 (by rfl) ⟨463742, by rfl⟩ : syracuseStep 618323 = 927485) B927485
theorem B3470039 : Blo 303832 3470039 := bstep (se 1 (by rfl) ⟨2602529, by rfl⟩ : syracuseStep 3470039 = 5205059) B5205059
theorem B5600087 : Blo 303832 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B325415 : Blo 303832 325415 := bstep (se 1 (by rfl) ⟨244061, by rfl⟩ : syracuseStep 325415 = 488123) B488123
theorem B685979 : Blo 303832 685979 := bstep (se 1 (by rfl) ⟨514484, by rfl⟩ : syracuseStep 685979 = 1028969) B1028969
theorem B456683 : Blo 303832 456683 := bstep (se 1 (by rfl) ⟨342512, by rfl⟩ : syracuseStep 456683 = 685025) B685025
theorem B653435 : Blo 303832 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B456911 : Blo 303832 456911 := bstep (se 1 (by rfl) ⟨342683, by rfl⟩ : syracuseStep 456911 = 685367) B685367
theorem B686393 : Blo 303832 686393 := bstep (se 2 (by rfl) ⟨257397, by rfl⟩ : syracuseStep 686393 = 514795) B514795
theorem B784703 : Blo 303832 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B981409 : Blo 303832 981409 := bstep (se 2 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 981409 = 736057) B736057
theorem B2947529 : Blo 303832 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B653879 : Blo 303832 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B51706507 : Blo 303832 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B63765143 : Blo 303832 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B686951 : Blo 303832 686951 := bstep (se 1 (by rfl) ⟨515213, by rfl⟩ : syracuseStep 686951 = 1030427) B1030427
theorem B687131 : Blo 303832 687131 := bstep (se 1 (by rfl) ⟨515348, by rfl⟩ : syracuseStep 687131 = 1030697) B1030697
theorem B16481513 : Blo 303832 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B458459 : Blo 303832 458459 := bstep (se 1 (by rfl) ⟨343844, by rfl⟩ : syracuseStep 458459 = 687689) B687689
theorem B458687 : Blo 303832 458687 := bstep (se 1 (by rfl) ⟨344015, by rfl⟩ : syracuseStep 458687 = 688031) B688031
theorem B1966045 : Blo 303832 1966045 := bstep (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) B737267
theorem B491627 : Blo 303832 491627 := bstep (se 1 (by rfl) ⟨368720, by rfl⟩ : syracuseStep 491627 = 737441) B737441
theorem B458921 : Blo 303832 458921 := bstep (se 2 (by rfl) ⟨172095, by rfl⟩ : syracuseStep 458921 = 344191) B344191
theorem B458975 : Blo 303832 458975 := bstep (se 1 (by rfl) ⟨344231, by rfl⟩ : syracuseStep 458975 = 688463) B688463
theorem B1966355 : Blo 303832 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B459131 : Blo 303832 459131 := bstep (se 1 (by rfl) ⟨344348, by rfl⟩ : syracuseStep 459131 = 688697) B688697
theorem B2818567 : Blo 303832 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B459419 : Blo 303832 459419 := bstep (se 1 (by rfl) ⟨344564, by rfl⟩ : syracuseStep 459419 = 689129) B689129
theorem B459497 : Blo 303832 459497 := bstep (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) B344623
theorem B459623 : Blo 303832 459623 := bstep (se 1 (by rfl) ⟨344717, by rfl⟩ : syracuseStep 459623 = 689435) B689435
theorem B460199 : Blo 303832 460199 := bstep (se 1 (by rfl) ⟨345149, by rfl⟩ : syracuseStep 460199 = 690299) B690299
theorem B460847 : Blo 303832 460847 := bstep (se 1 (by rfl) ⟨345635, by rfl⟩ : syracuseStep 460847 = 691271) B691271
theorem B3737825 : Blo 303832 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B461423 : Blo 303832 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B1313567 : Blo 303832 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B461705 : Blo 303832 461705 := bstep (se 2 (by rfl) ⟨173139, by rfl⟩ : syracuseStep 461705 = 346279) B346279
theorem B1576093 : Blo 303832 1576093 := bstep (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) B591035
theorem B5901983 : Blo 303832 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B6590423 : Blo 303832 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B1544183 : Blo 303832 1544183 := bstep (se 1 (by rfl) ⟨1158137, by rfl⟩ : syracuseStep 1544183 = 2316275) B2316275
theorem B1054889 : Blo 303832 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B1743677 : Blo 303832 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B43950701 : Blo 303832 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B6595445 : Blo 303832 6595445 := bstep (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) B618323
theorem B304455 : Blo 303832 304455 := bstep (se 1 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 304455 = 456683) B456683
theorem B435623 : Blo 303832 435623 := bstep (se 1 (by rfl) ⟨326717, by rfl⟩ : syracuseStep 435623 = 653435) B653435
theorem B304607 : Blo 303832 304607 := bstep (se 1 (by rfl) ⟨228455, by rfl⟩ : syracuseStep 304607 = 456911) B456911
theorem B42510095 : Blo 303832 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B993215 : Blo 303832 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B928169 : Blo 303832 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B305639 : Blo 303832 305639 := bstep (se 1 (by rfl) ⟨229229, by rfl⟩ : syracuseStep 305639 = 458459) B458459
theorem B305791 : Blo 303832 305791 := bstep (se 1 (by rfl) ⟨229343, by rfl⟩ : syracuseStep 305791 = 458687) B458687
theorem B306427 : Blo 303832 306427 := bstep (se 1 (by rfl) ⟨229820, by rfl⟩ : syracuseStep 306427 = 459641) B459641
theorem B437503 : Blo 303832 437503 := bstep (se 1 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 437503 = 656255) B656255
theorem B306671 : Blo 303832 306671 := bstep (se 1 (by rfl) ⟨230003, by rfl⟩ : syracuseStep 306671 = 460007) B460007
theorem B1027835 : Blo 303832 1027835 := bstep (se 1 (by rfl) ⟨770876, by rfl⟩ : syracuseStep 1027835 = 1541753) B1541753
theorem B306971 : Blo 303832 306971 := bstep (se 1 (by rfl) ⟨230228, by rfl⟩ : syracuseStep 306971 = 460457) B460457
theorem B1028321 : Blo 303832 1028321 := bstep (se 2 (by rfl) ⟨385620, by rfl⟩ : syracuseStep 1028321 = 771241) B771241
theorem B307439 : Blo 303832 307439 := bstep (se 1 (by rfl) ⟨230579, by rfl⟩ : syracuseStep 307439 = 461159) B461159
theorem B1159505 : Blo 303832 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B1946875 : Blo 303832 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B235518167 : Blo 303832 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B1555199 : Blo 303832 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B1030967 : Blo 303832 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B6274145 : Blo 303832 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B867773 : Blo 303832 867773 := bstep (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) B325415
theorem B343579 : Blo 303832 343579 := bstep (se 1 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 343579 = 515369) B515369
theorem B870335 : Blo 303832 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B870871 : Blo 303832 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B2313359 : Blo 303832 2313359 := bstep (se 1 (by rfl) ⟨1735019, by rfl⟩ : syracuseStep 2313359 = 3470039) B3470039
theorem B14798699 : Blo 303832 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B1560493 : Blo 303832 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B2609981 : Blo 303832 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B512831 : Blo 303832 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B512959 : Blo 303832 512959 := bstep (se 1 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 512959 = 769439) B769439
theorem B4937051 : Blo 303832 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B4446089 : Blo 303832 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B3496283 : Blo 303832 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B514559 : Blo 303832 514559 := bstep (se 1 (by rfl) ⟨385919, by rfl⟩ : syracuseStep 514559 = 771839) B771839
theorem B875393 : Blo 303832 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B580763 : Blo 303832 580763 := bstep (se 1 (by rfl) ⟨435572, by rfl⟩ : syracuseStep 580763 = 871145) B871145
theorem B9395453 : Blo 303832 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B51175709 : Blo 303832 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B2941379 : Blo 303832 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B2089633 : Blo 303832 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B517063 : Blo 303832 517063 := bstep (se 1 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 517063 = 775595) B775595
theorem B14903189 : Blo 303832 14903189 := bstep (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) B698587
theorem B2484125 : Blo 303832 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B518251 : Blo 303832 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B6646475 : Blo 303832 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B519223 : Blo 303832 519223 := bstep (se 1 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 519223 = 778835) B778835
theorem B23359013 : Blo 303832 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B7860077 : Blo 303832 7860077 := bstep (se 3 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 7860077 = 2947529) B2947529
theorem B520219 : Blo 303832 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B1308545 : Blo 303832 1308545 := bstep (se 2 (by rfl) ⟨490704, by rfl⟩ : syracuseStep 1308545 = 981409) B981409
theorem B3733391 : Blo 303832 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B68942009 : Blo 303832 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B686267 : Blo 303832 686267 := bstep (se 1 (by rfl) ⟨514700, by rfl⟩ : syracuseStep 686267 = 1029401) B1029401
theorem B457319 : Blo 303832 457319 := bstep (se 1 (by rfl) ⟨342989, by rfl⟩ : syracuseStep 457319 = 685979) B685979
theorem B1538675 : Blo 303832 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B686969 : Blo 303832 686969 := bstep (se 2 (by rfl) ⟨257613, by rfl⟩ : syracuseStep 686969 = 515227) B515227
theorem B457595 : Blo 303832 457595 := bstep (se 1 (by rfl) ⟨343196, by rfl⟩ : syracuseStep 457595 = 686393) B686393
theorem B523135 : Blo 303832 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B1735613 : Blo 303832 1735613 := bstep (se 3 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 1735613 = 650855) B650855
theorem B457721 : Blo 303832 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B621803 : Blo 303832 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B457967 : Blo 303832 457967 := bstep (se 1 (by rfl) ⟨343475, by rfl⟩ : syracuseStep 457967 = 686951) B686951
theorem B1539323 : Blo 303832 1539323 := bstep (se 1 (by rfl) ⟨1154492, by rfl⟩ : syracuseStep 1539323 = 2308985) B2308985
theorem B458087 : Blo 303832 458087 := bstep (se 1 (by rfl) ⟨343565, by rfl⟩ : syracuseStep 458087 = 687131) B687131
theorem B458345 : Blo 303832 458345 := bstep (se 2 (by rfl) ⟨171879, by rfl⟩ : syracuseStep 458345 = 343759) B343759
theorem B2621393 : Blo 303832 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B1310903 : Blo 303832 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1311005 : Blo 303832 1311005 := bstep (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) B491627
theorem B2786177 : Blo 303832 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B689417 : Blo 303832 689417 := bstep (se 2 (by rfl) ⟨258531, by rfl⟩ : syracuseStep 689417 = 517063) B517063
theorem B2491883 : Blo 303832 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B1542239 : Blo 303832 1542239 := bstep (se 1 (by rfl) ⟨1156679, by rfl⟩ : syracuseStep 1542239 = 2313359) B2313359
theorem B3934655 : Blo 303832 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B9865799 : Blo 303832 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B4393615 : Blo 303832 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B691001 : Blo 303832 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B1739987 : Blo 303832 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B692297 : Blo 303832 692297 := bstep (se 2 (by rfl) ⟨259611, by rfl⟩ : syracuseStep 692297 = 519223) B519223
theorem B2101457 : Blo 303832 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B2330855 : Blo 303832 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B6263635 : Blo 303832 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B693625 : Blo 303832 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B34117139 : Blo 303832 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B29300467 : Blo 303832 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B4396963 : Blo 303832 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B9935459 : Blo 303832 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B662143 : Blo 303832 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B2595833 : Blo 303832 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B4430983 : Blo 303832 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B15572675 : Blo 303832 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B697513 : Blo 303832 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B304879 : Blo 303832 304879 := bstep (se 1 (by rfl) ⟨228659, by rfl⟩ : syracuseStep 304879 = 457319) B457319
theorem B1025783 : Blo 303832 1025783 := bstep (se 1 (by rfl) ⟨769337, by rfl⟩ : syracuseStep 1025783 = 1538675) B1538675
theorem B305063 : Blo 303832 305063 := bstep (se 1 (by rfl) ⟨228797, by rfl⟩ : syracuseStep 305063 = 457595) B457595
theorem B1157075 : Blo 303832 1157075 := bstep (se 1 (by rfl) ⟨867806, by rfl⟩ : syracuseStep 1157075 = 1735613) B1735613
theorem B305147 : Blo 303832 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B305311 : Blo 303832 305311 := bstep (se 1 (by rfl) ⟨228983, by rfl⟩ : syracuseStep 305311 = 457967) B457967
theorem B1026215 : Blo 303832 1026215 := bstep (se 1 (by rfl) ⟨769661, by rfl⟩ : syracuseStep 1026215 = 1539323) B1539323
theorem B305391 : Blo 303832 305391 := bstep (se 1 (by rfl) ⟨229043, by rfl⟩ : syracuseStep 305391 = 458087) B458087
theorem B305563 : Blo 303832 305563 := bstep (se 1 (by rfl) ⟨229172, by rfl⟩ : syracuseStep 305563 = 458345) B458345
theorem B1747595 : Blo 303832 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B305947 : Blo 303832 305947 := bstep (se 1 (by rfl) ⟨229460, by rfl⟩ : syracuseStep 305947 = 458921) B458921
theorem B305983 : Blo 303832 305983 := bstep (se 1 (by rfl) ⟨229487, by rfl⟩ : syracuseStep 305983 = 458975) B458975
theorem B306087 : Blo 303832 306087 := bstep (se 1 (by rfl) ⟨229565, by rfl⟩ : syracuseStep 306087 = 459131) B459131
theorem B306279 : Blo 303832 306279 := bstep (se 1 (by rfl) ⟨229709, by rfl⟩ : syracuseStep 306279 = 459419) B459419
theorem B306331 : Blo 303832 306331 := bstep (se 1 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 306331 = 459497) B459497
theorem B306415 : Blo 303832 306415 := bstep (se 1 (by rfl) ⟨229811, by rfl⟩ : syracuseStep 306415 = 459623) B459623
theorem B306799 : Blo 303832 306799 := bstep (se 1 (by rfl) ⟨230099, by rfl⟩ : syracuseStep 306799 = 460199) B460199
theorem B307231 : Blo 303832 307231 := bstep (se 1 (by rfl) ⟨230423, by rfl⟩ : syracuseStep 307231 = 460847) B460847
theorem B307615 : Blo 303832 307615 := bstep (se 1 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 307615 = 461423) B461423
theorem B307803 : Blo 303832 307803 := bstep (se 1 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 307803 = 461705) B461705
theorem B1029455 : Blo 303832 1029455 := bstep (se 1 (by rfl) ⟨772091, by rfl⟩ : syracuseStep 1029455 = 1544183) B1544183
theorem B341887 : Blo 303832 341887 := bstep (se 1 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 341887 = 512831) B512831
theorem B1161161 : Blo 303832 1161161 := bstep (se 2 (by rfl) ⟨435435, by rfl⟩ : syracuseStep 1161161 = 870871) B870871
theorem B3291367 : Blo 303832 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B1161661 : Blo 303832 1161661 := bstep (se 3 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 1161661 = 435623) B435623
theorem B2964059 : Blo 303832 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B703259 : Blo 303832 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B343039 : Blo 303832 343039 := bstep (se 1 (by rfl) ⟨257279, by rfl⟩ : syracuseStep 343039 = 514559) B514559
theorem B1162451 : Blo 303832 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B2080657 : Blo 303832 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1656083 : Blo 303832 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B773003 : Blo 303832 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B1658141 : Blo 303832 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B872363 : Blo 303832 872363 := bstep (se 1 (by rfl) ⟨654272, by rfl⟩ : syracuseStep 872363 = 1308545) B1308545
theorem B45961339 : Blo 303832 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B157012111 : Blo 303832 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B1036799 : Blo 303832 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B4182763 : Blo 303832 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B578515 : Blo 303832 578515 := bstep (se 1 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 578515 = 867773) B867773
theorem B3758089 : Blo 303832 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B580223 : Blo 303832 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B875711 : Blo 303832 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B583337 : Blo 303832 583337 := bstep (se 2 (by rfl) ⟨218751, by rfl⟩ : syracuseStep 583337 = 437503) B437503
theorem B583595 : Blo 303832 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B387175 : Blo 303832 387175 := bstep (se 1 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 387175 = 580763) B580763
theorem B1960919 : Blo 303832 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B28340063 : Blo 303832 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B683945 : Blo 303832 683945 := bstep (se 2 (by rfl) ⟨256479, by rfl⟩ : syracuseStep 683945 = 512959) B512959
theorem B618779 : Blo 303832 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B685223 : Blo 303832 685223 := bstep (se 1 (by rfl) ⟨513917, by rfl⟩ : syracuseStep 685223 = 1027835) B1027835
theorem B5240051 : Blo 303832 5240051 := bstep (se 1 (by rfl) ⟨3930038, by rfl⟩ : syracuseStep 5240051 = 7860077) B7860077
theorem B685547 : Blo 303832 685547 := bstep (se 1 (by rfl) ⟨514160, by rfl⟩ : syracuseStep 685547 = 1028321) B1028321
theorem B2488927 : Blo 303832 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B457511 : Blo 303832 457511 := bstep (se 1 (by rfl) ⟨343133, by rfl⟩ : syracuseStep 457511 = 686267) B686267
theorem B687311 : Blo 303832 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B457979 : Blo 303832 457979 := bstep (se 1 (by rfl) ⟨343484, by rfl⟩ : syracuseStep 457979 = 686969) B686969
theorem B458105 : Blo 303832 458105 := bstep (se 2 (by rfl) ⟨171789, by rfl⟩ : syracuseStep 458105 = 343579) B343579
theorem B459611 : Blo 303832 459611 := bstep (se 1 (by rfl) ⟨344708, by rfl⟩ : syracuseStep 459611 = 689417) B689417
theorem B2623103 : Blo 303832 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B460667 : Blo 303832 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B461531 : Blo 303832 461531 := bstep (se 1 (by rfl) ⟨346148, by rfl⟩ : syracuseStep 461531 = 692297) B692297
theorem B691199 : Blo 303832 691199 := bstep (se 1 (by rfl) ⟨518399, by rfl⟩ : syracuseStep 691199 = 1036799) B1036799
theorem B22744759 : Blo 303832 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B6623639 : Blo 303832 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B61281785 : Blo 303832 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B5577017 : Blo 303832 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1547261 : Blo 303832 1547261 := bstep (se 3 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 1547261 = 580223) B580223
theorem B924833 : Blo 303832 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B39067289 : Blo 303832 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B2335229 : Blo 303832 2335229 := bstep (se 3 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 2335229 = 875711) B875711
theorem B1548881 : Blo 303832 1548881 := bstep (se 2 (by rfl) ⟨580830, by rfl⟩ : syracuseStep 1548881 = 1161661) B1161661
theorem B3318569 : Blo 303832 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B5907977 : Blo 303832 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B1976039 : Blo 303832 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B41527133 : Blo 303832 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B468839 : Blo 303832 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B305007 : Blo 303832 305007 := bstep (se 1 (by rfl) ⟨228755, by rfl⟩ : syracuseStep 305007 = 457511) B457511
theorem B305319 : Blo 303832 305319 := bstep (se 1 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 305319 = 457979) B457979
theorem B305403 : Blo 303832 305403 := bstep (se 1 (by rfl) ⟨229052, by rfl⟩ : syracuseStep 305403 = 458105) B458105
theorem B1650077 : Blo 303832 1650077 := bstep (se 3 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 1650077 = 618779) B618779
theorem B837397925 : Blo 303832 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B1028159 : Blo 303832 1028159 := bstep (se 1 (by rfl) ⟨771119, by rfl⟩ : syracuseStep 1028159 = 1542239) B1542239
theorem B930017 : Blo 303832 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B1159991 : Blo 303832 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1553903 : Blo 303832 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B771353 : Blo 303832 771353 := bstep (se 2 (by rfl) ⟨289257, by rfl⟩ : syracuseStep 771353 = 578515) B578515
theorem B771383 : Blo 303832 771383 := bstep (se 1 (by rfl) ⟨578537, by rfl⟩ : syracuseStep 771383 = 1157075) B1157075
theorem B1165063 : Blo 303832 1165063 := bstep (se 1 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 1165063 = 1747595) B1747595
theorem B18893375 : Blo 303832 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B3493367 : Blo 303832 3493367 := bstep (se 1 (by rfl) ⟨2620025, by rfl⟩ : syracuseStep 3493367 = 5240051) B5240051
theorem B774107 : Blo 303832 774107 := bstep (se 1 (by rfl) ⟨580580, by rfl⟩ : syracuseStep 774107 = 1161161) B1161161
theorem B11096837 : Blo 303832 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B774967 : Blo 303832 774967 := bstep (se 1 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 774967 = 1162451) B1162451
theorem B873935 : Blo 303832 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B874003 : Blo 303832 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B1857451 : Blo 303832 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B1661255 : Blo 303832 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B6577199 : Blo 303832 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B515335 : Blo 303832 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B1105427 : Blo 303832 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B581575 : Blo 303832 581575 := bstep (se 1 (by rfl) ⟨436181, by rfl⟩ : syracuseStep 581575 = 872363) B872363
theorem B516233 : Blo 303832 516233 := bstep (se 2 (by rfl) ⟨193587, by rfl⟩ : syracuseStep 516233 = 387175) B387175
theorem B1400971 : Blo 303832 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B4416221 : Blo 303832 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B5858153 : Blo 303832 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B1730555 : Blo 303832 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B8351513 : Blo 303832 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B388891 : Blo 303832 388891 := bstep (se 1 (by rfl) ⟨291668, by rfl⟩ : syracuseStep 388891 = 583337) B583337
theorem B683855 : Blo 303832 683855 := bstep (se 1 (by rfl) ⟨512891, by rfl⟩ : syracuseStep 683855 = 1025783) B1025783
theorem B389063 : Blo 303832 389063 := bstep (se 1 (by rfl) ⟨291797, by rfl⟩ : syracuseStep 389063 = 583595) B583595
theorem B684143 : Blo 303832 684143 := bstep (se 1 (by rfl) ⟨513107, by rfl⟩ : syracuseStep 684143 = 1026215) B1026215
theorem B1307279 : Blo 303832 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B455849 : Blo 303832 455849 := bstep (se 2 (by rfl) ⟨170943, by rfl⟩ : syracuseStep 455849 = 341887) B341887
theorem B5862617 : Blo 303832 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B455963 : Blo 303832 455963 := bstep (se 1 (by rfl) ⟨341972, by rfl⟩ : syracuseStep 455963 = 683945) B683945
theorem B5010785 : Blo 303832 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B4388489 : Blo 303832 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B456815 : Blo 303832 456815 := bstep (se 1 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 456815 = 685223) B685223
theorem B882857 : Blo 303832 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B686303 : Blo 303832 686303 := bstep (se 1 (by rfl) ⟨514727, by rfl⟩ : syracuseStep 686303 = 1029455) B1029455
theorem B457031 : Blo 303832 457031 := bstep (se 1 (by rfl) ⟨342773, by rfl⟩ : syracuseStep 457031 = 685547) B685547
theorem B457385 : Blo 303832 457385 := bstep (se 2 (by rfl) ⟨171519, by rfl⟩ : syracuseStep 457385 = 343039) B343039
theorem B458207 : Blo 303832 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B1867961 : Blo 303832 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B460799 : Blo 303832 460799 := bstep (se 1 (by rfl) ⟨345599, by rfl⟩ : syracuseStep 460799 = 691199) B691199
theorem B2328911 : Blo 303832 2328911 := bstep (se 1 (by rfl) ⟨1746683, by rfl⟩ : syracuseStep 2328911 = 3493367) B3493367
theorem B163418093 : Blo 303832 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B3905435 : Blo 303832 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B3938651 : Blo 303832 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B1317359 : Blo 303832 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1153703 : Blo 303832 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B303899 : Blo 303832 303899 := bstep (se 1 (by rfl) ⟨227924, by rfl⟩ : syracuseStep 303899 = 455849) B455849
theorem B3908411 : Blo 303832 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B303975 : Blo 303832 303975 := bstep (se 1 (by rfl) ⟨227981, by rfl⟩ : syracuseStep 303975 = 455963) B455963
theorem B2925659 : Blo 303832 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B304543 : Blo 303832 304543 := bstep (se 1 (by rfl) ⟨228407, by rfl⟩ : syracuseStep 304543 = 456815) B456815
theorem B304687 : Blo 303832 304687 := bstep (se 1 (by rfl) ⟨228515, by rfl⟩ : syracuseStep 304687 = 457031) B457031
theorem B304923 : Blo 303832 304923 := bstep (se 1 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 304923 = 457385) B457385
theorem B305471 : Blo 303832 305471 := bstep (se 1 (by rfl) ⟨229103, by rfl⟩ : syracuseStep 305471 = 458207) B458207
theorem B306407 : Blo 303832 306407 := bstep (se 1 (by rfl) ⟨229805, by rfl⟩ : syracuseStep 306407 = 459611) B459611
theorem B1748735 : Blo 303832 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B307111 : Blo 303832 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B3486077 : Blo 303832 3486077 := bstep (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) B1307279
theorem B12595583 : Blo 303832 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B307687 : Blo 303832 307687 := bstep (se 1 (by rfl) ⟨230765, by rfl⟩ : syracuseStep 307687 = 461531) B461531
theorem B1553417 : Blo 303832 1553417 := bstep (se 2 (by rfl) ⟨582531, by rfl⟩ : syracuseStep 1553417 = 1165063) B1165063
theorem B1031507 : Blo 303832 1031507 := bstep (se 1 (by rfl) ⟨773630, by rfl⟩ : syracuseStep 1031507 = 1547261) B1547261
theorem B30326345 : Blo 303832 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B736951 : Blo 303832 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B344155 : Blo 303832 344155 := bstep (se 1 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 344155 = 516233) B516233
theorem B1556819 : Blo 303832 1556819 := bstep (se 1 (by rfl) ⟨1167614, by rfl⟩ : syracuseStep 1556819 = 2335229) B2335229
theorem B1032587 : Blo 303832 1032587 := bstep (se 1 (by rfl) ⟨774440, by rfl⟩ : syracuseStep 1032587 = 1548881) B1548881
theorem B2212379 : Blo 303832 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B1033289 : Blo 303832 1033289 := bstep (se 2 (by rfl) ⟨387483, by rfl⟩ : syracuseStep 1033289 = 774967) B774967
theorem B312559 : Blo 303832 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B1165337 : Blo 303832 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B1100051 : Blo 303832 1100051 := bstep (se 1 (by rfl) ⟨825038, by rfl⟩ : syracuseStep 1100051 = 1650077) B1650077
theorem B2476601 : Blo 303832 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B773327 : Blo 303832 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B1035935 : Blo 303832 1035935 := bstep (se 1 (by rfl) ⟨776951, by rfl⟩ : syracuseStep 1035935 = 1553903) B1553903
theorem B1037501 : Blo 303832 1037501 := bstep (se 3 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 1037501 = 389063) B389063
theorem B775433 : Blo 303832 775433 := bstep (se 2 (by rfl) ⟨290787, by rfl⟩ : syracuseStep 775433 = 581575) B581575
theorem B514235 : Blo 303832 514235 := bstep (se 1 (by rfl) ⟨385676, by rfl⟩ : syracuseStep 514235 = 771353) B771353
theorem B514255 : Blo 303832 514255 := bstep (se 1 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 514255 = 771383) B771383
theorem B516071 : Blo 303832 516071 := bstep (se 1 (by rfl) ⟨387053, by rfl⟩ : syracuseStep 516071 = 774107) B774107
theorem B4415759 : Blo 303832 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B7397891 : Blo 303832 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B582623 : Blo 303832 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B1107503 : Blo 303832 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B4384799 : Blo 303832 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B616555 : Blo 303832 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B518521 : Blo 303832 518521 := bstep (se 2 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 518521 = 388891) B388891
theorem B26044859 : Blo 303832 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B2354285 : Blo 303832 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B2944147 : Blo 303832 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B14872045 : Blo 303832 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B27684755 : Blo 303832 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B558265283 : Blo 303832 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B5567675 : Blo 303832 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B455903 : Blo 303832 455903 := bstep (se 1 (by rfl) ⟨341927, by rfl⟩ : syracuseStep 455903 = 683855) B683855
theorem B685439 : Blo 303832 685439 := bstep (se 1 (by rfl) ⟨514079, by rfl⟩ : syracuseStep 685439 = 1028159) B1028159
theorem B456095 : Blo 303832 456095 := bstep (se 1 (by rfl) ⟨342071, by rfl⟩ : syracuseStep 456095 = 684143) B684143
theorem B620011 : Blo 303832 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B3340523 : Blo 303832 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B457535 : Blo 303832 457535 := bstep (se 1 (by rfl) ⟨343151, by rfl⟩ : syracuseStep 457535 = 686303) B686303
theorem B687113 : Blo 303832 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B458873 : Blo 303832 458873 := bstep (se 2 (by rfl) ⟨172077, by rfl⟩ : syracuseStep 458873 = 344155) B344155
theorem B1245307 : Blo 303832 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B688391 : Blo 303832 688391 := bstep (se 1 (by rfl) ⟨516293, by rfl⟩ : syracuseStep 688391 = 1032587) B1032587
theorem B1474919 : Blo 303832 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B688859 : Blo 303832 688859 := bstep (se 1 (by rfl) ⟨516644, by rfl⟩ : syracuseStep 688859 = 1033289) B1033289
theorem B690623 : Blo 303832 690623 := bstep (se 1 (by rfl) ⟨517967, by rfl⟩ : syracuseStep 690623 = 1035935) B1035935
theorem B822073 : Blo 303832 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B14847133 : Blo 303832 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B691361 : Blo 303832 691361 := bstep (se 2 (by rfl) ⟨259260, by rfl⟩ : syracuseStep 691361 = 518521) B518521
theorem B691667 : Blo 303832 691667 := bstep (se 1 (by rfl) ⟨518750, by rfl⟩ : syracuseStep 691667 = 1037501) B1037501
theorem B2625767 : Blo 303832 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B19829393 : Blo 303832 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B2923199 : Blo 303832 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B826681 : Blo 303832 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B18456503 : Blo 303832 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B8397055 : Blo 303832 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B303935 : Blo 303832 303935 := bstep (se 1 (by rfl) ⟨227951, by rfl⟩ : syracuseStep 303935 = 455903) B455903
theorem B304063 : Blo 303832 304063 := bstep (se 1 (by rfl) ⟨228047, by rfl⟩ : syracuseStep 304063 = 456095) B456095
theorem B305023 : Blo 303832 305023 := bstep (se 1 (by rfl) ⟨228767, by rfl⟩ : syracuseStep 305023 = 457535) B457535
theorem B307199 : Blo 303832 307199 := bstep (se 1 (by rfl) ⟨230399, by rfl⟩ : syracuseStep 307199 = 460799) B460799
theorem B733367 : Blo 303832 733367 := bstep (se 1 (by rfl) ⟨550025, by rfl⟩ : syracuseStep 733367 = 1100051) B1100051
theorem B1552607 : Blo 303832 1552607 := bstep (se 1 (by rfl) ⟨1164455, by rfl⟩ : syracuseStep 1552607 = 2328911) B2328911
theorem B1651067 : Blo 303832 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B2603623 : Blo 303832 2603623 := bstep (se 1 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 2603623 = 3905435) B3905435
theorem B342823 : Blo 303832 342823 := bstep (se 1 (by rfl) ⟨257117, by rfl⟩ : syracuseStep 342823 = 514235) B514235
theorem B769135 : Blo 303832 769135 := bstep (se 1 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 769135 = 1153703) B1153703
theorem B344047 : Blo 303832 344047 := bstep (se 1 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 344047 = 516071) B516071
theorem B4931927 : Blo 303832 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B2605607 : Blo 303832 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1950439 : Blo 303832 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B738335 : Blo 303832 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B69452957 : Blo 303832 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B1165823 : Blo 303832 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B6278093 : Blo 303832 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B1035611 : Blo 303832 1035611 := bstep (se 1 (by rfl) ⟨776708, by rfl⟩ : syracuseStep 1035611 = 1553417) B1553417
theorem B1037879 : Blo 303832 1037879 := bstep (se 1 (by rfl) ⟨778409, by rfl⟩ : syracuseStep 1037879 = 1556819) B1556819
theorem B776891 : Blo 303832 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B515551 : Blo 303832 515551 := bstep (se 1 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 515551 = 773327) B773327
theorem B108945395 : Blo 303832 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B516955 : Blo 303832 516955 := bstep (se 1 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 516955 = 775433) B775433
theorem B3925529 : Blo 303832 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B878239 : Blo 303832 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B2943839 : Blo 303832 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B8908061 : Blo 303832 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B388415 : Blo 303832 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B1666981 : Blo 303832 1666981 := bstep (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) B312559
theorem B2324051 : Blo 303832 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B685673 : Blo 303832 685673 := bstep (se 2 (by rfl) ⟨257127, by rfl⟩ : syracuseStep 685673 = 514255) B514255
theorem B372176855 : Blo 303832 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B456959 : Blo 303832 456959 := bstep (se 1 (by rfl) ⟨342719, by rfl⟩ : syracuseStep 456959 = 685439) B685439
theorem B458075 : Blo 303832 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B687671 : Blo 303832 687671 := bstep (se 1 (by rfl) ⟨515753, by rfl⟩ : syracuseStep 687671 = 1031507) B1031507
theorem B982601 : Blo 303832 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B20217563 : Blo 303832 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B458927 : Blo 303832 458927 := bstep (se 1 (by rfl) ⟨344195, by rfl⟩ : syracuseStep 458927 = 688391) B688391
theorem B983279 : Blo 303832 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B1737071 : Blo 303832 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B459239 : Blo 303832 459239 := bstep (se 1 (by rfl) ⟨344429, by rfl⟩ : syracuseStep 459239 = 688859) B688859
theorem B46301971 : Blo 303832 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B689273 : Blo 303832 689273 := bstep (se 2 (by rfl) ⟨258477, by rfl⟩ : syracuseStep 689273 = 516955) B516955
theorem B460415 : Blo 303832 460415 := bstep (se 1 (by rfl) ⟨345311, by rfl⟩ : syracuseStep 460415 = 690623) B690623
theorem B460907 : Blo 303832 460907 := bstep (se 1 (by rfl) ⟨345680, by rfl⟩ : syracuseStep 460907 = 691361) B691361
theorem B690407 : Blo 303832 690407 := bstep (se 1 (by rfl) ⟨517805, by rfl⟩ : syracuseStep 690407 = 1035611) B1035611
theorem B461111 : Blo 303832 461111 := bstep (se 1 (by rfl) ⟨345833, by rfl⟩ : syracuseStep 461111 = 691667) B691667
theorem B1968893 : Blo 303832 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B691919 : Blo 303832 691919 := bstep (se 1 (by rfl) ⟨518939, by rfl⟩ : syracuseStep 691919 = 1037879) B1037879
theorem B19796177 : Blo 303832 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B1549367 : Blo 303832 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B1025513 : Blo 303832 1025513 := bstep (se 2 (by rfl) ⟨384567, by rfl⟩ : syracuseStep 1025513 = 769135) B769135
theorem B304639 : Blo 303832 304639 := bstep (se 1 (by rfl) ⟨228479, by rfl⟩ : syracuseStep 304639 = 456959) B456959
theorem B8890565 : Blo 303832 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B305383 : Blo 303832 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B13478375 : Blo 303832 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B305915 : Blo 303832 305915 := bstep (se 1 (by rfl) ⟨229436, by rfl⟩ : syracuseStep 305915 = 458873) B458873
theorem B3287951 : Blo 303832 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B2600585 : Blo 303832 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B1750511 : Blo 303832 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B13219595 : Blo 303832 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B1096097 : Blo 303832 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B1948799 : Blo 303832 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B72630263 : Blo 303832 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B1035071 : Blo 303832 1035071 := bstep (se 1 (by rfl) ⟨776303, by rfl⟩ : syracuseStep 1035071 = 1552607) B1552607
theorem B1100711 : Blo 303832 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B1035773 : Blo 303832 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B1102241 : Blo 303832 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B1660409 : Blo 303832 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B11196073 : Blo 303832 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B777215 : Blo 303832 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B4185395 : Blo 303832 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B1170985 : Blo 303832 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B517927 : Blo 303832 517927 := bstep (se 1 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 517927 = 776891) B776891
theorem B2617019 : Blo 303832 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B1962559 : Blo 303832 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B488911 : Blo 303832 488911 := bstep (se 1 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 488911 = 733367) B733367
theorem B23754829 : Blo 303832 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B3471497 : Blo 303832 3471497 := bstep (se 2 (by rfl) ⟨1301811, by rfl⟩ : syracuseStep 3471497 = 2603623) B2603623
theorem B457097 : Blo 303832 457097 := bstep (se 2 (by rfl) ⟨171411, by rfl⟩ : syracuseStep 457097 = 342823) B342823
theorem B457115 : Blo 303832 457115 := bstep (se 1 (by rfl) ⟨342836, by rfl⟩ : syracuseStep 457115 = 685673) B685673
theorem B248117903 : Blo 303832 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B687401 : Blo 303832 687401 := bstep (se 2 (by rfl) ⟨257775, by rfl⟩ : syracuseStep 687401 = 515551) B515551
theorem B458447 : Blo 303832 458447 := bstep (se 1 (by rfl) ⟨343835, by rfl⟩ : syracuseStep 458447 = 687671) B687671
theorem B655067 : Blo 303832 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B49217341 : Blo 303832 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B458729 : Blo 303832 458729 := bstep (se 2 (by rfl) ⟨172023, by rfl⟩ : syracuseStep 458729 = 344047) B344047
theorem B2622077 : Blo 303832 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B459515 : Blo 303832 459515 := bstep (se 1 (by rfl) ⟨344636, by rfl⟩ : syracuseStep 459515 = 689273) B689273
theorem B61735961 : Blo 303832 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B460271 : Blo 303832 460271 := bstep (se 1 (by rfl) ⟨345203, by rfl⟩ : syracuseStep 460271 = 690407) B690407
theorem B1312595 : Blo 303832 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B690047 : Blo 303832 690047 := bstep (se 1 (by rfl) ⟨517535, by rfl⟩ : syracuseStep 690047 = 1035071) B1035071
theorem B690515 : Blo 303832 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B690569 : Blo 303832 690569 := bstep (se 2 (by rfl) ⟨258963, by rfl⟩ : syracuseStep 690569 = 517927) B517927
theorem B461279 : Blo 303832 461279 := bstep (se 1 (by rfl) ⟨345959, by rfl⟩ : syracuseStep 461279 = 691919) B691919
theorem B2790263 : Blo 303832 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B8985583 : Blo 303832 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B1744679 : Blo 303832 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B304731 : Blo 303832 304731 := bstep (se 1 (by rfl) ⟨228548, by rfl⟩ : syracuseStep 304731 = 457097) B457097
theorem B304743 : Blo 303832 304743 := bstep (se 1 (by rfl) ⟨228557, by rfl⟩ : syracuseStep 304743 = 457115) B457115
theorem B1746845 : Blo 303832 1746845 := bstep (se 3 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 1746845 = 655067) B655067
theorem B305631 : Blo 303832 305631 := bstep (se 1 (by rfl) ⟨229223, by rfl⟩ : syracuseStep 305631 = 458447) B458447
theorem B305819 : Blo 303832 305819 := bstep (se 1 (by rfl) ⟨229364, by rfl⟩ : syracuseStep 305819 = 458729) B458729
theorem B305951 : Blo 303832 305951 := bstep (se 1 (by rfl) ⟨229463, by rfl⟩ : syracuseStep 305951 = 458927) B458927
theorem B1158047 : Blo 303832 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B306159 : Blo 303832 306159 := bstep (se 1 (by rfl) ⟨229619, by rfl⟩ : syracuseStep 306159 = 459239) B459239
theorem B306943 : Blo 303832 306943 := bstep (se 1 (by rfl) ⟨230207, by rfl⟩ : syracuseStep 306943 = 460415) B460415
theorem B307271 : Blo 303832 307271 := bstep (se 1 (by rfl) ⟨230453, by rfl⟩ : syracuseStep 307271 = 460907) B460907
theorem B307407 : Blo 303832 307407 := bstep (se 1 (by rfl) ⟨230555, by rfl⟩ : syracuseStep 307407 = 461111) B461111
theorem B733807 : Blo 303832 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B734827 : Blo 303832 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B23708173 : Blo 303832 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1032911 : Blo 303832 1032911 := bstep (se 1 (by rfl) ⟨774683, by rfl⟩ : syracuseStep 1032911 = 1549367) B1549367
theorem B14928097 : Blo 303832 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B31673105 : Blo 303832 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B1167007 : Blo 303832 1167007 := bstep (se 1 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 1167007 = 1750511) B1750511
theorem B2314331 : Blo 303832 2314331 := bstep (se 1 (by rfl) ⟨1735748, by rfl⟩ : syracuseStep 2314331 = 3471497) B3471497
theorem B1561313 : Blo 303832 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B1299199 : Blo 303832 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B65623121 : Blo 303832 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B48420175 : Blo 303832 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B13197451 : Blo 303832 13197451 := bstep (se 1 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 13197451 = 19796177) B19796177
theorem B1106939 : Blo 303832 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B11691701 : Blo 303832 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B518143 : Blo 303832 518143 := bstep (se 1 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 518143 = 777215) B777215
theorem B2616745 : Blo 303832 2616745 := bstep (se 2 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 2616745 = 1962559) B1962559
theorem B683675 : Blo 303832 683675 := bstep (se 1 (by rfl) ⟨512756, by rfl⟩ : syracuseStep 683675 = 1025513) B1025513
theorem B2191967 : Blo 303832 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B651881 : Blo 303832 651881 := bstep (se 2 (by rfl) ⟨244455, by rfl⟩ : syracuseStep 651881 = 488911) B488911
theorem B1733723 : Blo 303832 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B8813063 : Blo 303832 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B165411935 : Blo 303832 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B458267 : Blo 303832 458267 := bstep (se 1 (by rfl) ⟨343700, by rfl⟩ : syracuseStep 458267 = 687401) B687401
theorem B17596601 : Blo 303832 17596601 := bstep (se 2 (by rfl) ⟨6598725, by rfl⟩ : syracuseStep 17596601 = 13197451) B13197451
theorem B688607 : Blo 303832 688607 := bstep (se 1 (by rfl) ⟨516455, by rfl⟩ : syracuseStep 688607 = 1032911) B1032911
theorem B41157307 : Blo 303832 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B460031 : Blo 303832 460031 := bstep (se 1 (by rfl) ⟨345023, by rfl⟩ : syracuseStep 460031 = 690047) B690047
theorem B460343 : Blo 303832 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B460379 : Blo 303832 460379 := bstep (se 1 (by rfl) ⟨345284, by rfl⟩ : syracuseStep 460379 = 690569) B690569
theorem B4163501 : Blo 303832 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B690857 : Blo 303832 690857 := bstep (se 2 (by rfl) ⟨259071, by rfl⟩ : syracuseStep 690857 = 518143) B518143
theorem B1542887 : Blo 303832 1542887 := bstep (se 1 (by rfl) ⟨1157165, by rfl⟩ : syracuseStep 1542887 = 2314331) B2314331
theorem B43748747 : Blo 303832 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B64560233 : Blo 303832 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B434587 : Blo 303832 434587 := bstep (se 1 (by rfl) ⟨325940, by rfl⟩ : syracuseStep 434587 = 651881) B651881
theorem B1155815 : Blo 303832 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B5875375 : Blo 303832 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B110274623 : Blo 303832 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B305511 : Blo 303832 305511 := bstep (se 1 (by rfl) ⟨229133, by rfl⟩ : syracuseStep 305511 = 458267) B458267
theorem B1748051 : Blo 303832 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B306343 : Blo 303832 306343 := bstep (se 1 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 306343 = 459515) B459515
theorem B306847 : Blo 303832 306847 := bstep (se 1 (by rfl) ⟨230135, by rfl⟩ : syracuseStep 306847 = 460271) B460271
theorem B307519 : Blo 303832 307519 := bstep (se 1 (by rfl) ⟨230639, by rfl⟩ : syracuseStep 307519 = 461279) B461279
theorem B21115403 : Blo 303832 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B19904129 : Blo 303832 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B3488993 : Blo 303832 3488993 := bstep (se 2 (by rfl) ⟨1308372, by rfl⟩ : syracuseStep 3488993 = 2616745) B2616745
theorem B1556009 : Blo 303832 1556009 := bstep (se 2 (by rfl) ⟨583503, by rfl⟩ : syracuseStep 1556009 = 1167007) B1167007
theorem B1163119 : Blo 303832 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B47923109 : Blo 303832 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B737959 : Blo 303832 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B1164563 : Blo 303832 1164563 := bstep (se 1 (by rfl) ⟨873422, by rfl⟩ : syracuseStep 1164563 = 1746845) B1746845
theorem B772031 : Blo 303832 772031 := bstep (se 1 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 772031 = 1158047) B1158047
theorem B1461311 : Blo 303832 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B31610897 : Blo 303832 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B875063 : Blo 303832 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B1860175 : Blo 303832 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B978409 : Blo 303832 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B1732265 : Blo 303832 1732265 := bstep (se 2 (by rfl) ⟨649599, by rfl⟩ : syracuseStep 1732265 = 1299199) B1299199
theorem B7794467 : Blo 303832 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B979769 : Blo 303832 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B455783 : Blo 303832 455783 := bstep (se 1 (by rfl) ⟨341837, by rfl⟩ : syracuseStep 455783 = 683675) B683675
theorem B11731067 : Blo 303832 11731067 := bstep (se 1 (by rfl) ⟨8798300, by rfl⟩ : syracuseStep 11731067 = 17596601) B17596601
theorem B459071 : Blo 303832 459071 := bstep (se 1 (by rfl) ⟨344303, by rfl⟩ : syracuseStep 459071 = 688607) B688607
theorem B983945 : Blo 303832 983945 := bstep (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) B737959
theorem B460571 : Blo 303832 460571 := bstep (se 1 (by rfl) ⟨345428, by rfl⟩ : syracuseStep 460571 = 690857) B690857
theorem B7833833 : Blo 303832 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B29165831 : Blo 303832 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B21073931 : Blo 303832 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B1154843 : Blo 303832 1154843 := bstep (se 1 (by rfl) ⟨866132, by rfl⟩ : syracuseStep 1154843 = 1732265) B1732265
theorem B5218181 : Blo 303832 5218181 := bstep (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) B978409
theorem B303855 : Blo 303832 303855 := bstep (se 1 (by rfl) ⟨227891, by rfl⟩ : syracuseStep 303855 = 455783) B455783
theorem B1550825 : Blo 303832 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B306687 : Blo 303832 306687 := bstep (se 1 (by rfl) ⟨230015, by rfl⟩ : syracuseStep 306687 = 460031) B460031
theorem B306895 : Blo 303832 306895 := bstep (se 1 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 306895 = 460343) B460343
theorem B306919 : Blo 303832 306919 := bstep (se 1 (by rfl) ⟨230189, by rfl⟩ : syracuseStep 306919 = 460379) B460379
theorem B1028591 : Blo 303832 1028591 := bstep (se 1 (by rfl) ⟨771443, by rfl⟩ : syracuseStep 1028591 = 1542887) B1542887
theorem B43040155 : Blo 303832 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B770543 : Blo 303832 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B73516415 : Blo 303832 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B1165367 : Blo 303832 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B5196311 : Blo 303832 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B14076935 : Blo 303832 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B1037339 : Blo 303832 1037339 := bstep (se 1 (by rfl) ⟨778004, by rfl⟩ : syracuseStep 1037339 = 1556009) B1556009
theorem B579449 : Blo 303832 579449 := bstep (se 2 (by rfl) ⟨217293, by rfl⟩ : syracuseStep 579449 = 434587) B434587
theorem B2480233 : Blo 303832 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B776375 : Blo 303832 776375 := bstep (se 1 (by rfl) ⟨582281, by rfl⟩ : syracuseStep 776375 = 1164563) B1164563
theorem B54876409 : Blo 303832 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B2775667 : Blo 303832 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B514687 : Blo 303832 514687 := bstep (se 1 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 514687 = 772031) B772031
theorem B974207 : Blo 303832 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B583375 : Blo 303832 583375 := bstep (se 1 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 583375 = 875063) B875063
theorem B653179 : Blo 303832 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B13269419 : Blo 303832 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B2325995 : Blo 303832 2325995 := bstep (se 1 (by rfl) ⟨1744496, by rfl⟩ : syracuseStep 2325995 = 3488993) B3488993
theorem B31948739 : Blo 303832 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B2623853 : Blo 303832 2623853 := bstep (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) B983945
theorem B691559 : Blo 303832 691559 := bstep (se 1 (by rfl) ⟨518669, by rfl⟩ : syracuseStep 691559 = 1037339) B1037339
theorem B3478787 : Blo 303832 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B57386873 : Blo 303832 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B1550663 : Blo 303832 1550663 := bstep (se 1 (by rfl) ⟨1162997, by rfl⟩ : syracuseStep 1550663 = 2325995) B2325995
theorem B306047 : Blo 303832 306047 := bstep (se 1 (by rfl) ⟨229535, by rfl⟩ : syracuseStep 306047 = 459071) B459071
theorem B307047 : Blo 303832 307047 := bstep (se 1 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 307047 = 460571) B460571
theorem B5222555 : Blo 303832 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B19443887 : Blo 303832 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B9384623 : Blo 303832 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B769895 : Blo 303832 769895 := bstep (se 1 (by rfl) ⟨577421, by rfl⟩ : syracuseStep 769895 = 1154843) B1154843
theorem B1033883 : Blo 303832 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B870905 : Blo 303832 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B7820711 : Blo 303832 7820711 := bstep (se 1 (by rfl) ⟨5865533, by rfl⟩ : syracuseStep 7820711 = 11731067) B11731067
theorem B513695 : Blo 303832 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B292674181 : Blo 303832 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B776911 : Blo 303832 776911 := bstep (se 1 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 776911 = 1165367) B1165367
theorem B3464207 : Blo 303832 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B777833 : Blo 303832 777833 := bstep (se 2 (by rfl) ⟨291687, by rfl⟩ : syracuseStep 777833 = 583375) B583375
theorem B14049287 : Blo 303832 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B196043773 : Blo 303832 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B386299 : Blo 303832 386299 := bstep (se 1 (by rfl) ⟨289724, by rfl⟩ : syracuseStep 386299 = 579449) B579449
theorem B517583 : Blo 303832 517583 := bstep (se 1 (by rfl) ⟨388187, by rfl⟩ : syracuseStep 517583 = 776375) B776375
theorem B649471 : Blo 303832 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B3306977 : Blo 303832 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B685727 : Blo 303832 685727 := bstep (se 1 (by rfl) ⟨514295, by rfl⟩ : syracuseStep 685727 = 1028591) B1028591
theorem B3700889 : Blo 303832 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B686249 : Blo 303832 686249 := bstep (se 2 (by rfl) ⟨257343, by rfl⟩ : syracuseStep 686249 = 514687) B514687
theorem B8846279 : Blo 303832 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B21299159 : Blo 303832 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B689255 : Blo 303832 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B261391697 : Blo 303832 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B461039 : Blo 303832 461039 := bstep (se 1 (by rfl) ⟨345779, by rfl⟩ : syracuseStep 461039 = 691559) B691559
theorem B5213807 : Blo 303832 5213807 := bstep (se 1 (by rfl) ⟨3910355, by rfl⟩ : syracuseStep 5213807 = 7820711) B7820711
theorem B3481703 : Blo 303832 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B2204651 : Blo 303832 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B2467259 : Blo 303832 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B56797757 : Blo 303832 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B1749235 : Blo 303832 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B865961 : Blo 303832 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B342463 : Blo 303832 342463 := bstep (se 1 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 342463 = 513695) B513695
theorem B2309471 : Blo 303832 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B345055 : Blo 303832 345055 := bstep (se 1 (by rfl) ⟨258791, by rfl⟩ : syracuseStep 345055 = 517583) B517583
theorem B38257915 : Blo 303832 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B1033775 : Blo 303832 1033775 := bstep (se 1 (by rfl) ⟨775331, by rfl⟩ : syracuseStep 1033775 = 1550663) B1550663
theorem B12962591 : Blo 303832 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1035881 : Blo 303832 1035881 := bstep (se 2 (by rfl) ⟨388455, by rfl⟩ : syracuseStep 1035881 = 776911) B776911
theorem B513263 : Blo 303832 513263 := bstep (se 1 (by rfl) ⟨384947, by rfl⟩ : syracuseStep 513263 = 769895) B769895
theorem B515065 : Blo 303832 515065 := bstep (se 2 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 515065 = 386299) B386299
theorem B580603 : Blo 303832 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B2319191 : Blo 303832 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B518555 : Blo 303832 518555 := bstep (se 1 (by rfl) ⟨388916, by rfl⟩ : syracuseStep 518555 = 777833) B777833
theorem B9366191 : Blo 303832 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B6256415 : Blo 303832 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B390232241 : Blo 303832 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B457151 : Blo 303832 457151 := bstep (se 1 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 457151 = 685727) B685727
theorem B457499 : Blo 303832 457499 := bstep (se 1 (by rfl) ⟨343124, by rfl⟩ : syracuseStep 457499 = 686249) B686249
theorem B5897519 : Blo 303832 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B459503 : Blo 303832 459503 := bstep (se 1 (by rfl) ⟨344627, by rfl⟩ : syracuseStep 459503 = 689255) B689255
theorem B174261131 : Blo 303832 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B689183 : Blo 303832 689183 := bstep (se 1 (by rfl) ⟨516887, by rfl⟩ : syracuseStep 689183 = 1033775) B1033775
theorem B460073 : Blo 303832 460073 := bstep (se 2 (by rfl) ⟨172527, by rfl⟩ : syracuseStep 460073 = 345055) B345055
theorem B690587 : Blo 303832 690587 := bstep (se 1 (by rfl) ⟨517940, by rfl⟩ : syracuseStep 690587 = 1035881) B1035881
theorem B3475871 : Blo 303832 3475871 := bstep (se 1 (by rfl) ⟨2606903, by rfl⟩ : syracuseStep 3475871 = 5213807) B5213807
theorem B2332313 : Blo 303832 2332313 := bstep (se 2 (by rfl) ⟨874617, by rfl⟩ : syracuseStep 2332313 = 1749235) B1749235
theorem B1546127 : Blo 303832 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B1644839 : Blo 303832 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B4170943 : Blo 303832 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B260154827 : Blo 303832 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B304767 : Blo 303832 304767 := bstep (se 1 (by rfl) ⟨228575, by rfl⟩ : syracuseStep 304767 = 457151) B457151
theorem B304999 : Blo 303832 304999 := bstep (se 1 (by rfl) ⟨228749, by rfl⟩ : syracuseStep 304999 = 457499) B457499
theorem B307359 : Blo 303832 307359 := bstep (se 1 (by rfl) ⟨230519, by rfl⟩ : syracuseStep 307359 = 461039) B461039
theorem B342175 : Blo 303832 342175 := bstep (se 1 (by rfl) ⟨256631, by rfl⟩ : syracuseStep 342175 = 513263) B513263
theorem B345703 : Blo 303832 345703 := bstep (se 1 (by rfl) ⟨259277, by rfl⟩ : syracuseStep 345703 = 518555) B518555
theorem B37865171 : Blo 303832 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B6244127 : Blo 303832 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B577307 : Blo 303832 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B774137 : Blo 303832 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B51010553 : Blo 303832 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B8641727 : Blo 303832 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B2321135 : Blo 303832 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B1469767 : Blo 303832 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B456617 : Blo 303832 456617 := bstep (se 2 (by rfl) ⟨171231, by rfl⟩ : syracuseStep 456617 = 342463) B342463
theorem B686753 : Blo 303832 686753 := bstep (se 2 (by rfl) ⟨257532, by rfl⟩ : syracuseStep 686753 = 515065) B515065
theorem B3931679 : Blo 303832 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B1539647 : Blo 303832 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B459455 : Blo 303832 459455 := bstep (se 1 (by rfl) ⟨344591, by rfl⟩ : syracuseStep 459455 = 689183) B689183
theorem B4162751 : Blo 303832 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B460391 : Blo 303832 460391 := bstep (se 1 (by rfl) ⟨345293, by rfl⟩ : syracuseStep 460391 = 690587) B690587
theorem B460937 : Blo 303832 460937 := bstep (se 2 (by rfl) ⟨172851, by rfl⟩ : syracuseStep 460937 = 345703) B345703
theorem B1547423 : Blo 303832 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B304411 : Blo 303832 304411 := bstep (se 1 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 304411 = 456617) B456617
theorem B1026431 : Blo 303832 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B306335 : Blo 303832 306335 := bstep (se 1 (by rfl) ⟨229751, by rfl⟩ : syracuseStep 306335 = 459503) B459503
theorem B116174087 : Blo 303832 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B306715 : Blo 303832 306715 := bstep (se 1 (by rfl) ⟨230036, by rfl⟩ : syracuseStep 306715 = 460073) B460073
theorem B25243447 : Blo 303832 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B1554875 : Blo 303832 1554875 := bstep (se 1 (by rfl) ⟨1166156, by rfl⟩ : syracuseStep 1554875 = 2332313) B2332313
theorem B1030751 : Blo 303832 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B1096559 : Blo 303832 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B5561257 : Blo 303832 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B2317247 : Blo 303832 2317247 := bstep (se 1 (by rfl) ⟨1737935, by rfl⟩ : syracuseStep 2317247 = 3475871) B3475871
theorem B516091 : Blo 303832 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B1959689 : Blo 303832 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B34007035 : Blo 303832 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B5761151 : Blo 303832 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B173436551 : Blo 303832 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B456233 : Blo 303832 456233 := bstep (se 2 (by rfl) ⟨171087, by rfl⟩ : syracuseStep 456233 = 342175) B342175
theorem B457835 : Blo 303832 457835 := bstep (se 1 (by rfl) ⟨343376, by rfl⟩ : syracuseStep 457835 = 686753) B686753
theorem B1539485 : Blo 303832 1539485 := bstep (se 3 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 1539485 = 577307) B577307
theorem B2621119 : Blo 303832 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B1544831 : Blo 303832 1544831 := bstep (se 1 (by rfl) ⟨1158623, by rfl⟩ : syracuseStep 1544831 = 2317247) B2317247
theorem B33657929 : Blo 303832 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B3840767 : Blo 303832 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B304155 : Blo 303832 304155 := bstep (se 1 (by rfl) ⟨228116, by rfl⟩ : syracuseStep 304155 = 456233) B456233
theorem B7415009 : Blo 303832 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B731039 : Blo 303832 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B305223 : Blo 303832 305223 := bstep (se 1 (by rfl) ⟨228917, by rfl⟩ : syracuseStep 305223 = 457835) B457835
theorem B1026323 : Blo 303832 1026323 := bstep (se 1 (by rfl) ⟨769742, by rfl⟩ : syracuseStep 1026323 = 1539485) B1539485
theorem B306303 : Blo 303832 306303 := bstep (se 1 (by rfl) ⟨229727, by rfl⟩ : syracuseStep 306303 = 459455) B459455
theorem B306927 : Blo 303832 306927 := bstep (se 1 (by rfl) ⟨230195, by rfl⟩ : syracuseStep 306927 = 460391) B460391
theorem B307291 : Blo 303832 307291 := bstep (se 1 (by rfl) ⟨230468, by rfl⟩ : syracuseStep 307291 = 460937) B460937
theorem B1031615 : Blo 303832 1031615 := bstep (se 1 (by rfl) ⟨773711, by rfl⟩ : syracuseStep 1031615 = 1547423) B1547423
theorem B77449391 : Blo 303832 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B115624367 : Blo 303832 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B1036583 : Blo 303832 1036583 := bstep (se 1 (by rfl) ⟨777437, by rfl⟩ : syracuseStep 1036583 = 1554875) B1554875
theorem B3494825 : Blo 303832 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B688121 : Blo 303832 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B2775167 : Blo 303832 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B45342713 : Blo 303832 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B1306459 : Blo 303832 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B684287 : Blo 303832 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B687167 : Blo 303832 687167 := bstep (se 1 (by rfl) ⟨515375, by rfl⟩ : syracuseStep 687167 = 1030751) B1030751
theorem B691055 : Blo 303832 691055 := bstep (se 1 (by rfl) ⟨518291, by rfl⟩ : syracuseStep 691055 = 1036583) B1036583
theorem B2329883 : Blo 303832 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B2560511 : Blo 303832 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B1741945 : Blo 303832 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B77082911 : Blo 303832 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B1029887 : Blo 303832 1029887 := bstep (se 1 (by rfl) ⟨772415, by rfl⟩ : syracuseStep 1029887 = 1544831) B1544831
theorem B1850111 : Blo 303832 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B1949437 : Blo 303832 1949437 := bstep (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) B731039
theorem B30228475 : Blo 303832 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B51632927 : Blo 303832 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B22438619 : Blo 303832 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B4943339 : Blo 303832 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B684215 : Blo 303832 684215 := bstep (se 1 (by rfl) ⟨513161, by rfl⟩ : syracuseStep 684215 = 1026323) B1026323
theorem B456191 : Blo 303832 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B458111 : Blo 303832 458111 := bstep (se 1 (by rfl) ⟨343583, by rfl⟩ : syracuseStep 458111 = 687167) B687167
theorem B687743 : Blo 303832 687743 := bstep (se 1 (by rfl) ⟨515807, by rfl⟩ : syracuseStep 687743 = 1031615) B1031615
theorem B458747 : Blo 303832 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B460703 : Blo 303832 460703 := bstep (se 1 (by rfl) ⟨345527, by rfl⟩ : syracuseStep 460703 = 691055) B691055
theorem B1707007 : Blo 303832 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B51388607 : Blo 303832 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B304127 : Blo 303832 304127 := bstep (se 1 (by rfl) ⟨228095, by rfl⟩ : syracuseStep 304127 = 456191) B456191
theorem B305407 : Blo 303832 305407 := bstep (se 1 (by rfl) ⟨229055, by rfl⟩ : syracuseStep 305407 = 458111) B458111
theorem B2599249 : Blo 303832 2599249 := bstep (se 2 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 2599249 = 1949437) B1949437
theorem B305831 : Blo 303832 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B1553255 : Blo 303832 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B34421951 : Blo 303832 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B14959079 : Blo 303832 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B3295559 : Blo 303832 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B1233407 : Blo 303832 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B2322593 : Blo 303832 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B456143 : Blo 303832 456143 := bstep (se 1 (by rfl) ⟨342107, by rfl⟩ : syracuseStep 456143 = 684215) B684215
theorem B686591 : Blo 303832 686591 := bstep (se 1 (by rfl) ⟨514943, by rfl⟩ : syracuseStep 686591 = 1029887) B1029887
theorem B458495 : Blo 303832 458495 := bstep (se 1 (by rfl) ⟨343871, by rfl⟩ : syracuseStep 458495 = 687743) B687743
theorem B40304633 : Blo 303832 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B2197039 : Blo 303832 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B822271 : Blo 303832 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B1548395 : Blo 303832 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B304095 : Blo 303832 304095 := bstep (se 1 (by rfl) ⟨228071, by rfl⟩ : syracuseStep 304095 = 456143) B456143
theorem B22947967 : Blo 303832 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B305663 : Blo 303832 305663 := bstep (se 1 (by rfl) ⟨229247, by rfl⟩ : syracuseStep 305663 = 458495) B458495
theorem B9972719 : Blo 303832 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B307135 : Blo 303832 307135 := bstep (se 1 (by rfl) ⟨230351, by rfl⟩ : syracuseStep 307135 = 460703) B460703
theorem B2276009 : Blo 303832 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B34259071 : Blo 303832 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B1035503 : Blo 303832 1035503 := bstep (se 1 (by rfl) ⟨776627, by rfl⟩ : syracuseStep 1035503 = 1553255) B1553255
theorem B3465665 : Blo 303832 3465665 := bstep (se 2 (by rfl) ⟨1299624, by rfl⟩ : syracuseStep 3465665 = 2599249) B2599249
theorem B457727 : Blo 303832 457727 := bstep (se 1 (by rfl) ⟨343295, by rfl⟩ : syracuseStep 457727 = 686591) B686591
theorem B107479021 : Blo 303832 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B45678761 : Blo 303832 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B122389157 : Blo 303832 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B690335 : Blo 303832 690335 := bstep (se 1 (by rfl) ⟨517751, by rfl⟩ : syracuseStep 690335 = 1035503) B1035503
theorem B1517339 : Blo 303832 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B305151 : Blo 303832 305151 := bstep (se 1 (by rfl) ⟨228863, by rfl⟩ : syracuseStep 305151 = 457727) B457727
theorem B143305361 : Blo 303832 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B2929385 : Blo 303832 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B1096361 : Blo 303832 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B1032263 : Blo 303832 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B2310443 : Blo 303832 2310443 := bstep (se 1 (by rfl) ⟨1732832, by rfl⟩ : syracuseStep 2310443 = 3465665) B3465665
theorem B6648479 : Blo 303832 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B688175 : Blo 303832 688175 := bstep (se 1 (by rfl) ⟨516131, by rfl⟩ : syracuseStep 688175 = 1032263) B1032263
theorem B1540295 : Blo 303832 1540295 := bstep (se 1 (by rfl) ⟨1155221, by rfl⟩ : syracuseStep 1540295 = 2310443) B2310443
theorem B81592771 : Blo 303832 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B460223 : Blo 303832 460223 := bstep (se 1 (by rfl) ⟨345167, by rfl⟩ : syracuseStep 460223 = 690335) B690335
theorem B4432319 : Blo 303832 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B730907 : Blo 303832 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B30452507 : Blo 303832 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B95536907 : Blo 303832 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1952923 : Blo 303832 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B1011559 : Blo 303832 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B458783 : Blo 303832 458783 := bstep (se 1 (by rfl) ⟨344087, by rfl⟩ : syracuseStep 458783 = 688175) B688175
theorem B108790361 : Blo 303832 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B1348745 : Blo 303832 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B2954879 : Blo 303832 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B1026863 : Blo 303832 1026863 := bstep (se 1 (by rfl) ⟨770147, by rfl⟩ : syracuseStep 1026863 = 1540295) B1540295
theorem B306815 : Blo 303832 306815 := bstep (se 1 (by rfl) ⟨230111, by rfl⟩ : syracuseStep 306815 = 460223) B460223
theorem B2603897 : Blo 303832 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B20301671 : Blo 303832 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B63691271 : Blo 303832 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B487271 : Blo 303832 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B13534447 : Blo 303832 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B1969919 : Blo 303832 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B305855 : Blo 303832 305855 := bstep (se 1 (by rfl) ⟨229391, by rfl⟩ : syracuseStep 305855 = 458783) B458783
theorem B72526907 : Blo 303832 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B3596653 : Blo 303832 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B42460847 : Blo 303832 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B684575 : Blo 303832 684575 := bstep (se 1 (by rfl) ⟨513431, by rfl⟩ : syracuseStep 684575 = 1026863) B1026863
theorem B324847 : Blo 303832 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B1735931 : Blo 303832 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B1313279 : Blo 303832 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B433129 : Blo 303832 433129 := bstep (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) B324847
theorem B1157287 : Blo 303832 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B4795537 : Blo 303832 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B48351271 : Blo 303832 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B18045929 : Blo 303832 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B28307231 : Blo 303832 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B456383 : Blo 303832 456383 := bstep (se 1 (by rfl) ⟨342287, by rfl⟩ : syracuseStep 456383 = 684575) B684575
theorem B1543049 : Blo 303832 1543049 := bstep (se 2 (by rfl) ⟨578643, by rfl⟩ : syracuseStep 1543049 = 1157287) B1157287
theorem B6394049 : Blo 303832 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B12030619 : Blo 303832 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B304255 : Blo 303832 304255 := bstep (se 1 (by rfl) ⟨228191, by rfl⟩ : syracuseStep 304255 = 456383) B456383
theorem B64468361 : Blo 303832 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B577505 : Blo 303832 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B875519 : Blo 303832 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B18871487 : Blo 303832 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B4262699 : Blo 303832 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B1028699 : Blo 303832 1028699 := bstep (se 1 (by rfl) ⟨771524, by rfl⟩ : syracuseStep 1028699 = 1543049) B1543049
theorem B16040825 : Blo 303832 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B42978907 : Blo 303832 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B385003 : Blo 303832 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B583679 : Blo 303832 583679 := bstep (se 1 (by rfl) ⟨437759, by rfl⟩ : syracuseStep 583679 = 875519) B875519
theorem B12580991 : Blo 303832 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B229220837 : Blo 303832 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B10693883 : Blo 303832 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B513337 : Blo 303832 513337 := bstep (se 2 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 513337 = 385003) B385003
theorem B2841799 : Blo 303832 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B389119 : Blo 303832 389119 := bstep (se 1 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 389119 = 583679) B583679
theorem B685799 : Blo 303832 685799 := bstep (se 1 (by rfl) ⟨514349, by rfl⟩ : syracuseStep 685799 = 1028699) B1028699
theorem B8387327 : Blo 303832 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B152813891 : Blo 303832 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B7129255 : Blo 303832 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B3789065 : Blo 303832 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B5591551 : Blo 303832 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B518825 : Blo 303832 518825 := bstep (se 2 (by rfl) ⟨194559, by rfl⟩ : syracuseStep 518825 = 389119) B389119
theorem B684449 : Blo 303832 684449 := bstep (se 2 (by rfl) ⟨256668, by rfl⟩ : syracuseStep 684449 = 513337) B513337
theorem B457199 : Blo 303832 457199 := bstep (se 1 (by rfl) ⟨342899, by rfl⟩ : syracuseStep 457199 = 685799) B685799
theorem B101875927 : Blo 303832 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B9505673 : Blo 303832 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B304799 : Blo 303832 304799 := bstep (se 1 (by rfl) ⟨228599, by rfl⟩ : syracuseStep 304799 = 457199) B457199
theorem B10104173 : Blo 303832 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B7455401 : Blo 303832 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B345883 : Blo 303832 345883 := bstep (se 1 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 345883 = 518825) B518825
theorem B456299 : Blo 303832 456299 := bstep (se 1 (by rfl) ⟨342224, by rfl⟩ : syracuseStep 456299 = 684449) B684449
theorem B461177 : Blo 303832 461177 := bstep (se 2 (by rfl) ⟨172941, by rfl⟩ : syracuseStep 461177 = 345883) B345883
theorem B304199 : Blo 303832 304199 := bstep (se 1 (by rfl) ⟨228149, by rfl⟩ : syracuseStep 304199 = 456299) B456299
theorem B135834569 : Blo 303832 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B6337115 : Blo 303832 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B6736115 : Blo 303832 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B4970267 : Blo 303832 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B4490743 : Blo 303832 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B3313511 : Blo 303832 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B307451 : Blo 303832 307451 := bstep (se 1 (by rfl) ⟨230588, by rfl⟩ : syracuseStep 307451 = 461177) B461177
theorem B90556379 : Blo 303832 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B4224743 : Blo 303832 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B60370919 : Blo 303832 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B2209007 : Blo 303832 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B5987657 : Blo 303832 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B2816495 : Blo 303832 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B40247279 : Blo 303832 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B1877663 : Blo 303832 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B3991771 : Blo 303832 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B1472671 : Blo 303832 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B1251775 : Blo 303832 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B5322361 : Blo 303832 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B26831519 : Blo 303832 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1963561 : Blo 303832 1963561 := bstep (se 2 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 1963561 = 1472671) B1472671
theorem B7096481 : Blo 303832 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B17887679 : Blo 303832 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B2618081 : Blo 303832 2618081 := bstep (se 2 (by rfl) ⟨981780, by rfl⟩ : syracuseStep 2618081 = 1963561) B1963561
theorem B1669033 : Blo 303832 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B1745387 : Blo 303832 1745387 := bstep (se 1 (by rfl) ⟨1309040, by rfl⟩ : syracuseStep 1745387 = 2618081) B2618081
theorem B4730987 : Blo 303832 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B2225377 : Blo 303832 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B11925119 : Blo 303832 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B11868677 : Blo 303832 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B3153991 : Blo 303832 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B1163591 : Blo 303832 1163591 := bstep (se 1 (by rfl) ⟨872693, by rfl⟩ : syracuseStep 1163591 = 1745387) B1745387
theorem B7950079 : Blo 303832 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B4205321 : Blo 303832 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B7912451 : Blo 303832 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B10600105 : Blo 303832 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B775727 : Blo 303832 775727 := bstep (se 1 (by rfl) ⟨581795, by rfl⟩ : syracuseStep 775727 = 1163591) B1163591
theorem B14133473 : Blo 303832 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B2803547 : Blo 303832 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B517151 : Blo 303832 517151 := bstep (se 1 (by rfl) ⟨387863, by rfl⟩ : syracuseStep 517151 = 775727) B775727
theorem B21099869 : Blo 303832 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B1869031 : Blo 303832 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B14066579 : Blo 303832 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B344767 : Blo 303832 344767 := bstep (se 1 (by rfl) ⟨258575, by rfl⟩ : syracuseStep 344767 = 517151) B517151
theorem B9422315 : Blo 303832 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B459689 : Blo 303832 459689 := bstep (se 2 (by rfl) ⟨172383, by rfl⟩ : syracuseStep 459689 = 344767) B344767
theorem B2492041 : Blo 303832 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B6281543 : Blo 303832 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B37510877 : Blo 303832 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B306459 : Blo 303832 306459 := bstep (se 1 (by rfl) ⟨229844, by rfl⟩ : syracuseStep 306459 = 459689) B459689
theorem B3322721 : Blo 303832 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B100029005 : Blo 303832 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B4187695 : Blo 303832 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B66686003 : Blo 303832 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B5583593 : Blo 303832 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B2215147 : Blo 303832 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B2953529 : Blo 303832 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B3722395 : Blo 303832 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B44457335 : Blo 303832 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B1969019 : Blo 303832 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B4963193 : Blo 303832 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B29638223 : Blo 303832 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B1312679 : Blo 303832 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B3308795 : Blo 303832 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B19758815 : Blo 303832 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B2205863 : Blo 303832 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B875119 : Blo 303832 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B13172543 : Blo 303832 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B1166825 : Blo 303832 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B1470575 : Blo 303832 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B8781695 : Blo 303832 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5854463 : Blo 303832 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B3921533 : Blo 303832 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B777883 : Blo 303832 777883 := bstep (se 1 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 777883 = 1166825) B1166825
theorem B3902975 : Blo 303832 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B1037177 : Blo 303832 1037177 := bstep (se 2 (by rfl) ⟨388941, by rfl⟩ : syracuseStep 1037177 = 777883) B777883
theorem B2614355 : Blo 303832 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B691451 : Blo 303832 691451 := bstep (se 1 (by rfl) ⟨518588, by rfl⟩ : syracuseStep 691451 = 1037177) B1037177
theorem B1742903 : Blo 303832 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B2601983 : Blo 303832 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B460967 : Blo 303832 460967 := bstep (se 1 (by rfl) ⟨345725, by rfl⟩ : syracuseStep 460967 = 691451) B691451
theorem B1161935 : Blo 303832 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B1734655 : Blo 303832 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B307311 : Blo 303832 307311 := bstep (se 1 (by rfl) ⟨230483, by rfl⟩ : syracuseStep 307311 = 460967) B460967
theorem B2312873 : Blo 303832 2312873 := bstep (se 2 (by rfl) ⟨867327, by rfl⟩ : syracuseStep 2312873 = 1734655) B1734655
theorem B774623 : Blo 303832 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B1541915 : Blo 303832 1541915 := bstep (se 1 (by rfl) ⟨1156436, by rfl⟩ : syracuseStep 1541915 = 2312873) B2312873
theorem B516415 : Blo 303832 516415 := bstep (se 1 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 516415 = 774623) B774623
theorem B688553 : Blo 303832 688553 := bstep (se 2 (by rfl) ⟨258207, by rfl⟩ : syracuseStep 688553 = 516415) B516415
theorem B1027943 : Blo 303832 1027943 := bstep (se 1 (by rfl) ⟨770957, by rfl⟩ : syracuseStep 1027943 = 1541915) B1541915
theorem B459035 : Blo 303832 459035 := bstep (se 1 (by rfl) ⟨344276, by rfl⟩ : syracuseStep 459035 = 688553) B688553
theorem B685295 : Blo 303832 685295 := bstep (se 1 (by rfl) ⟨513971, by rfl⟩ : syracuseStep 685295 = 1027943) B1027943
theorem B306023 : Blo 303832 306023 := bstep (se 1 (by rfl) ⟨229517, by rfl⟩ : syracuseStep 306023 = 459035) B459035
theorem B456863 : Blo 303832 456863 := bstep (se 1 (by rfl) ⟨342647, by rfl⟩ : syracuseStep 456863 = 685295) B685295
theorem B304575 : Blo 303832 304575 := bstep (se 1 (by rfl) ⟨228431, by rfl⟩ : syracuseStep 304575 = 456863) B456863

theorem C0 (j : ℕ) (h1 : 75958 ≤ j) (h2 : j ≤ 76657) : Blo 303832 (4 * j + 3) := by
  interval_cases j
  · exact B303835
  · exact B303839
  · exact B303843
  · exact B303847
  · exact B303851
  · exact B303855
  · exact B303859
  · exact B303863
  · exact B303867
  · exact B303871
  · exact B303875
  · exact B303879
  · exact B303883
  · exact B303887
  · exact B303891
  · exact B303895
  · exact B303899
  · exact B303903
  · exact B303907
  · exact B303911
  · exact B303915
  · exact B303919
  · exact B303923
  · exact B303927
  · exact B303931
  · exact B303935
  · exact B303939
  · exact B303943
  · exact B303947
  · exact B303951
  · exact B303955
  · exact B303959
  · exact B303963
  · exact B303967
  · exact B303971
  · exact B303975
  · exact B303979
  · exact B303983
  · exact B303987
  · exact B303991
  · exact B303995
  · exact B303999
  · exact B304003
  · exact B304007
  · exact B304011
  · exact B304015
  · exact B304019
  · exact B304023
  · exact B304027
  · exact B304031
  · exact B304035
  · exact B304039
  · exact B304043
  · exact B304047
  · exact B304051
  · exact B304055
  · exact B304059
  · exact B304063
  · exact B304067
  · exact B304071
  · exact B304075
  · exact B304079
  · exact B304083
  · exact B304087
  · exact B304091
  · exact B304095
  · exact B304099
  · exact B304103
  · exact B304107
  · exact B304111
  · exact B304115
  · exact B304119
  · exact B304123
  · exact B304127
  · exact B304131
  · exact B304135
  · exact B304139
  · exact B304143
  · exact B304147
  · exact B304151
  · exact B304155
  · exact B304159
  · exact B304163
  · exact B304167
  · exact B304171
  · exact B304175
  · exact B304179
  · exact B304183
  · exact B304187
  · exact B304191
  · exact B304195
  · exact B304199
  · exact B304203
  · exact B304207
  · exact B304211
  · exact B304215
  · exact B304219
  · exact B304223
  · exact B304227
  · exact B304231
  · exact B304235
  · exact B304239
  · exact B304243
  · exact B304247
  · exact B304251
  · exact B304255
  · exact B304259
  · exact B304263
  · exact B304267
  · exact B304271
  · exact B304275
  · exact B304279
  · exact B304283
  · exact B304287
  · exact B304291
  · exact B304295
  · exact B304299
  · exact B304303
  · exact B304307
  · exact B304311
  · exact B304315
  · exact B304319
  · exact B304323
  · exact B304327
  · exact B304331
  · exact B304335
  · exact B304339
  · exact B304343
  · exact B304347
  · exact B304351
  · exact B304355
  · exact B304359
  · exact B304363
  · exact B304367
  · exact B304371
  · exact B304375
  · exact B304379
  · exact B304383
  · exact B304387
  · exact B304391
  · exact B304395
  · exact B304399
  · exact B304403
  · exact B304407
  · exact B304411
  · exact B304415
  · exact B304419
  · exact B304423
  · exact B304427
  · exact B304431
  · exact B304435
  · exact B304439
  · exact B304443
  · exact B304447
  · exact B304451
  · exact B304455
  · exact B304459
  · exact B304463
  · exact B304467
  · exact B304471
  · exact B304475
  · exact B304479
  · exact B304483
  · exact B304487
  · exact B304491
  · exact B304495
  · exact B304499
  · exact B304503
  · exact B304507
  · exact B304511
  · exact B304515
  · exact B304519
  · exact B304523
  · exact B304527
  · exact B304531
  · exact B304535
  · exact B304539
  · exact B304543
  · exact B304547
  · exact B304551
  · exact B304555
  · exact B304559
  · exact B304563
  · exact B304567
  · exact B304571
  · exact B304575
  · exact B304579
  · exact B304583
  · exact B304587
  · exact B304591
  · exact B304595
  · exact B304599
  · exact B304603
  · exact B304607
  · exact B304611
  · exact B304615
  · exact B304619
  · exact B304623
  · exact B304627
  · exact B304631
  · exact B304635
  · exact B304639
  · exact B304643
  · exact B304647
  · exact B304651
  · exact B304655
  · exact B304659
  · exact B304663
  · exact B304667
  · exact B304671
  · exact B304675
  · exact B304679
  · exact B304683
  · exact B304687
  · exact B304691
  · exact B304695
  · exact B304699
  · exact B304703
  · exact B304707
  · exact B304711
  · exact B304715
  · exact B304719
  · exact B304723
  · exact B304727
  · exact B304731
  · exact B304735
  · exact B304739
  · exact B304743
  · exact B304747
  · exact B304751
  · exact B304755
  · exact B304759
  · exact B304763
  · exact B304767
  · exact B304771
  · exact B304775
  · exact B304779
  · exact B304783
  · exact B304787
  · exact B304791
  · exact B304795
  · exact B304799
  · exact B304803
  · exact B304807
  · exact B304811
  · exact B304815
  · exact B304819
  · exact B304823
  · exact B304827
  · exact B304831
  · exact B304835
  · exact B304839
  · exact B304843
  · exact B304847
  · exact B304851
  · exact B304855
  · exact B304859
  · exact B304863
  · exact B304867
  · exact B304871
  · exact B304875
  · exact B304879
  · exact B304883
  · exact B304887
  · exact B304891
  · exact B304895
  · exact B304899
  · exact B304903
  · exact B304907
  · exact B304911
  · exact B304915
  · exact B304919
  · exact B304923
  · exact B304927
  · exact B304931
  · exact B304935
  · exact B304939
  · exact B304943
  · exact B304947
  · exact B304951
  · exact B304955
  · exact B304959
  · exact B304963
  · exact B304967
  · exact B304971
  · exact B304975
  · exact B304979
  · exact B304983
  · exact B304987
  · exact B304991
  · exact B304995
  · exact B304999
  · exact B305003
  · exact B305007
  · exact B305011
  · exact B305015
  · exact B305019
  · exact B305023
  · exact B305027
  · exact B305031
  · exact B305035
  · exact B305039
  · exact B305043
  · exact B305047
  · exact B305051
  · exact B305055
  · exact B305059
  · exact B305063
  · exact B305067
  · exact B305071
  · exact B305075
  · exact B305079
  · exact B305083
  · exact B305087
  · exact B305091
  · exact B305095
  · exact B305099
  · exact B305103
  · exact B305107
  · exact B305111
  · exact B305115
  · exact B305119
  · exact B305123
  · exact B305127
  · exact B305131
  · exact B305135
  · exact B305139
  · exact B305143
  · exact B305147
  · exact B305151
  · exact B305155
  · exact B305159
  · exact B305163
  · exact B305167
  · exact B305171
  · exact B305175
  · exact B305179
  · exact B305183
  · exact B305187
  · exact B305191
  · exact B305195
  · exact B305199
  · exact B305203
  · exact B305207
  · exact B305211
  · exact B305215
  · exact B305219
  · exact B305223
  · exact B305227
  · exact B305231
  · exact B305235
  · exact B305239
  · exact B305243
  · exact B305247
  · exact B305251
  · exact B305255
  · exact B305259
  · exact B305263
  · exact B305267
  · exact B305271
  · exact B305275
  · exact B305279
  · exact B305283
  · exact B305287
  · exact B305291
  · exact B305295
  · exact B305299
  · exact B305303
  · exact B305307
  · exact B305311
  · exact B305315
  · exact B305319
  · exact B305323
  · exact B305327
  · exact B305331
  · exact B305335
  · exact B305339
  · exact B305343
  · exact B305347
  · exact B305351
  · exact B305355
  · exact B305359
  · exact B305363
  · exact B305367
  · exact B305371
  · exact B305375
  · exact B305379
  · exact B305383
  · exact B305387
  · exact B305391
  · exact B305395
  · exact B305399
  · exact B305403
  · exact B305407
  · exact B305411
  · exact B305415
  · exact B305419
  · exact B305423
  · exact B305427
  · exact B305431
  · exact B305435
  · exact B305439
  · exact B305443
  · exact B305447
  · exact B305451
  · exact B305455
  · exact B305459
  · exact B305463
  · exact B305467
  · exact B305471
  · exact B305475
  · exact B305479
  · exact B305483
  · exact B305487
  · exact B305491
  · exact B305495
  · exact B305499
  · exact B305503
  · exact B305507
  · exact B305511
  · exact B305515
  · exact B305519
  · exact B305523
  · exact B305527
  · exact B305531
  · exact B305535
  · exact B305539
  · exact B305543
  · exact B305547
  · exact B305551
  · exact B305555
  · exact B305559
  · exact B305563
  · exact B305567
  · exact B305571
  · exact B305575
  · exact B305579
  · exact B305583
  · exact B305587
  · exact B305591
  · exact B305595
  · exact B305599
  · exact B305603
  · exact B305607
  · exact B305611
  · exact B305615
  · exact B305619
  · exact B305623
  · exact B305627
  · exact B305631
  · exact B305635
  · exact B305639
  · exact B305643
  · exact B305647
  · exact B305651
  · exact B305655
  · exact B305659
  · exact B305663
  · exact B305667
  · exact B305671
  · exact B305675
  · exact B305679
  · exact B305683
  · exact B305687
  · exact B305691
  · exact B305695
  · exact B305699
  · exact B305703
  · exact B305707
  · exact B305711
  · exact B305715
  · exact B305719
  · exact B305723
  · exact B305727
  · exact B305731
  · exact B305735
  · exact B305739
  · exact B305743
  · exact B305747
  · exact B305751
  · exact B305755
  · exact B305759
  · exact B305763
  · exact B305767
  · exact B305771
  · exact B305775
  · exact B305779
  · exact B305783
  · exact B305787
  · exact B305791
  · exact B305795
  · exact B305799
  · exact B305803
  · exact B305807
  · exact B305811
  · exact B305815
  · exact B305819
  · exact B305823
  · exact B305827
  · exact B305831
  · exact B305835
  · exact B305839
  · exact B305843
  · exact B305847
  · exact B305851
  · exact B305855
  · exact B305859
  · exact B305863
  · exact B305867
  · exact B305871
  · exact B305875
  · exact B305879
  · exact B305883
  · exact B305887
  · exact B305891
  · exact B305895
  · exact B305899
  · exact B305903
  · exact B305907
  · exact B305911
  · exact B305915
  · exact B305919
  · exact B305923
  · exact B305927
  · exact B305931
  · exact B305935
  · exact B305939
  · exact B305943
  · exact B305947
  · exact B305951
  · exact B305955
  · exact B305959
  · exact B305963
  · exact B305967
  · exact B305971
  · exact B305975
  · exact B305979
  · exact B305983
  · exact B305987
  · exact B305991
  · exact B305995
  · exact B305999
  · exact B306003
  · exact B306007
  · exact B306011
  · exact B306015
  · exact B306019
  · exact B306023
  · exact B306027
  · exact B306031
  · exact B306035
  · exact B306039
  · exact B306043
  · exact B306047
  · exact B306051
  · exact B306055
  · exact B306059
  · exact B306063
  · exact B306067
  · exact B306071
  · exact B306075
  · exact B306079
  · exact B306083
  · exact B306087
  · exact B306091
  · exact B306095
  · exact B306099
  · exact B306103
  · exact B306107
  · exact B306111
  · exact B306115
  · exact B306119
  · exact B306123
  · exact B306127
  · exact B306131
  · exact B306135
  · exact B306139
  · exact B306143
  · exact B306147
  · exact B306151
  · exact B306155
  · exact B306159
  · exact B306163
  · exact B306167
  · exact B306171
  · exact B306175
  · exact B306179
  · exact B306183
  · exact B306187
  · exact B306191
  · exact B306195
  · exact B306199
  · exact B306203
  · exact B306207
  · exact B306211
  · exact B306215
  · exact B306219
  · exact B306223
  · exact B306227
  · exact B306231
  · exact B306235
  · exact B306239
  · exact B306243
  · exact B306247
  · exact B306251
  · exact B306255
  · exact B306259
  · exact B306263
  · exact B306267
  · exact B306271
  · exact B306275
  · exact B306279
  · exact B306283
  · exact B306287
  · exact B306291
  · exact B306295
  · exact B306299
  · exact B306303
  · exact B306307
  · exact B306311
  · exact B306315
  · exact B306319
  · exact B306323
  · exact B306327
  · exact B306331
  · exact B306335
  · exact B306339
  · exact B306343
  · exact B306347
  · exact B306351
  · exact B306355
  · exact B306359
  · exact B306363
  · exact B306367
  · exact B306371
  · exact B306375
  · exact B306379
  · exact B306383
  · exact B306387
  · exact B306391
  · exact B306395
  · exact B306399
  · exact B306403
  · exact B306407
  · exact B306411
  · exact B306415
  · exact B306419
  · exact B306423
  · exact B306427
  · exact B306431
  · exact B306435
  · exact B306439
  · exact B306443
  · exact B306447
  · exact B306451
  · exact B306455
  · exact B306459
  · exact B306463
  · exact B306467
  · exact B306471
  · exact B306475
  · exact B306479
  · exact B306483
  · exact B306487
  · exact B306491
  · exact B306495
  · exact B306499
  · exact B306503
  · exact B306507
  · exact B306511
  · exact B306515
  · exact B306519
  · exact B306523
  · exact B306527
  · exact B306531
  · exact B306535
  · exact B306539
  · exact B306543
  · exact B306547
  · exact B306551
  · exact B306555
  · exact B306559
  · exact B306563
  · exact B306567
  · exact B306571
  · exact B306575
  · exact B306579
  · exact B306583
  · exact B306587
  · exact B306591
  · exact B306595
  · exact B306599
  · exact B306603
  · exact B306607
  · exact B306611
  · exact B306615
  · exact B306619
  · exact B306623
  · exact B306627
  · exact B306631

theorem C1 (j : ℕ) (h1 : 76658 ≤ j) (h2 : j ≤ 76957) : Blo 303832 (4 * j + 3) := by
  interval_cases j
  · exact B306635
  · exact B306639
  · exact B306643
  · exact B306647
  · exact B306651
  · exact B306655
  · exact B306659
  · exact B306663
  · exact B306667
  · exact B306671
  · exact B306675
  · exact B306679
  · exact B306683
  · exact B306687
  · exact B306691
  · exact B306695
  · exact B306699
  · exact B306703
  · exact B306707
  · exact B306711
  · exact B306715
  · exact B306719
  · exact B306723
  · exact B306727
  · exact B306731
  · exact B306735
  · exact B306739
  · exact B306743
  · exact B306747
  · exact B306751
  · exact B306755
  · exact B306759
  · exact B306763
  · exact B306767
  · exact B306771
  · exact B306775
  · exact B306779
  · exact B306783
  · exact B306787
  · exact B306791
  · exact B306795
  · exact B306799
  · exact B306803
  · exact B306807
  · exact B306811
  · exact B306815
  · exact B306819
  · exact B306823
  · exact B306827
  · exact B306831
  · exact B306835
  · exact B306839
  · exact B306843
  · exact B306847
  · exact B306851
  · exact B306855
  · exact B306859
  · exact B306863
  · exact B306867
  · exact B306871
  · exact B306875
  · exact B306879
  · exact B306883
  · exact B306887
  · exact B306891
  · exact B306895
  · exact B306899
  · exact B306903
  · exact B306907
  · exact B306911
  · exact B306915
  · exact B306919
  · exact B306923
  · exact B306927
  · exact B306931
  · exact B306935
  · exact B306939
  · exact B306943
  · exact B306947
  · exact B306951
  · exact B306955
  · exact B306959
  · exact B306963
  · exact B306967
  · exact B306971
  · exact B306975
  · exact B306979
  · exact B306983
  · exact B306987
  · exact B306991
  · exact B306995
  · exact B306999
  · exact B307003
  · exact B307007
  · exact B307011
  · exact B307015
  · exact B307019
  · exact B307023
  · exact B307027
  · exact B307031
  · exact B307035
  · exact B307039
  · exact B307043
  · exact B307047
  · exact B307051
  · exact B307055
  · exact B307059
  · exact B307063
  · exact B307067
  · exact B307071
  · exact B307075
  · exact B307079
  · exact B307083
  · exact B307087
  · exact B307091
  · exact B307095
  · exact B307099
  · exact B307103
  · exact B307107
  · exact B307111
  · exact B307115
  · exact B307119
  · exact B307123
  · exact B307127
  · exact B307131
  · exact B307135
  · exact B307139
  · exact B307143
  · exact B307147
  · exact B307151
  · exact B307155
  · exact B307159
  · exact B307163
  · exact B307167
  · exact B307171
  · exact B307175
  · exact B307179
  · exact B307183
  · exact B307187
  · exact B307191
  · exact B307195
  · exact B307199
  · exact B307203
  · exact B307207
  · exact B307211
  · exact B307215
  · exact B307219
  · exact B307223
  · exact B307227
  · exact B307231
  · exact B307235
  · exact B307239
  · exact B307243
  · exact B307247
  · exact B307251
  · exact B307255
  · exact B307259
  · exact B307263
  · exact B307267
  · exact B307271
  · exact B307275
  · exact B307279
  · exact B307283
  · exact B307287
  · exact B307291
  · exact B307295
  · exact B307299
  · exact B307303
  · exact B307307
  · exact B307311
  · exact B307315
  · exact B307319
  · exact B307323
  · exact B307327
  · exact B307331
  · exact B307335
  · exact B307339
  · exact B307343
  · exact B307347
  · exact B307351
  · exact B307355
  · exact B307359
  · exact B307363
  · exact B307367
  · exact B307371
  · exact B307375
  · exact B307379
  · exact B307383
  · exact B307387
  · exact B307391
  · exact B307395
  · exact B307399
  · exact B307403
  · exact B307407
  · exact B307411
  · exact B307415
  · exact B307419
  · exact B307423
  · exact B307427
  · exact B307431
  · exact B307435
  · exact B307439
  · exact B307443
  · exact B307447
  · exact B307451
  · exact B307455
  · exact B307459
  · exact B307463
  · exact B307467
  · exact B307471
  · exact B307475
  · exact B307479
  · exact B307483
  · exact B307487
  · exact B307491
  · exact B307495
  · exact B307499
  · exact B307503
  · exact B307507
  · exact B307511
  · exact B307515
  · exact B307519
  · exact B307523
  · exact B307527
  · exact B307531
  · exact B307535
  · exact B307539
  · exact B307543
  · exact B307547
  · exact B307551
  · exact B307555
  · exact B307559
  · exact B307563
  · exact B307567
  · exact B307571
  · exact B307575
  · exact B307579
  · exact B307583
  · exact B307587
  · exact B307591
  · exact B307595
  · exact B307599
  · exact B307603
  · exact B307607
  · exact B307611
  · exact B307615
  · exact B307619
  · exact B307623
  · exact B307627
  · exact B307631
  · exact B307635
  · exact B307639
  · exact B307643
  · exact B307647
  · exact B307651
  · exact B307655
  · exact B307659
  · exact B307663
  · exact B307667
  · exact B307671
  · exact B307675
  · exact B307679
  · exact B307683
  · exact B307687
  · exact B307691
  · exact B307695
  · exact B307699
  · exact B307703
  · exact B307707
  · exact B307711
  · exact B307715
  · exact B307719
  · exact B307723
  · exact B307727
  · exact B307731
  · exact B307735
  · exact B307739
  · exact B307743
  · exact B307747
  · exact B307751
  · exact B307755
  · exact B307759
  · exact B307763
  · exact B307767
  · exact B307771
  · exact B307775
  · exact B307779
  · exact B307783
  · exact B307787
  · exact B307791
  · exact B307795
  · exact B307799
  · exact B307803
  · exact B307807
  · exact B307811
  · exact B307815
  · exact B307819
  · exact B307823
  · exact B307827
  · exact B307831

theorem solution (m : ℕ) (hlo : 303832 ≤ m) (hhi : m ≤ 307832) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 75958 ≤ j := by omega
    have hj2 : j ≤ 76957 := by omega
    have hb : Blo 303832 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 76658 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
