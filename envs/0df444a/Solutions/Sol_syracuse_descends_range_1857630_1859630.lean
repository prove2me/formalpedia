-- Prove2me | solution 1 for syracuse_descends_range_1857630_1859630
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:09:21.49089+00:00
-- url     : https://prove2.me/submissions/97dbddc8-298a-41e1-aadf-86e0269dac69

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


theorem B2646037 : Blo 1857630 2646037 := bbase (se 6 (by rfl) ⟨62016, by rfl⟩ : syracuseStep 2646037 = 124033) (by norm_num)
theorem B101761109 : Blo 1857630 101761109 := bbase (se 8 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 101761109 = 1192513) (by norm_num)
theorem B2351197 : Blo 1857630 2351197 := bbase (se 3 (by rfl) ⟨440849, by rfl⟩ : syracuseStep 2351197 = 881699) (by norm_num)
theorem B3137629 : Blo 1857630 3137629 := bbase (se 3 (by rfl) ⟨588305, by rfl⟩ : syracuseStep 3137629 = 1176611) (by norm_num)
theorem B4702333 : Blo 1857630 4702333 := bbase (se 3 (by rfl) ⟨881687, by rfl⟩ : syracuseStep 4702333 = 1763375) (by norm_num)
theorem B2384005 : Blo 1857630 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B3178645 : Blo 1857630 3178645 := bbase (se 6 (by rfl) ⟨74499, by rfl⟩ : syracuseStep 3178645 = 148999) (by norm_num)
theorem B2384041 : Blo 1857630 2384041 := bbase (se 2 (by rfl) ⟨894015, by rfl⟩ : syracuseStep 2384041 = 1788031) (by norm_num)
theorem B3137717 : Blo 1857630 3137717 := bbase (se 5 (by rfl) ⟨147080, by rfl⟩ : syracuseStep 3137717 = 294161) (by norm_num)
theorem B25428181 : Blo 1857630 25428181 := bbase (se 7 (by rfl) ⟨297986, by rfl⟩ : syracuseStep 25428181 = 595973) (by norm_num)
theorem B6275285 : Blo 1857630 6275285 := bbase (se 7 (by rfl) ⟨73538, by rfl⟩ : syracuseStep 6275285 = 147077) (by norm_num)
theorem B4702445 : Blo 1857630 4702445 := bbase (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) (by norm_num)
theorem B2351369 : Blo 1857630 2351369 := bbase (se 2 (by rfl) ⟨881763, by rfl⟩ : syracuseStep 2351369 = 1763527) (by norm_num)
theorem B1884469 : Blo 1857630 1884469 := bbase (se 5 (by rfl) ⟨88334, by rfl⟩ : syracuseStep 1884469 = 176669) (by norm_num)
theorem B3137845 : Blo 1857630 3137845 := bbase (se 5 (by rfl) ⟨147086, by rfl⟩ : syracuseStep 3137845 = 294173) (by norm_num)
theorem B2351425 : Blo 1857630 2351425 := bbase (se 2 (by rfl) ⟨881784, by rfl⟩ : syracuseStep 2351425 = 1763569) (by norm_num)
theorem B6037829 : Blo 1857630 6037829 := bbase (se 4 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 6037829 = 1132093) (by norm_num)
theorem B23814485 : Blo 1857630 23814485 := bbase (se 10 (by rfl) ⟨34884, by rfl⟩ : syracuseStep 23814485 = 69769) (by norm_num)
theorem B2646373 : Blo 1857630 2646373 := bbase (se 4 (by rfl) ⟨248097, by rfl⟩ : syracuseStep 2646373 = 496195) (by norm_num)
theorem B3137933 : Blo 1857630 3137933 := bbase (se 3 (by rfl) ⟨588362, by rfl⟩ : syracuseStep 3137933 = 1176725) (by norm_num)
theorem B2351521 : Blo 1857630 2351521 := bbase (se 2 (by rfl) ⟨881820, by rfl⟩ : syracuseStep 2351521 = 1763641) (by norm_num)
theorem B4702637 : Blo 1857630 4702637 := bbase (se 3 (by rfl) ⟨881744, by rfl⟩ : syracuseStep 4702637 = 1763489) (by norm_num)
theorem B10584533 : Blo 1857630 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B3138061 : Blo 1857630 3138061 := bbase (se 3 (by rfl) ⟨588386, by rfl⟩ : syracuseStep 3138061 = 1176773) (by norm_num)
theorem B2646589 : Blo 1857630 2646589 := bbase (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) (by norm_num)
theorem B2351693 : Blo 1857630 2351693 := bbase (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) (by norm_num)
theorem B7053925 : Blo 1857630 7053925 := bbase (se 4 (by rfl) ⟨661305, by rfl⟩ : syracuseStep 7053925 = 1322611) (by norm_num)
theorem B2384497 : Blo 1857630 2384497 := bbase (se 2 (by rfl) ⟨894186, by rfl⟩ : syracuseStep 2384497 = 1788373) (by norm_num)
theorem B2351749 : Blo 1857630 2351749 := bbase (se 4 (by rfl) ⟨220476, by rfl⟩ : syracuseStep 2351749 = 440953) (by norm_num)
theorem B5292677 : Blo 1857630 5292677 := bbase (se 4 (by rfl) ⟨496188, by rfl⟩ : syracuseStep 5292677 = 992377) (by norm_num)
theorem B6275717 : Blo 1857630 6275717 := bbase (se 4 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 6275717 = 1176697) (by norm_num)
theorem B2826893 : Blo 1857630 2826893 := bbase (se 3 (by rfl) ⟨530042, by rfl⟩ : syracuseStep 2826893 = 1060085) (by norm_num)
theorem B6701717 : Blo 1857630 6701717 := bbase (se 6 (by rfl) ⟨157071, by rfl⟩ : syracuseStep 6701717 = 314143) (by norm_num)
theorem B9413333 : Blo 1857630 9413333 := bbase (se 7 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 9413333 = 220625) (by norm_num)
theorem B2351845 : Blo 1857630 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B3769085 : Blo 1857630 3769085 := bbase (se 3 (by rfl) ⟨706703, by rfl⟩ : syracuseStep 3769085 = 1413407) (by norm_num)
theorem B2384641 : Blo 1857630 2384641 := bbase (se 2 (by rfl) ⟨894240, by rfl⟩ : syracuseStep 2384641 = 1788481) (by norm_num)
theorem B4702981 : Blo 1857630 4702981 := bbase (se 4 (by rfl) ⟨440904, by rfl⟩ : syracuseStep 4702981 = 881809) (by norm_num)
theorem B4703093 : Blo 1857630 4703093 := bbase (se 5 (by rfl) ⟨220457, by rfl⟩ : syracuseStep 4703093 = 440915) (by norm_num)
theorem B2089849 : Blo 1857630 2089849 := bbase (se 2 (by rfl) ⟨783693, by rfl⟩ : syracuseStep 2089849 = 1567387) (by norm_num)
theorem B2352017 : Blo 1857630 2352017 := bbase (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) (by norm_num)
theorem B7054229 : Blo 1857630 7054229 := bbase (se 6 (by rfl) ⟨165333, by rfl⟩ : syracuseStep 7054229 = 330667) (by norm_num)
theorem B2089885 : Blo 1857630 2089885 := bbase (se 3 (by rfl) ⟨391853, by rfl⟩ : syracuseStep 2089885 = 783707) (by norm_num)
theorem B5956517 : Blo 1857630 5956517 := bbase (se 4 (by rfl) ⟨558423, by rfl⟩ : syracuseStep 5956517 = 1116847) (by norm_num)
theorem B2646965 : Blo 1857630 2646965 := bbase (se 5 (by rfl) ⟨124076, by rfl⟩ : syracuseStep 2646965 = 248153) (by norm_num)
theorem B2089921 : Blo 1857630 2089921 := bbase (se 2 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 2089921 = 1567441) (by norm_num)
theorem B2352073 : Blo 1857630 2352073 := bbase (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) (by norm_num)
theorem B2089957 : Blo 1857630 2089957 := bbase (se 4 (by rfl) ⟨195933, by rfl⟩ : syracuseStep 2089957 = 391867) (by norm_num)
theorem B2089993 : Blo 1857630 2089993 := bbase (se 2 (by rfl) ⟨783747, by rfl⟩ : syracuseStep 2089993 = 1567495) (by norm_num)
theorem B16950293 : Blo 1857630 16950293 := bbase (se 6 (by rfl) ⟨397272, by rfl⟩ : syracuseStep 16950293 = 794545) (by norm_num)
theorem B2352169 : Blo 1857630 2352169 := bbase (se 2 (by rfl) ⟨882063, by rfl⟩ : syracuseStep 2352169 = 1764127) (by norm_num)
theorem B2090029 : Blo 1857630 2090029 := bbase (se 3 (by rfl) ⟨391880, by rfl⟩ : syracuseStep 2090029 = 783761) (by norm_num)
theorem B4703285 : Blo 1857630 4703285 := bbase (se 5 (by rfl) ⟨220466, by rfl⟩ : syracuseStep 4703285 = 440933) (by norm_num)
theorem B6276149 : Blo 1857630 6276149 := bbase (se 5 (by rfl) ⟨294194, by rfl⟩ : syracuseStep 6276149 = 588389) (by norm_num)
theorem B2090065 : Blo 1857630 2090065 := bbase (se 2 (by rfl) ⟨783774, by rfl⟩ : syracuseStep 2090065 = 1567549) (by norm_num)
theorem B2090101 : Blo 1857630 2090101 := bbase (se 5 (by rfl) ⟨97973, by rfl⟩ : syracuseStep 2090101 = 195947) (by norm_num)
theorem B9405557 : Blo 1857630 9405557 := bbase (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) (by norm_num)
theorem B7939205 : Blo 1857630 7939205 := bbase (se 4 (by rfl) ⟨744300, by rfl⟩ : syracuseStep 7939205 = 1488601) (by norm_num)
theorem B2786453 : Blo 1857630 2786453 := bbase (se 6 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 2786453 = 130615) (by norm_num)
theorem B2090137 : Blo 1857630 2090137 := bbase (se 2 (by rfl) ⟨783801, by rfl⟩ : syracuseStep 2090137 = 1567603) (by norm_num)
theorem B2786477 : Blo 1857630 2786477 := bbase (se 3 (by rfl) ⟨522464, by rfl⟩ : syracuseStep 2786477 = 1044929) (by norm_num)
theorem B2090173 : Blo 1857630 2090173 := bbase (se 3 (by rfl) ⟨391907, by rfl⟩ : syracuseStep 2090173 = 783815) (by norm_num)
theorem B2786501 : Blo 1857630 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B2352341 : Blo 1857630 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B2786525 : Blo 1857630 2786525 := bbase (se 3 (by rfl) ⟨522473, by rfl⟩ : syracuseStep 2786525 = 1044947) (by norm_num)
theorem B2090209 : Blo 1857630 2090209 := bbase (se 2 (by rfl) ⟨783828, by rfl⟩ : syracuseStep 2090209 = 1567657) (by norm_num)
theorem B2786549 : Blo 1857630 2786549 := bbase (se 5 (by rfl) ⟨130619, by rfl⟩ : syracuseStep 2786549 = 261239) (by norm_num)
theorem B12723445 : Blo 1857630 12723445 := bbase (se 5 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 12723445 = 1192823) (by norm_num)
theorem B2090245 : Blo 1857630 2090245 := bbase (se 4 (by rfl) ⟨195960, by rfl⟩ : syracuseStep 2090245 = 391921) (by norm_num)
theorem B2786573 : Blo 1857630 2786573 := bbase (se 3 (by rfl) ⟨522482, by rfl⟩ : syracuseStep 2786573 = 1044965) (by norm_num)
theorem B2352397 : Blo 1857630 2352397 := bbase (se 3 (by rfl) ⟨441074, by rfl⟩ : syracuseStep 2352397 = 882149) (by norm_num)
theorem B2786597 : Blo 1857630 2786597 := bbase (se 4 (by rfl) ⟨261243, by rfl⟩ : syracuseStep 2786597 = 522487) (by norm_num)
theorem B4465957 : Blo 1857630 4465957 := bbase (se 4 (by rfl) ⟨418683, by rfl⟩ : syracuseStep 4465957 = 837367) (by norm_num)
theorem B2090281 : Blo 1857630 2090281 := bbase (se 2 (by rfl) ⟨783855, by rfl⟩ : syracuseStep 2090281 = 1567711) (by norm_num)
theorem B2786621 : Blo 1857630 2786621 := bbase (se 3 (by rfl) ⟨522491, by rfl⟩ : syracuseStep 2786621 = 1044983) (by norm_num)
theorem B1910081 : Blo 1857630 1910081 := bbase (se 2 (by rfl) ⟨716280, by rfl⟩ : syracuseStep 1910081 = 1432561) (by norm_num)
theorem B2090317 : Blo 1857630 2090317 := bbase (se 3 (by rfl) ⟨391934, by rfl⟩ : syracuseStep 2090317 = 783869) (by norm_num)
theorem B2786645 : Blo 1857630 2786645 := bbase (se 12 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2786645 = 2041) (by norm_num)
theorem B2786669 : Blo 1857630 2786669 := bbase (se 3 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 2786669 = 1045001) (by norm_num)
theorem B2352493 : Blo 1857630 2352493 := bbase (se 3 (by rfl) ⟨441092, by rfl⟩ : syracuseStep 2352493 = 882185) (by norm_num)
theorem B1983857 : Blo 1857630 1983857 := bbase (se 2 (by rfl) ⟨743946, by rfl⟩ : syracuseStep 1983857 = 1487893) (by norm_num)
theorem B2090353 : Blo 1857630 2090353 := bbase (se 2 (by rfl) ⟨783882, by rfl⟩ : syracuseStep 2090353 = 1567765) (by norm_num)
theorem B2786693 : Blo 1857630 2786693 := bbase (se 4 (by rfl) ⟨261252, by rfl⟩ : syracuseStep 2786693 = 522505) (by norm_num)
theorem B4703629 : Blo 1857630 4703629 := bbase (se 3 (by rfl) ⟨881930, by rfl⟩ : syracuseStep 4703629 = 1763861) (by norm_num)
theorem B2090389 : Blo 1857630 2090389 := bbase (se 6 (by rfl) ⟨48993, by rfl⟩ : syracuseStep 2090389 = 97987) (by norm_num)
theorem B2786717 : Blo 1857630 2786717 := bbase (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) (by norm_num)
theorem B2786741 : Blo 1857630 2786741 := bbase (se 5 (by rfl) ⟨130628, by rfl⟩ : syracuseStep 2786741 = 261257) (by norm_num)
theorem B2090425 : Blo 1857630 2090425 := bbase (se 2 (by rfl) ⟨783909, by rfl⟩ : syracuseStep 2090425 = 1567819) (by norm_num)
theorem B2786765 : Blo 1857630 2786765 := bbase (se 3 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 2786765 = 1045037) (by norm_num)
theorem B2090461 : Blo 1857630 2090461 := bbase (se 3 (by rfl) ⟨391961, by rfl⟩ : syracuseStep 2090461 = 783923) (by norm_num)
theorem B2786789 : Blo 1857630 2786789 := bbase (se 4 (by rfl) ⟨261261, by rfl⟩ : syracuseStep 2786789 = 522523) (by norm_num)
theorem B2786813 : Blo 1857630 2786813 := bbase (se 3 (by rfl) ⟨522527, by rfl⟩ : syracuseStep 2786813 = 1045055) (by norm_num)
theorem B4703741 : Blo 1857630 4703741 := bbase (se 3 (by rfl) ⟨881951, by rfl⟩ : syracuseStep 4703741 = 1763903) (by norm_num)
theorem B2090497 : Blo 1857630 2090497 := bbase (se 2 (by rfl) ⟨783936, by rfl⟩ : syracuseStep 2090497 = 1567873) (by norm_num)
theorem B2786837 : Blo 1857630 2786837 := bbase (se 6 (by rfl) ⟨65316, by rfl⟩ : syracuseStep 2786837 = 130633) (by norm_num)
theorem B2352665 : Blo 1857630 2352665 := bbase (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) (by norm_num)
theorem B2090533 : Blo 1857630 2090533 := bbase (se 4 (by rfl) ⟨195987, by rfl⟩ : syracuseStep 2090533 = 391975) (by norm_num)
theorem B2786861 : Blo 1857630 2786861 := bbase (se 3 (by rfl) ⟨522536, by rfl⟩ : syracuseStep 2786861 = 1045073) (by norm_num)
theorem B2786885 : Blo 1857630 2786885 := bbase (se 4 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 2786885 = 522541) (by norm_num)
theorem B2090569 : Blo 1857630 2090569 := bbase (se 2 (by rfl) ⟨783963, by rfl⟩ : syracuseStep 2090569 = 1567927) (by norm_num)
theorem B2352721 : Blo 1857630 2352721 := bbase (se 2 (by rfl) ⟨882270, by rfl⟩ : syracuseStep 2352721 = 1764541) (by norm_num)
theorem B40175189 : Blo 1857630 40175189 := bbase (se 8 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 40175189 = 470803) (by norm_num)
theorem B2786909 : Blo 1857630 2786909 := bbase (se 3 (by rfl) ⟨522545, by rfl⟩ : syracuseStep 2786909 = 1045091) (by norm_num)
theorem B1984105 : Blo 1857630 1984105 := bbase (se 2 (by rfl) ⟨744039, by rfl⟩ : syracuseStep 1984105 = 1488079) (by norm_num)
theorem B2090605 : Blo 1857630 2090605 := bbase (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) (by norm_num)
theorem B2786933 : Blo 1857630 2786933 := bbase (se 5 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 2786933 = 261275) (by norm_num)
theorem B2786957 : Blo 1857630 2786957 := bbase (se 3 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 2786957 = 1045109) (by norm_num)
theorem B2090641 : Blo 1857630 2090641 := bbase (se 2 (by rfl) ⟨783990, by rfl⟩ : syracuseStep 2090641 = 1567981) (by norm_num)
theorem B9537173 : Blo 1857630 9537173 := bbase (se 6 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 9537173 = 447055) (by norm_num)
theorem B2786981 : Blo 1857630 2786981 := bbase (se 4 (by rfl) ⟨261279, by rfl⟩ : syracuseStep 2786981 = 522559) (by norm_num)
theorem B3180205 : Blo 1857630 3180205 := bbase (se 3 (by rfl) ⟨596288, by rfl⟩ : syracuseStep 3180205 = 1192577) (by norm_num)
theorem B2352817 : Blo 1857630 2352817 := bbase (se 2 (by rfl) ⟨882306, by rfl⟩ : syracuseStep 2352817 = 1764613) (by norm_num)
theorem B2090677 : Blo 1857630 2090677 := bbase (se 5 (by rfl) ⟨98000, by rfl⟩ : syracuseStep 2090677 = 196001) (by norm_num)
theorem B2787005 : Blo 1857630 2787005 := bbase (se 3 (by rfl) ⟨522563, by rfl⟩ : syracuseStep 2787005 = 1045127) (by norm_num)
theorem B4703933 : Blo 1857630 4703933 := bbase (se 3 (by rfl) ⟨881987, by rfl⟩ : syracuseStep 4703933 = 1763975) (by norm_num)
theorem B2787029 : Blo 1857630 2787029 := bbase (se 7 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 2787029 = 65321) (by norm_num)
theorem B2090713 : Blo 1857630 2090713 := bbase (se 2 (by rfl) ⟨784017, by rfl⟩ : syracuseStep 2090713 = 1568035) (by norm_num)
theorem B2787053 : Blo 1857630 2787053 := bbase (se 3 (by rfl) ⟨522572, by rfl⟩ : syracuseStep 2787053 = 1045145) (by norm_num)
theorem B2090749 : Blo 1857630 2090749 := bbase (se 3 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 2090749 = 784031) (by norm_num)
theorem B2787077 : Blo 1857630 2787077 := bbase (se 4 (by rfl) ⟨261288, by rfl⟩ : syracuseStep 2787077 = 522577) (by norm_num)
theorem B4179725 : Blo 1857630 4179725 := bbase (se 3 (by rfl) ⟨783698, by rfl⟩ : syracuseStep 4179725 = 1567397) (by norm_num)
theorem B2066197 : Blo 1857630 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B2787101 : Blo 1857630 2787101 := bbase (se 3 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 2787101 = 1045163) (by norm_num)
theorem B2090785 : Blo 1857630 2090785 := bbase (se 2 (by rfl) ⟨784044, by rfl⟩ : syracuseStep 2090785 = 1568089) (by norm_num)
theorem B2787125 : Blo 1857630 2787125 := bbase (se 5 (by rfl) ⟨130646, by rfl⟩ : syracuseStep 2787125 = 261293) (by norm_num)
theorem B2090821 : Blo 1857630 2090821 := bbase (se 4 (by rfl) ⟨196014, by rfl⟩ : syracuseStep 2090821 = 392029) (by norm_num)
theorem B2787149 : Blo 1857630 2787149 := bbase (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) (by norm_num)
theorem B4179797 : Blo 1857630 4179797 := bbase (se 9 (by rfl) ⟨12245, by rfl⟩ : syracuseStep 4179797 = 24491) (by norm_num)
theorem B2352989 : Blo 1857630 2352989 := bbase (se 3 (by rfl) ⟨441185, by rfl⟩ : syracuseStep 2352989 = 882371) (by norm_num)
theorem B2787173 : Blo 1857630 2787173 := bbase (se 4 (by rfl) ⟨261297, by rfl⟩ : syracuseStep 2787173 = 522595) (by norm_num)
theorem B2090857 : Blo 1857630 2090857 := bbase (se 2 (by rfl) ⟨784071, by rfl⟩ : syracuseStep 2090857 = 1568143) (by norm_num)
theorem B2787197 : Blo 1857630 2787197 := bbase (se 3 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 2787197 = 1045199) (by norm_num)
theorem B2090893 : Blo 1857630 2090893 := bbase (se 3 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 2090893 = 784085) (by norm_num)
theorem B4466573 : Blo 1857630 4466573 := bbase (se 3 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 4466573 = 1674965) (by norm_num)
theorem B2787221 : Blo 1857630 2787221 := bbase (se 6 (by rfl) ⟨65325, by rfl⟩ : syracuseStep 2787221 = 130651) (by norm_num)
theorem B2353045 : Blo 1857630 2353045 := bbase (se 6 (by rfl) ⟨55149, by rfl⟩ : syracuseStep 2353045 = 110299) (by norm_num)
theorem B4179869 : Blo 1857630 4179869 := bbase (se 3 (by rfl) ⟨783725, by rfl⟩ : syracuseStep 4179869 = 1567451) (by norm_num)
theorem B2787245 : Blo 1857630 2787245 := bbase (se 3 (by rfl) ⟨522608, by rfl⟩ : syracuseStep 2787245 = 1045217) (by norm_num)
theorem B2090929 : Blo 1857630 2090929 := bbase (se 2 (by rfl) ⟨784098, by rfl⟩ : syracuseStep 2090929 = 1568197) (by norm_num)
theorem B8480693 : Blo 1857630 8480693 := bbase (se 5 (by rfl) ⟨397532, by rfl⟩ : syracuseStep 8480693 = 795065) (by norm_num)
theorem B2787269 : Blo 1857630 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B10045397 : Blo 1857630 10045397 := bbase (se 7 (by rfl) ⟨117719, by rfl⟩ : syracuseStep 10045397 = 235439) (by norm_num)
theorem B2090965 : Blo 1857630 2090965 := bbase (se 7 (by rfl) ⟨24503, by rfl⟩ : syracuseStep 2090965 = 49007) (by norm_num)
theorem B2787293 : Blo 1857630 2787293 := bbase (se 3 (by rfl) ⟨522617, by rfl⟩ : syracuseStep 2787293 = 1045235) (by norm_num)
theorem B4179941 : Blo 1857630 4179941 := bbase (se 4 (by rfl) ⟨391869, by rfl⟩ : syracuseStep 4179941 = 783739) (by norm_num)
theorem B2787317 : Blo 1857630 2787317 := bbase (se 5 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 2787317 = 261311) (by norm_num)
theorem B2353141 : Blo 1857630 2353141 := bbase (se 5 (by rfl) ⟨110303, by rfl⟩ : syracuseStep 2353141 = 220607) (by norm_num)
theorem B2091001 : Blo 1857630 2091001 := bbase (se 2 (by rfl) ⟨784125, by rfl⟩ : syracuseStep 2091001 = 1568251) (by norm_num)
theorem B2787341 : Blo 1857630 2787341 := bbase (se 3 (by rfl) ⟨522626, by rfl⟩ : syracuseStep 2787341 = 1045253) (by norm_num)
theorem B4704277 : Blo 1857630 4704277 := bbase (se 6 (by rfl) ⟨110256, by rfl⟩ : syracuseStep 4704277 = 220513) (by norm_num)
theorem B2975773 : Blo 1857630 2975773 := bbase (se 3 (by rfl) ⟨557957, by rfl⟩ : syracuseStep 2975773 = 1115915) (by norm_num)
theorem B2091037 : Blo 1857630 2091037 := bbase (se 3 (by rfl) ⟨392069, by rfl⟩ : syracuseStep 2091037 = 784139) (by norm_num)
theorem B2787365 : Blo 1857630 2787365 := bbase (se 4 (by rfl) ⟨261315, by rfl⟩ : syracuseStep 2787365 = 522631) (by norm_num)
theorem B1984549 : Blo 1857630 1984549 := bbase (se 4 (by rfl) ⟨186051, by rfl⟩ : syracuseStep 1984549 = 372103) (by norm_num)
theorem B4180013 : Blo 1857630 4180013 := bbase (se 3 (by rfl) ⟨783752, by rfl⟩ : syracuseStep 4180013 = 1567505) (by norm_num)
theorem B2787389 : Blo 1857630 2787389 := bbase (se 3 (by rfl) ⟨522635, by rfl⟩ : syracuseStep 2787389 = 1045271) (by norm_num)
theorem B2091073 : Blo 1857630 2091073 := bbase (se 2 (by rfl) ⟨784152, by rfl⟩ : syracuseStep 2091073 = 1568305) (by norm_num)
theorem B2787413 : Blo 1857630 2787413 := bbase (se 8 (by rfl) ⟨16332, by rfl⟩ : syracuseStep 2787413 = 32665) (by norm_num)
theorem B4466773 : Blo 1857630 4466773 := bbase (se 8 (by rfl) ⟨26172, by rfl⟩ : syracuseStep 4466773 = 52345) (by norm_num)
theorem B1984609 : Blo 1857630 1984609 := bbase (se 2 (by rfl) ⟨744228, by rfl⟩ : syracuseStep 1984609 = 1488457) (by norm_num)
theorem B2091109 : Blo 1857630 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B2787437 : Blo 1857630 2787437 := bbase (se 3 (by rfl) ⟨522644, by rfl⟩ : syracuseStep 2787437 = 1045289) (by norm_num)
theorem B4180085 : Blo 1857630 4180085 := bbase (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) (by norm_num)
theorem B7940213 : Blo 1857630 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B2975869 : Blo 1857630 2975869 := bbase (se 3 (by rfl) ⟨557975, by rfl⟩ : syracuseStep 2975869 = 1115951) (by norm_num)
theorem B2787461 : Blo 1857630 2787461 := bbase (se 4 (by rfl) ⟨261324, by rfl⟩ : syracuseStep 2787461 = 522649) (by norm_num)
theorem B4704389 : Blo 1857630 4704389 := bbase (se 4 (by rfl) ⟨441036, by rfl⟩ : syracuseStep 4704389 = 882073) (by norm_num)
theorem B2091145 : Blo 1857630 2091145 := bbase (se 2 (by rfl) ⟨784179, by rfl⟩ : syracuseStep 2091145 = 1568359) (by norm_num)
theorem B2787485 : Blo 1857630 2787485 := bbase (se 3 (by rfl) ⟨522653, by rfl⟩ : syracuseStep 2787485 = 1045307) (by norm_num)
theorem B2353313 : Blo 1857630 2353313 := bbase (se 2 (by rfl) ⟨882492, by rfl⟩ : syracuseStep 2353313 = 1764985) (by norm_num)
theorem B2091181 : Blo 1857630 2091181 := bbase (se 3 (by rfl) ⟨392096, by rfl⟩ : syracuseStep 2091181 = 784193) (by norm_num)
theorem B2787509 : Blo 1857630 2787509 := bbase (se 5 (by rfl) ⟨130664, by rfl⟩ : syracuseStep 2787509 = 261329) (by norm_num)
theorem B5294261 : Blo 1857630 5294261 := bbase (se 5 (by rfl) ⟨248168, by rfl⟩ : syracuseStep 5294261 = 496337) (by norm_num)
theorem B4180157 : Blo 1857630 4180157 := bbase (se 3 (by rfl) ⟨783779, by rfl⟩ : syracuseStep 4180157 = 1567559) (by norm_num)
theorem B2787533 : Blo 1857630 2787533 := bbase (se 3 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 2787533 = 1045325) (by norm_num)
theorem B2091217 : Blo 1857630 2091217 := bbase (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) (by norm_num)
theorem B2353369 : Blo 1857630 2353369 := bbase (se 2 (by rfl) ⟨882513, by rfl⟩ : syracuseStep 2353369 = 1765027) (by norm_num)
theorem B2787557 : Blo 1857630 2787557 := bbase (se 4 (by rfl) ⟨261333, by rfl⟩ : syracuseStep 2787557 = 522667) (by norm_num)
theorem B1908733 : Blo 1857630 1908733 := bbase (se 3 (by rfl) ⟨357887, by rfl⟩ : syracuseStep 1908733 = 715775) (by norm_num)
theorem B7637237 : Blo 1857630 7637237 := bbase (se 5 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 7637237 = 715991) (by norm_num)
theorem B2091253 : Blo 1857630 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B2787581 : Blo 1857630 2787581 := bbase (se 3 (by rfl) ⟨522671, by rfl⟩ : syracuseStep 2787581 = 1045343) (by norm_num)
theorem B4180229 : Blo 1857630 4180229 := bbase (se 4 (by rfl) ⟨391896, by rfl⟩ : syracuseStep 4180229 = 783793) (by norm_num)
theorem B2787605 : Blo 1857630 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2091289 : Blo 1857630 2091289 := bbase (se 2 (by rfl) ⟨784233, by rfl⟩ : syracuseStep 2091289 = 1568467) (by norm_num)
theorem B2976029 : Blo 1857630 2976029 := bbase (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) (by norm_num)
theorem B2787629 : Blo 1857630 2787629 := bbase (se 3 (by rfl) ⟨522680, by rfl⟩ : syracuseStep 2787629 = 1045361) (by norm_num)
theorem B2353465 : Blo 1857630 2353465 := bbase (se 2 (by rfl) ⟨882549, by rfl⟩ : syracuseStep 2353465 = 1765099) (by norm_num)
theorem B2091325 : Blo 1857630 2091325 := bbase (se 3 (by rfl) ⟨392123, by rfl⟩ : syracuseStep 2091325 = 784247) (by norm_num)
theorem B2787653 : Blo 1857630 2787653 := bbase (se 4 (by rfl) ⟨261342, by rfl⟩ : syracuseStep 2787653 = 522685) (by norm_num)
theorem B4704581 : Blo 1857630 4704581 := bbase (se 4 (by rfl) ⟨441054, by rfl⟩ : syracuseStep 4704581 = 882109) (by norm_num)
theorem B4180301 : Blo 1857630 4180301 := bbase (se 3 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 4180301 = 1567613) (by norm_num)
theorem B2787677 : Blo 1857630 2787677 := bbase (se 3 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 2787677 = 1045379) (by norm_num)
theorem B2091361 : Blo 1857630 2091361 := bbase (se 2 (by rfl) ⟨784260, by rfl⟩ : syracuseStep 2091361 = 1568521) (by norm_num)
theorem B2787701 : Blo 1857630 2787701 := bbase (se 5 (by rfl) ⟨130673, by rfl⟩ : syracuseStep 2787701 = 261347) (by norm_num)
theorem B8931701 : Blo 1857630 8931701 := bbase (se 5 (by rfl) ⟨418673, by rfl⟩ : syracuseStep 8931701 = 837347) (by norm_num)
theorem B9406853 : Blo 1857630 9406853 := bbase (se 4 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 9406853 = 1763785) (by norm_num)
theorem B2091397 : Blo 1857630 2091397 := bbase (se 4 (by rfl) ⟨196068, by rfl⟩ : syracuseStep 2091397 = 392137) (by norm_num)
theorem B2787725 : Blo 1857630 2787725 := bbase (se 3 (by rfl) ⟨522698, by rfl⟩ : syracuseStep 2787725 = 1045397) (by norm_num)
theorem B4180373 : Blo 1857630 4180373 := bbase (se 6 (by rfl) ⟨97977, by rfl⟩ : syracuseStep 4180373 = 195955) (by norm_num)
theorem B1984925 : Blo 1857630 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B2787749 : Blo 1857630 2787749 := bbase (se 4 (by rfl) ⟨261351, by rfl⟩ : syracuseStep 2787749 = 522703) (by norm_num)
theorem B2091433 : Blo 1857630 2091433 := bbase (se 2 (by rfl) ⟨784287, by rfl⟩ : syracuseStep 2091433 = 1568575) (by norm_num)
theorem B2787773 : Blo 1857630 2787773 := bbase (se 3 (by rfl) ⟨522707, by rfl⟩ : syracuseStep 2787773 = 1045415) (by norm_num)
theorem B2091469 : Blo 1857630 2091469 := bbase (se 3 (by rfl) ⟨392150, by rfl⟩ : syracuseStep 2091469 = 784301) (by norm_num)
theorem B2787797 : Blo 1857630 2787797 := bbase (se 7 (by rfl) ⟨32669, by rfl⟩ : syracuseStep 2787797 = 65339) (by norm_num)
theorem B4180445 : Blo 1857630 4180445 := bbase (se 3 (by rfl) ⟨783833, by rfl⟩ : syracuseStep 4180445 = 1567667) (by norm_num)
theorem B2787821 : Blo 1857630 2787821 := bbase (se 3 (by rfl) ⟨522716, by rfl⟩ : syracuseStep 2787821 = 1045433) (by norm_num)
theorem B2091505 : Blo 1857630 2091505 := bbase (se 2 (by rfl) ⟨784314, by rfl⟩ : syracuseStep 2091505 = 1568629) (by norm_num)
theorem B2787845 : Blo 1857630 2787845 := bbase (se 4 (by rfl) ⟨261360, by rfl⟩ : syracuseStep 2787845 = 522721) (by norm_num)
theorem B2091541 : Blo 1857630 2091541 := bbase (se 6 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 2091541 = 98041) (by norm_num)
theorem B2787869 : Blo 1857630 2787869 := bbase (se 3 (by rfl) ⟨522725, by rfl⟩ : syracuseStep 2787869 = 1045451) (by norm_num)
theorem B4180517 : Blo 1857630 4180517 := bbase (se 4 (by rfl) ⟨391923, by rfl⟩ : syracuseStep 4180517 = 783847) (by norm_num)
theorem B2787893 : Blo 1857630 2787893 := bbase (se 5 (by rfl) ⟨130682, by rfl⟩ : syracuseStep 2787893 = 261365) (by norm_num)
theorem B9054773 : Blo 1857630 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B2091577 : Blo 1857630 2091577 := bbase (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) (by norm_num)
theorem B2787917 : Blo 1857630 2787917 := bbase (se 3 (by rfl) ⟨522734, by rfl⟩ : syracuseStep 2787917 = 1045469) (by norm_num)
theorem B2091613 : Blo 1857630 2091613 := bbase (se 3 (by rfl) ⟨392177, by rfl⟩ : syracuseStep 2091613 = 784355) (by norm_num)
theorem B2787941 : Blo 1857630 2787941 := bbase (se 4 (by rfl) ⟨261369, by rfl⟩ : syracuseStep 2787941 = 522739) (by norm_num)
theorem B4180589 : Blo 1857630 4180589 := bbase (se 3 (by rfl) ⟨783860, by rfl⟩ : syracuseStep 4180589 = 1567721) (by norm_num)
theorem B2787965 : Blo 1857630 2787965 := bbase (se 3 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 2787965 = 1045487) (by norm_num)
theorem B2091649 : Blo 1857630 2091649 := bbase (se 2 (by rfl) ⟨784368, by rfl⟩ : syracuseStep 2091649 = 1568737) (by norm_num)
theorem B2787989 : Blo 1857630 2787989 := bbase (se 6 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 2787989 = 130687) (by norm_num)
theorem B4704925 : Blo 1857630 4704925 := bbase (se 3 (by rfl) ⟨882173, by rfl⟩ : syracuseStep 4704925 = 1764347) (by norm_num)
theorem B2091685 : Blo 1857630 2091685 := bbase (se 4 (by rfl) ⟨196095, by rfl⟩ : syracuseStep 2091685 = 392191) (by norm_num)
theorem B2788013 : Blo 1857630 2788013 := bbase (se 3 (by rfl) ⟨522752, by rfl⟩ : syracuseStep 2788013 = 1045505) (by norm_num)
theorem B4180661 : Blo 1857630 4180661 := bbase (se 5 (by rfl) ⟨195968, by rfl⟩ : syracuseStep 4180661 = 391937) (by norm_num)
theorem B2788037 : Blo 1857630 2788037 := bbase (se 4 (by rfl) ⟨261378, by rfl⟩ : syracuseStep 2788037 = 522757) (by norm_num)
theorem B2091721 : Blo 1857630 2091721 := bbase (se 2 (by rfl) ⟨784395, by rfl⟩ : syracuseStep 2091721 = 1568791) (by norm_num)
theorem B2788061 : Blo 1857630 2788061 := bbase (se 3 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 2788061 = 1045523) (by norm_num)
theorem B6269669 : Blo 1857630 6269669 := bbase (se 4 (by rfl) ⟨587781, by rfl⟩ : syracuseStep 6269669 = 1175563) (by norm_num)
theorem B2091757 : Blo 1857630 2091757 := bbase (se 3 (by rfl) ⟨392204, by rfl⟩ : syracuseStep 2091757 = 784409) (by norm_num)
theorem B2788085 : Blo 1857630 2788085 := bbase (se 5 (by rfl) ⟨130691, by rfl⟩ : syracuseStep 2788085 = 261383) (by norm_num)
theorem B8932085 : Blo 1857630 8932085 := bbase (se 5 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 8932085 = 837383) (by norm_num)
theorem B4180733 : Blo 1857630 4180733 := bbase (se 3 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 4180733 = 1567775) (by norm_num)
theorem B2788109 : Blo 1857630 2788109 := bbase (se 3 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 2788109 = 1045541) (by norm_num)
theorem B4705037 : Blo 1857630 4705037 := bbase (se 3 (by rfl) ⟨882194, by rfl⟩ : syracuseStep 4705037 = 1764389) (by norm_num)
theorem B2091793 : Blo 1857630 2091793 := bbase (se 2 (by rfl) ⟨784422, by rfl⟩ : syracuseStep 2091793 = 1568845) (by norm_num)
theorem B2788133 : Blo 1857630 2788133 := bbase (se 4 (by rfl) ⟨261387, by rfl⟩ : syracuseStep 2788133 = 522775) (by norm_num)
theorem B2091829 : Blo 1857630 2091829 := bbase (se 5 (by rfl) ⟨98054, by rfl⟩ : syracuseStep 2091829 = 196109) (by norm_num)
theorem B2788157 : Blo 1857630 2788157 := bbase (se 3 (by rfl) ⟨522779, by rfl⟩ : syracuseStep 2788157 = 1045559) (by norm_num)
theorem B4180805 : Blo 1857630 4180805 := bbase (se 4 (by rfl) ⟨391950, by rfl⟩ : syracuseStep 4180805 = 783901) (by norm_num)
theorem B2788181 : Blo 1857630 2788181 := bbase (se 9 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 2788181 = 16337) (by norm_num)
theorem B5294933 : Blo 1857630 5294933 := bbase (se 9 (by rfl) ⟨15512, by rfl⟩ : syracuseStep 5294933 = 31025) (by norm_num)
theorem B1985369 : Blo 1857630 1985369 := bbase (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) (by norm_num)
theorem B2091865 : Blo 1857630 2091865 := bbase (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) (by norm_num)
theorem B2788205 : Blo 1857630 2788205 := bbase (se 3 (by rfl) ⟨522788, by rfl⟩ : syracuseStep 2788205 = 1045577) (by norm_num)
theorem B4467581 : Blo 1857630 4467581 := bbase (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) (by norm_num)
theorem B2091901 : Blo 1857630 2091901 := bbase (se 3 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 2091901 = 784463) (by norm_num)
theorem B2788229 : Blo 1857630 2788229 := bbase (se 4 (by rfl) ⟨261396, by rfl⟩ : syracuseStep 2788229 = 522793) (by norm_num)
theorem B5024645 : Blo 1857630 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B4180877 : Blo 1857630 4180877 := bbase (se 3 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 4180877 = 1567829) (by norm_num)
theorem B1985429 : Blo 1857630 1985429 := bbase (se 6 (by rfl) ⟨46533, by rfl⟩ : syracuseStep 1985429 = 93067) (by norm_num)
theorem B2788253 : Blo 1857630 2788253 := bbase (se 3 (by rfl) ⟨522797, by rfl⟩ : syracuseStep 2788253 = 1045595) (by norm_num)
theorem B2091937 : Blo 1857630 2091937 := bbase (se 2 (by rfl) ⟨784476, by rfl⟩ : syracuseStep 2091937 = 1568953) (by norm_num)
theorem B2788277 : Blo 1857630 2788277 := bbase (se 5 (by rfl) ⟨130700, by rfl⟩ : syracuseStep 2788277 = 261401) (by norm_num)
theorem B14117813 : Blo 1857630 14117813 := bbase (se 5 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 14117813 = 1323545) (by norm_num)
theorem B2091973 : Blo 1857630 2091973 := bbase (se 4 (by rfl) ⟨196122, by rfl⟩ : syracuseStep 2091973 = 392245) (by norm_num)
theorem B4705229 : Blo 1857630 4705229 := bbase (se 3 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 4705229 = 1764461) (by norm_num)
theorem B2788301 : Blo 1857630 2788301 := bbase (se 3 (by rfl) ⟨522806, by rfl⟩ : syracuseStep 2788301 = 1045613) (by norm_num)
theorem B4180949 : Blo 1857630 4180949 := bbase (se 7 (by rfl) ⟨48995, by rfl⟩ : syracuseStep 4180949 = 97991) (by norm_num)
theorem B7056341 : Blo 1857630 7056341 := bbase (se 7 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 7056341 = 165383) (by norm_num)
theorem B2788325 : Blo 1857630 2788325 := bbase (se 4 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 2788325 = 522811) (by norm_num)
theorem B2092009 : Blo 1857630 2092009 := bbase (se 2 (by rfl) ⟨784503, by rfl⟩ : syracuseStep 2092009 = 1569007) (by norm_num)
theorem B2788349 : Blo 1857630 2788349 := bbase (se 3 (by rfl) ⟨522815, by rfl⟩ : syracuseStep 2788349 = 1045631) (by norm_num)
theorem B2092045 : Blo 1857630 2092045 := bbase (se 3 (by rfl) ⟨392258, by rfl⟩ : syracuseStep 2092045 = 784517) (by norm_num)
theorem B2788373 : Blo 1857630 2788373 := bbase (se 6 (by rfl) ⟨65352, by rfl⟩ : syracuseStep 2788373 = 130705) (by norm_num)
theorem B1985557 : Blo 1857630 1985557 := bbase (se 6 (by rfl) ⟨46536, by rfl⟩ : syracuseStep 1985557 = 93073) (by norm_num)
theorem B4181021 : Blo 1857630 4181021 := bbase (se 3 (by rfl) ⟨783941, by rfl⟩ : syracuseStep 4181021 = 1567883) (by norm_num)
theorem B2788397 : Blo 1857630 2788397 := bbase (se 3 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 2788397 = 1045649) (by norm_num)
theorem B4590637 : Blo 1857630 4590637 := bbase (se 3 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 4590637 = 1721489) (by norm_num)
theorem B2092081 : Blo 1857630 2092081 := bbase (se 2 (by rfl) ⟨784530, by rfl⟩ : syracuseStep 2092081 = 1569061) (by norm_num)
theorem B2788421 : Blo 1857630 2788421 := bbase (se 4 (by rfl) ⟨261414, by rfl⟩ : syracuseStep 2788421 = 522829) (by norm_num)
theorem B2788445 : Blo 1857630 2788445 := bbase (se 3 (by rfl) ⟨522833, by rfl⟩ : syracuseStep 2788445 = 1045667) (by norm_num)
theorem B4181093 : Blo 1857630 4181093 := bbase (se 4 (by rfl) ⟨391977, by rfl⟩ : syracuseStep 4181093 = 783955) (by norm_num)
theorem B11906165 : Blo 1857630 11906165 := bbase (se 5 (by rfl) ⟨558101, by rfl⟩ : syracuseStep 11906165 = 1116203) (by norm_num)
theorem B2788469 : Blo 1857630 2788469 := bbase (se 5 (by rfl) ⟨130709, by rfl⟩ : syracuseStep 2788469 = 261419) (by norm_num)
theorem B2788493 : Blo 1857630 2788493 := bbase (se 3 (by rfl) ⟨522842, by rfl⟩ : syracuseStep 2788493 = 1045685) (by norm_num)
theorem B6270101 : Blo 1857630 6270101 := bbase (se 6 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 6270101 = 293911) (by norm_num)
theorem B33918101 : Blo 1857630 33918101 := bbase (se 6 (by rfl) ⟨794955, by rfl⟩ : syracuseStep 33918101 = 1589911) (by norm_num)
theorem B2788517 : Blo 1857630 2788517 := bbase (se 4 (by rfl) ⟨261423, by rfl⟩ : syracuseStep 2788517 = 522847) (by norm_num)
theorem B4181165 : Blo 1857630 4181165 := bbase (se 3 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 4181165 = 1567937) (by norm_num)
theorem B2788541 : Blo 1857630 2788541 := bbase (se 3 (by rfl) ⟨522851, by rfl⟩ : syracuseStep 2788541 = 1045703) (by norm_num)
theorem B2788565 : Blo 1857630 2788565 := bbase (se 7 (by rfl) ⟨32678, by rfl⟩ : syracuseStep 2788565 = 65357) (by norm_num)
theorem B2788589 : Blo 1857630 2788589 := bbase (se 3 (by rfl) ⟨522860, by rfl⟩ : syracuseStep 2788589 = 1045721) (by norm_num)
theorem B4181237 : Blo 1857630 4181237 := bbase (se 5 (by rfl) ⟨195995, by rfl⟩ : syracuseStep 4181237 = 391991) (by norm_num)
theorem B7056629 : Blo 1857630 7056629 := bbase (se 5 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 7056629 = 661559) (by norm_num)
theorem B3968261 : Blo 1857630 3968261 := bbase (se 4 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 3968261 = 744049) (by norm_num)
theorem B2788613 : Blo 1857630 2788613 := bbase (se 4 (by rfl) ⟨261432, by rfl⟩ : syracuseStep 2788613 = 522865) (by norm_num)
theorem B5295365 : Blo 1857630 5295365 := bbase (se 4 (by rfl) ⟨496440, by rfl⟩ : syracuseStep 5295365 = 992881) (by norm_num)
theorem B2788637 : Blo 1857630 2788637 := bbase (se 3 (by rfl) ⟨522869, by rfl⟩ : syracuseStep 2788637 = 1045739) (by norm_num)
theorem B4705573 : Blo 1857630 4705573 := bbase (se 4 (by rfl) ⟨441147, by rfl⟩ : syracuseStep 4705573 = 882295) (by norm_num)
theorem B2788661 : Blo 1857630 2788661 := bbase (se 5 (by rfl) ⟨130718, by rfl⟩ : syracuseStep 2788661 = 261437) (by norm_num)
theorem B4181309 : Blo 1857630 4181309 := bbase (se 3 (by rfl) ⟨783995, by rfl⟩ : syracuseStep 4181309 = 1567991) (by norm_num)
theorem B4238669 : Blo 1857630 4238669 := bbase (se 3 (by rfl) ⟨794750, by rfl⟩ : syracuseStep 4238669 = 1589501) (by norm_num)
theorem B2788685 : Blo 1857630 2788685 := bbase (se 3 (by rfl) ⟨522878, by rfl⟩ : syracuseStep 2788685 = 1045757) (by norm_num)
theorem B14110037 : Blo 1857630 14110037 := bbase (se 11 (by rfl) ⟨10334, by rfl⟩ : syracuseStep 14110037 = 20669) (by norm_num)
theorem B2788709 : Blo 1857630 2788709 := bbase (se 4 (by rfl) ⟨261441, by rfl⟩ : syracuseStep 2788709 = 522883) (by norm_num)
theorem B2788733 : Blo 1857630 2788733 := bbase (se 3 (by rfl) ⟨522887, by rfl⟩ : syracuseStep 2788733 = 1045775) (by norm_num)
theorem B4181381 : Blo 1857630 4181381 := bbase (se 4 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 4181381 = 784009) (by norm_num)
theorem B2977157 : Blo 1857630 2977157 := bbase (se 4 (by rfl) ⟨279108, by rfl⟩ : syracuseStep 2977157 = 558217) (by norm_num)
theorem B4705685 : Blo 1857630 4705685 := bbase (se 6 (by rfl) ⟨110289, by rfl⟩ : syracuseStep 4705685 = 220579) (by norm_num)
theorem B2788757 : Blo 1857630 2788757 := bbase (se 6 (by rfl) ⟨65361, by rfl⟩ : syracuseStep 2788757 = 130723) (by norm_num)
theorem B2788781 : Blo 1857630 2788781 := bbase (se 3 (by rfl) ⟨522896, by rfl⟩ : syracuseStep 2788781 = 1045793) (by norm_num)
theorem B7531973 : Blo 1857630 7531973 := bbase (se 4 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 7531973 = 1412245) (by norm_num)
theorem B2788805 : Blo 1857630 2788805 := bbase (se 4 (by rfl) ⟨261450, by rfl⟩ : syracuseStep 2788805 = 522901) (by norm_num)
theorem B4181453 : Blo 1857630 4181453 := bbase (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) (by norm_num)
theorem B4238813 : Blo 1857630 4238813 := bbase (se 3 (by rfl) ⟨794777, by rfl⟩ : syracuseStep 4238813 = 1589555) (by norm_num)
theorem B2788829 : Blo 1857630 2788829 := bbase (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) (by norm_num)
theorem B2788853 : Blo 1857630 2788853 := bbase (se 5 (by rfl) ⟨130727, by rfl⟩ : syracuseStep 2788853 = 261455) (by norm_num)
theorem B3968509 : Blo 1857630 3968509 := bbase (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) (by norm_num)
theorem B2788877 : Blo 1857630 2788877 := bbase (se 3 (by rfl) ⟨522914, by rfl⟩ : syracuseStep 2788877 = 1045829) (by norm_num)
theorem B6696469 : Blo 1857630 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B4181525 : Blo 1857630 4181525 := bbase (se 6 (by rfl) ⟨98004, by rfl⟩ : syracuseStep 4181525 = 196009) (by norm_num)
theorem B2788901 : Blo 1857630 2788901 := bbase (se 4 (by rfl) ⟨261459, by rfl⟩ : syracuseStep 2788901 = 522919) (by norm_num)
theorem B2788925 : Blo 1857630 2788925 := bbase (se 3 (by rfl) ⟨522923, by rfl⟩ : syracuseStep 2788925 = 1045847) (by norm_num)
theorem B6270533 : Blo 1857630 6270533 := bbase (se 4 (by rfl) ⟨587862, by rfl⟩ : syracuseStep 6270533 = 1175725) (by norm_num)
theorem B4705877 : Blo 1857630 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B2788949 : Blo 1857630 2788949 := bbase (se 8 (by rfl) ⟨16341, by rfl⟩ : syracuseStep 2788949 = 32683) (by norm_num)
theorem B53612117 : Blo 1857630 53612117 := bbase (se 8 (by rfl) ⟨314133, by rfl⟩ : syracuseStep 53612117 = 628267) (by norm_num)
theorem B4181597 : Blo 1857630 4181597 := bbase (se 3 (by rfl) ⟨784049, by rfl⟩ : syracuseStep 4181597 = 1568099) (by norm_num)
theorem B2788973 : Blo 1857630 2788973 := bbase (se 3 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 2788973 = 1045865) (by norm_num)
theorem B2788997 : Blo 1857630 2788997 := bbase (se 4 (by rfl) ⟨261468, by rfl⟩ : syracuseStep 2788997 = 522937) (by norm_num)
theorem B9408149 : Blo 1857630 9408149 := bbase (se 6 (by rfl) ⟨220503, by rfl⟩ : syracuseStep 9408149 = 441007) (by norm_num)
theorem B2789021 : Blo 1857630 2789021 := bbase (se 3 (by rfl) ⟨522941, by rfl⟩ : syracuseStep 2789021 = 1045883) (by norm_num)
theorem B4181669 : Blo 1857630 4181669 := bbase (se 4 (by rfl) ⟨392031, by rfl⟩ : syracuseStep 4181669 = 784063) (by norm_num)
theorem B2789045 : Blo 1857630 2789045 := bbase (se 5 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 2789045 = 261473) (by norm_num)
theorem B2231993 : Blo 1857630 2231993 := bbase (se 2 (by rfl) ⟨836997, by rfl⟩ : syracuseStep 2231993 = 1673995) (by norm_num)
theorem B2789069 : Blo 1857630 2789069 := bbase (se 3 (by rfl) ⟨522950, by rfl⟩ : syracuseStep 2789069 = 1045901) (by norm_num)
theorem B2789093 : Blo 1857630 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B4181741 : Blo 1857630 4181741 := bbase (se 3 (by rfl) ⟨784076, by rfl⟩ : syracuseStep 4181741 = 1568153) (by norm_num)
theorem B2789117 : Blo 1857630 2789117 := bbase (se 3 (by rfl) ⟨522959, by rfl⟩ : syracuseStep 2789117 = 1045919) (by norm_num)
theorem B5951237 : Blo 1857630 5951237 := bbase (se 4 (by rfl) ⟨557928, by rfl⟩ : syracuseStep 5951237 = 1115857) (by norm_num)
theorem B2789141 : Blo 1857630 2789141 := bbase (se 6 (by rfl) ⟨65370, by rfl⟩ : syracuseStep 2789141 = 130741) (by norm_num)
theorem B2789165 : Blo 1857630 2789165 := bbase (se 3 (by rfl) ⟨522968, by rfl⟩ : syracuseStep 2789165 = 1045937) (by norm_num)
theorem B4525877 : Blo 1857630 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B4181813 : Blo 1857630 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B2789189 : Blo 1857630 2789189 := bbase (se 4 (by rfl) ⟨261486, by rfl⟩ : syracuseStep 2789189 = 522973) (by norm_num)
theorem B2789213 : Blo 1857630 2789213 := bbase (se 3 (by rfl) ⟨522977, by rfl⟩ : syracuseStep 2789213 = 1045955) (by norm_num)
theorem B7941989 : Blo 1857630 7941989 := bbase (se 4 (by rfl) ⟨744561, by rfl⟩ : syracuseStep 7941989 = 1489123) (by norm_num)
theorem B2789237 : Blo 1857630 2789237 := bbase (se 5 (by rfl) ⟨130745, by rfl⟩ : syracuseStep 2789237 = 261491) (by norm_num)
theorem B4181885 : Blo 1857630 4181885 := bbase (se 3 (by rfl) ⟨784103, by rfl⟩ : syracuseStep 4181885 = 1568207) (by norm_num)
theorem B2977669 : Blo 1857630 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B2789261 : Blo 1857630 2789261 := bbase (se 3 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 2789261 = 1045973) (by norm_num)
theorem B2789285 : Blo 1857630 2789285 := bbase (se 4 (by rfl) ⟨261495, by rfl⟩ : syracuseStep 2789285 = 522991) (by norm_num)
theorem B4706221 : Blo 1857630 4706221 := bbase (se 3 (by rfl) ⟨882416, by rfl⟩ : syracuseStep 4706221 = 1764833) (by norm_num)
theorem B2789309 : Blo 1857630 2789309 := bbase (se 3 (by rfl) ⟨522995, by rfl⟩ : syracuseStep 2789309 = 1045991) (by norm_num)
theorem B4181957 : Blo 1857630 4181957 := bbase (se 4 (by rfl) ⟨392058, by rfl⟩ : syracuseStep 4181957 = 784117) (by norm_num)
theorem B2789333 : Blo 1857630 2789333 := bbase (se 7 (by rfl) ⟨32687, by rfl⟩ : syracuseStep 2789333 = 65375) (by norm_num)
theorem B2232301 : Blo 1857630 2232301 := bbase (se 3 (by rfl) ⟨418556, by rfl⟩ : syracuseStep 2232301 = 837113) (by norm_num)
theorem B2789357 : Blo 1857630 2789357 := bbase (se 3 (by rfl) ⟨523004, by rfl⟩ : syracuseStep 2789357 = 1046009) (by norm_num)
theorem B6270965 : Blo 1857630 6270965 := bbase (se 5 (by rfl) ⟨293951, by rfl⟩ : syracuseStep 6270965 = 587903) (by norm_num)
theorem B3969013 : Blo 1857630 3969013 := bbase (se 5 (by rfl) ⟨186047, by rfl⟩ : syracuseStep 3969013 = 372095) (by norm_num)
theorem B2789381 : Blo 1857630 2789381 := bbase (se 4 (by rfl) ⟨261504, by rfl⟩ : syracuseStep 2789381 = 523009) (by norm_num)
theorem B2232329 : Blo 1857630 2232329 := bbase (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) (by norm_num)
theorem B4182029 : Blo 1857630 4182029 := bbase (se 3 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 4182029 = 1568261) (by norm_num)
theorem B4706333 : Blo 1857630 4706333 := bbase (se 3 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 4706333 = 1764875) (by norm_num)
theorem B2789405 : Blo 1857630 2789405 := bbase (se 3 (by rfl) ⟨523013, by rfl⟩ : syracuseStep 2789405 = 1046027) (by norm_num)
theorem B4239397 : Blo 1857630 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B2789429 : Blo 1857630 2789429 := bbase (se 5 (by rfl) ⟨130754, by rfl⟩ : syracuseStep 2789429 = 261509) (by norm_num)
theorem B4182101 : Blo 1857630 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B4182173 : Blo 1857630 4182173 := bbase (se 3 (by rfl) ⟨784157, by rfl⟩ : syracuseStep 4182173 = 1568315) (by norm_num)
theorem B9539797 : Blo 1857630 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B4706525 : Blo 1857630 4706525 := bbase (se 3 (by rfl) ⟨882473, by rfl⟩ : syracuseStep 4706525 = 1764947) (by norm_num)
theorem B4182245 : Blo 1857630 4182245 := bbase (se 4 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 4182245 = 784171) (by norm_num)
theorem B4182317 : Blo 1857630 4182317 := bbase (se 3 (by rfl) ⟨784184, by rfl⟩ : syracuseStep 4182317 = 1568369) (by norm_num)
theorem B10580341 : Blo 1857630 10580341 := bbase (se 5 (by rfl) ⟨495953, by rfl⟩ : syracuseStep 10580341 = 991907) (by norm_num)
theorem B4182389 : Blo 1857630 4182389 := bbase (se 5 (by rfl) ⟨196049, by rfl⟩ : syracuseStep 4182389 = 392099) (by norm_num)
theorem B7057813 : Blo 1857630 7057813 := bbase (se 6 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 7057813 = 330835) (by norm_num)
theorem B3527077 : Blo 1857630 3527077 := bbase (se 4 (by rfl) ⟨330663, by rfl⟩ : syracuseStep 3527077 = 661327) (by norm_num)
theorem B6271397 : Blo 1857630 6271397 := bbase (se 4 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 6271397 = 1175887) (by norm_num)
theorem B4182461 : Blo 1857630 4182461 := bbase (se 3 (by rfl) ⟨784211, by rfl⟩ : syracuseStep 4182461 = 1568423) (by norm_num)
theorem B2232829 : Blo 1857630 2232829 := bbase (se 3 (by rfl) ⟨418655, by rfl⟩ : syracuseStep 2232829 = 837311) (by norm_num)
theorem B4182533 : Blo 1857630 4182533 := bbase (se 4 (by rfl) ⟨392112, by rfl⟩ : syracuseStep 4182533 = 784225) (by norm_num)
theorem B3527221 : Blo 1857630 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B4706869 : Blo 1857630 4706869 := bbase (se 5 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 4706869 = 441269) (by norm_num)
theorem B4182605 : Blo 1857630 4182605 := bbase (se 3 (by rfl) ⟨784238, by rfl⟩ : syracuseStep 4182605 = 1568477) (by norm_num)
theorem B2863717 : Blo 1857630 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B2683525 : Blo 1857630 2683525 := bbase (se 4 (by rfl) ⟨251580, by rfl⟩ : syracuseStep 2683525 = 503161) (by norm_num)
theorem B5952149 : Blo 1857630 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B19075733 : Blo 1857630 19075733 := bbase (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) (by norm_num)
theorem B4182677 : Blo 1857630 4182677 := bbase (se 6 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 4182677 = 196063) (by norm_num)
theorem B4706981 : Blo 1857630 4706981 := bbase (se 4 (by rfl) ⟨441279, by rfl⟩ : syracuseStep 4706981 = 882559) (by norm_num)
theorem B7058117 : Blo 1857630 7058117 := bbase (se 4 (by rfl) ⟨661698, by rfl⟩ : syracuseStep 7058117 = 1323397) (by norm_num)
theorem B3527381 : Blo 1857630 3527381 := bbase (se 7 (by rfl) ⟨41336, by rfl⟩ : syracuseStep 3527381 = 82673) (by norm_num)
theorem B4182749 : Blo 1857630 4182749 := bbase (se 3 (by rfl) ⟨784265, by rfl⟩ : syracuseStep 4182749 = 1568531) (by norm_num)
theorem B4182821 : Blo 1857630 4182821 := bbase (se 4 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 4182821 = 784279) (by norm_num)
theorem B6271829 : Blo 1857630 6271829 := bbase (se 9 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 6271829 = 36749) (by norm_num)
theorem B3527525 : Blo 1857630 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B4707173 : Blo 1857630 4707173 := bbase (se 4 (by rfl) ⟨441297, by rfl⟩ : syracuseStep 4707173 = 882595) (by norm_num)
theorem B3969901 : Blo 1857630 3969901 := bbase (se 3 (by rfl) ⟨744356, by rfl⟩ : syracuseStep 3969901 = 1488713) (by norm_num)
theorem B4182893 : Blo 1857630 4182893 := bbase (se 3 (by rfl) ⟨784292, by rfl⟩ : syracuseStep 4182893 = 1568585) (by norm_num)
theorem B2978669 : Blo 1857630 2978669 := bbase (se 3 (by rfl) ⟨558500, by rfl⟩ : syracuseStep 2978669 = 1117001) (by norm_num)
theorem B5305205 : Blo 1857630 5305205 := bbase (se 5 (by rfl) ⟨248681, by rfl⟩ : syracuseStep 5305205 = 497363) (by norm_num)
theorem B9409445 : Blo 1857630 9409445 := bbase (se 4 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 9409445 = 1764271) (by norm_num)
theorem B4182965 : Blo 1857630 4182965 := bbase (se 5 (by rfl) ⟨196076, by rfl⟩ : syracuseStep 4182965 = 392153) (by norm_num)
theorem B4183037 : Blo 1857630 4183037 := bbase (se 3 (by rfl) ⟨784319, by rfl⟩ : syracuseStep 4183037 = 1568639) (by norm_num)
theorem B4240421 : Blo 1857630 4240421 := bbase (se 4 (by rfl) ⟨397539, by rfl⟩ : syracuseStep 4240421 = 795079) (by norm_num)
theorem B4183109 : Blo 1857630 4183109 := bbase (se 4 (by rfl) ⟨392166, by rfl⟩ : syracuseStep 4183109 = 784333) (by norm_num)
theorem B3527813 : Blo 1857630 3527813 := bbase (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) (by norm_num)
theorem B4183181 : Blo 1857630 4183181 := bbase (se 3 (by rfl) ⟨784346, by rfl⟩ : syracuseStep 4183181 = 1568693) (by norm_num)
theorem B17863861 : Blo 1857630 17863861 := bbase (se 5 (by rfl) ⟨837368, by rfl⟩ : syracuseStep 17863861 = 1674737) (by norm_num)
theorem B4240565 : Blo 1857630 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B4183253 : Blo 1857630 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B4076765 : Blo 1857630 4076765 := bbase (se 3 (by rfl) ⟨764393, by rfl⟩ : syracuseStep 4076765 = 1528787) (by norm_num)
theorem B2512117 : Blo 1857630 2512117 := bbase (se 5 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 2512117 = 235511) (by norm_num)
theorem B6272261 : Blo 1857630 6272261 := bbase (se 4 (by rfl) ⟨588024, by rfl⟩ : syracuseStep 6272261 = 1176049) (by norm_num)
theorem B3527965 : Blo 1857630 3527965 := bbase (se 3 (by rfl) ⟨661493, by rfl⟩ : syracuseStep 3527965 = 1322987) (by norm_num)
theorem B4183325 : Blo 1857630 4183325 := bbase (se 3 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 4183325 = 1568747) (by norm_num)
theorem B3626293 : Blo 1857630 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B3347773 : Blo 1857630 3347773 := bbase (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) (by norm_num)
theorem B3970397 : Blo 1857630 3970397 := bbase (se 3 (by rfl) ⟨744449, by rfl⟩ : syracuseStep 3970397 = 1488899) (by norm_num)
theorem B3134821 : Blo 1857630 3134821 := bbase (se 4 (by rfl) ⟨293889, by rfl⟩ : syracuseStep 3134821 = 587779) (by norm_num)
theorem B4183397 : Blo 1857630 4183397 := bbase (se 4 (by rfl) ⟨392193, by rfl⟩ : syracuseStep 4183397 = 784387) (by norm_num)
theorem B2512301 : Blo 1857630 2512301 := bbase (se 3 (by rfl) ⟨471056, by rfl⟩ : syracuseStep 2512301 = 942113) (by norm_num)
theorem B4183469 : Blo 1857630 4183469 := bbase (se 3 (by rfl) ⟨784400, by rfl⟩ : syracuseStep 4183469 = 1568801) (by norm_num)
theorem B3134909 : Blo 1857630 3134909 := bbase (se 3 (by rfl) ⟨587795, by rfl⟩ : syracuseStep 3134909 = 1175591) (by norm_num)
theorem B4183541 : Blo 1857630 4183541 := bbase (se 5 (by rfl) ⟨196103, by rfl⟩ : syracuseStep 4183541 = 392207) (by norm_num)
theorem B3135037 : Blo 1857630 3135037 := bbase (se 3 (by rfl) ⟨587819, by rfl⟩ : syracuseStep 3135037 = 1175639) (by norm_num)
theorem B4183613 : Blo 1857630 4183613 := bbase (se 3 (by rfl) ⟨784427, by rfl⟩ : syracuseStep 4183613 = 1568855) (by norm_num)
theorem B3528269 : Blo 1857630 3528269 := bbase (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) (by norm_num)
theorem B4183685 : Blo 1857630 4183685 := bbase (se 4 (by rfl) ⟨392220, by rfl⟩ : syracuseStep 4183685 = 784441) (by norm_num)
theorem B3135125 : Blo 1857630 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B2234017 : Blo 1857630 2234017 := bbase (se 2 (by rfl) ⟨837756, by rfl⟩ : syracuseStep 2234017 = 1675513) (by norm_num)
theorem B6272693 : Blo 1857630 6272693 := bbase (se 5 (by rfl) ⟨294032, by rfl⟩ : syracuseStep 6272693 = 588065) (by norm_num)
theorem B4183757 : Blo 1857630 4183757 := bbase (se 3 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 4183757 = 1568909) (by norm_num)
theorem B3135253 : Blo 1857630 3135253 := bbase (se 6 (by rfl) ⟨73482, by rfl⟩ : syracuseStep 3135253 = 146965) (by norm_num)
theorem B4183829 : Blo 1857630 4183829 := bbase (se 6 (by rfl) ⟨98058, by rfl⟩ : syracuseStep 4183829 = 196117) (by norm_num)
theorem B13391669 : Blo 1857630 13391669 := bbase (se 5 (by rfl) ⟨627734, by rfl⟩ : syracuseStep 13391669 = 1255469) (by norm_num)
theorem B4183901 : Blo 1857630 4183901 := bbase (se 3 (by rfl) ⟨784481, by rfl⟩ : syracuseStep 4183901 = 1568963) (by norm_num)
theorem B3135341 : Blo 1857630 3135341 := bbase (se 3 (by rfl) ⟨587876, by rfl⟩ : syracuseStep 3135341 = 1175753) (by norm_num)
theorem B3766181 : Blo 1857630 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B4183973 : Blo 1857630 4183973 := bbase (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) (by norm_num)
theorem B5953493 : Blo 1857630 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B3135469 : Blo 1857630 3135469 := bbase (se 3 (by rfl) ⟨587900, by rfl⟩ : syracuseStep 3135469 = 1175801) (by norm_num)
theorem B4184045 : Blo 1857630 4184045 := bbase (se 3 (by rfl) ⟨784508, by rfl⟩ : syracuseStep 4184045 = 1569017) (by norm_num)
theorem B4184117 : Blo 1857630 4184117 := bbase (se 5 (by rfl) ⟨196130, by rfl⟩ : syracuseStep 4184117 = 392261) (by norm_num)
theorem B3135557 : Blo 1857630 3135557 := bbase (se 4 (by rfl) ⟨293958, by rfl⟩ : syracuseStep 3135557 = 587917) (by norm_num)
theorem B5290069 : Blo 1857630 5290069 := bbase (se 8 (by rfl) ⟨30996, by rfl⟩ : syracuseStep 5290069 = 61993) (by norm_num)
theorem B6273125 : Blo 1857630 6273125 := bbase (se 4 (by rfl) ⟨588105, by rfl⟩ : syracuseStep 6273125 = 1176211) (by norm_num)
theorem B4528261 : Blo 1857630 4528261 := bbase (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) (by norm_num)
theorem B2513053 : Blo 1857630 2513053 := bbase (se 3 (by rfl) ⟨471197, by rfl⟩ : syracuseStep 2513053 = 942395) (by norm_num)
theorem B9410741 : Blo 1857630 9410741 := bbase (se 5 (by rfl) ⟨441128, by rfl⟩ : syracuseStep 9410741 = 882257) (by norm_num)
theorem B3135685 : Blo 1857630 3135685 := bbase (se 4 (by rfl) ⟨293970, by rfl⟩ : syracuseStep 3135685 = 587941) (by norm_num)
theorem B2513101 : Blo 1857630 2513101 := bbase (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) (by norm_num)
theorem B7936213 : Blo 1857630 7936213 := bbase (se 7 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 7936213 = 186005) (by norm_num)
theorem B3971285 : Blo 1857630 3971285 := bbase (se 7 (by rfl) ⟨46538, by rfl⟩ : syracuseStep 3971285 = 93077) (by norm_num)
theorem B3135773 : Blo 1857630 3135773 := bbase (se 3 (by rfl) ⟨587957, by rfl⟩ : syracuseStep 3135773 = 1175915) (by norm_num)
theorem B10582325 : Blo 1857630 10582325 := bbase (se 5 (by rfl) ⟨496046, by rfl⟩ : syracuseStep 10582325 = 992093) (by norm_num)
theorem B3529021 : Blo 1857630 3529021 := bbase (se 3 (by rfl) ⟨661691, by rfl⟩ : syracuseStep 3529021 = 1323383) (by norm_num)
theorem B3971405 : Blo 1857630 3971405 := bbase (se 3 (by rfl) ⟨744638, by rfl⟩ : syracuseStep 3971405 = 1489277) (by norm_num)
theorem B8477045 : Blo 1857630 8477045 := bbase (se 5 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 8477045 = 794723) (by norm_num)
theorem B20363669 : Blo 1857630 20363669 := bbase (se 6 (by rfl) ⟨477273, by rfl⟩ : syracuseStep 20363669 = 954547) (by norm_num)
theorem B3135901 : Blo 1857630 3135901 := bbase (se 3 (by rfl) ⟨587981, by rfl⟩ : syracuseStep 3135901 = 1175963) (by norm_num)
theorem B2513317 : Blo 1857630 2513317 := bbase (se 4 (by rfl) ⟨235623, by rfl⟩ : syracuseStep 2513317 = 471247) (by norm_num)
theorem B3529165 : Blo 1857630 3529165 := bbase (se 3 (by rfl) ⟨661718, by rfl⟩ : syracuseStep 3529165 = 1323437) (by norm_num)
theorem B5650901 : Blo 1857630 5650901 := bbase (se 7 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 5650901 = 132443) (by norm_num)
theorem B3135989 : Blo 1857630 3135989 := bbase (se 5 (by rfl) ⟨146999, by rfl⟩ : syracuseStep 3135989 = 293999) (by norm_num)
theorem B6273557 : Blo 1857630 6273557 := bbase (se 6 (by rfl) ⟨147036, by rfl⟩ : syracuseStep 6273557 = 294073) (by norm_num)
theorem B15874613 : Blo 1857630 15874613 := bbase (se 5 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 15874613 = 1488245) (by norm_num)
theorem B3529325 : Blo 1857630 3529325 := bbase (se 3 (by rfl) ⟨661748, by rfl⟩ : syracuseStep 3529325 = 1323497) (by norm_num)
theorem B3136117 : Blo 1857630 3136117 := bbase (se 5 (by rfl) ⟨147005, by rfl⟩ : syracuseStep 3136117 = 294011) (by norm_num)
theorem B3676837 : Blo 1857630 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B3349181 : Blo 1857630 3349181 := bbase (se 3 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 3349181 = 1255943) (by norm_num)
theorem B3136205 : Blo 1857630 3136205 := bbase (se 3 (by rfl) ⟨588038, by rfl⟩ : syracuseStep 3136205 = 1176077) (by norm_num)
theorem B3349237 : Blo 1857630 3349237 := bbase (se 5 (by rfl) ⟨156995, by rfl⟩ : syracuseStep 3349237 = 313991) (by norm_num)
theorem B3529469 : Blo 1857630 3529469 := bbase (se 3 (by rfl) ⟨661775, by rfl⟩ : syracuseStep 3529469 = 1323551) (by norm_num)
theorem B7060229 : Blo 1857630 7060229 := bbase (se 4 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 7060229 = 1323793) (by norm_num)
theorem B3136333 : Blo 1857630 3136333 := bbase (se 3 (by rfl) ⟨588062, by rfl⟩ : syracuseStep 3136333 = 1176125) (by norm_num)
theorem B1882985 : Blo 1857630 1882985 := bbase (se 2 (by rfl) ⟨706119, by rfl⟩ : syracuseStep 1882985 = 1412239) (by norm_num)
theorem B11910037 : Blo 1857630 11910037 := bbase (se 6 (by rfl) ⟨279141, by rfl⟩ : syracuseStep 11910037 = 558283) (by norm_num)
theorem B4463525 : Blo 1857630 4463525 := bbase (se 4 (by rfl) ⟨418455, by rfl⟩ : syracuseStep 4463525 = 836911) (by norm_num)
theorem B3136421 : Blo 1857630 3136421 := bbase (se 4 (by rfl) ⟨294039, by rfl⟩ : syracuseStep 3136421 = 588079) (by norm_num)
theorem B6273989 : Blo 1857630 6273989 := bbase (se 4 (by rfl) ⟨588186, by rfl⟩ : syracuseStep 6273989 = 1176373) (by norm_num)
theorem B7535605 : Blo 1857630 7535605 := bbase (se 5 (by rfl) ⟨353231, by rfl⟩ : syracuseStep 7535605 = 706463) (by norm_num)
theorem B3529757 : Blo 1857630 3529757 := bbase (se 3 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 3529757 = 1323659) (by norm_num)
theorem B3136549 : Blo 1857630 3136549 := bbase (se 4 (by rfl) ⟨294051, by rfl⟩ : syracuseStep 3136549 = 588103) (by norm_num)
theorem B7060517 : Blo 1857630 7060517 := bbase (se 4 (by rfl) ⟨661923, by rfl⟩ : syracuseStep 7060517 = 1323847) (by norm_num)
theorem B6200405 : Blo 1857630 6200405 := bbase (se 8 (by rfl) ⟨36330, by rfl⟩ : syracuseStep 6200405 = 72661) (by norm_num)
theorem B3136637 : Blo 1857630 3136637 := bbase (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) (by norm_num)
theorem B5291173 : Blo 1857630 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B3529909 : Blo 1857630 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B2645245 : Blo 1857630 2645245 := bbase (se 3 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 2645245 = 991967) (by norm_num)
theorem B3136765 : Blo 1857630 3136765 := bbase (se 3 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 3136765 = 1176287) (by norm_num)
theorem B5160197 : Blo 1857630 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B3136853 : Blo 1857630 3136853 := bbase (se 11 (by rfl) ⟨2297, by rfl⟩ : syracuseStep 3136853 = 4595) (by norm_num)
theorem B5954917 : Blo 1857630 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B6274421 : Blo 1857630 6274421 := bbase (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) (by norm_num)
theorem B1883557 : Blo 1857630 1883557 := bbase (se 4 (by rfl) ⟨176583, by rfl⟩ : syracuseStep 1883557 = 353167) (by norm_num)
theorem B9412037 : Blo 1857630 9412037 := bbase (se 4 (by rfl) ⟨882378, by rfl⟩ : syracuseStep 9412037 = 1764757) (by norm_num)
theorem B3136981 : Blo 1857630 3136981 := bbase (se 7 (by rfl) ⟨36761, by rfl⟩ : syracuseStep 3136981 = 73523) (by norm_num)
theorem B3530213 : Blo 1857630 3530213 := bbase (se 4 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 3530213 = 661915) (by norm_num)
theorem B3137069 : Blo 1857630 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B3137197 : Blo 1857630 3137197 := bbase (se 3 (by rfl) ⟨588224, by rfl⟩ : syracuseStep 3137197 = 1176449) (by norm_num)
theorem B3137285 : Blo 1857630 3137285 := bbase (se 4 (by rfl) ⟨294120, by rfl⟩ : syracuseStep 3137285 = 588241) (by norm_num)
theorem B6274853 : Blo 1857630 6274853 := bbase (se 4 (by rfl) ⟨588267, by rfl⟩ : syracuseStep 6274853 = 1176535) (by norm_num)
theorem B9404261 : Blo 1857630 9404261 := bbase (se 4 (by rfl) ⟨881649, by rfl⟩ : syracuseStep 9404261 = 1763299) (by norm_num)
theorem B3137413 : Blo 1857630 3137413 := bbase (se 4 (by rfl) ⟨294132, by rfl⟩ : syracuseStep 3137413 = 588265) (by norm_num)
theorem B3137501 : Blo 1857630 3137501 := bbase (se 3 (by rfl) ⟨588281, by rfl⟩ : syracuseStep 3137501 = 1176563) (by norm_num)
theorem B2351101 : Blo 1857630 2351101 := bbase (se 3 (by rfl) ⟨440831, by rfl⟩ : syracuseStep 2351101 = 881663) (by norm_num)
theorem B1859587 : Blo 1857630 1859587 := bstep (se 1 (by rfl) ⟨1394690, by rfl⟩ : syracuseStep 1859587 = 2789381) B2789381
theorem B3137555 : Blo 1857630 3137555 := bstep (se 1 (by rfl) ⟨2353166, by rfl⟩ : syracuseStep 3137555 = 4706333) B4706333
theorem B1859603 : Blo 1857630 1859603 := bstep (se 1 (by rfl) ⟨1394702, by rfl⟩ : syracuseStep 1859603 = 2789405) B2789405
theorem B1859619 : Blo 1857630 1859619 := bstep (se 1 (by rfl) ⟨1394714, by rfl⟩ : syracuseStep 1859619 = 2789429) B2789429
theorem B2646065 : Blo 1857630 2646065 := bstep (se 2 (by rfl) ⟨992274, by rfl⟩ : syracuseStep 2646065 = 1984549) B1984549
theorem B9412685 : Blo 1857630 9412685 := bstep (se 3 (by rfl) ⟨1764878, by rfl⟩ : syracuseStep 9412685 = 3529757) B3529757
theorem B7053425 : Blo 1857630 7053425 := bstep (se 2 (by rfl) ⟨2645034, by rfl⟩ : syracuseStep 7053425 = 5290069) B5290069
theorem B5955697 : Blo 1857630 5955697 := bstep (se 2 (by rfl) ⟨2233386, by rfl⟩ : syracuseStep 5955697 = 4466773) B4466773
theorem B2646145 : Blo 1857630 2646145 := bstep (se 2 (by rfl) ⟨992304, by rfl⟩ : syracuseStep 2646145 = 1984609) B1984609
theorem B3137683 : Blo 1857630 3137683 := bstep (se 1 (by rfl) ⟨2353262, by rfl⟩ : syracuseStep 3137683 = 4706525) B4706525
theorem B3178673 : Blo 1857630 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B6037681 : Blo 1857630 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B22610117 : Blo 1857630 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B3350737 : Blo 1857630 3350737 := bstep (se 2 (by rfl) ⟨1256526, by rfl⟩ : syracuseStep 3350737 = 2513053) B2513053
theorem B3178721 : Blo 1857630 3178721 := bstep (se 2 (by rfl) ⟨1192020, by rfl⟩ : syracuseStep 3178721 = 2384041) B2384041
theorem B15876323 : Blo 1857630 15876323 := bstep (se 1 (by rfl) ⟨11907242, by rfl⟩ : syracuseStep 15876323 = 23814485) B23814485
theorem B3350801 : Blo 1857630 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B3137825 : Blo 1857630 3137825 := bstep (se 2 (by rfl) ⟨1176684, by rfl⟩ : syracuseStep 3137825 = 2353369) B2353369
theorem B3137953 : Blo 1857630 3137953 := bstep (se 2 (by rfl) ⟨1176732, by rfl⟩ : syracuseStep 3137953 = 2353465) B2353465
theorem B6275501 : Blo 1857630 6275501 := bstep (se 3 (by rfl) ⟨1176656, by rfl⟩ : syracuseStep 6275501 = 2353313) B2353313
theorem B1884595 : Blo 1857630 1884595 := bstep (se 1 (by rfl) ⟨1413446, by rfl⟩ : syracuseStep 1884595 = 2826893) B2826893
theorem B3137987 : Blo 1857630 3137987 := bstep (se 1 (by rfl) ⟨2353490, by rfl⟩ : syracuseStep 3137987 = 4706981) B4706981
theorem B2351587 : Blo 1857630 2351587 := bstep (se 1 (by rfl) ⟨1763690, by rfl⟩ : syracuseStep 2351587 = 3527381) B3527381
theorem B6275555 : Blo 1857630 6275555 := bstep (se 1 (by rfl) ⟨4706666, by rfl⟩ : syracuseStep 6275555 = 9413333) B9413333
theorem B14107121 : Blo 1857630 14107121 := bstep (se 2 (by rfl) ⟨5290170, by rfl⟩ : syracuseStep 14107121 = 10580341) B10580341
theorem B4702769 : Blo 1857630 4702769 := bstep (se 2 (by rfl) ⟨1763538, by rfl⟩ : syracuseStep 4702769 = 3527077) B3527077
theorem B3351089 : Blo 1857630 3351089 := bstep (se 2 (by rfl) ⟨1256658, by rfl⟩ : syracuseStep 3351089 = 2513317) B2513317
theorem B2351683 : Blo 1857630 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B3138115 : Blo 1857630 3138115 := bstep (se 1 (by rfl) ⟨2353586, by rfl⟩ : syracuseStep 3138115 = 4707173) B4707173
theorem B4702819 : Blo 1857630 4702819 := bstep (se 1 (by rfl) ⟨3527114, by rfl⟩ : syracuseStep 4702819 = 7054229) B7054229
theorem B2826947 : Blo 1857630 2826947 := bstep (se 1 (by rfl) ⟨2120210, by rfl⟩ : syracuseStep 2826947 = 4240421) B4240421
theorem B4702961 : Blo 1857630 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B6275825 : Blo 1857630 6275825 := bstep (se 2 (by rfl) ⟨2353434, by rfl⟩ : syracuseStep 6275825 = 4706869) B4706869
theorem B5292803 : Blo 1857630 5292803 := bstep (se 1 (by rfl) ⟨3969602, by rfl⟩ : syracuseStep 5292803 = 7939205) B7939205
theorem B2827043 : Blo 1857630 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B9405233 : Blo 1857630 9405233 := bstep (se 2 (by rfl) ⟨3526962, by rfl⟩ : syracuseStep 9405233 = 7053925) B7053925
theorem B2646931 : Blo 1857630 2646931 := bstep (se 1 (by rfl) ⟨1985198, by rfl⟩ : syracuseStep 2646931 = 3970397) B3970397
theorem B2089939 : Blo 1857630 2089939 := bstep (se 1 (by rfl) ⟨1567454, by rfl⟩ : syracuseStep 2089939 = 3134909) B3134909
theorem B4465649 : Blo 1857630 4465649 := bstep (se 2 (by rfl) ⟨1674618, by rfl⟩ : syracuseStep 4465649 = 3349237) B3349237
theorem B3179521 : Blo 1857630 3179521 := bstep (se 2 (by rfl) ⟨1192320, by rfl⟩ : syracuseStep 3179521 = 2384641) B2384641
theorem B2352179 : Blo 1857630 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B5293133 : Blo 1857630 5293133 := bstep (se 3 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 5293133 = 1984925) B1984925
theorem B2090083 : Blo 1857630 2090083 := bstep (se 1 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 2090083 = 3135125) B3135125
theorem B6358115 : Blo 1857630 6358115 := bstep (se 1 (by rfl) ⟨4768586, by rfl⟩ : syracuseStep 6358115 = 9537173) B9537173
theorem B5293201 : Blo 1857630 5293201 := bstep (se 2 (by rfl) ⟨1984950, by rfl⟩ : syracuseStep 5293201 = 3969901) B3969901
theorem B2786465 : Blo 1857630 2786465 := bstep (se 2 (by rfl) ⟨1044924, by rfl⟩ : syracuseStep 2786465 = 2089849) B2089849
theorem B2786483 : Blo 1857630 2786483 := bstep (se 1 (by rfl) ⟨2089862, by rfl⟩ : syracuseStep 2786483 = 4179725) B4179725
theorem B2786513 : Blo 1857630 2786513 := bstep (se 2 (by rfl) ⟨1044942, by rfl⟩ : syracuseStep 2786513 = 2089885) B2089885
theorem B2786531 : Blo 1857630 2786531 := bstep (se 1 (by rfl) ⟨2089898, by rfl⟩ : syracuseStep 2786531 = 4179797) B4179797
theorem B2090227 : Blo 1857630 2090227 := bstep (se 1 (by rfl) ⟨1567670, by rfl⟩ : syracuseStep 2090227 = 3135341) B3135341
theorem B2786561 : Blo 1857630 2786561 := bstep (se 2 (by rfl) ⟨1044960, by rfl⟩ : syracuseStep 2786561 = 2089921) B2089921
theorem B2786579 : Blo 1857630 2786579 := bstep (se 1 (by rfl) ⟨2089934, by rfl⟩ : syracuseStep 2786579 = 4179869) B4179869
theorem B5653795 : Blo 1857630 5653795 := bstep (se 1 (by rfl) ⟨4240346, by rfl⟩ : syracuseStep 5653795 = 8480693) B8480693
theorem B2786609 : Blo 1857630 2786609 := bstep (se 2 (by rfl) ⟨1044978, by rfl⟩ : syracuseStep 2786609 = 2089957) B2089957
theorem B2786627 : Blo 1857630 2786627 := bstep (se 1 (by rfl) ⟨2089970, by rfl⟩ : syracuseStep 2786627 = 4179941) B4179941
theorem B2786657 : Blo 1857630 2786657 := bstep (se 2 (by rfl) ⟨1044996, by rfl⟩ : syracuseStep 2786657 = 2089993) B2089993
theorem B2786675 : Blo 1857630 2786675 := bstep (se 1 (by rfl) ⟨2090006, by rfl⟩ : syracuseStep 2786675 = 4180013) B4180013
theorem B2647409 : Blo 1857630 2647409 := bstep (se 2 (by rfl) ⟨992778, by rfl⟩ : syracuseStep 2647409 = 1985557) B1985557
theorem B2090371 : Blo 1857630 2090371 := bstep (se 1 (by rfl) ⟨1567778, by rfl⟩ : syracuseStep 2090371 = 3135557) B3135557
theorem B2786705 : Blo 1857630 2786705 := bstep (se 2 (by rfl) ⟨1045014, by rfl⟩ : syracuseStep 2786705 = 2090029) B2090029
theorem B2786723 : Blo 1857630 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B5293475 : Blo 1857630 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B2786753 : Blo 1857630 2786753 := bstep (se 2 (by rfl) ⟨1045032, by rfl⟩ : syracuseStep 2786753 = 2090065) B2090065
theorem B2786771 : Blo 1857630 2786771 := bstep (se 1 (by rfl) ⟨2090078, by rfl⟩ : syracuseStep 2786771 = 4180157) B4180157
theorem B2647523 : Blo 1857630 2647523 := bstep (se 1 (by rfl) ⟨1985642, by rfl⟩ : syracuseStep 2647523 = 3971285) B3971285
theorem B2786801 : Blo 1857630 2786801 := bstep (se 2 (by rfl) ⟨1045050, by rfl⟩ : syracuseStep 2786801 = 2090101) B2090101
theorem B2786819 : Blo 1857630 2786819 := bstep (se 1 (by rfl) ⟨2090114, by rfl⟩ : syracuseStep 2786819 = 4180229) B4180229
theorem B1984019 : Blo 1857630 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B2090515 : Blo 1857630 2090515 := bstep (se 1 (by rfl) ⟨1567886, by rfl⟩ : syracuseStep 2090515 = 3135773) B3135773
theorem B2786849 : Blo 1857630 2786849 := bstep (se 2 (by rfl) ⟨1045068, by rfl⟩ : syracuseStep 2786849 = 2090137) B2090137
theorem B7054883 : Blo 1857630 7054883 := bstep (se 1 (by rfl) ⟨5291162, by rfl⟩ : syracuseStep 7054883 = 10582325) B10582325
theorem B7054897 : Blo 1857630 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B2786867 : Blo 1857630 2786867 := bstep (se 1 (by rfl) ⟨2090150, by rfl⟩ : syracuseStep 2786867 = 4180301) B4180301
theorem B2647603 : Blo 1857630 2647603 := bstep (se 1 (by rfl) ⟨1985702, by rfl⟩ : syracuseStep 2647603 = 3971405) B3971405
theorem B2786897 : Blo 1857630 2786897 := bstep (se 2 (by rfl) ⟨1045086, by rfl⟩ : syracuseStep 2786897 = 2090173) B2090173
theorem B2786915 : Blo 1857630 2786915 := bstep (se 1 (by rfl) ⟨2090186, by rfl⟩ : syracuseStep 2786915 = 4180373) B4180373
theorem B13575779 : Blo 1857630 13575779 := bstep (se 1 (by rfl) ⟨10181834, by rfl⟩ : syracuseStep 13575779 = 20363669) B20363669
theorem B2786945 : Blo 1857630 2786945 := bstep (se 2 (by rfl) ⟨1045104, by rfl⟩ : syracuseStep 2786945 = 2090209) B2090209
theorem B2786963 : Blo 1857630 2786963 := bstep (se 1 (by rfl) ⟨2090222, by rfl⟩ : syracuseStep 2786963 = 4180445) B4180445
theorem B2090659 : Blo 1857630 2090659 := bstep (se 1 (by rfl) ⟨1567994, by rfl⟩ : syracuseStep 2090659 = 3135989) B3135989
theorem B2786993 : Blo 1857630 2786993 := bstep (se 2 (by rfl) ⟨1045122, by rfl⟩ : syracuseStep 2786993 = 2090245) B2090245
theorem B2787011 : Blo 1857630 2787011 := bstep (se 1 (by rfl) ⟨2090258, by rfl⟩ : syracuseStep 2787011 = 4180517) B4180517
theorem B4703953 : Blo 1857630 4703953 := bstep (se 2 (by rfl) ⟨1763982, by rfl⟩ : syracuseStep 4703953 = 3527965) B3527965
theorem B2787041 : Blo 1857630 2787041 := bstep (se 2 (by rfl) ⟨1045140, by rfl⟩ : syracuseStep 2787041 = 2090281) B2090281
theorem B4835057 : Blo 1857630 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B2787059 : Blo 1857630 2787059 := bstep (se 1 (by rfl) ⟨2090294, by rfl⟩ : syracuseStep 2787059 = 4180589) B4180589
theorem B2352883 : Blo 1857630 2352883 := bstep (se 1 (by rfl) ⟨1764662, by rfl⟩ : syracuseStep 2352883 = 3529325) B3529325
theorem B2787089 : Blo 1857630 2787089 := bstep (se 2 (by rfl) ⟨1045158, by rfl⟩ : syracuseStep 2787089 = 2090317) B2090317
theorem B2787107 : Blo 1857630 2787107 := bstep (se 1 (by rfl) ⟨2090330, by rfl⟩ : syracuseStep 2787107 = 4180661) B4180661
theorem B4179761 : Blo 1857630 4179761 := bstep (se 2 (by rfl) ⟨1567410, by rfl⟩ : syracuseStep 4179761 = 3134821) B3134821
theorem B7939889 : Blo 1857630 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B2090803 : Blo 1857630 2090803 := bstep (se 1 (by rfl) ⟨1568102, by rfl⟩ : syracuseStep 2090803 = 3136205) B3136205
theorem B2787137 : Blo 1857630 2787137 := bstep (se 2 (by rfl) ⟨1045176, by rfl⟩ : syracuseStep 2787137 = 2090353) B2090353
theorem B4179779 : Blo 1857630 4179779 := bstep (se 1 (by rfl) ⟨3134834, by rfl⟩ : syracuseStep 4179779 = 6269669) B6269669
theorem B2787155 : Blo 1857630 2787155 := bstep (se 1 (by rfl) ⟨2090366, by rfl⟩ : syracuseStep 2787155 = 4180733) B4180733
theorem B2352979 : Blo 1857630 2352979 := bstep (se 1 (by rfl) ⟨1764734, by rfl⟩ : syracuseStep 2352979 = 3529469) B3529469
theorem B2787185 : Blo 1857630 2787185 := bstep (se 2 (by rfl) ⟨1045194, by rfl⟩ : syracuseStep 2787185 = 2090389) B2090389
theorem B2787203 : Blo 1857630 2787203 := bstep (se 1 (by rfl) ⟨2090402, by rfl⟩ : syracuseStep 2787203 = 4180805) B4180805
theorem B2787233 : Blo 1857630 2787233 := bstep (se 2 (by rfl) ⟨1045212, by rfl⟩ : syracuseStep 2787233 = 2090425) B2090425
theorem B2787251 : Blo 1857630 2787251 := bstep (se 1 (by rfl) ⟨2090438, by rfl⟩ : syracuseStep 2787251 = 4180877) B4180877
theorem B2090947 : Blo 1857630 2090947 := bstep (se 1 (by rfl) ⟨1568210, by rfl⟩ : syracuseStep 2090947 = 3136421) B3136421
theorem B2787281 : Blo 1857630 2787281 := bstep (se 2 (by rfl) ⟨1045230, by rfl⟩ : syracuseStep 2787281 = 2090461) B2090461
theorem B2787299 : Blo 1857630 2787299 := bstep (se 1 (by rfl) ⟨2090474, by rfl⟩ : syracuseStep 2787299 = 4180949) B4180949
theorem B4704227 : Blo 1857630 4704227 := bstep (se 1 (by rfl) ⟨3528170, by rfl⟩ : syracuseStep 4704227 = 7056341) B7056341
theorem B2787329 : Blo 1857630 2787329 := bstep (se 2 (by rfl) ⟨1045248, by rfl⟩ : syracuseStep 2787329 = 2090497) B2090497
theorem B15869965 : Blo 1857630 15869965 := bstep (se 3 (by rfl) ⟨2975618, by rfl⟩ : syracuseStep 15869965 = 5951237) B5951237
theorem B2787347 : Blo 1857630 2787347 := bstep (se 1 (by rfl) ⟨2090510, by rfl⟩ : syracuseStep 2787347 = 4181021) B4181021
theorem B2787377 : Blo 1857630 2787377 := bstep (se 2 (by rfl) ⟨1045266, by rfl⟩ : syracuseStep 2787377 = 2090533) B2090533
theorem B2787395 : Blo 1857630 2787395 := bstep (se 1 (by rfl) ⟨2090546, by rfl⟩ : syracuseStep 2787395 = 4181093) B4181093
theorem B4180049 : Blo 1857630 4180049 := bstep (se 2 (by rfl) ⟨1567518, by rfl⟩ : syracuseStep 4180049 = 3135037) B3135037
theorem B2091091 : Blo 1857630 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B2787425 : Blo 1857630 2787425 := bstep (se 2 (by rfl) ⟨1045284, by rfl⟩ : syracuseStep 2787425 = 2090569) B2090569
theorem B4180067 : Blo 1857630 4180067 := bstep (se 1 (by rfl) ⟨3135050, by rfl⟩ : syracuseStep 4180067 = 6270101) B6270101
theorem B22612067 : Blo 1857630 22612067 := bstep (se 1 (by rfl) ⟨16959050, by rfl⟩ : syracuseStep 22612067 = 33918101) B33918101
theorem B2787443 : Blo 1857630 2787443 := bstep (se 1 (by rfl) ⟨2090582, by rfl⟩ : syracuseStep 2787443 = 4181165) B4181165
theorem B12069005 : Blo 1857630 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B2787473 : Blo 1857630 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B2787491 : Blo 1857630 2787491 := bstep (se 1 (by rfl) ⟨2090618, by rfl⟩ : syracuseStep 2787491 = 4181237) B4181237
theorem B4704419 : Blo 1857630 4704419 := bstep (se 1 (by rfl) ⟨3528314, by rfl⟩ : syracuseStep 4704419 = 7056629) B7056629
theorem B2787521 : Blo 1857630 2787521 := bstep (se 2 (by rfl) ⟨1045320, by rfl⟩ : syracuseStep 2787521 = 2090641) B2090641
theorem B2787539 : Blo 1857630 2787539 := bstep (se 1 (by rfl) ⟨2090654, by rfl⟩ : syracuseStep 2787539 = 4181309) B4181309
theorem B9406691 : Blo 1857630 9406691 := bstep (se 1 (by rfl) ⟨7055018, by rfl⟩ : syracuseStep 9406691 = 14110037) B14110037
theorem B2091235 : Blo 1857630 2091235 := bstep (se 1 (by rfl) ⟨1568426, by rfl⟩ : syracuseStep 2091235 = 3136853) B3136853
theorem B5294317 : Blo 1857630 5294317 := bstep (se 3 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 5294317 = 1985369) B1985369
theorem B2787569 : Blo 1857630 2787569 := bstep (se 2 (by rfl) ⟨1045338, by rfl⟩ : syracuseStep 2787569 = 2090677) B2090677
theorem B2787587 : Blo 1857630 2787587 := bstep (se 1 (by rfl) ⟨2090690, by rfl⟩ : syracuseStep 2787587 = 4181381) B4181381
theorem B1984771 : Blo 1857630 1984771 := bstep (se 1 (by rfl) ⟨1488578, by rfl⟩ : syracuseStep 1984771 = 2977157) B2977157
theorem B2787617 : Blo 1857630 2787617 := bstep (se 2 (by rfl) ⟨1045356, by rfl⟩ : syracuseStep 2787617 = 2090713) B2090713
theorem B2787635 : Blo 1857630 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B2353475 : Blo 1857630 2353475 := bstep (se 1 (by rfl) ⟨1765106, by rfl⟩ : syracuseStep 2353475 = 3530213) B3530213
theorem B2787665 : Blo 1857630 2787665 := bstep (se 2 (by rfl) ⟨1045374, by rfl⟩ : syracuseStep 2787665 = 2090749) B2090749
theorem B2787683 : Blo 1857630 2787683 := bstep (se 1 (by rfl) ⟨2090762, by rfl⟩ : syracuseStep 2787683 = 4181525) B4181525
theorem B2754929 : Blo 1857630 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B4180337 : Blo 1857630 4180337 := bstep (se 2 (by rfl) ⟨1567626, by rfl⟩ : syracuseStep 4180337 = 3135253) B3135253
theorem B2091379 : Blo 1857630 2091379 := bstep (se 1 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 2091379 = 3137069) B3137069
theorem B2787713 : Blo 1857630 2787713 := bstep (se 2 (by rfl) ⟨1045392, by rfl⟩ : syracuseStep 2787713 = 2090785) B2090785
theorem B4180355 : Blo 1857630 4180355 := bstep (se 1 (by rfl) ⟨3135266, by rfl⟩ : syracuseStep 4180355 = 6270533) B6270533
theorem B5294477 : Blo 1857630 5294477 := bstep (se 3 (by rfl) ⟨992714, by rfl⟩ : syracuseStep 5294477 = 1985429) B1985429
theorem B2787731 : Blo 1857630 2787731 := bstep (se 1 (by rfl) ⟨2090798, by rfl⟩ : syracuseStep 2787731 = 4181597) B4181597
theorem B2787761 : Blo 1857630 2787761 := bstep (se 2 (by rfl) ⟨1045410, by rfl⟩ : syracuseStep 2787761 = 2090821) B2090821
theorem B2787779 : Blo 1857630 2787779 := bstep (se 1 (by rfl) ⟨2090834, by rfl⟩ : syracuseStep 2787779 = 4181669) B4181669
theorem B2787809 : Blo 1857630 2787809 := bstep (se 2 (by rfl) ⟨1045428, by rfl⟩ : syracuseStep 2787809 = 2090857) B2090857
theorem B2787827 : Blo 1857630 2787827 := bstep (se 1 (by rfl) ⟨2090870, by rfl⟩ : syracuseStep 2787827 = 4181741) B4181741
theorem B2091523 : Blo 1857630 2091523 := bstep (se 1 (by rfl) ⟨1568642, by rfl⟩ : syracuseStep 2091523 = 3137285) B3137285
theorem B2787857 : Blo 1857630 2787857 := bstep (se 2 (by rfl) ⟨1045446, by rfl⟩ : syracuseStep 2787857 = 2090893) B2090893
theorem B2787875 : Blo 1857630 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B2787905 : Blo 1857630 2787905 := bstep (se 2 (by rfl) ⟨1045464, by rfl⟩ : syracuseStep 2787905 = 2090929) B2090929
theorem B6269507 : Blo 1857630 6269507 := bstep (se 1 (by rfl) ⟨4702130, by rfl⟩ : syracuseStep 6269507 = 9404261) B9404261
theorem B5294659 : Blo 1857630 5294659 := bstep (se 1 (by rfl) ⟨3970994, by rfl⟩ : syracuseStep 5294659 = 7941989) B7941989
theorem B2787923 : Blo 1857630 2787923 := bstep (se 1 (by rfl) ⟨2090942, by rfl⟩ : syracuseStep 2787923 = 4181885) B4181885
theorem B2787953 : Blo 1857630 2787953 := bstep (se 2 (by rfl) ⟨1045482, by rfl⟩ : syracuseStep 2787953 = 2090965) B2090965
theorem B2787971 : Blo 1857630 2787971 := bstep (se 1 (by rfl) ⟨2090978, by rfl⟩ : syracuseStep 2787971 = 4181957) B4181957
theorem B4180625 : Blo 1857630 4180625 := bstep (se 2 (by rfl) ⟨1567734, by rfl⟩ : syracuseStep 4180625 = 3135469) B3135469
theorem B2976401 : Blo 1857630 2976401 := bstep (se 2 (by rfl) ⟨1116150, by rfl⟩ : syracuseStep 2976401 = 2232301) B2232301
theorem B2091667 : Blo 1857630 2091667 := bstep (se 1 (by rfl) ⟨1568750, by rfl⟩ : syracuseStep 2091667 = 3137501) B3137501
theorem B2788001 : Blo 1857630 2788001 := bstep (se 2 (by rfl) ⟨1045500, by rfl⟩ : syracuseStep 2788001 = 2091001) B2091001
theorem B4180643 : Blo 1857630 4180643 := bstep (se 1 (by rfl) ⟨3135482, by rfl⟩ : syracuseStep 4180643 = 6270965) B6270965
theorem B2788019 : Blo 1857630 2788019 := bstep (se 1 (by rfl) ⟨2091014, by rfl⟩ : syracuseStep 2788019 = 4182029) B4182029
theorem B3967697 : Blo 1857630 3967697 := bstep (se 2 (by rfl) ⟨1487886, by rfl⟩ : syracuseStep 3967697 = 2975773) B2975773
theorem B2788049 : Blo 1857630 2788049 := bstep (se 2 (by rfl) ⟨1045518, by rfl⟩ : syracuseStep 2788049 = 2091037) B2091037
theorem B2788067 : Blo 1857630 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B67840739 : Blo 1857630 67840739 := bstep (se 1 (by rfl) ⟨50880554, by rfl⟩ : syracuseStep 67840739 = 101761109) B101761109
theorem B2788097 : Blo 1857630 2788097 := bstep (se 2 (by rfl) ⟨1045536, by rfl⟩ : syracuseStep 2788097 = 2091073) B2091073
theorem B2788115 : Blo 1857630 2788115 := bstep (se 1 (by rfl) ⟨2091086, by rfl⟩ : syracuseStep 2788115 = 4182173) B4182173
theorem B2091811 : Blo 1857630 2091811 := bstep (se 1 (by rfl) ⟨1568858, by rfl⟩ : syracuseStep 2091811 = 3137717) B3137717
theorem B2788145 : Blo 1857630 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B2788163 : Blo 1857630 2788163 := bstep (se 1 (by rfl) ⟨2091122, by rfl⟩ : syracuseStep 2788163 = 4182245) B4182245
theorem B6269777 : Blo 1857630 6269777 := bstep (se 2 (by rfl) ⟨2351166, by rfl⟩ : syracuseStep 6269777 = 4702333) B4702333
theorem B2788193 : Blo 1857630 2788193 := bstep (se 2 (by rfl) ⟨1045572, by rfl⟩ : syracuseStep 2788193 = 2091145) B2091145
theorem B2788211 : Blo 1857630 2788211 := bstep (se 1 (by rfl) ⟨2091158, by rfl⟩ : syracuseStep 2788211 = 4182317) B4182317
theorem B4025219 : Blo 1857630 4025219 := bstep (se 1 (by rfl) ⟨3018914, by rfl⟩ : syracuseStep 4025219 = 6037829) B6037829
theorem B2788241 : Blo 1857630 2788241 := bstep (se 2 (by rfl) ⟨1045590, by rfl⟩ : syracuseStep 2788241 = 2091181) B2091181
theorem B2788259 : Blo 1857630 2788259 := bstep (se 1 (by rfl) ⟨2091194, by rfl⟩ : syracuseStep 2788259 = 4182389) B4182389
theorem B4180913 : Blo 1857630 4180913 := bstep (se 2 (by rfl) ⟨1567842, by rfl⟩ : syracuseStep 4180913 = 3135685) B3135685
theorem B2091955 : Blo 1857630 2091955 := bstep (se 1 (by rfl) ⟨1568966, by rfl⟩ : syracuseStep 2091955 = 3137933) B3137933
theorem B2788289 : Blo 1857630 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B4180931 : Blo 1857630 4180931 := bstep (se 1 (by rfl) ⟨3135698, by rfl⟩ : syracuseStep 4180931 = 6271397) B6271397
theorem B2788307 : Blo 1857630 2788307 := bstep (se 1 (by rfl) ⟨2091230, by rfl⟩ : syracuseStep 2788307 = 4182461) B4182461
theorem B7056355 : Blo 1857630 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B2788337 : Blo 1857630 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B2788355 : Blo 1857630 2788355 := bstep (se 1 (by rfl) ⟨2091266, by rfl⟩ : syracuseStep 2788355 = 4182533) B4182533
theorem B9407501 : Blo 1857630 9407501 := bstep (se 3 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 9407501 = 3527813) B3527813
theorem B2788385 : Blo 1857630 2788385 := bstep (se 2 (by rfl) ⟨1045644, by rfl⟩ : syracuseStep 2788385 = 2091289) B2091289
theorem B2788403 : Blo 1857630 2788403 := bstep (se 1 (by rfl) ⟨2091302, by rfl⟩ : syracuseStep 2788403 = 4182605) B4182605
theorem B4705361 : Blo 1857630 4705361 := bstep (se 2 (by rfl) ⟨1764510, by rfl⟩ : syracuseStep 4705361 = 3529021) B3529021
theorem B2788433 : Blo 1857630 2788433 := bstep (se 2 (by rfl) ⟨1045662, by rfl⟩ : syracuseStep 2788433 = 2091325) B2091325
theorem B3968099 : Blo 1857630 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B12717155 : Blo 1857630 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B2788451 : Blo 1857630 2788451 := bstep (se 1 (by rfl) ⟨2091338, by rfl⟩ : syracuseStep 2788451 = 4182677) B4182677
theorem B4467811 : Blo 1857630 4467811 := bstep (se 1 (by rfl) ⟨3350858, by rfl⟩ : syracuseStep 4467811 = 6701717) B6701717
theorem B2788481 : Blo 1857630 2788481 := bstep (se 2 (by rfl) ⟨1045680, by rfl⟩ : syracuseStep 2788481 = 2091361) B2091361
theorem B4705411 : Blo 1857630 4705411 := bstep (se 1 (by rfl) ⟨3529058, by rfl⟩ : syracuseStep 4705411 = 7058117) B7058117
theorem B2788499 : Blo 1857630 2788499 := bstep (se 1 (by rfl) ⟨2091374, by rfl⟩ : syracuseStep 2788499 = 4182749) B4182749
theorem B2788529 : Blo 1857630 2788529 := bstep (se 2 (by rfl) ⟨1045698, by rfl⟩ : syracuseStep 2788529 = 2091397) B2091397
theorem B2788547 : Blo 1857630 2788547 := bstep (se 1 (by rfl) ⟨2091410, by rfl⟩ : syracuseStep 2788547 = 4182821) B4182821
theorem B4181201 : Blo 1857630 4181201 := bstep (se 2 (by rfl) ⟨1567950, by rfl⟩ : syracuseStep 4181201 = 3135901) B3135901
theorem B2788577 : Blo 1857630 2788577 := bstep (se 2 (by rfl) ⟨1045716, by rfl⟩ : syracuseStep 2788577 = 2091433) B2091433
theorem B4181219 : Blo 1857630 4181219 := bstep (se 1 (by rfl) ⟨3135914, by rfl⟩ : syracuseStep 4181219 = 6271829) B6271829
theorem B2788595 : Blo 1857630 2788595 := bstep (se 1 (by rfl) ⟨2091446, by rfl⟩ : syracuseStep 2788595 = 4182893) B4182893
theorem B1985779 : Blo 1857630 1985779 := bstep (se 1 (by rfl) ⟨1489334, by rfl⟩ : syracuseStep 1985779 = 2978669) B2978669
theorem B12717317 : Blo 1857630 12717317 := bstep (se 4 (by rfl) ⟨1192248, by rfl⟩ : syracuseStep 12717317 = 2384497) B2384497
theorem B4705553 : Blo 1857630 4705553 := bstep (se 2 (by rfl) ⟨1764582, by rfl⟩ : syracuseStep 4705553 = 3529165) B3529165
theorem B2788625 : Blo 1857630 2788625 := bstep (se 2 (by rfl) ⟨1045734, by rfl⟩ : syracuseStep 2788625 = 2091469) B2091469
theorem B2788643 : Blo 1857630 2788643 := bstep (se 1 (by rfl) ⟨2091482, by rfl⟩ : syracuseStep 2788643 = 4182965) B4182965
theorem B2788673 : Blo 1857630 2788673 := bstep (se 2 (by rfl) ⟨1045752, by rfl⟩ : syracuseStep 2788673 = 2091505) B2091505
theorem B15871301 : Blo 1857630 15871301 := bstep (se 4 (by rfl) ⟨1487934, by rfl⟩ : syracuseStep 15871301 = 2975869) B2975869
theorem B2788691 : Blo 1857630 2788691 := bstep (se 1 (by rfl) ⟨2091518, by rfl⟩ : syracuseStep 2788691 = 4183037) B4183037
theorem B11300195 : Blo 1857630 11300195 := bstep (se 1 (by rfl) ⟨8475146, by rfl⟩ : syracuseStep 11300195 = 16950293) B16950293
theorem B6270317 : Blo 1857630 6270317 := bstep (se 3 (by rfl) ⟨1175684, by rfl⟩ : syracuseStep 6270317 = 2351369) B2351369
theorem B2788721 : Blo 1857630 2788721 := bstep (se 2 (by rfl) ⟨1045770, by rfl⟩ : syracuseStep 2788721 = 2091541) B2091541
theorem B2788739 : Blo 1857630 2788739 := bstep (se 1 (by rfl) ⟨2091554, by rfl⟩ : syracuseStep 2788739 = 4183109) B4183109
theorem B2788769 : Blo 1857630 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B6270371 : Blo 1857630 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B2788787 : Blo 1857630 2788787 := bstep (se 1 (by rfl) ⟨2091590, by rfl⟩ : syracuseStep 2788787 = 4183181) B4183181
theorem B2788817 : Blo 1857630 2788817 := bstep (se 2 (by rfl) ⟨1045806, by rfl⟩ : syracuseStep 2788817 = 2091613) B2091613
theorem B2788835 : Blo 1857630 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B4181489 : Blo 1857630 4181489 := bstep (se 2 (by rfl) ⟨1568058, by rfl⟩ : syracuseStep 4181489 = 3136117) B3136117
theorem B2788865 : Blo 1857630 2788865 := bstep (se 2 (by rfl) ⟨1045824, by rfl⟩ : syracuseStep 2788865 = 2091649) B2091649
theorem B4181507 : Blo 1857630 4181507 := bstep (se 1 (by rfl) ⟨3136130, by rfl⟩ : syracuseStep 4181507 = 6272261) B6272261
theorem B2788883 : Blo 1857630 2788883 := bstep (se 1 (by rfl) ⟨2091662, by rfl⟩ : syracuseStep 2788883 = 4183325) B4183325
theorem B2788913 : Blo 1857630 2788913 := bstep (se 2 (by rfl) ⟨1045842, by rfl⟩ : syracuseStep 2788913 = 2091685) B2091685
theorem B4902449 : Blo 1857630 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B2788931 : Blo 1857630 2788931 := bstep (se 1 (by rfl) ⟨2091698, by rfl⟩ : syracuseStep 2788931 = 4183397) B4183397
theorem B2788961 : Blo 1857630 2788961 := bstep (se 2 (by rfl) ⟨1045860, by rfl⟩ : syracuseStep 2788961 = 2091721) B2091721
theorem B2788979 : Blo 1857630 2788979 := bstep (se 1 (by rfl) ⟨2091734, by rfl⟩ : syracuseStep 2788979 = 4183469) B4183469
theorem B2789009 : Blo 1857630 2789009 := bstep (se 2 (by rfl) ⟨1045878, by rfl⟩ : syracuseStep 2789009 = 2091757) B2091757
theorem B2789027 : Blo 1857630 2789027 := bstep (se 1 (by rfl) ⟨2091770, by rfl⟩ : syracuseStep 2789027 = 4183541) B4183541
theorem B6270641 : Blo 1857630 6270641 := bstep (se 2 (by rfl) ⟨2351490, by rfl⟩ : syracuseStep 6270641 = 4702981) B4702981
theorem B2789057 : Blo 1857630 2789057 := bstep (se 2 (by rfl) ⟨1045896, by rfl⟩ : syracuseStep 2789057 = 2091793) B2091793
theorem B2789075 : Blo 1857630 2789075 := bstep (se 1 (by rfl) ⟨2091806, by rfl⟩ : syracuseStep 2789075 = 4183613) B4183613
theorem B26783459 : Blo 1857630 26783459 := bstep (se 1 (by rfl) ⟨20087594, by rfl⟩ : syracuseStep 26783459 = 40175189) B40175189
theorem B2789105 : Blo 1857630 2789105 := bstep (se 2 (by rfl) ⟨1045914, by rfl⟩ : syracuseStep 2789105 = 2091829) B2091829
theorem B2789123 : Blo 1857630 2789123 := bstep (se 1 (by rfl) ⟨2091842, by rfl⟩ : syracuseStep 2789123 = 4183685) B4183685
theorem B4181777 : Blo 1857630 4181777 := bstep (se 2 (by rfl) ⟨1568166, by rfl⟩ : syracuseStep 4181777 = 3136333) B3136333
theorem B2789153 : Blo 1857630 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B4181795 : Blo 1857630 4181795 := bstep (se 1 (by rfl) ⟨3136346, by rfl⟩ : syracuseStep 4181795 = 6272693) B6272693
theorem B2789171 : Blo 1857630 2789171 := bstep (se 1 (by rfl) ⟨2091878, by rfl⟩ : syracuseStep 2789171 = 4183757) B4183757
theorem B2789201 : Blo 1857630 2789201 := bstep (se 2 (by rfl) ⟨1045950, by rfl⟩ : syracuseStep 2789201 = 2091901) B2091901
theorem B2789219 : Blo 1857630 2789219 := bstep (se 1 (by rfl) ⟨2091914, by rfl⟩ : syracuseStep 2789219 = 4183829) B4183829
theorem B15880049 : Blo 1857630 15880049 := bstep (se 2 (by rfl) ⟨5955018, by rfl⟩ : syracuseStep 15880049 = 11910037) B11910037
theorem B2789249 : Blo 1857630 2789249 := bstep (se 2 (by rfl) ⟨1045968, by rfl⟩ : syracuseStep 2789249 = 2091937) B2091937
theorem B2789267 : Blo 1857630 2789267 := bstep (se 1 (by rfl) ⟨2091950, by rfl⟩ : syracuseStep 2789267 = 4183901) B4183901
theorem B2789297 : Blo 1857630 2789297 := bstep (se 2 (by rfl) ⟨1045986, by rfl⟩ : syracuseStep 2789297 = 2091973) B2091973
theorem B2977715 : Blo 1857630 2977715 := bstep (se 1 (by rfl) ⟨2233286, by rfl⟩ : syracuseStep 2977715 = 4466573) B4466573
theorem B2789315 : Blo 1857630 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B13397957 : Blo 1857630 13397957 := bstep (se 4 (by rfl) ⟨1256058, by rfl⟩ : syracuseStep 13397957 = 2512117) B2512117
theorem B67858373 : Blo 1857630 67858373 := bstep (se 4 (by rfl) ⟨6361722, by rfl⟩ : syracuseStep 67858373 = 12723445) B12723445
theorem B2789345 : Blo 1857630 2789345 := bstep (se 2 (by rfl) ⟨1046004, by rfl⟩ : syracuseStep 2789345 = 2092009) B2092009
theorem B6696931 : Blo 1857630 6696931 := bstep (se 1 (by rfl) ⟨5022698, by rfl⟩ : syracuseStep 6696931 = 10045397) B10045397
theorem B3968995 : Blo 1857630 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B10047473 : Blo 1857630 10047473 := bstep (se 2 (by rfl) ⟨3767802, by rfl⟩ : syracuseStep 10047473 = 7535605) B7535605
theorem B2789363 : Blo 1857630 2789363 := bstep (se 1 (by rfl) ⟨2092022, by rfl⟩ : syracuseStep 2789363 = 4184045) B4184045
theorem B2789393 : Blo 1857630 2789393 := bstep (se 2 (by rfl) ⟨1046022, by rfl⟩ : syracuseStep 2789393 = 2092045) B2092045
theorem B2789411 : Blo 1857630 2789411 := bstep (se 1 (by rfl) ⟨2092058, by rfl⟩ : syracuseStep 2789411 = 4184117) B4184117
theorem B4182065 : Blo 1857630 4182065 := bstep (se 2 (by rfl) ⟨1568274, by rfl⟩ : syracuseStep 4182065 = 3136549) B3136549
theorem B2789441 : Blo 1857630 2789441 := bstep (se 2 (by rfl) ⟨1046040, by rfl⟩ : syracuseStep 2789441 = 2092081) B2092081
theorem B4182083 : Blo 1857630 4182083 := bstep (se 1 (by rfl) ⟨3136562, by rfl⟩ : syracuseStep 4182083 = 6273125) B6273125
theorem B5091491 : Blo 1857630 5091491 := bstep (se 1 (by rfl) ⟨3818618, by rfl⟩ : syracuseStep 5091491 = 7637237) B7637237
theorem B6271181 : Blo 1857630 6271181 := bstep (se 3 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 6271181 = 2351693) B2351693
theorem B23818481 : Blo 1857630 23818481 := bstep (se 2 (by rfl) ⟨8931930, by rfl⟩ : syracuseStep 23818481 = 17863861) B17863861
theorem B4706545 : Blo 1857630 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B6271235 : Blo 1857630 6271235 := bstep (se 1 (by rfl) ⟨4703426, by rfl⟩ : syracuseStep 6271235 = 9406853) B9406853
theorem B17854789 : Blo 1857630 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B3526993 : Blo 1857630 3526993 := bstep (se 2 (by rfl) ⟨1322622, by rfl⟩ : syracuseStep 3526993 = 2645245) B2645245
theorem B4182353 : Blo 1857630 4182353 := bstep (se 2 (by rfl) ⟨1568382, by rfl⟩ : syracuseStep 4182353 = 3136765) B3136765
theorem B4182371 : Blo 1857630 4182371 := bstep (se 1 (by rfl) ⟨3136778, by rfl⟩ : syracuseStep 4182371 = 6273557) B6273557
theorem B2232787 : Blo 1857630 2232787 := bstep (se 1 (by rfl) ⟨1674590, by rfl⟩ : syracuseStep 2232787 = 3349181) B3349181
theorem B5951981 : Blo 1857630 5951981 := bstep (se 3 (by rfl) ⟨1115996, by rfl⟩ : syracuseStep 5951981 = 2231993) B2231993
theorem B4706819 : Blo 1857630 4706819 := bstep (se 1 (by rfl) ⟨3530114, by rfl⟩ : syracuseStep 4706819 = 7060229) B7060229
theorem B6271505 : Blo 1857630 6271505 := bstep (se 2 (by rfl) ⟨2351814, by rfl⟩ : syracuseStep 6271505 = 4703629) B4703629
theorem B2511409 : Blo 1857630 2511409 := bstep (se 2 (by rfl) ⟨941778, by rfl⟩ : syracuseStep 2511409 = 1883557) B1883557
theorem B2978387 : Blo 1857630 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B4182641 : Blo 1857630 4182641 := bstep (se 2 (by rfl) ⟨1568490, by rfl⟩ : syracuseStep 4182641 = 3136981) B3136981
theorem B4182659 : Blo 1857630 4182659 := bstep (se 1 (by rfl) ⟨3136994, by rfl⟩ : syracuseStep 4182659 = 6273989) B6273989
theorem B4707011 : Blo 1857630 4707011 := bstep (se 1 (by rfl) ⟨3530258, by rfl⟩ : syracuseStep 4707011 = 7060517) B7060517
theorem B4133603 : Blo 1857630 4133603 := bstep (se 1 (by rfl) ⟨3100202, by rfl⟩ : syracuseStep 4133603 = 6200405) B6200405
theorem B61092629 : Blo 1857630 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B2978689 : Blo 1857630 2978689 := bstep (se 2 (by rfl) ⟨1117008, by rfl⟩ : syracuseStep 2978689 = 2234017) B2234017
theorem B4182929 : Blo 1857630 4182929 := bstep (se 2 (by rfl) ⟨1568598, by rfl⟩ : syracuseStep 4182929 = 3137197) B3137197
theorem B4240273 : Blo 1857630 4240273 := bstep (se 2 (by rfl) ⟨1590102, by rfl⟩ : syracuseStep 4240273 = 3180205) B3180205
theorem B4182947 : Blo 1857630 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B6272045 : Blo 1857630 6272045 := bstep (se 3 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 6272045 = 2352017) B2352017
theorem B6272099 : Blo 1857630 6272099 := bstep (se 1 (by rfl) ⟨4704074, by rfl⟩ : syracuseStep 6272099 = 9408149) B9408149
theorem B7058573 : Blo 1857630 7058573 := bstep (se 3 (by rfl) ⟨1323482, by rfl⟩ : syracuseStep 7058573 = 2646965) B2646965
theorem B3970225 : Blo 1857630 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B4183217 : Blo 1857630 4183217 := bstep (se 2 (by rfl) ⟨1568706, by rfl⟩ : syracuseStep 4183217 = 3137413) B3137413
theorem B4183235 : Blo 1857630 4183235 := bstep (se 1 (by rfl) ⟨3137426, by rfl⟩ : syracuseStep 4183235 = 6274853) B6274853
theorem B11908421 : Blo 1857630 11908421 := bstep (se 4 (by rfl) ⟨1116414, by rfl⟩ : syracuseStep 11908421 = 2232829) B2232829
theorem B3134801 : Blo 1857630 3134801 := bstep (se 2 (by rfl) ⟨1175550, by rfl⟩ : syracuseStep 3134801 = 2351101) B2351101
theorem B2544977 : Blo 1857630 2544977 := bstep (se 2 (by rfl) ⟨954366, by rfl⟩ : syracuseStep 2544977 = 1908733) B1908733
theorem B3528049 : Blo 1857630 3528049 := bstep (se 2 (by rfl) ⟨1323018, by rfl⟩ : syracuseStep 3528049 = 2646037) B2646037
theorem B6272369 : Blo 1857630 6272369 := bstep (se 2 (by rfl) ⟨2352138, by rfl⟩ : syracuseStep 6272369 = 4704277) B4704277
theorem B23811509 : Blo 1857630 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B3134929 : Blo 1857630 3134929 := bstep (se 2 (by rfl) ⟨1175598, by rfl⟩ : syracuseStep 3134929 = 2351197) B2351197
theorem B4183505 : Blo 1857630 4183505 := bstep (se 2 (by rfl) ⟨1568814, by rfl⟩ : syracuseStep 4183505 = 3137629) B3137629
theorem B4183523 : Blo 1857630 4183523 := bstep (se 1 (by rfl) ⟨3137642, by rfl⟩ : syracuseStep 4183523 = 6275285) B6275285
theorem B3134963 : Blo 1857630 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B24483397 : Blo 1857630 24483397 := bstep (se 4 (by rfl) ⟨2295318, by rfl⟩ : syracuseStep 24483397 = 4590637) B4590637
theorem B10581617 : Blo 1857630 10581617 := bstep (se 2 (by rfl) ⟨3968106, by rfl⟩ : syracuseStep 10581617 = 7936213) B7936213
theorem B33904241 : Blo 1857630 33904241 := bstep (se 2 (by rfl) ⟨12714090, by rfl⟩ : syracuseStep 33904241 = 25428181) B25428181
theorem B3135091 : Blo 1857630 3135091 := bstep (se 1 (by rfl) ⟨2351318, by rfl⟩ : syracuseStep 3135091 = 4702637) B4702637
theorem B12719729 : Blo 1857630 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B2512625 : Blo 1857630 2512625 := bstep (se 2 (by rfl) ⟨942234, by rfl⟩ : syracuseStep 2512625 = 1884469) B1884469
theorem B4183793 : Blo 1857630 4183793 := bstep (se 2 (by rfl) ⟨1568922, by rfl⟩ : syracuseStep 4183793 = 3137845) B3137845
theorem B3135233 : Blo 1857630 3135233 := bstep (se 2 (by rfl) ⟨1175712, by rfl⟩ : syracuseStep 3135233 = 2351425) B2351425
theorem B3528451 : Blo 1857630 3528451 := bstep (se 1 (by rfl) ⟨2646338, by rfl⟩ : syracuseStep 3528451 = 5292677) B5292677
theorem B4183811 : Blo 1857630 4183811 := bstep (se 1 (by rfl) ⟨3137858, by rfl⟩ : syracuseStep 4183811 = 6275717) B6275717
theorem B67811093 : Blo 1857630 67811093 := bstep (se 6 (by rfl) ⟨1589322, by rfl⟩ : syracuseStep 67811093 = 3178645) B3178645
theorem B3528497 : Blo 1857630 3528497 := bstep (se 2 (by rfl) ⟨1323186, by rfl⟩ : syracuseStep 3528497 = 2646373) B2646373
theorem B2512723 : Blo 1857630 2512723 := bstep (se 1 (by rfl) ⟨1884542, by rfl⟩ : syracuseStep 2512723 = 3769085) B3769085
theorem B9410417 : Blo 1857630 9410417 := bstep (se 2 (by rfl) ⟨3528906, by rfl⟩ : syracuseStep 9410417 = 7057813) B7057813
theorem B3135361 : Blo 1857630 3135361 := bstep (se 2 (by rfl) ⟨1175760, by rfl⟩ : syracuseStep 3135361 = 2351521) B2351521
theorem B6272909 : Blo 1857630 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B3135395 : Blo 1857630 3135395 := bstep (se 1 (by rfl) ⟨2351546, by rfl⟩ : syracuseStep 3135395 = 4703093) B4703093
theorem B3536803 : Blo 1857630 3536803 := bstep (se 1 (by rfl) ⟨2652602, by rfl⟩ : syracuseStep 3536803 = 5305205) B5305205
theorem B6272963 : Blo 1857630 6272963 := bstep (se 1 (by rfl) ⟨4704722, by rfl⟩ : syracuseStep 6272963 = 9409445) B9409445
theorem B13760525 : Blo 1857630 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B4184081 : Blo 1857630 4184081 := bstep (se 2 (by rfl) ⟨1569030, by rfl⟩ : syracuseStep 4184081 = 3138061) B3138061
theorem B3135523 : Blo 1857630 3135523 := bstep (se 1 (by rfl) ⟨2351642, by rfl⟩ : syracuseStep 3135523 = 4703285) B4703285
theorem B4184099 : Blo 1857630 4184099 := bstep (se 1 (by rfl) ⟨3138074, by rfl⟩ : syracuseStep 4184099 = 6276149) B6276149
theorem B3528785 : Blo 1857630 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B1857635 : Blo 1857630 1857635 := bstep (se 1 (by rfl) ⟨1393226, by rfl⟩ : syracuseStep 1857635 = 2786453) B2786453
theorem B1857651 : Blo 1857630 1857651 := bstep (se 1 (by rfl) ⟨1393238, by rfl⟩ : syracuseStep 1857651 = 2786477) B2786477
theorem B1857667 : Blo 1857630 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B1857683 : Blo 1857630 1857683 := bstep (se 1 (by rfl) ⟨1393262, by rfl⟩ : syracuseStep 1857683 = 2786525) B2786525
theorem B2717843 : Blo 1857630 2717843 := bstep (se 1 (by rfl) ⟨2038382, by rfl⟩ : syracuseStep 2717843 = 4076765) B4076765
theorem B1857699 : Blo 1857630 1857699 := bstep (se 1 (by rfl) ⟨1393274, by rfl⟩ : syracuseStep 1857699 = 2786549) B2786549
theorem B5093549 : Blo 1857630 5093549 := bstep (se 3 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 5093549 = 1910081) B1910081
theorem B3135665 : Blo 1857630 3135665 := bstep (se 2 (by rfl) ⟨1175874, by rfl⟩ : syracuseStep 3135665 = 2351749) B2351749
theorem B3578033 : Blo 1857630 3578033 := bstep (se 2 (by rfl) ⟨1341762, by rfl⟩ : syracuseStep 3578033 = 2683525) B2683525
theorem B1857715 : Blo 1857630 1857715 := bstep (se 1 (by rfl) ⟨1393286, by rfl⟩ : syracuseStep 1857715 = 2786573) B2786573
theorem B1857731 : Blo 1857630 1857731 := bstep (se 1 (by rfl) ⟨1393298, by rfl⟩ : syracuseStep 1857731 = 2786597) B2786597
theorem B6273233 : Blo 1857630 6273233 := bstep (se 2 (by rfl) ⟨2352462, by rfl⟩ : syracuseStep 6273233 = 4704925) B4704925
theorem B1857747 : Blo 1857630 1857747 := bstep (se 1 (by rfl) ⟨1393310, by rfl⟩ : syracuseStep 1857747 = 2786621) B2786621
theorem B1857763 : Blo 1857630 1857763 := bstep (se 1 (by rfl) ⟨1393322, by rfl⟩ : syracuseStep 1857763 = 2786645) B2786645
theorem B1857779 : Blo 1857630 1857779 := bstep (se 1 (by rfl) ⟨1393334, by rfl⟩ : syracuseStep 1857779 = 2786669) B2786669
theorem B1857795 : Blo 1857630 1857795 := bstep (se 1 (by rfl) ⟨1393346, by rfl⟩ : syracuseStep 1857795 = 2786693) B2786693
theorem B1857811 : Blo 1857630 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B1857827 : Blo 1857630 1857827 := bstep (se 1 (by rfl) ⟨1393370, by rfl⟩ : syracuseStep 1857827 = 2786741) B2786741
theorem B5290285 : Blo 1857630 5290285 := bstep (se 3 (by rfl) ⟨991928, by rfl⟩ : syracuseStep 5290285 = 1983857) B1983857
theorem B3135793 : Blo 1857630 3135793 := bstep (se 2 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 3135793 = 2351845) B2351845
theorem B1857843 : Blo 1857630 1857843 := bstep (se 1 (by rfl) ⟨1393382, by rfl⟩ : syracuseStep 1857843 = 2786765) B2786765
theorem B1857859 : Blo 1857630 1857859 := bstep (se 1 (by rfl) ⟨1393394, by rfl⟩ : syracuseStep 1857859 = 2786789) B2786789
theorem B1857875 : Blo 1857630 1857875 := bstep (se 1 (by rfl) ⟨1393406, by rfl⟩ : syracuseStep 1857875 = 2786813) B2786813
theorem B3135827 : Blo 1857630 3135827 := bstep (se 1 (by rfl) ⟨2351870, by rfl⟩ : syracuseStep 3135827 = 4703741) B4703741
theorem B1857891 : Blo 1857630 1857891 := bstep (se 1 (by rfl) ⟨1393418, by rfl⟩ : syracuseStep 1857891 = 2786837) B2786837
theorem B1857907 : Blo 1857630 1857907 := bstep (se 1 (by rfl) ⟨1393430, by rfl⟩ : syracuseStep 1857907 = 2786861) B2786861
theorem B1857923 : Blo 1857630 1857923 := bstep (se 1 (by rfl) ⟨1393442, by rfl⟩ : syracuseStep 1857923 = 2786885) B2786885
theorem B1857939 : Blo 1857630 1857939 := bstep (se 1 (by rfl) ⟨1393454, by rfl⟩ : syracuseStep 1857939 = 2786909) B2786909
theorem B1857955 : Blo 1857630 1857955 := bstep (se 1 (by rfl) ⟨1393466, by rfl⟩ : syracuseStep 1857955 = 2786933) B2786933
theorem B1857971 : Blo 1857630 1857971 := bstep (se 1 (by rfl) ⟨1393478, by rfl⟩ : syracuseStep 1857971 = 2786957) B2786957
theorem B1857987 : Blo 1857630 1857987 := bstep (se 1 (by rfl) ⟨1393490, by rfl⟩ : syracuseStep 1857987 = 2786981) B2786981
theorem B6699469 : Blo 1857630 6699469 := bstep (se 3 (by rfl) ⟨1256150, by rfl⟩ : syracuseStep 6699469 = 2512301) B2512301
theorem B1858003 : Blo 1857630 1858003 := bstep (se 1 (by rfl) ⟨1393502, by rfl⟩ : syracuseStep 1858003 = 2787005) B2787005
theorem B3135955 : Blo 1857630 3135955 := bstep (se 1 (by rfl) ⟨2351966, by rfl⟩ : syracuseStep 3135955 = 4703933) B4703933
theorem B1858019 : Blo 1857630 1858019 := bstep (se 1 (by rfl) ⟨1393514, by rfl⟩ : syracuseStep 1858019 = 2787029) B2787029
theorem B1858035 : Blo 1857630 1858035 := bstep (se 1 (by rfl) ⟨1393526, by rfl⟩ : syracuseStep 1858035 = 2787053) B2787053
theorem B1858051 : Blo 1857630 1858051 := bstep (se 1 (by rfl) ⟨1393538, by rfl⟩ : syracuseStep 1858051 = 2787077) B2787077
theorem B1858067 : Blo 1857630 1858067 := bstep (se 1 (by rfl) ⟨1393550, by rfl⟩ : syracuseStep 1858067 = 2787101) B2787101
theorem B8927779 : Blo 1857630 8927779 := bstep (se 1 (by rfl) ⟨6695834, by rfl⟩ : syracuseStep 8927779 = 13391669) B13391669
theorem B1858083 : Blo 1857630 1858083 := bstep (se 1 (by rfl) ⟨1393562, by rfl⟩ : syracuseStep 1858083 = 2787125) B2787125
theorem B1858099 : Blo 1857630 1858099 := bstep (se 1 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 1858099 = 2787149) B2787149
theorem B1858115 : Blo 1857630 1858115 := bstep (se 1 (by rfl) ⟨1393586, by rfl⟩ : syracuseStep 1858115 = 2787173) B2787173
theorem B11303501 : Blo 1857630 11303501 := bstep (se 3 (by rfl) ⟨2119406, by rfl⟩ : syracuseStep 11303501 = 4238813) B4238813
theorem B1858131 : Blo 1857630 1858131 := bstep (se 1 (by rfl) ⟨1393598, by rfl⟩ : syracuseStep 1858131 = 2787197) B2787197
theorem B3136097 : Blo 1857630 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B1858147 : Blo 1857630 1858147 := bstep (se 1 (by rfl) ⟨1393610, by rfl⟩ : syracuseStep 1858147 = 2787221) B2787221
theorem B1858163 : Blo 1857630 1858163 := bstep (se 1 (by rfl) ⟨1393622, by rfl⟩ : syracuseStep 1858163 = 2787245) B2787245
theorem B1858179 : Blo 1857630 1858179 := bstep (se 1 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 1858179 = 2787269) B2787269
theorem B1858195 : Blo 1857630 1858195 := bstep (se 1 (by rfl) ⟨1393646, by rfl⟩ : syracuseStep 1858195 = 2787293) B2787293
theorem B1858211 : Blo 1857630 1858211 := bstep (se 1 (by rfl) ⟨1393658, by rfl⟩ : syracuseStep 1858211 = 2787317) B2787317
theorem B1858227 : Blo 1857630 1858227 := bstep (se 1 (by rfl) ⟨1393670, by rfl⟩ : syracuseStep 1858227 = 2787341) B2787341
theorem B1858243 : Blo 1857630 1858243 := bstep (se 1 (by rfl) ⟨1393682, by rfl⟩ : syracuseStep 1858243 = 2787365) B2787365
theorem B1858259 : Blo 1857630 1858259 := bstep (se 1 (by rfl) ⟨1393694, by rfl⟩ : syracuseStep 1858259 = 2787389) B2787389
theorem B3136225 : Blo 1857630 3136225 := bstep (se 2 (by rfl) ⟨1176084, by rfl⟩ : syracuseStep 3136225 = 2352169) B2352169
theorem B1858275 : Blo 1857630 1858275 := bstep (se 1 (by rfl) ⟨1393706, by rfl⟩ : syracuseStep 1858275 = 2787413) B2787413
theorem B6273773 : Blo 1857630 6273773 := bstep (se 3 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 6273773 = 2352665) B2352665
theorem B1858291 : Blo 1857630 1858291 := bstep (se 1 (by rfl) ⟨1393718, by rfl⟩ : syracuseStep 1858291 = 2787437) B2787437
theorem B1858307 : Blo 1857630 1858307 := bstep (se 1 (by rfl) ⟨1393730, by rfl⟩ : syracuseStep 1858307 = 2787461) B2787461
theorem B3136259 : Blo 1857630 3136259 := bstep (se 1 (by rfl) ⟨2352194, by rfl⟩ : syracuseStep 3136259 = 4704389) B4704389
theorem B1858323 : Blo 1857630 1858323 := bstep (se 1 (by rfl) ⟨1393742, by rfl⟩ : syracuseStep 1858323 = 2787485) B2787485
theorem B1858339 : Blo 1857630 1858339 := bstep (se 1 (by rfl) ⟨1393754, by rfl⟩ : syracuseStep 1858339 = 2787509) B2787509
theorem B6273827 : Blo 1857630 6273827 := bstep (se 1 (by rfl) ⟨4705370, by rfl⟩ : syracuseStep 6273827 = 9410741) B9410741
theorem B3529507 : Blo 1857630 3529507 := bstep (se 1 (by rfl) ⟨2647130, by rfl⟩ : syracuseStep 3529507 = 5294261) B5294261
theorem B1858355 : Blo 1857630 1858355 := bstep (se 1 (by rfl) ⟨1393766, by rfl⟩ : syracuseStep 1858355 = 2787533) B2787533
theorem B1858371 : Blo 1857630 1858371 := bstep (se 1 (by rfl) ⟨1393778, by rfl⟩ : syracuseStep 1858371 = 2787557) B2787557
theorem B1858387 : Blo 1857630 1858387 := bstep (se 1 (by rfl) ⟨1393790, by rfl⟩ : syracuseStep 1858387 = 2787581) B2787581
theorem B1858403 : Blo 1857630 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B1858419 : Blo 1857630 1858419 := bstep (se 1 (by rfl) ⟨1393814, by rfl⟩ : syracuseStep 1858419 = 2787629) B2787629
theorem B1858435 : Blo 1857630 1858435 := bstep (se 1 (by rfl) ⟨1393826, by rfl⟩ : syracuseStep 1858435 = 2787653) B2787653
theorem B3136387 : Blo 1857630 3136387 := bstep (se 1 (by rfl) ⟨2352290, by rfl⟩ : syracuseStep 3136387 = 4704581) B4704581
theorem B1858451 : Blo 1857630 1858451 := bstep (se 1 (by rfl) ⟨1393838, by rfl⟩ : syracuseStep 1858451 = 2787677) B2787677
theorem B5651363 : Blo 1857630 5651363 := bstep (se 1 (by rfl) ⟨4238522, by rfl⟩ : syracuseStep 5651363 = 8477045) B8477045
theorem B1858467 : Blo 1857630 1858467 := bstep (se 1 (by rfl) ⟨1393850, by rfl⟩ : syracuseStep 1858467 = 2787701) B2787701
theorem B5954467 : Blo 1857630 5954467 := bstep (se 1 (by rfl) ⟨4465850, by rfl⟩ : syracuseStep 5954467 = 8931701) B8931701
theorem B1858483 : Blo 1857630 1858483 := bstep (se 1 (by rfl) ⟨1393862, by rfl⟩ : syracuseStep 1858483 = 2787725) B2787725
theorem B1858499 : Blo 1857630 1858499 := bstep (se 1 (by rfl) ⟨1393874, by rfl⟩ : syracuseStep 1858499 = 2787749) B2787749
theorem B1858515 : Blo 1857630 1858515 := bstep (se 1 (by rfl) ⟨1393886, by rfl⟩ : syracuseStep 1858515 = 2787773) B2787773
theorem B3767267 : Blo 1857630 3767267 := bstep (se 1 (by rfl) ⟨2825450, by rfl⟩ : syracuseStep 3767267 = 5650901) B5650901
theorem B1858531 : Blo 1857630 1858531 := bstep (se 1 (by rfl) ⟨1393898, by rfl⟩ : syracuseStep 1858531 = 2787797) B2787797
theorem B1858547 : Blo 1857630 1858547 := bstep (se 1 (by rfl) ⟨1393910, by rfl⟩ : syracuseStep 1858547 = 2787821) B2787821
theorem B1858563 : Blo 1857630 1858563 := bstep (se 1 (by rfl) ⟨1393922, by rfl⟩ : syracuseStep 1858563 = 2787845) B2787845
theorem B3136529 : Blo 1857630 3136529 := bstep (se 2 (by rfl) ⟨1176198, by rfl⟩ : syracuseStep 3136529 = 2352397) B2352397
theorem B1858579 : Blo 1857630 1858579 := bstep (se 1 (by rfl) ⟨1393934, by rfl⟩ : syracuseStep 1858579 = 2787869) B2787869
theorem B10583075 : Blo 1857630 10583075 := bstep (se 1 (by rfl) ⟨7937306, by rfl⟩ : syracuseStep 10583075 = 15874613) B15874613
theorem B1858595 : Blo 1857630 1858595 := bstep (se 1 (by rfl) ⟨1393946, by rfl⟩ : syracuseStep 1858595 = 2787893) B2787893
theorem B6036515 : Blo 1857630 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B5954609 : Blo 1857630 5954609 := bstep (se 2 (by rfl) ⟨2232978, by rfl⟩ : syracuseStep 5954609 = 4465957) B4465957
theorem B6274097 : Blo 1857630 6274097 := bstep (se 2 (by rfl) ⟨2352786, by rfl⟩ : syracuseStep 6274097 = 4705573) B4705573
theorem B1858611 : Blo 1857630 1858611 := bstep (se 1 (by rfl) ⟨1393958, by rfl⟩ : syracuseStep 1858611 = 2787917) B2787917
theorem B1858627 : Blo 1857630 1858627 := bstep (se 1 (by rfl) ⟨1393970, by rfl⟩ : syracuseStep 1858627 = 2787941) B2787941
theorem B1858643 : Blo 1857630 1858643 := bstep (se 1 (by rfl) ⟨1393982, by rfl⟩ : syracuseStep 1858643 = 2787965) B2787965
theorem B1858659 : Blo 1857630 1858659 := bstep (se 1 (by rfl) ⟨1393994, by rfl⟩ : syracuseStep 1858659 = 2787989) B2787989
theorem B1858675 : Blo 1857630 1858675 := bstep (se 1 (by rfl) ⟨1394006, by rfl⟩ : syracuseStep 1858675 = 2788013) B2788013
theorem B1858691 : Blo 1857630 1858691 := bstep (se 1 (by rfl) ⟨1394018, by rfl⟩ : syracuseStep 1858691 = 2788037) B2788037
theorem B3136657 : Blo 1857630 3136657 := bstep (se 2 (by rfl) ⟨1176246, by rfl⟩ : syracuseStep 3136657 = 2352493) B2352493
theorem B1858707 : Blo 1857630 1858707 := bstep (se 1 (by rfl) ⟨1394030, by rfl⟩ : syracuseStep 1858707 = 2788061) B2788061
theorem B1858723 : Blo 1857630 1858723 := bstep (se 1 (by rfl) ⟨1394042, by rfl⟩ : syracuseStep 1858723 = 2788085) B2788085
theorem B5954723 : Blo 1857630 5954723 := bstep (se 1 (by rfl) ⟨4466042, by rfl⟩ : syracuseStep 5954723 = 8932085) B8932085
theorem B1858739 : Blo 1857630 1858739 := bstep (se 1 (by rfl) ⟨1394054, by rfl⟩ : syracuseStep 1858739 = 2788109) B2788109
theorem B3136691 : Blo 1857630 3136691 := bstep (se 1 (by rfl) ⟨2352518, by rfl⟩ : syracuseStep 3136691 = 4705037) B4705037
theorem B1858755 : Blo 1857630 1858755 := bstep (se 1 (by rfl) ⟨1394066, by rfl⟩ : syracuseStep 1858755 = 2788133) B2788133
theorem B1858771 : Blo 1857630 1858771 := bstep (se 1 (by rfl) ⟨1394078, by rfl⟩ : syracuseStep 1858771 = 2788157) B2788157
theorem B1858787 : Blo 1857630 1858787 := bstep (se 1 (by rfl) ⟨1394090, by rfl⟩ : syracuseStep 1858787 = 2788181) B2788181
theorem B3529955 : Blo 1857630 3529955 := bstep (se 1 (by rfl) ⟨2647466, by rfl⟩ : syracuseStep 3529955 = 5294933) B5294933
theorem B1858803 : Blo 1857630 1858803 := bstep (se 1 (by rfl) ⟨1394102, by rfl⟩ : syracuseStep 1858803 = 2788205) B2788205
theorem B1858819 : Blo 1857630 1858819 := bstep (se 1 (by rfl) ⟨1394114, by rfl⟩ : syracuseStep 1858819 = 2788229) B2788229
theorem B3349763 : Blo 1857630 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B1858835 : Blo 1857630 1858835 := bstep (se 1 (by rfl) ⟨1394126, by rfl⟩ : syracuseStep 1858835 = 2788253) B2788253
theorem B1858851 : Blo 1857630 1858851 := bstep (se 1 (by rfl) ⟨1394138, by rfl⟩ : syracuseStep 1858851 = 2788277) B2788277
theorem B9411875 : Blo 1857630 9411875 := bstep (se 1 (by rfl) ⟨7058906, by rfl⟩ : syracuseStep 9411875 = 14117813) B14117813
theorem B3136819 : Blo 1857630 3136819 := bstep (se 1 (by rfl) ⟨2352614, by rfl⟩ : syracuseStep 3136819 = 4705229) B4705229
theorem B1858867 : Blo 1857630 1858867 := bstep (se 1 (by rfl) ⟨1394150, by rfl⟩ : syracuseStep 1858867 = 2788301) B2788301
theorem B1858883 : Blo 1857630 1858883 := bstep (se 1 (by rfl) ⟨1394162, by rfl⟩ : syracuseStep 1858883 = 2788325) B2788325
theorem B5291345 : Blo 1857630 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B1858899 : Blo 1857630 1858899 := bstep (se 1 (by rfl) ⟨1394174, by rfl⟩ : syracuseStep 1858899 = 2788349) B2788349
theorem B1858915 : Blo 1857630 1858915 := bstep (se 1 (by rfl) ⟨1394186, by rfl⟩ : syracuseStep 1858915 = 2788373) B2788373
theorem B8928625 : Blo 1857630 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1858931 : Blo 1857630 1858931 := bstep (se 1 (by rfl) ⟨1394198, by rfl⟩ : syracuseStep 1858931 = 2788397) B2788397
theorem B1858947 : Blo 1857630 1858947 := bstep (se 1 (by rfl) ⟨1394210, by rfl⟩ : syracuseStep 1858947 = 2788421) B2788421
theorem B1858963 : Blo 1857630 1858963 := bstep (se 1 (by rfl) ⟨1394222, by rfl⟩ : syracuseStep 1858963 = 2788445) B2788445
theorem B7937443 : Blo 1857630 7937443 := bstep (se 1 (by rfl) ⟨5953082, by rfl⟩ : syracuseStep 7937443 = 11906165) B11906165
theorem B1858979 : Blo 1857630 1858979 := bstep (se 1 (by rfl) ⟨1394234, by rfl⟩ : syracuseStep 1858979 = 2788469) B2788469
theorem B1858995 : Blo 1857630 1858995 := bstep (se 1 (by rfl) ⟨1394246, by rfl⟩ : syracuseStep 1858995 = 2788493) B2788493
theorem B3136961 : Blo 1857630 3136961 := bstep (se 2 (by rfl) ⟨1176360, by rfl⟩ : syracuseStep 3136961 = 2352721) B2352721
theorem B1859011 : Blo 1857630 1859011 := bstep (se 1 (by rfl) ⟨1394258, by rfl⟩ : syracuseStep 1859011 = 2788517) B2788517
theorem B1859027 : Blo 1857630 1859027 := bstep (se 1 (by rfl) ⟨1394270, by rfl⟩ : syracuseStep 1859027 = 2788541) B2788541
theorem B2645473 : Blo 1857630 2645473 := bstep (se 2 (by rfl) ⟨992052, by rfl⟩ : syracuseStep 2645473 = 1984105) B1984105
theorem B1859043 : Blo 1857630 1859043 := bstep (se 1 (by rfl) ⟨1394282, by rfl⟩ : syracuseStep 1859043 = 2788565) B2788565
theorem B1859059 : Blo 1857630 1859059 := bstep (se 1 (by rfl) ⟨1394294, by rfl⟩ : syracuseStep 1859059 = 2788589) B2788589
theorem B2645507 : Blo 1857630 2645507 := bstep (se 1 (by rfl) ⟨1984130, by rfl⟩ : syracuseStep 2645507 = 3968261) B3968261
theorem B1859075 : Blo 1857630 1859075 := bstep (se 1 (by rfl) ⟨1394306, by rfl⟩ : syracuseStep 1859075 = 2788613) B2788613
theorem B3530243 : Blo 1857630 3530243 := bstep (se 1 (by rfl) ⟨2647682, by rfl⟩ : syracuseStep 3530243 = 5295365) B5295365
theorem B1859091 : Blo 1857630 1859091 := bstep (se 1 (by rfl) ⟨1394318, by rfl⟩ : syracuseStep 1859091 = 2788637) B2788637
theorem B1859107 : Blo 1857630 1859107 := bstep (se 1 (by rfl) ⟨1394330, by rfl⟩ : syracuseStep 1859107 = 2788661) B2788661
theorem B2825779 : Blo 1857630 2825779 := bstep (se 1 (by rfl) ⟨2119334, by rfl⟩ : syracuseStep 2825779 = 4238669) B4238669
theorem B1859123 : Blo 1857630 1859123 := bstep (se 1 (by rfl) ⟨1394342, by rfl⟩ : syracuseStep 1859123 = 2788685) B2788685
theorem B3137089 : Blo 1857630 3137089 := bstep (se 2 (by rfl) ⟨1176408, by rfl⟩ : syracuseStep 3137089 = 2352817) B2352817
theorem B1859139 : Blo 1857630 1859139 := bstep (se 1 (by rfl) ⟨1394354, by rfl⟩ : syracuseStep 1859139 = 2788709) B2788709
theorem B6274637 : Blo 1857630 6274637 := bstep (se 3 (by rfl) ⟨1176494, by rfl⟩ : syracuseStep 6274637 = 2352989) B2352989
theorem B1859155 : Blo 1857630 1859155 := bstep (se 1 (by rfl) ⟨1394366, by rfl⟩ : syracuseStep 1859155 = 2788733) B2788733
theorem B3137123 : Blo 1857630 3137123 := bstep (se 1 (by rfl) ⟨2352842, by rfl⟩ : syracuseStep 3137123 = 4705685) B4705685
theorem B1859171 : Blo 1857630 1859171 := bstep (se 1 (by rfl) ⟨1394378, by rfl⟩ : syracuseStep 1859171 = 2788757) B2788757
theorem B5021293 : Blo 1857630 5021293 := bstep (se 3 (by rfl) ⟨941492, by rfl⟩ : syracuseStep 5021293 = 1882985) B1882985
theorem B1859187 : Blo 1857630 1859187 := bstep (se 1 (by rfl) ⟨1394390, by rfl⟩ : syracuseStep 1859187 = 2788781) B2788781
theorem B5021315 : Blo 1857630 5021315 := bstep (se 1 (by rfl) ⟨3765986, by rfl⟩ : syracuseStep 5021315 = 7531973) B7531973
theorem B6274691 : Blo 1857630 6274691 := bstep (se 1 (by rfl) ⟨4706018, by rfl⟩ : syracuseStep 6274691 = 9412037) B9412037
theorem B1859203 : Blo 1857630 1859203 := bstep (se 1 (by rfl) ⟨1394402, by rfl⟩ : syracuseStep 1859203 = 2788805) B2788805
theorem B1859219 : Blo 1857630 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B1859235 : Blo 1857630 1859235 := bstep (se 1 (by rfl) ⟨1394426, by rfl⟩ : syracuseStep 1859235 = 2788853) B2788853
theorem B1859251 : Blo 1857630 1859251 := bstep (se 1 (by rfl) ⟨1394438, by rfl⟩ : syracuseStep 1859251 = 2788877) B2788877
theorem B1859267 : Blo 1857630 1859267 := bstep (se 1 (by rfl) ⟨1394450, by rfl⟩ : syracuseStep 1859267 = 2788901) B2788901
theorem B1859283 : Blo 1857630 1859283 := bstep (se 1 (by rfl) ⟨1394462, by rfl⟩ : syracuseStep 1859283 = 2788925) B2788925
theorem B3137251 : Blo 1857630 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1859299 : Blo 1857630 1859299 := bstep (se 1 (by rfl) ⟨1394474, by rfl⟩ : syracuseStep 1859299 = 2788949) B2788949
theorem B35741411 : Blo 1857630 35741411 := bstep (se 1 (by rfl) ⟨26806058, by rfl⟩ : syracuseStep 35741411 = 53612117) B53612117
theorem B1859315 : Blo 1857630 1859315 := bstep (se 1 (by rfl) ⟨1394486, by rfl⟩ : syracuseStep 1859315 = 2788973) B2788973
theorem B1859331 : Blo 1857630 1859331 := bstep (se 1 (by rfl) ⟨1394498, by rfl⟩ : syracuseStep 1859331 = 2788997) B2788997
theorem B11902733 : Blo 1857630 11902733 := bstep (se 3 (by rfl) ⟨2231762, by rfl⟩ : syracuseStep 11902733 = 4463525) B4463525
theorem B10043149 : Blo 1857630 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B15884045 : Blo 1857630 15884045 := bstep (se 3 (by rfl) ⟨2978258, by rfl⟩ : syracuseStep 15884045 = 5956517) B5956517
theorem B1859347 : Blo 1857630 1859347 := bstep (se 1 (by rfl) ⟨1394510, by rfl⟩ : syracuseStep 1859347 = 2789021) B2789021
theorem B1859363 : Blo 1857630 1859363 := bstep (se 1 (by rfl) ⟨1394522, by rfl⟩ : syracuseStep 1859363 = 2789045) B2789045
theorem B1859379 : Blo 1857630 1859379 := bstep (se 1 (by rfl) ⟨1394534, by rfl⟩ : syracuseStep 1859379 = 2789069) B2789069
theorem B1859395 : Blo 1857630 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B1859411 : Blo 1857630 1859411 := bstep (se 1 (by rfl) ⟨1394558, by rfl⟩ : syracuseStep 1859411 = 2789117) B2789117
theorem B1859427 : Blo 1857630 1859427 := bstep (se 1 (by rfl) ⟨1394570, by rfl⟩ : syracuseStep 1859427 = 2789141) B2789141
theorem B3137393 : Blo 1857630 3137393 := bstep (se 2 (by rfl) ⟨1176522, by rfl⟩ : syracuseStep 3137393 = 2353045) B2353045
theorem B1859443 : Blo 1857630 1859443 := bstep (se 1 (by rfl) ⟨1394582, by rfl⟩ : syracuseStep 1859443 = 2789165) B2789165
theorem B1859459 : Blo 1857630 1859459 := bstep (se 1 (by rfl) ⟨1394594, by rfl⟩ : syracuseStep 1859459 = 2789189) B2789189
theorem B6274961 : Blo 1857630 6274961 := bstep (se 2 (by rfl) ⟨2353110, by rfl⟩ : syracuseStep 6274961 = 4706221) B4706221
theorem B1859475 : Blo 1857630 1859475 := bstep (se 1 (by rfl) ⟨1394606, by rfl⟩ : syracuseStep 1859475 = 2789213) B2789213
theorem B1859491 : Blo 1857630 1859491 := bstep (se 1 (by rfl) ⟨1394618, by rfl⟩ : syracuseStep 1859491 = 2789237) B2789237
theorem B1859507 : Blo 1857630 1859507 := bstep (se 1 (by rfl) ⟨1394630, by rfl⟩ : syracuseStep 1859507 = 2789261) B2789261
theorem B1859523 : Blo 1857630 1859523 := bstep (se 1 (by rfl) ⟨1394642, by rfl⟩ : syracuseStep 1859523 = 2789285) B2789285
theorem B1859539 : Blo 1857630 1859539 := bstep (se 1 (by rfl) ⟨1394654, by rfl⟩ : syracuseStep 1859539 = 2789309) B2789309
theorem B1859555 : Blo 1857630 1859555 := bstep (se 1 (by rfl) ⟨1394666, by rfl⟩ : syracuseStep 1859555 = 2789333) B2789333
theorem B5292017 : Blo 1857630 5292017 := bstep (se 2 (by rfl) ⟨1984506, by rfl⟩ : syracuseStep 5292017 = 3969013) B3969013
theorem B3137521 : Blo 1857630 3137521 := bstep (se 2 (by rfl) ⟨1176570, by rfl⟩ : syracuseStep 3137521 = 2353141) B2353141
theorem B1859571 : Blo 1857630 1859571 := bstep (se 1 (by rfl) ⟨1394678, by rfl⟩ : syracuseStep 1859571 = 2789357) B2789357
theorem B1859595 : Blo 1857630 1859595 := bstep (se 1 (by rfl) ⟨1394696, by rfl⟩ : syracuseStep 1859595 = 2789393) B2789393
theorem B21159953 : Blo 1857630 21159953 := bstep (se 2 (by rfl) ⟨7934982, by rfl⟩ : syracuseStep 21159953 = 15869965) B15869965
theorem B1859607 : Blo 1857630 1859607 := bstep (se 1 (by rfl) ⟨1394705, by rfl⟩ : syracuseStep 1859607 = 2789411) B2789411
theorem B1859627 : Blo 1857630 1859627 := bstep (se 1 (by rfl) ⟨1394720, by rfl⟩ : syracuseStep 1859627 = 2789441) B2789441
theorem B6275123 : Blo 1857630 6275123 := bstep (se 1 (by rfl) ⟨4706342, by rfl⟩ : syracuseStep 6275123 = 9412685) B9412685
theorem B4702283 : Blo 1857630 4702283 := bstep (se 1 (by rfl) ⟨3526712, by rfl⟩ : syracuseStep 4702283 = 7053425) B7053425
theorem B10584215 : Blo 1857630 10584215 := bstep (se 1 (by rfl) ⟨7938161, by rfl⟩ : syracuseStep 10584215 = 15876323) B15876323
theorem B6275393 : Blo 1857630 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B9404747 : Blo 1857630 9404747 := bstep (se 1 (by rfl) ⟨7053560, by rfl⟩ : syracuseStep 9404747 = 14107121) B14107121
theorem B3137879 : Blo 1857630 3137879 := bstep (se 1 (by rfl) ⟨2353409, by rfl⟩ : syracuseStep 3137879 = 4706819) B4706819
theorem B2646361 : Blo 1857630 2646361 := bstep (se 2 (by rfl) ⟨992385, by rfl⟩ : syracuseStep 2646361 = 1984771) B1984771
theorem B7053713 : Blo 1857630 7053713 := bstep (se 2 (by rfl) ⟨2645142, by rfl⟩ : syracuseStep 7053713 = 5290285) B5290285
theorem B23806385 : Blo 1857630 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B4702657 : Blo 1857630 4702657 := bstep (se 2 (by rfl) ⟨1763496, by rfl⟩ : syracuseStep 4702657 = 3526993) B3526993
theorem B1884631 : Blo 1857630 1884631 := bstep (se 1 (by rfl) ⟨1413473, by rfl⟩ : syracuseStep 1884631 = 2826947) B2826947
theorem B3138007 : Blo 1857630 3138007 := bstep (se 1 (by rfl) ⟨2353505, by rfl⟩ : syracuseStep 3138007 = 4707011) B4707011
theorem B60293645 : Blo 1857630 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B1859575 : Blo 1857630 1859575 := bstep (se 1 (by rfl) ⟨1394681, by rfl⟩ : syracuseStep 1859575 = 2789363) B2789363
theorem B11903705 : Blo 1857630 11903705 := bstep (se 2 (by rfl) ⟨4463889, by rfl⟩ : syracuseStep 11903705 = 8927779) B8927779
theorem B120570677 : Blo 1857630 120570677 := bstep (se 5 (by rfl) ⟨5651750, by rfl⟩ : syracuseStep 120570677 = 11303501) B11303501
theorem B6275933 : Blo 1857630 6275933 := bstep (se 3 (by rfl) ⟨1176737, by rfl⟩ : syracuseStep 6275933 = 2353475) B2353475
theorem B7938947 : Blo 1857630 7938947 := bstep (se 1 (by rfl) ⟨5954210, by rfl⟩ : syracuseStep 7938947 = 11908421) B11908421
theorem B2089867 : Blo 1857630 2089867 := bstep (se 1 (by rfl) ⟨1567400, by rfl⟩ : syracuseStep 2089867 = 3134801) B3134801
theorem B2089975 : Blo 1857630 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B128803861 : Blo 1857630 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B4703255 : Blo 1857630 4703255 := bstep (se 1 (by rfl) ⟨3527441, by rfl⟩ : syracuseStep 4703255 = 7054883) B7054883
theorem B7054411 : Blo 1857630 7054411 := bstep (se 1 (by rfl) ⟨5290808, by rfl⟩ : syracuseStep 7054411 = 10581617) B10581617
theorem B22602827 : Blo 1857630 22602827 := bstep (se 1 (by rfl) ⟨16952120, by rfl⟩ : syracuseStep 22602827 = 33904241) B33904241
theorem B8479819 : Blo 1857630 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B2090155 : Blo 1857630 2090155 := bstep (se 1 (by rfl) ⟨1567616, by rfl⟩ : syracuseStep 2090155 = 3135233) B3135233
theorem B5653697 : Blo 1857630 5653697 := bstep (se 2 (by rfl) ⟨2120136, by rfl⟩ : syracuseStep 5653697 = 4240273) B4240273
theorem B2786507 : Blo 1857630 2786507 := bstep (se 1 (by rfl) ⟨2089880, by rfl⟩ : syracuseStep 2786507 = 4179761) B4179761
theorem B2352331 : Blo 1857630 2352331 := bstep (se 1 (by rfl) ⟨1764248, by rfl⟩ : syracuseStep 2352331 = 3528497) B3528497
theorem B5293259 : Blo 1857630 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B2786519 : Blo 1857630 2786519 := bstep (se 1 (by rfl) ⟨2089889, by rfl⟩ : syracuseStep 2786519 = 4179779) B4179779
theorem B7939289 : Blo 1857630 7939289 := bstep (se 2 (by rfl) ⟨2977233, by rfl⟩ : syracuseStep 7939289 = 5954467) B5954467
theorem B2090263 : Blo 1857630 2090263 := bstep (se 1 (by rfl) ⟨1567697, by rfl⟩ : syracuseStep 2090263 = 3135395) B3135395
theorem B2786585 : Blo 1857630 2786585 := bstep (se 2 (by rfl) ⟨1044969, by rfl⟩ : syracuseStep 2786585 = 2089939) B2089939
theorem B7054685 : Blo 1857630 7054685 := bstep (se 3 (by rfl) ⟨1322753, by rfl⟩ : syracuseStep 7054685 = 2645507) B2645507
theorem B9413981 : Blo 1857630 9413981 := bstep (se 3 (by rfl) ⟨1765121, by rfl⟩ : syracuseStep 9413981 = 3530243) B3530243
theorem B2786699 : Blo 1857630 2786699 := bstep (se 1 (by rfl) ⟨2090024, by rfl⟩ : syracuseStep 2786699 = 4180049) B4180049
theorem B2786711 : Blo 1857630 2786711 := bstep (se 1 (by rfl) ⟨2090033, by rfl⟩ : syracuseStep 2786711 = 4180067) B4180067
theorem B15074711 : Blo 1857630 15074711 := bstep (se 1 (by rfl) ⟨11306033, by rfl⟩ : syracuseStep 15074711 = 22612067) B22612067
theorem B2090443 : Blo 1857630 2090443 := bstep (se 1 (by rfl) ⟨1567832, by rfl⟩ : syracuseStep 2090443 = 3135665) B3135665
theorem B2385355 : Blo 1857630 2385355 := bstep (se 1 (by rfl) ⟨1789016, by rfl⟩ : syracuseStep 2385355 = 3578033) B3578033
theorem B120620501 : Blo 1857630 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B2786777 : Blo 1857630 2786777 := bstep (se 2 (by rfl) ⟨1045041, by rfl⟩ : syracuseStep 2786777 = 2090083) B2090083
theorem B5957081 : Blo 1857630 5957081 := bstep (se 2 (by rfl) ⟨2233905, by rfl⟩ : syracuseStep 5957081 = 4467811) B4467811
theorem B2090551 : Blo 1857630 2090551 := bstep (se 1 (by rfl) ⟨1567913, by rfl⟩ : syracuseStep 2090551 = 3135827) B3135827
theorem B2786891 : Blo 1857630 2786891 := bstep (se 1 (by rfl) ⟨2090168, by rfl⟩ : syracuseStep 2786891 = 4180337) B4180337
theorem B2786903 : Blo 1857630 2786903 := bstep (se 1 (by rfl) ⟨2090177, by rfl⟩ : syracuseStep 2786903 = 4180355) B4180355
theorem B2786969 : Blo 1857630 2786969 := bstep (se 2 (by rfl) ⟨1045113, by rfl⟩ : syracuseStep 2786969 = 2090227) B2090227
theorem B4179671 : Blo 1857630 4179671 := bstep (se 1 (by rfl) ⟨3134753, by rfl⟩ : syracuseStep 4179671 = 6269507) B6269507
theorem B7538393 : Blo 1857630 7538393 := bstep (se 2 (by rfl) ⟨2826897, by rfl⟩ : syracuseStep 7538393 = 5653795) B5653795
theorem B2090731 : Blo 1857630 2090731 := bstep (se 1 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 2090731 = 3136097) B3136097
theorem B2787083 : Blo 1857630 2787083 := bstep (se 1 (by rfl) ⟨2090312, by rfl⟩ : syracuseStep 2787083 = 4180625) B4180625
theorem B1984267 : Blo 1857630 1984267 := bstep (se 1 (by rfl) ⟨1488200, by rfl⟩ : syracuseStep 1984267 = 2976401) B2976401
theorem B2787095 : Blo 1857630 2787095 := bstep (se 1 (by rfl) ⟨2090321, by rfl⟩ : syracuseStep 2787095 = 4180643) B4180643
theorem B11904833 : Blo 1857630 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B4704065 : Blo 1857630 4704065 := bstep (se 2 (by rfl) ⟨1764024, by rfl⟩ : syracuseStep 4704065 = 3528049) B3528049
theorem B2090839 : Blo 1857630 2090839 := bstep (se 1 (by rfl) ⟨1568129, by rfl⟩ : syracuseStep 2090839 = 3136259) B3136259
theorem B2787161 : Blo 1857630 2787161 := bstep (se 2 (by rfl) ⟨1045185, by rfl⟩ : syracuseStep 2787161 = 2090371) B2090371
theorem B4179851 : Blo 1857630 4179851 := bstep (se 1 (by rfl) ⟨3134888, by rfl⟩ : syracuseStep 4179851 = 6269777) B6269777
theorem B4179905 : Blo 1857630 4179905 := bstep (se 2 (by rfl) ⟨1567464, by rfl⟩ : syracuseStep 4179905 = 3134929) B3134929
theorem B2787275 : Blo 1857630 2787275 := bstep (se 1 (by rfl) ⟨2090456, by rfl⟩ : syracuseStep 2787275 = 4180913) B4180913
theorem B2787287 : Blo 1857630 2787287 := bstep (se 1 (by rfl) ⟨2090465, by rfl⟩ : syracuseStep 2787287 = 4180931) B4180931
theorem B2091019 : Blo 1857630 2091019 := bstep (se 1 (by rfl) ⟨1568264, by rfl⟩ : syracuseStep 2091019 = 3136529) B3136529
theorem B7055383 : Blo 1857630 7055383 := bstep (se 1 (by rfl) ⟨5291537, by rfl⟩ : syracuseStep 7055383 = 10583075) B10583075
theorem B4024343 : Blo 1857630 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2787353 : Blo 1857630 2787353 := bstep (se 2 (by rfl) ⟨1045257, by rfl⟩ : syracuseStep 2787353 = 2090515) B2090515
theorem B9406529 : Blo 1857630 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B2091127 : Blo 1857630 2091127 := bstep (se 1 (by rfl) ⟨1568345, by rfl⟩ : syracuseStep 2091127 = 3136691) B3136691
theorem B2787467 : Blo 1857630 2787467 := bstep (se 1 (by rfl) ⟨2090600, by rfl⟩ : syracuseStep 2787467 = 4181201) B4181201
theorem B6695057 : Blo 1857630 6695057 := bstep (se 2 (by rfl) ⟨2510646, by rfl⟩ : syracuseStep 6695057 = 5021293) B5021293
theorem B2787479 : Blo 1857630 2787479 := bstep (se 1 (by rfl) ⟨2090609, by rfl⟩ : syracuseStep 2787479 = 4181219) B4181219
theorem B2353303 : Blo 1857630 2353303 := bstep (se 1 (by rfl) ⟨1764977, by rfl⟩ : syracuseStep 2353303 = 3529955) B3529955
theorem B4180121 : Blo 1857630 4180121 := bstep (se 2 (by rfl) ⟨1567545, by rfl⟩ : syracuseStep 4180121 = 3135091) B3135091
theorem B2787545 : Blo 1857630 2787545 := bstep (se 2 (by rfl) ⟨1045329, by rfl⟩ : syracuseStep 2787545 = 2090659) B2090659
theorem B4180211 : Blo 1857630 4180211 := bstep (se 1 (by rfl) ⟨3135158, by rfl⟩ : syracuseStep 4180211 = 6270317) B6270317
theorem B4180247 : Blo 1857630 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B2091307 : Blo 1857630 2091307 := bstep (se 1 (by rfl) ⟨1568480, by rfl⟩ : syracuseStep 2091307 = 3136961) B3136961
theorem B2787659 : Blo 1857630 2787659 := bstep (se 1 (by rfl) ⟨2090744, by rfl⟩ : syracuseStep 2787659 = 4181489) B4181489
theorem B2787671 : Blo 1857630 2787671 := bstep (se 1 (by rfl) ⟨2090753, by rfl⟩ : syracuseStep 2787671 = 4181507) B4181507
theorem B4704601 : Blo 1857630 4704601 := bstep (se 2 (by rfl) ⟨1764225, by rfl⟩ : syracuseStep 4704601 = 3528451) B3528451
theorem B10733917 : Blo 1857630 10733917 := bstep (se 3 (by rfl) ⟨2012609, by rfl⟩ : syracuseStep 10733917 = 4025219) B4025219
theorem B2091415 : Blo 1857630 2091415 := bstep (se 1 (by rfl) ⟨1568561, by rfl⟩ : syracuseStep 2091415 = 3137123) B3137123
theorem B2787737 : Blo 1857630 2787737 := bstep (se 2 (by rfl) ⟨1045401, by rfl⟩ : syracuseStep 2787737 = 2090803) B2090803
theorem B4180427 : Blo 1857630 4180427 := bstep (se 1 (by rfl) ⟨3135320, by rfl⟩ : syracuseStep 4180427 = 6270641) B6270641
theorem B4180481 : Blo 1857630 4180481 := bstep (se 2 (by rfl) ⟨1567680, by rfl⟩ : syracuseStep 4180481 = 3135361) B3135361
theorem B2787851 : Blo 1857630 2787851 := bstep (se 1 (by rfl) ⟨2090888, by rfl⟩ : syracuseStep 2787851 = 4181777) B4181777
theorem B2787863 : Blo 1857630 2787863 := bstep (se 1 (by rfl) ⟨2090897, by rfl⟩ : syracuseStep 2787863 = 4181795) B4181795
theorem B10586699 : Blo 1857630 10586699 := bstep (se 1 (by rfl) ⟨7940024, by rfl⟩ : syracuseStep 10586699 = 15880049) B15880049
theorem B2091595 : Blo 1857630 2091595 := bstep (se 1 (by rfl) ⟨1568696, by rfl⟩ : syracuseStep 2091595 = 3137393) B3137393
theorem B2787929 : Blo 1857630 2787929 := bstep (se 2 (by rfl) ⟨1045473, by rfl⟩ : syracuseStep 2787929 = 2090947) B2090947
theorem B10046045 : Blo 1857630 10046045 := bstep (se 3 (by rfl) ⟨1883633, by rfl⟩ : syracuseStep 10046045 = 3767267) B3767267
theorem B1985143 : Blo 1857630 1985143 := bstep (se 1 (by rfl) ⟨1488857, by rfl⟩ : syracuseStep 1985143 = 2977715) B2977715
theorem B8931971 : Blo 1857630 8931971 := bstep (se 1 (by rfl) ⟨6698978, by rfl⟩ : syracuseStep 8931971 = 13397957) B13397957
theorem B45238915 : Blo 1857630 45238915 := bstep (se 1 (by rfl) ⟨33929186, by rfl⟩ : syracuseStep 45238915 = 67858373) B67858373
theorem B2091703 : Blo 1857630 2091703 := bstep (se 1 (by rfl) ⟨1568777, by rfl⟩ : syracuseStep 2091703 = 3137555) B3137555
theorem B2788043 : Blo 1857630 2788043 := bstep (se 1 (by rfl) ⟨2091032, by rfl⟩ : syracuseStep 2788043 = 4182065) B4182065
theorem B2788055 : Blo 1857630 2788055 := bstep (se 1 (by rfl) ⟨2091041, by rfl⟩ : syracuseStep 2788055 = 4182083) B4182083
theorem B4180697 : Blo 1857630 4180697 := bstep (se 2 (by rfl) ⟨1567761, by rfl⟩ : syracuseStep 4180697 = 3135523) B3135523
theorem B3394327 : Blo 1857630 3394327 := bstep (se 1 (by rfl) ⟨2545745, by rfl⟩ : syracuseStep 3394327 = 5091491) B5091491
theorem B2788121 : Blo 1857630 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B7056173 : Blo 1857630 7056173 := bstep (se 3 (by rfl) ⟨1323032, by rfl⟩ : syracuseStep 7056173 = 2646065) B2646065
theorem B4180787 : Blo 1857630 4180787 := bstep (se 1 (by rfl) ⟨3135590, by rfl⟩ : syracuseStep 4180787 = 6271181) B6271181
theorem B7940929 : Blo 1857630 7940929 := bstep (se 2 (by rfl) ⟨2977848, by rfl⟩ : syracuseStep 7940929 = 5955697) B5955697
theorem B15878987 : Blo 1857630 15878987 := bstep (se 1 (by rfl) ⟨11909240, by rfl⟩ : syracuseStep 15878987 = 23818481) B23818481
theorem B4180823 : Blo 1857630 4180823 := bstep (se 1 (by rfl) ⟨3135617, by rfl⟩ : syracuseStep 4180823 = 6271235) B6271235
theorem B2091883 : Blo 1857630 2091883 := bstep (se 1 (by rfl) ⟨1568912, by rfl⟩ : syracuseStep 2091883 = 3137825) B3137825
theorem B21162869 : Blo 1857630 21162869 := bstep (se 5 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 21162869 = 1984019) B1984019
theorem B2788235 : Blo 1857630 2788235 := bstep (se 1 (by rfl) ⟨2091176, by rfl⟩ : syracuseStep 2788235 = 4182353) B4182353
theorem B2788247 : Blo 1857630 2788247 := bstep (se 1 (by rfl) ⟨2091185, by rfl⟩ : syracuseStep 2788247 = 4182371) B4182371
theorem B4467649 : Blo 1857630 4467649 := bstep (se 2 (by rfl) ⟨1675368, by rfl⟩ : syracuseStep 4467649 = 3350737) B3350737
theorem B2091991 : Blo 1857630 2091991 := bstep (se 1 (by rfl) ⟨1568993, by rfl⟩ : syracuseStep 2091991 = 3137987) B3137987
theorem B2788313 : Blo 1857630 2788313 := bstep (se 2 (by rfl) ⟨1045617, by rfl⟩ : syracuseStep 2788313 = 2091235) B2091235
theorem B4181003 : Blo 1857630 4181003 := bstep (se 1 (by rfl) ⟨3135752, by rfl⟩ : syracuseStep 4181003 = 6271505) B6271505
theorem B1985591 : Blo 1857630 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B4181057 : Blo 1857630 4181057 := bstep (se 2 (by rfl) ⟨1567896, by rfl⟩ : syracuseStep 4181057 = 3135793) B3135793
theorem B2788427 : Blo 1857630 2788427 := bstep (se 1 (by rfl) ⟨2091320, by rfl⟩ : syracuseStep 2788427 = 4182641) B4182641
theorem B2788439 : Blo 1857630 2788439 := bstep (se 1 (by rfl) ⟨2091329, by rfl⟩ : syracuseStep 2788439 = 4182659) B4182659
theorem B2788505 : Blo 1857630 2788505 := bstep (se 2 (by rfl) ⟨1045689, by rfl⟩ : syracuseStep 2788505 = 2091379) B2091379
theorem B52292789 : Blo 1857630 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B6270155 : Blo 1857630 6270155 := bstep (se 1 (by rfl) ⟨4702616, by rfl⟩ : syracuseStep 6270155 = 9405233) B9405233
theorem B2788619 : Blo 1857630 2788619 := bstep (se 1 (by rfl) ⟨2091464, by rfl⟩ : syracuseStep 2788619 = 4182929) B4182929
theorem B8932625 : Blo 1857630 8932625 := bstep (se 2 (by rfl) ⟨3349734, by rfl⟩ : syracuseStep 8932625 = 6699469) B6699469
theorem B2788631 : Blo 1857630 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B4181273 : Blo 1857630 4181273 := bstep (se 2 (by rfl) ⟨1567977, by rfl⟩ : syracuseStep 4181273 = 3135955) B3135955
theorem B2977049 : Blo 1857630 2977049 := bstep (se 2 (by rfl) ⟨1116393, by rfl⟩ : syracuseStep 2977049 = 2232787) B2232787
theorem B2788697 : Blo 1857630 2788697 := bstep (se 2 (by rfl) ⟨1045761, by rfl⟩ : syracuseStep 2788697 = 2091523) B2091523
theorem B4181363 : Blo 1857630 4181363 := bstep (se 1 (by rfl) ⟨3136022, by rfl⟩ : syracuseStep 4181363 = 6272045) B6272045
theorem B4181399 : Blo 1857630 4181399 := bstep (se 1 (by rfl) ⟨3136049, by rfl⟩ : syracuseStep 4181399 = 6272099) B6272099
theorem B4238743 : Blo 1857630 4238743 := bstep (se 1 (by rfl) ⟨3179057, by rfl⟩ : syracuseStep 4238743 = 6358115) B6358115
theorem B4705715 : Blo 1857630 4705715 := bstep (se 1 (by rfl) ⟨3529286, by rfl⟩ : syracuseStep 4705715 = 7058573) B7058573
theorem B2788811 : Blo 1857630 2788811 := bstep (se 1 (by rfl) ⟨2091608, by rfl⟩ : syracuseStep 2788811 = 4183217) B4183217
theorem B2788823 : Blo 1857630 2788823 := bstep (se 1 (by rfl) ⟨2091617, by rfl⟩ : syracuseStep 2788823 = 4183235) B4183235
theorem B6270425 : Blo 1857630 6270425 := bstep (se 2 (by rfl) ⟨2351409, by rfl⟩ : syracuseStep 6270425 = 4702819) B4702819
theorem B2788889 : Blo 1857630 2788889 := bstep (se 2 (by rfl) ⟨1045833, by rfl⟩ : syracuseStep 2788889 = 2091667) B2091667
theorem B6786605 : Blo 1857630 6786605 := bstep (se 3 (by rfl) ⟨1272488, by rfl⟩ : syracuseStep 6786605 = 2544977) B2544977
theorem B4181579 : Blo 1857630 4181579 := bstep (se 1 (by rfl) ⟨3136184, by rfl⟩ : syracuseStep 4181579 = 6272369) B6272369
theorem B30133853 : Blo 1857630 30133853 := bstep (se 3 (by rfl) ⟨5650097, by rfl⟩ : syracuseStep 30133853 = 11300195) B11300195
theorem B4181633 : Blo 1857630 4181633 := bstep (se 2 (by rfl) ⟨1568112, by rfl⟩ : syracuseStep 4181633 = 3136225) B3136225
theorem B2789003 : Blo 1857630 2789003 := bstep (se 1 (by rfl) ⟨2091752, by rfl⟩ : syracuseStep 2789003 = 4183505) B4183505
theorem B2789015 : Blo 1857630 2789015 := bstep (se 1 (by rfl) ⟨2091761, by rfl⟩ : syracuseStep 2789015 = 4183523) B4183523
theorem B4706009 : Blo 1857630 4706009 := bstep (se 2 (by rfl) ⟨1764753, by rfl⟩ : syracuseStep 4706009 = 3529507) B3529507
theorem B2789081 : Blo 1857630 2789081 := bstep (se 2 (by rfl) ⟨1045905, by rfl⟩ : syracuseStep 2789081 = 2091811) B2091811
theorem B2789195 : Blo 1857630 2789195 := bstep (se 1 (by rfl) ⟨2091896, by rfl⟩ : syracuseStep 2789195 = 4183793) B4183793
theorem B2789207 : Blo 1857630 2789207 := bstep (se 1 (by rfl) ⟨2091905, by rfl⟩ : syracuseStep 2789207 = 4183811) B4183811
theorem B4181849 : Blo 1857630 4181849 := bstep (se 2 (by rfl) ⟨1568193, by rfl⟩ : syracuseStep 4181849 = 3136387) B3136387
theorem B45207395 : Blo 1857630 45207395 := bstep (se 1 (by rfl) ⟨33905546, by rfl⟩ : syracuseStep 45207395 = 67811093) B67811093
theorem B2789273 : Blo 1857630 2789273 := bstep (se 2 (by rfl) ⟨1045977, by rfl⟩ : syracuseStep 2789273 = 2091955) B2091955
theorem B4181939 : Blo 1857630 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B15871949 : Blo 1857630 15871949 := bstep (se 3 (by rfl) ⟨2975990, by rfl⟩ : syracuseStep 15871949 = 5951981) B5951981
theorem B4181975 : Blo 1857630 4181975 := bstep (se 1 (by rfl) ⟨3136481, by rfl⟩ : syracuseStep 4181975 = 6272963) B6272963
theorem B9408473 : Blo 1857630 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B4239361 : Blo 1857630 4239361 := bstep (se 2 (by rfl) ⟨1589760, by rfl⟩ : syracuseStep 4239361 = 3179521) B3179521
theorem B2789387 : Blo 1857630 2789387 := bstep (se 1 (by rfl) ⟨2092040, by rfl⟩ : syracuseStep 2789387 = 4184081) B4184081
theorem B2789399 : Blo 1857630 2789399 := bstep (se 1 (by rfl) ⟨2092049, by rfl⟩ : syracuseStep 2789399 = 4184099) B4184099
theorem B3395699 : Blo 1857630 3395699 := bstep (se 1 (by rfl) ⟨2546774, by rfl⟩ : syracuseStep 3395699 = 5093549) B5093549
theorem B4182155 : Blo 1857630 4182155 := bstep (se 1 (by rfl) ⟨3136616, by rfl⟩ : syracuseStep 4182155 = 6273233) B6273233
theorem B6271127 : Blo 1857630 6271127 := bstep (se 1 (by rfl) ⟨4703345, by rfl⟩ : syracuseStep 6271127 = 9406691) B9406691
theorem B4182209 : Blo 1857630 4182209 := bstep (se 2 (by rfl) ⟨1568328, by rfl⟩ : syracuseStep 4182209 = 3136657) B3136657
theorem B7057601 : Blo 1857630 7057601 := bstep (se 2 (by rfl) ⟨2646600, by rfl⟩ : syracuseStep 7057601 = 5293201) B5293201
theorem B4182425 : Blo 1857630 4182425 := bstep (se 2 (by rfl) ⟨1568409, by rfl⟩ : syracuseStep 4182425 = 3136819) B3136819
theorem B4182515 : Blo 1857630 4182515 := bstep (se 1 (by rfl) ⟨3136886, by rfl⟩ : syracuseStep 4182515 = 6273773) B6273773
theorem B4182551 : Blo 1857630 4182551 := bstep (se 1 (by rfl) ⟨3136913, by rfl⟩ : syracuseStep 4182551 = 6273827) B6273827
theorem B11022941 : Blo 1857630 11022941 := bstep (se 3 (by rfl) ⟨2066801, by rfl⟩ : syracuseStep 11022941 = 4133603) B4133603
theorem B3527297 : Blo 1857630 3527297 := bstep (se 2 (by rfl) ⟨1322736, by rfl⟩ : syracuseStep 3527297 = 2645473) B2645473
theorem B6271667 : Blo 1857630 6271667 := bstep (se 1 (by rfl) ⟨4703750, by rfl⟩ : syracuseStep 6271667 = 9407501) B9407501
theorem B3969739 : Blo 1857630 3969739 := bstep (se 1 (by rfl) ⟨2977304, by rfl⟩ : syracuseStep 3969739 = 5954609) B5954609
theorem B4182731 : Blo 1857630 4182731 := bstep (se 1 (by rfl) ⟨3137048, by rfl⟩ : syracuseStep 4182731 = 6274097) B6274097
theorem B4182785 : Blo 1857630 4182785 := bstep (se 2 (by rfl) ⟨1568544, by rfl⟩ : syracuseStep 4182785 = 3137089) B3137089
theorem B3969815 : Blo 1857630 3969815 := bstep (se 1 (by rfl) ⟨2977361, by rfl⟩ : syracuseStep 3969815 = 5954723) B5954723
theorem B2233175 : Blo 1857630 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B18862949 : Blo 1857630 18862949 := bstep (se 4 (by rfl) ⟨1768401, by rfl⟩ : syracuseStep 18862949 = 3536803) B3536803
theorem B10580867 : Blo 1857630 10580867 := bstep (se 1 (by rfl) ⟨7935650, by rfl⟩ : syracuseStep 10580867 = 15871301) B15871301
theorem B3527563 : Blo 1857630 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B6271937 : Blo 1857630 6271937 := bstep (se 2 (by rfl) ⟨2351976, by rfl⟩ : syracuseStep 6271937 = 4703953) B4703953
theorem B4183001 : Blo 1857630 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B13390865 : Blo 1857630 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B4183091 : Blo 1857630 4183091 := bstep (se 1 (by rfl) ⟨3137318, by rfl⟩ : syracuseStep 4183091 = 6274637) B6274637
theorem B3347543 : Blo 1857630 3347543 := bstep (se 1 (by rfl) ⟨2510657, by rfl⟩ : syracuseStep 3347543 = 5021315) B5021315
theorem B4183127 : Blo 1857630 4183127 := bstep (se 1 (by rfl) ⟨3137345, by rfl⟩ : syracuseStep 4183127 = 6274691) B6274691
theorem B17855639 : Blo 1857630 17855639 := bstep (se 1 (by rfl) ⟨13391729, by rfl⟩ : syracuseStep 17855639 = 26783459) B26783459
theorem B23827607 : Blo 1857630 23827607 := bstep (se 1 (by rfl) ⟨17870705, by rfl⟩ : syracuseStep 23827607 = 35741411) B35741411
theorem B7935155 : Blo 1857630 7935155 := bstep (se 1 (by rfl) ⟨5951366, by rfl⟩ : syracuseStep 7935155 = 11902733) B11902733
theorem B10589363 : Blo 1857630 10589363 := bstep (se 1 (by rfl) ⟨7942022, by rfl⟩ : syracuseStep 10589363 = 15884045) B15884045
theorem B51573941 : Blo 1857630 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B4183307 : Blo 1857630 4183307 := bstep (se 1 (by rfl) ⟨3137480, by rfl⟩ : syracuseStep 4183307 = 6274961) B6274961
theorem B11908397 : Blo 1857630 11908397 := bstep (se 3 (by rfl) ⟨2232824, by rfl⟩ : syracuseStep 11908397 = 4465649) B4465649
theorem B4183361 : Blo 1857630 4183361 := bstep (se 2 (by rfl) ⟨1568760, by rfl⟩ : syracuseStep 4183361 = 3137521) B3137521
theorem B3528011 : Blo 1857630 3528011 := bstep (se 1 (by rfl) ⟨2646008, by rfl⟩ : syracuseStep 3528011 = 5292017) B5292017
theorem B6698315 : Blo 1857630 6698315 := bstep (se 1 (by rfl) ⟨5023736, by rfl⟩ : syracuseStep 6698315 = 10047473) B10047473
theorem B2119115 : Blo 1857630 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B6272477 : Blo 1857630 6272477 := bstep (se 3 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 6272477 = 2352179) B2352179
theorem B2119147 : Blo 1857630 2119147 := bstep (se 1 (by rfl) ⟨1589360, by rfl⟩ : syracuseStep 2119147 = 3178721) B3178721
theorem B3528193 : Blo 1857630 3528193 := bstep (se 2 (by rfl) ⟨1323072, by rfl⟩ : syracuseStep 3528193 = 2646145) B2646145
theorem B2233867 : Blo 1857630 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B4183577 : Blo 1857630 4183577 := bstep (se 2 (by rfl) ⟨1568841, by rfl⟩ : syracuseStep 4183577 = 3137683) B3137683
theorem B9410093 : Blo 1857630 9410093 := bstep (se 3 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 9410093 = 3528785) B3528785
theorem B4183667 : Blo 1857630 4183667 := bstep (se 1 (by rfl) ⟨3137750, by rfl⟩ : syracuseStep 4183667 = 6275501) B6275501
theorem B7059089 : Blo 1857630 7059089 := bstep (se 2 (by rfl) ⟨2647158, by rfl⟩ : syracuseStep 7059089 = 5294317) B5294317
theorem B4183703 : Blo 1857630 4183703 := bstep (se 1 (by rfl) ⟨3137777, by rfl⟩ : syracuseStep 4183703 = 6275555) B6275555
theorem B3135179 : Blo 1857630 3135179 := bstep (se 1 (by rfl) ⟨2351384, by rfl⟩ : syracuseStep 3135179 = 4702769) B4702769
theorem B32184013 : Blo 1857630 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B3135307 : Blo 1857630 3135307 := bstep (se 1 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 3135307 = 4702961) B4702961
theorem B4183883 : Blo 1857630 4183883 := bstep (se 1 (by rfl) ⟨3137912, by rfl⟩ : syracuseStep 4183883 = 6275825) B6275825
theorem B3528535 : Blo 1857630 3528535 := bstep (se 1 (by rfl) ⟨2646401, by rfl⟩ : syracuseStep 3528535 = 5292803) B5292803
theorem B40728419 : Blo 1857630 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B4183937 : Blo 1857630 4183937 := bstep (se 2 (by rfl) ⟨1568976, by rfl⟩ : syracuseStep 4183937 = 3137953) B3137953
theorem B2512793 : Blo 1857630 2512793 := bstep (se 2 (by rfl) ⟨942297, by rfl⟩ : syracuseStep 2512793 = 1884595) B1884595
theorem B3135449 : Blo 1857630 3135449 := bstep (se 2 (by rfl) ⟨1175793, by rfl⟩ : syracuseStep 3135449 = 2351587) B2351587
theorem B3528755 : Blo 1857630 3528755 := bstep (se 1 (by rfl) ⟨2646566, by rfl⟩ : syracuseStep 3528755 = 5293133) B5293133
theorem B3348545 : Blo 1857630 3348545 := bstep (se 2 (by rfl) ⟨1255704, by rfl⟩ : syracuseStep 3348545 = 2511409) B2511409
theorem B3135577 : Blo 1857630 3135577 := bstep (se 2 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 3135577 = 2351683) B2351683
theorem B7059545 : Blo 1857630 7059545 := bstep (se 2 (by rfl) ⟨2647329, by rfl⟩ : syracuseStep 7059545 = 5294659) B5294659
theorem B4184153 : Blo 1857630 4184153 := bstep (se 2 (by rfl) ⟨1569057, by rfl⟩ : syracuseStep 4184153 = 3138115) B3138115
theorem B1857643 : Blo 1857630 1857643 := bstep (se 1 (by rfl) ⟨1393232, by rfl⟩ : syracuseStep 1857643 = 2786465) B2786465
theorem B1857655 : Blo 1857630 1857655 := bstep (se 1 (by rfl) ⟨1393241, by rfl⟩ : syracuseStep 1857655 = 2786483) B2786483
theorem B1857675 : Blo 1857630 1857675 := bstep (se 1 (by rfl) ⟨1393256, by rfl⟩ : syracuseStep 1857675 = 2786513) B2786513
theorem B1857687 : Blo 1857630 1857687 := bstep (se 1 (by rfl) ⟨1393265, by rfl⟩ : syracuseStep 1857687 = 2786531) B2786531
theorem B1857707 : Blo 1857630 1857707 := bstep (se 1 (by rfl) ⟨1393280, by rfl⟩ : syracuseStep 1857707 = 2786561) B2786561
theorem B1857719 : Blo 1857630 1857719 := bstep (se 1 (by rfl) ⟨1393289, by rfl⟩ : syracuseStep 1857719 = 2786579) B2786579
theorem B1857739 : Blo 1857630 1857739 := bstep (se 1 (by rfl) ⟨1393304, by rfl⟩ : syracuseStep 1857739 = 2786609) B2786609
theorem B1857751 : Blo 1857630 1857751 := bstep (se 1 (by rfl) ⟨1393313, by rfl⟩ : syracuseStep 1857751 = 2786627) B2786627
theorem B1857771 : Blo 1857630 1857771 := bstep (se 1 (by rfl) ⟨1393328, by rfl⟩ : syracuseStep 1857771 = 2786657) B2786657
theorem B1857783 : Blo 1857630 1857783 := bstep (se 1 (by rfl) ⟨1393337, by rfl⟩ : syracuseStep 1857783 = 2786675) B2786675
theorem B21174533 : Blo 1857630 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B1857803 : Blo 1857630 1857803 := bstep (se 1 (by rfl) ⟨1393352, by rfl⟩ : syracuseStep 1857803 = 2786705) B2786705
theorem B1857815 : Blo 1857630 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B3528983 : Blo 1857630 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B15874339 : Blo 1857630 15874339 := bstep (se 1 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 15874339 = 23811509) B23811509
theorem B1857835 : Blo 1857630 1857835 := bstep (se 1 (by rfl) ⟨1393376, by rfl⟩ : syracuseStep 1857835 = 2786753) B2786753
theorem B7346477 : Blo 1857630 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B7059757 : Blo 1857630 7059757 := bstep (se 3 (by rfl) ⟨1323704, by rfl⟩ : syracuseStep 7059757 = 2647409) B2647409
theorem B1857847 : Blo 1857630 1857847 := bstep (se 1 (by rfl) ⟨1393385, by rfl⟩ : syracuseStep 1857847 = 2786771) B2786771
theorem B1857867 : Blo 1857630 1857867 := bstep (se 1 (by rfl) ⟨1393400, by rfl⟩ : syracuseStep 1857867 = 2786801) B2786801
theorem B1857879 : Blo 1857630 1857879 := bstep (se 1 (by rfl) ⟨1393409, by rfl⟩ : syracuseStep 1857879 = 2786819) B2786819
theorem B1857899 : Blo 1857630 1857899 := bstep (se 1 (by rfl) ⟨1393424, by rfl⟩ : syracuseStep 1857899 = 2786849) B2786849
theorem B1857911 : Blo 1857630 1857911 := bstep (se 1 (by rfl) ⟨1393433, by rfl⟩ : syracuseStep 1857911 = 2786867) B2786867
theorem B1857931 : Blo 1857630 1857931 := bstep (se 1 (by rfl) ⟨1393448, by rfl⟩ : syracuseStep 1857931 = 2786897) B2786897
theorem B1857943 : Blo 1857630 1857943 := bstep (se 1 (by rfl) ⟨1393457, by rfl⟩ : syracuseStep 1857943 = 2786915) B2786915
theorem B9050519 : Blo 1857630 9050519 := bstep (se 1 (by rfl) ⟨6787889, by rfl⟩ : syracuseStep 9050519 = 13575779) B13575779
theorem B1857963 : Blo 1857630 1857963 := bstep (se 1 (by rfl) ⟨1393472, by rfl⟩ : syracuseStep 1857963 = 2786945) B2786945
theorem B1857975 : Blo 1857630 1857975 := bstep (se 1 (by rfl) ⟨1393481, by rfl⟩ : syracuseStep 1857975 = 2786963) B2786963
theorem B1857995 : Blo 1857630 1857995 := bstep (se 1 (by rfl) ⟨1393496, by rfl⟩ : syracuseStep 1857995 = 2786993) B2786993
theorem B1858007 : Blo 1857630 1858007 := bstep (se 1 (by rfl) ⟨1393505, by rfl⟩ : syracuseStep 1858007 = 2787011) B2787011
theorem B1858027 : Blo 1857630 1858027 := bstep (se 1 (by rfl) ⟨1393520, by rfl⟩ : syracuseStep 1858027 = 2787041) B2787041
theorem B1858039 : Blo 1857630 1858039 := bstep (se 1 (by rfl) ⟨1393529, by rfl⟩ : syracuseStep 1858039 = 2787059) B2787059
theorem B3971585 : Blo 1857630 3971585 := bstep (se 2 (by rfl) ⟨1489344, by rfl⟩ : syracuseStep 3971585 = 2978689) B2978689
theorem B1858059 : Blo 1857630 1858059 := bstep (se 1 (by rfl) ⟨1393544, by rfl⟩ : syracuseStep 1858059 = 2787089) B2787089
theorem B1858071 : Blo 1857630 1858071 := bstep (se 1 (by rfl) ⟨1393553, by rfl⟩ : syracuseStep 1858071 = 2787107) B2787107
theorem B3529241 : Blo 1857630 3529241 := bstep (se 2 (by rfl) ⟨1323465, by rfl⟩ : syracuseStep 3529241 = 2646931) B2646931
theorem B1858091 : Blo 1857630 1858091 := bstep (se 1 (by rfl) ⟨1393568, by rfl⟩ : syracuseStep 1858091 = 2787137) B2787137
theorem B1858103 : Blo 1857630 1858103 := bstep (se 1 (by rfl) ⟨1393577, by rfl⟩ : syracuseStep 1858103 = 2787155) B2787155
theorem B1858123 : Blo 1857630 1858123 := bstep (se 1 (by rfl) ⟨1393592, by rfl⟩ : syracuseStep 1858123 = 2787185) B2787185
theorem B6273611 : Blo 1857630 6273611 := bstep (se 1 (by rfl) ⟨4705208, by rfl⟩ : syracuseStep 6273611 = 9410417) B9410417
theorem B1858135 : Blo 1857630 1858135 := bstep (se 1 (by rfl) ⟨1393601, by rfl⟩ : syracuseStep 1858135 = 2787203) B2787203
theorem B7060061 : Blo 1857630 7060061 := bstep (se 3 (by rfl) ⟨1323761, by rfl⟩ : syracuseStep 7060061 = 2647523) B2647523
theorem B10590821 : Blo 1857630 10590821 := bstep (se 4 (by rfl) ⟨992889, by rfl⟩ : syracuseStep 10590821 = 1985779) B1985779
theorem B1858155 : Blo 1857630 1858155 := bstep (se 1 (by rfl) ⟨1393616, by rfl⟩ : syracuseStep 1858155 = 2787233) B2787233
theorem B1858167 : Blo 1857630 1858167 := bstep (se 1 (by rfl) ⟨1393625, by rfl⟩ : syracuseStep 1858167 = 2787251) B2787251
theorem B1858187 : Blo 1857630 1858187 := bstep (se 1 (by rfl) ⟨1393640, by rfl⟩ : syracuseStep 1858187 = 2787281) B2787281
theorem B1858199 : Blo 1857630 1858199 := bstep (se 1 (by rfl) ⟨1393649, by rfl⟩ : syracuseStep 1858199 = 2787299) B2787299
theorem B3136151 : Blo 1857630 3136151 := bstep (se 1 (by rfl) ⟨2352113, by rfl⟩ : syracuseStep 3136151 = 4704227) B4704227
theorem B1858219 : Blo 1857630 1858219 := bstep (se 1 (by rfl) ⟨1393664, by rfl⟩ : syracuseStep 1858219 = 2787329) B2787329
theorem B9173683 : Blo 1857630 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B1858231 : Blo 1857630 1858231 := bstep (se 1 (by rfl) ⟨1393673, by rfl⟩ : syracuseStep 1858231 = 2787347) B2787347
theorem B1858251 : Blo 1857630 1858251 := bstep (se 1 (by rfl) ⟨1393688, by rfl⟩ : syracuseStep 1858251 = 2787377) B2787377
theorem B1858263 : Blo 1857630 1858263 := bstep (se 1 (by rfl) ⟨1393697, by rfl⟩ : syracuseStep 1858263 = 2787395) B2787395
theorem B1858283 : Blo 1857630 1858283 := bstep (se 1 (by rfl) ⟨1393712, by rfl⟩ : syracuseStep 1858283 = 2787425) B2787425
theorem B1858295 : Blo 1857630 1858295 := bstep (se 1 (by rfl) ⟨1393721, by rfl⟩ : syracuseStep 1858295 = 2787443) B2787443
theorem B1858315 : Blo 1857630 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B1858327 : Blo 1857630 1858327 := bstep (se 1 (by rfl) ⟨1393745, by rfl⟩ : syracuseStep 1858327 = 2787491) B2787491
theorem B3136279 : Blo 1857630 3136279 := bstep (se 1 (by rfl) ⟨2352209, by rfl⟩ : syracuseStep 3136279 = 4704419) B4704419
theorem B1858347 : Blo 1857630 1858347 := bstep (se 1 (by rfl) ⟨1393760, by rfl⟩ : syracuseStep 1858347 = 2787521) B2787521
theorem B8936237 : Blo 1857630 8936237 := bstep (se 3 (by rfl) ⟨1675544, by rfl⟩ : syracuseStep 8936237 = 3351089) B3351089
theorem B1858359 : Blo 1857630 1858359 := bstep (se 1 (by rfl) ⟨1393769, by rfl⟩ : syracuseStep 1858359 = 2787539) B2787539
theorem B1858379 : Blo 1857630 1858379 := bstep (se 1 (by rfl) ⟨1393784, by rfl⟩ : syracuseStep 1858379 = 2787569) B2787569
theorem B1858391 : Blo 1857630 1858391 := bstep (se 1 (by rfl) ⟨1393793, by rfl⟩ : syracuseStep 1858391 = 2787587) B2787587
theorem B6273881 : Blo 1857630 6273881 := bstep (se 2 (by rfl) ⟨2352705, by rfl⟩ : syracuseStep 6273881 = 4705411) B4705411
theorem B1858411 : Blo 1857630 1858411 := bstep (se 1 (by rfl) ⟨1393808, by rfl⟩ : syracuseStep 1858411 = 2787617) B2787617
theorem B28990325 : Blo 1857630 28990325 := bstep (se 5 (by rfl) ⟨1358921, by rfl⟩ : syracuseStep 28990325 = 2717843) B2717843
theorem B1858423 : Blo 1857630 1858423 := bstep (se 1 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 1858423 = 2787635) B2787635
theorem B1858443 : Blo 1857630 1858443 := bstep (se 1 (by rfl) ⟨1393832, by rfl⟩ : syracuseStep 1858443 = 2787665) B2787665
theorem B1858455 : Blo 1857630 1858455 := bstep (se 1 (by rfl) ⟨1393841, by rfl⟩ : syracuseStep 1858455 = 2787683) B2787683
theorem B1858475 : Blo 1857630 1858475 := bstep (se 1 (by rfl) ⟨1393856, by rfl⟩ : syracuseStep 1858475 = 2787713) B2787713
theorem B3529651 : Blo 1857630 3529651 := bstep (se 1 (by rfl) ⟨2647238, by rfl⟩ : syracuseStep 3529651 = 5294477) B5294477
theorem B1858487 : Blo 1857630 1858487 := bstep (se 1 (by rfl) ⟨1393865, by rfl⟩ : syracuseStep 1858487 = 2787731) B2787731
theorem B1858507 : Blo 1857630 1858507 := bstep (se 1 (by rfl) ⟨1393880, by rfl⟩ : syracuseStep 1858507 = 2787761) B2787761
theorem B1858519 : Blo 1857630 1858519 := bstep (se 1 (by rfl) ⟨1393889, by rfl⟩ : syracuseStep 1858519 = 2787779) B2787779
theorem B1858539 : Blo 1857630 1858539 := bstep (se 1 (by rfl) ⟨1393904, by rfl⟩ : syracuseStep 1858539 = 2787809) B2787809
theorem B1858551 : Blo 1857630 1858551 := bstep (se 1 (by rfl) ⟨1393913, by rfl⟩ : syracuseStep 1858551 = 2787827) B2787827
theorem B1858571 : Blo 1857630 1858571 := bstep (se 1 (by rfl) ⟨1393928, by rfl⟩ : syracuseStep 1858571 = 2787857) B2787857
theorem B1858583 : Blo 1857630 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B1858603 : Blo 1857630 1858603 := bstep (se 1 (by rfl) ⟨1393952, by rfl⟩ : syracuseStep 1858603 = 2787905) B2787905
theorem B1858615 : Blo 1857630 1858615 := bstep (se 1 (by rfl) ⟨1393961, by rfl⟩ : syracuseStep 1858615 = 2787923) B2787923
theorem B1858635 : Blo 1857630 1858635 := bstep (se 1 (by rfl) ⟨1393976, by rfl⟩ : syracuseStep 1858635 = 2787953) B2787953
theorem B1858647 : Blo 1857630 1858647 := bstep (se 1 (by rfl) ⟨1393985, by rfl⟩ : syracuseStep 1858647 = 2787971) B2787971
theorem B1858667 : Blo 1857630 1858667 := bstep (se 1 (by rfl) ⟨1394000, by rfl⟩ : syracuseStep 1858667 = 2788001) B2788001
theorem B1858679 : Blo 1857630 1858679 := bstep (se 1 (by rfl) ⟨1394009, by rfl⟩ : syracuseStep 1858679 = 2788019) B2788019
theorem B2645131 : Blo 1857630 2645131 := bstep (se 1 (by rfl) ⟨1983848, by rfl⟩ : syracuseStep 2645131 = 3967697) B3967697
theorem B1858699 : Blo 1857630 1858699 := bstep (se 1 (by rfl) ⟨1394024, by rfl⟩ : syracuseStep 1858699 = 2788049) B2788049
theorem B1858711 : Blo 1857630 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B45227159 : Blo 1857630 45227159 := bstep (se 1 (by rfl) ⟨33920369, by rfl⟩ : syracuseStep 45227159 = 67840739) B67840739
theorem B1858731 : Blo 1857630 1858731 := bstep (se 1 (by rfl) ⟨1394048, by rfl⟩ : syracuseStep 1858731 = 2788097) B2788097
theorem B1858743 : Blo 1857630 1858743 := bstep (se 1 (by rfl) ⟨1394057, by rfl⟩ : syracuseStep 1858743 = 2788115) B2788115
theorem B1858763 : Blo 1857630 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B1858775 : Blo 1857630 1858775 := bstep (se 1 (by rfl) ⟨1394081, by rfl⟩ : syracuseStep 1858775 = 2788163) B2788163
theorem B10583257 : Blo 1857630 10583257 := bstep (se 2 (by rfl) ⟨3968721, by rfl⟩ : syracuseStep 10583257 = 7937443) B7937443
theorem B1858795 : Blo 1857630 1858795 := bstep (se 1 (by rfl) ⟨1394096, by rfl⟩ : syracuseStep 1858795 = 2788193) B2788193
theorem B1858807 : Blo 1857630 1858807 := bstep (se 1 (by rfl) ⟨1394105, by rfl⟩ : syracuseStep 1858807 = 2788211) B2788211
theorem B1858827 : Blo 1857630 1858827 := bstep (se 1 (by rfl) ⟨1394120, by rfl⟩ : syracuseStep 1858827 = 2788241) B2788241
theorem B3767575 : Blo 1857630 3767575 := bstep (se 1 (by rfl) ⟨2825681, by rfl⟩ : syracuseStep 3767575 = 5651363) B5651363
theorem B1858839 : Blo 1857630 1858839 := bstep (se 1 (by rfl) ⟨1394129, by rfl⟩ : syracuseStep 1858839 = 2788259) B2788259
theorem B1858859 : Blo 1857630 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B6700333 : Blo 1857630 6700333 := bstep (se 3 (by rfl) ⟨1256312, by rfl⟩ : syracuseStep 6700333 = 2512625) B2512625
theorem B1858871 : Blo 1857630 1858871 := bstep (se 1 (by rfl) ⟨1394153, by rfl⟩ : syracuseStep 1858871 = 2788307) B2788307
theorem B1858891 : Blo 1857630 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B1858903 : Blo 1857630 1858903 := bstep (se 1 (by rfl) ⟨1394177, by rfl⟩ : syracuseStep 1858903 = 2788355) B2788355
theorem B1858923 : Blo 1857630 1858923 := bstep (se 1 (by rfl) ⟨1394192, by rfl⟩ : syracuseStep 1858923 = 2788385) B2788385
theorem B1858935 : Blo 1857630 1858935 := bstep (se 1 (by rfl) ⟨1394201, by rfl⟩ : syracuseStep 1858935 = 2788403) B2788403
theorem B3136907 : Blo 1857630 3136907 := bstep (se 1 (by rfl) ⟨2352680, by rfl⟩ : syracuseStep 3136907 = 4705361) B4705361
theorem B1858955 : Blo 1857630 1858955 := bstep (se 1 (by rfl) ⟨1394216, by rfl⟩ : syracuseStep 1858955 = 2788433) B2788433
theorem B2645399 : Blo 1857630 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B8478103 : Blo 1857630 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B3767705 : Blo 1857630 3767705 := bstep (se 2 (by rfl) ⟨1412889, by rfl⟩ : syracuseStep 3767705 = 2825779) B2825779
theorem B1858967 : Blo 1857630 1858967 := bstep (se 1 (by rfl) ⟨1394225, by rfl⟩ : syracuseStep 1858967 = 2788451) B2788451
theorem B3530137 : Blo 1857630 3530137 := bstep (se 2 (by rfl) ⟨1323801, by rfl⟩ : syracuseStep 3530137 = 2647603) B2647603
theorem B1858987 : Blo 1857630 1858987 := bstep (se 1 (by rfl) ⟨1394240, by rfl⟩ : syracuseStep 1858987 = 2788481) B2788481
theorem B32644529 : Blo 1857630 32644529 := bstep (se 2 (by rfl) ⟨12241698, by rfl⟩ : syracuseStep 32644529 = 24483397) B24483397
theorem B1858999 : Blo 1857630 1858999 := bstep (se 1 (by rfl) ⟨1394249, by rfl⟩ : syracuseStep 1858999 = 2788499) B2788499
theorem B1859019 : Blo 1857630 1859019 := bstep (se 1 (by rfl) ⟨1394264, by rfl⟩ : syracuseStep 1859019 = 2788529) B2788529
theorem B1859031 : Blo 1857630 1859031 := bstep (se 1 (by rfl) ⟨1394273, by rfl⟩ : syracuseStep 1859031 = 2788547) B2788547
theorem B1859051 : Blo 1857630 1859051 := bstep (se 1 (by rfl) ⟨1394288, by rfl⟩ : syracuseStep 1859051 = 2788577) B2788577
theorem B1859063 : Blo 1857630 1859063 := bstep (se 1 (by rfl) ⟨1394297, by rfl⟩ : syracuseStep 1859063 = 2788595) B2788595
theorem B8478211 : Blo 1857630 8478211 := bstep (se 1 (by rfl) ⟨6358658, by rfl⟩ : syracuseStep 8478211 = 12717317) B12717317
theorem B3137035 : Blo 1857630 3137035 := bstep (se 1 (by rfl) ⟨2352776, by rfl⟩ : syracuseStep 3137035 = 4705553) B4705553
theorem B1859083 : Blo 1857630 1859083 := bstep (se 1 (by rfl) ⟨1394312, by rfl⟩ : syracuseStep 1859083 = 2788625) B2788625
theorem B1859095 : Blo 1857630 1859095 := bstep (se 1 (by rfl) ⟨1394321, by rfl⟩ : syracuseStep 1859095 = 2788643) B2788643
theorem B6274583 : Blo 1857630 6274583 := bstep (se 1 (by rfl) ⟨4705937, by rfl⟩ : syracuseStep 6274583 = 9411875) B9411875
theorem B1859115 : Blo 1857630 1859115 := bstep (se 1 (by rfl) ⟨1394336, by rfl⟩ : syracuseStep 1859115 = 2788673) B2788673
theorem B1859127 : Blo 1857630 1859127 := bstep (se 1 (by rfl) ⟨1394345, by rfl⟩ : syracuseStep 1859127 = 2788691) B2788691
theorem B1859147 : Blo 1857630 1859147 := bstep (se 1 (by rfl) ⟨1394360, by rfl⟩ : syracuseStep 1859147 = 2788721) B2788721
theorem B1859159 : Blo 1857630 1859159 := bstep (se 1 (by rfl) ⟨1394369, by rfl⟩ : syracuseStep 1859159 = 2788739) B2788739
theorem B1859179 : Blo 1857630 1859179 := bstep (se 1 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 1859179 = 2788769) B2788769
theorem B1859191 : Blo 1857630 1859191 := bstep (se 1 (by rfl) ⟨1394393, by rfl⟩ : syracuseStep 1859191 = 2788787) B2788787
theorem B1859211 : Blo 1857630 1859211 := bstep (se 1 (by rfl) ⟨1394408, by rfl⟩ : syracuseStep 1859211 = 2788817) B2788817
theorem B1859223 : Blo 1857630 1859223 := bstep (se 1 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 1859223 = 2788835) B2788835
theorem B3137177 : Blo 1857630 3137177 := bstep (se 2 (by rfl) ⟨1176441, by rfl⟩ : syracuseStep 3137177 = 2352883) B2352883
theorem B1859243 : Blo 1857630 1859243 := bstep (se 1 (by rfl) ⟨1394432, by rfl⟩ : syracuseStep 1859243 = 2788865) B2788865
theorem B1859255 : Blo 1857630 1859255 := bstep (se 1 (by rfl) ⟨1394441, by rfl⟩ : syracuseStep 1859255 = 2788883) B2788883
theorem B1859275 : Blo 1857630 1859275 := bstep (se 1 (by rfl) ⟨1394456, by rfl⟩ : syracuseStep 1859275 = 2788913) B2788913
theorem B1859287 : Blo 1857630 1859287 := bstep (se 1 (by rfl) ⟨1394465, by rfl⟩ : syracuseStep 1859287 = 2788931) B2788931
theorem B1859307 : Blo 1857630 1859307 := bstep (se 1 (by rfl) ⟨1394480, by rfl⟩ : syracuseStep 1859307 = 2788961) B2788961
theorem B1859319 : Blo 1857630 1859319 := bstep (se 1 (by rfl) ⟨1394489, by rfl⟩ : syracuseStep 1859319 = 2788979) B2788979
theorem B1859339 : Blo 1857630 1859339 := bstep (se 1 (by rfl) ⟨1394504, by rfl⟩ : syracuseStep 1859339 = 2789009) B2789009
theorem B1859351 : Blo 1857630 1859351 := bstep (se 1 (by rfl) ⟨1394513, by rfl⟩ : syracuseStep 1859351 = 2789027) B2789027
theorem B3137305 : Blo 1857630 3137305 := bstep (se 2 (by rfl) ⟨1176489, by rfl⟩ : syracuseStep 3137305 = 2352979) B2352979
theorem B3350297 : Blo 1857630 3350297 := bstep (se 2 (by rfl) ⟨1256361, by rfl⟩ : syracuseStep 3350297 = 2512723) B2512723
theorem B1859371 : Blo 1857630 1859371 := bstep (se 1 (by rfl) ⟨1394528, by rfl⟩ : syracuseStep 1859371 = 2789057) B2789057
theorem B1859383 : Blo 1857630 1859383 := bstep (se 1 (by rfl) ⟨1394537, by rfl⟩ : syracuseStep 1859383 = 2789075) B2789075
theorem B1859403 : Blo 1857630 1859403 := bstep (se 1 (by rfl) ⟨1394552, by rfl⟩ : syracuseStep 1859403 = 2789105) B2789105
theorem B1859415 : Blo 1857630 1859415 := bstep (se 1 (by rfl) ⟨1394561, by rfl⟩ : syracuseStep 1859415 = 2789123) B2789123
theorem B1859435 : Blo 1857630 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B1859447 : Blo 1857630 1859447 := bstep (se 1 (by rfl) ⟨1394585, by rfl⟩ : syracuseStep 1859447 = 2789171) B2789171
theorem B1859467 : Blo 1857630 1859467 := bstep (se 1 (by rfl) ⟨1394600, by rfl⟩ : syracuseStep 1859467 = 2789201) B2789201
theorem B1859479 : Blo 1857630 1859479 := bstep (se 1 (by rfl) ⟨1394609, by rfl⟩ : syracuseStep 1859479 = 2789219) B2789219
theorem B1859499 : Blo 1857630 1859499 := bstep (se 1 (by rfl) ⟨1394624, by rfl⟩ : syracuseStep 1859499 = 2789249) B2789249
theorem B1859511 : Blo 1857630 1859511 := bstep (se 1 (by rfl) ⟨1394633, by rfl⟩ : syracuseStep 1859511 = 2789267) B2789267
theorem B1859531 : Blo 1857630 1859531 := bstep (se 1 (by rfl) ⟨1394648, by rfl⟩ : syracuseStep 1859531 = 2789297) B2789297
theorem B1859543 : Blo 1857630 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B8929241 : Blo 1857630 8929241 := bstep (se 2 (by rfl) ⟨3348465, by rfl⟩ : syracuseStep 8929241 = 6696931) B6696931
theorem B5291993 : Blo 1857630 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B1859563 : Blo 1857630 1859563 := bstep (se 1 (by rfl) ⟨1394672, by rfl⟩ : syracuseStep 1859563 = 2789345) B2789345
theorem B22609925 : Blo 1857630 22609925 := bstep (se 4 (by rfl) ⟨2119680, by rfl⟩ : syracuseStep 22609925 = 4239361) B4239361
theorem B1859591 : Blo 1857630 1859591 := bstep (se 1 (by rfl) ⟨1394693, by rfl⟩ : syracuseStep 1859591 = 2789387) B2789387
theorem B14106635 : Blo 1857630 14106635 := bstep (se 1 (by rfl) ⟨10579976, by rfl⟩ : syracuseStep 14106635 = 21159953) B21159953
theorem B1859599 : Blo 1857630 1859599 := bstep (se 1 (by rfl) ⟨1394699, by rfl⟩ : syracuseStep 1859599 = 2789399) B2789399
theorem B8929453 : Blo 1857630 8929453 := bstep (se 3 (by rfl) ⟨1674272, by rfl⟩ : syracuseStep 8929453 = 3348545) B3348545
theorem B3137737 : Blo 1857630 3137737 := bstep (se 2 (by rfl) ⟨1176651, by rfl⟩ : syracuseStep 3137737 = 2353303) B2353303
theorem B4702475 : Blo 1857630 4702475 := bstep (se 1 (by rfl) ⟨3526856, by rfl⟩ : syracuseStep 4702475 = 7053713) B7053713
theorem B9413009 : Blo 1857630 9413009 := bstep (se 2 (by rfl) ⟨3529878, by rfl⟩ : syracuseStep 9413009 = 7059757) B7059757
theorem B2351531 : Blo 1857630 2351531 := bstep (se 1 (by rfl) ⟨1763648, by rfl⟩ : syracuseStep 2351531 = 3527297) B3527297
theorem B14311889 : Blo 1857630 14311889 := bstep (se 2 (by rfl) ⟨5366958, by rfl⟩ : syracuseStep 14311889 = 10733917) B10733917
theorem B80380451 : Blo 1857630 80380451 := bstep (se 1 (by rfl) ⟨60285338, by rfl⟩ : syracuseStep 80380451 = 120570677) B120570677
theorem B12575299 : Blo 1857630 12575299 := bstep (se 1 (by rfl) ⟨9431474, by rfl⟩ : syracuseStep 12575299 = 18862949) B18862949
theorem B7053911 : Blo 1857630 7053911 := bstep (se 1 (by rfl) ⟨5290433, by rfl⟩ : syracuseStep 7053911 = 10580867) B10580867
theorem B5292631 : Blo 1857630 5292631 := bstep (se 1 (by rfl) ⟨3969473, by rfl⟩ : syracuseStep 5292631 = 7938947) B7938947
theorem B11903759 : Blo 1857630 11903759 := bstep (se 1 (by rfl) ⟨8927819, by rfl⟩ : syracuseStep 11903759 = 17855639) B17855639
theorem B15885071 : Blo 1857630 15885071 := bstep (se 1 (by rfl) ⟨11913803, by rfl⟩ : syracuseStep 15885071 = 23827607) B23827607
theorem B34382627 : Blo 1857630 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B5292859 : Blo 1857630 5292859 := bstep (se 1 (by rfl) ⟨3969644, by rfl⟩ : syracuseStep 5292859 = 7939289) B7939289
theorem B2646857 : Blo 1857630 2646857 := bstep (se 2 (by rfl) ⟨992571, by rfl⟩ : syracuseStep 2646857 = 1985143) B1985143
theorem B7938931 : Blo 1857630 7938931 := bstep (se 1 (by rfl) ⟨5954198, by rfl⟩ : syracuseStep 7938931 = 11908397) B11908397
theorem B2352007 : Blo 1857630 2352007 := bstep (se 1 (by rfl) ⟨1764005, by rfl⟩ : syracuseStep 2352007 = 3528011) B3528011
theorem B4465543 : Blo 1857630 4465543 := bstep (se 1 (by rfl) ⟨3349157, by rfl⟩ : syracuseStep 4465543 = 6698315) B6698315
theorem B4703123 : Blo 1857630 4703123 := bstep (se 1 (by rfl) ⟨3527342, by rfl⟩ : syracuseStep 4703123 = 7054685) B7054685
theorem B6275987 : Blo 1857630 6275987 := bstep (se 1 (by rfl) ⟨4706990, by rfl⟩ : syracuseStep 6275987 = 9413981) B9413981
theorem B12231577 : Blo 1857630 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B5292985 : Blo 1857630 5292985 := bstep (se 2 (by rfl) ⟨1984869, by rfl⟩ : syracuseStep 5292985 = 3969739) B3969739
theorem B80413667 : Blo 1857630 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B7054397 : Blo 1857630 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B2090119 : Blo 1857630 2090119 := bstep (se 1 (by rfl) ⟨1567589, by rfl⟩ : syracuseStep 2090119 = 3135179) B3135179
theorem B2786447 : Blo 1857630 2786447 := bstep (se 1 (by rfl) ⟨2089835, by rfl⟩ : syracuseStep 2786447 = 4179671) B4179671
theorem B2786489 : Blo 1857630 2786489 := bstep (se 2 (by rfl) ⟨1044933, by rfl⟩ : syracuseStep 2786489 = 2089867) B2089867
theorem B4703417 : Blo 1857630 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B5956865 : Blo 1857630 5956865 := bstep (se 2 (by rfl) ⟨2233824, by rfl⟩ : syracuseStep 5956865 = 4467649) B4467649
theorem B2786567 : Blo 1857630 2786567 := bstep (se 1 (by rfl) ⟨2089925, by rfl⟩ : syracuseStep 2786567 = 4179851) B4179851
theorem B2786603 : Blo 1857630 2786603 := bstep (se 1 (by rfl) ⟨2089952, by rfl⟩ : syracuseStep 2786603 = 4179905) B4179905
theorem B2090299 : Blo 1857630 2090299 := bstep (se 1 (by rfl) ⟨1567724, by rfl⟩ : syracuseStep 2090299 = 3135449) B3135449
theorem B2786633 : Blo 1857630 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B171738481 : Blo 1857630 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B2352503 : Blo 1857630 2352503 := bstep (se 1 (by rfl) ⟨1764377, by rfl⟩ : syracuseStep 2352503 = 3528755) B3528755
theorem B9405881 : Blo 1857630 9405881 := bstep (se 2 (by rfl) ⟨3527205, by rfl⟩ : syracuseStep 9405881 = 7054411) B7054411
theorem B2786747 : Blo 1857630 2786747 := bstep (se 1 (by rfl) ⟨2090060, by rfl⟩ : syracuseStep 2786747 = 4180121) B4180121
theorem B11306425 : Blo 1857630 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B2786807 : Blo 1857630 2786807 := bstep (se 1 (by rfl) ⟨2090105, by rfl⟩ : syracuseStep 2786807 = 4180211) B4180211
theorem B14116355 : Blo 1857630 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B2786831 : Blo 1857630 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B2352655 : Blo 1857630 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B2786873 : Blo 1857630 2786873 := bstep (se 2 (by rfl) ⟨1045077, by rfl⟩ : syracuseStep 2786873 = 2090155) B2090155
theorem B26789453 : Blo 1857630 26789453 := bstep (se 3 (by rfl) ⟨5023022, by rfl⟩ : syracuseStep 26789453 = 10046045) B10046045
theorem B29394509 : Blo 1857630 29394509 := bstep (se 3 (by rfl) ⟨5511470, by rfl⟩ : syracuseStep 29394509 = 11022941) B11022941
theorem B2786951 : Blo 1857630 2786951 := bstep (se 1 (by rfl) ⟨2090213, by rfl⟩ : syracuseStep 2786951 = 4180427) B4180427
theorem B2786987 : Blo 1857630 2786987 := bstep (se 1 (by rfl) ⟨2090240, by rfl⟩ : syracuseStep 2786987 = 4180481) B4180481
theorem B2647723 : Blo 1857630 2647723 := bstep (se 1 (by rfl) ⟨1985792, by rfl⟩ : syracuseStep 2647723 = 3971585) B3971585
theorem B2352827 : Blo 1857630 2352827 := bstep (se 1 (by rfl) ⟨1764620, by rfl⟩ : syracuseStep 2352827 = 3529241) B3529241
theorem B2787017 : Blo 1857630 2787017 := bstep (se 2 (by rfl) ⟨1045131, by rfl⟩ : syracuseStep 2787017 = 2090263) B2090263
theorem B5023433 : Blo 1857630 5023433 := bstep (se 2 (by rfl) ⟨1883787, by rfl⟩ : syracuseStep 5023433 = 3767575) B3767575
theorem B2090767 : Blo 1857630 2090767 := bstep (se 1 (by rfl) ⟨1568075, by rfl⟩ : syracuseStep 2090767 = 3136151) B3136151
theorem B2787131 : Blo 1857630 2787131 := bstep (se 1 (by rfl) ⟨2090348, by rfl⟩ : syracuseStep 2787131 = 4180697) B4180697
theorem B4704115 : Blo 1857630 4704115 := bstep (se 1 (by rfl) ⟨3528086, by rfl⟩ : syracuseStep 4704115 = 7056173) B7056173
theorem B5957491 : Blo 1857630 5957491 := bstep (se 1 (by rfl) ⟨4468118, by rfl⟩ : syracuseStep 5957491 = 8936237) B8936237
theorem B2787191 : Blo 1857630 2787191 := bstep (se 1 (by rfl) ⟨2090393, by rfl⟩ : syracuseStep 2787191 = 4180787) B4180787
theorem B10585991 : Blo 1857630 10585991 := bstep (se 1 (by rfl) ⟨7939493, by rfl⟩ : syracuseStep 10585991 = 15878987) B15878987
theorem B2787215 : Blo 1857630 2787215 := bstep (se 1 (by rfl) ⟨2090411, by rfl⟩ : syracuseStep 2787215 = 4180823) B4180823
theorem B19326883 : Blo 1857630 19326883 := bstep (se 1 (by rfl) ⟨14495162, by rfl⟩ : syracuseStep 19326883 = 28990325) B28990325
theorem B14108579 : Blo 1857630 14108579 := bstep (se 1 (by rfl) ⟨10581434, by rfl⟩ : syracuseStep 14108579 = 21162869) B21162869
theorem B2787257 : Blo 1857630 2787257 := bstep (se 2 (by rfl) ⟨1045221, by rfl⟩ : syracuseStep 2787257 = 2090443) B2090443
theorem B3180473 : Blo 1857630 3180473 := bstep (se 2 (by rfl) ⟨1192677, by rfl⟩ : syracuseStep 3180473 = 2385355) B2385355
theorem B4704257 : Blo 1857630 4704257 := bstep (se 2 (by rfl) ⟨1764096, by rfl⟩ : syracuseStep 4704257 = 3528193) B3528193
theorem B2787335 : Blo 1857630 2787335 := bstep (se 1 (by rfl) ⟨2090501, by rfl⟩ : syracuseStep 2787335 = 4181003) B4181003
theorem B2787371 : Blo 1857630 2787371 := bstep (se 1 (by rfl) ⟨2090528, by rfl⟩ : syracuseStep 2787371 = 4181057) B4181057
theorem B10586173 : Blo 1857630 10586173 := bstep (se 3 (by rfl) ⟨1984907, by rfl⟩ : syracuseStep 10586173 = 3969815) B3969815
theorem B2787401 : Blo 1857630 2787401 := bstep (se 2 (by rfl) ⟨1045275, by rfl⟩ : syracuseStep 2787401 = 2090551) B2090551
theorem B4180103 : Blo 1857630 4180103 := bstep (se 1 (by rfl) ⟨3135077, by rfl⟩ : syracuseStep 4180103 = 6270155) B6270155
theorem B2787515 : Blo 1857630 2787515 := bstep (se 1 (by rfl) ⟨2090636, by rfl⟩ : syracuseStep 2787515 = 4181273) B4181273
theorem B1984699 : Blo 1857630 1984699 := bstep (se 1 (by rfl) ⟨1488524, by rfl⟩ : syracuseStep 1984699 = 2977049) B2977049
theorem B2787575 : Blo 1857630 2787575 := bstep (se 1 (by rfl) ⟨2090681, by rfl⟩ : syracuseStep 2787575 = 4181363) B4181363
theorem B2091271 : Blo 1857630 2091271 := bstep (se 1 (by rfl) ⟨1568453, by rfl⟩ : syracuseStep 2091271 = 3136907) B3136907
theorem B2787599 : Blo 1857630 2787599 := bstep (se 1 (by rfl) ⟨2090699, by rfl⟩ : syracuseStep 2787599 = 4181399) B4181399
theorem B42912017 : Blo 1857630 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B2787641 : Blo 1857630 2787641 := bstep (se 2 (by rfl) ⟨1045365, by rfl⟩ : syracuseStep 2787641 = 2090731) B2090731
theorem B4180283 : Blo 1857630 4180283 := bstep (se 1 (by rfl) ⟨3135212, by rfl⟩ : syracuseStep 4180283 = 6270425) B6270425
theorem B4524403 : Blo 1857630 4524403 := bstep (se 1 (by rfl) ⟨3393302, by rfl⟩ : syracuseStep 4524403 = 6786605) B6786605
theorem B2787719 : Blo 1857630 2787719 := bstep (se 1 (by rfl) ⟨2090789, by rfl⟩ : syracuseStep 2787719 = 4181579) B4181579
theorem B20089235 : Blo 1857630 20089235 := bstep (se 1 (by rfl) ⟨15066926, by rfl⟩ : syracuseStep 20089235 = 30133853) B30133853
theorem B2787755 : Blo 1857630 2787755 := bstep (se 1 (by rfl) ⟨2090816, by rfl⟩ : syracuseStep 2787755 = 4181633) B4181633
theorem B4180409 : Blo 1857630 4180409 := bstep (se 2 (by rfl) ⟨1567653, by rfl⟩ : syracuseStep 4180409 = 3135307) B3135307
theorem B2091451 : Blo 1857630 2091451 := bstep (se 1 (by rfl) ⟨1568588, by rfl⟩ : syracuseStep 2091451 = 3137177) B3137177
theorem B2787785 : Blo 1857630 2787785 := bstep (se 2 (by rfl) ⟨1045419, by rfl⟩ : syracuseStep 2787785 = 2090839) B2090839
theorem B4704713 : Blo 1857630 4704713 := bstep (se 2 (by rfl) ⟨1764267, by rfl⟩ : syracuseStep 4704713 = 3528535) B3528535
theorem B2787899 : Blo 1857630 2787899 := bstep (se 1 (by rfl) ⟨2090924, by rfl⟩ : syracuseStep 2787899 = 4181849) B4181849
theorem B2787959 : Blo 1857630 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B2787983 : Blo 1857630 2787983 := bstep (se 1 (by rfl) ⟨2090987, by rfl⟩ : syracuseStep 2787983 = 4181975) B4181975
theorem B2788025 : Blo 1857630 2788025 := bstep (se 2 (by rfl) ⟨1045509, by rfl⟩ : syracuseStep 2788025 = 2091019) B2091019
theorem B9407177 : Blo 1857630 9407177 := bstep (se 2 (by rfl) ⟨3527691, by rfl⟩ : syracuseStep 9407177 = 7055383) B7055383
theorem B2263799 : Blo 1857630 2263799 := bstep (se 1 (by rfl) ⟨1697849, by rfl⟩ : syracuseStep 2263799 = 3395699) B3395699
theorem B2788103 : Blo 1857630 2788103 := bstep (se 1 (by rfl) ⟨2091077, by rfl⟩ : syracuseStep 2788103 = 4182155) B4182155
theorem B4180751 : Blo 1857630 4180751 := bstep (se 1 (by rfl) ⟨3135563, by rfl⟩ : syracuseStep 4180751 = 6271127) B6271127
theorem B7056143 : Blo 1857630 7056143 := bstep (se 1 (by rfl) ⟨5292107, by rfl⟩ : syracuseStep 7056143 = 10584215) B10584215
theorem B4180769 : Blo 1857630 4180769 := bstep (se 2 (by rfl) ⟨1567788, by rfl⟩ : syracuseStep 4180769 = 3135577) B3135577
theorem B2788139 : Blo 1857630 2788139 := bstep (se 1 (by rfl) ⟨2091104, by rfl⟩ : syracuseStep 2788139 = 4182209) B4182209
theorem B4705067 : Blo 1857630 4705067 := bstep (se 1 (by rfl) ⟨3528800, by rfl⟩ : syracuseStep 4705067 = 7057601) B7057601
theorem B5294909 : Blo 1857630 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B2788169 : Blo 1857630 2788169 := bstep (se 2 (by rfl) ⟨1045563, by rfl⟩ : syracuseStep 2788169 = 2091127) B2091127
theorem B6269831 : Blo 1857630 6269831 := bstep (se 1 (by rfl) ⟨4702373, by rfl⟩ : syracuseStep 6269831 = 9404747) B9404747
theorem B2091919 : Blo 1857630 2091919 := bstep (se 1 (by rfl) ⟨1568939, by rfl⟩ : syracuseStep 2091919 = 3137879) B3137879
theorem B2788283 : Blo 1857630 2788283 := bstep (se 1 (by rfl) ⟨2091212, by rfl⟩ : syracuseStep 2788283 = 4182425) B4182425
theorem B15870923 : Blo 1857630 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B2788343 : Blo 1857630 2788343 := bstep (se 1 (by rfl) ⟨2091257, by rfl⟩ : syracuseStep 2788343 = 4182515) B4182515
theorem B2788367 : Blo 1857630 2788367 := bstep (se 1 (by rfl) ⟨2091275, by rfl⟩ : syracuseStep 2788367 = 4182551) B4182551
theorem B2788409 : Blo 1857630 2788409 := bstep (se 2 (by rfl) ⟨1045653, by rfl⟩ : syracuseStep 2788409 = 2091307) B2091307
theorem B4181111 : Blo 1857630 4181111 := bstep (se 1 (by rfl) ⟨3135833, by rfl⟩ : syracuseStep 4181111 = 6271667) B6271667
theorem B2788487 : Blo 1857630 2788487 := bstep (se 1 (by rfl) ⟨2091365, by rfl⟩ : syracuseStep 2788487 = 4182731) B4182731
theorem B2788523 : Blo 1857630 2788523 := bstep (se 1 (by rfl) ⟨2091392, by rfl⟩ : syracuseStep 2788523 = 4182785) B4182785
theorem B15076525 : Blo 1857630 15076525 := bstep (se 3 (by rfl) ⟨2826848, by rfl⟩ : syracuseStep 15076525 = 5653697) B5653697
theorem B2788553 : Blo 1857630 2788553 := bstep (se 2 (by rfl) ⟨1045707, by rfl⟩ : syracuseStep 2788553 = 2091415) B2091415
theorem B6270209 : Blo 1857630 6270209 := bstep (se 2 (by rfl) ⟨2351328, by rfl⟩ : syracuseStep 6270209 = 4702657) B4702657
theorem B4181291 : Blo 1857630 4181291 := bstep (se 1 (by rfl) ⟨3135968, by rfl⟩ : syracuseStep 4181291 = 6271937) B6271937
theorem B2788667 : Blo 1857630 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B241274213 : Blo 1857630 241274213 := bstep (se 4 (by rfl) ⟨22619457, by rfl⟩ : syracuseStep 241274213 = 45238915) B45238915
theorem B2788727 : Blo 1857630 2788727 := bstep (se 1 (by rfl) ⟨2091545, by rfl⟩ : syracuseStep 2788727 = 4183091) B4183091
theorem B15068551 : Blo 1857630 15068551 := bstep (se 1 (by rfl) ⟨11301413, by rfl⟩ : syracuseStep 15068551 = 22602827) B22602827
theorem B2231695 : Blo 1857630 2231695 := bstep (se 1 (by rfl) ⟨1673771, by rfl⟩ : syracuseStep 2231695 = 3347543) B3347543
theorem B2788751 : Blo 1857630 2788751 := bstep (se 1 (by rfl) ⟨2091563, by rfl⟩ : syracuseStep 2788751 = 4183127) B4183127
theorem B2788793 : Blo 1857630 2788793 := bstep (se 2 (by rfl) ⟨1045797, by rfl⟩ : syracuseStep 2788793 = 2091595) B2091595
theorem B19590605 : Blo 1857630 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B2788871 : Blo 1857630 2788871 := bstep (se 1 (by rfl) ⟨2091653, by rfl⟩ : syracuseStep 2788871 = 4183307) B4183307
theorem B2788907 : Blo 1857630 2788907 := bstep (se 1 (by rfl) ⟨2091680, by rfl⟩ : syracuseStep 2788907 = 4183361) B4183361
theorem B2788937 : Blo 1857630 2788937 := bstep (se 2 (by rfl) ⟨1045851, by rfl⟩ : syracuseStep 2788937 = 2091703) B2091703
theorem B4181651 : Blo 1857630 4181651 := bstep (se 1 (by rfl) ⟨3136238, by rfl⟩ : syracuseStep 4181651 = 6272477) B6272477
theorem B2789051 : Blo 1857630 2789051 := bstep (se 1 (by rfl) ⟨2091788, by rfl⟩ : syracuseStep 2789051 = 4183577) B4183577
theorem B4525769 : Blo 1857630 4525769 := bstep (se 2 (by rfl) ⟨1697163, by rfl⟩ : syracuseStep 4525769 = 3394327) B3394327
theorem B4181705 : Blo 1857630 4181705 := bstep (se 2 (by rfl) ⟨1568139, by rfl⟩ : syracuseStep 4181705 = 3136279) B3136279
theorem B2789111 : Blo 1857630 2789111 := bstep (se 1 (by rfl) ⟨2091833, by rfl⟩ : syracuseStep 2789111 = 4183667) B4183667
theorem B10587905 : Blo 1857630 10587905 := bstep (se 2 (by rfl) ⟨3970464, by rfl⟩ : syracuseStep 10587905 = 7940929) B7940929
theorem B4706059 : Blo 1857630 4706059 := bstep (se 1 (by rfl) ⟨3529544, by rfl⟩ : syracuseStep 4706059 = 7059089) B7059089
theorem B2789135 : Blo 1857630 2789135 := bstep (se 1 (by rfl) ⟨2091851, by rfl⟩ : syracuseStep 2789135 = 4183703) B4183703
theorem B2789177 : Blo 1857630 2789177 := bstep (se 2 (by rfl) ⟨1045941, by rfl⟩ : syracuseStep 2789177 = 2091883) B2091883
theorem B2789255 : Blo 1857630 2789255 := bstep (se 1 (by rfl) ⟨2091941, by rfl⟩ : syracuseStep 2789255 = 4183883) B4183883
theorem B27152279 : Blo 1857630 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B4706201 : Blo 1857630 4706201 := bstep (se 2 (by rfl) ⟨1764825, by rfl⟩ : syracuseStep 4706201 = 3529651) B3529651
theorem B2789291 : Blo 1857630 2789291 := bstep (se 1 (by rfl) ⟨2091968, by rfl⟩ : syracuseStep 2789291 = 4183937) B4183937
theorem B2789321 : Blo 1857630 2789321 := bstep (se 2 (by rfl) ⟨1045995, by rfl⟩ : syracuseStep 2789321 = 2091991) B2091991
theorem B2682895 : Blo 1857630 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B6271019 : Blo 1857630 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B4706363 : Blo 1857630 4706363 := bstep (se 1 (by rfl) ⟨3529772, by rfl⟩ : syracuseStep 4706363 = 7059545) B7059545
theorem B2789435 : Blo 1857630 2789435 := bstep (se 1 (by rfl) ⟨2092076, by rfl⟩ : syracuseStep 2789435 = 4184153) B4184153
theorem B3526841 : Blo 1857630 3526841 := bstep (se 2 (by rfl) ⟨1322565, by rfl⟩ : syracuseStep 3526841 = 2645131) B2645131
theorem B6033679 : Blo 1857630 6033679 := bstep (se 1 (by rfl) ⟨4525259, by rfl⟩ : syracuseStep 6033679 = 9050519) B9050519
theorem B14111009 : Blo 1857630 14111009 := bstep (se 2 (by rfl) ⟨5291628, by rfl⟩ : syracuseStep 14111009 = 10583257) B10583257
theorem B7057799 : Blo 1857630 7057799 := bstep (se 1 (by rfl) ⟨5293349, by rfl⟩ : syracuseStep 7057799 = 10586699) B10586699
theorem B4182407 : Blo 1857630 4182407 := bstep (se 1 (by rfl) ⟨3136805, by rfl⟩ : syracuseStep 4182407 = 6273611) B6273611
theorem B8933777 : Blo 1857630 8933777 := bstep (se 2 (by rfl) ⟨3350166, by rfl⟩ : syracuseStep 8933777 = 6700333) B6700333
theorem B4706707 : Blo 1857630 4706707 := bstep (se 1 (by rfl) ⟨3530030, by rfl⟩ : syracuseStep 4706707 = 7060061) B7060061
theorem B4706849 : Blo 1857630 4706849 := bstep (se 2 (by rfl) ⟨1765068, by rfl⟩ : syracuseStep 4706849 = 3530137) B3530137
theorem B4182587 : Blo 1857630 4182587 := bstep (se 1 (by rfl) ⟨3136940, by rfl⟩ : syracuseStep 4182587 = 6273881) B6273881
theorem B4182713 : Blo 1857630 4182713 := bstep (se 2 (by rfl) ⟨1568517, by rfl⟩ : syracuseStep 4182713 = 3137035) B3137035
theorem B2978489 : Blo 1857630 2978489 := bstep (se 2 (by rfl) ⟨1116933, by rfl⟩ : syracuseStep 2978489 = 2233867) B2233867
theorem B30151439 : Blo 1857630 30151439 := bstep (se 1 (by rfl) ⟨22613579, by rfl⟩ : syracuseStep 30151439 = 45227159) B45227159
theorem B34861859 : Blo 1857630 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B45208469 : Blo 1857630 45208469 := bstep (se 6 (by rfl) ⟨1059573, by rfl⟩ : syracuseStep 45208469 = 2119147) B2119147
theorem B2511803 : Blo 1857630 2511803 := bstep (se 1 (by rfl) ⟨1883852, by rfl⟩ : syracuseStep 2511803 = 3767705) B3767705
theorem B21763019 : Blo 1857630 21763019 := bstep (se 1 (by rfl) ⟨16322264, by rfl⟩ : syracuseStep 21763019 = 32644529) B32644529
theorem B4183055 : Blo 1857630 4183055 := bstep (se 1 (by rfl) ⟨3137291, by rfl⟩ : syracuseStep 4183055 = 6274583) B6274583
theorem B4183073 : Blo 1857630 4183073 := bstep (se 2 (by rfl) ⟨1568652, by rfl⟩ : syracuseStep 4183073 = 3137305) B3137305
theorem B2233531 : Blo 1857630 2233531 := bstep (se 1 (by rfl) ⟨1675148, by rfl⟩ : syracuseStep 2233531 = 3350297) B3350297
theorem B14111981 : Blo 1857630 14111981 := bstep (se 3 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 14111981 = 5291993) B5291993
theorem B10581299 : Blo 1857630 10581299 := bstep (se 1 (by rfl) ⟨7935974, by rfl⟩ : syracuseStep 10581299 = 15871949) B15871949
theorem B5952827 : Blo 1857630 5952827 := bstep (se 1 (by rfl) ⟨4464620, by rfl⟩ : syracuseStep 5952827 = 8929241) B8929241
theorem B6272315 : Blo 1857630 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B4183415 : Blo 1857630 4183415 := bstep (se 1 (by rfl) ⟨3137561, by rfl⟩ : syracuseStep 4183415 = 6275123) B6275123
theorem B3134855 : Blo 1857630 3134855 := bstep (se 1 (by rfl) ⟨2351141, by rfl⟩ : syracuseStep 3134855 = 4702283) B4702283
theorem B4183595 : Blo 1857630 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B40195763 : Blo 1857630 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B21165785 : Blo 1857630 21165785 := bstep (se 2 (by rfl) ⟨7937169, by rfl⟩ : syracuseStep 21165785 = 15874339) B15874339
theorem B6272801 : Blo 1857630 6272801 := bstep (se 2 (by rfl) ⟨2352300, by rfl⟩ : syracuseStep 6272801 = 4704601) B4704601
theorem B7935803 : Blo 1857630 7935803 := bstep (se 1 (by rfl) ⟨5951852, by rfl⟩ : syracuseStep 7935803 = 11903705) B11903705
theorem B4183955 : Blo 1857630 4183955 := bstep (se 1 (by rfl) ⟨3137966, by rfl⟩ : syracuseStep 4183955 = 6275933) B6275933
theorem B2512841 : Blo 1857630 2512841 := bstep (se 2 (by rfl) ⟨942315, by rfl⟩ : syracuseStep 2512841 = 1884631) B1884631
theorem B4184009 : Blo 1857630 4184009 := bstep (se 2 (by rfl) ⟨1569003, by rfl⟩ : syracuseStep 4184009 = 3138007) B3138007
theorem B8927243 : Blo 1857630 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B3135503 : Blo 1857630 3135503 := bstep (se 1 (by rfl) ⟨2351627, by rfl⟩ : syracuseStep 3135503 = 4703255) B4703255
theorem B5290103 : Blo 1857630 5290103 := bstep (se 1 (by rfl) ⟨3967577, by rfl⟩ : syracuseStep 5290103 = 7935155) B7935155
theorem B7059575 : Blo 1857630 7059575 := bstep (se 1 (by rfl) ⟨5294681, by rfl⟩ : syracuseStep 7059575 = 10589363) B10589363
theorem B1857671 : Blo 1857630 1857671 := bstep (se 1 (by rfl) ⟨1393253, by rfl⟩ : syracuseStep 1857671 = 2786507) B2786507
theorem B3528839 : Blo 1857630 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B1857679 : Blo 1857630 1857679 := bstep (se 1 (by rfl) ⟨1393259, by rfl⟩ : syracuseStep 1857679 = 2786519) B2786519
theorem B1857723 : Blo 1857630 1857723 := bstep (se 1 (by rfl) ⟨1393292, by rfl⟩ : syracuseStep 1857723 = 2786585) B2786585
theorem B1857799 : Blo 1857630 1857799 := bstep (se 1 (by rfl) ⟨1393349, by rfl⟩ : syracuseStep 1857799 = 2786699) B2786699
theorem B1857807 : Blo 1857630 1857807 := bstep (se 1 (by rfl) ⟨1393355, by rfl⟩ : syracuseStep 1857807 = 2786711) B2786711
theorem B10049807 : Blo 1857630 10049807 := bstep (se 1 (by rfl) ⟨7537355, by rfl⟩ : syracuseStep 10049807 = 15074711) B15074711
theorem B1857851 : Blo 1857630 1857851 := bstep (se 1 (by rfl) ⟨1393388, by rfl⟩ : syracuseStep 1857851 = 2786777) B2786777
theorem B3971387 : Blo 1857630 3971387 := bstep (se 1 (by rfl) ⟨2978540, by rfl⟩ : syracuseStep 3971387 = 5957081) B5957081
theorem B6273395 : Blo 1857630 6273395 := bstep (se 1 (by rfl) ⟨4705046, by rfl⟩ : syracuseStep 6273395 = 9410093) B9410093
theorem B1857927 : Blo 1857630 1857927 := bstep (se 1 (by rfl) ⟨1393445, by rfl⟩ : syracuseStep 1857927 = 2786891) B2786891
theorem B1857935 : Blo 1857630 1857935 := bstep (se 1 (by rfl) ⟨1393451, by rfl⟩ : syracuseStep 1857935 = 2786903) B2786903
theorem B1857979 : Blo 1857630 1857979 := bstep (se 1 (by rfl) ⟨1393484, by rfl⟩ : syracuseStep 1857979 = 2786969) B2786969
theorem B1858055 : Blo 1857630 1858055 := bstep (se 1 (by rfl) ⟨1393541, by rfl⟩ : syracuseStep 1858055 = 2787083) B2787083
theorem B1858063 : Blo 1857630 1858063 := bstep (se 1 (by rfl) ⟨1393547, by rfl⟩ : syracuseStep 1858063 = 2787095) B2787095
theorem B5650973 : Blo 1857630 5650973 := bstep (se 3 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 5650973 = 2119115) B2119115
theorem B7936555 : Blo 1857630 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B3136043 : Blo 1857630 3136043 := bstep (se 1 (by rfl) ⟨2352032, by rfl⟩ : syracuseStep 3136043 = 4704065) B4704065
theorem B1858107 : Blo 1857630 1858107 := bstep (se 1 (by rfl) ⟨1393580, by rfl⟩ : syracuseStep 1858107 = 2787161) B2787161
theorem B1858183 : Blo 1857630 1858183 := bstep (se 1 (by rfl) ⟨1393637, by rfl⟩ : syracuseStep 1858183 = 2787275) B2787275
theorem B1858191 : Blo 1857630 1858191 := bstep (se 1 (by rfl) ⟨1393643, by rfl⟩ : syracuseStep 1858191 = 2787287) B2787287
theorem B1858235 : Blo 1857630 1858235 := bstep (se 1 (by rfl) ⟨1393676, by rfl⟩ : syracuseStep 1858235 = 2787353) B2787353
theorem B10582757 : Blo 1857630 10582757 := bstep (se 4 (by rfl) ⟨992133, by rfl⟩ : syracuseStep 10582757 = 1984267) B1984267
theorem B1858311 : Blo 1857630 1858311 := bstep (se 1 (by rfl) ⟨1393733, by rfl⟩ : syracuseStep 1858311 = 2787467) B2787467
theorem B4463371 : Blo 1857630 4463371 := bstep (se 1 (by rfl) ⟨3347528, by rfl⟩ : syracuseStep 4463371 = 6695057) B6695057
theorem B1858319 : Blo 1857630 1858319 := bstep (se 1 (by rfl) ⟨1393739, by rfl⟩ : syracuseStep 1858319 = 2787479) B2787479
theorem B1858363 : Blo 1857630 1858363 := bstep (se 1 (by rfl) ⟨1393772, by rfl⟩ : syracuseStep 1858363 = 2787545) B2787545
theorem B1858439 : Blo 1857630 1858439 := bstep (se 1 (by rfl) ⟨1393829, by rfl⟩ : syracuseStep 1858439 = 2787659) B2787659
theorem B1858447 : Blo 1857630 1858447 := bstep (se 1 (by rfl) ⟨1393835, by rfl⟩ : syracuseStep 1858447 = 2787671) B2787671
theorem B3136441 : Blo 1857630 3136441 := bstep (se 2 (by rfl) ⟨1176165, by rfl⟩ : syracuseStep 3136441 = 2352331) B2352331
theorem B1858491 : Blo 1857630 1858491 := bstep (se 1 (by rfl) ⟨1393868, by rfl⟩ : syracuseStep 1858491 = 2787737) B2787737
theorem B1858567 : Blo 1857630 1858567 := bstep (se 1 (by rfl) ⟨1393925, by rfl⟩ : syracuseStep 1858567 = 2787851) B2787851
theorem B1858575 : Blo 1857630 1858575 := bstep (se 1 (by rfl) ⟨1393931, by rfl⟩ : syracuseStep 1858575 = 2787863) B2787863
theorem B1858619 : Blo 1857630 1858619 := bstep (se 1 (by rfl) ⟨1393964, by rfl⟩ : syracuseStep 1858619 = 2787929) B2787929
theorem B7060547 : Blo 1857630 7060547 := bstep (se 1 (by rfl) ⟨5295410, by rfl⟩ : syracuseStep 7060547 = 10590821) B10590821
theorem B5954647 : Blo 1857630 5954647 := bstep (se 1 (by rfl) ⟨4465985, by rfl⟩ : syracuseStep 5954647 = 8931971) B8931971
theorem B14113925 : Blo 1857630 14113925 := bstep (se 4 (by rfl) ⟨1323180, by rfl⟩ : syracuseStep 14113925 = 2646361) B2646361
theorem B1858695 : Blo 1857630 1858695 := bstep (se 1 (by rfl) ⟨1394021, by rfl⟩ : syracuseStep 1858695 = 2788043) B2788043
theorem B1858703 : Blo 1857630 1858703 := bstep (se 1 (by rfl) ⟨1394027, by rfl⟩ : syracuseStep 1858703 = 2788055) B2788055
theorem B1858747 : Blo 1857630 1858747 := bstep (se 1 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 1858747 = 2788121) B2788121
theorem B5651657 : Blo 1857630 5651657 := bstep (se 2 (by rfl) ⟨2119371, by rfl⟩ : syracuseStep 5651657 = 4238743) B4238743
theorem B11304137 : Blo 1857630 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B20102381 : Blo 1857630 20102381 := bstep (se 3 (by rfl) ⟨3769196, by rfl⟩ : syracuseStep 20102381 = 7538393) B7538393
theorem B1858823 : Blo 1857630 1858823 := bstep (se 1 (by rfl) ⟨1394117, by rfl⟩ : syracuseStep 1858823 = 2788235) B2788235
theorem B1858831 : Blo 1857630 1858831 := bstep (se 1 (by rfl) ⟨1394123, by rfl⟩ : syracuseStep 1858831 = 2788247) B2788247
theorem B1858875 : Blo 1857630 1858875 := bstep (se 1 (by rfl) ⟨1394156, by rfl⟩ : syracuseStep 1858875 = 2788313) B2788313
theorem B11304281 : Blo 1857630 11304281 := bstep (se 2 (by rfl) ⟨4239105, by rfl⟩ : syracuseStep 11304281 = 8478211) B8478211
theorem B1858951 : Blo 1857630 1858951 := bstep (se 1 (by rfl) ⟨1394213, by rfl⟩ : syracuseStep 1858951 = 2788427) B2788427
theorem B1858959 : Blo 1857630 1858959 := bstep (se 1 (by rfl) ⟨1394219, by rfl⟩ : syracuseStep 1858959 = 2788439) B2788439
theorem B1859003 : Blo 1857630 1859003 := bstep (se 1 (by rfl) ⟨1394252, by rfl⟩ : syracuseStep 1859003 = 2788505) B2788505
theorem B1859079 : Blo 1857630 1859079 := bstep (se 1 (by rfl) ⟨1394309, by rfl⟩ : syracuseStep 1859079 = 2788619) B2788619
theorem B5955083 : Blo 1857630 5955083 := bstep (se 1 (by rfl) ⟨4466312, by rfl⟩ : syracuseStep 5955083 = 8932625) B8932625
theorem B1859087 : Blo 1857630 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B1859131 : Blo 1857630 1859131 := bstep (se 1 (by rfl) ⟨1394348, by rfl⟩ : syracuseStep 1859131 = 2788697) B2788697
theorem B5955133 : Blo 1857630 5955133 := bstep (se 3 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 5955133 = 2233175) B2233175
theorem B3137143 : Blo 1857630 3137143 := bstep (se 1 (by rfl) ⟨2352857, by rfl⟩ : syracuseStep 3137143 = 4705715) B4705715
theorem B1859207 : Blo 1857630 1859207 := bstep (se 1 (by rfl) ⟨1394405, by rfl⟩ : syracuseStep 1859207 = 2788811) B2788811
theorem B1859215 : Blo 1857630 1859215 := bstep (se 1 (by rfl) ⟨1394411, by rfl⟩ : syracuseStep 1859215 = 2788823) B2788823
theorem B1859259 : Blo 1857630 1859259 := bstep (se 1 (by rfl) ⟨1394444, by rfl⟩ : syracuseStep 1859259 = 2788889) B2788889
theorem B6700781 : Blo 1857630 6700781 := bstep (se 3 (by rfl) ⟨1256396, by rfl⟩ : syracuseStep 6700781 = 2512793) B2512793
theorem B1859335 : Blo 1857630 1859335 := bstep (se 1 (by rfl) ⟨1394501, by rfl⟩ : syracuseStep 1859335 = 2789003) B2789003
theorem B1859343 : Blo 1857630 1859343 := bstep (se 1 (by rfl) ⟨1394507, by rfl⟩ : syracuseStep 1859343 = 2789015) B2789015
theorem B3137339 : Blo 1857630 3137339 := bstep (se 1 (by rfl) ⟨2353004, by rfl⟩ : syracuseStep 3137339 = 4706009) B4706009
theorem B1859387 : Blo 1857630 1859387 := bstep (se 1 (by rfl) ⟨1394540, by rfl⟩ : syracuseStep 1859387 = 2789081) B2789081
theorem B1859463 : Blo 1857630 1859463 := bstep (se 1 (by rfl) ⟨1394597, by rfl⟩ : syracuseStep 1859463 = 2789195) B2789195
theorem B1859471 : Blo 1857630 1859471 := bstep (se 1 (by rfl) ⟨1394603, by rfl⟩ : syracuseStep 1859471 = 2789207) B2789207
theorem B30138263 : Blo 1857630 30138263 := bstep (se 1 (by rfl) ⟨22603697, by rfl⟩ : syracuseStep 30138263 = 45207395) B45207395
theorem B1859515 : Blo 1857630 1859515 := bstep (se 1 (by rfl) ⟨1394636, by rfl⟩ : syracuseStep 1859515 = 2789273) B2789273
theorem B15073283 : Blo 1857630 15073283 := bstep (se 1 (by rfl) ⟨11304962, by rfl⟩ : syracuseStep 15073283 = 22609925) B22609925
theorem B9404423 : Blo 1857630 9404423 := bstep (se 1 (by rfl) ⟨7053317, by rfl⟩ : syracuseStep 9404423 = 14106635) B14106635
theorem B3137575 : Blo 1857630 3137575 := bstep (se 1 (by rfl) ⟨2353181, by rfl⟩ : syracuseStep 3137575 = 4706363) B4706363
theorem B1859623 : Blo 1857630 1859623 := bstep (se 1 (by rfl) ⟨1394717, by rfl⟩ : syracuseStep 1859623 = 2789435) B2789435
theorem B14114897 : Blo 1857630 14114897 := bstep (se 2 (by rfl) ⟨5293086, by rfl⟩ : syracuseStep 14114897 = 10586173) B10586173
theorem B2646265 : Blo 1857630 2646265 := bstep (se 2 (by rfl) ⟨992349, by rfl⟩ : syracuseStep 2646265 = 1984699) B1984699
theorem B5955851 : Blo 1857630 5955851 := bstep (se 1 (by rfl) ⟨4466888, by rfl⟩ : syracuseStep 5955851 = 8933777) B8933777
theorem B6275339 : Blo 1857630 6275339 := bstep (se 1 (by rfl) ⟨4706504, by rfl⟩ : syracuseStep 6275339 = 9413009) B9413009
theorem B3137899 : Blo 1857630 3137899 := bstep (se 1 (by rfl) ⟨2353424, by rfl⟩ : syracuseStep 3137899 = 4706849) B4706849
theorem B4702607 : Blo 1857630 4702607 := bstep (se 1 (by rfl) ⟨3526955, by rfl⟩ : syracuseStep 4702607 = 7053911) B7053911
theorem B9404909 : Blo 1857630 9404909 := bstep (se 3 (by rfl) ⟨1763420, by rfl⟩ : syracuseStep 9404909 = 3526841) B3526841
theorem B22921751 : Blo 1857630 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B23241239 : Blo 1857630 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B6275609 : Blo 1857630 6275609 := bstep (se 2 (by rfl) ⟨2353353, by rfl⟩ : syracuseStep 6275609 = 4706707) B4706707
theorem B30138979 : Blo 1857630 30138979 := bstep (se 1 (by rfl) ⟨22604234, by rfl⟩ : syracuseStep 30138979 = 45208469) B45208469
theorem B14508679 : Blo 1857630 14508679 := bstep (se 1 (by rfl) ⟨10881509, by rfl⟩ : syracuseStep 14508679 = 21763019) B21763019
theorem B53609111 : Blo 1857630 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B4702931 : Blo 1857630 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B7054199 : Blo 1857630 7054199 := bstep (se 1 (by rfl) ⟨5290649, by rfl⟩ : syracuseStep 7054199 = 10581299) B10581299
theorem B2089903 : Blo 1857630 2089903 := bstep (se 1 (by rfl) ⟨1567427, by rfl⟩ : syracuseStep 2089903 = 3134855) B3134855
theorem B17859635 : Blo 1857630 17859635 := bstep (se 1 (by rfl) ⟨13394726, by rfl⟩ : syracuseStep 17859635 = 26789453) B26789453
theorem B26797175 : Blo 1857630 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B10585241 : Blo 1857630 10585241 := bstep (se 2 (by rfl) ⟨3969465, by rfl⟩ : syracuseStep 10585241 = 7938931) B7938931
theorem B9405719 : Blo 1857630 9405719 := bstep (se 1 (by rfl) ⟨7054289, by rfl⟩ : syracuseStep 9405719 = 14108579) B14108579
theorem B2090335 : Blo 1857630 2090335 := bstep (se 1 (by rfl) ⟨1567751, by rfl⟩ : syracuseStep 2090335 = 3135503) B3135503
theorem B32179621 : Blo 1857630 32179621 := bstep (se 4 (by rfl) ⟨3016839, by rfl⟩ : syracuseStep 32179621 = 6033679) B6033679
theorem B2786735 : Blo 1857630 2786735 := bstep (se 1 (by rfl) ⟨2090051, by rfl⟩ : syracuseStep 2786735 = 4180103) B4180103
theorem B2352559 : Blo 1857630 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B7939529 : Blo 1857630 7939529 := bstep (se 2 (by rfl) ⟨2977323, by rfl⟩ : syracuseStep 7939529 = 5954647) B5954647
theorem B2786825 : Blo 1857630 2786825 := bstep (se 2 (by rfl) ⟨1045059, by rfl⟩ : syracuseStep 2786825 = 2090119) B2090119
theorem B28608011 : Blo 1857630 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B2786855 : Blo 1857630 2786855 := bstep (se 1 (by rfl) ⟨2090141, by rfl⟩ : syracuseStep 2786855 = 4180283) B4180283
theorem B2786939 : Blo 1857630 2786939 := bstep (se 1 (by rfl) ⟨2090204, by rfl⟩ : syracuseStep 2786939 = 4180409) B4180409
theorem B2090695 : Blo 1857630 2090695 := bstep (se 1 (by rfl) ⟨1568021, by rfl⟩ : syracuseStep 2090695 = 3136043) B3136043
theorem B2787065 : Blo 1857630 2787065 := bstep (se 2 (by rfl) ⟨1045149, by rfl⟩ : syracuseStep 2787065 = 2090299) B2090299
theorem B7055171 : Blo 1857630 7055171 := bstep (se 1 (by rfl) ⟨5291378, by rfl⟩ : syracuseStep 7055171 = 10582757) B10582757
theorem B228984641 : Blo 1857630 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B2787167 : Blo 1857630 2787167 := bstep (se 1 (by rfl) ⟨2090375, by rfl⟩ : syracuseStep 2787167 = 4180751) B4180751
theorem B4704095 : Blo 1857630 4704095 := bstep (se 1 (by rfl) ⟨3528071, by rfl⟩ : syracuseStep 4704095 = 7056143) B7056143
theorem B2787179 : Blo 1857630 2787179 := bstep (se 1 (by rfl) ⟨2090384, by rfl⟩ : syracuseStep 2787179 = 4180769) B4180769
theorem B15075233 : Blo 1857630 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B4179887 : Blo 1857630 4179887 := bstep (se 1 (by rfl) ⟨3134915, by rfl⟩ : syracuseStep 4179887 = 6269831) B6269831
theorem B2787407 : Blo 1857630 2787407 := bstep (se 1 (by rfl) ⟨2090555, by rfl⟩ : syracuseStep 2787407 = 4181111) B4181111
theorem B7940177 : Blo 1857630 7940177 := bstep (se 2 (by rfl) ⟨2977566, by rfl⟩ : syracuseStep 7940177 = 5955133) B5955133
theorem B4180139 : Blo 1857630 4180139 := bstep (se 1 (by rfl) ⟨3135104, by rfl⟩ : syracuseStep 4180139 = 6270209) B6270209
theorem B2787527 : Blo 1857630 2787527 := bstep (se 1 (by rfl) ⟨2090645, by rfl⟩ : syracuseStep 2787527 = 4181291) B4181291
theorem B13060403 : Blo 1857630 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B2787689 : Blo 1857630 2787689 := bstep (se 2 (by rfl) ⟨1045383, by rfl⟩ : syracuseStep 2787689 = 2090767) B2090767
theorem B2787767 : Blo 1857630 2787767 := bstep (se 1 (by rfl) ⟨2090825, by rfl⟩ : syracuseStep 2787767 = 4181651) B4181651
theorem B3017179 : Blo 1857630 3017179 := bstep (se 1 (by rfl) ⟨2262884, by rfl⟩ : syracuseStep 3017179 = 4525769) B4525769
theorem B2787803 : Blo 1857630 2787803 := bstep (se 1 (by rfl) ⟨2090852, by rfl⟩ : syracuseStep 2787803 = 4181705) B4181705
theorem B4467187 : Blo 1857630 4467187 := bstep (se 1 (by rfl) ⟨3350390, by rfl⟩ : syracuseStep 4467187 = 6700781) B6700781
theorem B2091559 : Blo 1857630 2091559 := bstep (se 1 (by rfl) ⟨1568669, by rfl⟩ : syracuseStep 2091559 = 3137339) B3137339
theorem B4180679 : Blo 1857630 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B9407339 : Blo 1857630 9407339 := bstep (se 1 (by rfl) ⟨7055504, by rfl⟩ : syracuseStep 9407339 = 14111009) B14111009
theorem B11905937 : Blo 1857630 11905937 := bstep (se 2 (by rfl) ⟨4464726, by rfl⟩ : syracuseStep 11905937 = 8929453) B8929453
theorem B4705199 : Blo 1857630 4705199 := bstep (se 1 (by rfl) ⟨3528899, by rfl⟩ : syracuseStep 4705199 = 7057799) B7057799
theorem B2788271 : Blo 1857630 2788271 := bstep (se 1 (by rfl) ⟨2091203, by rfl⟩ : syracuseStep 2788271 = 4182407) B4182407
theorem B2788361 : Blo 1857630 2788361 := bstep (se 2 (by rfl) ⟨1045635, by rfl⟩ : syracuseStep 2788361 = 2091271) B2091271
theorem B53586967 : Blo 1857630 53586967 := bstep (se 1 (by rfl) ⟨40190225, by rfl⟩ : syracuseStep 53586967 = 80380451) B80380451
theorem B2788391 : Blo 1857630 2788391 := bstep (se 1 (by rfl) ⟨2091293, by rfl⟩ : syracuseStep 2788391 = 4182587) B4182587
theorem B2788475 : Blo 1857630 2788475 := bstep (se 1 (by rfl) ⟨2091356, by rfl⟩ : syracuseStep 2788475 = 4182713) B4182713
theorem B6032537 : Blo 1857630 6032537 := bstep (se 2 (by rfl) ⟨2262201, by rfl⟩ : syracuseStep 6032537 = 4524403) B4524403
theorem B2788601 : Blo 1857630 2788601 := bstep (se 2 (by rfl) ⟨1045725, by rfl⟩ : syracuseStep 2788601 = 2091451) B2091451
theorem B2788703 : Blo 1857630 2788703 := bstep (se 1 (by rfl) ⟨2091527, by rfl⟩ : syracuseStep 2788703 = 4183055) B4183055
theorem B2788715 : Blo 1857630 2788715 := bstep (se 1 (by rfl) ⟨2091536, by rfl⟩ : syracuseStep 2788715 = 4183073) B4183073
theorem B7056841 : Blo 1857630 7056841 := bstep (se 2 (by rfl) ⟨2646315, by rfl⟩ : syracuseStep 7056841 = 5292631) B5292631
theorem B9407987 : Blo 1857630 9407987 := bstep (se 1 (by rfl) ⟨7055990, by rfl⟩ : syracuseStep 9407987 = 14111981) B14111981
theorem B3968551 : Blo 1857630 3968551 := bstep (se 1 (by rfl) ⟨2976413, by rfl⟩ : syracuseStep 3968551 = 5952827) B5952827
theorem B4181543 : Blo 1857630 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B2788943 : Blo 1857630 2788943 := bstep (se 1 (by rfl) ⟨2091707, by rfl⟩ : syracuseStep 2788943 = 4183415) B4183415
theorem B6270587 : Blo 1857630 6270587 := bstep (se 1 (by rfl) ⟨4702940, by rfl⟩ : syracuseStep 6270587 = 9405881) B9405881
theorem B5951161 : Blo 1857630 5951161 := bstep (se 2 (by rfl) ⟨2231685, by rfl⟩ : syracuseStep 5951161 = 4463371) B4463371
theorem B2789063 : Blo 1857630 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B7057145 : Blo 1857630 7057145 := bstep (se 2 (by rfl) ⟨2646429, by rfl⟩ : syracuseStep 7057145 = 5292859) B5292859
theorem B6270749 : Blo 1857630 6270749 := bstep (se 3 (by rfl) ⟨1175765, by rfl⟩ : syracuseStep 6270749 = 2351531) B2351531
theorem B14110523 : Blo 1857630 14110523 := bstep (se 1 (by rfl) ⟨10582892, by rfl⟩ : syracuseStep 14110523 = 21165785) B21165785
theorem B2789225 : Blo 1857630 2789225 := bstep (se 2 (by rfl) ⟨1045959, by rfl⟩ : syracuseStep 2789225 = 2091919) B2091919
theorem B4181867 : Blo 1857630 4181867 := bstep (se 1 (by rfl) ⟨3136400, by rfl⟩ : syracuseStep 4181867 = 6272801) B6272801
theorem B4181921 : Blo 1857630 4181921 := bstep (se 2 (by rfl) ⟨1568220, by rfl⟩ : syracuseStep 4181921 = 3136441) B3136441
theorem B7057313 : Blo 1857630 7057313 := bstep (se 2 (by rfl) ⟨2646492, by rfl⟩ : syracuseStep 7057313 = 5292985) B5292985
theorem B7057327 : Blo 1857630 7057327 := bstep (se 1 (by rfl) ⟨5292995, by rfl⟩ : syracuseStep 7057327 = 10585991) B10585991
theorem B2789303 : Blo 1857630 2789303 := bstep (se 1 (by rfl) ⟨2091977, by rfl⟩ : syracuseStep 2789303 = 4183955) B4183955
theorem B2789339 : Blo 1857630 2789339 := bstep (se 1 (by rfl) ⟨2092004, by rfl⟩ : syracuseStep 2789339 = 4184009) B4184009
theorem B5951495 : Blo 1857630 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B3526735 : Blo 1857630 3526735 := bstep (se 1 (by rfl) ⟨2645051, by rfl⟩ : syracuseStep 3526735 = 5290103) B5290103
theorem B4706383 : Blo 1857630 4706383 := bstep (se 1 (by rfl) ⟨3529787, by rfl⟩ : syracuseStep 4706383 = 7059575) B7059575
theorem B78385357 : Blo 1857630 78385357 := bstep (se 3 (by rfl) ⟨14697254, by rfl⟩ : syracuseStep 78385357 = 29394509) B29394509
theorem B4182263 : Blo 1857630 4182263 := bstep (se 1 (by rfl) ⟨3136697, by rfl⟩ : syracuseStep 4182263 = 6273395) B6273395
theorem B2978041 : Blo 1857630 2978041 := bstep (se 2 (by rfl) ⟨1116765, by rfl⟩ : syracuseStep 2978041 = 2233531) B2233531
theorem B6271451 : Blo 1857630 6271451 := bstep (se 1 (by rfl) ⟨4703588, by rfl⟩ : syracuseStep 6271451 = 9407177) B9407177
theorem B7942637 : Blo 1857630 7942637 := bstep (se 3 (by rfl) ⟨1489244, by rfl⟩ : syracuseStep 7942637 = 2978489) B2978489
theorem B20091401 : Blo 1857630 20091401 := bstep (se 2 (by rfl) ⟨7534275, by rfl⟩ : syracuseStep 20091401 = 15068551) B15068551
theorem B10580615 : Blo 1857630 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B4707031 : Blo 1857630 4707031 := bstep (se 1 (by rfl) ⟨3530273, by rfl⟩ : syracuseStep 4707031 = 7060547) B7060547
theorem B9409283 : Blo 1857630 9409283 := bstep (se 1 (by rfl) ⟨7056962, by rfl⟩ : syracuseStep 9409283 = 14113925) B14113925
theorem B4182857 : Blo 1857630 4182857 := bstep (se 2 (by rfl) ⟨1568571, by rfl⟩ : syracuseStep 4182857 = 3137143) B3137143
theorem B14119757 : Blo 1857630 14119757 := bstep (se 3 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 14119757 = 5294909) B5294909
theorem B7058285 : Blo 1857630 7058285 := bstep (se 3 (by rfl) ⟨1323428, by rfl⟩ : syracuseStep 7058285 = 2646857) B2646857
theorem B3970055 : Blo 1857630 3970055 := bstep (se 1 (by rfl) ⟨2977541, by rfl⟩ : syracuseStep 3970055 = 5955083) B5955083
theorem B6272153 : Blo 1857630 6272153 := bstep (se 2 (by rfl) ⟨2352057, by rfl⟩ : syracuseStep 6272153 = 4704115) B4704115
theorem B7943321 : Blo 1857630 7943321 := bstep (se 2 (by rfl) ⟨2978745, by rfl⟩ : syracuseStep 7943321 = 5957491) B5957491
theorem B6698141 : Blo 1857630 6698141 := bstep (se 3 (by rfl) ⟨1255901, by rfl⟩ : syracuseStep 6698141 = 2511803) B2511803
theorem B7058603 : Blo 1857630 7058603 := bstep (se 1 (by rfl) ⟨5293952, by rfl⟩ : syracuseStep 7058603 = 10587905) B10587905
theorem B25769177 : Blo 1857630 25769177 := bstep (se 2 (by rfl) ⟨9663441, by rfl⟩ : syracuseStep 25769177 = 19326883) B19326883
theorem B18101519 : Blo 1857630 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B20092175 : Blo 1857630 20092175 := bstep (se 1 (by rfl) ⟨15069131, by rfl⟩ : syracuseStep 20092175 = 30138263) B30138263
theorem B3577193 : Blo 1857630 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B3134983 : Blo 1857630 3134983 := bstep (se 1 (by rfl) ⟨2351237, by rfl⟩ : syracuseStep 3134983 = 4702475) B4702475
theorem B4183649 : Blo 1857630 4183649 := bstep (se 2 (by rfl) ⟨1568868, by rfl⟩ : syracuseStep 4183649 = 3137737) B3137737
theorem B9541259 : Blo 1857630 9541259 := bstep (se 1 (by rfl) ⟨7155944, by rfl⟩ : syracuseStep 9541259 = 14311889) B14311889
theorem B7935839 : Blo 1857630 7935839 := bstep (se 1 (by rfl) ⟨5951879, by rfl⟩ : syracuseStep 7935839 = 11903759) B11903759
theorem B20100959 : Blo 1857630 20100959 := bstep (se 1 (by rfl) ⟨15075719, by rfl⟩ : syracuseStep 20100959 = 30151439) B30151439
theorem B10590047 : Blo 1857630 10590047 := bstep (se 1 (by rfl) ⟨7942535, by rfl⟩ : syracuseStep 10590047 = 15885071) B15885071
theorem B3135415 : Blo 1857630 3135415 := bstep (se 1 (by rfl) ⟨2351561, by rfl⟩ : syracuseStep 3135415 = 4703123) B4703123
theorem B4183991 : Blo 1857630 4183991 := bstep (se 1 (by rfl) ⟨3137993, by rfl⟩ : syracuseStep 4183991 = 6275987) B6275987
theorem B10582073 : Blo 1857630 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B16767065 : Blo 1857630 16767065 := bstep (se 2 (by rfl) ⟨6287649, by rfl⟩ : syracuseStep 16767065 = 12575299) B12575299
theorem B1857631 : Blo 1857630 1857631 := bstep (se 1 (by rfl) ⟨1393223, by rfl⟩ : syracuseStep 1857631 = 2786447) B2786447
theorem B1857659 : Blo 1857630 1857659 := bstep (se 1 (by rfl) ⟨1393244, by rfl⟩ : syracuseStep 1857659 = 2786489) B2786489
theorem B3135611 : Blo 1857630 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B10590365 : Blo 1857630 10590365 := bstep (se 3 (by rfl) ⟨1985693, by rfl⟩ : syracuseStep 10590365 = 3971387) B3971387
theorem B3971243 : Blo 1857630 3971243 := bstep (se 1 (by rfl) ⟨2978432, by rfl⟩ : syracuseStep 3971243 = 5956865) B5956865
theorem B1857711 : Blo 1857630 1857711 := bstep (se 1 (by rfl) ⟨1393283, by rfl⟩ : syracuseStep 1857711 = 2786567) B2786567
theorem B1857735 : Blo 1857630 1857735 := bstep (se 1 (by rfl) ⟨1393301, by rfl⟩ : syracuseStep 1857735 = 2786603) B2786603
theorem B1857755 : Blo 1857630 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B1857831 : Blo 1857630 1857831 := bstep (se 1 (by rfl) ⟨1393373, by rfl⟩ : syracuseStep 1857831 = 2786747) B2786747
theorem B6273341 : Blo 1857630 6273341 := bstep (se 3 (by rfl) ⟨1176251, by rfl⟩ : syracuseStep 6273341 = 2352503) B2352503
theorem B1857871 : Blo 1857630 1857871 := bstep (se 1 (by rfl) ⟨1393403, by rfl⟩ : syracuseStep 1857871 = 2786807) B2786807
theorem B9410903 : Blo 1857630 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B1857887 : Blo 1857630 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B1857915 : Blo 1857630 1857915 := bstep (se 1 (by rfl) ⟨1393436, by rfl⟩ : syracuseStep 1857915 = 2786873) B2786873
theorem B1857967 : Blo 1857630 1857967 := bstep (se 1 (by rfl) ⟨1393475, by rfl⟩ : syracuseStep 1857967 = 2786951) B2786951
theorem B1857991 : Blo 1857630 1857991 := bstep (se 1 (by rfl) ⟨1393493, by rfl⟩ : syracuseStep 1857991 = 2786987) B2786987
theorem B1858011 : Blo 1857630 1858011 := bstep (se 1 (by rfl) ⟨1393508, by rfl⟩ : syracuseStep 1858011 = 2787017) B2787017
theorem B3348955 : Blo 1857630 3348955 := bstep (se 1 (by rfl) ⟨2511716, by rfl⟩ : syracuseStep 3348955 = 5023433) B5023433
theorem B3136009 : Blo 1857630 3136009 := bstep (se 2 (by rfl) ⟨1176003, by rfl⟩ : syracuseStep 3136009 = 2352007) B2352007
theorem B5954057 : Blo 1857630 5954057 := bstep (se 2 (by rfl) ⟨2232771, by rfl⟩ : syracuseStep 5954057 = 4465543) B4465543
theorem B16308769 : Blo 1857630 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B5290535 : Blo 1857630 5290535 := bstep (se 1 (by rfl) ⟨3967901, by rfl⟩ : syracuseStep 5290535 = 7935803) B7935803
theorem B1858087 : Blo 1857630 1858087 := bstep (se 1 (by rfl) ⟨1393565, by rfl⟩ : syracuseStep 1858087 = 2787131) B2787131
theorem B1858127 : Blo 1857630 1858127 := bstep (se 1 (by rfl) ⟨1393595, by rfl⟩ : syracuseStep 1858127 = 2787191) B2787191
theorem B1858143 : Blo 1857630 1858143 := bstep (se 1 (by rfl) ⟨1393607, by rfl⟩ : syracuseStep 1858143 = 2787215) B2787215
theorem B1858171 : Blo 1857630 1858171 := bstep (se 1 (by rfl) ⟨1393628, by rfl⟩ : syracuseStep 1858171 = 2787257) B2787257
theorem B2120315 : Blo 1857630 2120315 := bstep (se 1 (by rfl) ⟨1590236, by rfl⟩ : syracuseStep 2120315 = 3180473) B3180473
theorem B3136171 : Blo 1857630 3136171 := bstep (se 1 (by rfl) ⟨2352128, by rfl⟩ : syracuseStep 3136171 = 4704257) B4704257
theorem B1858223 : Blo 1857630 1858223 := bstep (se 1 (by rfl) ⟨1393667, by rfl⟩ : syracuseStep 1858223 = 2787335) B2787335
theorem B1858247 : Blo 1857630 1858247 := bstep (se 1 (by rfl) ⟨1393685, by rfl⟩ : syracuseStep 1858247 = 2787371) B2787371
theorem B1858267 : Blo 1857630 1858267 := bstep (se 1 (by rfl) ⟨1393700, by rfl⟩ : syracuseStep 1858267 = 2787401) B2787401
theorem B1858343 : Blo 1857630 1858343 := bstep (se 1 (by rfl) ⟨1393757, by rfl⟩ : syracuseStep 1858343 = 2787515) B2787515
theorem B1858383 : Blo 1857630 1858383 := bstep (se 1 (by rfl) ⟨1393787, by rfl⟩ : syracuseStep 1858383 = 2787575) B2787575
theorem B1858399 : Blo 1857630 1858399 := bstep (se 1 (by rfl) ⟨1393799, by rfl⟩ : syracuseStep 1858399 = 2787599) B2787599
theorem B6699871 : Blo 1857630 6699871 := bstep (se 1 (by rfl) ⟨5024903, by rfl⟩ : syracuseStep 6699871 = 10049807) B10049807
theorem B1858427 : Blo 1857630 1858427 := bstep (se 1 (by rfl) ⟨1393820, by rfl⟩ : syracuseStep 1858427 = 2787641) B2787641
theorem B20102033 : Blo 1857630 20102033 := bstep (se 2 (by rfl) ⟨7538262, by rfl⟩ : syracuseStep 20102033 = 15076525) B15076525
theorem B1858479 : Blo 1857630 1858479 := bstep (se 1 (by rfl) ⟨1393859, by rfl⟩ : syracuseStep 1858479 = 2787719) B2787719
theorem B13392823 : Blo 1857630 13392823 := bstep (se 1 (by rfl) ⟨10044617, by rfl⟩ : syracuseStep 13392823 = 20089235) B20089235
theorem B1858503 : Blo 1857630 1858503 := bstep (se 1 (by rfl) ⟨1393877, by rfl⟩ : syracuseStep 1858503 = 2787755) B2787755
theorem B1858523 : Blo 1857630 1858523 := bstep (se 1 (by rfl) ⟨1393892, by rfl⟩ : syracuseStep 1858523 = 2787785) B2787785
theorem B3136475 : Blo 1857630 3136475 := bstep (se 1 (by rfl) ⟨2352356, by rfl⟩ : syracuseStep 3136475 = 4704713) B4704713
theorem B3767315 : Blo 1857630 3767315 := bstep (se 1 (by rfl) ⟨2825486, by rfl⟩ : syracuseStep 3767315 = 5650973) B5650973
theorem B1858599 : Blo 1857630 1858599 := bstep (se 1 (by rfl) ⟨1393949, by rfl⟩ : syracuseStep 1858599 = 2787899) B2787899
theorem B1858639 : Blo 1857630 1858639 := bstep (se 1 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 1858639 = 2787959) B2787959
theorem B1858655 : Blo 1857630 1858655 := bstep (se 1 (by rfl) ⟨1393991, by rfl⟩ : syracuseStep 1858655 = 2787983) B2787983
theorem B1858683 : Blo 1857630 1858683 := bstep (se 1 (by rfl) ⟨1394012, by rfl⟩ : syracuseStep 1858683 = 2788025) B2788025
theorem B6274205 : Blo 1857630 6274205 := bstep (se 3 (by rfl) ⟨1176413, by rfl⟩ : syracuseStep 6274205 = 2352827) B2352827
theorem B1858735 : Blo 1857630 1858735 := bstep (se 1 (by rfl) ⟨1394051, by rfl⟩ : syracuseStep 1858735 = 2788103) B2788103
theorem B1858759 : Blo 1857630 1858759 := bstep (se 1 (by rfl) ⟨1394069, by rfl⟩ : syracuseStep 1858759 = 2788139) B2788139
theorem B3136711 : Blo 1857630 3136711 := bstep (se 1 (by rfl) ⟨2352533, by rfl⟩ : syracuseStep 3136711 = 4705067) B4705067
theorem B1858779 : Blo 1857630 1858779 := bstep (se 1 (by rfl) ⟨1394084, by rfl⟩ : syracuseStep 1858779 = 2788169) B2788169
theorem B1858855 : Blo 1857630 1858855 := bstep (se 1 (by rfl) ⟨1394141, by rfl⟩ : syracuseStep 1858855 = 2788283) B2788283
theorem B6036797 : Blo 1857630 6036797 := bstep (se 3 (by rfl) ⟨1131899, by rfl⟩ : syracuseStep 6036797 = 2263799) B2263799
theorem B1858895 : Blo 1857630 1858895 := bstep (se 1 (by rfl) ⟨1394171, by rfl⟩ : syracuseStep 1858895 = 2788343) B2788343
theorem B1858911 : Blo 1857630 1858911 := bstep (se 1 (by rfl) ⟨1394183, by rfl⟩ : syracuseStep 1858911 = 2788367) B2788367
theorem B3136873 : Blo 1857630 3136873 := bstep (se 2 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 3136873 = 2352655) B2352655
theorem B1858939 : Blo 1857630 1858939 := bstep (se 1 (by rfl) ⟨1394204, by rfl⟩ : syracuseStep 1858939 = 2788409) B2788409
theorem B11902373 : Blo 1857630 11902373 := bstep (se 4 (by rfl) ⟨1115847, by rfl⟩ : syracuseStep 11902373 = 2231695) B2231695
theorem B1858991 : Blo 1857630 1858991 := bstep (se 1 (by rfl) ⟨1394243, by rfl⟩ : syracuseStep 1858991 = 2788487) B2788487
theorem B1859015 : Blo 1857630 1859015 := bstep (se 1 (by rfl) ⟨1394261, by rfl⟩ : syracuseStep 1859015 = 2788523) B2788523
theorem B3767771 : Blo 1857630 3767771 := bstep (se 1 (by rfl) ⟨2825828, by rfl⟩ : syracuseStep 3767771 = 5651657) B5651657
theorem B7536091 : Blo 1857630 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B1859035 : Blo 1857630 1859035 := bstep (se 1 (by rfl) ⟨1394276, by rfl⟩ : syracuseStep 1859035 = 2788553) B2788553
theorem B13401587 : Blo 1857630 13401587 := bstep (se 1 (by rfl) ⟨10051190, by rfl⟩ : syracuseStep 13401587 = 20102381) B20102381
theorem B1859111 : Blo 1857630 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B3530297 : Blo 1857630 3530297 := bstep (se 2 (by rfl) ⟨1323861, by rfl⟩ : syracuseStep 3530297 = 2647723) B2647723
theorem B7536187 : Blo 1857630 7536187 := bstep (se 1 (by rfl) ⟨5652140, by rfl⟩ : syracuseStep 7536187 = 11304281) B11304281
theorem B160849475 : Blo 1857630 160849475 := bstep (se 1 (by rfl) ⟨120637106, by rfl⟩ : syracuseStep 160849475 = 241274213) B241274213
theorem B1859151 : Blo 1857630 1859151 := bstep (se 1 (by rfl) ⟨1394363, by rfl⟩ : syracuseStep 1859151 = 2788727) B2788727
theorem B1859167 : Blo 1857630 1859167 := bstep (se 1 (by rfl) ⟨1394375, by rfl⟩ : syracuseStep 1859167 = 2788751) B2788751
theorem B1859195 : Blo 1857630 1859195 := bstep (se 1 (by rfl) ⟨1394396, by rfl⟩ : syracuseStep 1859195 = 2788793) B2788793
theorem B1859247 : Blo 1857630 1859247 := bstep (se 1 (by rfl) ⟨1394435, by rfl⟩ : syracuseStep 1859247 = 2788871) B2788871
theorem B6274745 : Blo 1857630 6274745 := bstep (se 2 (by rfl) ⟨2353029, by rfl⟩ : syracuseStep 6274745 = 4706059) B4706059
theorem B1859271 : Blo 1857630 1859271 := bstep (se 1 (by rfl) ⟨1394453, by rfl⟩ : syracuseStep 1859271 = 2788907) B2788907
theorem B1859291 : Blo 1857630 1859291 := bstep (se 1 (by rfl) ⟨1394468, by rfl⟩ : syracuseStep 1859291 = 2788937) B2788937
theorem B1859367 : Blo 1857630 1859367 := bstep (se 1 (by rfl) ⟨1394525, by rfl⟩ : syracuseStep 1859367 = 2789051) B2789051
theorem B1859407 : Blo 1857630 1859407 := bstep (se 1 (by rfl) ⟨1394555, by rfl⟩ : syracuseStep 1859407 = 2789111) B2789111
theorem B1859423 : Blo 1857630 1859423 := bstep (se 1 (by rfl) ⟨1394567, by rfl⟩ : syracuseStep 1859423 = 2789135) B2789135
theorem B6700909 : Blo 1857630 6700909 := bstep (se 3 (by rfl) ⟨1256420, by rfl⟩ : syracuseStep 6700909 = 2512841) B2512841
theorem B1859451 : Blo 1857630 1859451 := bstep (se 1 (by rfl) ⟨1394588, by rfl⟩ : syracuseStep 1859451 = 2789177) B2789177
theorem B1859503 : Blo 1857630 1859503 := bstep (se 1 (by rfl) ⟨1394627, by rfl⟩ : syracuseStep 1859503 = 2789255) B2789255
theorem B3137467 : Blo 1857630 3137467 := bstep (se 1 (by rfl) ⟨2353100, by rfl⟩ : syracuseStep 3137467 = 4706201) B4706201
theorem B1859527 : Blo 1857630 1859527 := bstep (se 1 (by rfl) ⟨1394645, by rfl⟩ : syracuseStep 1859527 = 2789291) B2789291
theorem B1859547 : Blo 1857630 1859547 := bstep (se 1 (by rfl) ⟨1394660, by rfl⟩ : syracuseStep 1859547 = 2789321) B2789321
theorem B4702313 : Blo 1857630 4702313 := bstep (se 2 (by rfl) ⟨1763367, by rfl⟩ : syracuseStep 4702313 = 3526735) B3526735
theorem B6275177 : Blo 1857630 6275177 := bstep (se 2 (by rfl) ⟨2353191, by rfl⟩ : syracuseStep 6275177 = 4706383) B4706383
theorem B44712173 : Blo 1857630 44712173 := bstep (se 3 (by rfl) ⟨8383532, by rfl⟩ : syracuseStep 44712173 = 16767065) B16767065
theorem B104513809 : Blo 1857630 104513809 := bstep (se 2 (by rfl) ⟨39192678, by rfl⟩ : syracuseStep 104513809 = 78385357) B78385357
theorem B13394267 : Blo 1857630 13394267 := bstep (se 1 (by rfl) ⟨10045700, by rfl⟩ : syracuseStep 13394267 = 20091401) B20091401
theorem B7053743 : Blo 1857630 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B9413171 : Blo 1857630 9413171 := bstep (se 1 (by rfl) ⟨7059878, by rfl⟩ : syracuseStep 9413171 = 14119757) B14119757
theorem B4702799 : Blo 1857630 4702799 := bstep (se 1 (by rfl) ⟨3527099, by rfl⟩ : syracuseStep 4702799 = 7054199) B7054199
theorem B5956249 : Blo 1857630 5956249 := bstep (se 2 (by rfl) ⟨2233593, by rfl⟩ : syracuseStep 5956249 = 4467187) B4467187
theorem B2646703 : Blo 1857630 2646703 := bstep (se 1 (by rfl) ⟨1985027, by rfl⟩ : syracuseStep 2646703 = 3970055) B3970055
theorem B4465427 : Blo 1857630 4465427 := bstep (se 1 (by rfl) ⟨3349070, by rfl⟩ : syracuseStep 4465427 = 6698141) B6698141
theorem B17179451 : Blo 1857630 17179451 := bstep (se 1 (by rfl) ⟨12884588, by rfl⟩ : syracuseStep 17179451 = 25769177) B25769177
theorem B12067679 : Blo 1857630 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B13394783 : Blo 1857630 13394783 := bstep (se 1 (by rfl) ⟨10046087, by rfl⟩ : syracuseStep 13394783 = 20092175) B20092175
theorem B2384795 : Blo 1857630 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B6276041 : Blo 1857630 6276041 := bstep (se 2 (by rfl) ⟨2353515, by rfl⟩ : syracuseStep 6276041 = 4707031) B4707031
theorem B5293019 : Blo 1857630 5293019 := bstep (se 1 (by rfl) ⟨3969764, by rfl⟩ : syracuseStep 5293019 = 7939529) B7939529
theorem B19072007 : Blo 1857630 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B4703447 : Blo 1857630 4703447 := bstep (se 1 (by rfl) ⟨3527585, by rfl⟩ : syracuseStep 4703447 = 7055171) B7055171
theorem B2786537 : Blo 1857630 2786537 := bstep (se 2 (by rfl) ⟨1044951, by rfl⟩ : syracuseStep 2786537 = 2089903) B2089903
theorem B2786591 : Blo 1857630 2786591 := bstep (se 1 (by rfl) ⟨2089943, by rfl⟩ : syracuseStep 2786591 = 4179887) B4179887
theorem B7054715 : Blo 1857630 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B5293451 : Blo 1857630 5293451 := bstep (se 1 (by rfl) ⟨3970088, by rfl⟩ : syracuseStep 5293451 = 7940177) B7940177
theorem B2090407 : Blo 1857630 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B14108093 : Blo 1857630 14108093 := bstep (se 3 (by rfl) ⟨2645267, by rfl⟩ : syracuseStep 14108093 = 5290535) B5290535
theorem B2786759 : Blo 1857630 2786759 := bstep (se 1 (by rfl) ⟨2090069, by rfl⟩ : syracuseStep 2786759 = 4180139) B4180139
theorem B2647495 : Blo 1857630 2647495 := bstep (se 1 (by rfl) ⟨1985621, by rfl⟩ : syracuseStep 2647495 = 3971243) B3971243
theorem B5654173 : Blo 1857630 5654173 := bstep (se 3 (by rfl) ⟨1060157, by rfl⟩ : syracuseStep 5654173 = 2120315) B2120315
theorem B2787113 : Blo 1857630 2787113 := bstep (se 2 (by rfl) ⟨1045167, by rfl⟩ : syracuseStep 2787113 = 2090335) B2090335
theorem B2787119 : Blo 1857630 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B2090983 : Blo 1857630 2090983 := bstep (se 1 (by rfl) ⟨1568237, by rfl⟩ : syracuseStep 2090983 = 3136475) B3136475
theorem B4179977 : Blo 1857630 4179977 := bstep (se 2 (by rfl) ⟨1567491, by rfl⟩ : syracuseStep 4179977 = 3134983) B3134983
theorem B4024531 : Blo 1857630 4024531 := bstep (se 1 (by rfl) ⟨3018398, by rfl⟩ : syracuseStep 4024531 = 6036797) B6036797
theorem B2787593 : Blo 1857630 2787593 := bstep (se 2 (by rfl) ⟨1045347, by rfl⟩ : syracuseStep 2787593 = 2090695) B2090695
theorem B2787695 : Blo 1857630 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B2353531 : Blo 1857630 2353531 := bstep (se 1 (by rfl) ⟨1765148, by rfl⟩ : syracuseStep 2353531 = 3530297) B3530297
theorem B4180391 : Blo 1857630 4180391 := bstep (se 1 (by rfl) ⟨3135293, by rfl⟩ : syracuseStep 4180391 = 6270587) B6270587
theorem B16091621 : Blo 1857630 16091621 := bstep (se 4 (by rfl) ⟨1508589, by rfl⟩ : syracuseStep 16091621 = 3017179) B3017179
theorem B17861093 : Blo 1857630 17861093 := bstep (se 4 (by rfl) ⟨1674477, by rfl⟩ : syracuseStep 17861093 = 3348955) B3348955
theorem B4704763 : Blo 1857630 4704763 := bstep (se 1 (by rfl) ⟨3528572, by rfl⟩ : syracuseStep 4704763 = 7057145) B7057145
theorem B4180499 : Blo 1857630 4180499 := bstep (se 1 (by rfl) ⟨3135374, by rfl⟩ : syracuseStep 4180499 = 6270749) B6270749
theorem B9407015 : Blo 1857630 9407015 := bstep (se 1 (by rfl) ⟨7055261, by rfl⟩ : syracuseStep 9407015 = 14110523) B14110523
theorem B2787911 : Blo 1857630 2787911 := bstep (se 1 (by rfl) ⟨2090933, by rfl⟩ : syracuseStep 2787911 = 4181867) B4181867
theorem B4180553 : Blo 1857630 4180553 := bstep (se 2 (by rfl) ⟨1567707, by rfl⟩ : syracuseStep 4180553 = 3135415) B3135415
theorem B2787947 : Blo 1857630 2787947 := bstep (se 1 (by rfl) ⟨2090960, by rfl⟩ : syracuseStep 2787947 = 4181921) B4181921
theorem B4704875 : Blo 1857630 4704875 := bstep (se 1 (by rfl) ⟨3528656, by rfl⟩ : syracuseStep 4704875 = 7057313) B7057313
theorem B6269615 : Blo 1857630 6269615 := bstep (se 1 (by rfl) ⟨4702211, by rfl⟩ : syracuseStep 6269615 = 9404423) B9404423
theorem B3967663 : Blo 1857630 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B10046173 : Blo 1857630 10046173 := bstep (se 3 (by rfl) ⟨1883657, by rfl⟩ : syracuseStep 10046173 = 3767315) B3767315
theorem B2788175 : Blo 1857630 2788175 := bstep (se 1 (by rfl) ⟨2091131, by rfl⟩ : syracuseStep 2788175 = 4182263) B4182263
theorem B4180967 : Blo 1857630 4180967 := bstep (se 1 (by rfl) ⟨3135725, by rfl⟩ : syracuseStep 4180967 = 6271451) B6271451
theorem B6269939 : Blo 1857630 6269939 := bstep (se 1 (by rfl) ⟨4702454, by rfl⟩ : syracuseStep 6269939 = 9404909) B9404909
theorem B15281167 : Blo 1857630 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B15494159 : Blo 1857630 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B2788571 : Blo 1857630 2788571 := bstep (se 1 (by rfl) ⟨2091428, by rfl⟩ : syracuseStep 2788571 = 4182857) B4182857
theorem B4705523 : Blo 1857630 4705523 := bstep (se 1 (by rfl) ⟨3529142, by rfl⟩ : syracuseStep 4705523 = 7058285) B7058285
theorem B4181345 : Blo 1857630 4181345 := bstep (se 2 (by rfl) ⟨1568004, by rfl⟩ : syracuseStep 4181345 = 3136009) B3136009
theorem B11906423 : Blo 1857630 11906423 := bstep (se 1 (by rfl) ⟨8929817, by rfl⟩ : syracuseStep 11906423 = 17859635) B17859635
theorem B21745025 : Blo 1857630 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B2788745 : Blo 1857630 2788745 := bstep (se 2 (by rfl) ⟨1045779, by rfl⟩ : syracuseStep 2788745 = 2091559) B2091559
theorem B4181435 : Blo 1857630 4181435 := bstep (se 1 (by rfl) ⟨3136076, by rfl⟩ : syracuseStep 4181435 = 6272153) B6272153
theorem B7056827 : Blo 1857630 7056827 := bstep (se 1 (by rfl) ⟨5292620, by rfl⟩ : syracuseStep 7056827 = 10585241) B10585241
theorem B5295547 : Blo 1857630 5295547 := bstep (se 1 (by rfl) ⟨3971660, by rfl⟩ : syracuseStep 5295547 = 7943321) B7943321
theorem B4705735 : Blo 1857630 4705735 := bstep (se 1 (by rfl) ⟨3529301, by rfl⟩ : syracuseStep 4705735 = 7058603) B7058603
theorem B40185305 : Blo 1857630 40185305 := bstep (se 2 (by rfl) ⟨15069489, by rfl⟩ : syracuseStep 40185305 = 30138979) B30138979
theorem B19344905 : Blo 1857630 19344905 := bstep (se 2 (by rfl) ⟨7254339, by rfl⟩ : syracuseStep 19344905 = 14508679) B14508679
theorem B6270479 : Blo 1857630 6270479 := bstep (se 1 (by rfl) ⟨4702859, by rfl⟩ : syracuseStep 6270479 = 9405719) B9405719
theorem B4181561 : Blo 1857630 4181561 := bstep (se 2 (by rfl) ⟨1568085, by rfl⟩ : syracuseStep 4181561 = 3136171) B3136171
theorem B2789099 : Blo 1857630 2789099 := bstep (se 1 (by rfl) ⟨2091824, by rfl⟩ : syracuseStep 2789099 = 4183649) B4183649
theorem B6360839 : Blo 1857630 6360839 := bstep (se 1 (by rfl) ⟨4770629, by rfl⟩ : syracuseStep 6360839 = 9541259) B9541259
theorem B8933161 : Blo 1857630 8933161 := bstep (se 2 (by rfl) ⟨3349935, by rfl⟩ : syracuseStep 8933161 = 6699871) B6699871
theorem B21180365 : Blo 1857630 21180365 := bstep (se 3 (by rfl) ⟨3971318, by rfl⟩ : syracuseStep 21180365 = 7942637) B7942637
theorem B2789327 : Blo 1857630 2789327 := bstep (se 1 (by rfl) ⟨2091995, by rfl⟩ : syracuseStep 2789327 = 4183991) B4183991
theorem B4182227 : Blo 1857630 4182227 := bstep (se 1 (by rfl) ⟨3136670, by rfl⟩ : syracuseStep 4182227 = 6273341) B6273341
theorem B4182281 : Blo 1857630 4182281 := bstep (se 2 (by rfl) ⟨1568355, by rfl⟩ : syracuseStep 4182281 = 3136711) B3136711
theorem B3969371 : Blo 1857630 3969371 := bstep (se 1 (by rfl) ⟨2977028, by rfl⟩ : syracuseStep 3969371 = 5954057) B5954057
theorem B4182497 : Blo 1857630 4182497 := bstep (se 2 (by rfl) ⟨1568436, by rfl⟩ : syracuseStep 4182497 = 3136873) B3136873
theorem B42906161 : Blo 1857630 42906161 := bstep (se 2 (by rfl) ⟨16089810, by rfl⟩ : syracuseStep 42906161 = 32179621) B32179621
theorem B6271559 : Blo 1857630 6271559 := bstep (se 1 (by rfl) ⟨4703669, by rfl⟩ : syracuseStep 6271559 = 9407339) B9407339
theorem B9409121 : Blo 1857630 9409121 := bstep (se 2 (by rfl) ⟨3528420, by rfl⟩ : syracuseStep 9409121 = 7056841) B7056841
theorem B10048121 : Blo 1857630 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B10048249 : Blo 1857630 10048249 := bstep (se 2 (by rfl) ⟨3768093, by rfl⟩ : syracuseStep 10048249 = 7536187) B7536187
theorem B4182803 : Blo 1857630 4182803 := bstep (se 1 (by rfl) ⟨3137102, by rfl⟩ : syracuseStep 4182803 = 6274205) B6274205
theorem B7934881 : Blo 1857630 7934881 := bstep (se 2 (by rfl) ⟨2975580, by rfl⟩ : syracuseStep 7934881 = 5951161) B5951161
theorem B7934915 : Blo 1857630 7934915 := bstep (se 1 (by rfl) ⟨5951186, by rfl⟩ : syracuseStep 7934915 = 11902373) B11902373
theorem B2511847 : Blo 1857630 2511847 := bstep (se 1 (by rfl) ⟨1883885, by rfl⟩ : syracuseStep 2511847 = 3767771) B3767771
theorem B6271991 : Blo 1857630 6271991 := bstep (se 1 (by rfl) ⟨4703993, by rfl⟩ : syracuseStep 6271991 = 9407987) B9407987
theorem B8934391 : Blo 1857630 8934391 := bstep (se 1 (by rfl) ⟨6700793, by rfl⟩ : syracuseStep 8934391 = 13401587) B13401587
theorem B53605421 : Blo 1857630 53605421 := bstep (se 3 (by rfl) ⟨10051016, by rfl⟩ : syracuseStep 53605421 = 20102033) B20102033
theorem B4183163 : Blo 1857630 4183163 := bstep (se 1 (by rfl) ⟨3137372, by rfl⟩ : syracuseStep 4183163 = 6274745) B6274745
theorem B8934545 : Blo 1857630 8934545 := bstep (se 2 (by rfl) ⟨3350454, by rfl⟩ : syracuseStep 8934545 = 6700909) B6700909
theorem B9409769 : Blo 1857630 9409769 := bstep (se 2 (by rfl) ⟨3528663, by rfl⟩ : syracuseStep 9409769 = 7057327) B7057327
theorem B4183289 : Blo 1857630 4183289 := bstep (se 2 (by rfl) ⟨1568733, by rfl⟩ : syracuseStep 4183289 = 3137467) B3137467
theorem B10048855 : Blo 1857630 10048855 := bstep (se 1 (by rfl) ⟨7536641, by rfl⟩ : syracuseStep 10048855 = 15073283) B15073283
theorem B4183433 : Blo 1857630 4183433 := bstep (se 2 (by rfl) ⟨1568787, by rfl⟩ : syracuseStep 4183433 = 3137575) B3137575
theorem B9409931 : Blo 1857630 9409931 := bstep (se 1 (by rfl) ⟨7057448, by rfl⟩ : syracuseStep 9409931 = 14114897) B14114897
theorem B3970567 : Blo 1857630 3970567 := bstep (se 1 (by rfl) ⟨2977925, by rfl⟩ : syracuseStep 3970567 = 5955851) B5955851
theorem B4183559 : Blo 1857630 4183559 := bstep (se 1 (by rfl) ⟨3137669, by rfl⟩ : syracuseStep 4183559 = 6275339) B6275339
theorem B3135071 : Blo 1857630 3135071 := bstep (se 1 (by rfl) ⟨2351303, by rfl⟩ : syracuseStep 3135071 = 4702607) B4702607
theorem B3528353 : Blo 1857630 3528353 := bstep (se 2 (by rfl) ⟨1323132, by rfl⟩ : syracuseStep 3528353 = 2646265) B2646265
theorem B3970721 : Blo 1857630 3970721 := bstep (se 2 (by rfl) ⟨1489020, by rfl⟩ : syracuseStep 3970721 = 2978041) B2978041
theorem B4183739 : Blo 1857630 4183739 := bstep (se 1 (by rfl) ⟨3137804, by rfl⟩ : syracuseStep 4183739 = 6275609) B6275609
theorem B35739407 : Blo 1857630 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B3135287 : Blo 1857630 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B4183865 : Blo 1857630 4183865 := bstep (se 2 (by rfl) ⟨1568949, by rfl⟩ : syracuseStep 4183865 = 3137899) B3137899
theorem B6272855 : Blo 1857630 6272855 := bstep (se 1 (by rfl) ⟨4704641, by rfl⟩ : syracuseStep 6272855 = 9409283) B9409283
theorem B17864783 : Blo 1857630 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B1857823 : Blo 1857630 1857823 := bstep (se 1 (by rfl) ⟨1393367, by rfl⟩ : syracuseStep 1857823 = 2786735) B2786735
theorem B1857883 : Blo 1857630 1857883 := bstep (se 1 (by rfl) ⟨1393412, by rfl⟩ : syracuseStep 1857883 = 2786825) B2786825
theorem B1857903 : Blo 1857630 1857903 := bstep (se 1 (by rfl) ⟨1393427, by rfl⟩ : syracuseStep 1857903 = 2786855) B2786855
theorem B1857959 : Blo 1857630 1857959 := bstep (se 1 (by rfl) ⟨1393469, by rfl⟩ : syracuseStep 1857959 = 2786939) B2786939
theorem B1858043 : Blo 1857630 1858043 := bstep (se 1 (by rfl) ⟨1393532, by rfl⟩ : syracuseStep 1858043 = 2787065) B2787065
theorem B152656427 : Blo 1857630 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B5290559 : Blo 1857630 5290559 := bstep (se 1 (by rfl) ⟨3967919, by rfl⟩ : syracuseStep 5290559 = 7935839) B7935839
theorem B1858111 : Blo 1857630 1858111 := bstep (se 1 (by rfl) ⟨1393583, by rfl⟩ : syracuseStep 1858111 = 2787167) B2787167
theorem B3136063 : Blo 1857630 3136063 := bstep (se 1 (by rfl) ⟨2352047, by rfl⟩ : syracuseStep 3136063 = 4704095) B4704095
theorem B13400639 : Blo 1857630 13400639 := bstep (se 1 (by rfl) ⟨10050479, by rfl⟩ : syracuseStep 13400639 = 20100959) B20100959
theorem B7060031 : Blo 1857630 7060031 := bstep (se 1 (by rfl) ⟨5295023, by rfl⟩ : syracuseStep 7060031 = 10590047) B10590047
theorem B1858119 : Blo 1857630 1858119 := bstep (se 1 (by rfl) ⟨1393589, by rfl⟩ : syracuseStep 1858119 = 2787179) B2787179
theorem B17857097 : Blo 1857630 17857097 := bstep (se 2 (by rfl) ⟨6696411, by rfl⟩ : syracuseStep 17857097 = 13392823) B13392823
theorem B10050155 : Blo 1857630 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B71449289 : Blo 1857630 71449289 := bstep (se 2 (by rfl) ⟨26793483, by rfl⟩ : syracuseStep 71449289 = 53586967) B53586967
theorem B1858271 : Blo 1857630 1858271 := bstep (se 1 (by rfl) ⟨1393703, by rfl⟩ : syracuseStep 1858271 = 2787407) B2787407
theorem B7060243 : Blo 1857630 7060243 := bstep (se 1 (by rfl) ⟨5295182, by rfl⟩ : syracuseStep 7060243 = 10590365) B10590365
theorem B1858351 : Blo 1857630 1858351 := bstep (se 1 (by rfl) ⟨1393763, by rfl⟩ : syracuseStep 1858351 = 2787527) B2787527
theorem B8706935 : Blo 1857630 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B6273935 : Blo 1857630 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1858459 : Blo 1857630 1858459 := bstep (se 1 (by rfl) ⟨1393844, by rfl⟩ : syracuseStep 1858459 = 2787689) B2787689
theorem B1858511 : Blo 1857630 1858511 := bstep (se 1 (by rfl) ⟨1393883, by rfl⟩ : syracuseStep 1858511 = 2787767) B2787767
theorem B1858535 : Blo 1857630 1858535 := bstep (se 1 (by rfl) ⟨1393901, by rfl⟩ : syracuseStep 1858535 = 2787803) B2787803
theorem B3136745 : Blo 1857630 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B7937291 : Blo 1857630 7937291 := bstep (se 1 (by rfl) ⟨5952968, by rfl⟩ : syracuseStep 7937291 = 11905937) B11905937
theorem B3136799 : Blo 1857630 3136799 := bstep (se 1 (by rfl) ⟨2352599, by rfl⟩ : syracuseStep 3136799 = 4705199) B4705199
theorem B1858847 : Blo 1857630 1858847 := bstep (se 1 (by rfl) ⟨1394135, by rfl⟩ : syracuseStep 1858847 = 2788271) B2788271
theorem B1858907 : Blo 1857630 1858907 := bstep (se 1 (by rfl) ⟨1394180, by rfl⟩ : syracuseStep 1858907 = 2788361) B2788361
theorem B1858927 : Blo 1857630 1858927 := bstep (se 1 (by rfl) ⟨1394195, by rfl⟩ : syracuseStep 1858927 = 2788391) B2788391
theorem B5291401 : Blo 1857630 5291401 := bstep (se 2 (by rfl) ⟨1984275, by rfl⟩ : syracuseStep 5291401 = 3968551) B3968551
theorem B1858983 : Blo 1857630 1858983 := bstep (se 1 (by rfl) ⟨1394237, by rfl⟩ : syracuseStep 1858983 = 2788475) B2788475
theorem B4021691 : Blo 1857630 4021691 := bstep (se 1 (by rfl) ⟨3016268, by rfl⟩ : syracuseStep 4021691 = 6032537) B6032537
theorem B1859067 : Blo 1857630 1859067 := bstep (se 1 (by rfl) ⟨1394300, by rfl⟩ : syracuseStep 1859067 = 2788601) B2788601
theorem B1859135 : Blo 1857630 1859135 := bstep (se 1 (by rfl) ⟨1394351, by rfl⟩ : syracuseStep 1859135 = 2788703) B2788703
theorem B1859143 : Blo 1857630 1859143 := bstep (se 1 (by rfl) ⟨1394357, by rfl⟩ : syracuseStep 1859143 = 2788715) B2788715
theorem B107232983 : Blo 1857630 107232983 := bstep (se 1 (by rfl) ⟨80424737, by rfl⟩ : syracuseStep 107232983 = 160849475) B160849475
theorem B1859295 : Blo 1857630 1859295 := bstep (se 1 (by rfl) ⟨1394471, by rfl⟩ : syracuseStep 1859295 = 2788943) B2788943
theorem B1859375 : Blo 1857630 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B1859483 : Blo 1857630 1859483 := bstep (se 1 (by rfl) ⟨1394612, by rfl⟩ : syracuseStep 1859483 = 2789225) B2789225
theorem B1859535 : Blo 1857630 1859535 := bstep (se 1 (by rfl) ⟨1394651, by rfl⟩ : syracuseStep 1859535 = 2789303) B2789303
theorem B1859559 : Blo 1857630 1859559 := bstep (se 1 (by rfl) ⟨1394669, by rfl⟩ : syracuseStep 1859559 = 2789339) B2789339
theorem B8929511 : Blo 1857630 8929511 := bstep (se 1 (by rfl) ⟨6697133, by rfl⟩ : syracuseStep 8929511 = 13394267) B13394267
theorem B4702495 : Blo 1857630 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B6275447 : Blo 1857630 6275447 := bstep (se 1 (by rfl) ⟨4706585, by rfl⟩ : syracuseStep 6275447 = 9413171) B9413171
theorem B3138041 : Blo 1857630 3138041 := bstep (se 2 (by rfl) ⟨1176765, by rfl⟩ : syracuseStep 3138041 = 2353531) B2353531
theorem B11452967 : Blo 1857630 11452967 := bstep (se 1 (by rfl) ⟨8589725, by rfl⟩ : syracuseStep 11452967 = 17179451) B17179451
theorem B8045119 : Blo 1857630 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B8929855 : Blo 1857630 8929855 := bstep (se 1 (by rfl) ⟨6697391, by rfl⟩ : syracuseStep 8929855 = 13394783) B13394783
theorem B12714671 : Blo 1857630 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B5956363 : Blo 1857630 5956363 := bstep (se 1 (by rfl) ⟨4467272, by rfl⟩ : syracuseStep 5956363 = 8934545) B8934545
theorem B10584989 : Blo 1857630 10584989 := bstep (se 3 (by rfl) ⟨1984685, by rfl⟩ : syracuseStep 10584989 = 3969371) B3969371
theorem B4703143 : Blo 1857630 4703143 := bstep (se 1 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 4703143 = 7054715) B7054715
theorem B13394897 : Blo 1857630 13394897 := bstep (se 2 (by rfl) ⟨5023086, by rfl⟩ : syracuseStep 13394897 = 10046173) B10046173
theorem B9405395 : Blo 1857630 9405395 := bstep (se 1 (by rfl) ⟨7054046, by rfl⟩ : syracuseStep 9405395 = 14108093) B14108093
theorem B9413657 : Blo 1857630 9413657 := bstep (se 2 (by rfl) ⟨3530121, by rfl⟩ : syracuseStep 9413657 = 7060243) B7060243
theorem B14115869 : Blo 1857630 14115869 := bstep (se 3 (by rfl) ⟨2646725, by rfl⟩ : syracuseStep 14115869 = 5293451) B5293451
theorem B2090047 : Blo 1857630 2090047 := bstep (se 1 (by rfl) ⟨1567535, by rfl⟩ : syracuseStep 2090047 = 3135071) B3135071
theorem B21464165 : Blo 1857630 21464165 := bstep (se 4 (by rfl) ⟨2012265, by rfl⟩ : syracuseStep 21464165 = 4024531) B4024531
theorem B2352235 : Blo 1857630 2352235 := bstep (se 1 (by rfl) ⟨1764176, by rfl⟩ : syracuseStep 2352235 = 3528353) B3528353
theorem B10724509 : Blo 1857630 10724509 := bstep (se 3 (by rfl) ⟨2010845, by rfl⟩ : syracuseStep 10724509 = 4021691) B4021691
theorem B2090191 : Blo 1857630 2090191 := bstep (se 1 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 2090191 = 3135287) B3135287
theorem B11912521 : Blo 1857630 11912521 := bstep (se 2 (by rfl) ⟨4467195, by rfl⟩ : syracuseStep 11912521 = 8934391) B8934391
theorem B2786651 : Blo 1857630 2786651 := bstep (se 1 (by rfl) ⟨2089988, by rfl⟩ : syracuseStep 2786651 = 4179977) B4179977
theorem B2786927 : Blo 1857630 2786927 := bstep (se 1 (by rfl) ⟨2090195, by rfl⟩ : syracuseStep 2786927 = 4180391) B4180391
theorem B2786999 : Blo 1857630 2786999 := bstep (se 1 (by rfl) ⟨2090249, by rfl⟩ : syracuseStep 2786999 = 4180499) B4180499
theorem B101770951 : Blo 1857630 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B11904731 : Blo 1857630 11904731 := bstep (se 1 (by rfl) ⟨8928548, by rfl⟩ : syracuseStep 11904731 = 17857097) B17857097
theorem B2787035 : Blo 1857630 2787035 := bstep (se 1 (by rfl) ⟨2090276, by rfl⟩ : syracuseStep 2787035 = 4180553) B4180553
theorem B4179743 : Blo 1857630 4179743 := bstep (se 1 (by rfl) ⟨3134807, by rfl⟩ : syracuseStep 4179743 = 6269615) B6269615
theorem B7055201 : Blo 1857630 7055201 := bstep (se 2 (by rfl) ⟨2645700, by rfl⟩ : syracuseStep 7055201 = 5291401) B5291401
theorem B2787209 : Blo 1857630 2787209 := bstep (se 2 (by rfl) ⟨1045203, by rfl⟩ : syracuseStep 2787209 = 2090407) B2090407
theorem B2787311 : Blo 1857630 2787311 := bstep (se 1 (by rfl) ⟨2090483, by rfl⟩ : syracuseStep 2787311 = 4180967) B4180967
theorem B4179959 : Blo 1857630 4179959 := bstep (se 1 (by rfl) ⟨3134969, by rfl⟩ : syracuseStep 4179959 = 6269939) B6269939
theorem B5294089 : Blo 1857630 5294089 := bstep (se 2 (by rfl) ⟨1985283, by rfl⟩ : syracuseStep 5294089 = 3970567) B3970567
theorem B2091163 : Blo 1857630 2091163 := bstep (se 1 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 2091163 = 3136745) B3136745
theorem B2091199 : Blo 1857630 2091199 := bstep (se 1 (by rfl) ⟨1568399, by rfl⟩ : syracuseStep 2091199 = 3136799) B3136799
theorem B7538897 : Blo 1857630 7538897 := bstep (se 2 (by rfl) ⟨2827086, by rfl⟩ : syracuseStep 7538897 = 5654173) B5654173
theorem B2787563 : Blo 1857630 2787563 := bstep (se 1 (by rfl) ⟨2090672, by rfl⟩ : syracuseStep 2787563 = 4181345) B4181345
theorem B2787623 : Blo 1857630 2787623 := bstep (se 1 (by rfl) ⟨2090717, by rfl⟩ : syracuseStep 2787623 = 4181435) B4181435
theorem B4704551 : Blo 1857630 4704551 := bstep (se 1 (by rfl) ⟨3528413, by rfl⟩ : syracuseStep 4704551 = 7056827) B7056827
theorem B26790203 : Blo 1857630 26790203 := bstep (se 1 (by rfl) ⟨20092652, by rfl⟩ : syracuseStep 26790203 = 40185305) B40185305
theorem B12896603 : Blo 1857630 12896603 := bstep (se 1 (by rfl) ⟨9672452, by rfl⟩ : syracuseStep 12896603 = 19344905) B19344905
theorem B4180319 : Blo 1857630 4180319 := bstep (se 1 (by rfl) ⟨3135239, by rfl⟩ : syracuseStep 4180319 = 6270479) B6270479
theorem B2787707 : Blo 1857630 2787707 := bstep (se 1 (by rfl) ⟨2090780, by rfl⟩ : syracuseStep 2787707 = 4181561) B4181561
theorem B6359453 : Blo 1857630 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B2787977 : Blo 1857630 2787977 := bstep (se 2 (by rfl) ⟨1045491, by rfl⟩ : syracuseStep 2787977 = 2090983) B2090983
theorem B2788151 : Blo 1857630 2788151 := bstep (se 1 (by rfl) ⟨2091113, by rfl⟩ : syracuseStep 2788151 = 4182227) B4182227
theorem B2788187 : Blo 1857630 2788187 := bstep (se 1 (by rfl) ⟨2091140, by rfl⟩ : syracuseStep 2788187 = 4182281) B4182281
theorem B2788331 : Blo 1857630 2788331 := bstep (se 1 (by rfl) ⟨2091248, by rfl⟩ : syracuseStep 2788331 = 4182497) B4182497
theorem B4181039 : Blo 1857630 4181039 := bstep (se 1 (by rfl) ⟨3135779, by rfl⟩ : syracuseStep 4181039 = 6271559) B6271559
theorem B2788535 : Blo 1857630 2788535 := bstep (se 1 (by rfl) ⟨2091401, by rfl⟩ : syracuseStep 2788535 = 4182803) B4182803
theorem B4181327 : Blo 1857630 4181327 := bstep (se 1 (by rfl) ⟨3135995, by rfl⟩ : syracuseStep 4181327 = 6271991) B6271991
theorem B35736947 : Blo 1857630 35736947 := bstep (se 1 (by rfl) ⟨26802710, by rfl⟩ : syracuseStep 35736947 = 53605421) B53605421
theorem B2788775 : Blo 1857630 2788775 := bstep (se 1 (by rfl) ⟨2091581, by rfl⟩ : syracuseStep 2788775 = 4183163) B4183163
theorem B4181417 : Blo 1857630 4181417 := bstep (se 2 (by rfl) ⟨1568031, by rfl⟩ : syracuseStep 4181417 = 3136063) B3136063
theorem B2788859 : Blo 1857630 2788859 := bstep (se 1 (by rfl) ⟨2091644, by rfl⟩ : syracuseStep 2788859 = 4183289) B4183289
theorem B7941665 : Blo 1857630 7941665 := bstep (se 2 (by rfl) ⟨2978124, by rfl⟩ : syracuseStep 7941665 = 5956249) B5956249
theorem B2788955 : Blo 1857630 2788955 := bstep (se 1 (by rfl) ⟨2091716, by rfl⟩ : syracuseStep 2788955 = 4183433) B4183433
theorem B13397665 : Blo 1857630 13397665 := bstep (se 2 (by rfl) ⟨5024124, by rfl⟩ : syracuseStep 13397665 = 10048249) B10048249
theorem B2789039 : Blo 1857630 2789039 := bstep (se 1 (by rfl) ⟨2091779, by rfl⟩ : syracuseStep 2789039 = 4183559) B4183559
theorem B2789159 : Blo 1857630 2789159 := bstep (se 1 (by rfl) ⟨2091869, by rfl⟩ : syracuseStep 2789159 = 4183739) B4183739
theorem B23826271 : Blo 1857630 23826271 := bstep (se 1 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 23826271 = 35739407) B35739407
theorem B2789243 : Blo 1857630 2789243 := bstep (se 1 (by rfl) ⟨2091932, by rfl⟩ : syracuseStep 2789243 = 4183865) B4183865
theorem B10579841 : Blo 1857630 10579841 := bstep (se 2 (by rfl) ⟨3967440, by rfl⟩ : syracuseStep 10579841 = 7934881) B7934881
theorem B4181903 : Blo 1857630 4181903 := bstep (se 1 (by rfl) ⟨3136427, by rfl⟩ : syracuseStep 4181903 = 6272855) B6272855
theorem B10727747 : Blo 1857630 10727747 := bstep (se 1 (by rfl) ⟨8045810, by rfl⟩ : syracuseStep 10727747 = 16091621) B16091621
theorem B11907395 : Blo 1857630 11907395 := bstep (se 1 (by rfl) ⟨8930546, by rfl⟩ : syracuseStep 11907395 = 17861093) B17861093
theorem B6271343 : Blo 1857630 6271343 := bstep (se 1 (by rfl) ⟨4703507, by rfl⟩ : syracuseStep 6271343 = 9407015) B9407015
theorem B3527039 : Blo 1857630 3527039 := bstep (se 1 (by rfl) ⟨2645279, by rfl⟩ : syracuseStep 3527039 = 5290559) B5290559
theorem B8933759 : Blo 1857630 8933759 := bstep (se 1 (by rfl) ⟨6700319, by rfl⟩ : syracuseStep 8933759 = 13400639) B13400639
theorem B4706687 : Blo 1857630 4706687 := bstep (se 1 (by rfl) ⟨3530015, by rfl⟩ : syracuseStep 4706687 = 7060031) B7060031
theorem B10588589 : Blo 1857630 10588589 := bstep (se 3 (by rfl) ⟨1985360, by rfl⟩ : syracuseStep 10588589 = 3970721) B3970721
theorem B13398473 : Blo 1857630 13398473 := bstep (se 2 (by rfl) ⟨5024427, by rfl⟩ : syracuseStep 13398473 = 10048855) B10048855
theorem B47632859 : Blo 1857630 47632859 := bstep (se 1 (by rfl) ⟨35724644, by rfl⟩ : syracuseStep 47632859 = 71449289) B71449289
theorem B5804623 : Blo 1857630 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B4182623 : Blo 1857630 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B11907805 : Blo 1857630 11907805 := bstep (se 3 (by rfl) ⟨2232713, by rfl⟩ : syracuseStep 11907805 = 4465427) B4465427
theorem B14496683 : Blo 1857630 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B71488655 : Blo 1857630 71488655 := bstep (se 1 (by rfl) ⟨53616491, by rfl⟩ : syracuseStep 71488655 = 107232983) B107232983
theorem B4240559 : Blo 1857630 4240559 := bstep (se 1 (by rfl) ⟨3180419, by rfl⟩ : syracuseStep 4240559 = 6360839) B6360839
theorem B14120243 : Blo 1857630 14120243 := bstep (se 1 (by rfl) ⟨10590182, by rfl⟩ : syracuseStep 14120243 = 21180365) B21180365
theorem B3134875 : Blo 1857630 3134875 := bstep (se 1 (by rfl) ⟨2351156, by rfl⟩ : syracuseStep 3134875 = 4702313) B4702313
theorem B4183451 : Blo 1857630 4183451 := bstep (se 1 (by rfl) ⟨3137588, by rfl⟩ : syracuseStep 4183451 = 6275177) B6275177
theorem B325998229 : Blo 1857630 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B139351745 : Blo 1857630 139351745 := bstep (se 2 (by rfl) ⟨52256904, by rfl⟩ : syracuseStep 139351745 = 104513809) B104513809
theorem B28604107 : Blo 1857630 28604107 := bstep (se 1 (by rfl) ⟨21453080, by rfl⟩ : syracuseStep 28604107 = 42906161) B42906161
theorem B3135199 : Blo 1857630 3135199 := bstep (se 1 (by rfl) ⟨2351399, by rfl⟩ : syracuseStep 3135199 = 4702799) B4702799
theorem B6272747 : Blo 1857630 6272747 := bstep (se 1 (by rfl) ⟨4704560, by rfl⟩ : syracuseStep 6272747 = 9409121) B9409121
theorem B6698747 : Blo 1857630 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B119232461 : Blo 1857630 119232461 := bstep (se 3 (by rfl) ⟨22356086, by rfl⟩ : syracuseStep 119232461 = 44712173) B44712173
theorem B5289943 : Blo 1857630 5289943 := bstep (se 1 (by rfl) ⟨3967457, by rfl⟩ : syracuseStep 5289943 = 7934915) B7934915
theorem B4184027 : Blo 1857630 4184027 := bstep (se 1 (by rfl) ⟨3138020, by rfl⟩ : syracuseStep 4184027 = 6276041) B6276041
theorem B3528679 : Blo 1857630 3528679 := bstep (se 1 (by rfl) ⟨2646509, by rfl⟩ : syracuseStep 3528679 = 5293019) B5293019
theorem B6273017 : Blo 1857630 6273017 := bstep (se 2 (by rfl) ⟨2352381, by rfl⟩ : syracuseStep 6273017 = 4704763) B4704763
theorem B3135631 : Blo 1857630 3135631 := bstep (se 1 (by rfl) ⟨2351723, by rfl⟩ : syracuseStep 3135631 = 4703447) B4703447
theorem B1857691 : Blo 1857630 1857691 := bstep (se 1 (by rfl) ⟨1393268, by rfl⟩ : syracuseStep 1857691 = 2786537) B2786537
theorem B6273179 : Blo 1857630 6273179 := bstep (se 1 (by rfl) ⟨4704884, by rfl⟩ : syracuseStep 6273179 = 9409769) B9409769
theorem B1857727 : Blo 1857630 1857727 := bstep (se 1 (by rfl) ⟨1393295, by rfl⟩ : syracuseStep 1857727 = 2786591) B2786591
theorem B5290217 : Blo 1857630 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B3528937 : Blo 1857630 3528937 := bstep (se 2 (by rfl) ⟨1323351, by rfl⟩ : syracuseStep 3528937 = 2646703) B2646703
theorem B6273287 : Blo 1857630 6273287 := bstep (se 1 (by rfl) ⟨4704965, by rfl⟩ : syracuseStep 6273287 = 9409931) B9409931
theorem B1857839 : Blo 1857630 1857839 := bstep (se 1 (by rfl) ⟨1393379, by rfl⟩ : syracuseStep 1857839 = 2786759) B2786759
theorem B1858075 : Blo 1857630 1858075 := bstep (se 1 (by rfl) ⟨1393556, by rfl⟩ : syracuseStep 1858075 = 2787113) B2787113
theorem B1858079 : Blo 1857630 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B3349129 : Blo 1857630 3349129 := bstep (se 2 (by rfl) ⟨1255923, by rfl⟩ : syracuseStep 3349129 = 2511847) B2511847
theorem B11909855 : Blo 1857630 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B1858395 : Blo 1857630 1858395 := bstep (se 1 (by rfl) ⟨1393796, by rfl⟩ : syracuseStep 1858395 = 2787593) B2787593
theorem B1858463 : Blo 1857630 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B1858607 : Blo 1857630 1858607 := bstep (se 1 (by rfl) ⟨1393955, by rfl⟩ : syracuseStep 1858607 = 2787911) B2787911
theorem B1858631 : Blo 1857630 1858631 := bstep (se 1 (by rfl) ⟨1393973, by rfl⟩ : syracuseStep 1858631 = 2787947) B2787947
theorem B3136583 : Blo 1857630 3136583 := bstep (se 1 (by rfl) ⟨2352437, by rfl⟩ : syracuseStep 3136583 = 4704875) B4704875
theorem B6700103 : Blo 1857630 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B1858783 : Blo 1857630 1858783 := bstep (se 1 (by rfl) ⟨1394087, by rfl⟩ : syracuseStep 1858783 = 2788175) B2788175
theorem B7060729 : Blo 1857630 7060729 := bstep (se 2 (by rfl) ⟨2647773, by rfl⟩ : syracuseStep 7060729 = 5295547) B5295547
theorem B6274313 : Blo 1857630 6274313 := bstep (se 2 (by rfl) ⟨2352867, by rfl⟩ : syracuseStep 6274313 = 4705735) B4705735
theorem B3529993 : Blo 1857630 3529993 := bstep (se 2 (by rfl) ⟨1323747, by rfl⟩ : syracuseStep 3529993 = 2647495) B2647495
theorem B10329439 : Blo 1857630 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B1859047 : Blo 1857630 1859047 := bstep (se 1 (by rfl) ⟨1394285, by rfl⟩ : syracuseStep 1859047 = 2788571) B2788571
theorem B3137015 : Blo 1857630 3137015 := bstep (se 1 (by rfl) ⟨2352761, by rfl⟩ : syracuseStep 3137015 = 4705523) B4705523
theorem B5291527 : Blo 1857630 5291527 := bstep (se 1 (by rfl) ⟨3968645, by rfl⟩ : syracuseStep 5291527 = 7937291) B7937291
theorem B7937615 : Blo 1857630 7937615 := bstep (se 1 (by rfl) ⟨5953211, by rfl⟩ : syracuseStep 7937615 = 11906423) B11906423
theorem B1859163 : Blo 1857630 1859163 := bstep (se 1 (by rfl) ⟨1394372, by rfl⟩ : syracuseStep 1859163 = 2788745) B2788745
theorem B11910881 : Blo 1857630 11910881 := bstep (se 2 (by rfl) ⟨4466580, by rfl⟩ : syracuseStep 11910881 = 8933161) B8933161
theorem B1859399 : Blo 1857630 1859399 := bstep (se 1 (by rfl) ⟨1394549, by rfl⟩ : syracuseStep 1859399 = 2789099) B2789099
theorem B1859551 : Blo 1857630 1859551 := bstep (se 1 (by rfl) ⟨1394663, by rfl⟩ : syracuseStep 1859551 = 2789327) B2789327
theorem B7151831 : Blo 1857630 7151831 := bstep (se 1 (by rfl) ⟨5363873, by rfl⟩ : syracuseStep 7151831 = 10727747) B10727747
theorem B7938263 : Blo 1857630 7938263 := bstep (se 1 (by rfl) ⟨5953697, by rfl⟩ : syracuseStep 7938263 = 11907395) B11907395
theorem B2351359 : Blo 1857630 2351359 := bstep (se 1 (by rfl) ⟨1763519, by rfl⟩ : syracuseStep 2351359 = 3527039) B3527039
theorem B5955839 : Blo 1857630 5955839 := bstep (se 1 (by rfl) ⟨4466879, by rfl⟩ : syracuseStep 5955839 = 8933759) B8933759
theorem B3137791 : Blo 1857630 3137791 := bstep (se 1 (by rfl) ⟨2353343, by rfl⟩ : syracuseStep 3137791 = 4706687) B4706687
theorem B7635311 : Blo 1857630 7635311 := bstep (se 1 (by rfl) ⟨5726483, by rfl⟩ : syracuseStep 7635311 = 11452967) B11452967
theorem B8929931 : Blo 1857630 8929931 := bstep (se 1 (by rfl) ⟨6697448, by rfl⟩ : syracuseStep 8929931 = 13394897) B13394897
theorem B6275771 : Blo 1857630 6275771 := bstep (se 1 (by rfl) ⟨4706828, by rfl⟩ : syracuseStep 6275771 = 9413657) B9413657
theorem B4465505 : Blo 1857630 4465505 := bstep (se 2 (by rfl) ⟨1674564, by rfl⟩ : syracuseStep 4465505 = 3349129) B3349129
theorem B9413495 : Blo 1857630 9413495 := bstep (se 1 (by rfl) ⟨7060121, by rfl⟩ : syracuseStep 9413495 = 14120243) B14120243
theorem B15877073 : Blo 1857630 15877073 := bstep (se 2 (by rfl) ⟨5953902, by rfl⟩ : syracuseStep 15877073 = 11907805) B11907805
theorem B2786495 : Blo 1857630 2786495 := bstep (se 1 (by rfl) ⟨2089871, by rfl⟩ : syracuseStep 2786495 = 4179743) B4179743
theorem B4703467 : Blo 1857630 4703467 := bstep (se 1 (by rfl) ⟨3527600, by rfl⟩ : syracuseStep 4703467 = 7055201) B7055201
theorem B79488307 : Blo 1857630 79488307 := bstep (se 1 (by rfl) ⟨59616230, by rfl⟩ : syracuseStep 79488307 = 119232461) B119232461
theorem B2786639 : Blo 1857630 2786639 := bstep (se 1 (by rfl) ⟨2089979, by rfl⟩ : syracuseStep 2786639 = 4179959) B4179959
theorem B2786729 : Blo 1857630 2786729 := bstep (se 2 (by rfl) ⟨1045023, by rfl⟩ : syracuseStep 2786729 = 2090047) B2090047
theorem B17860135 : Blo 1857630 17860135 := bstep (se 1 (by rfl) ⟨13395101, by rfl⟩ : syracuseStep 17860135 = 26790203) B26790203
theorem B2786879 : Blo 1857630 2786879 := bstep (se 1 (by rfl) ⟨2090159, by rfl⟩ : syracuseStep 2786879 = 4180319) B4180319
theorem B2786921 : Blo 1857630 2786921 := bstep (se 2 (by rfl) ⟨1045095, by rfl⟩ : syracuseStep 2786921 = 2090191) B2090191
theorem B9414305 : Blo 1857630 9414305 := bstep (se 2 (by rfl) ⟨3530364, by rfl⟩ : syracuseStep 9414305 = 7060729) B7060729
theorem B13772585 : Blo 1857630 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B4179833 : Blo 1857630 4179833 := bstep (se 2 (by rfl) ⟨1567437, by rfl⟩ : syracuseStep 4179833 = 3134875) B3134875
theorem B7055369 : Blo 1857630 7055369 := bstep (se 2 (by rfl) ⟨2645763, by rfl⟩ : syracuseStep 7055369 = 5291527) B5291527
theorem B2787359 : Blo 1857630 2787359 := bstep (se 1 (by rfl) ⟨2090519, by rfl⟩ : syracuseStep 2787359 = 4181039) B4181039
theorem B2091055 : Blo 1857630 2091055 := bstep (se 1 (by rfl) ⟨1568291, by rfl⟩ : syracuseStep 2091055 = 3136583) B3136583
theorem B4466735 : Blo 1857630 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B2787551 : Blo 1857630 2787551 := bstep (se 1 (by rfl) ⟨2090663, by rfl⟩ : syracuseStep 2787551 = 4181327) B4181327
theorem B23824631 : Blo 1857630 23824631 := bstep (se 1 (by rfl) ⟨17868473, by rfl⟩ : syracuseStep 23824631 = 35736947) B35736947
theorem B135694601 : Blo 1857630 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B2787611 : Blo 1857630 2787611 := bstep (se 1 (by rfl) ⟨2090708, by rfl⟩ : syracuseStep 2787611 = 4181417) B4181417
theorem B4180265 : Blo 1857630 4180265 := bstep (se 2 (by rfl) ⟨1567599, by rfl⟩ : syracuseStep 4180265 = 3135199) B3135199
theorem B2091343 : Blo 1857630 2091343 := bstep (se 1 (by rfl) ⟨1568507, by rfl⟩ : syracuseStep 2091343 = 3137015) B3137015
theorem B5294443 : Blo 1857630 5294443 := bstep (se 1 (by rfl) ⟨3970832, by rfl⟩ : syracuseStep 5294443 = 7941665) B7941665
theorem B7940587 : Blo 1857630 7940587 := bstep (se 1 (by rfl) ⟨5955440, by rfl⟩ : syracuseStep 7940587 = 11910881) B11910881
theorem B2787935 : Blo 1857630 2787935 := bstep (se 1 (by rfl) ⟨2090951, by rfl⟩ : syracuseStep 2787935 = 4181903) B4181903
theorem B4704905 : Blo 1857630 4704905 := bstep (se 2 (by rfl) ⟨1764339, by rfl⟩ : syracuseStep 4704905 = 3528679) B3528679
theorem B4180841 : Blo 1857630 4180841 := bstep (se 2 (by rfl) ⟨1567815, by rfl⟩ : syracuseStep 4180841 = 3135631) B3135631
theorem B2788217 : Blo 1857630 2788217 := bstep (se 2 (by rfl) ⟨1045581, by rfl⟩ : syracuseStep 2788217 = 2091163) B2091163
theorem B4180895 : Blo 1857630 4180895 := bstep (se 1 (by rfl) ⟨3135671, by rfl⟩ : syracuseStep 4180895 = 6271343) B6271343
theorem B2788265 : Blo 1857630 2788265 := bstep (se 2 (by rfl) ⟨1045599, by rfl⟩ : syracuseStep 2788265 = 2091199) B2091199
theorem B4705249 : Blo 1857630 4705249 := bstep (se 2 (by rfl) ⟨1764468, by rfl⟩ : syracuseStep 4705249 = 3528937) B3528937
theorem B31755239 : Blo 1857630 31755239 := bstep (se 1 (by rfl) ⟨23816429, by rfl⟩ : syracuseStep 31755239 = 47632859) B47632859
theorem B2092027 : Blo 1857630 2092027 := bstep (se 1 (by rfl) ⟨1569020, by rfl⟩ : syracuseStep 2092027 = 3138041) B3138041
theorem B6269993 : Blo 1857630 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B2788415 : Blo 1857630 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B11308157 : Blo 1857630 11308157 := bstep (se 3 (by rfl) ⟨2120279, by rfl⟩ : syracuseStep 11308157 = 4240559) B4240559
theorem B7056659 : Blo 1857630 7056659 := bstep (se 1 (by rfl) ⟨5292494, by rfl⟩ : syracuseStep 7056659 = 10584989) B10584989
theorem B6270263 : Blo 1857630 6270263 := bstep (se 1 (by rfl) ⟨4702697, by rfl⟩ : syracuseStep 6270263 = 9405395) B9405395
theorem B10726825 : Blo 1857630 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B11906473 : Blo 1857630 11906473 := bstep (se 2 (by rfl) ⟨4464927, by rfl⟩ : syracuseStep 11906473 = 8929855) B8929855
theorem B2788967 : Blo 1857630 2788967 := bstep (se 1 (by rfl) ⟨2091725, by rfl⟩ : syracuseStep 2788967 = 4183451) B4183451
theorem B7941817 : Blo 1857630 7941817 := bstep (se 2 (by rfl) ⟨2978181, by rfl⟩ : syracuseStep 7941817 = 5956363) B5956363
theorem B92901163 : Blo 1857630 92901163 := bstep (se 1 (by rfl) ⟨69675872, by rfl⟩ : syracuseStep 92901163 = 139351745) B139351745
theorem B4181831 : Blo 1857630 4181831 := bstep (se 1 (by rfl) ⟨3136373, by rfl⟩ : syracuseStep 4181831 = 6272747) B6272747
theorem B35729261 : Blo 1857630 35729261 := bstep (se 3 (by rfl) ⟨6699236, by rfl⟩ : syracuseStep 35729261 = 13398473) B13398473
theorem B6270857 : Blo 1857630 6270857 := bstep (se 2 (by rfl) ⟨2351571, by rfl⟩ : syracuseStep 6270857 = 4703143) B4703143
theorem B2789351 : Blo 1857630 2789351 := bstep (se 1 (by rfl) ⟨2092013, by rfl⟩ : syracuseStep 2789351 = 4184027) B4184027
theorem B4182011 : Blo 1857630 4182011 := bstep (se 1 (by rfl) ⟨3136508, by rfl⟩ : syracuseStep 4182011 = 6273017) B6273017
theorem B4182119 : Blo 1857630 4182119 := bstep (se 1 (by rfl) ⟨3136589, by rfl⟩ : syracuseStep 4182119 = 6273179) B6273179
theorem B5025931 : Blo 1857630 5025931 := bstep (se 1 (by rfl) ⟨3769448, by rfl⟩ : syracuseStep 5025931 = 7538897) B7538897
theorem B3526811 : Blo 1857630 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B4182191 : Blo 1857630 4182191 := bstep (se 1 (by rfl) ⟨3136643, by rfl⟩ : syracuseStep 4182191 = 6273287) B6273287
theorem B14299345 : Blo 1857630 14299345 := bstep (se 2 (by rfl) ⟨5362254, by rfl⟩ : syracuseStep 14299345 = 10724509) B10724509
theorem B8597735 : Blo 1857630 8597735 := bstep (se 1 (by rfl) ⟨6448301, by rfl⟩ : syracuseStep 8597735 = 12896603) B12896603
theorem B4239635 : Blo 1857630 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B4706657 : Blo 1857630 4706657 := bstep (se 2 (by rfl) ⟨1764996, by rfl⟩ : syracuseStep 4706657 = 3529993) B3529993
theorem B17863325 : Blo 1857630 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B4182875 : Blo 1857630 4182875 := bstep (se 1 (by rfl) ⟨3137156, by rfl⟩ : syracuseStep 4182875 = 6274313) B6274313
theorem B434664305 : Blo 1857630 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B17863553 : Blo 1857630 17863553 := bstep (se 2 (by rfl) ⟨6698832, by rfl⟩ : syracuseStep 17863553 = 13397665) B13397665
theorem B38138809 : Blo 1857630 38138809 := bstep (se 2 (by rfl) ⟨14302053, by rfl⟩ : syracuseStep 38138809 = 28604107) B28604107
theorem B7058785 : Blo 1857630 7058785 := bstep (se 2 (by rfl) ⟨2647044, by rfl⟩ : syracuseStep 7058785 = 5294089) B5294089
theorem B5953007 : Blo 1857630 5953007 := bstep (se 1 (by rfl) ⟨4464755, by rfl⟩ : syracuseStep 5953007 = 8929511) B8929511
theorem B4183631 : Blo 1857630 4183631 := bstep (se 1 (by rfl) ⟨3137723, by rfl⟩ : syracuseStep 4183631 = 6275447) B6275447
theorem B7059059 : Blo 1857630 7059059 := bstep (se 1 (by rfl) ⟨5294294, by rfl⟩ : syracuseStep 7059059 = 10588589) B10588589
theorem B8476447 : Blo 1857630 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B9410579 : Blo 1857630 9410579 := bstep (se 1 (by rfl) ⟨7057934, by rfl⟩ : syracuseStep 9410579 = 14115869) B14115869
theorem B14309443 : Blo 1857630 14309443 := bstep (se 1 (by rfl) ⟨10732082, by rfl⟩ : syracuseStep 14309443 = 21464165) B21464165
theorem B47659103 : Blo 1857630 47659103 := bstep (se 1 (by rfl) ⟨35744327, by rfl⟩ : syracuseStep 47659103 = 71488655) B71488655
theorem B7739497 : Blo 1857630 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B1857767 : Blo 1857630 1857767 := bstep (se 1 (by rfl) ⟨1393325, by rfl⟩ : syracuseStep 1857767 = 2786651) B2786651
theorem B1857951 : Blo 1857630 1857951 := bstep (se 1 (by rfl) ⟨1393463, by rfl⟩ : syracuseStep 1857951 = 2786927) B2786927
theorem B1857999 : Blo 1857630 1857999 := bstep (se 1 (by rfl) ⟨1393499, by rfl⟩ : syracuseStep 1857999 = 2786999) B2786999
theorem B7936487 : Blo 1857630 7936487 := bstep (se 1 (by rfl) ⟨5952365, by rfl⟩ : syracuseStep 7936487 = 11904731) B11904731
theorem B1858023 : Blo 1857630 1858023 := bstep (se 1 (by rfl) ⟨1393517, by rfl⟩ : syracuseStep 1858023 = 2787035) B2787035
theorem B1858139 : Blo 1857630 1858139 := bstep (se 1 (by rfl) ⟨1393604, by rfl⟩ : syracuseStep 1858139 = 2787209) B2787209
theorem B1858207 : Blo 1857630 1858207 := bstep (se 1 (by rfl) ⟨1393655, by rfl⟩ : syracuseStep 1858207 = 2787311) B2787311
theorem B3136313 : Blo 1857630 3136313 := bstep (se 2 (by rfl) ⟨1176117, by rfl⟩ : syracuseStep 3136313 = 2352235) B2352235
theorem B1858375 : Blo 1857630 1858375 := bstep (se 1 (by rfl) ⟨1393781, by rfl⟩ : syracuseStep 1858375 = 2787563) B2787563
theorem B1858415 : Blo 1857630 1858415 := bstep (se 1 (by rfl) ⟨1393811, by rfl⟩ : syracuseStep 1858415 = 2787623) B2787623
theorem B3136367 : Blo 1857630 3136367 := bstep (se 1 (by rfl) ⟨2352275, by rfl⟩ : syracuseStep 3136367 = 4704551) B4704551
theorem B1858471 : Blo 1857630 1858471 := bstep (se 1 (by rfl) ⟨1393853, by rfl⟩ : syracuseStep 1858471 = 2787707) B2787707
theorem B1858651 : Blo 1857630 1858651 := bstep (se 1 (by rfl) ⟨1393988, by rfl⟩ : syracuseStep 1858651 = 2787977) B2787977
theorem B15883361 : Blo 1857630 15883361 := bstep (se 2 (by rfl) ⟨5956260, by rfl⟩ : syracuseStep 15883361 = 11912521) B11912521
theorem B1858767 : Blo 1857630 1858767 := bstep (se 1 (by rfl) ⟨1394075, by rfl⟩ : syracuseStep 1858767 = 2788151) B2788151
theorem B1858791 : Blo 1857630 1858791 := bstep (se 1 (by rfl) ⟨1394093, by rfl⟩ : syracuseStep 1858791 = 2788187) B2788187
theorem B31759613 : Blo 1857630 31759613 := bstep (se 3 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 31759613 = 11909855) B11909855
theorem B1858887 : Blo 1857630 1858887 := bstep (se 1 (by rfl) ⟨1394165, by rfl⟩ : syracuseStep 1858887 = 2788331) B2788331
theorem B1859023 : Blo 1857630 1859023 := bstep (se 1 (by rfl) ⟨1394267, by rfl⟩ : syracuseStep 1859023 = 2788535) B2788535
theorem B1859183 : Blo 1857630 1859183 := bstep (se 1 (by rfl) ⟨1394387, by rfl⟩ : syracuseStep 1859183 = 2788775) B2788775
theorem B1859239 : Blo 1857630 1859239 := bstep (se 1 (by rfl) ⟨1394429, by rfl⟩ : syracuseStep 1859239 = 2788859) B2788859
theorem B5291743 : Blo 1857630 5291743 := bstep (se 1 (by rfl) ⟨3968807, by rfl⟩ : syracuseStep 5291743 = 7937615) B7937615
theorem B1859303 : Blo 1857630 1859303 := bstep (se 1 (by rfl) ⟨1394477, by rfl⟩ : syracuseStep 1859303 = 2788955) B2788955
theorem B38657821 : Blo 1857630 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B1859359 : Blo 1857630 1859359 := bstep (se 1 (by rfl) ⟨1394519, by rfl⟩ : syracuseStep 1859359 = 2789039) B2789039
theorem B31768361 : Blo 1857630 31768361 := bstep (se 2 (by rfl) ⟨11913135, by rfl⟩ : syracuseStep 31768361 = 23826271) B23826271
theorem B1859439 : Blo 1857630 1859439 := bstep (se 1 (by rfl) ⟨1394579, by rfl⟩ : syracuseStep 1859439 = 2789159) B2789159
theorem B1859495 : Blo 1857630 1859495 := bstep (se 1 (by rfl) ⟨1394621, by rfl⟩ : syracuseStep 1859495 = 2789243) B2789243
theorem B7053227 : Blo 1857630 7053227 := bstep (se 1 (by rfl) ⟨5289920, by rfl⟩ : syracuseStep 7053227 = 10579841) B10579841
theorem B7053257 : Blo 1857630 7053257 := bstep (se 2 (by rfl) ⟨2644971, by rfl⟩ : syracuseStep 7053257 = 5289943) B5289943
theorem B2351207 : Blo 1857630 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B4767887 : Blo 1857630 4767887 := bstep (se 1 (by rfl) ⟨3575915, by rfl⟩ : syracuseStep 4767887 = 7151831) B7151831
theorem B3137771 : Blo 1857630 3137771 := bstep (se 1 (by rfl) ⟨2353328, by rfl⟩ : syracuseStep 3137771 = 4706657) B4706657
theorem B76317029 : Blo 1857630 76317029 := bstep (se 4 (by rfl) ⟨7154721, by rfl⟩ : syracuseStep 76317029 = 14309443) B14309443
theorem B21168701 : Blo 1857630 21168701 := bstep (se 3 (by rfl) ⟨3969131, by rfl⟩ : syracuseStep 21168701 = 7938263) B7938263
theorem B289776203 : Blo 1857630 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B6275663 : Blo 1857630 6275663 := bstep (se 1 (by rfl) ⟨4706747, by rfl⟩ : syracuseStep 6275663 = 9413495) B9413495
theorem B10584715 : Blo 1857630 10584715 := bstep (se 1 (by rfl) ⟨7938536, by rfl⟩ : syracuseStep 10584715 = 15877073) B15877073
theorem B11305693 : Blo 1857630 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B26804965 : Blo 1857630 26804965 := bstep (se 4 (by rfl) ⟨2512965, by rfl⟩ : syracuseStep 26804965 = 5025931) B5025931
theorem B6276203 : Blo 1857630 6276203 := bstep (se 1 (by rfl) ⟨4707152, by rfl⟩ : syracuseStep 6276203 = 9414305) B9414305
theorem B2786555 : Blo 1857630 2786555 := bstep (se 1 (by rfl) ⟨2089916, by rfl⟩ : syracuseStep 2786555 = 4179833) B4179833
theorem B4703579 : Blo 1857630 4703579 := bstep (se 1 (by rfl) ⟨3527684, by rfl⟩ : syracuseStep 4703579 = 7055369) B7055369
theorem B2786843 : Blo 1857630 2786843 := bstep (se 1 (by rfl) ⟨2090132, by rfl⟩ : syracuseStep 2786843 = 4180265) B4180265
theorem B2090875 : Blo 1857630 2090875 := bstep (se 1 (by rfl) ⟨1568156, by rfl⟩ : syracuseStep 2090875 = 3136313) B3136313
theorem B2787227 : Blo 1857630 2787227 := bstep (se 1 (by rfl) ⟨2090420, by rfl⟩ : syracuseStep 2787227 = 4180841) B4180841
theorem B2090911 : Blo 1857630 2090911 := bstep (se 1 (by rfl) ⟨1568183, by rfl⟩ : syracuseStep 2090911 = 3136367) B3136367
theorem B2787263 : Blo 1857630 2787263 := bstep (se 1 (by rfl) ⟨2090447, by rfl⟩ : syracuseStep 2787263 = 4180895) B4180895
theorem B21170159 : Blo 1857630 21170159 := bstep (se 1 (by rfl) ⟨15877619, by rfl⟩ : syracuseStep 21170159 = 31755239) B31755239
theorem B4179995 : Blo 1857630 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B7538771 : Blo 1857630 7538771 := bstep (se 1 (by rfl) ⟨5654078, by rfl⟩ : syracuseStep 7538771 = 11308157) B11308157
theorem B4704439 : Blo 1857630 4704439 := bstep (se 1 (by rfl) ⟨3528329, by rfl⟩ : syracuseStep 4704439 = 7056659) B7056659
theorem B4180175 : Blo 1857630 4180175 := bstep (se 1 (by rfl) ⟨3135131, by rfl⟩ : syracuseStep 4180175 = 6270263) B6270263
theorem B7055657 : Blo 1857630 7055657 := bstep (se 2 (by rfl) ⟨2645871, by rfl⟩ : syracuseStep 7055657 = 5291743) B5291743
theorem B21178907 : Blo 1857630 21178907 := bstep (se 1 (by rfl) ⟨15884180, by rfl⟩ : syracuseStep 21178907 = 31768361) B31768361
theorem B2787887 : Blo 1857630 2787887 := bstep (se 1 (by rfl) ⟨2090915, by rfl⟩ : syracuseStep 2787887 = 4181831) B4181831
theorem B4180571 : Blo 1857630 4180571 := bstep (se 1 (by rfl) ⟨3135428, by rfl⟩ : syracuseStep 4180571 = 6270857) B6270857
theorem B2788007 : Blo 1857630 2788007 := bstep (se 1 (by rfl) ⟨2091005, by rfl⟩ : syracuseStep 2788007 = 4182011) B4182011
theorem B2788073 : Blo 1857630 2788073 := bstep (se 2 (by rfl) ⟨1045527, by rfl⟩ : syracuseStep 2788073 = 2091055) B2091055
theorem B2788079 : Blo 1857630 2788079 := bstep (se 1 (by rfl) ⟨2091059, by rfl⟩ : syracuseStep 2788079 = 4182119) B4182119
theorem B2788127 : Blo 1857630 2788127 := bstep (se 1 (by rfl) ⟨2091095, by rfl⟩ : syracuseStep 2788127 = 4182191) B4182191
theorem B5090207 : Blo 1857630 5090207 := bstep (se 1 (by rfl) ⟨3817655, by rfl⟩ : syracuseStep 5090207 = 7635311) B7635311
theorem B19065793 : Blo 1857630 19065793 := bstep (se 2 (by rfl) ⟨7149672, by rfl⟩ : syracuseStep 19065793 = 14299345) B14299345
theorem B2788457 : Blo 1857630 2788457 := bstep (se 2 (by rfl) ⟨1045671, by rfl⟩ : syracuseStep 2788457 = 2091343) B2091343
theorem B2788583 : Blo 1857630 2788583 := bstep (se 1 (by rfl) ⟨2091437, by rfl⟩ : syracuseStep 2788583 = 4182875) B4182875
theorem B2977003 : Blo 1857630 2977003 := bstep (se 1 (by rfl) ⟨2232752, by rfl⟩ : syracuseStep 2977003 = 4465505) B4465505
theorem B10587449 : Blo 1857630 10587449 := bstep (se 2 (by rfl) ⟨3970293, by rfl⟩ : syracuseStep 10587449 = 7940587) B7940587
theorem B3968671 : Blo 1857630 3968671 := bstep (se 1 (by rfl) ⟨2976503, by rfl⟩ : syracuseStep 3968671 = 5953007) B5953007
theorem B2789087 : Blo 1857630 2789087 := bstep (se 1 (by rfl) ⟨2091815, by rfl⟩ : syracuseStep 2789087 = 4183631) B4183631
theorem B4706039 : Blo 1857630 4706039 := bstep (se 1 (by rfl) ⟨3529529, by rfl⟩ : syracuseStep 4706039 = 7059059) B7059059
theorem B50851745 : Blo 1857630 50851745 := bstep (se 2 (by rfl) ⟨19069404, by rfl⟩ : syracuseStep 50851745 = 38138809) B38138809
theorem B2789369 : Blo 1857630 2789369 := bstep (se 2 (by rfl) ⟨1046013, by rfl⟩ : syracuseStep 2789369 = 2092027) B2092027
theorem B2977823 : Blo 1857630 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B31772735 : Blo 1857630 31772735 := bstep (se 1 (by rfl) ⟨23829551, by rfl⟩ : syracuseStep 31772735 = 47659103) B47659103
theorem B6271289 : Blo 1857630 6271289 := bstep (se 2 (by rfl) ⟨2351733, by rfl⟩ : syracuseStep 6271289 = 4703467) B4703467
theorem B105984409 : Blo 1857630 105984409 := bstep (se 2 (by rfl) ⟨39744153, by rfl⟩ : syracuseStep 105984409 = 79488307) B79488307
theorem B10588907 : Blo 1857630 10588907 := bstep (se 1 (by rfl) ⟨7941680, by rfl⟩ : syracuseStep 10588907 = 15883361) B15883361
theorem B21173075 : Blo 1857630 21173075 := bstep (se 1 (by rfl) ⟨15879806, by rfl⟩ : syracuseStep 21173075 = 31759613) B31759613
theorem B10589089 : Blo 1857630 10589089 := bstep (se 2 (by rfl) ⟨3970908, by rfl⟩ : syracuseStep 10589089 = 7941817) B7941817
theorem B11301929 : Blo 1857630 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B123868217 : Blo 1857630 123868217 := bstep (se 2 (by rfl) ⟨46450581, by rfl⟩ : syracuseStep 123868217 = 92901163) B92901163
theorem B23819507 : Blo 1857630 23819507 := bstep (se 1 (by rfl) ⟨17864630, by rfl⟩ : syracuseStep 23819507 = 35729261) B35729261
theorem B10319329 : Blo 1857630 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B5731823 : Blo 1857630 5731823 := bstep (se 1 (by rfl) ⟨4298867, by rfl⟩ : syracuseStep 5731823 = 8597735) B8597735
theorem B3970559 : Blo 1857630 3970559 := bstep (se 1 (by rfl) ⟨2977919, by rfl⟩ : syracuseStep 3970559 = 5955839) B5955839
theorem B3135145 : Blo 1857630 3135145 := bstep (se 2 (by rfl) ⟨1175679, by rfl⟩ : syracuseStep 3135145 = 2351359) B2351359
theorem B4183721 : Blo 1857630 4183721 := bstep (se 2 (by rfl) ⟨1568895, by rfl⟩ : syracuseStep 4183721 = 3137791) B3137791
theorem B11908883 : Blo 1857630 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B4183847 : Blo 1857630 4183847 := bstep (se 1 (by rfl) ⟨3137885, by rfl⟩ : syracuseStep 4183847 = 6275771) B6275771
theorem B7059257 : Blo 1857630 7059257 := bstep (se 2 (by rfl) ⟨2647221, by rfl⟩ : syracuseStep 7059257 = 5294443) B5294443
theorem B11909035 : Blo 1857630 11909035 := bstep (se 1 (by rfl) ⟨8931776, by rfl⟩ : syracuseStep 11909035 = 17863553) B17863553
theorem B1857663 : Blo 1857630 1857663 := bstep (se 1 (by rfl) ⟨1393247, by rfl⟩ : syracuseStep 1857663 = 2786495) B2786495
theorem B1857759 : Blo 1857630 1857759 := bstep (se 1 (by rfl) ⟨1393319, by rfl⟩ : syracuseStep 1857759 = 2786639) B2786639
theorem B1857819 : Blo 1857630 1857819 := bstep (se 1 (by rfl) ⟨1393364, by rfl⟩ : syracuseStep 1857819 = 2786729) B2786729
theorem B1857919 : Blo 1857630 1857919 := bstep (se 1 (by rfl) ⟨1393439, by rfl⟩ : syracuseStep 1857919 = 2786879) B2786879
theorem B1857947 : Blo 1857630 1857947 := bstep (se 1 (by rfl) ⟨1393460, by rfl⟩ : syracuseStep 1857947 = 2786921) B2786921
theorem B9181723 : Blo 1857630 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B6273665 : Blo 1857630 6273665 := bstep (se 2 (by rfl) ⟨2352624, by rfl⟩ : syracuseStep 6273665 = 4705249) B4705249
theorem B6273719 : Blo 1857630 6273719 := bstep (se 1 (by rfl) ⟨4705289, by rfl⟩ : syracuseStep 6273719 = 9410579) B9410579
theorem B1858239 : Blo 1857630 1858239 := bstep (se 1 (by rfl) ⟨1393679, by rfl⟩ : syracuseStep 1858239 = 2787359) B2787359
theorem B1858367 : Blo 1857630 1858367 := bstep (se 1 (by rfl) ⟨1393775, by rfl⟩ : syracuseStep 1858367 = 2787551) B2787551
theorem B15883087 : Blo 1857630 15883087 := bstep (se 1 (by rfl) ⟨11912315, by rfl⟩ : syracuseStep 15883087 = 23824631) B23824631
theorem B90463067 : Blo 1857630 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B1858407 : Blo 1857630 1858407 := bstep (se 1 (by rfl) ⟨1393805, by rfl⟩ : syracuseStep 1858407 = 2787611) B2787611
theorem B5290991 : Blo 1857630 5290991 := bstep (se 1 (by rfl) ⟨3968243, by rfl⟩ : syracuseStep 5290991 = 7936487) B7936487
theorem B23813149 : Blo 1857630 23813149 := bstep (se 3 (by rfl) ⟨4464965, by rfl⟩ : syracuseStep 23813149 = 8929931) B8929931
theorem B1858623 : Blo 1857630 1858623 := bstep (se 1 (by rfl) ⟨1393967, by rfl⟩ : syracuseStep 1858623 = 2787935) B2787935
theorem B3136603 : Blo 1857630 3136603 := bstep (se 1 (by rfl) ⟨2352452, by rfl⟩ : syracuseStep 3136603 = 4704905) B4704905
theorem B9411713 : Blo 1857630 9411713 := bstep (se 2 (by rfl) ⟨3529392, by rfl⟩ : syracuseStep 9411713 = 7058785) B7058785
theorem B14302433 : Blo 1857630 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B15875297 : Blo 1857630 15875297 := bstep (se 2 (by rfl) ⟨5953236, by rfl⟩ : syracuseStep 15875297 = 11906473) B11906473
theorem B1858811 : Blo 1857630 1858811 := bstep (se 1 (by rfl) ⟨1394108, by rfl⟩ : syracuseStep 1858811 = 2788217) B2788217
theorem B1858843 : Blo 1857630 1858843 := bstep (se 1 (by rfl) ⟨1394132, by rfl⟩ : syracuseStep 1858843 = 2788265) B2788265
theorem B1858943 : Blo 1857630 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B23813513 : Blo 1857630 23813513 := bstep (se 2 (by rfl) ⟨8930067, by rfl⟩ : syracuseStep 23813513 = 17860135) B17860135
theorem B51543761 : Blo 1857630 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B1859311 : Blo 1857630 1859311 := bstep (se 1 (by rfl) ⟨1394483, by rfl⟩ : syracuseStep 1859311 = 2788967) B2788967
theorem B4702151 : Blo 1857630 4702151 := bstep (se 1 (by rfl) ⟨3526613, by rfl⟩ : syracuseStep 4702151 = 7053227) B7053227
theorem B4702171 : Blo 1857630 4702171 := bstep (se 1 (by rfl) ⟨3526628, by rfl⟩ : syracuseStep 4702171 = 7053257) B7053257
theorem B1859567 : Blo 1857630 1859567 := bstep (se 1 (by rfl) ⟨1394675, by rfl⟩ : syracuseStep 1859567 = 2789351) B2789351
theorem B3178591 : Blo 1857630 3178591 := bstep (se 1 (by rfl) ⟨2383943, by rfl⟩ : syracuseStep 3178591 = 4767887) B4767887
theorem B193184135 : Blo 1857630 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B141312545 : Blo 1857630 141312545 := bstep (se 2 (by rfl) ⟨52992204, by rfl⟩ : syracuseStep 141312545 = 105984409) B105984409
theorem B14115383 : Blo 1857630 14115383 := bstep (se 1 (by rfl) ⟨10586537, by rfl⟩ : syracuseStep 14115383 = 21173075) B21173075
theorem B15074257 : Blo 1857630 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B21177449 : Blo 1857630 21177449 := bstep (se 2 (by rfl) ⟨7941543, by rfl⟩ : syracuseStep 21177449 = 15883087) B15883087
theorem B7939255 : Blo 1857630 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B25421057 : Blo 1857630 25421057 := bstep (se 2 (by rfl) ⟨9532896, by rfl⟩ : syracuseStep 25421057 = 19065793) B19065793
theorem B2786663 : Blo 1857630 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B2786783 : Blo 1857630 2786783 := bstep (se 1 (by rfl) ⟨2090087, by rfl⟩ : syracuseStep 2786783 = 4180175) B4180175
theorem B4703771 : Blo 1857630 4703771 := bstep (se 1 (by rfl) ⟨3527828, by rfl⟩ : syracuseStep 4703771 = 7055657) B7055657
theorem B2787047 : Blo 1857630 2787047 := bstep (se 1 (by rfl) ⟨2090285, by rfl⟩ : syracuseStep 2787047 = 4180571) B4180571
theorem B4180193 : Blo 1857630 4180193 := bstep (se 2 (by rfl) ⟨1567572, by rfl⟩ : syracuseStep 4180193 = 3135145) B3135145
theorem B2787833 : Blo 1857630 2787833 := bstep (se 2 (by rfl) ⟨1045437, by rfl⟩ : syracuseStep 2787833 = 2090875) B2090875
theorem B2787881 : Blo 1857630 2787881 := bstep (se 2 (by rfl) ⟨1045455, by rfl⟩ : syracuseStep 2787881 = 2090911) B2090911
theorem B15878713 : Blo 1857630 15878713 := bstep (se 2 (by rfl) ⟨5954517, by rfl⟩ : syracuseStep 15878713 = 11909035) B11909035
theorem B33901163 : Blo 1857630 33901163 := bstep (se 1 (by rfl) ⟨25425872, by rfl⟩ : syracuseStep 33901163 = 50851745) B50851745
theorem B6269561 : Blo 1857630 6269561 := bstep (se 2 (by rfl) ⟨2351085, by rfl⟩ : syracuseStep 6269561 = 4702171) B4702171
theorem B7940861 : Blo 1857630 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B2091847 : Blo 1857630 2091847 := bstep (se 1 (by rfl) ⟨1568885, by rfl⟩ : syracuseStep 2091847 = 3137771) B3137771
theorem B4180859 : Blo 1857630 4180859 := bstep (se 1 (by rfl) ⟨3135644, by rfl⟩ : syracuseStep 4180859 = 6271289) B6271289
theorem B6269885 : Blo 1857630 6269885 := bstep (se 3 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 6269885 = 2351207) B2351207
theorem B12242297 : Blo 1857630 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B82578811 : Blo 1857630 82578811 := bstep (se 1 (by rfl) ⟨61934108, by rfl⟩ : syracuseStep 82578811 = 123868217) B123868217
theorem B15879671 : Blo 1857630 15879671 := bstep (se 1 (by rfl) ⟨11909753, by rfl⟩ : syracuseStep 15879671 = 23819507) B23819507
theorem B2789147 : Blo 1857630 2789147 := bstep (se 1 (by rfl) ⟨2091860, by rfl⟩ : syracuseStep 2789147 = 4183721) B4183721
theorem B2789231 : Blo 1857630 2789231 := bstep (se 1 (by rfl) ⟨2091923, by rfl⟩ : syracuseStep 2789231 = 4183847) B4183847
theorem B4706171 : Blo 1857630 4706171 := bstep (se 1 (by rfl) ⟨3529628, by rfl⟩ : syracuseStep 4706171 = 7059257) B7059257
theorem B14118785 : Blo 1857630 14118785 := bstep (se 2 (by rfl) ⟨5294544, by rfl⟩ : syracuseStep 14118785 = 10589089) B10589089
theorem B10588157 : Blo 1857630 10588157 := bstep (se 3 (by rfl) ⟨1985279, by rfl⟩ : syracuseStep 10588157 = 3970559) B3970559
theorem B5025847 : Blo 1857630 5025847 := bstep (se 1 (by rfl) ⟨3769385, by rfl⟩ : syracuseStep 5025847 = 7538771) B7538771
theorem B4182137 : Blo 1857630 4182137 := bstep (se 2 (by rfl) ⟨1568301, by rfl⟩ : syracuseStep 4182137 = 3136603) B3136603
theorem B3969337 : Blo 1857630 3969337 := bstep (se 2 (by rfl) ⟨1488501, by rfl⟩ : syracuseStep 3969337 = 2977003) B2977003
theorem B14119271 : Blo 1857630 14119271 := bstep (se 1 (by rfl) ⟨10589453, by rfl⟩ : syracuseStep 14119271 = 21178907) B21178907
theorem B4182443 : Blo 1857630 4182443 := bstep (se 1 (by rfl) ⟨3136832, by rfl⟩ : syracuseStep 4182443 = 6273665) B6273665
theorem B4182479 : Blo 1857630 4182479 := bstep (se 1 (by rfl) ⟨3136859, by rfl⟩ : syracuseStep 4182479 = 6273719) B6273719
theorem B137450029 : Blo 1857630 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B13759105 : Blo 1857630 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B3527327 : Blo 1857630 3527327 := bstep (se 1 (by rfl) ⟨2645495, by rfl⟩ : syracuseStep 3527327 = 5290991) B5290991
theorem B7058299 : Blo 1857630 7058299 := bstep (se 1 (by rfl) ⟨5293724, by rfl⟩ : syracuseStep 7058299 = 10587449) B10587449
theorem B3134767 : Blo 1857630 3134767 := bstep (se 1 (by rfl) ⟨2351075, by rfl⟩ : syracuseStep 3134767 = 4702151) B4702151
theorem B21181823 : Blo 1857630 21181823 := bstep (se 1 (by rfl) ⟨15886367, by rfl⟩ : syracuseStep 21181823 = 31772735) B31772735
theorem B50878019 : Blo 1857630 50878019 := bstep (se 1 (by rfl) ⟨38158514, by rfl⟩ : syracuseStep 50878019 = 76317029) B76317029
theorem B6272585 : Blo 1857630 6272585 := bstep (se 2 (by rfl) ⟨2352219, by rfl⟩ : syracuseStep 6272585 = 4704439) B4704439
theorem B14112467 : Blo 1857630 14112467 := bstep (se 1 (by rfl) ⟨10584350, by rfl⟩ : syracuseStep 14112467 = 21168701) B21168701
theorem B4183775 : Blo 1857630 4183775 := bstep (se 1 (by rfl) ⟨3137831, by rfl⟩ : syracuseStep 4183775 = 6275663) B6275663
theorem B7059271 : Blo 1857630 7059271 := bstep (se 1 (by rfl) ⟨5294453, by rfl⟩ : syracuseStep 7059271 = 10588907) B10588907
theorem B7534619 : Blo 1857630 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B4184135 : Blo 1857630 4184135 := bstep (se 1 (by rfl) ⟨3138101, by rfl⟩ : syracuseStep 4184135 = 6276203) B6276203
theorem B1857703 : Blo 1857630 1857703 := bstep (se 1 (by rfl) ⟨1393277, by rfl⟩ : syracuseStep 1857703 = 2786555) B2786555
theorem B14112953 : Blo 1857630 14112953 := bstep (se 2 (by rfl) ⟨5292357, by rfl⟩ : syracuseStep 14112953 = 10584715) B10584715
theorem B3135719 : Blo 1857630 3135719 := bstep (se 1 (by rfl) ⟨2351789, by rfl⟩ : syracuseStep 3135719 = 4703579) B4703579
theorem B35739953 : Blo 1857630 35739953 := bstep (se 2 (by rfl) ⟨13402482, by rfl⟩ : syracuseStep 35739953 = 26804965) B26804965
theorem B1857895 : Blo 1857630 1857895 := bstep (se 1 (by rfl) ⟨1393421, by rfl⟩ : syracuseStep 1857895 = 2786843) B2786843
theorem B1858151 : Blo 1857630 1858151 := bstep (se 1 (by rfl) ⟨1393613, by rfl⟩ : syracuseStep 1858151 = 2787227) B2787227
theorem B15284861 : Blo 1857630 15284861 := bstep (se 3 (by rfl) ⟨2865911, by rfl⟩ : syracuseStep 15284861 = 5731823) B5731823
theorem B1858175 : Blo 1857630 1858175 := bstep (se 1 (by rfl) ⟨1393631, by rfl⟩ : syracuseStep 1858175 = 2787263) B2787263
theorem B14113439 : Blo 1857630 14113439 := bstep (se 1 (by rfl) ⟨10585079, by rfl⟩ : syracuseStep 14113439 = 21170159) B21170159
theorem B31750865 : Blo 1857630 31750865 := bstep (se 2 (by rfl) ⟨11906574, by rfl⟩ : syracuseStep 31750865 = 23813149) B23813149
theorem B54295541 : Blo 1857630 54295541 := bstep (se 5 (by rfl) ⟨2545103, by rfl⟩ : syracuseStep 54295541 = 5090207) B5090207
theorem B1858591 : Blo 1857630 1858591 := bstep (se 1 (by rfl) ⟨1393943, by rfl⟩ : syracuseStep 1858591 = 2787887) B2787887
theorem B1858671 : Blo 1857630 1858671 := bstep (se 1 (by rfl) ⟨1394003, by rfl⟩ : syracuseStep 1858671 = 2788007) B2788007
theorem B1858715 : Blo 1857630 1858715 := bstep (se 1 (by rfl) ⟨1394036, by rfl⟩ : syracuseStep 1858715 = 2788073) B2788073
theorem B1858719 : Blo 1857630 1858719 := bstep (se 1 (by rfl) ⟨1394039, by rfl⟩ : syracuseStep 1858719 = 2788079) B2788079
theorem B1858751 : Blo 1857630 1858751 := bstep (se 1 (by rfl) ⟨1394063, by rfl⟩ : syracuseStep 1858751 = 2788127) B2788127
theorem B60308711 : Blo 1857630 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B1858971 : Blo 1857630 1858971 := bstep (se 1 (by rfl) ⟨1394228, by rfl⟩ : syracuseStep 1858971 = 2788457) B2788457
theorem B6274475 : Blo 1857630 6274475 := bstep (se 1 (by rfl) ⟨4705856, by rfl⟩ : syracuseStep 6274475 = 9411713) B9411713
theorem B9534955 : Blo 1857630 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B10583531 : Blo 1857630 10583531 := bstep (se 1 (by rfl) ⟨7937648, by rfl⟩ : syracuseStep 10583531 = 15875297) B15875297
theorem B1859055 : Blo 1857630 1859055 := bstep (se 1 (by rfl) ⟨1394291, by rfl⟩ : syracuseStep 1859055 = 2788583) B2788583
theorem B5291561 : Blo 1857630 5291561 := bstep (se 2 (by rfl) ⟨1984335, by rfl⟩ : syracuseStep 5291561 = 3968671) B3968671
theorem B15875675 : Blo 1857630 15875675 := bstep (se 1 (by rfl) ⟨11906756, by rfl⟩ : syracuseStep 15875675 = 23813513) B23813513
theorem B1859391 : Blo 1857630 1859391 := bstep (se 1 (by rfl) ⟨1394543, by rfl⟩ : syracuseStep 1859391 = 2789087) B2789087
theorem B3137359 : Blo 1857630 3137359 := bstep (se 1 (by rfl) ⟨2353019, by rfl⟩ : syracuseStep 3137359 = 4706039) B4706039
theorem B1859579 : Blo 1857630 1859579 := bstep (se 1 (by rfl) ⟨1394684, by rfl⟩ : syracuseStep 1859579 = 2789369) B2789369
theorem B6701129 : Blo 1857630 6701129 := bstep (se 2 (by rfl) ⟨2512923, by rfl⟩ : syracuseStep 6701129 = 5025847) B5025847
theorem B9412847 : Blo 1857630 9412847 := bstep (se 1 (by rfl) ⟨7059635, by rfl⟩ : syracuseStep 9412847 = 14119271) B14119271
theorem B94208363 : Blo 1857630 94208363 := bstep (se 1 (by rfl) ⟨70656272, by rfl⟩ : syracuseStep 94208363 = 141312545) B141312545
theorem B5292449 : Blo 1857630 5292449 := bstep (se 2 (by rfl) ⟨1984668, by rfl⟩ : syracuseStep 5292449 = 3969337) B3969337
theorem B32646125 : Blo 1857630 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B5023079 : Blo 1857630 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B2786795 : Blo 1857630 2786795 := bstep (se 1 (by rfl) ⟨2090096, by rfl⟩ : syracuseStep 2786795 = 4180193) B4180193
theorem B2090479 : Blo 1857630 2090479 := bstep (se 1 (by rfl) ⟨1567859, by rfl⟩ : syracuseStep 2090479 = 3135719) B3135719
theorem B10585673 : Blo 1857630 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B4179689 : Blo 1857630 4179689 := bstep (se 2 (by rfl) ⟨1567383, by rfl⟩ : syracuseStep 4179689 = 3134767) B3134767
theorem B4179707 : Blo 1857630 4179707 := bstep (se 1 (by rfl) ⟨3134780, by rfl⟩ : syracuseStep 4179707 = 6269561) B6269561
theorem B9406205 : Blo 1857630 9406205 := bstep (se 3 (by rfl) ⟨1763663, by rfl⟩ : syracuseStep 9406205 = 3527327) B3527327
theorem B5293907 : Blo 1857630 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B2787239 : Blo 1857630 2787239 := bstep (se 1 (by rfl) ⟨2090429, by rfl⟩ : syracuseStep 2787239 = 4180859) B4180859
theorem B4179923 : Blo 1857630 4179923 := bstep (se 1 (by rfl) ⟨3134942, by rfl⟩ : syracuseStep 4179923 = 6269885) B6269885
theorem B7055687 : Blo 1857630 7055687 := bstep (se 1 (by rfl) ⟨5291765, by rfl⟩ : syracuseStep 7055687 = 10583531) B10583531
theorem B10586447 : Blo 1857630 10586447 := bstep (se 1 (by rfl) ⟨7939835, by rfl⟩ : syracuseStep 10586447 = 15879671) B15879671
theorem B2788091 : Blo 1857630 2788091 := bstep (se 1 (by rfl) ⟨2091068, by rfl⟩ : syracuseStep 2788091 = 4182137) B4182137
theorem B128789423 : Blo 1857630 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B2788295 : Blo 1857630 2788295 := bstep (se 1 (by rfl) ⟨2091221, by rfl⟩ : syracuseStep 2788295 = 4182443) B4182443
theorem B2788319 : Blo 1857630 2788319 := bstep (se 1 (by rfl) ⟨2091239, by rfl⟩ : syracuseStep 2788319 = 4182479) B4182479
theorem B16952485 : Blo 1857630 16952485 := bstep (se 4 (by rfl) ⟨1589295, by rfl⟩ : syracuseStep 16952485 = 3178591) B3178591
theorem B183266705 : Blo 1857630 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B14118299 : Blo 1857630 14118299 := bstep (se 1 (by rfl) ⟨10588724, by rfl⟩ : syracuseStep 14118299 = 21177449) B21177449
theorem B21171617 : Blo 1857630 21171617 := bstep (se 2 (by rfl) ⟨7939356, by rfl⟩ : syracuseStep 21171617 = 15878713) B15878713
theorem B18345473 : Blo 1857630 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B33918679 : Blo 1857630 33918679 := bstep (se 1 (by rfl) ⟨25439009, by rfl⟩ : syracuseStep 33918679 = 50878019) B50878019
theorem B4181723 : Blo 1857630 4181723 := bstep (se 1 (by rfl) ⟨3136292, by rfl⟩ : syracuseStep 4181723 = 6272585) B6272585
theorem B2789129 : Blo 1857630 2789129 := bstep (se 2 (by rfl) ⟨1045923, by rfl⟩ : syracuseStep 2789129 = 2091847) B2091847
theorem B9408311 : Blo 1857630 9408311 := bstep (se 1 (by rfl) ⟨7056233, by rfl⟩ : syracuseStep 9408311 = 14112467) B14112467
theorem B2789183 : Blo 1857630 2789183 := bstep (se 1 (by rfl) ⟨2091887, by rfl⟩ : syracuseStep 2789183 = 4183775) B4183775
theorem B20099009 : Blo 1857630 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B2789423 : Blo 1857630 2789423 := bstep (se 1 (by rfl) ⟨2092067, by rfl⟩ : syracuseStep 2789423 = 4184135) B4184135
theorem B9408635 : Blo 1857630 9408635 := bstep (se 1 (by rfl) ⟨7056476, by rfl⟩ : syracuseStep 9408635 = 14112953) B14112953
theorem B23826635 : Blo 1857630 23826635 := bstep (se 1 (by rfl) ⟨17869976, by rfl⟩ : syracuseStep 23826635 = 35739953) B35739953
theorem B9408959 : Blo 1857630 9408959 := bstep (se 1 (by rfl) ⟨7056719, by rfl⟩ : syracuseStep 9408959 = 14113439) B14113439
theorem B110105081 : Blo 1857630 110105081 := bstep (se 2 (by rfl) ⟨41289405, by rfl⟩ : syracuseStep 110105081 = 82578811) B82578811
theorem B36197027 : Blo 1857630 36197027 := bstep (se 1 (by rfl) ⟨27147770, by rfl⟩ : syracuseStep 36197027 = 54295541) B54295541
theorem B4182983 : Blo 1857630 4182983 := bstep (se 1 (by rfl) ⟨3137237, by rfl⟩ : syracuseStep 4182983 = 6274475) B6274475
theorem B3527707 : Blo 1857630 3527707 := bstep (se 1 (by rfl) ⟨2645780, by rfl⟩ : syracuseStep 3527707 = 5291561) B5291561
theorem B4183145 : Blo 1857630 4183145 := bstep (se 2 (by rfl) ⟨1568679, by rfl⟩ : syracuseStep 4183145 = 3137359) B3137359
theorem B7058771 : Blo 1857630 7058771 := bstep (se 1 (by rfl) ⟨5294078, by rfl⟩ : syracuseStep 7058771 = 10588157) B10588157
theorem B9410255 : Blo 1857630 9410255 := bstep (se 1 (by rfl) ⟨7057691, by rfl⟩ : syracuseStep 9410255 = 14115383) B14115383
theorem B16947371 : Blo 1857630 16947371 := bstep (se 1 (by rfl) ⟨12710528, by rfl⟩ : syracuseStep 16947371 = 25421057) B25421057
theorem B1857775 : Blo 1857630 1857775 := bstep (se 1 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 1857775 = 2786663) B2786663
theorem B14121215 : Blo 1857630 14121215 := bstep (se 1 (by rfl) ⟨10590911, by rfl⟩ : syracuseStep 14121215 = 21181823) B21181823
theorem B1857855 : Blo 1857630 1857855 := bstep (se 1 (by rfl) ⟨1393391, by rfl⟩ : syracuseStep 1857855 = 2786783) B2786783
theorem B3135847 : Blo 1857630 3135847 := bstep (se 1 (by rfl) ⟨2351885, by rfl⟩ : syracuseStep 3135847 = 4703771) B4703771
theorem B1858031 : Blo 1857630 1858031 := bstep (se 1 (by rfl) ⟨1393523, by rfl⟩ : syracuseStep 1858031 = 2787047) B2787047
theorem B9411065 : Blo 1857630 9411065 := bstep (se 2 (by rfl) ⟨3529149, by rfl⟩ : syracuseStep 9411065 = 7058299) B7058299
theorem B1858555 : Blo 1857630 1858555 := bstep (se 1 (by rfl) ⟨1393916, by rfl⟩ : syracuseStep 1858555 = 2787833) B2787833
theorem B1858587 : Blo 1857630 1858587 := bstep (se 1 (by rfl) ⟨1393940, by rfl⟩ : syracuseStep 1858587 = 2787881) B2787881
theorem B22600775 : Blo 1857630 22600775 := bstep (se 1 (by rfl) ⟨16950581, by rfl⟩ : syracuseStep 22600775 = 33901163) B33901163
theorem B10189907 : Blo 1857630 10189907 := bstep (se 1 (by rfl) ⟨7642430, by rfl⟩ : syracuseStep 10189907 = 15284861) B15284861
theorem B21167243 : Blo 1857630 21167243 := bstep (se 1 (by rfl) ⟨15875432, by rfl⟩ : syracuseStep 21167243 = 31750865) B31750865
theorem B12713273 : Blo 1857630 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B40205807 : Blo 1857630 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B10583783 : Blo 1857630 10583783 := bstep (se 1 (by rfl) ⟨7937837, by rfl⟩ : syracuseStep 10583783 = 15875675) B15875675
theorem B9412361 : Blo 1857630 9412361 := bstep (se 2 (by rfl) ⟨3529635, by rfl⟩ : syracuseStep 9412361 = 7059271) B7059271
theorem B1859431 : Blo 1857630 1859431 := bstep (se 1 (by rfl) ⟨1394573, by rfl⟩ : syracuseStep 1859431 = 2789147) B2789147
theorem B1859487 : Blo 1857630 1859487 := bstep (se 1 (by rfl) ⟨1394615, by rfl⟩ : syracuseStep 1859487 = 2789231) B2789231
theorem B3137447 : Blo 1857630 3137447 := bstep (se 1 (by rfl) ⟨2353085, by rfl⟩ : syracuseStep 3137447 = 4706171) B4706171
theorem B9412523 : Blo 1857630 9412523 := bstep (se 1 (by rfl) ⟨7059392, by rfl⟩ : syracuseStep 9412523 = 14118785) B14118785
theorem B1859615 : Blo 1857630 1859615 := bstep (se 1 (by rfl) ⟨1394711, by rfl⟩ : syracuseStep 1859615 = 2789423) B2789423
theorem B15884423 : Blo 1857630 15884423 := bstep (se 1 (by rfl) ⟨11913317, by rfl⟩ : syracuseStep 15884423 = 23826635) B23826635
theorem B6275231 : Blo 1857630 6275231 := bstep (se 1 (by rfl) ⟨4706423, by rfl⟩ : syracuseStep 6275231 = 9412847) B9412847
theorem B2786459 : Blo 1857630 2786459 := bstep (se 1 (by rfl) ⟨2089844, by rfl⟩ : syracuseStep 2786459 = 4179689) B4179689
theorem B2786471 : Blo 1857630 2786471 := bstep (se 1 (by rfl) ⟨2089853, by rfl⟩ : syracuseStep 2786471 = 4179707) B4179707
theorem B2786615 : Blo 1857630 2786615 := bstep (se 1 (by rfl) ⟨2089961, by rfl⟩ : syracuseStep 2786615 = 4179923) B4179923
theorem B4703609 : Blo 1857630 4703609 := bstep (se 2 (by rfl) ⟨1763853, by rfl⟩ : syracuseStep 4703609 = 3527707) B3527707
theorem B11298247 : Blo 1857630 11298247 := bstep (se 1 (by rfl) ⟨8473685, by rfl⟩ : syracuseStep 11298247 = 16947371) B16947371
theorem B9414143 : Blo 1857630 9414143 := bstep (se 1 (by rfl) ⟨7060607, by rfl⟩ : syracuseStep 9414143 = 14121215) B14121215
theorem B4703791 : Blo 1857630 4703791 := bstep (se 1 (by rfl) ⟨3527843, by rfl⟩ : syracuseStep 4703791 = 7055687) B7055687
theorem B22603313 : Blo 1857630 22603313 := bstep (se 2 (by rfl) ⟨8476242, by rfl⟩ : syracuseStep 22603313 = 16952485) B16952485
theorem B2787305 : Blo 1857630 2787305 := bstep (se 2 (by rfl) ⟨1045239, by rfl⟩ : syracuseStep 2787305 = 2090479) B2090479
theorem B15067183 : Blo 1857630 15067183 := bstep (se 1 (by rfl) ⟨11300387, by rfl⟩ : syracuseStep 15067183 = 22600775) B22600775
theorem B6793271 : Blo 1857630 6793271 := bstep (se 1 (by rfl) ⟨5094953, by rfl⟩ : syracuseStep 6793271 = 10189907) B10189907
theorem B122177803 : Blo 1857630 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B2787815 : Blo 1857630 2787815 := bstep (se 1 (by rfl) ⟨2090861, by rfl⟩ : syracuseStep 2787815 = 4181723) B4181723
theorem B7055855 : Blo 1857630 7055855 := bstep (se 1 (by rfl) ⟨5291891, by rfl⟩ : syracuseStep 7055855 = 10583783) B10583783
theorem B2091631 : Blo 1857630 2091631 := bstep (se 1 (by rfl) ⟨1568723, by rfl⟩ : syracuseStep 2091631 = 3137447) B3137447
theorem B4467419 : Blo 1857630 4467419 := bstep (se 1 (by rfl) ⟨3350564, by rfl⟩ : syracuseStep 4467419 = 6701129) B6701129
theorem B73403387 : Blo 1857630 73403387 := bstep (se 1 (by rfl) ⟨55052540, by rfl⟩ : syracuseStep 73403387 = 110105081) B110105081
theorem B4181129 : Blo 1857630 4181129 := bstep (se 2 (by rfl) ⟨1567923, by rfl⟩ : syracuseStep 4181129 = 3135847) B3135847
theorem B2788655 : Blo 1857630 2788655 := bstep (se 1 (by rfl) ⟨2091491, by rfl⟩ : syracuseStep 2788655 = 4182983) B4182983
theorem B2788763 : Blo 1857630 2788763 := bstep (se 1 (by rfl) ⟨2091572, by rfl⟩ : syracuseStep 2788763 = 4183145) B4183145
theorem B4705847 : Blo 1857630 4705847 := bstep (se 1 (by rfl) ⟨3529385, by rfl⟩ : syracuseStep 4705847 = 7058771) B7058771
theorem B7057115 : Blo 1857630 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B6270803 : Blo 1857630 6270803 := bstep (se 1 (by rfl) ⟨4703102, by rfl⟩ : syracuseStep 6270803 = 9406205) B9406205
theorem B7057631 : Blo 1857630 7057631 := bstep (se 1 (by rfl) ⟨5293223, by rfl⟩ : syracuseStep 7057631 = 10586447) B10586447
theorem B14111495 : Blo 1857630 14111495 := bstep (se 1 (by rfl) ⟨10583621, by rfl⟩ : syracuseStep 14111495 = 21167243) B21167243
theorem B8475515 : Blo 1857630 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B45224905 : Blo 1857630 45224905 := bstep (se 2 (by rfl) ⟨16959339, by rfl⟩ : syracuseStep 45224905 = 33918679) B33918679
theorem B6272207 : Blo 1857630 6272207 := bstep (se 1 (by rfl) ⟨4704155, by rfl⟩ : syracuseStep 6272207 = 9408311) B9408311
theorem B13399339 : Blo 1857630 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B6272423 : Blo 1857630 6272423 := bstep (se 1 (by rfl) ⟨4704317, by rfl⟩ : syracuseStep 6272423 = 9408635) B9408635
theorem B62805575 : Blo 1857630 62805575 := bstep (se 1 (by rfl) ⟨47104181, by rfl⟩ : syracuseStep 62805575 = 94208363) B94208363
theorem B3528299 : Blo 1857630 3528299 := bstep (se 1 (by rfl) ⟨2646224, by rfl⟩ : syracuseStep 3528299 = 5292449) B5292449
theorem B6272639 : Blo 1857630 6272639 := bstep (se 1 (by rfl) ⟨4704479, by rfl⟩ : syracuseStep 6272639 = 9408959) B9408959
theorem B24131351 : Blo 1857630 24131351 := bstep (se 1 (by rfl) ⟨18098513, by rfl⟩ : syracuseStep 24131351 = 36197027) B36197027
theorem B3348719 : Blo 1857630 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B1857863 : Blo 1857630 1857863 := bstep (se 1 (by rfl) ⟨1393397, by rfl⟩ : syracuseStep 1857863 = 2786795) B2786795
theorem B6273503 : Blo 1857630 6273503 := bstep (se 1 (by rfl) ⟨4705127, by rfl⟩ : syracuseStep 6273503 = 9410255) B9410255
theorem B3529271 : Blo 1857630 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B1858159 : Blo 1857630 1858159 := bstep (se 1 (by rfl) ⟨1393619, by rfl⟩ : syracuseStep 1858159 = 2787239) B2787239
theorem B6274043 : Blo 1857630 6274043 := bstep (se 1 (by rfl) ⟨4705532, by rfl⟩ : syracuseStep 6274043 = 9411065) B9411065
theorem B1858727 : Blo 1857630 1858727 := bstep (se 1 (by rfl) ⟨1394045, by rfl⟩ : syracuseStep 1858727 = 2788091) B2788091
theorem B85859615 : Blo 1857630 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B1858863 : Blo 1857630 1858863 := bstep (se 1 (by rfl) ⟨1394147, by rfl⟩ : syracuseStep 1858863 = 2788295) B2788295
theorem B1858879 : Blo 1857630 1858879 := bstep (se 1 (by rfl) ⟨1394159, by rfl⟩ : syracuseStep 1858879 = 2788319) B2788319
theorem B9412199 : Blo 1857630 9412199 := bstep (se 1 (by rfl) ⟨7059149, by rfl⟩ : syracuseStep 9412199 = 14118299) B14118299
theorem B14114411 : Blo 1857630 14114411 := bstep (se 1 (by rfl) ⟨10585808, by rfl⟩ : syracuseStep 14114411 = 21171617) B21171617
theorem B26803871 : Blo 1857630 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B12230315 : Blo 1857630 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B6274907 : Blo 1857630 6274907 := bstep (se 1 (by rfl) ⟨4706180, by rfl⟩ : syracuseStep 6274907 = 9412361) B9412361
theorem B1859419 : Blo 1857630 1859419 := bstep (se 1 (by rfl) ⟨1394564, by rfl⟩ : syracuseStep 1859419 = 2789129) B2789129
theorem B1859455 : Blo 1857630 1859455 := bstep (se 1 (by rfl) ⟨1394591, by rfl⟩ : syracuseStep 1859455 = 2789183) B2789183
theorem B6275015 : Blo 1857630 6275015 := bstep (se 1 (by rfl) ⟨4706261, by rfl⟩ : syracuseStep 6275015 = 9412523) B9412523
theorem B87056333 : Blo 1857630 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B6276095 : Blo 1857630 6276095 := bstep (se 1 (by rfl) ⟨4707071, by rfl⟩ : syracuseStep 6276095 = 9414143) B9414143
theorem B4703903 : Blo 1857630 4703903 := bstep (se 1 (by rfl) ⟨3527927, by rfl⟩ : syracuseStep 4703903 = 7055855) B7055855
theorem B2787419 : Blo 1857630 2787419 := bstep (se 1 (by rfl) ⟨2090564, by rfl⟩ : syracuseStep 2787419 = 4181129) B4181129
theorem B57239743 : Blo 1857630 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B17869247 : Blo 1857630 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B8153543 : Blo 1857630 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B4704743 : Blo 1857630 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B4180535 : Blo 1857630 4180535 := bstep (se 1 (by rfl) ⟨3135401, by rfl⟩ : syracuseStep 4180535 = 6270803) B6270803
theorem B20089577 : Blo 1857630 20089577 := bstep (se 2 (by rfl) ⟨7533591, by rfl⟩ : syracuseStep 20089577 = 15067183) B15067183
theorem B4705087 : Blo 1857630 4705087 := bstep (se 1 (by rfl) ⟨3528815, by rfl⟩ : syracuseStep 4705087 = 7057631) B7057631
theorem B9407663 : Blo 1857630 9407663 := bstep (se 1 (by rfl) ⟨7055747, by rfl⟩ : syracuseStep 9407663 = 14111495) B14111495
theorem B4181471 : Blo 1857630 4181471 := bstep (se 1 (by rfl) ⟨3136103, by rfl⟩ : syracuseStep 4181471 = 6272207) B6272207
theorem B2788841 : Blo 1857630 2788841 := bstep (se 2 (by rfl) ⟨1045815, by rfl⟩ : syracuseStep 2788841 = 2091631) B2091631
theorem B4181615 : Blo 1857630 4181615 := bstep (se 1 (by rfl) ⟨3136211, by rfl⟩ : syracuseStep 4181615 = 6272423) B6272423
theorem B15068875 : Blo 1857630 15068875 := bstep (se 1 (by rfl) ⟨11301656, by rfl⟩ : syracuseStep 15068875 = 22603313) B22603313
theorem B4181759 : Blo 1857630 4181759 := bstep (se 1 (by rfl) ⟨3136319, by rfl⟩ : syracuseStep 4181759 = 6272639) B6272639
theorem B2232479 : Blo 1857630 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B167481533 : Blo 1857630 167481533 := bstep (se 3 (by rfl) ⟨31402787, by rfl⟩ : syracuseStep 167481533 = 62805575) B62805575
theorem B9408797 : Blo 1857630 9408797 := bstep (se 3 (by rfl) ⟨1764149, by rfl⟩ : syracuseStep 9408797 = 3528299) B3528299
theorem B4182335 : Blo 1857630 4182335 := bstep (se 1 (by rfl) ⟨3136751, by rfl⟩ : syracuseStep 4182335 = 6273503) B6273503
theorem B2978279 : Blo 1857630 2978279 := bstep (se 1 (by rfl) ⟨2233709, by rfl⟩ : syracuseStep 2978279 = 4467419) B4467419
theorem B48935591 : Blo 1857630 48935591 := bstep (se 1 (by rfl) ⟨36701693, by rfl⟩ : syracuseStep 48935591 = 73403387) B73403387
theorem B4182695 : Blo 1857630 4182695 := bstep (se 1 (by rfl) ⟨3137021, by rfl⟩ : syracuseStep 4182695 = 6274043) B6274043
theorem B6271721 : Blo 1857630 6271721 := bstep (se 2 (by rfl) ⟨2351895, by rfl⟩ : syracuseStep 6271721 = 4703791) B4703791
theorem B60257317 : Blo 1857630 60257317 := bstep (se 4 (by rfl) ⟨5649123, by rfl⟩ : syracuseStep 60257317 = 11298247) B11298247
theorem B9409607 : Blo 1857630 9409607 := bstep (se 1 (by rfl) ⟨7057205, by rfl⟩ : syracuseStep 9409607 = 14114411) B14114411
theorem B4183271 : Blo 1857630 4183271 := bstep (se 1 (by rfl) ⟨3137453, by rfl⟩ : syracuseStep 4183271 = 6274907) B6274907
theorem B4183343 : Blo 1857630 4183343 := bstep (se 1 (by rfl) ⟨3137507, by rfl⟩ : syracuseStep 4183343 = 6275015) B6275015
theorem B58037555 : Blo 1857630 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B10589615 : Blo 1857630 10589615 := bstep (se 1 (by rfl) ⟨7942211, by rfl⟩ : syracuseStep 10589615 = 15884423) B15884423
theorem B4183487 : Blo 1857630 4183487 := bstep (se 1 (by rfl) ⟨3137615, by rfl⟩ : syracuseStep 4183487 = 6275231) B6275231
theorem B162903737 : Blo 1857630 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B5650343 : Blo 1857630 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B1857639 : Blo 1857630 1857639 := bstep (se 1 (by rfl) ⟨1393229, by rfl⟩ : syracuseStep 1857639 = 2786459) B2786459
theorem B1857647 : Blo 1857630 1857647 := bstep (se 1 (by rfl) ⟨1393235, by rfl⟩ : syracuseStep 1857647 = 2786471) B2786471
theorem B1857743 : Blo 1857630 1857743 := bstep (se 1 (by rfl) ⟨1393307, by rfl⟩ : syracuseStep 1857743 = 2786615) B2786615
theorem B3135739 : Blo 1857630 3135739 := bstep (se 1 (by rfl) ⟨2351804, by rfl⟩ : syracuseStep 3135739 = 4703609) B4703609
theorem B16087567 : Blo 1857630 16087567 := bstep (se 1 (by rfl) ⟨12065675, by rfl⟩ : syracuseStep 16087567 = 24131351) B24131351
theorem B60299873 : Blo 1857630 60299873 := bstep (se 2 (by rfl) ⟨22612452, by rfl⟩ : syracuseStep 60299873 = 45224905) B45224905
theorem B1858203 : Blo 1857630 1858203 := bstep (se 1 (by rfl) ⟨1393652, by rfl⟩ : syracuseStep 1858203 = 2787305) B2787305
theorem B4528847 : Blo 1857630 4528847 := bstep (se 1 (by rfl) ⟨3396635, by rfl⟩ : syracuseStep 4528847 = 6793271) B6793271
theorem B9411389 : Blo 1857630 9411389 := bstep (se 3 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 9411389 = 3529271) B3529271
theorem B1858543 : Blo 1857630 1858543 := bstep (se 1 (by rfl) ⟨1393907, by rfl⟩ : syracuseStep 1858543 = 2787815) B2787815
theorem B17865785 : Blo 1857630 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B1859103 : Blo 1857630 1859103 := bstep (se 1 (by rfl) ⟨1394327, by rfl⟩ : syracuseStep 1859103 = 2788655) B2788655
theorem B1859175 : Blo 1857630 1859175 := bstep (se 1 (by rfl) ⟨1394381, by rfl⟩ : syracuseStep 1859175 = 2788763) B2788763
theorem B3137231 : Blo 1857630 3137231 := bstep (se 1 (by rfl) ⟨2352923, by rfl⟩ : syracuseStep 3137231 = 4705847) B4705847
theorem B6274799 : Blo 1857630 6274799 := bstep (se 1 (by rfl) ⟨4706099, by rfl⟩ : syracuseStep 6274799 = 9412199) B9412199
theorem B38691703 : Blo 1857630 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B108602491 : Blo 1857630 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B11912831 : Blo 1857630 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B2787023 : Blo 1857630 2787023 := bstep (se 1 (by rfl) ⟨2090267, by rfl⟩ : syracuseStep 2787023 = 4180535) B4180535
theorem B40199915 : Blo 1857630 40199915 := bstep (se 1 (by rfl) ⟨30149936, by rfl⟩ : syracuseStep 40199915 = 60299873) B60299873
theorem B2787647 : Blo 1857630 2787647 := bstep (se 1 (by rfl) ⟨2090735, by rfl⟩ : syracuseStep 2787647 = 4181471) B4181471
theorem B2787743 : Blo 1857630 2787743 := bstep (se 1 (by rfl) ⟨2090807, by rfl⟩ : syracuseStep 2787743 = 4181615) B4181615
theorem B2091487 : Blo 1857630 2091487 := bstep (se 1 (by rfl) ⟨1568615, by rfl⟩ : syracuseStep 2091487 = 3137231) B3137231
theorem B2787839 : Blo 1857630 2787839 := bstep (se 1 (by rfl) ⟨2090879, by rfl⟩ : syracuseStep 2787839 = 4181759) B4181759
theorem B2788223 : Blo 1857630 2788223 := bstep (se 1 (by rfl) ⟨2091167, by rfl⟩ : syracuseStep 2788223 = 4182335) B4182335
theorem B76319657 : Blo 1857630 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B1985519 : Blo 1857630 1985519 := bstep (se 1 (by rfl) ⟨1489139, by rfl⟩ : syracuseStep 1985519 = 2978279) B2978279
theorem B4180985 : Blo 1857630 4180985 := bstep (se 2 (by rfl) ⟨1567869, by rfl⟩ : syracuseStep 4180985 = 3135739) B3135739
theorem B32623727 : Blo 1857630 32623727 := bstep (se 1 (by rfl) ⟨24467795, by rfl⟩ : syracuseStep 32623727 = 48935591) B48935591
theorem B2788463 : Blo 1857630 2788463 := bstep (se 1 (by rfl) ⟨2091347, by rfl⟩ : syracuseStep 2788463 = 4182695) B4182695
theorem B4181147 : Blo 1857630 4181147 := bstep (se 1 (by rfl) ⟨3135860, by rfl⟩ : syracuseStep 4181147 = 6271721) B6271721
theorem B21450089 : Blo 1857630 21450089 := bstep (se 2 (by rfl) ⟨8043783, by rfl⟩ : syracuseStep 21450089 = 16087567) B16087567
theorem B2788847 : Blo 1857630 2788847 := bstep (se 1 (by rfl) ⟨2091635, by rfl⟩ : syracuseStep 2788847 = 4183271) B4183271
theorem B2788895 : Blo 1857630 2788895 := bstep (se 1 (by rfl) ⟨2091671, by rfl⟩ : syracuseStep 2788895 = 4183343) B4183343
theorem B2788991 : Blo 1857630 2788991 := bstep (se 1 (by rfl) ⟨2091743, by rfl⟩ : syracuseStep 2788991 = 4183487) B4183487
theorem B80343089 : Blo 1857630 80343089 := bstep (se 2 (by rfl) ⟨30128658, by rfl⟩ : syracuseStep 80343089 = 60257317) B60257317
theorem B5435695 : Blo 1857630 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B3019231 : Blo 1857630 3019231 := bstep (se 1 (by rfl) ⟨2264423, by rfl⟩ : syracuseStep 3019231 = 4528847) B4528847
theorem B53572205 : Blo 1857630 53572205 := bstep (se 3 (by rfl) ⟨10044788, by rfl⟩ : syracuseStep 53572205 = 20089577) B20089577
theorem B6271775 : Blo 1857630 6271775 := bstep (se 1 (by rfl) ⟨4703831, by rfl⟩ : syracuseStep 6271775 = 9407663) B9407663
theorem B20091833 : Blo 1857630 20091833 := bstep (se 2 (by rfl) ⟨7534437, by rfl⟩ : syracuseStep 20091833 = 15068875) B15068875
theorem B4183199 : Blo 1857630 4183199 := bstep (se 1 (by rfl) ⟨3137399, by rfl⟩ : syracuseStep 4183199 = 6274799) B6274799
theorem B111654355 : Blo 1857630 111654355 := bstep (se 1 (by rfl) ⟨83740766, by rfl⟩ : syracuseStep 111654355 = 167481533) B167481533
theorem B6272531 : Blo 1857630 6272531 := bstep (se 1 (by rfl) ⟨4704398, by rfl⟩ : syracuseStep 6272531 = 9408797) B9408797
theorem B5953277 : Blo 1857630 5953277 := bstep (se 3 (by rfl) ⟨1116239, by rfl⟩ : syracuseStep 5953277 = 2232479) B2232479
theorem B4184063 : Blo 1857630 4184063 := bstep (se 1 (by rfl) ⟨3138047, by rfl⟩ : syracuseStep 4184063 = 6276095) B6276095
theorem B6273071 : Blo 1857630 6273071 := bstep (se 1 (by rfl) ⟨4704803, by rfl⟩ : syracuseStep 6273071 = 9409607) B9409607
theorem B7059743 : Blo 1857630 7059743 := bstep (se 1 (by rfl) ⟨5294807, by rfl⟩ : syracuseStep 7059743 = 10589615) B10589615
theorem B6273449 : Blo 1857630 6273449 := bstep (se 2 (by rfl) ⟨2352543, by rfl⟩ : syracuseStep 6273449 = 4705087) B4705087
theorem B3135935 : Blo 1857630 3135935 := bstep (se 1 (by rfl) ⟨2351951, by rfl⟩ : syracuseStep 3135935 = 4703903) B4703903
theorem B3766895 : Blo 1857630 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B1858279 : Blo 1857630 1858279 := bstep (se 1 (by rfl) ⟨1393709, by rfl⟩ : syracuseStep 1858279 = 2787419) B2787419
theorem B3136495 : Blo 1857630 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B6274259 : Blo 1857630 6274259 := bstep (se 1 (by rfl) ⟨4705694, by rfl⟩ : syracuseStep 6274259 = 9411389) B9411389
theorem B11910523 : Blo 1857630 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B1859227 : Blo 1857630 1859227 := bstep (se 1 (by rfl) ⟨1394420, by rfl⟩ : syracuseStep 1859227 = 2788841) B2788841
theorem B13394555 : Blo 1857630 13394555 := bstep (se 1 (by rfl) ⟨10045916, by rfl⟩ : syracuseStep 13394555 = 20091833) B20091833
theorem B144803321 : Blo 1857630 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B2090623 : Blo 1857630 2090623 := bstep (se 1 (by rfl) ⟨1567967, by rfl⟩ : syracuseStep 2090623 = 3135935) B3135935
theorem B2787323 : Blo 1857630 2787323 := bstep (se 1 (by rfl) ⟨2090492, by rfl⟩ : syracuseStep 2787323 = 4180985) B4180985
theorem B2787431 : Blo 1857630 2787431 := bstep (se 1 (by rfl) ⟨2090573, by rfl⟩ : syracuseStep 2787431 = 4181147) B4181147
theorem B5294717 : Blo 1857630 5294717 := bstep (se 3 (by rfl) ⟨992759, by rfl⟩ : syracuseStep 5294717 = 1985519) B1985519
theorem B53562059 : Blo 1857630 53562059 := bstep (se 1 (by rfl) ⟨40171544, by rfl⟩ : syracuseStep 53562059 = 80343089) B80343089
theorem B4181183 : Blo 1857630 4181183 := bstep (se 1 (by rfl) ⟨3135887, by rfl⟩ : syracuseStep 4181183 = 6271775) B6271775
theorem B2788649 : Blo 1857630 2788649 := bstep (se 2 (by rfl) ⟨1045743, by rfl⟩ : syracuseStep 2788649 = 2091487) B2091487
theorem B4025641 : Blo 1857630 4025641 := bstep (se 2 (by rfl) ⟨1509615, by rfl⟩ : syracuseStep 4025641 = 3019231) B3019231
theorem B2788799 : Blo 1857630 2788799 := bstep (se 1 (by rfl) ⟨2091599, by rfl⟩ : syracuseStep 2788799 = 4183199) B4183199
theorem B4181687 : Blo 1857630 4181687 := bstep (se 1 (by rfl) ⟨3136265, by rfl⟩ : syracuseStep 4181687 = 6272531) B6272531
theorem B7941887 : Blo 1857630 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B26799943 : Blo 1857630 26799943 := bstep (se 1 (by rfl) ⟨20099957, by rfl⟩ : syracuseStep 26799943 = 40199915) B40199915
theorem B51588937 : Blo 1857630 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B3968851 : Blo 1857630 3968851 := bstep (se 1 (by rfl) ⟨2976638, by rfl⟩ : syracuseStep 3968851 = 5953277) B5953277
theorem B4181993 : Blo 1857630 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B2789375 : Blo 1857630 2789375 := bstep (se 1 (by rfl) ⟨2092031, by rfl⟩ : syracuseStep 2789375 = 4184063) B4184063
theorem B4182047 : Blo 1857630 4182047 := bstep (se 1 (by rfl) ⟨3136535, by rfl⟩ : syracuseStep 4182047 = 6273071) B6273071
theorem B4706495 : Blo 1857630 4706495 := bstep (se 1 (by rfl) ⟨3529871, by rfl⟩ : syracuseStep 4706495 = 7059743) B7059743
theorem B4182299 : Blo 1857630 4182299 := bstep (se 1 (by rfl) ⟨3136724, by rfl⟩ : syracuseStep 4182299 = 6273449) B6273449
theorem B2511263 : Blo 1857630 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B15880697 : Blo 1857630 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B4182839 : Blo 1857630 4182839 := bstep (se 1 (by rfl) ⟨3137129, by rfl⟩ : syracuseStep 4182839 = 6274259) B6274259
theorem B14300059 : Blo 1857630 14300059 := bstep (se 1 (by rfl) ⟨10725044, by rfl⟩ : syracuseStep 14300059 = 21450089) B21450089
theorem B86996605 : Blo 1857630 86996605 := bstep (se 3 (by rfl) ⟨16311863, by rfl⟩ : syracuseStep 86996605 = 32623727) B32623727
theorem B7247593 : Blo 1857630 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B35714803 : Blo 1857630 35714803 := bstep (se 1 (by rfl) ⟨26786102, by rfl⟩ : syracuseStep 35714803 = 53572205) B53572205
theorem B1858015 : Blo 1857630 1858015 := bstep (se 1 (by rfl) ⟨1393511, by rfl⟩ : syracuseStep 1858015 = 2787023) B2787023
theorem B1858431 : Blo 1857630 1858431 := bstep (se 1 (by rfl) ⟨1393823, by rfl⟩ : syracuseStep 1858431 = 2787647) B2787647
theorem B1858495 : Blo 1857630 1858495 := bstep (se 1 (by rfl) ⟨1393871, by rfl⟩ : syracuseStep 1858495 = 2787743) B2787743
theorem B1858559 : Blo 1857630 1858559 := bstep (se 1 (by rfl) ⟨1393919, by rfl⟩ : syracuseStep 1858559 = 2787839) B2787839
theorem B1858815 : Blo 1857630 1858815 := bstep (se 1 (by rfl) ⟨1394111, by rfl⟩ : syracuseStep 1858815 = 2788223) B2788223
theorem B148872473 : Blo 1857630 148872473 := bstep (se 2 (by rfl) ⟨55827177, by rfl⟩ : syracuseStep 148872473 = 111654355) B111654355
theorem B50879771 : Blo 1857630 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B1858975 : Blo 1857630 1858975 := bstep (se 1 (by rfl) ⟨1394231, by rfl⟩ : syracuseStep 1858975 = 2788463) B2788463
theorem B1859231 : Blo 1857630 1859231 := bstep (se 1 (by rfl) ⟨1394423, by rfl⟩ : syracuseStep 1859231 = 2788847) B2788847
theorem B1859263 : Blo 1857630 1859263 := bstep (se 1 (by rfl) ⟨1394447, by rfl⟩ : syracuseStep 1859263 = 2788895) B2788895
theorem B1859327 : Blo 1857630 1859327 := bstep (se 1 (by rfl) ⟨1394495, by rfl⟩ : syracuseStep 1859327 = 2788991) B2788991
theorem B3137663 : Blo 1857630 3137663 := bstep (se 1 (by rfl) ⟨2353247, by rfl⟩ : syracuseStep 3137663 = 4706495) B4706495
theorem B8929703 : Blo 1857630 8929703 := bstep (se 1 (by rfl) ⟨6697277, by rfl⟩ : syracuseStep 8929703 = 13394555) B13394555
theorem B96535547 : Blo 1857630 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B5367521 : Blo 1857630 5367521 := bstep (se 2 (by rfl) ⟨2012820, by rfl⟩ : syracuseStep 5367521 = 4025641) B4025641
theorem B2787455 : Blo 1857630 2787455 := bstep (se 1 (by rfl) ⟨2090591, by rfl⟩ : syracuseStep 2787455 = 4181183) B4181183
theorem B2787497 : Blo 1857630 2787497 := bstep (se 2 (by rfl) ⟨1045311, by rfl⟩ : syracuseStep 2787497 = 2090623) B2090623
theorem B2787791 : Blo 1857630 2787791 := bstep (se 1 (by rfl) ⟨2090843, by rfl⟩ : syracuseStep 2787791 = 4181687) B4181687
theorem B5294591 : Blo 1857630 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B2787995 : Blo 1857630 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B2788031 : Blo 1857630 2788031 := bstep (se 1 (by rfl) ⟨2091023, by rfl⟩ : syracuseStep 2788031 = 4182047) B4182047
theorem B2788199 : Blo 1857630 2788199 := bstep (se 1 (by rfl) ⟨2091149, by rfl⟩ : syracuseStep 2788199 = 4182299) B4182299
theorem B1587973045 : Blo 1857630 1587973045 := bstep (se 5 (by rfl) ⟨74436236, by rfl⟩ : syracuseStep 1587973045 = 148872473) B148872473
theorem B10587131 : Blo 1857630 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B2788559 : Blo 1857630 2788559 := bstep (se 1 (by rfl) ⟨2091419, by rfl⟩ : syracuseStep 2788559 = 4182839) B4182839
theorem B6696701 : Blo 1857630 6696701 := bstep (se 3 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 6696701 = 2511263) B2511263
theorem B19066745 : Blo 1857630 19066745 := bstep (se 2 (by rfl) ⟨7150029, by rfl⟩ : syracuseStep 19066745 = 14300059) B14300059
theorem B115995473 : Blo 1857630 115995473 := bstep (se 2 (by rfl) ⟨43498302, by rfl⟩ : syracuseStep 115995473 = 86996605) B86996605
theorem B33919847 : Blo 1857630 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B9663457 : Blo 1857630 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B68785249 : Blo 1857630 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B1858215 : Blo 1857630 1858215 := bstep (se 1 (by rfl) ⟨1393661, by rfl⟩ : syracuseStep 1858215 = 2787323) B2787323
theorem B1858287 : Blo 1857630 1858287 := bstep (se 1 (by rfl) ⟨1393715, by rfl⟩ : syracuseStep 1858287 = 2787431) B2787431
theorem B3529811 : Blo 1857630 3529811 := bstep (se 1 (by rfl) ⟨2647358, by rfl⟩ : syracuseStep 3529811 = 5294717) B5294717
theorem B35708039 : Blo 1857630 35708039 := bstep (se 1 (by rfl) ⟨26781029, by rfl⟩ : syracuseStep 35708039 = 53562059) B53562059
theorem B1859099 : Blo 1857630 1859099 := bstep (se 1 (by rfl) ⟨1394324, by rfl⟩ : syracuseStep 1859099 = 2788649) B2788649
theorem B1859199 : Blo 1857630 1859199 := bstep (se 1 (by rfl) ⟨1394399, by rfl⟩ : syracuseStep 1859199 = 2788799) B2788799
theorem B47619737 : Blo 1857630 47619737 := bstep (se 2 (by rfl) ⟨17857401, by rfl⟩ : syracuseStep 47619737 = 35714803) B35714803
theorem B35733257 : Blo 1857630 35733257 := bstep (se 2 (by rfl) ⟨13399971, by rfl⟩ : syracuseStep 35733257 = 26799943) B26799943
theorem B5291801 : Blo 1857630 5291801 := bstep (se 2 (by rfl) ⟨1984425, by rfl⟩ : syracuseStep 5291801 = 3968851) B3968851
theorem B1859583 : Blo 1857630 1859583 := bstep (se 1 (by rfl) ⟨1394687, by rfl⟩ : syracuseStep 1859583 = 2789375) B2789375
theorem B64357031 : Blo 1857630 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B2117297393 : Blo 1857630 2117297393 := bstep (se 2 (by rfl) ⟨793986522, by rfl⟩ : syracuseStep 2117297393 = 1587973045) B1587973045
theorem B2353207 : Blo 1857630 2353207 := bstep (se 1 (by rfl) ⟨1764905, by rfl⟩ : syracuseStep 2353207 = 3529811) B3529811
theorem B31746491 : Blo 1857630 31746491 := bstep (se 1 (by rfl) ⟨23809868, by rfl⟩ : syracuseStep 31746491 = 47619737) B47619737
theorem B2091775 : Blo 1857630 2091775 := bstep (se 1 (by rfl) ⟨1568831, by rfl⟩ : syracuseStep 2091775 = 3137663) B3137663
theorem B22613231 : Blo 1857630 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B91713665 : Blo 1857630 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B7058087 : Blo 1857630 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B3527867 : Blo 1857630 3527867 := bstep (se 1 (by rfl) ⟨2645900, by rfl⟩ : syracuseStep 3527867 = 5291801) B5291801
theorem B12711163 : Blo 1857630 12711163 := bstep (se 1 (by rfl) ⟨9533372, by rfl⟩ : syracuseStep 12711163 = 19066745) B19066745
theorem B5953135 : Blo 1857630 5953135 := bstep (se 1 (by rfl) ⟨4464851, by rfl⟩ : syracuseStep 5953135 = 8929703) B8929703
theorem B77330315 : Blo 1857630 77330315 := bstep (se 1 (by rfl) ⟨57997736, by rfl⟩ : syracuseStep 77330315 = 115995473) B115995473
theorem B3578347 : Blo 1857630 3578347 := bstep (se 1 (by rfl) ⟨2683760, by rfl⟩ : syracuseStep 3578347 = 5367521) B5367521
theorem B12884609 : Blo 1857630 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B1858303 : Blo 1857630 1858303 := bstep (se 1 (by rfl) ⟨1393727, by rfl⟩ : syracuseStep 1858303 = 2787455) B2787455
theorem B1858331 : Blo 1857630 1858331 := bstep (se 1 (by rfl) ⟨1393748, by rfl⟩ : syracuseStep 1858331 = 2787497) B2787497
theorem B1858527 : Blo 1857630 1858527 := bstep (se 1 (by rfl) ⟨1393895, by rfl⟩ : syracuseStep 1858527 = 2787791) B2787791
theorem B3529727 : Blo 1857630 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B1858663 : Blo 1857630 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B1858687 : Blo 1857630 1858687 := bstep (se 1 (by rfl) ⟨1394015, by rfl⟩ : syracuseStep 1858687 = 2788031) B2788031
theorem B1858799 : Blo 1857630 1858799 := bstep (se 1 (by rfl) ⟨1394099, by rfl⟩ : syracuseStep 1858799 = 2788199) B2788199
theorem B23805359 : Blo 1857630 23805359 := bstep (se 1 (by rfl) ⟨17854019, by rfl⟩ : syracuseStep 23805359 = 35708039) B35708039
theorem B1859039 : Blo 1857630 1859039 := bstep (se 1 (by rfl) ⟨1394279, by rfl⟩ : syracuseStep 1859039 = 2788559) B2788559
theorem B4464467 : Blo 1857630 4464467 := bstep (se 1 (by rfl) ⟨3348350, by rfl⟩ : syracuseStep 4464467 = 6696701) B6696701
theorem B23822171 : Blo 1857630 23822171 := bstep (se 1 (by rfl) ⟨17866628, by rfl⟩ : syracuseStep 23822171 = 35733257) B35733257
theorem B3137609 : Blo 1857630 3137609 := bstep (se 2 (by rfl) ⟨1176603, by rfl⟩ : syracuseStep 3137609 = 2353207) B2353207
theorem B2351911 : Blo 1857630 2351911 := bstep (se 1 (by rfl) ⟨1763933, by rfl⟩ : syracuseStep 2351911 = 3527867) B3527867
theorem B1411531595 : Blo 1857630 1411531595 := bstep (se 1 (by rfl) ⟨1058648696, by rfl⟩ : syracuseStep 1411531595 = 2117297393) B2117297393
theorem B51553543 : Blo 1857630 51553543 := bstep (se 1 (by rfl) ⟨38665157, by rfl⟩ : syracuseStep 51553543 = 77330315) B77330315
theorem B34358957 : Blo 1857630 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B2353151 : Blo 1857630 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B15075487 : Blo 1857630 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B15870239 : Blo 1857630 15870239 := bstep (se 1 (by rfl) ⟨11902679, by rfl⟩ : syracuseStep 15870239 = 23805359) B23805359
theorem B2976311 : Blo 1857630 2976311 := bstep (se 1 (by rfl) ⟨2232233, by rfl⟩ : syracuseStep 2976311 = 4464467) B4464467
theorem B42904687 : Blo 1857630 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B4705391 : Blo 1857630 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B4771129 : Blo 1857630 4771129 := bstep (se 2 (by rfl) ⟨1789173, by rfl⟩ : syracuseStep 4771129 = 3578347) B3578347
theorem B2789033 : Blo 1857630 2789033 := bstep (se 2 (by rfl) ⟨1045887, by rfl⟩ : syracuseStep 2789033 = 2091775) B2091775
theorem B21164327 : Blo 1857630 21164327 := bstep (se 1 (by rfl) ⟨15873245, by rfl⟩ : syracuseStep 21164327 = 31746491) B31746491
theorem B15881447 : Blo 1857630 15881447 := bstep (se 1 (by rfl) ⟨11911085, by rfl⟩ : syracuseStep 15881447 = 23822171) B23822171
theorem B244569773 : Blo 1857630 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B16948217 : Blo 1857630 16948217 := bstep (se 2 (by rfl) ⟨6355581, by rfl⟩ : syracuseStep 16948217 = 12711163) B12711163
theorem B7937513 : Blo 1857630 7937513 := bstep (se 2 (by rfl) ⟨2976567, by rfl⟩ : syracuseStep 7937513 = 5953135) B5953135
theorem B22905971 : Blo 1857630 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B163046515 : Blo 1857630 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B57206249 : Blo 1857630 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B2091739 : Blo 1857630 2091739 := bstep (se 1 (by rfl) ⟨1568804, by rfl⟩ : syracuseStep 2091739 = 3137609) B3137609
theorem B14109551 : Blo 1857630 14109551 := bstep (se 1 (by rfl) ⟨10582163, by rfl⟩ : syracuseStep 14109551 = 21164327) B21164327
theorem B10587631 : Blo 1857630 10587631 := bstep (se 1 (by rfl) ⟨7940723, by rfl⟩ : syracuseStep 10587631 = 15881447) B15881447
theorem B10580159 : Blo 1857630 10580159 := bstep (se 1 (by rfl) ⟨7935119, by rfl⟩ : syracuseStep 10580159 = 15870239) B15870239
theorem B6361505 : Blo 1857630 6361505 := bstep (se 2 (by rfl) ⟨2385564, by rfl⟩ : syracuseStep 6361505 = 4771129) B4771129
theorem B20100649 : Blo 1857630 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B941021063 : Blo 1857630 941021063 := bstep (se 1 (by rfl) ⟨705765797, by rfl⟩ : syracuseStep 941021063 = 1411531595) B1411531595
theorem B3135881 : Blo 1857630 3135881 := bstep (se 2 (by rfl) ⟨1175955, by rfl⟩ : syracuseStep 3135881 = 2351911) B2351911
theorem B7936829 : Blo 1857630 7936829 := bstep (se 3 (by rfl) ⟨1488155, by rfl⟩ : syracuseStep 7936829 = 2976311) B2976311
theorem B68738057 : Blo 1857630 68738057 := bstep (se 2 (by rfl) ⟨25776771, by rfl⟩ : syracuseStep 68738057 = 51553543) B51553543
theorem B3136927 : Blo 1857630 3136927 := bstep (se 1 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 3136927 = 4705391) B4705391
theorem B6275069 : Blo 1857630 6275069 := bstep (se 3 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 6275069 = 2353151) B2353151
theorem B5291675 : Blo 1857630 5291675 := bstep (se 1 (by rfl) ⟨3968756, by rfl⟩ : syracuseStep 5291675 = 7937513) B7937513
theorem B1859355 : Blo 1857630 1859355 := bstep (se 1 (by rfl) ⟨1394516, by rfl⟩ : syracuseStep 1859355 = 2789033) B2789033
theorem B45195245 : Blo 1857630 45195245 := bstep (se 3 (by rfl) ⟨8474108, by rfl⟩ : syracuseStep 45195245 = 16948217) B16948217
theorem B7053439 : Blo 1857630 7053439 := bstep (se 1 (by rfl) ⟨5290079, by rfl⟩ : syracuseStep 7053439 = 10580159) B10580159
theorem B15270647 : Blo 1857630 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B2090587 : Blo 1857630 2090587 := bstep (se 1 (by rfl) ⟨1567940, by rfl⟩ : syracuseStep 2090587 = 3135881) B3135881
theorem B9406367 : Blo 1857630 9406367 := bstep (se 1 (by rfl) ⟨7054775, by rfl⟩ : syracuseStep 9406367 = 14109551) B14109551
theorem B14116841 : Blo 1857630 14116841 := bstep (se 2 (by rfl) ⟨5293815, by rfl⟩ : syracuseStep 14116841 = 10587631) B10587631
theorem B2788985 : Blo 1857630 2788985 := bstep (se 2 (by rfl) ⟨1045869, by rfl⟩ : syracuseStep 2788985 = 2091739) B2091739
theorem B38137499 : Blo 1857630 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B627347375 : Blo 1857630 627347375 := bstep (se 1 (by rfl) ⟨470510531, by rfl⟩ : syracuseStep 627347375 = 941021063) B941021063
theorem B217395353 : Blo 1857630 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B4182569 : Blo 1857630 4182569 := bstep (se 2 (by rfl) ⟨1568463, by rfl⟩ : syracuseStep 4182569 = 3136927) B3136927
theorem B26800865 : Blo 1857630 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B3527783 : Blo 1857630 3527783 := bstep (se 1 (by rfl) ⟨2645837, by rfl⟩ : syracuseStep 3527783 = 5291675) B5291675
theorem B4183379 : Blo 1857630 4183379 := bstep (se 1 (by rfl) ⟨3137534, by rfl⟩ : syracuseStep 4183379 = 6275069) B6275069
theorem B4241003 : Blo 1857630 4241003 := bstep (se 1 (by rfl) ⟨3180752, by rfl⟩ : syracuseStep 4241003 = 6361505) B6361505
theorem B5291219 : Blo 1857630 5291219 := bstep (se 1 (by rfl) ⟨3968414, by rfl⟩ : syracuseStep 5291219 = 7936829) B7936829
theorem B45825371 : Blo 1857630 45825371 := bstep (se 1 (by rfl) ⟨34369028, by rfl⟩ : syracuseStep 45825371 = 68738057) B68738057
theorem B30130163 : Blo 1857630 30130163 := bstep (se 1 (by rfl) ⟨22597622, by rfl⟩ : syracuseStep 30130163 = 45195245) B45195245
theorem B9404585 : Blo 1857630 9404585 := bstep (se 2 (by rfl) ⟨3526719, by rfl⟩ : syracuseStep 9404585 = 7053439) B7053439
theorem B17867243 : Blo 1857630 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B2351855 : Blo 1857630 2351855 := bstep (se 1 (by rfl) ⟨1763891, by rfl⟩ : syracuseStep 2351855 = 3527783) B3527783
theorem B45237365 : Blo 1857630 45237365 := bstep (se 5 (by rfl) ⟨2120501, by rfl⟩ : syracuseStep 45237365 = 4241003) B4241003
theorem B2787449 : Blo 1857630 2787449 := bstep (se 2 (by rfl) ⟨1045293, by rfl⟩ : syracuseStep 2787449 = 2090587) B2090587
theorem B30550247 : Blo 1857630 30550247 := bstep (se 1 (by rfl) ⟨22912685, by rfl⟩ : syracuseStep 30550247 = 45825371) B45825371
theorem B2788379 : Blo 1857630 2788379 := bstep (se 1 (by rfl) ⟨2091284, by rfl⟩ : syracuseStep 2788379 = 4182569) B4182569
theorem B2788919 : Blo 1857630 2788919 := bstep (se 1 (by rfl) ⟨2091689, by rfl⟩ : syracuseStep 2788919 = 4183379) B4183379
theorem B6270911 : Blo 1857630 6270911 := bstep (se 1 (by rfl) ⟨4703183, by rfl⟩ : syracuseStep 6270911 = 9406367) B9406367
theorem B3527479 : Blo 1857630 3527479 := bstep (se 1 (by rfl) ⟨2645609, by rfl⟩ : syracuseStep 3527479 = 5291219) B5291219
theorem B25424999 : Blo 1857630 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B418231583 : Blo 1857630 418231583 := bstep (se 1 (by rfl) ⟨313673687, by rfl⟩ : syracuseStep 418231583 = 627347375) B627347375
theorem B144930235 : Blo 1857630 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B9411227 : Blo 1857630 9411227 := bstep (se 1 (by rfl) ⟨7058420, by rfl⟩ : syracuseStep 9411227 = 14116841) B14116841
theorem B40721725 : Blo 1857630 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B1859323 : Blo 1857630 1859323 := bstep (se 1 (by rfl) ⟨1394492, by rfl⟩ : syracuseStep 1859323 = 2788985) B2788985
theorem B20086775 : Blo 1857630 20086775 := bstep (se 1 (by rfl) ⟨15065081, by rfl⟩ : syracuseStep 20086775 = 30130163) B30130163
theorem B16949999 : Blo 1857630 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B4703305 : Blo 1857630 4703305 := bstep (se 2 (by rfl) ⟨1763739, by rfl⟩ : syracuseStep 4703305 = 3527479) B3527479
theorem B47645981 : Blo 1857630 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B20366831 : Blo 1857630 20366831 := bstep (se 1 (by rfl) ⟨15275123, by rfl⟩ : syracuseStep 20366831 = 30550247) B30550247
theorem B4180607 : Blo 1857630 4180607 := bstep (se 1 (by rfl) ⟨3135455, by rfl⟩ : syracuseStep 4180607 = 6270911) B6270911
theorem B6269723 : Blo 1857630 6269723 := bstep (se 1 (by rfl) ⟨4702292, by rfl⟩ : syracuseStep 6269723 = 9404585) B9404585
theorem B30158243 : Blo 1857630 30158243 := bstep (se 1 (by rfl) ⟨22618682, by rfl⟩ : syracuseStep 30158243 = 45237365) B45237365
theorem B6271613 : Blo 1857630 6271613 := bstep (se 3 (by rfl) ⟨1175927, by rfl⟩ : syracuseStep 6271613 = 2351855) B2351855
theorem B13391183 : Blo 1857630 13391183 := bstep (se 1 (by rfl) ⟨10043387, by rfl⟩ : syracuseStep 13391183 = 20086775) B20086775
theorem B278821055 : Blo 1857630 278821055 := bstep (se 1 (by rfl) ⟨209115791, by rfl⟩ : syracuseStep 278821055 = 418231583) B418231583
theorem B1858299 : Blo 1857630 1858299 := bstep (se 1 (by rfl) ⟨1393724, by rfl⟩ : syracuseStep 1858299 = 2787449) B2787449
theorem B54295633 : Blo 1857630 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B6274151 : Blo 1857630 6274151 := bstep (se 1 (by rfl) ⟨4705613, by rfl⟩ : syracuseStep 6274151 = 9411227) B9411227
theorem B193240313 : Blo 1857630 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B1858919 : Blo 1857630 1858919 := bstep (se 1 (by rfl) ⟨1394189, by rfl⟩ : syracuseStep 1858919 = 2788379) B2788379
theorem B1859279 : Blo 1857630 1859279 := bstep (se 1 (by rfl) ⟨1394459, by rfl⟩ : syracuseStep 1859279 = 2788919) B2788919
theorem B72394177 : Blo 1857630 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B2787071 : Blo 1857630 2787071 := bstep (se 1 (by rfl) ⟨2090303, by rfl⟩ : syracuseStep 2787071 = 4180607) B4180607
theorem B4179815 : Blo 1857630 4179815 := bstep (se 1 (by rfl) ⟨3134861, by rfl⟩ : syracuseStep 4179815 = 6269723) B6269723
theorem B20105495 : Blo 1857630 20105495 := bstep (se 1 (by rfl) ⟨15079121, by rfl⟩ : syracuseStep 20105495 = 30158243) B30158243
theorem B4181075 : Blo 1857630 4181075 := bstep (se 1 (by rfl) ⟨3135806, by rfl⟩ : syracuseStep 4181075 = 6271613) B6271613
theorem B11299999 : Blo 1857630 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B31763987 : Blo 1857630 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B13577887 : Blo 1857630 13577887 := bstep (se 1 (by rfl) ⟨10183415, by rfl⟩ : syracuseStep 13577887 = 20366831) B20366831
theorem B6271073 : Blo 1857630 6271073 := bstep (se 2 (by rfl) ⟨2351652, by rfl⟩ : syracuseStep 6271073 = 4703305) B4703305
theorem B185880703 : Blo 1857630 185880703 := bstep (se 1 (by rfl) ⟨139410527, by rfl⟩ : syracuseStep 185880703 = 278821055) B278821055
theorem B4182767 : Blo 1857630 4182767 := bstep (se 1 (by rfl) ⟨3137075, by rfl⟩ : syracuseStep 4182767 = 6274151) B6274151
theorem B8927455 : Blo 1857630 8927455 := bstep (se 1 (by rfl) ⟨6695591, by rfl⟩ : syracuseStep 8927455 = 13391183) B13391183
theorem B128826875 : Blo 1857630 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B247840937 : Blo 1857630 247840937 := bstep (se 2 (by rfl) ⟨92940351, by rfl⟩ : syracuseStep 247840937 = 185880703) B185880703
theorem B11903273 : Blo 1857630 11903273 := bstep (se 2 (by rfl) ⟨4463727, by rfl⟩ : syracuseStep 11903273 = 8927455) B8927455
theorem B2786543 : Blo 1857630 2786543 := bstep (se 1 (by rfl) ⟨2089907, by rfl⟩ : syracuseStep 2786543 = 4179815) B4179815
theorem B13403663 : Blo 1857630 13403663 := bstep (se 1 (by rfl) ⟨10052747, by rfl⟩ : syracuseStep 13403663 = 20105495) B20105495
theorem B15066665 : Blo 1857630 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B2787383 : Blo 1857630 2787383 := bstep (se 1 (by rfl) ⟨2090537, by rfl⟩ : syracuseStep 2787383 = 4181075) B4181075
theorem B4180715 : Blo 1857630 4180715 := bstep (se 1 (by rfl) ⟨3135536, by rfl⟩ : syracuseStep 4180715 = 6271073) B6271073
theorem B2788511 : Blo 1857630 2788511 := bstep (se 1 (by rfl) ⟨2091383, by rfl⟩ : syracuseStep 2788511 = 4182767) B4182767
theorem B72415397 : Blo 1857630 72415397 := bstep (se 4 (by rfl) ⟨6788943, by rfl⟩ : syracuseStep 72415397 = 13577887) B13577887
theorem B1858047 : Blo 1857630 1858047 := bstep (se 1 (by rfl) ⟨1393535, by rfl⟩ : syracuseStep 1858047 = 2787071) B2787071
theorem B96525569 : Blo 1857630 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B85884583 : Blo 1857630 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B21175991 : Blo 1857630 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B10044443 : Blo 1857630 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B48276931 : Blo 1857630 48276931 := bstep (se 1 (by rfl) ⟨36207698, by rfl⟩ : syracuseStep 48276931 = 72415397) B72415397
theorem B2787143 : Blo 1857630 2787143 := bstep (se 1 (by rfl) ⟨2090357, by rfl⟩ : syracuseStep 2787143 = 4180715) B4180715
theorem B64350379 : Blo 1857630 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B14117327 : Blo 1857630 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B165227291 : Blo 1857630 165227291 := bstep (se 1 (by rfl) ⟨123920468, by rfl⟩ : syracuseStep 165227291 = 247840937) B247840937
theorem B114512777 : Blo 1857630 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B7935515 : Blo 1857630 7935515 := bstep (se 1 (by rfl) ⟨5951636, by rfl⟩ : syracuseStep 7935515 = 11903273) B11903273
theorem B1857695 : Blo 1857630 1857695 := bstep (se 1 (by rfl) ⟨1393271, by rfl⟩ : syracuseStep 1857695 = 2786543) B2786543
theorem B8935775 : Blo 1857630 8935775 := bstep (se 1 (by rfl) ⟨6701831, by rfl⟩ : syracuseStep 8935775 = 13403663) B13403663
theorem B1858255 : Blo 1857630 1858255 := bstep (se 1 (by rfl) ⟨1393691, by rfl⟩ : syracuseStep 1858255 = 2787383) B2787383
theorem B1859007 : Blo 1857630 1859007 := bstep (se 1 (by rfl) ⟨1394255, by rfl⟩ : syracuseStep 1859007 = 2788511) B2788511
theorem B76341851 : Blo 1857630 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B5957183 : Blo 1857630 5957183 := bstep (se 1 (by rfl) ⟨4467887, by rfl⟩ : syracuseStep 5957183 = 8935775) B8935775
theorem B110151527 : Blo 1857630 110151527 := bstep (se 1 (by rfl) ⟨82613645, by rfl⟩ : syracuseStep 110151527 = 165227291) B165227291
theorem B64369241 : Blo 1857630 64369241 := bstep (se 2 (by rfl) ⟨24138465, by rfl⟩ : syracuseStep 64369241 = 48276931) B48276931
theorem B26785181 : Blo 1857630 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B85800505 : Blo 1857630 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B5290343 : Blo 1857630 5290343 := bstep (se 1 (by rfl) ⟨3967757, by rfl⟩ : syracuseStep 5290343 = 7935515) B7935515
theorem B1858095 : Blo 1857630 1858095 := bstep (se 1 (by rfl) ⟨1393571, by rfl⟩ : syracuseStep 1858095 = 2787143) B2787143
theorem B9411551 : Blo 1857630 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B15885821 : Blo 1857630 15885821 := bstep (se 3 (by rfl) ⟨2978591, by rfl⟩ : syracuseStep 15885821 = 5957183) B5957183
theorem B42912827 : Blo 1857630 42912827 := bstep (se 1 (by rfl) ⟨32184620, by rfl⟩ : syracuseStep 42912827 = 64369241) B64369241
theorem B1174949621 : Blo 1857630 1174949621 := bstep (se 5 (by rfl) ⟨55075763, by rfl⟩ : syracuseStep 1174949621 = 110151527) B110151527
theorem B3526895 : Blo 1857630 3526895 := bstep (se 1 (by rfl) ⟨2645171, by rfl⟩ : syracuseStep 3526895 = 5290343) B5290343
theorem B50894567 : Blo 1857630 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B17856787 : Blo 1857630 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B6274367 : Blo 1857630 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B114400673 : Blo 1857630 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B2351263 : Blo 1857630 2351263 := bstep (se 1 (by rfl) ⟨1763447, by rfl⟩ : syracuseStep 2351263 = 3526895) B3526895
theorem B28608551 : Blo 1857630 28608551 := bstep (se 1 (by rfl) ⟨21456413, by rfl⟩ : syracuseStep 28608551 = 42912827) B42912827
theorem B23809049 : Blo 1857630 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B4182911 : Blo 1857630 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B783299747 : Blo 1857630 783299747 := bstep (se 1 (by rfl) ⟨587474810, by rfl⟩ : syracuseStep 783299747 = 1174949621) B1174949621
theorem B10590547 : Blo 1857630 10590547 := bstep (se 1 (by rfl) ⟨7942910, by rfl⟩ : syracuseStep 10590547 = 15885821) B15885821
theorem B33929711 : Blo 1857630 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B76267115 : Blo 1857630 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B522199831 : Blo 1857630 522199831 := bstep (se 1 (by rfl) ⟨391649873, by rfl⟩ : syracuseStep 522199831 = 783299747) B783299747
theorem B19072367 : Blo 1857630 19072367 := bstep (se 1 (by rfl) ⟨14304275, by rfl⟩ : syracuseStep 19072367 = 28608551) B28608551
theorem B22619807 : Blo 1857630 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B2788607 : Blo 1857630 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B15872699 : Blo 1857630 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B50844743 : Blo 1857630 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B3135017 : Blo 1857630 3135017 := bstep (se 2 (by rfl) ⟨1175631, by rfl⟩ : syracuseStep 3135017 = 2351263) B2351263
theorem B14120729 : Blo 1857630 14120729 := bstep (se 2 (by rfl) ⟨5295273, by rfl⟩ : syracuseStep 14120729 = 10590547) B10590547
theorem B12714911 : Blo 1857630 12714911 := bstep (se 1 (by rfl) ⟨9536183, by rfl⟩ : syracuseStep 12714911 = 19072367) B19072367
theorem B2090011 : Blo 1857630 2090011 := bstep (se 1 (by rfl) ⟨1567508, by rfl⟩ : syracuseStep 2090011 = 3135017) B3135017
theorem B9413819 : Blo 1857630 9413819 := bstep (se 1 (by rfl) ⟨7060364, by rfl⟩ : syracuseStep 9413819 = 14120729) B14120729
theorem B696266441 : Blo 1857630 696266441 := bstep (se 2 (by rfl) ⟨261099915, by rfl⟩ : syracuseStep 696266441 = 522199831) B522199831
theorem B10581799 : Blo 1857630 10581799 := bstep (se 1 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 10581799 = 15872699) B15872699
theorem B33896495 : Blo 1857630 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B15079871 : Blo 1857630 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B1859071 : Blo 1857630 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B6275879 : Blo 1857630 6275879 := bstep (se 1 (by rfl) ⟨4706909, by rfl⟩ : syracuseStep 6275879 = 9413819) B9413819
theorem B2786681 : Blo 1857630 2786681 := bstep (se 2 (by rfl) ⟨1045005, by rfl⟩ : syracuseStep 2786681 = 2090011) B2090011
theorem B10053247 : Blo 1857630 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B14109065 : Blo 1857630 14109065 := bstep (se 2 (by rfl) ⟨5290899, by rfl⟩ : syracuseStep 14109065 = 10581799) B10581799
theorem B464177627 : Blo 1857630 464177627 := bstep (se 1 (by rfl) ⟨348133220, by rfl⟩ : syracuseStep 464177627 = 696266441) B696266441
theorem B22597663 : Blo 1857630 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B8476607 : Blo 1857630 8476607 := bstep (se 1 (by rfl) ⟨6357455, by rfl⟩ : syracuseStep 8476607 = 12714911) B12714911
theorem B30130217 : Blo 1857630 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B9406043 : Blo 1857630 9406043 := bstep (se 1 (by rfl) ⟨7054532, by rfl⟩ : syracuseStep 9406043 = 14109065) B14109065
theorem B13404329 : Blo 1857630 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B22604285 : Blo 1857630 22604285 := bstep (se 3 (by rfl) ⟨4238303, by rfl⟩ : syracuseStep 22604285 = 8476607) B8476607
theorem B4183919 : Blo 1857630 4183919 := bstep (se 1 (by rfl) ⟨3137939, by rfl⟩ : syracuseStep 4183919 = 6275879) B6275879
theorem B1857787 : Blo 1857630 1857787 := bstep (se 1 (by rfl) ⟨1393340, by rfl⟩ : syracuseStep 1857787 = 2786681) B2786681
theorem B309451751 : Blo 1857630 309451751 := bstep (se 1 (by rfl) ⟨232088813, by rfl⟩ : syracuseStep 309451751 = 464177627) B464177627
theorem B20086811 : Blo 1857630 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B206301167 : Blo 1857630 206301167 := bstep (se 1 (by rfl) ⟨154725875, by rfl⟩ : syracuseStep 206301167 = 309451751) B309451751
theorem B6270695 : Blo 1857630 6270695 := bstep (se 1 (by rfl) ⟨4703021, by rfl⟩ : syracuseStep 6270695 = 9406043) B9406043
theorem B2789279 : Blo 1857630 2789279 := bstep (se 1 (by rfl) ⟨2091959, by rfl⟩ : syracuseStep 2789279 = 4183919) B4183919
theorem B15069523 : Blo 1857630 15069523 := bstep (se 1 (by rfl) ⟨11302142, by rfl⟩ : syracuseStep 15069523 = 22604285) B22604285
theorem B8936219 : Blo 1857630 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B5957479 : Blo 1857630 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B4180463 : Blo 1857630 4180463 := bstep (se 1 (by rfl) ⟨3135347, by rfl⟩ : syracuseStep 4180463 = 6270695) B6270695
theorem B13391207 : Blo 1857630 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B20092697 : Blo 1857630 20092697 := bstep (se 2 (by rfl) ⟨7534761, by rfl⟩ : syracuseStep 20092697 = 15069523) B15069523
theorem B137534111 : Blo 1857630 137534111 := bstep (se 1 (by rfl) ⟨103150583, by rfl⟩ : syracuseStep 137534111 = 206301167) B206301167
theorem B1859519 : Blo 1857630 1859519 := bstep (se 1 (by rfl) ⟨1394639, by rfl⟩ : syracuseStep 1859519 = 2789279) B2789279
theorem B13395131 : Blo 1857630 13395131 := bstep (se 1 (by rfl) ⟨10046348, by rfl⟩ : syracuseStep 13395131 = 20092697) B20092697
theorem B2786975 : Blo 1857630 2786975 := bstep (se 1 (by rfl) ⟨2090231, by rfl⟩ : syracuseStep 2786975 = 4180463) B4180463
theorem B91689407 : Blo 1857630 91689407 := bstep (se 1 (by rfl) ⟨68767055, by rfl⟩ : syracuseStep 91689407 = 137534111) B137534111
theorem B7943305 : Blo 1857630 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B8927471 : Blo 1857630 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B8930087 : Blo 1857630 8930087 := bstep (se 1 (by rfl) ⟨6697565, by rfl⟩ : syracuseStep 8930087 = 13395131) B13395131
theorem B5951647 : Blo 1857630 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B61126271 : Blo 1857630 61126271 := bstep (se 1 (by rfl) ⟨45844703, by rfl⟩ : syracuseStep 61126271 = 91689407) B91689407
theorem B1857983 : Blo 1857630 1857983 := bstep (se 1 (by rfl) ⟨1393487, by rfl⟩ : syracuseStep 1857983 = 2786975) B2786975
theorem B10591073 : Blo 1857630 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B40750847 : Blo 1857630 40750847 := bstep (se 1 (by rfl) ⟨30563135, by rfl⟩ : syracuseStep 40750847 = 61126271) B61126271
theorem B5953391 : Blo 1857630 5953391 := bstep (se 1 (by rfl) ⟨4465043, by rfl⟩ : syracuseStep 5953391 = 8930087) B8930087
theorem B31742117 : Blo 1857630 31742117 := bstep (se 4 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 31742117 = 5951647) B5951647
theorem B7060715 : Blo 1857630 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B21161411 : Blo 1857630 21161411 := bstep (se 1 (by rfl) ⟨15871058, by rfl⟩ : syracuseStep 21161411 = 31742117) B31742117
theorem B27167231 : Blo 1857630 27167231 := bstep (se 1 (by rfl) ⟨20375423, by rfl⟩ : syracuseStep 27167231 = 40750847) B40750847
theorem B3968927 : Blo 1857630 3968927 := bstep (se 1 (by rfl) ⟨2976695, by rfl⟩ : syracuseStep 3968927 = 5953391) B5953391
theorem B4707143 : Blo 1857630 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B3138095 : Blo 1857630 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B14107607 : Blo 1857630 14107607 := bstep (se 1 (by rfl) ⟨10580705, by rfl⟩ : syracuseStep 14107607 = 21161411) B21161411
theorem B18111487 : Blo 1857630 18111487 := bstep (se 1 (by rfl) ⟨13583615, by rfl⟩ : syracuseStep 18111487 = 27167231) B27167231
theorem B2645951 : Blo 1857630 2645951 := bstep (se 1 (by rfl) ⟨1984463, by rfl⟩ : syracuseStep 2645951 = 3968927) B3968927
theorem B9405071 : Blo 1857630 9405071 := bstep (se 1 (by rfl) ⟨7053803, by rfl⟩ : syracuseStep 9405071 = 14107607) B14107607
theorem B7055869 : Blo 1857630 7055869 := bstep (se 3 (by rfl) ⟨1322975, by rfl⟩ : syracuseStep 7055869 = 2645951) B2645951
theorem B2092063 : Blo 1857630 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B24148649 : Blo 1857630 24148649 := bstep (se 2 (by rfl) ⟨9055743, by rfl⟩ : syracuseStep 24148649 = 18111487) B18111487
theorem B6270047 : Blo 1857630 6270047 := bstep (se 1 (by rfl) ⟨4702535, by rfl⟩ : syracuseStep 6270047 = 9405071) B9405071
theorem B9407825 : Blo 1857630 9407825 := bstep (se 2 (by rfl) ⟨3527934, by rfl⟩ : syracuseStep 9407825 = 7055869) B7055869
theorem B2789417 : Blo 1857630 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B64396397 : Blo 1857630 64396397 := bstep (se 3 (by rfl) ⟨12074324, by rfl⟩ : syracuseStep 64396397 = 24148649) B24148649
theorem B1859611 : Blo 1857630 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B4180031 : Blo 1857630 4180031 := bstep (se 1 (by rfl) ⟨3135023, by rfl⟩ : syracuseStep 4180031 = 6270047) B6270047
theorem B42930931 : Blo 1857630 42930931 := bstep (se 1 (by rfl) ⟨32198198, by rfl⟩ : syracuseStep 42930931 = 64396397) B64396397
theorem B6271883 : Blo 1857630 6271883 := bstep (se 1 (by rfl) ⟨4703912, by rfl⟩ : syracuseStep 6271883 = 9407825) B9407825
theorem B2786687 : Blo 1857630 2786687 := bstep (se 1 (by rfl) ⟨2090015, by rfl⟩ : syracuseStep 2786687 = 4180031) B4180031
theorem B4181255 : Blo 1857630 4181255 := bstep (se 1 (by rfl) ⟨3135941, by rfl⟩ : syracuseStep 4181255 = 6271883) B6271883
theorem B57241241 : Blo 1857630 57241241 := bstep (se 2 (by rfl) ⟨21465465, by rfl⟩ : syracuseStep 57241241 = 42930931) B42930931
theorem B2787503 : Blo 1857630 2787503 := bstep (se 1 (by rfl) ⟨2090627, by rfl⟩ : syracuseStep 2787503 = 4181255) B4181255
theorem B38160827 : Blo 1857630 38160827 := bstep (se 1 (by rfl) ⟨28620620, by rfl⟩ : syracuseStep 38160827 = 57241241) B57241241
theorem B1857791 : Blo 1857630 1857791 := bstep (se 1 (by rfl) ⟨1393343, by rfl⟩ : syracuseStep 1857791 = 2786687) B2786687
theorem B25440551 : Blo 1857630 25440551 := bstep (se 1 (by rfl) ⟨19080413, by rfl⟩ : syracuseStep 25440551 = 38160827) B38160827
theorem B1858335 : Blo 1857630 1858335 := bstep (se 1 (by rfl) ⟨1393751, by rfl⟩ : syracuseStep 1858335 = 2787503) B2787503
theorem B16960367 : Blo 1857630 16960367 := bstep (se 1 (by rfl) ⟨12720275, by rfl⟩ : syracuseStep 16960367 = 25440551) B25440551
theorem B11306911 : Blo 1857630 11306911 := bstep (se 1 (by rfl) ⟨8480183, by rfl⟩ : syracuseStep 11306911 = 16960367) B16960367
theorem B15075881 : Blo 1857630 15075881 := bstep (se 2 (by rfl) ⟨5653455, by rfl⟩ : syracuseStep 15075881 = 11306911) B11306911
theorem B10050587 : Blo 1857630 10050587 := bstep (se 1 (by rfl) ⟨7537940, by rfl⟩ : syracuseStep 10050587 = 15075881) B15075881
theorem B6700391 : Blo 1857630 6700391 := bstep (se 1 (by rfl) ⟨5025293, by rfl⟩ : syracuseStep 6700391 = 10050587) B10050587
theorem B4466927 : Blo 1857630 4466927 := bstep (se 1 (by rfl) ⟨3350195, by rfl⟩ : syracuseStep 4466927 = 6700391) B6700391
theorem B11911805 : Blo 1857630 11911805 := bstep (se 3 (by rfl) ⟨2233463, by rfl⟩ : syracuseStep 11911805 = 4466927) B4466927
theorem B7941203 : Blo 1857630 7941203 := bstep (se 1 (by rfl) ⟨5955902, by rfl⟩ : syracuseStep 7941203 = 11911805) B11911805
theorem B5294135 : Blo 1857630 5294135 := bstep (se 1 (by rfl) ⟨3970601, by rfl⟩ : syracuseStep 5294135 = 7941203) B7941203
theorem B3529423 : Blo 1857630 3529423 := bstep (se 1 (by rfl) ⟨2647067, by rfl⟩ : syracuseStep 3529423 = 5294135) B5294135
theorem B4705897 : Blo 1857630 4705897 := bstep (se 2 (by rfl) ⟨1764711, by rfl⟩ : syracuseStep 4705897 = 3529423) B3529423
theorem B6274529 : Blo 1857630 6274529 := bstep (se 2 (by rfl) ⟨2352948, by rfl⟩ : syracuseStep 6274529 = 4705897) B4705897
theorem B4183019 : Blo 1857630 4183019 := bstep (se 1 (by rfl) ⟨3137264, by rfl⟩ : syracuseStep 4183019 = 6274529) B6274529
theorem B2788679 : Blo 1857630 2788679 := bstep (se 1 (by rfl) ⟨2091509, by rfl⟩ : syracuseStep 2788679 = 4183019) B4183019
theorem B1859119 : Blo 1857630 1859119 := bstep (se 1 (by rfl) ⟨1394339, by rfl⟩ : syracuseStep 1859119 = 2788679) B2788679

theorem C0 (j : ℕ) (h1 : 464407 ≤ j) (h2 : j ≤ 464906) : Blo 1857630 (4 * j + 3) := by
  interval_cases j
  · exact B1857631
  · exact B1857635
  · exact B1857639
  · exact B1857643
  · exact B1857647
  · exact B1857651
  · exact B1857655
  · exact B1857659
  · exact B1857663
  · exact B1857667
  · exact B1857671
  · exact B1857675
  · exact B1857679
  · exact B1857683
  · exact B1857687
  · exact B1857691
  · exact B1857695
  · exact B1857699
  · exact B1857703
  · exact B1857707
  · exact B1857711
  · exact B1857715
  · exact B1857719
  · exact B1857723
  · exact B1857727
  · exact B1857731
  · exact B1857735
  · exact B1857739
  · exact B1857743
  · exact B1857747
  · exact B1857751
  · exact B1857755
  · exact B1857759
  · exact B1857763
  · exact B1857767
  · exact B1857771
  · exact B1857775
  · exact B1857779
  · exact B1857783
  · exact B1857787
  · exact B1857791
  · exact B1857795
  · exact B1857799
  · exact B1857803
  · exact B1857807
  · exact B1857811
  · exact B1857815
  · exact B1857819
  · exact B1857823
  · exact B1857827
  · exact B1857831
  · exact B1857835
  · exact B1857839
  · exact B1857843
  · exact B1857847
  · exact B1857851
  · exact B1857855
  · exact B1857859
  · exact B1857863
  · exact B1857867
  · exact B1857871
  · exact B1857875
  · exact B1857879
  · exact B1857883
  · exact B1857887
  · exact B1857891
  · exact B1857895
  · exact B1857899
  · exact B1857903
  · exact B1857907
  · exact B1857911
  · exact B1857915
  · exact B1857919
  · exact B1857923
  · exact B1857927
  · exact B1857931
  · exact B1857935
  · exact B1857939
  · exact B1857943
  · exact B1857947
  · exact B1857951
  · exact B1857955
  · exact B1857959
  · exact B1857963
  · exact B1857967
  · exact B1857971
  · exact B1857975
  · exact B1857979
  · exact B1857983
  · exact B1857987
  · exact B1857991
  · exact B1857995
  · exact B1857999
  · exact B1858003
  · exact B1858007
  · exact B1858011
  · exact B1858015
  · exact B1858019
  · exact B1858023
  · exact B1858027
  · exact B1858031
  · exact B1858035
  · exact B1858039
  · exact B1858043
  · exact B1858047
  · exact B1858051
  · exact B1858055
  · exact B1858059
  · exact B1858063
  · exact B1858067
  · exact B1858071
  · exact B1858075
  · exact B1858079
  · exact B1858083
  · exact B1858087
  · exact B1858091
  · exact B1858095
  · exact B1858099
  · exact B1858103
  · exact B1858107
  · exact B1858111
  · exact B1858115
  · exact B1858119
  · exact B1858123
  · exact B1858127
  · exact B1858131
  · exact B1858135
  · exact B1858139
  · exact B1858143
  · exact B1858147
  · exact B1858151
  · exact B1858155
  · exact B1858159
  · exact B1858163
  · exact B1858167
  · exact B1858171
  · exact B1858175
  · exact B1858179
  · exact B1858183
  · exact B1858187
  · exact B1858191
  · exact B1858195
  · exact B1858199
  · exact B1858203
  · exact B1858207
  · exact B1858211
  · exact B1858215
  · exact B1858219
  · exact B1858223
  · exact B1858227
  · exact B1858231
  · exact B1858235
  · exact B1858239
  · exact B1858243
  · exact B1858247
  · exact B1858251
  · exact B1858255
  · exact B1858259
  · exact B1858263
  · exact B1858267
  · exact B1858271
  · exact B1858275
  · exact B1858279
  · exact B1858283
  · exact B1858287
  · exact B1858291
  · exact B1858295
  · exact B1858299
  · exact B1858303
  · exact B1858307
  · exact B1858311
  · exact B1858315
  · exact B1858319
  · exact B1858323
  · exact B1858327
  · exact B1858331
  · exact B1858335
  · exact B1858339
  · exact B1858343
  · exact B1858347
  · exact B1858351
  · exact B1858355
  · exact B1858359
  · exact B1858363
  · exact B1858367
  · exact B1858371
  · exact B1858375
  · exact B1858379
  · exact B1858383
  · exact B1858387
  · exact B1858391
  · exact B1858395
  · exact B1858399
  · exact B1858403
  · exact B1858407
  · exact B1858411
  · exact B1858415
  · exact B1858419
  · exact B1858423
  · exact B1858427
  · exact B1858431
  · exact B1858435
  · exact B1858439
  · exact B1858443
  · exact B1858447
  · exact B1858451
  · exact B1858455
  · exact B1858459
  · exact B1858463
  · exact B1858467
  · exact B1858471
  · exact B1858475
  · exact B1858479
  · exact B1858483
  · exact B1858487
  · exact B1858491
  · exact B1858495
  · exact B1858499
  · exact B1858503
  · exact B1858507
  · exact B1858511
  · exact B1858515
  · exact B1858519
  · exact B1858523
  · exact B1858527
  · exact B1858531
  · exact B1858535
  · exact B1858539
  · exact B1858543
  · exact B1858547
  · exact B1858551
  · exact B1858555
  · exact B1858559
  · exact B1858563
  · exact B1858567
  · exact B1858571
  · exact B1858575
  · exact B1858579
  · exact B1858583
  · exact B1858587
  · exact B1858591
  · exact B1858595
  · exact B1858599
  · exact B1858603
  · exact B1858607
  · exact B1858611
  · exact B1858615
  · exact B1858619
  · exact B1858623
  · exact B1858627
  · exact B1858631
  · exact B1858635
  · exact B1858639
  · exact B1858643
  · exact B1858647
  · exact B1858651
  · exact B1858655
  · exact B1858659
  · exact B1858663
  · exact B1858667
  · exact B1858671
  · exact B1858675
  · exact B1858679
  · exact B1858683
  · exact B1858687
  · exact B1858691
  · exact B1858695
  · exact B1858699
  · exact B1858703
  · exact B1858707
  · exact B1858711
  · exact B1858715
  · exact B1858719
  · exact B1858723
  · exact B1858727
  · exact B1858731
  · exact B1858735
  · exact B1858739
  · exact B1858743
  · exact B1858747
  · exact B1858751
  · exact B1858755
  · exact B1858759
  · exact B1858763
  · exact B1858767
  · exact B1858771
  · exact B1858775
  · exact B1858779
  · exact B1858783
  · exact B1858787
  · exact B1858791
  · exact B1858795
  · exact B1858799
  · exact B1858803
  · exact B1858807
  · exact B1858811
  · exact B1858815
  · exact B1858819
  · exact B1858823
  · exact B1858827
  · exact B1858831
  · exact B1858835
  · exact B1858839
  · exact B1858843
  · exact B1858847
  · exact B1858851
  · exact B1858855
  · exact B1858859
  · exact B1858863
  · exact B1858867
  · exact B1858871
  · exact B1858875
  · exact B1858879
  · exact B1858883
  · exact B1858887
  · exact B1858891
  · exact B1858895
  · exact B1858899
  · exact B1858903
  · exact B1858907
  · exact B1858911
  · exact B1858915
  · exact B1858919
  · exact B1858923
  · exact B1858927
  · exact B1858931
  · exact B1858935
  · exact B1858939
  · exact B1858943
  · exact B1858947
  · exact B1858951
  · exact B1858955
  · exact B1858959
  · exact B1858963
  · exact B1858967
  · exact B1858971
  · exact B1858975
  · exact B1858979
  · exact B1858983
  · exact B1858987
  · exact B1858991
  · exact B1858995
  · exact B1858999
  · exact B1859003
  · exact B1859007
  · exact B1859011
  · exact B1859015
  · exact B1859019
  · exact B1859023
  · exact B1859027
  · exact B1859031
  · exact B1859035
  · exact B1859039
  · exact B1859043
  · exact B1859047
  · exact B1859051
  · exact B1859055
  · exact B1859059
  · exact B1859063
  · exact B1859067
  · exact B1859071
  · exact B1859075
  · exact B1859079
  · exact B1859083
  · exact B1859087
  · exact B1859091
  · exact B1859095
  · exact B1859099
  · exact B1859103
  · exact B1859107
  · exact B1859111
  · exact B1859115
  · exact B1859119
  · exact B1859123
  · exact B1859127
  · exact B1859131
  · exact B1859135
  · exact B1859139
  · exact B1859143
  · exact B1859147
  · exact B1859151
  · exact B1859155
  · exact B1859159
  · exact B1859163
  · exact B1859167
  · exact B1859171
  · exact B1859175
  · exact B1859179
  · exact B1859183
  · exact B1859187
  · exact B1859191
  · exact B1859195
  · exact B1859199
  · exact B1859203
  · exact B1859207
  · exact B1859211
  · exact B1859215
  · exact B1859219
  · exact B1859223
  · exact B1859227
  · exact B1859231
  · exact B1859235
  · exact B1859239
  · exact B1859243
  · exact B1859247
  · exact B1859251
  · exact B1859255
  · exact B1859259
  · exact B1859263
  · exact B1859267
  · exact B1859271
  · exact B1859275
  · exact B1859279
  · exact B1859283
  · exact B1859287
  · exact B1859291
  · exact B1859295
  · exact B1859299
  · exact B1859303
  · exact B1859307
  · exact B1859311
  · exact B1859315
  · exact B1859319
  · exact B1859323
  · exact B1859327
  · exact B1859331
  · exact B1859335
  · exact B1859339
  · exact B1859343
  · exact B1859347
  · exact B1859351
  · exact B1859355
  · exact B1859359
  · exact B1859363
  · exact B1859367
  · exact B1859371
  · exact B1859375
  · exact B1859379
  · exact B1859383
  · exact B1859387
  · exact B1859391
  · exact B1859395
  · exact B1859399
  · exact B1859403
  · exact B1859407
  · exact B1859411
  · exact B1859415
  · exact B1859419
  · exact B1859423
  · exact B1859427
  · exact B1859431
  · exact B1859435
  · exact B1859439
  · exact B1859443
  · exact B1859447
  · exact B1859451
  · exact B1859455
  · exact B1859459
  · exact B1859463
  · exact B1859467
  · exact B1859471
  · exact B1859475
  · exact B1859479
  · exact B1859483
  · exact B1859487
  · exact B1859491
  · exact B1859495
  · exact B1859499
  · exact B1859503
  · exact B1859507
  · exact B1859511
  · exact B1859515
  · exact B1859519
  · exact B1859523
  · exact B1859527
  · exact B1859531
  · exact B1859535
  · exact B1859539
  · exact B1859543
  · exact B1859547
  · exact B1859551
  · exact B1859555
  · exact B1859559
  · exact B1859563
  · exact B1859567
  · exact B1859571
  · exact B1859575
  · exact B1859579
  · exact B1859583
  · exact B1859587
  · exact B1859591
  · exact B1859595
  · exact B1859599
  · exact B1859603
  · exact B1859607
  · exact B1859611
  · exact B1859615
  · exact B1859619
  · exact B1859623
  · exact B1859627

theorem solution (m : ℕ) (hlo : 1857630 ≤ m) (hhi : m ≤ 1859630) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 464407 ≤ j := by omega
    have hj2 : j ≤ 464906 := by omega
    have hb : Blo 1857630 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
