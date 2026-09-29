-- Prove2me | solution 1 for syracuse_descends_range_1393516_1395516
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:40.090255+00:00
-- url     : https://prove2.me/submissions/e3910aae-f87f-4be1-9e88-273fbd7575f6

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


theorem B7946261 : Blo 1393516 7946261 := bbase (se 6 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 7946261 = 372481) (by norm_num)
theorem B3973141 : Blo 1393516 3973141 := bbase (se 6 (by rfl) ⟨93120, by rfl⟩ : syracuseStep 3973141 = 186241) (by norm_num)
theorem B3137597 : Blo 1393516 3137597 := bbase (se 3 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 3137597 = 1176599) (by norm_num)
theorem B3530861 : Blo 1393516 3530861 := bbase (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) (by norm_num)
theorem B3137669 : Blo 1393516 3137669 := bbase (se 4 (by rfl) ⟨294156, by rfl⟩ : syracuseStep 3137669 = 588313) (by norm_num)
theorem B5652661 : Blo 1393516 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B3137741 : Blo 1393516 3137741 := bbase (se 3 (by rfl) ⟨588326, by rfl⟩ : syracuseStep 3137741 = 1176653) (by norm_num)
theorem B3137813 : Blo 1393516 3137813 := bbase (se 6 (by rfl) ⟨73542, by rfl⟩ : syracuseStep 3137813 = 147085) (by norm_num)
theorem B3350821 : Blo 1393516 3350821 := bbase (se 4 (by rfl) ⟨314139, by rfl⟩ : syracuseStep 3350821 = 628279) (by norm_num)
theorem B3531053 : Blo 1393516 3531053 := bbase (se 3 (by rfl) ⟨662072, by rfl⟩ : syracuseStep 3531053 = 1324145) (by norm_num)
theorem B3137885 : Blo 1393516 3137885 := bbase (se 3 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 3137885 = 1176707) (by norm_num)
theorem B6037877 : Blo 1393516 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B3178885 : Blo 1393516 3178885 := bbase (se 4 (by rfl) ⟨298020, by rfl⟩ : syracuseStep 3178885 = 596041) (by norm_num)
theorem B3137957 : Blo 1393516 3137957 := bbase (se 4 (by rfl) ⟨294183, by rfl⟩ : syracuseStep 3137957 = 588367) (by norm_num)
theorem B2646445 : Blo 1393516 2646445 := bbase (se 3 (by rfl) ⟨496208, by rfl⟩ : syracuseStep 2646445 = 992417) (by norm_num)
theorem B5956021 : Blo 1393516 5956021 := bbase (se 5 (by rfl) ⟨279188, by rfl⟩ : syracuseStep 5956021 = 558377) (by norm_num)
theorem B3138029 : Blo 1393516 3138029 := bbase (se 3 (by rfl) ⟨588380, by rfl⟩ : syracuseStep 3138029 = 1176761) (by norm_num)
theorem B2351605 : Blo 1393516 2351605 := bbase (se 5 (by rfl) ⟨110231, by rfl⟩ : syracuseStep 2351605 = 220463) (by norm_num)
theorem B13591061 : Blo 1393516 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B3138101 : Blo 1393516 3138101 := bbase (se 5 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 3138101 = 294197) (by norm_num)
theorem B2646589 : Blo 1393516 2646589 := bbase (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) (by norm_num)
theorem B2351693 : Blo 1393516 2351693 := bbase (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) (by norm_num)
theorem B5292661 : Blo 1393516 5292661 := bbase (se 5 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 5292661 = 496187) (by norm_num)
theorem B3138173 : Blo 1393516 3138173 := bbase (se 3 (by rfl) ⟨588407, by rfl⟩ : syracuseStep 3138173 = 1176815) (by norm_num)
theorem B3531397 : Blo 1393516 3531397 := bbase (se 4 (by rfl) ⟨331068, by rfl⟩ : syracuseStep 3531397 = 662137) (by norm_num)
theorem B8938133 : Blo 1393516 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B3138245 : Blo 1393516 3138245 := bbase (se 4 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 3138245 = 588421) (by norm_num)
theorem B2351821 : Blo 1393516 2351821 := bbase (se 3 (by rfl) ⟨440966, by rfl⟩ : syracuseStep 2351821 = 881933) (by norm_num)
theorem B2646749 : Blo 1393516 2646749 := bbase (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) (by norm_num)
theorem B3531509 : Blo 1393516 3531509 := bbase (se 5 (by rfl) ⟨165539, by rfl⟩ : syracuseStep 3531509 = 331079) (by norm_num)
theorem B3138317 : Blo 1393516 3138317 := bbase (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) (by norm_num)
theorem B2351909 : Blo 1393516 2351909 := bbase (se 4 (by rfl) ⟨220491, by rfl⟩ : syracuseStep 2351909 = 440983) (by norm_num)
theorem B1590085 : Blo 1393516 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B3138389 : Blo 1393516 3138389 := bbase (se 9 (by rfl) ⟨9194, by rfl⟩ : syracuseStep 3138389 = 18389) (by norm_num)
theorem B2646893 : Blo 1393516 2646893 := bbase (se 3 (by rfl) ⟨496292, by rfl⟩ : syracuseStep 2646893 = 992585) (by norm_num)
theorem B7062389 : Blo 1393516 7062389 := bbase (se 5 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 7062389 = 662099) (by norm_num)
theorem B3138461 : Blo 1393516 3138461 := bbase (se 3 (by rfl) ⟨588461, by rfl⟩ : syracuseStep 3138461 = 1176923) (by norm_num)
theorem B2352037 : Blo 1393516 2352037 := bbase (se 4 (by rfl) ⟨220503, by rfl⟩ : syracuseStep 2352037 = 441007) (by norm_num)
theorem B5292965 : Blo 1393516 5292965 := bbase (se 4 (by rfl) ⟨496215, by rfl⟩ : syracuseStep 5292965 = 992431) (by norm_num)
theorem B7283621 : Blo 1393516 7283621 := bbase (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) (by norm_num)
theorem B3531701 : Blo 1393516 3531701 := bbase (se 5 (by rfl) ⟨165548, by rfl⟩ : syracuseStep 3531701 = 331097) (by norm_num)
theorem B3138533 : Blo 1393516 3138533 := bbase (se 4 (by rfl) ⟨294237, by rfl⟩ : syracuseStep 3138533 = 588475) (by norm_num)
theorem B2352125 : Blo 1393516 2352125 := bbase (se 3 (by rfl) ⟨441023, by rfl⟩ : syracuseStep 2352125 = 882047) (by norm_num)
theorem B4703237 : Blo 1393516 4703237 := bbase (se 4 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 4703237 = 881857) (by norm_num)
theorem B3138605 : Blo 1393516 3138605 := bbase (se 3 (by rfl) ⟨588488, by rfl⟩ : syracuseStep 3138605 = 1176977) (by norm_num)
theorem B3138677 : Blo 1393516 3138677 := bbase (se 5 (by rfl) ⟨147125, by rfl⟩ : syracuseStep 3138677 = 294251) (by norm_num)
theorem B2352253 : Blo 1393516 2352253 := bbase (se 3 (by rfl) ⟨441047, by rfl⟩ : syracuseStep 2352253 = 882095) (by norm_num)
theorem B2647181 : Blo 1393516 2647181 := bbase (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) (by norm_num)
theorem B4465813 : Blo 1393516 4465813 := bbase (se 6 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 4465813 = 209335) (by norm_num)
theorem B3138749 : Blo 1393516 3138749 := bbase (se 3 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 3138749 = 1177031) (by norm_num)
theorem B2352341 : Blo 1393516 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B12723445 : Blo 1393516 12723445 := bbase (se 5 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 12723445 = 1192823) (by norm_num)
theorem B3138821 : Blo 1393516 3138821 := bbase (se 4 (by rfl) ⟨294264, by rfl⟩ : syracuseStep 3138821 = 588529) (by norm_num)
theorem B2417933 : Blo 1393516 2417933 := bbase (se 3 (by rfl) ⟨453362, by rfl⟩ : syracuseStep 2417933 = 906725) (by norm_num)
theorem B3532045 : Blo 1393516 3532045 := bbase (se 3 (by rfl) ⟨662258, by rfl⟩ : syracuseStep 3532045 = 1324517) (by norm_num)
theorem B2647333 : Blo 1393516 2647333 := bbase (se 4 (by rfl) ⟨248187, by rfl⟩ : syracuseStep 2647333 = 496375) (by norm_num)
theorem B2090285 : Blo 1393516 2090285 := bbase (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) (by norm_num)
theorem B2090309 : Blo 1393516 2090309 := bbase (se 4 (by rfl) ⟨195966, by rfl⟩ : syracuseStep 2090309 = 391933) (by norm_num)
theorem B3138893 : Blo 1393516 3138893 := bbase (se 3 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 3138893 = 1177085) (by norm_num)
theorem B2352469 : Blo 1393516 2352469 := bbase (se 12 (by rfl) ⟨861, by rfl⟩ : syracuseStep 2352469 = 1723) (by norm_num)
theorem B2090333 : Blo 1393516 2090333 := bbase (se 3 (by rfl) ⟨391937, by rfl⟩ : syracuseStep 2090333 = 783875) (by norm_num)
theorem B2090357 : Blo 1393516 2090357 := bbase (se 5 (by rfl) ⟨97985, by rfl⟩ : syracuseStep 2090357 = 195971) (by norm_num)
theorem B3532157 : Blo 1393516 3532157 := bbase (se 3 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 3532157 = 1324559) (by norm_num)
theorem B2090381 : Blo 1393516 2090381 := bbase (se 3 (by rfl) ⟨391946, by rfl⟩ : syracuseStep 2090381 = 783893) (by norm_num)
theorem B3138965 : Blo 1393516 3138965 := bbase (se 6 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 3138965 = 147139) (by norm_num)
theorem B2090405 : Blo 1393516 2090405 := bbase (se 4 (by rfl) ⟨195975, by rfl⟩ : syracuseStep 2090405 = 391951) (by norm_num)
theorem B2352557 : Blo 1393516 2352557 := bbase (se 3 (by rfl) ⟨441104, by rfl⟩ : syracuseStep 2352557 = 882209) (by norm_num)
theorem B4703669 : Blo 1393516 4703669 := bbase (se 5 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 4703669 = 440969) (by norm_num)
theorem B2090429 : Blo 1393516 2090429 := bbase (se 3 (by rfl) ⟨391955, by rfl⟩ : syracuseStep 2090429 = 783911) (by norm_num)
theorem B2090453 : Blo 1393516 2090453 := bbase (se 7 (by rfl) ⟨24497, by rfl⟩ : syracuseStep 2090453 = 48995) (by norm_num)
theorem B3139037 : Blo 1393516 3139037 := bbase (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) (by norm_num)
theorem B2090477 : Blo 1393516 2090477 := bbase (se 3 (by rfl) ⟨391964, by rfl⟩ : syracuseStep 2090477 = 783929) (by norm_num)
theorem B2090501 : Blo 1393516 2090501 := bbase (se 4 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 2090501 = 391969) (by norm_num)
theorem B3180053 : Blo 1393516 3180053 := bbase (se 6 (by rfl) ⟨74532, by rfl⟩ : syracuseStep 3180053 = 149065) (by norm_num)
theorem B2090525 : Blo 1393516 2090525 := bbase (se 3 (by rfl) ⟨391973, by rfl⟩ : syracuseStep 2090525 = 783947) (by norm_num)
theorem B3139109 : Blo 1393516 3139109 := bbase (se 4 (by rfl) ⟨294291, by rfl⟩ : syracuseStep 3139109 = 588583) (by norm_num)
theorem B2352685 : Blo 1393516 2352685 := bbase (se 3 (by rfl) ⟨441128, by rfl⟩ : syracuseStep 2352685 = 882257) (by norm_num)
theorem B2090549 : Blo 1393516 2090549 := bbase (se 5 (by rfl) ⟨97994, by rfl⟩ : syracuseStep 2090549 = 195989) (by norm_num)
theorem B3532349 : Blo 1393516 3532349 := bbase (se 3 (by rfl) ⟨662315, by rfl⟩ : syracuseStep 3532349 = 1324631) (by norm_num)
theorem B2090573 : Blo 1393516 2090573 := bbase (se 3 (by rfl) ⟨391982, by rfl⟩ : syracuseStep 2090573 = 783965) (by norm_num)
theorem B2647637 : Blo 1393516 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B6702677 : Blo 1393516 6702677 := bbase (se 8 (by rfl) ⟨39273, by rfl⟩ : syracuseStep 6702677 = 78547) (by norm_num)
theorem B2090597 : Blo 1393516 2090597 := bbase (se 4 (by rfl) ⟨195993, by rfl⟩ : syracuseStep 2090597 = 391987) (by norm_num)
theorem B4769381 : Blo 1393516 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B3139181 : Blo 1393516 3139181 := bbase (se 3 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 3139181 = 1177193) (by norm_num)
theorem B6039157 : Blo 1393516 6039157 := bbase (se 5 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 6039157 = 566171) (by norm_num)
theorem B2090621 : Blo 1393516 2090621 := bbase (se 3 (by rfl) ⟨391991, by rfl⟩ : syracuseStep 2090621 = 783983) (by norm_num)
theorem B1984133 : Blo 1393516 1984133 := bbase (se 4 (by rfl) ⟨186012, by rfl⟩ : syracuseStep 1984133 = 372025) (by norm_num)
theorem B2352773 : Blo 1393516 2352773 := bbase (se 4 (by rfl) ⟨220572, by rfl⟩ : syracuseStep 2352773 = 441145) (by norm_num)
theorem B3352205 : Blo 1393516 3352205 := bbase (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) (by norm_num)
theorem B2090645 : Blo 1393516 2090645 := bbase (se 6 (by rfl) ⟨48999, by rfl⟩ : syracuseStep 2090645 = 97999) (by norm_num)
theorem B9537173 : Blo 1393516 9537173 := bbase (se 6 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 9537173 = 447055) (by norm_num)
theorem B2090669 : Blo 1393516 2090669 := bbase (se 3 (by rfl) ⟨392000, by rfl⟩ : syracuseStep 2090669 = 784001) (by norm_num)
theorem B3139253 : Blo 1393516 3139253 := bbase (se 5 (by rfl) ⟨147152, by rfl⟩ : syracuseStep 3139253 = 294305) (by norm_num)
theorem B2090693 : Blo 1393516 2090693 := bbase (se 4 (by rfl) ⟨196002, by rfl⟩ : syracuseStep 2090693 = 392005) (by norm_num)
theorem B1984213 : Blo 1393516 1984213 := bbase (se 7 (by rfl) ⟨23252, by rfl⟩ : syracuseStep 1984213 = 46505) (by norm_num)
theorem B20113109 : Blo 1393516 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B2090717 : Blo 1393516 2090717 := bbase (se 3 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 2090717 = 784019) (by norm_num)
theorem B2090741 : Blo 1393516 2090741 := bbase (se 5 (by rfl) ⟨98003, by rfl⟩ : syracuseStep 2090741 = 196007) (by norm_num)
theorem B3139325 : Blo 1393516 3139325 := bbase (se 3 (by rfl) ⟨588623, by rfl⟩ : syracuseStep 3139325 = 1177247) (by norm_num)
theorem B2352901 : Blo 1393516 2352901 := bbase (se 4 (by rfl) ⟨220584, by rfl⟩ : syracuseStep 2352901 = 441169) (by norm_num)
theorem B2090765 : Blo 1393516 2090765 := bbase (se 3 (by rfl) ⟨392018, by rfl⟩ : syracuseStep 2090765 = 784037) (by norm_num)
theorem B2090789 : Blo 1393516 2090789 := bbase (se 4 (by rfl) ⟨196011, by rfl⟩ : syracuseStep 2090789 = 392023) (by norm_num)
theorem B2090813 : Blo 1393516 2090813 := bbase (se 3 (by rfl) ⟨392027, by rfl⟩ : syracuseStep 2090813 = 784055) (by norm_num)
theorem B3139397 : Blo 1393516 3139397 := bbase (se 4 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 3139397 = 588637) (by norm_num)
theorem B1984333 : Blo 1393516 1984333 := bbase (se 3 (by rfl) ⟨372062, by rfl⟩ : syracuseStep 1984333 = 744125) (by norm_num)
theorem B2090837 : Blo 1393516 2090837 := bbase (se 9 (by rfl) ⟨6125, by rfl⟩ : syracuseStep 2090837 = 12251) (by norm_num)
theorem B2352989 : Blo 1393516 2352989 := bbase (se 3 (by rfl) ⟨441185, by rfl⟩ : syracuseStep 2352989 = 882371) (by norm_num)
theorem B4704101 : Blo 1393516 4704101 := bbase (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) (by norm_num)
theorem B2090861 : Blo 1393516 2090861 := bbase (se 3 (by rfl) ⟨392036, by rfl⟩ : syracuseStep 2090861 = 784073) (by norm_num)
theorem B2090885 : Blo 1393516 2090885 := bbase (se 4 (by rfl) ⟨196020, by rfl⟩ : syracuseStep 2090885 = 392041) (by norm_num)
theorem B5957509 : Blo 1393516 5957509 := bbase (se 4 (by rfl) ⟨558516, by rfl⟩ : syracuseStep 5957509 = 1117033) (by norm_num)
theorem B3139469 : Blo 1393516 3139469 := bbase (se 3 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 3139469 = 1177301) (by norm_num)
theorem B5957525 : Blo 1393516 5957525 := bbase (se 6 (by rfl) ⟨139629, by rfl⟩ : syracuseStep 5957525 = 279259) (by norm_num)
theorem B2090909 : Blo 1393516 2090909 := bbase (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) (by norm_num)
theorem B1984429 : Blo 1393516 1984429 := bbase (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) (by norm_num)
theorem B2090933 : Blo 1393516 2090933 := bbase (se 5 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 2090933 = 196025) (by norm_num)
theorem B10053557 : Blo 1393516 10053557 := bbase (se 5 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 10053557 = 942521) (by norm_num)
theorem B2090957 : Blo 1393516 2090957 := bbase (se 3 (by rfl) ⟨392054, by rfl⟩ : syracuseStep 2090957 = 784109) (by norm_num)
theorem B3139541 : Blo 1393516 3139541 := bbase (se 7 (by rfl) ⟨36791, by rfl⟩ : syracuseStep 3139541 = 73583) (by norm_num)
theorem B1697753 : Blo 1393516 1697753 := bbase (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) (by norm_num)
theorem B2353117 : Blo 1393516 2353117 := bbase (se 3 (by rfl) ⟨441209, by rfl⟩ : syracuseStep 2353117 = 882419) (by norm_num)
theorem B2090981 : Blo 1393516 2090981 := bbase (se 4 (by rfl) ⟨196029, by rfl⟩ : syracuseStep 2090981 = 392059) (by norm_num)
theorem B2091005 : Blo 1393516 2091005 := bbase (se 3 (by rfl) ⟨392063, by rfl⟩ : syracuseStep 2091005 = 784127) (by norm_num)
theorem B2091029 : Blo 1393516 2091029 := bbase (se 6 (by rfl) ⟨49008, by rfl⟩ : syracuseStep 2091029 = 98017) (by norm_num)
theorem B3139613 : Blo 1393516 3139613 := bbase (se 3 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 3139613 = 1177355) (by norm_num)
theorem B2091053 : Blo 1393516 2091053 := bbase (se 3 (by rfl) ⟨392072, by rfl⟩ : syracuseStep 2091053 = 784145) (by norm_num)
theorem B2066485 : Blo 1393516 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B2353205 : Blo 1393516 2353205 := bbase (se 5 (by rfl) ⟨110306, by rfl⟩ : syracuseStep 2353205 = 220613) (by norm_num)
theorem B2828341 : Blo 1393516 2828341 := bbase (se 5 (by rfl) ⟨132578, by rfl⟩ : syracuseStep 2828341 = 265157) (by norm_num)
theorem B3352637 : Blo 1393516 3352637 := bbase (se 3 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 3352637 = 1257239) (by norm_num)
theorem B2091077 : Blo 1393516 2091077 := bbase (se 4 (by rfl) ⟨196038, by rfl⟩ : syracuseStep 2091077 = 392077) (by norm_num)
theorem B2091101 : Blo 1393516 2091101 := bbase (se 3 (by rfl) ⟨392081, by rfl⟩ : syracuseStep 2091101 = 784163) (by norm_num)
theorem B3139685 : Blo 1393516 3139685 := bbase (se 4 (by rfl) ⟨294345, by rfl⟩ : syracuseStep 3139685 = 588691) (by norm_num)
theorem B2091125 : Blo 1393516 2091125 := bbase (se 5 (by rfl) ⟨98021, by rfl⟩ : syracuseStep 2091125 = 196043) (by norm_num)
theorem B7063685 : Blo 1393516 7063685 := bbase (se 4 (by rfl) ⟨662220, by rfl⟩ : syracuseStep 7063685 = 1324441) (by norm_num)
theorem B1788041 : Blo 1393516 1788041 := bbase (se 2 (by rfl) ⟨670515, by rfl⟩ : syracuseStep 1788041 = 1341031) (by norm_num)
theorem B2721925 : Blo 1393516 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B2091149 : Blo 1393516 2091149 := bbase (se 3 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 2091149 = 784181) (by norm_num)
theorem B2091173 : Blo 1393516 2091173 := bbase (se 4 (by rfl) ⟨196047, by rfl⟩ : syracuseStep 2091173 = 392095) (by norm_num)
theorem B3139757 : Blo 1393516 3139757 := bbase (se 3 (by rfl) ⟨588704, by rfl⟩ : syracuseStep 3139757 = 1177409) (by norm_num)
theorem B2353333 : Blo 1393516 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B2091197 : Blo 1393516 2091197 := bbase (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) (by norm_num)
theorem B2091221 : Blo 1393516 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B10053845 : Blo 1393516 10053845 := bbase (se 7 (by rfl) ⟨117818, by rfl⟩ : syracuseStep 10053845 = 235637) (by norm_num)
theorem B2091245 : Blo 1393516 2091245 := bbase (se 3 (by rfl) ⟨392108, by rfl⟩ : syracuseStep 2091245 = 784217) (by norm_num)
theorem B7637237 : Blo 1393516 7637237 := bbase (se 5 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 7637237 = 715991) (by norm_num)
theorem B3139829 : Blo 1393516 3139829 := bbase (se 5 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 3139829 = 294359) (by norm_num)
theorem B2091269 : Blo 1393516 2091269 := bbase (se 4 (by rfl) ⟨196056, by rfl⟩ : syracuseStep 2091269 = 392113) (by norm_num)
theorem B2353421 : Blo 1393516 2353421 := bbase (se 3 (by rfl) ⟨441266, by rfl⟩ : syracuseStep 2353421 = 882533) (by norm_num)
theorem B4704533 : Blo 1393516 4704533 := bbase (se 6 (by rfl) ⟨110262, by rfl⟩ : syracuseStep 4704533 = 220525) (by norm_num)
theorem B2091293 : Blo 1393516 2091293 := bbase (se 3 (by rfl) ⟨392117, by rfl⟩ : syracuseStep 2091293 = 784235) (by norm_num)
theorem B2091317 : Blo 1393516 2091317 := bbase (se 5 (by rfl) ⟨98030, by rfl⟩ : syracuseStep 2091317 = 196061) (by norm_num)
theorem B3139901 : Blo 1393516 3139901 := bbase (se 3 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 3139901 = 1177463) (by norm_num)
theorem B1788229 : Blo 1393516 1788229 := bbase (se 4 (by rfl) ⟨167646, by rfl⟩ : syracuseStep 1788229 = 335293) (by norm_num)
theorem B2648389 : Blo 1393516 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B2091341 : Blo 1393516 2091341 := bbase (se 3 (by rfl) ⟨392126, by rfl⟩ : syracuseStep 2091341 = 784253) (by norm_num)
theorem B2091365 : Blo 1393516 2091365 := bbase (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) (by norm_num)
theorem B1763689 : Blo 1393516 1763689 := bbase (se 2 (by rfl) ⟨661383, by rfl⟩ : syracuseStep 1763689 = 1322767) (by norm_num)
theorem B2091389 : Blo 1393516 2091389 := bbase (se 3 (by rfl) ⟨392135, by rfl⟩ : syracuseStep 2091389 = 784271) (by norm_num)
theorem B2353549 : Blo 1393516 2353549 := bbase (se 3 (by rfl) ⟨441290, by rfl⟩ : syracuseStep 2353549 = 882581) (by norm_num)
theorem B2091413 : Blo 1393516 2091413 := bbase (se 6 (by rfl) ⟨49017, by rfl⟩ : syracuseStep 2091413 = 98035) (by norm_num)
theorem B1984925 : Blo 1393516 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B2091437 : Blo 1393516 2091437 := bbase (se 3 (by rfl) ⟨392144, by rfl⟩ : syracuseStep 2091437 = 784289) (by norm_num)
theorem B2091461 : Blo 1393516 2091461 := bbase (se 4 (by rfl) ⟨196074, by rfl⟩ : syracuseStep 2091461 = 392149) (by norm_num)
theorem B1763785 : Blo 1393516 1763785 := bbase (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) (by norm_num)
theorem B2648533 : Blo 1393516 2648533 := bbase (se 7 (by rfl) ⟨31037, by rfl⟩ : syracuseStep 2648533 = 62075) (by norm_num)
theorem B2091485 : Blo 1393516 2091485 := bbase (se 3 (by rfl) ⟨392153, by rfl⟩ : syracuseStep 2091485 = 784307) (by norm_num)
theorem B2353637 : Blo 1393516 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B8931829 : Blo 1393516 8931829 := bbase (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) (by norm_num)
theorem B2091509 : Blo 1393516 2091509 := bbase (se 5 (by rfl) ⟨98039, by rfl⟩ : syracuseStep 2091509 = 196079) (by norm_num)
theorem B2091533 : Blo 1393516 2091533 := bbase (se 3 (by rfl) ⟨392162, by rfl⟩ : syracuseStep 2091533 = 784325) (by norm_num)
theorem B7055909 : Blo 1393516 7055909 := bbase (se 4 (by rfl) ⟨661491, by rfl⟩ : syracuseStep 7055909 = 1322983) (by norm_num)
theorem B2091557 : Blo 1393516 2091557 := bbase (se 4 (by rfl) ⟨196083, by rfl⟩ : syracuseStep 2091557 = 392167) (by norm_num)
theorem B1813045 : Blo 1393516 1813045 := bbase (se 5 (by rfl) ⟨84986, by rfl⟩ : syracuseStep 1813045 = 169973) (by norm_num)
theorem B2091581 : Blo 1393516 2091581 := bbase (se 3 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 2091581 = 784343) (by norm_num)
theorem B2091605 : Blo 1393516 2091605 := bbase (se 8 (by rfl) ⟨12255, by rfl⟩ : syracuseStep 2091605 = 24511) (by norm_num)
theorem B2148965 : Blo 1393516 2148965 := bbase (se 4 (by rfl) ⟨201465, by rfl⟩ : syracuseStep 2148965 = 402931) (by norm_num)
theorem B2353765 : Blo 1393516 2353765 := bbase (se 4 (by rfl) ⟨220665, by rfl⟩ : syracuseStep 2353765 = 441331) (by norm_num)
theorem B2091629 : Blo 1393516 2091629 := bbase (se 3 (by rfl) ⟨392180, by rfl⟩ : syracuseStep 2091629 = 784361) (by norm_num)
theorem B1763957 : Blo 1393516 1763957 := bbase (se 5 (by rfl) ⟨82685, by rfl⟩ : syracuseStep 1763957 = 165371) (by norm_num)
theorem B2648693 : Blo 1393516 2648693 := bbase (se 5 (by rfl) ⟨124157, by rfl⟩ : syracuseStep 2648693 = 248315) (by norm_num)
theorem B2091653 : Blo 1393516 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B2091677 : Blo 1393516 2091677 := bbase (se 3 (by rfl) ⟨392189, by rfl⟩ : syracuseStep 2091677 = 784379) (by norm_num)
theorem B1764013 : Blo 1393516 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B2091701 : Blo 1393516 2091701 := bbase (se 5 (by rfl) ⟨98048, by rfl⟩ : syracuseStep 2091701 = 196097) (by norm_num)
theorem B2353853 : Blo 1393516 2353853 := bbase (se 3 (by rfl) ⟨441347, by rfl⟩ : syracuseStep 2353853 = 882695) (by norm_num)
theorem B4704965 : Blo 1393516 4704965 := bbase (se 4 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 4704965 = 882181) (by norm_num)
theorem B2091725 : Blo 1393516 2091725 := bbase (se 3 (by rfl) ⟨392198, by rfl⟩ : syracuseStep 2091725 = 784397) (by norm_num)
theorem B2091749 : Blo 1393516 2091749 := bbase (se 4 (by rfl) ⟨196101, by rfl⟩ : syracuseStep 2091749 = 392203) (by norm_num)
theorem B2091773 : Blo 1393516 2091773 := bbase (se 3 (by rfl) ⟨392207, by rfl⟩ : syracuseStep 2091773 = 784415) (by norm_num)
theorem B2648837 : Blo 1393516 2648837 := bbase (se 4 (by rfl) ⟨248328, by rfl⟩ : syracuseStep 2648837 = 496657) (by norm_num)
theorem B1764109 : Blo 1393516 1764109 := bbase (se 3 (by rfl) ⟨330770, by rfl⟩ : syracuseStep 1764109 = 661541) (by norm_num)
theorem B2091797 : Blo 1393516 2091797 := bbase (se 6 (by rfl) ⟨49026, by rfl⟩ : syracuseStep 2091797 = 98053) (by norm_num)
theorem B2091821 : Blo 1393516 2091821 := bbase (se 3 (by rfl) ⟨392216, by rfl⟩ : syracuseStep 2091821 = 784433) (by norm_num)
theorem B2353981 : Blo 1393516 2353981 := bbase (se 3 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 2353981 = 882743) (by norm_num)
theorem B2091845 : Blo 1393516 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B13405013 : Blo 1393516 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B2091869 : Blo 1393516 2091869 := bbase (se 3 (by rfl) ⟨392225, by rfl⟩ : syracuseStep 2091869 = 784451) (by norm_num)
theorem B2091893 : Blo 1393516 2091893 := bbase (se 5 (by rfl) ⟨98057, by rfl⟩ : syracuseStep 2091893 = 196115) (by norm_num)
theorem B5368693 : Blo 1393516 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B5024645 : Blo 1393516 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B2091917 : Blo 1393516 2091917 := bbase (se 3 (by rfl) ⟨392234, by rfl⟩ : syracuseStep 2091917 = 784469) (by norm_num)
theorem B2354069 : Blo 1393516 2354069 := bbase (se 6 (by rfl) ⟨55173, by rfl⟩ : syracuseStep 2354069 = 110347) (by norm_num)
theorem B2091941 : Blo 1393516 2091941 := bbase (se 4 (by rfl) ⟨196119, by rfl⟩ : syracuseStep 2091941 = 392239) (by norm_num)
theorem B1764281 : Blo 1393516 1764281 := bbase (se 2 (by rfl) ⟨661605, by rfl⟩ : syracuseStep 1764281 = 1323211) (by norm_num)
theorem B2091965 : Blo 1393516 2091965 := bbase (se 3 (by rfl) ⟨392243, by rfl⟩ : syracuseStep 2091965 = 784487) (by norm_num)
theorem B1985477 : Blo 1393516 1985477 := bbase (se 4 (by rfl) ⟨186138, by rfl⟩ : syracuseStep 1985477 = 372277) (by norm_num)
theorem B2091989 : Blo 1393516 2091989 := bbase (se 7 (by rfl) ⟨24515, by rfl⟩ : syracuseStep 2091989 = 49031) (by norm_num)
theorem B10595285 : Blo 1393516 10595285 := bbase (se 7 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 10595285 = 248327) (by norm_num)
theorem B5295077 : Blo 1393516 5295077 := bbase (se 4 (by rfl) ⟨496413, by rfl⟩ : syracuseStep 5295077 = 992827) (by norm_num)
theorem B2092013 : Blo 1393516 2092013 := bbase (se 3 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 2092013 = 784505) (by norm_num)
theorem B1764337 : Blo 1393516 1764337 := bbase (se 2 (by rfl) ⟨661626, by rfl⟩ : syracuseStep 1764337 = 1323253) (by norm_num)
theorem B11914229 : Blo 1393516 11914229 := bbase (se 5 (by rfl) ⟨558479, by rfl⟩ : syracuseStep 11914229 = 1116959) (by norm_num)
theorem B1567741 : Blo 1393516 1567741 := bbase (se 3 (by rfl) ⟨293951, by rfl⟩ : syracuseStep 1567741 = 587903) (by norm_num)
theorem B2092037 : Blo 1393516 2092037 := bbase (se 4 (by rfl) ⟨196128, by rfl⟩ : syracuseStep 2092037 = 392257) (by norm_num)
theorem B2354197 : Blo 1393516 2354197 := bbase (se 6 (by rfl) ⟨55176, by rfl⟩ : syracuseStep 2354197 = 110353) (by norm_num)
theorem B2092061 : Blo 1393516 2092061 := bbase (se 3 (by rfl) ⟨392261, by rfl⟩ : syracuseStep 2092061 = 784523) (by norm_num)
theorem B1567777 : Blo 1393516 1567777 := bbase (se 2 (by rfl) ⟨587916, by rfl⟩ : syracuseStep 1567777 = 1175833) (by norm_num)
theorem B2649125 : Blo 1393516 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B2092085 : Blo 1393516 2092085 := bbase (se 5 (by rfl) ⟨98066, by rfl⟩ : syracuseStep 2092085 = 196133) (by norm_num)
theorem B1567813 : Blo 1393516 1567813 := bbase (se 4 (by rfl) ⟨146982, by rfl⟩ : syracuseStep 1567813 = 293965) (by norm_num)
theorem B2092109 : Blo 1393516 2092109 := bbase (se 3 (by rfl) ⟨392270, by rfl⟩ : syracuseStep 2092109 = 784541) (by norm_num)
theorem B1764433 : Blo 1393516 1764433 := bbase (se 2 (by rfl) ⟨661662, by rfl⟩ : syracuseStep 1764433 = 1323325) (by norm_num)
theorem B2092133 : Blo 1393516 2092133 := bbase (se 4 (by rfl) ⟨196137, by rfl⟩ : syracuseStep 2092133 = 392275) (by norm_num)
theorem B1567849 : Blo 1393516 1567849 := bbase (se 2 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 1567849 = 1175887) (by norm_num)
theorem B2354285 : Blo 1393516 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B4705397 : Blo 1393516 4705397 := bbase (se 5 (by rfl) ⟨220565, by rfl⟩ : syracuseStep 4705397 = 441131) (by norm_num)
theorem B2092157 : Blo 1393516 2092157 := bbase (se 3 (by rfl) ⟨392279, by rfl⟩ : syracuseStep 2092157 = 784559) (by norm_num)
theorem B1674373 : Blo 1393516 1674373 := bbase (se 4 (by rfl) ⟨156972, by rfl⟩ : syracuseStep 1674373 = 313945) (by norm_num)
theorem B1567885 : Blo 1393516 1567885 := bbase (se 3 (by rfl) ⟨293978, by rfl⟩ : syracuseStep 1567885 = 587957) (by norm_num)
theorem B2976917 : Blo 1393516 2976917 := bbase (se 6 (by rfl) ⟨69771, by rfl⟩ : syracuseStep 2976917 = 139543) (by norm_num)
theorem B2092181 : Blo 1393516 2092181 := bbase (se 6 (by rfl) ⟨49035, by rfl⟩ : syracuseStep 2092181 = 98071) (by norm_num)
theorem B2092205 : Blo 1393516 2092205 := bbase (se 3 (by rfl) ⟨392288, by rfl⟩ : syracuseStep 2092205 = 784577) (by norm_num)
theorem B1567921 : Blo 1393516 1567921 := bbase (se 2 (by rfl) ⟨587970, by rfl⟩ : syracuseStep 1567921 = 1175941) (by norm_num)
theorem B2649277 : Blo 1393516 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B2092229 : Blo 1393516 2092229 := bbase (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) (by norm_num)
theorem B1567957 : Blo 1393516 1567957 := bbase (se 7 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 1567957 = 36749) (by norm_num)
theorem B2092253 : Blo 1393516 2092253 := bbase (se 3 (by rfl) ⟨392297, by rfl⟩ : syracuseStep 2092253 = 784595) (by norm_num)
theorem B3181805 : Blo 1393516 3181805 := bbase (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) (by norm_num)
theorem B2354413 : Blo 1393516 2354413 := bbase (se 3 (by rfl) ⟨441452, by rfl⟩ : syracuseStep 2354413 = 882905) (by norm_num)
theorem B2092277 : Blo 1393516 2092277 := bbase (se 5 (by rfl) ⟨98075, by rfl⟩ : syracuseStep 2092277 = 196151) (by norm_num)
theorem B1567993 : Blo 1393516 1567993 := bbase (se 2 (by rfl) ⟨587997, by rfl⟩ : syracuseStep 1567993 = 1175995) (by norm_num)
theorem B1764605 : Blo 1393516 1764605 := bbase (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) (by norm_num)
theorem B5295365 : Blo 1393516 5295365 := bbase (se 4 (by rfl) ⟨496440, by rfl⟩ : syracuseStep 5295365 = 992881) (by norm_num)
theorem B2092301 : Blo 1393516 2092301 := bbase (se 3 (by rfl) ⟨392306, by rfl⟩ : syracuseStep 2092301 = 784613) (by norm_num)
theorem B1568029 : Blo 1393516 1568029 := bbase (se 3 (by rfl) ⟨294005, by rfl⟩ : syracuseStep 1568029 = 588011) (by norm_num)
theorem B2092325 : Blo 1393516 2092325 := bbase (se 4 (by rfl) ⟨196155, by rfl⟩ : syracuseStep 2092325 = 392311) (by norm_num)
theorem B1764661 : Blo 1393516 1764661 := bbase (se 5 (by rfl) ⟨82718, by rfl⟩ : syracuseStep 1764661 = 165437) (by norm_num)
theorem B2092349 : Blo 1393516 2092349 := bbase (se 3 (by rfl) ⟨392315, by rfl⟩ : syracuseStep 2092349 = 784631) (by norm_num)
theorem B1568065 : Blo 1393516 1568065 := bbase (se 2 (by rfl) ⟨588024, by rfl⟩ : syracuseStep 1568065 = 1176049) (by norm_num)
theorem B2354501 : Blo 1393516 2354501 := bbase (se 4 (by rfl) ⟨220734, by rfl⟩ : syracuseStep 2354501 = 441469) (by norm_num)
theorem B2092373 : Blo 1393516 2092373 := bbase (se 11 (by rfl) ⟨1532, by rfl⟩ : syracuseStep 2092373 = 3065) (by norm_num)
theorem B1674589 : Blo 1393516 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B1568101 : Blo 1393516 1568101 := bbase (se 4 (by rfl) ⟨147009, by rfl⟩ : syracuseStep 1568101 = 294019) (by norm_num)
theorem B2092397 : Blo 1393516 2092397 := bbase (se 3 (by rfl) ⟨392324, by rfl⟩ : syracuseStep 2092397 = 784649) (by norm_num)
theorem B10587509 : Blo 1393516 10587509 := bbase (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) (by norm_num)
theorem B2977157 : Blo 1393516 2977157 := bbase (se 4 (by rfl) ⟨279108, by rfl⟩ : syracuseStep 2977157 = 558217) (by norm_num)
theorem B2092421 : Blo 1393516 2092421 := bbase (se 4 (by rfl) ⟨196164, by rfl⟩ : syracuseStep 2092421 = 392329) (by norm_num)
theorem B1568137 : Blo 1393516 1568137 := bbase (se 2 (by rfl) ⟨588051, by rfl⟩ : syracuseStep 1568137 = 1176103) (by norm_num)
theorem B1764757 : Blo 1393516 1764757 := bbase (se 6 (by rfl) ⟨41361, by rfl⟩ : syracuseStep 1764757 = 82723) (by norm_num)
theorem B2092445 : Blo 1393516 2092445 := bbase (se 3 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 2092445 = 784667) (by norm_num)
theorem B1568173 : Blo 1393516 1568173 := bbase (se 3 (by rfl) ⟨294032, by rfl⟩ : syracuseStep 1568173 = 588065) (by norm_num)
theorem B2092469 : Blo 1393516 2092469 := bbase (se 5 (by rfl) ⟨98084, by rfl⟩ : syracuseStep 2092469 = 196169) (by norm_num)
theorem B2354629 : Blo 1393516 2354629 := bbase (se 4 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 2354629 = 441493) (by norm_num)
theorem B2092493 : Blo 1393516 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B3182029 : Blo 1393516 3182029 := bbase (se 3 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 3182029 = 1193261) (by norm_num)
theorem B1568209 : Blo 1393516 1568209 := bbase (se 2 (by rfl) ⟨588078, by rfl⟩ : syracuseStep 1568209 = 1176157) (by norm_num)
theorem B2092517 : Blo 1393516 2092517 := bbase (se 4 (by rfl) ⟨196173, by rfl⟩ : syracuseStep 2092517 = 392347) (by norm_num)
theorem B1568245 : Blo 1393516 1568245 := bbase (se 5 (by rfl) ⟨73511, by rfl⟩ : syracuseStep 1568245 = 147023) (by norm_num)
theorem B2092541 : Blo 1393516 2092541 := bbase (se 3 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 2092541 = 784703) (by norm_num)
theorem B2092565 : Blo 1393516 2092565 := bbase (se 6 (by rfl) ⟨49044, by rfl⟩ : syracuseStep 2092565 = 98089) (by norm_num)
theorem B1568281 : Blo 1393516 1568281 := bbase (se 2 (by rfl) ⟨588105, by rfl⟩ : syracuseStep 1568281 = 1176211) (by norm_num)
theorem B2354717 : Blo 1393516 2354717 := bbase (se 3 (by rfl) ⟨441509, by rfl⟩ : syracuseStep 2354717 = 883019) (by norm_num)
theorem B4705829 : Blo 1393516 4705829 := bbase (se 4 (by rfl) ⟨441171, by rfl⟩ : syracuseStep 4705829 = 882343) (by norm_num)
theorem B2092589 : Blo 1393516 2092589 := bbase (se 3 (by rfl) ⟨392360, by rfl⟩ : syracuseStep 2092589 = 784721) (by norm_num)
theorem B1568317 : Blo 1393516 1568317 := bbase (se 3 (by rfl) ⟨294059, by rfl⟩ : syracuseStep 1568317 = 588119) (by norm_num)
theorem B1764929 : Blo 1393516 1764929 := bbase (se 2 (by rfl) ⟨661848, by rfl⟩ : syracuseStep 1764929 = 1323697) (by norm_num)
theorem B2092613 : Blo 1393516 2092613 := bbase (se 4 (by rfl) ⟨196182, by rfl⟩ : syracuseStep 2092613 = 392365) (by norm_num)
theorem B48303701 : Blo 1393516 48303701 := bbase (se 8 (by rfl) ⟨283029, by rfl⟩ : syracuseStep 48303701 = 566059) (by norm_num)
theorem B2092637 : Blo 1393516 2092637 := bbase (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) (by norm_num)
theorem B1568353 : Blo 1393516 1568353 := bbase (se 2 (by rfl) ⟨588132, by rfl⟩ : syracuseStep 1568353 = 1176265) (by norm_num)
theorem B2092661 : Blo 1393516 2092661 := bbase (se 5 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 2092661 = 196187) (by norm_num)
theorem B1764985 : Blo 1393516 1764985 := bbase (se 2 (by rfl) ⟨661869, by rfl⟩ : syracuseStep 1764985 = 1323739) (by norm_num)
theorem B1568389 : Blo 1393516 1568389 := bbase (se 4 (by rfl) ⟨147036, by rfl⟩ : syracuseStep 1568389 = 294073) (by norm_num)
theorem B2092685 : Blo 1393516 2092685 := bbase (se 3 (by rfl) ⟨392378, by rfl⟩ : syracuseStep 2092685 = 784757) (by norm_num)
theorem B11308693 : Blo 1393516 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B2354845 : Blo 1393516 2354845 := bbase (se 3 (by rfl) ⟨441533, by rfl⟩ : syracuseStep 2354845 = 883067) (by norm_num)
theorem B2092709 : Blo 1393516 2092709 := bbase (se 4 (by rfl) ⟨196191, by rfl⟩ : syracuseStep 2092709 = 392383) (by norm_num)
theorem B1568425 : Blo 1393516 1568425 := bbase (se 2 (by rfl) ⟨588159, by rfl⟩ : syracuseStep 1568425 = 1176319) (by norm_num)
theorem B1986229 : Blo 1393516 1986229 := bbase (se 5 (by rfl) ⟨93104, by rfl⟩ : syracuseStep 1986229 = 186209) (by norm_num)
theorem B2092733 : Blo 1393516 2092733 := bbase (se 3 (by rfl) ⟨392387, by rfl⟩ : syracuseStep 2092733 = 784775) (by norm_num)
theorem B1568461 : Blo 1393516 1568461 := bbase (se 3 (by rfl) ⟨294086, by rfl⟩ : syracuseStep 1568461 = 588173) (by norm_num)
theorem B2092757 : Blo 1393516 2092757 := bbase (se 7 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 2092757 = 49049) (by norm_num)
theorem B1765081 : Blo 1393516 1765081 := bbase (se 2 (by rfl) ⟨661905, by rfl⟩ : syracuseStep 1765081 = 1323811) (by norm_num)
theorem B2092781 : Blo 1393516 2092781 := bbase (se 3 (by rfl) ⟨392396, by rfl⟩ : syracuseStep 2092781 = 784793) (by norm_num)
theorem B1568497 : Blo 1393516 1568497 := bbase (se 2 (by rfl) ⟨588186, by rfl⟩ : syracuseStep 1568497 = 1176373) (by norm_num)
theorem B2354933 : Blo 1393516 2354933 := bbase (se 5 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 2354933 = 220775) (by norm_num)
theorem B2092805 : Blo 1393516 2092805 := bbase (se 4 (by rfl) ⟨196200, by rfl⟩ : syracuseStep 2092805 = 392401) (by norm_num)
theorem B1568533 : Blo 1393516 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B2092829 : Blo 1393516 2092829 := bbase (se 3 (by rfl) ⟨392405, by rfl⟩ : syracuseStep 2092829 = 784811) (by norm_num)
theorem B7057205 : Blo 1393516 7057205 := bbase (se 5 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 7057205 = 661613) (by norm_num)
theorem B2092853 : Blo 1393516 2092853 := bbase (se 5 (by rfl) ⟨98102, by rfl⟩ : syracuseStep 2092853 = 196205) (by norm_num)
theorem B1568569 : Blo 1393516 1568569 := bbase (se 2 (by rfl) ⟨588213, by rfl⟩ : syracuseStep 1568569 = 1176427) (by norm_num)
theorem B2092877 : Blo 1393516 2092877 := bbase (se 3 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 2092877 = 784829) (by norm_num)
theorem B1568605 : Blo 1393516 1568605 := bbase (se 3 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 1568605 = 588227) (by norm_num)
theorem B2092901 : Blo 1393516 2092901 := bbase (se 4 (by rfl) ⟨196209, by rfl⟩ : syracuseStep 2092901 = 392419) (by norm_num)
theorem B2977661 : Blo 1393516 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B2092925 : Blo 1393516 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B1568641 : Blo 1393516 1568641 := bbase (se 2 (by rfl) ⟨588240, by rfl⟩ : syracuseStep 1568641 = 1176481) (by norm_num)
theorem B2977669 : Blo 1393516 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1765253 : Blo 1393516 1765253 := bbase (se 4 (by rfl) ⟨165492, by rfl⟩ : syracuseStep 1765253 = 330985) (by norm_num)
theorem B8736661 : Blo 1393516 8736661 := bbase (se 6 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 8736661 = 409531) (by norm_num)
theorem B2092949 : Blo 1393516 2092949 := bbase (se 6 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 2092949 = 98107) (by norm_num)
theorem B1568677 : Blo 1393516 1568677 := bbase (se 4 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 1568677 = 294127) (by norm_num)
theorem B2092973 : Blo 1393516 2092973 := bbase (se 3 (by rfl) ⟨392432, by rfl⟩ : syracuseStep 2092973 = 784865) (by norm_num)
theorem B1675189 : Blo 1393516 1675189 := bbase (se 5 (by rfl) ⟨78524, by rfl⟩ : syracuseStep 1675189 = 157049) (by norm_num)
theorem B1765309 : Blo 1393516 1765309 := bbase (se 3 (by rfl) ⟨330995, by rfl⟩ : syracuseStep 1765309 = 661991) (by norm_num)
theorem B2092997 : Blo 1393516 2092997 := bbase (se 4 (by rfl) ⟨196218, by rfl⟩ : syracuseStep 2092997 = 392437) (by norm_num)
theorem B1568713 : Blo 1393516 1568713 := bbase (se 2 (by rfl) ⟨588267, by rfl⟩ : syracuseStep 1568713 = 1176535) (by norm_num)
theorem B4706261 : Blo 1393516 4706261 := bbase (se 7 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 4706261 = 110303) (by norm_num)
theorem B2093021 : Blo 1393516 2093021 := bbase (se 3 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 2093021 = 784883) (by norm_num)
theorem B4468709 : Blo 1393516 4468709 := bbase (se 4 (by rfl) ⟨418941, by rfl⟩ : syracuseStep 4468709 = 837883) (by norm_num)
theorem B1568749 : Blo 1393516 1568749 := bbase (se 3 (by rfl) ⟨294140, by rfl⟩ : syracuseStep 1568749 = 588281) (by norm_num)
theorem B2093045 : Blo 1393516 2093045 := bbase (se 5 (by rfl) ⟨98111, by rfl⟩ : syracuseStep 2093045 = 196223) (by norm_num)
theorem B2093069 : Blo 1393516 2093069 := bbase (se 3 (by rfl) ⟨392450, by rfl⟩ : syracuseStep 2093069 = 784901) (by norm_num)
theorem B1568785 : Blo 1393516 1568785 := bbase (se 2 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 1568785 = 1176589) (by norm_num)
theorem B1765405 : Blo 1393516 1765405 := bbase (se 3 (by rfl) ⟨331013, by rfl⟩ : syracuseStep 1765405 = 662027) (by norm_num)
theorem B4239397 : Blo 1393516 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B2093093 : Blo 1393516 2093093 := bbase (se 4 (by rfl) ⟨196227, by rfl⟩ : syracuseStep 2093093 = 392455) (by norm_num)
theorem B1568821 : Blo 1393516 1568821 := bbase (se 5 (by rfl) ⟨73538, by rfl⟩ : syracuseStep 1568821 = 147077) (by norm_num)
theorem B2093117 : Blo 1393516 2093117 := bbase (se 3 (by rfl) ⟨392459, by rfl⟩ : syracuseStep 2093117 = 784919) (by norm_num)
theorem B2093141 : Blo 1393516 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1568857 : Blo 1393516 1568857 := bbase (se 2 (by rfl) ⟨588321, by rfl⟩ : syracuseStep 1568857 = 1176643) (by norm_num)
theorem B5959781 : Blo 1393516 5959781 := bbase (se 4 (by rfl) ⟨558729, by rfl⟩ : syracuseStep 5959781 = 1117459) (by norm_num)
theorem B2093165 : Blo 1393516 2093165 := bbase (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) (by norm_num)
theorem B1568893 : Blo 1393516 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B2093189 : Blo 1393516 2093189 := bbase (se 4 (by rfl) ⟨196236, by rfl⟩ : syracuseStep 2093189 = 392473) (by norm_num)
theorem B2093213 : Blo 1393516 2093213 := bbase (se 3 (by rfl) ⟨392477, by rfl⟩ : syracuseStep 2093213 = 784955) (by norm_num)
theorem B1568929 : Blo 1393516 1568929 := bbase (se 2 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 1568929 = 1176697) (by norm_num)
theorem B2093237 : Blo 1393516 2093237 := bbase (se 5 (by rfl) ⟨98120, by rfl⟩ : syracuseStep 2093237 = 196241) (by norm_num)
theorem B1568965 : Blo 1393516 1568965 := bbase (se 4 (by rfl) ⟨147090, by rfl⟩ : syracuseStep 1568965 = 294181) (by norm_num)
theorem B1765577 : Blo 1393516 1765577 := bbase (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) (by norm_num)
theorem B2093261 : Blo 1393516 2093261 := bbase (se 3 (by rfl) ⟨392486, by rfl⟩ : syracuseStep 2093261 = 784973) (by norm_num)
theorem B9539797 : Blo 1393516 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B1569001 : Blo 1393516 1569001 := bbase (se 2 (by rfl) ⟨588375, by rfl⟩ : syracuseStep 1569001 = 1176751) (by norm_num)
theorem B3969269 : Blo 1393516 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B1765633 : Blo 1393516 1765633 := bbase (se 2 (by rfl) ⟨662112, by rfl⟩ : syracuseStep 1765633 = 1324225) (by norm_num)
theorem B1569037 : Blo 1393516 1569037 := bbase (se 3 (by rfl) ⟨294194, by rfl⟩ : syracuseStep 1569037 = 588389) (by norm_num)
theorem B6705445 : Blo 1393516 6705445 := bbase (se 4 (by rfl) ⟨628635, by rfl⟩ : syracuseStep 6705445 = 1257271) (by norm_num)
theorem B1569073 : Blo 1393516 1569073 := bbase (se 2 (by rfl) ⟨588402, by rfl⟩ : syracuseStep 1569073 = 1176805) (by norm_num)
theorem B1790257 : Blo 1393516 1790257 := bbase (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) (by norm_num)
theorem B1413433 : Blo 1393516 1413433 := bbase (se 2 (by rfl) ⟨530037, by rfl⟩ : syracuseStep 1413433 = 1060075) (by norm_num)
theorem B1569109 : Blo 1393516 1569109 := bbase (se 10 (by rfl) ⟨2298, by rfl⟩ : syracuseStep 1569109 = 4597) (by norm_num)
theorem B1765729 : Blo 1393516 1765729 := bbase (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) (by norm_num)
theorem B1569145 : Blo 1393516 1569145 := bbase (se 2 (by rfl) ⟨588429, by rfl⟩ : syracuseStep 1569145 = 1176859) (by norm_num)
theorem B4706693 : Blo 1393516 4706693 := bbase (se 4 (by rfl) ⟨441252, by rfl⟩ : syracuseStep 4706693 = 882505) (by norm_num)
theorem B1569181 : Blo 1393516 1569181 := bbase (se 3 (by rfl) ⟨294221, by rfl⟩ : syracuseStep 1569181 = 588443) (by norm_num)
theorem B5296549 : Blo 1393516 5296549 := bbase (se 4 (by rfl) ⟨496551, by rfl⟩ : syracuseStep 5296549 = 993103) (by norm_num)
theorem B1569217 : Blo 1393516 1569217 := bbase (se 2 (by rfl) ⟨588456, by rfl⟩ : syracuseStep 1569217 = 1176913) (by norm_num)
theorem B1569253 : Blo 1393516 1569253 := bbase (se 4 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 1569253 = 294235) (by norm_num)
theorem B1569289 : Blo 1393516 1569289 := bbase (se 2 (by rfl) ⟨588483, by rfl⟩ : syracuseStep 1569289 = 1176967) (by norm_num)
theorem B1765901 : Blo 1393516 1765901 := bbase (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) (by norm_num)
theorem B1569325 : Blo 1393516 1569325 := bbase (se 3 (by rfl) ⟨294248, by rfl⟩ : syracuseStep 1569325 = 588497) (by norm_num)
theorem B2232893 : Blo 1393516 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B1765957 : Blo 1393516 1765957 := bbase (se 4 (by rfl) ⟨165558, by rfl⟩ : syracuseStep 1765957 = 331117) (by norm_num)
theorem B1569361 : Blo 1393516 1569361 := bbase (se 2 (by rfl) ⟨588510, by rfl⟩ : syracuseStep 1569361 = 1177021) (by norm_num)
theorem B1569397 : Blo 1393516 1569397 := bbase (se 5 (by rfl) ⟨73565, by rfl⟩ : syracuseStep 1569397 = 147131) (by norm_num)
theorem B1569433 : Blo 1393516 1569433 := bbase (se 2 (by rfl) ⟨588537, by rfl⟩ : syracuseStep 1569433 = 1177075) (by norm_num)
theorem B1766053 : Blo 1393516 1766053 := bbase (se 4 (by rfl) ⟨165567, by rfl⟩ : syracuseStep 1766053 = 331135) (by norm_num)
theorem B1569469 : Blo 1393516 1569469 := bbase (se 3 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 1569469 = 588551) (by norm_num)
theorem B5296853 : Blo 1393516 5296853 := bbase (se 7 (by rfl) ⟨62072, by rfl⟩ : syracuseStep 5296853 = 124145) (by norm_num)
theorem B1569505 : Blo 1393516 1569505 := bbase (se 2 (by rfl) ⟨588564, by rfl⟩ : syracuseStep 1569505 = 1177129) (by norm_num)
theorem B1569541 : Blo 1393516 1569541 := bbase (se 4 (by rfl) ⟨147144, by rfl⟩ : syracuseStep 1569541 = 294289) (by norm_num)
theorem B1569577 : Blo 1393516 1569577 := bbase (se 2 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 1569577 = 1177183) (by norm_num)
theorem B4707125 : Blo 1393516 4707125 := bbase (se 5 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 4707125 = 441293) (by norm_num)
theorem B1569613 : Blo 1393516 1569613 := bbase (se 3 (by rfl) ⟨294302, by rfl⟩ : syracuseStep 1569613 = 588605) (by norm_num)
theorem B3527509 : Blo 1393516 3527509 := bbase (se 9 (by rfl) ⟨10334, by rfl⟩ : syracuseStep 3527509 = 20669) (by norm_num)
theorem B1413973 : Blo 1393516 1413973 := bbase (se 9 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 1413973 = 8285) (by norm_num)
theorem B1569649 : Blo 1393516 1569649 := bbase (se 2 (by rfl) ⟨588618, by rfl⟩ : syracuseStep 1569649 = 1177237) (by norm_num)
theorem B1569685 : Blo 1393516 1569685 := bbase (se 6 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 1569685 = 73579) (by norm_num)
theorem B4527029 : Blo 1393516 4527029 := bbase (se 5 (by rfl) ⟨212204, by rfl⟩ : syracuseStep 4527029 = 424409) (by norm_num)
theorem B7943093 : Blo 1393516 7943093 := bbase (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) (by norm_num)
theorem B1569721 : Blo 1393516 1569721 := bbase (se 2 (by rfl) ⟨588645, by rfl⟩ : syracuseStep 1569721 = 1177291) (by norm_num)
theorem B3527621 : Blo 1393516 3527621 := bbase (se 4 (by rfl) ⟨330714, by rfl⟩ : syracuseStep 3527621 = 661429) (by norm_num)
theorem B6034373 : Blo 1393516 6034373 := bbase (se 4 (by rfl) ⟨565722, by rfl⟩ : syracuseStep 6034373 = 1131445) (by norm_num)
theorem B1569757 : Blo 1393516 1569757 := bbase (se 3 (by rfl) ⟨294329, by rfl⟩ : syracuseStep 1569757 = 588659) (by norm_num)
theorem B2978797 : Blo 1393516 2978797 := bbase (se 3 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 2978797 = 1117049) (by norm_num)
theorem B1569793 : Blo 1393516 1569793 := bbase (se 2 (by rfl) ⟨588672, by rfl⟩ : syracuseStep 1569793 = 1177345) (by norm_num)
theorem B2233349 : Blo 1393516 2233349 := bbase (se 4 (by rfl) ⟨209376, by rfl⟩ : syracuseStep 2233349 = 418753) (by norm_num)
theorem B1569829 : Blo 1393516 1569829 := bbase (se 4 (by rfl) ⟨147171, by rfl⟩ : syracuseStep 1569829 = 294343) (by norm_num)
theorem B1676333 : Blo 1393516 1676333 := bbase (se 3 (by rfl) ⟨314312, by rfl⟩ : syracuseStep 1676333 = 628625) (by norm_num)
theorem B7058501 : Blo 1393516 7058501 := bbase (se 4 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 7058501 = 1323469) (by norm_num)
theorem B1569865 : Blo 1393516 1569865 := bbase (se 2 (by rfl) ⟨588699, by rfl⟩ : syracuseStep 1569865 = 1177399) (by norm_num)
theorem B1676381 : Blo 1393516 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1569901 : Blo 1393516 1569901 := bbase (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) (by norm_num)
theorem B3527813 : Blo 1393516 3527813 := bbase (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) (by norm_num)
theorem B1569937 : Blo 1393516 1569937 := bbase (se 2 (by rfl) ⟨588726, by rfl⟩ : syracuseStep 1569937 = 1177453) (by norm_num)
theorem B1676477 : Blo 1393516 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B4707557 : Blo 1393516 4707557 := bbase (se 4 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 4707557 = 882667) (by norm_num)
theorem B3626293 : Blo 1393516 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B6362453 : Blo 1393516 6362453 := bbase (se 14 (by rfl) ⟨582, by rfl⟩ : syracuseStep 6362453 = 1165) (by norm_num)
theorem B2979173 : Blo 1393516 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B3970453 : Blo 1393516 3970453 := bbase (se 6 (by rfl) ⟨93057, by rfl⟩ : syracuseStep 3970453 = 186115) (by norm_num)
theorem B1488305 : Blo 1393516 1488305 := bbase (se 2 (by rfl) ⟨558114, by rfl⟩ : syracuseStep 1488305 = 1116229) (by norm_num)
theorem B2512309 : Blo 1393516 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B3528157 : Blo 1393516 3528157 := bbase (se 3 (by rfl) ⟨661529, by rfl⟩ : syracuseStep 3528157 = 1323059) (by norm_num)
theorem B2119213 : Blo 1393516 2119213 := bbase (se 3 (by rfl) ⟨397352, by rfl⟩ : syracuseStep 2119213 = 794705) (by norm_num)
theorem B3970613 : Blo 1393516 3970613 := bbase (se 5 (by rfl) ⟨186122, by rfl⟩ : syracuseStep 3970613 = 372245) (by norm_num)
theorem B3528269 : Blo 1393516 3528269 := bbase (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) (by norm_num)
theorem B1488493 : Blo 1393516 1488493 := bbase (se 3 (by rfl) ⟨279092, by rfl⟩ : syracuseStep 1488493 = 558185) (by norm_num)
theorem B4707989 : Blo 1393516 4707989 := bbase (se 6 (by rfl) ⟨110343, by rfl⟩ : syracuseStep 4707989 = 220687) (by norm_num)
theorem B3528461 : Blo 1393516 3528461 := bbase (se 3 (by rfl) ⟨661586, by rfl⟩ : syracuseStep 3528461 = 1323173) (by norm_num)
theorem B3970853 : Blo 1393516 3970853 := bbase (se 4 (by rfl) ⟨372267, by rfl⟩ : syracuseStep 3970853 = 744535) (by norm_num)
theorem B3348341 : Blo 1393516 3348341 := bbase (se 5 (by rfl) ⟨156953, by rfl⟩ : syracuseStep 3348341 = 313907) (by norm_num)
theorem B11917205 : Blo 1393516 11917205 := bbase (se 6 (by rfl) ⟨279309, by rfl⟩ : syracuseStep 11917205 = 558619) (by norm_num)
theorem B3135437 : Blo 1393516 3135437 := bbase (se 3 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 3135437 = 1175789) (by norm_num)
theorem B5953493 : Blo 1393516 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B3971045 : Blo 1393516 3971045 := bbase (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) (by norm_num)
theorem B5027845 : Blo 1393516 5027845 := bbase (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) (by norm_num)
theorem B3135509 : Blo 1393516 3135509 := bbase (se 6 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 3135509 = 146977) (by norm_num)
theorem B3348533 : Blo 1393516 3348533 := bbase (se 5 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 3348533 = 313925) (by norm_num)
theorem B5363765 : Blo 1393516 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B4708421 : Blo 1393516 4708421 := bbase (se 4 (by rfl) ⟨441414, by rfl⟩ : syracuseStep 4708421 = 882829) (by norm_num)
theorem B7944277 : Blo 1393516 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B3135581 : Blo 1393516 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B3528805 : Blo 1393516 3528805 := bbase (se 4 (by rfl) ⟨330825, by rfl⟩ : syracuseStep 3528805 = 661651) (by norm_num)
theorem B4528261 : Blo 1393516 4528261 := bbase (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) (by norm_num)
theorem B3061901 : Blo 1393516 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B3135653 : Blo 1393516 3135653 := bbase (se 4 (by rfl) ⟨293967, by rfl⟩ : syracuseStep 3135653 = 587935) (by norm_num)
theorem B5953733 : Blo 1393516 5953733 := bbase (se 4 (by rfl) ⟨558162, by rfl⟩ : syracuseStep 5953733 = 1116325) (by norm_num)
theorem B2513101 : Blo 1393516 2513101 := bbase (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) (by norm_num)
theorem B3528917 : Blo 1393516 3528917 := bbase (se 7 (by rfl) ⟨41354, by rfl⟩ : syracuseStep 3528917 = 82709) (by norm_num)
theorem B3135725 : Blo 1393516 3135725 := bbase (se 3 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 3135725 = 1175897) (by norm_num)
theorem B3135797 : Blo 1393516 3135797 := bbase (se 5 (by rfl) ⟨146990, by rfl⟩ : syracuseStep 3135797 = 293981) (by norm_num)
theorem B3348821 : Blo 1393516 3348821 := bbase (se 10 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 3348821 = 9811) (by norm_num)
theorem B7059797 : Blo 1393516 7059797 := bbase (se 10 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 7059797 = 20683) (by norm_num)
theorem B8477045 : Blo 1393516 8477045 := bbase (se 5 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 8477045 = 794723) (by norm_num)
theorem B3135869 : Blo 1393516 3135869 := bbase (se 3 (by rfl) ⟨587975, by rfl⟩ : syracuseStep 3135869 = 1175951) (by norm_num)
theorem B2234765 : Blo 1393516 2234765 := bbase (se 3 (by rfl) ⟨419018, by rfl⟩ : syracuseStep 2234765 = 838037) (by norm_num)
theorem B2685325 : Blo 1393516 2685325 := bbase (se 3 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 2685325 = 1006997) (by norm_num)
theorem B3529109 : Blo 1393516 3529109 := bbase (se 6 (by rfl) ⟨82713, by rfl⟩ : syracuseStep 3529109 = 165427) (by norm_num)
theorem B1489313 : Blo 1393516 1489313 := bbase (se 2 (by rfl) ⟨558492, by rfl⟩ : syracuseStep 1489313 = 1116985) (by norm_num)
theorem B3135941 : Blo 1393516 3135941 := bbase (se 4 (by rfl) ⟨293994, by rfl⟩ : syracuseStep 3135941 = 587989) (by norm_num)
theorem B4708853 : Blo 1393516 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B2513405 : Blo 1393516 2513405 := bbase (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) (by norm_num)
theorem B3136013 : Blo 1393516 3136013 := bbase (se 3 (by rfl) ⟨588002, by rfl⟩ : syracuseStep 3136013 = 1176005) (by norm_num)
theorem B3136085 : Blo 1393516 3136085 := bbase (se 8 (by rfl) ⟨18375, by rfl⟩ : syracuseStep 3136085 = 36751) (by norm_num)
theorem B2234989 : Blo 1393516 2234989 := bbase (se 3 (by rfl) ⟨419060, by rfl⟩ : syracuseStep 2234989 = 838121) (by norm_num)
theorem B22928021 : Blo 1393516 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B3136157 : Blo 1393516 3136157 := bbase (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) (by norm_num)
theorem B2120357 : Blo 1393516 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B3627733 : Blo 1393516 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B3136229 : Blo 1393516 3136229 := bbase (se 4 (by rfl) ⟨294021, by rfl⟩ : syracuseStep 3136229 = 588043) (by norm_num)
theorem B4242149 : Blo 1393516 4242149 := bbase (se 4 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 4242149 = 795403) (by norm_num)
theorem B3529453 : Blo 1393516 3529453 := bbase (se 3 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 3529453 = 1323545) (by norm_num)
theorem B2513693 : Blo 1393516 2513693 := bbase (se 3 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 2513693 = 942635) (by norm_num)
theorem B3136301 : Blo 1393516 3136301 := bbase (se 3 (by rfl) ⟨588056, by rfl⟩ : syracuseStep 3136301 = 1176113) (by norm_num)
theorem B3529565 : Blo 1393516 3529565 := bbase (se 3 (by rfl) ⟨661793, by rfl⟩ : syracuseStep 3529565 = 1323587) (by norm_num)
theorem B1489757 : Blo 1393516 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B3136373 : Blo 1393516 3136373 := bbase (se 5 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 3136373 = 294035) (by norm_num)
theorem B3627917 : Blo 1393516 3627917 := bbase (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) (by norm_num)
theorem B17882005 : Blo 1393516 17882005 := bbase (se 6 (by rfl) ⟨419109, by rfl⟩ : syracuseStep 17882005 = 838219) (by norm_num)
theorem B4709285 : Blo 1393516 4709285 := bbase (se 4 (by rfl) ⟨441495, by rfl⟩ : syracuseStep 4709285 = 882991) (by norm_num)
theorem B3136445 : Blo 1393516 3136445 := bbase (se 3 (by rfl) ⟨588083, by rfl⟩ : syracuseStep 3136445 = 1176167) (by norm_num)
theorem B3972037 : Blo 1393516 3972037 := bbase (se 4 (by rfl) ⟨372378, by rfl⟩ : syracuseStep 3972037 = 744757) (by norm_num)
theorem B10730485 : Blo 1393516 10730485 := bbase (se 5 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 10730485 = 1005983) (by norm_num)
theorem B5028853 : Blo 1393516 5028853 := bbase (se 5 (by rfl) ⟨235727, by rfl⟩ : syracuseStep 5028853 = 471455) (by norm_num)
theorem B3136517 : Blo 1393516 3136517 := bbase (se 4 (by rfl) ⟨294048, by rfl⟩ : syracuseStep 3136517 = 588097) (by norm_num)
theorem B3529757 : Blo 1393516 3529757 := bbase (se 3 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 3529757 = 1323659) (by norm_num)
theorem B2825293 : Blo 1393516 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B3136589 : Blo 1393516 3136589 := bbase (se 3 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 3136589 = 1176221) (by norm_num)
theorem B1490005 : Blo 1393516 1490005 := bbase (se 8 (by rfl) ⟨8730, by rfl⟩ : syracuseStep 1490005 = 17461) (by norm_num)
theorem B3136661 : Blo 1393516 3136661 := bbase (se 6 (by rfl) ⟨73515, by rfl⟩ : syracuseStep 3136661 = 147031) (by norm_num)
theorem B5291189 : Blo 1393516 5291189 := bbase (se 5 (by rfl) ⟨248024, by rfl⟩ : syracuseStep 5291189 = 496049) (by norm_num)
theorem B3136733 : Blo 1393516 3136733 := bbase (se 3 (by rfl) ⟨588137, by rfl⟩ : syracuseStep 3136733 = 1176275) (by norm_num)
theorem B3136805 : Blo 1393516 3136805 := bbase (se 4 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 3136805 = 588151) (by norm_num)
theorem B4709717 : Blo 1393516 4709717 := bbase (se 11 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 4709717 = 6899) (by norm_num)
theorem B3136877 : Blo 1393516 3136877 := bbase (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) (by norm_num)
theorem B3530101 : Blo 1393516 3530101 := bbase (se 5 (by rfl) ⟨165473, by rfl⟩ : syracuseStep 3530101 = 330947) (by norm_num)
theorem B3136949 : Blo 1393516 3136949 := bbase (se 5 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 3136949 = 294089) (by norm_num)
theorem B5291477 : Blo 1393516 5291477 := bbase (se 7 (by rfl) ⟨62009, by rfl⟩ : syracuseStep 5291477 = 124019) (by norm_num)
theorem B3530213 : Blo 1393516 3530213 := bbase (se 4 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 3530213 = 661915) (by norm_num)
theorem B3137021 : Blo 1393516 3137021 := bbase (se 3 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 3137021 = 1176383) (by norm_num)
theorem B2514485 : Blo 1393516 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B3137093 : Blo 1393516 3137093 := bbase (se 4 (by rfl) ⟨294102, by rfl⟩ : syracuseStep 3137093 = 588205) (by norm_num)
theorem B7061093 : Blo 1393516 7061093 := bbase (se 4 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 7061093 = 1323955) (by norm_num)
theorem B3137165 : Blo 1393516 3137165 := bbase (se 3 (by rfl) ⟨588218, by rfl⟩ : syracuseStep 3137165 = 1176437) (by norm_num)
theorem B3530405 : Blo 1393516 3530405 := bbase (se 4 (by rfl) ⟨330975, by rfl⟩ : syracuseStep 3530405 = 661951) (by norm_num)
theorem B2645693 : Blo 1393516 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B2514629 : Blo 1393516 2514629 := bbase (se 4 (by rfl) ⟨235746, by rfl⟩ : syracuseStep 2514629 = 471493) (by norm_num)
theorem B2825933 : Blo 1393516 2825933 := bbase (se 3 (by rfl) ⟨529862, by rfl⟩ : syracuseStep 2825933 = 1059725) (by norm_num)
theorem B3137237 : Blo 1393516 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B1883917 : Blo 1393516 1883917 := bbase (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) (by norm_num)
theorem B3137309 : Blo 1393516 3137309 := bbase (se 3 (by rfl) ⟨588245, by rfl⟩ : syracuseStep 3137309 = 1176491) (by norm_num)
theorem B3137381 : Blo 1393516 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B3178381 : Blo 1393516 3178381 := bbase (se 3 (by rfl) ⟨595946, by rfl⟩ : syracuseStep 3178381 = 1191893) (by norm_num)
theorem B3137453 : Blo 1393516 3137453 := bbase (se 3 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 3137453 = 1176545) (by norm_num)
theorem B3137525 : Blo 1393516 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B3530749 : Blo 1393516 3530749 := bbase (se 3 (by rfl) ⟨662015, by rfl⟩ : syracuseStep 3530749 = 1324031) (by norm_num)
theorem B3973187 : Blo 1393516 3973187 := bstep (se 1 (by rfl) ⟨2979890, by rfl⟩ : syracuseStep 3973187 = 5959781) B5959781
theorem B10592369 : Blo 1393516 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B2646179 : Blo 1393516 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B6037681 : Blo 1393516 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B3629233 : Blo 1393516 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B22610117 : Blo 1393516 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B7536881 : Blo 1393516 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B3137777 : Blo 1393516 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B3137795 : Blo 1393516 3137795 := bstep (se 1 (by rfl) ⟨2353346, by rfl⟩ : syracuseStep 3137795 = 4706693) B4706693
theorem B3350801 : Blo 1393516 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B9060707 : Blo 1393516 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B4768109 : Blo 1393516 4768109 := bstep (se 3 (by rfl) ⟨894020, by rfl⟩ : syracuseStep 4768109 = 1788041) B1788041
theorem B7938445 : Blo 1393516 7938445 := bstep (se 3 (by rfl) ⟨1488458, by rfl⟩ : syracuseStep 7938445 = 2976917) B2976917
theorem B3531185 : Blo 1393516 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B7946693 : Blo 1393516 7946693 := bstep (se 4 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 7946693 = 1490005) B1490005
theorem B2351585 : Blo 1393516 2351585 := bstep (se 2 (by rfl) ⟨881844, by rfl⟩ : syracuseStep 2351585 = 1763689) B1763689
theorem B3531235 : Blo 1393516 3531235 := bstep (se 1 (by rfl) ⟨2648426, by rfl⟩ : syracuseStep 3531235 = 5296853) B5296853
theorem B3138065 : Blo 1393516 3138065 := bstep (se 2 (by rfl) ⟨1176774, by rfl⟩ : syracuseStep 3138065 = 2353549) B2353549
theorem B3580433 : Blo 1393516 3580433 := bstep (se 2 (by rfl) ⟨1342662, by rfl⟩ : syracuseStep 3580433 = 2685325) B2685325
theorem B3138083 : Blo 1393516 3138083 := bstep (se 1 (by rfl) ⟨2353562, by rfl⟩ : syracuseStep 3138083 = 4707125) B4707125
theorem B7062065 : Blo 1393516 7062065 := bstep (se 2 (by rfl) ⟨2648274, by rfl⟩ : syracuseStep 7062065 = 5296549) B5296549
theorem B2351713 : Blo 1393516 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B3531377 : Blo 1393516 3531377 := bstep (se 2 (by rfl) ⟨1324266, by rfl⟩ : syracuseStep 3531377 = 2648533) B2648533
theorem B2351747 : Blo 1393516 2351747 := bstep (se 1 (by rfl) ⟨1763810, by rfl⟩ : syracuseStep 2351747 = 3527621) B3527621
theorem B4022915 : Blo 1393516 4022915 := bstep (se 1 (by rfl) ⟨3017186, by rfl⟩ : syracuseStep 4022915 = 6034373) B6034373
theorem B2417393 : Blo 1393516 2417393 := bstep (se 2 (by rfl) ⟨906522, by rfl⟩ : syracuseStep 2417393 = 1813045) B1813045
theorem B2351875 : Blo 1393516 2351875 := bstep (se 1 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 2351875 = 3527813) B3527813
theorem B3138353 : Blo 1393516 3138353 := bstep (se 2 (by rfl) ⟨1176882, by rfl⟩ : syracuseStep 3138353 = 2353765) B2353765
theorem B3138371 : Blo 1393516 3138371 := bstep (se 1 (by rfl) ⟨2353778, by rfl⟩ : syracuseStep 3138371 = 4707557) B4707557
theorem B1393523 : Blo 1393516 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B1393539 : Blo 1393516 1393539 := bstep (se 1 (by rfl) ⟨1045154, by rfl⟩ : syracuseStep 1393539 = 2090309) B2090309
theorem B8930189 : Blo 1393516 8930189 := bstep (se 3 (by rfl) ⟨1674410, by rfl⟩ : syracuseStep 8930189 = 3348821) B3348821
theorem B16966541 : Blo 1393516 16966541 := bstep (se 3 (by rfl) ⟨3181226, by rfl⟩ : syracuseStep 16966541 = 6362453) B6362453
theorem B2352017 : Blo 1393516 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B1393555 : Blo 1393516 1393555 := bstep (se 1 (by rfl) ⟨1045166, by rfl⟩ : syracuseStep 1393555 = 2090333) B2090333
theorem B1393571 : Blo 1393516 1393571 := bstep (se 1 (by rfl) ⟨1045178, by rfl⟩ : syracuseStep 1393571 = 2090357) B2090357
theorem B1393587 : Blo 1393516 1393587 := bstep (se 1 (by rfl) ⟨1045190, by rfl⟩ : syracuseStep 1393587 = 2090381) B2090381
theorem B1393603 : Blo 1393516 1393603 := bstep (se 1 (by rfl) ⟨1045202, by rfl⟩ : syracuseStep 1393603 = 2090405) B2090405
theorem B1393619 : Blo 1393516 1393619 := bstep (se 1 (by rfl) ⟨1045214, by rfl⟩ : syracuseStep 1393619 = 2090429) B2090429
theorem B1393635 : Blo 1393516 1393635 := bstep (se 1 (by rfl) ⟨1045226, by rfl⟩ : syracuseStep 1393635 = 2090453) B2090453
theorem B1393651 : Blo 1393516 1393651 := bstep (se 1 (by rfl) ⟨1045238, by rfl⟩ : syracuseStep 1393651 = 2090477) B2090477
theorem B1393667 : Blo 1393516 1393667 := bstep (se 1 (by rfl) ⟨1045250, by rfl⟩ : syracuseStep 1393667 = 2090501) B2090501
theorem B2352145 : Blo 1393516 2352145 := bstep (se 2 (by rfl) ⟨882054, by rfl⟩ : syracuseStep 2352145 = 1764109) B1764109
theorem B1393683 : Blo 1393516 1393683 := bstep (se 1 (by rfl) ⟨1045262, by rfl⟩ : syracuseStep 1393683 = 2090525) B2090525
theorem B1393699 : Blo 1393516 1393699 := bstep (se 1 (by rfl) ⟨1045274, by rfl⟩ : syracuseStep 1393699 = 2090549) B2090549
theorem B2647075 : Blo 1393516 2647075 := bstep (se 1 (by rfl) ⟨1985306, by rfl⟩ : syracuseStep 2647075 = 3970613) B3970613
theorem B1393715 : Blo 1393516 1393715 := bstep (se 1 (by rfl) ⟨1045286, by rfl⟩ : syracuseStep 1393715 = 2090573) B2090573
theorem B2352179 : Blo 1393516 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B1393731 : Blo 1393516 1393731 := bstep (se 1 (by rfl) ⟨1045298, by rfl⟩ : syracuseStep 1393731 = 2090597) B2090597
theorem B3179587 : Blo 1393516 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B5293133 : Blo 1393516 5293133 := bstep (se 3 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 5293133 = 1984925) B1984925
theorem B3138641 : Blo 1393516 3138641 := bstep (se 2 (by rfl) ⟨1176990, by rfl⟩ : syracuseStep 3138641 = 2353981) B2353981
theorem B1393747 : Blo 1393516 1393747 := bstep (se 1 (by rfl) ⟨1045310, by rfl⟩ : syracuseStep 1393747 = 2090621) B2090621
theorem B1393763 : Blo 1393516 1393763 := bstep (se 1 (by rfl) ⟨1045322, by rfl⟩ : syracuseStep 1393763 = 2090645) B2090645
theorem B6358115 : Blo 1393516 6358115 := bstep (se 1 (by rfl) ⟨4768586, by rfl⟩ : syracuseStep 6358115 = 9537173) B9537173
theorem B3138659 : Blo 1393516 3138659 := bstep (se 1 (by rfl) ⟨2353994, by rfl⟩ : syracuseStep 3138659 = 4707989) B4707989
theorem B4703345 : Blo 1393516 4703345 := bstep (se 2 (by rfl) ⟨1763754, by rfl⟩ : syracuseStep 4703345 = 3527509) B3527509
theorem B1885297 : Blo 1393516 1885297 := bstep (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) B1413973
theorem B1393779 : Blo 1393516 1393779 := bstep (se 1 (by rfl) ⟨1045334, by rfl⟩ : syracuseStep 1393779 = 2090669) B2090669
theorem B1393795 : Blo 1393516 1393795 := bstep (se 1 (by rfl) ⟨1045346, by rfl⟩ : syracuseStep 1393795 = 2090693) B2090693
theorem B1393811 : Blo 1393516 1393811 := bstep (se 1 (by rfl) ⟨1045358, by rfl⟩ : syracuseStep 1393811 = 2090717) B2090717
theorem B1393827 : Blo 1393516 1393827 := bstep (se 1 (by rfl) ⟨1045370, by rfl⟩ : syracuseStep 1393827 = 2090741) B2090741
theorem B1393843 : Blo 1393516 1393843 := bstep (se 1 (by rfl) ⟨1045382, by rfl⟩ : syracuseStep 1393843 = 2090765) B2090765
theorem B2352307 : Blo 1393516 2352307 := bstep (se 1 (by rfl) ⟨1764230, by rfl⟩ : syracuseStep 2352307 = 3528461) B3528461
theorem B1393859 : Blo 1393516 1393859 := bstep (se 1 (by rfl) ⟨1045394, by rfl⟩ : syracuseStep 1393859 = 2090789) B2090789
theorem B2647235 : Blo 1393516 2647235 := bstep (se 1 (by rfl) ⟨1985426, by rfl⟩ : syracuseStep 2647235 = 3970853) B3970853
theorem B1393875 : Blo 1393516 1393875 := bstep (se 1 (by rfl) ⟨1045406, by rfl⟩ : syracuseStep 1393875 = 2090813) B2090813
theorem B1393891 : Blo 1393516 1393891 := bstep (se 1 (by rfl) ⟨1045418, by rfl⟩ : syracuseStep 1393891 = 2090837) B2090837
theorem B1393907 : Blo 1393516 1393907 := bstep (se 1 (by rfl) ⟨1045430, by rfl⟩ : syracuseStep 1393907 = 2090861) B2090861
theorem B1393923 : Blo 1393516 1393923 := bstep (se 1 (by rfl) ⟨1045442, by rfl⟩ : syracuseStep 1393923 = 2090885) B2090885
theorem B1393939 : Blo 1393516 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B1393955 : Blo 1393516 1393955 := bstep (se 1 (by rfl) ⟨1045466, by rfl⟩ : syracuseStep 1393955 = 2090933) B2090933
theorem B6702371 : Blo 1393516 6702371 := bstep (se 1 (by rfl) ⟨5026778, by rfl⟩ : syracuseStep 6702371 = 10053557) B10053557
theorem B2090291 : Blo 1393516 2090291 := bstep (se 1 (by rfl) ⟨1567718, by rfl⟩ : syracuseStep 2090291 = 3135437) B3135437
theorem B1393971 : Blo 1393516 1393971 := bstep (se 1 (by rfl) ⟨1045478, by rfl⟩ : syracuseStep 1393971 = 2090957) B2090957
theorem B2352449 : Blo 1393516 2352449 := bstep (se 2 (by rfl) ⟨882168, by rfl⟩ : syracuseStep 2352449 = 1764337) B1764337
theorem B1393987 : Blo 1393516 1393987 := bstep (se 1 (by rfl) ⟨1045490, by rfl⟩ : syracuseStep 1393987 = 2090981) B2090981
theorem B2090321 : Blo 1393516 2090321 := bstep (se 2 (by rfl) ⟨783870, by rfl⟩ : syracuseStep 2090321 = 1567741) B1567741
theorem B1394003 : Blo 1393516 1394003 := bstep (se 1 (by rfl) ⟨1045502, by rfl⟩ : syracuseStep 1394003 = 2091005) B2091005
theorem B2090339 : Blo 1393516 2090339 := bstep (se 1 (by rfl) ⟨1567754, by rfl⟩ : syracuseStep 2090339 = 3135509) B3135509
theorem B1394019 : Blo 1393516 1394019 := bstep (se 1 (by rfl) ⟨1045514, by rfl⟩ : syracuseStep 1394019 = 2091029) B2091029
theorem B3138929 : Blo 1393516 3138929 := bstep (se 2 (by rfl) ⟨1177098, by rfl⟩ : syracuseStep 3138929 = 2354197) B2354197
theorem B1394035 : Blo 1393516 1394035 := bstep (se 1 (by rfl) ⟨1045526, by rfl⟩ : syracuseStep 1394035 = 2091053) B2091053
theorem B2090369 : Blo 1393516 2090369 := bstep (se 2 (by rfl) ⟨783888, by rfl⟩ : syracuseStep 2090369 = 1567777) B1567777
theorem B1394051 : Blo 1393516 1394051 := bstep (se 1 (by rfl) ⟨1045538, by rfl⟩ : syracuseStep 1394051 = 2091077) B2091077
theorem B3138947 : Blo 1393516 3138947 := bstep (se 1 (by rfl) ⟨2354210, by rfl⟩ : syracuseStep 3138947 = 4708421) B4708421
theorem B2090387 : Blo 1393516 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B1394067 : Blo 1393516 1394067 := bstep (se 1 (by rfl) ⟨1045550, by rfl⟩ : syracuseStep 1394067 = 2091101) B2091101
theorem B1394083 : Blo 1393516 1394083 := bstep (se 1 (by rfl) ⟨1045562, by rfl⟩ : syracuseStep 1394083 = 2091125) B2091125
theorem B2090417 : Blo 1393516 2090417 := bstep (se 2 (by rfl) ⟨783906, by rfl⟩ : syracuseStep 2090417 = 1567813) B1567813
theorem B1394099 : Blo 1393516 1394099 := bstep (se 1 (by rfl) ⟨1045574, by rfl⟩ : syracuseStep 1394099 = 2091149) B2091149
theorem B2352577 : Blo 1393516 2352577 := bstep (se 2 (by rfl) ⟨882216, by rfl⟩ : syracuseStep 2352577 = 1764433) B1764433
theorem B2090435 : Blo 1393516 2090435 := bstep (se 1 (by rfl) ⟨1567826, by rfl⟩ : syracuseStep 2090435 = 3135653) B3135653
theorem B1394115 : Blo 1393516 1394115 := bstep (se 1 (by rfl) ⟨1045586, by rfl⟩ : syracuseStep 1394115 = 2091173) B2091173
theorem B1394131 : Blo 1393516 1394131 := bstep (se 1 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 1394131 = 2091197) B2091197
theorem B2090465 : Blo 1393516 2090465 := bstep (se 2 (by rfl) ⟨783924, by rfl⟩ : syracuseStep 2090465 = 1567849) B1567849
theorem B2352611 : Blo 1393516 2352611 := bstep (se 1 (by rfl) ⟨1764458, by rfl⟩ : syracuseStep 2352611 = 3528917) B3528917
theorem B1394147 : Blo 1393516 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B6702563 : Blo 1393516 6702563 := bstep (se 1 (by rfl) ⟨5026922, by rfl⟩ : syracuseStep 6702563 = 10053845) B10053845
theorem B2090483 : Blo 1393516 2090483 := bstep (se 1 (by rfl) ⟨1567862, by rfl⟩ : syracuseStep 2090483 = 3135725) B3135725
theorem B1394163 : Blo 1393516 1394163 := bstep (se 1 (by rfl) ⟨1045622, by rfl⟩ : syracuseStep 1394163 = 2091245) B2091245
theorem B1394179 : Blo 1393516 1394179 := bstep (se 1 (by rfl) ⟨1045634, by rfl⟩ : syracuseStep 1394179 = 2091269) B2091269
theorem B2090513 : Blo 1393516 2090513 := bstep (se 2 (by rfl) ⟨783942, by rfl⟩ : syracuseStep 2090513 = 1567885) B1567885
theorem B1394195 : Blo 1393516 1394195 := bstep (se 1 (by rfl) ⟨1045646, by rfl⟩ : syracuseStep 1394195 = 2091293) B2091293
theorem B2090531 : Blo 1393516 2090531 := bstep (se 1 (by rfl) ⟨1567898, by rfl⟩ : syracuseStep 2090531 = 3135797) B3135797
theorem B1394211 : Blo 1393516 1394211 := bstep (se 1 (by rfl) ⟨1045658, by rfl⟩ : syracuseStep 1394211 = 2091317) B2091317
theorem B1394227 : Blo 1393516 1394227 := bstep (se 1 (by rfl) ⟨1045670, by rfl⟩ : syracuseStep 1394227 = 2091341) B2091341
theorem B2090561 : Blo 1393516 2090561 := bstep (se 2 (by rfl) ⟨783960, by rfl⟩ : syracuseStep 2090561 = 1567921) B1567921
theorem B1394243 : Blo 1393516 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B3532369 : Blo 1393516 3532369 := bstep (se 2 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 3532369 = 2649277) B2649277
theorem B2090579 : Blo 1393516 2090579 := bstep (se 1 (by rfl) ⟨1567934, by rfl⟩ : syracuseStep 2090579 = 3135869) B3135869
theorem B1394259 : Blo 1393516 1394259 := bstep (se 1 (by rfl) ⟨1045694, by rfl⟩ : syracuseStep 1394259 = 2091389) B2091389
theorem B2352739 : Blo 1393516 2352739 := bstep (se 1 (by rfl) ⟨1764554, by rfl⟩ : syracuseStep 2352739 = 3529109) B3529109
theorem B1394275 : Blo 1393516 1394275 := bstep (se 1 (by rfl) ⟨1045706, by rfl⟩ : syracuseStep 1394275 = 2091413) B2091413
theorem B2090609 : Blo 1393516 2090609 := bstep (se 2 (by rfl) ⟨783978, by rfl⟩ : syracuseStep 2090609 = 1567957) B1567957
theorem B1394291 : Blo 1393516 1394291 := bstep (se 1 (by rfl) ⟨1045718, by rfl⟩ : syracuseStep 1394291 = 2091437) B2091437
theorem B2090627 : Blo 1393516 2090627 := bstep (se 1 (by rfl) ⟨1567970, by rfl⟩ : syracuseStep 2090627 = 3135941) B3135941
theorem B1394307 : Blo 1393516 1394307 := bstep (se 1 (by rfl) ⟨1045730, by rfl⟩ : syracuseStep 1394307 = 2091461) B2091461
theorem B7538309 : Blo 1393516 7538309 := bstep (se 4 (by rfl) ⟨706716, by rfl⟩ : syracuseStep 7538309 = 1413433) B1413433
theorem B4703885 : Blo 1393516 4703885 := bstep (se 3 (by rfl) ⟨881978, by rfl⟩ : syracuseStep 4703885 = 1763957) B1763957
theorem B3139217 : Blo 1393516 3139217 := bstep (se 2 (by rfl) ⟨1177206, by rfl⟩ : syracuseStep 3139217 = 2354413) B2354413
theorem B1394323 : Blo 1393516 1394323 := bstep (se 1 (by rfl) ⟨1045742, by rfl⟩ : syracuseStep 1394323 = 2091485) B2091485
theorem B2090657 : Blo 1393516 2090657 := bstep (se 2 (by rfl) ⟨783996, by rfl⟩ : syracuseStep 2090657 = 1567993) B1567993
theorem B1394339 : Blo 1393516 1394339 := bstep (se 1 (by rfl) ⟨1045754, by rfl⟩ : syracuseStep 1394339 = 2091509) B2091509
theorem B3139235 : Blo 1393516 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B2090675 : Blo 1393516 2090675 := bstep (se 1 (by rfl) ⟨1568006, by rfl⟩ : syracuseStep 2090675 = 3136013) B3136013
theorem B1394355 : Blo 1393516 1394355 := bstep (se 1 (by rfl) ⟨1045766, by rfl⟩ : syracuseStep 1394355 = 2091533) B2091533
theorem B4703939 : Blo 1393516 4703939 := bstep (se 1 (by rfl) ⟨3527954, by rfl⟩ : syracuseStep 4703939 = 7055909) B7055909
theorem B1394371 : Blo 1393516 1394371 := bstep (se 1 (by rfl) ⟨1045778, by rfl⟩ : syracuseStep 1394371 = 2091557) B2091557
theorem B9537221 : Blo 1393516 9537221 := bstep (se 4 (by rfl) ⟨894114, by rfl⟩ : syracuseStep 9537221 = 1788229) B1788229
theorem B2090705 : Blo 1393516 2090705 := bstep (se 2 (by rfl) ⟨784014, by rfl⟩ : syracuseStep 2090705 = 1568029) B1568029
theorem B1394387 : Blo 1393516 1394387 := bstep (se 1 (by rfl) ⟨1045790, by rfl⟩ : syracuseStep 1394387 = 2091581) B2091581
theorem B2090723 : Blo 1393516 2090723 := bstep (se 1 (by rfl) ⟨1568042, by rfl⟩ : syracuseStep 2090723 = 3136085) B3136085
theorem B1394403 : Blo 1393516 1394403 := bstep (se 1 (by rfl) ⟨1045802, by rfl⟩ : syracuseStep 1394403 = 2091605) B2091605
theorem B2352881 : Blo 1393516 2352881 := bstep (se 2 (by rfl) ⟨882330, by rfl⟩ : syracuseStep 2352881 = 1764661) B1764661
theorem B4835057 : Blo 1393516 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1394419 : Blo 1393516 1394419 := bstep (se 1 (by rfl) ⟨1045814, by rfl⟩ : syracuseStep 1394419 = 2091629) B2091629
theorem B2090753 : Blo 1393516 2090753 := bstep (se 2 (by rfl) ⟨784032, by rfl⟩ : syracuseStep 2090753 = 1568065) B1568065
theorem B1394435 : Blo 1393516 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B5654285 : Blo 1393516 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B2090771 : Blo 1393516 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B1394451 : Blo 1393516 1394451 := bstep (se 1 (by rfl) ⟨1045838, by rfl⟩ : syracuseStep 1394451 = 2091677) B2091677
theorem B1394467 : Blo 1393516 1394467 := bstep (se 1 (by rfl) ⟨1045850, by rfl⟩ : syracuseStep 1394467 = 2091701) B2091701
theorem B2090801 : Blo 1393516 2090801 := bstep (se 2 (by rfl) ⟨784050, by rfl⟩ : syracuseStep 2090801 = 1568101) B1568101
theorem B1394483 : Blo 1393516 1394483 := bstep (se 1 (by rfl) ⟨1045862, by rfl⟩ : syracuseStep 1394483 = 2091725) B2091725
theorem B2090819 : Blo 1393516 2090819 := bstep (se 1 (by rfl) ⟨1568114, by rfl⟩ : syracuseStep 2090819 = 3136229) B3136229
theorem B1394499 : Blo 1393516 1394499 := bstep (se 1 (by rfl) ⟨1045874, by rfl⟩ : syracuseStep 1394499 = 2091749) B2091749
theorem B2828099 : Blo 1393516 2828099 := bstep (se 1 (by rfl) ⟨2121074, by rfl⟩ : syracuseStep 2828099 = 4242149) B4242149
theorem B1394515 : Blo 1393516 1394515 := bstep (se 1 (by rfl) ⟨1045886, by rfl⟩ : syracuseStep 1394515 = 2091773) B2091773
theorem B2090849 : Blo 1393516 2090849 := bstep (se 2 (by rfl) ⟨784068, by rfl⟩ : syracuseStep 2090849 = 1568137) B1568137
theorem B1394531 : Blo 1393516 1394531 := bstep (se 1 (by rfl) ⟨1045898, by rfl⟩ : syracuseStep 1394531 = 2091797) B2091797
theorem B5293937 : Blo 1393516 5293937 := bstep (se 2 (by rfl) ⟨1985226, by rfl⟩ : syracuseStep 5293937 = 3970453) B3970453
theorem B2353009 : Blo 1393516 2353009 := bstep (se 2 (by rfl) ⟨882378, by rfl⟩ : syracuseStep 2353009 = 1764757) B1764757
theorem B2090867 : Blo 1393516 2090867 := bstep (se 1 (by rfl) ⟨1568150, by rfl⟩ : syracuseStep 2090867 = 3136301) B3136301
theorem B1394547 : Blo 1393516 1394547 := bstep (se 1 (by rfl) ⟨1045910, by rfl⟩ : syracuseStep 1394547 = 2091821) B2091821
theorem B1394563 : Blo 1393516 1394563 := bstep (se 1 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 1394563 = 2091845) B2091845
theorem B2090897 : Blo 1393516 2090897 := bstep (se 2 (by rfl) ⟨784086, by rfl⟩ : syracuseStep 2090897 = 1568173) B1568173
theorem B2353043 : Blo 1393516 2353043 := bstep (se 1 (by rfl) ⟨1764782, by rfl⟩ : syracuseStep 2353043 = 3529565) B3529565
theorem B1394579 : Blo 1393516 1394579 := bstep (se 1 (by rfl) ⟨1045934, by rfl⟩ : syracuseStep 1394579 = 2091869) B2091869
theorem B2090915 : Blo 1393516 2090915 := bstep (se 1 (by rfl) ⟨1568186, by rfl⟩ : syracuseStep 2090915 = 3136373) B3136373
theorem B1394595 : Blo 1393516 1394595 := bstep (se 1 (by rfl) ⟨1045946, by rfl⟩ : syracuseStep 1394595 = 2091893) B2091893
theorem B3139505 : Blo 1393516 3139505 := bstep (se 2 (by rfl) ⟨1177314, by rfl⟩ : syracuseStep 3139505 = 2354629) B2354629
theorem B1394611 : Blo 1393516 1394611 := bstep (se 1 (by rfl) ⟨1045958, by rfl⟩ : syracuseStep 1394611 = 2091917) B2091917
theorem B2418611 : Blo 1393516 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B2090945 : Blo 1393516 2090945 := bstep (se 2 (by rfl) ⟨784104, by rfl⟩ : syracuseStep 2090945 = 1568209) B1568209
theorem B1394627 : Blo 1393516 1394627 := bstep (se 1 (by rfl) ⟨1045970, by rfl⟩ : syracuseStep 1394627 = 2091941) B2091941
theorem B3139523 : Blo 1393516 3139523 := bstep (se 1 (by rfl) ⟨2354642, by rfl⟩ : syracuseStep 3139523 = 4709285) B4709285
theorem B4704209 : Blo 1393516 4704209 := bstep (se 2 (by rfl) ⟨1764078, by rfl⟩ : syracuseStep 4704209 = 3528157) B3528157
theorem B2090963 : Blo 1393516 2090963 := bstep (se 1 (by rfl) ⟨1568222, by rfl⟩ : syracuseStep 2090963 = 3136445) B3136445
theorem B1394643 : Blo 1393516 1394643 := bstep (se 1 (by rfl) ⟨1045982, by rfl⟩ : syracuseStep 1394643 = 2091965) B2091965
theorem B1394659 : Blo 1393516 1394659 := bstep (se 1 (by rfl) ⟨1045994, by rfl⟩ : syracuseStep 1394659 = 2091989) B2091989
theorem B7063523 : Blo 1393516 7063523 := bstep (se 1 (by rfl) ⟨5297642, by rfl⟩ : syracuseStep 7063523 = 10595285) B10595285
theorem B2090993 : Blo 1393516 2090993 := bstep (se 2 (by rfl) ⟨784122, by rfl⟩ : syracuseStep 2090993 = 1568245) B1568245
theorem B1394675 : Blo 1393516 1394675 := bstep (se 1 (by rfl) ⟨1046006, by rfl⟩ : syracuseStep 1394675 = 2092013) B2092013
theorem B2091011 : Blo 1393516 2091011 := bstep (se 1 (by rfl) ⟨1568258, by rfl⟩ : syracuseStep 2091011 = 3136517) B3136517
theorem B1394691 : Blo 1393516 1394691 := bstep (se 1 (by rfl) ⟨1046018, by rfl⟩ : syracuseStep 1394691 = 2092037) B2092037
theorem B2353171 : Blo 1393516 2353171 := bstep (se 1 (by rfl) ⟨1764878, by rfl⟩ : syracuseStep 2353171 = 3529757) B3529757
theorem B1394707 : Blo 1393516 1394707 := bstep (se 1 (by rfl) ⟨1046030, by rfl⟩ : syracuseStep 1394707 = 2092061) B2092061
theorem B2091041 : Blo 1393516 2091041 := bstep (se 2 (by rfl) ⟨784140, by rfl⟩ : syracuseStep 2091041 = 1568281) B1568281
theorem B1394723 : Blo 1393516 1394723 := bstep (se 1 (by rfl) ⟨1046042, by rfl⟩ : syracuseStep 1394723 = 2092085) B2092085
theorem B2091059 : Blo 1393516 2091059 := bstep (se 1 (by rfl) ⟨1568294, by rfl⟩ : syracuseStep 2091059 = 3136589) B3136589
theorem B1394739 : Blo 1393516 1394739 := bstep (se 1 (by rfl) ⟨1046054, by rfl⟩ : syracuseStep 1394739 = 2092109) B2092109
theorem B1394755 : Blo 1393516 1394755 := bstep (se 1 (by rfl) ⟨1046066, by rfl⟩ : syracuseStep 1394755 = 2092133) B2092133
theorem B2091089 : Blo 1393516 2091089 := bstep (se 2 (by rfl) ⟨784158, by rfl⟩ : syracuseStep 2091089 = 1568317) B1568317
theorem B1394771 : Blo 1393516 1394771 := bstep (se 1 (by rfl) ⟨1046078, by rfl⟩ : syracuseStep 1394771 = 2092157) B2092157
theorem B2091107 : Blo 1393516 2091107 := bstep (se 1 (by rfl) ⟨1568330, by rfl⟩ : syracuseStep 2091107 = 3136661) B3136661
theorem B1394787 : Blo 1393516 1394787 := bstep (se 1 (by rfl) ⟨1046090, by rfl⟩ : syracuseStep 1394787 = 2092181) B2092181
theorem B1394803 : Blo 1393516 1394803 := bstep (se 1 (by rfl) ⟨1046102, by rfl⟩ : syracuseStep 1394803 = 2092205) B2092205
theorem B2091137 : Blo 1393516 2091137 := bstep (se 2 (by rfl) ⟨784176, by rfl⟩ : syracuseStep 2091137 = 1568353) B1568353
theorem B1394819 : Blo 1393516 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B1984657 : Blo 1393516 1984657 := bstep (se 2 (by rfl) ⟨744246, by rfl⟩ : syracuseStep 1984657 = 1488493) B1488493
theorem B2091155 : Blo 1393516 2091155 := bstep (se 1 (by rfl) ⟨1568366, by rfl⟩ : syracuseStep 2091155 = 3136733) B3136733
theorem B1394835 : Blo 1393516 1394835 := bstep (se 1 (by rfl) ⟨1046126, by rfl⟩ : syracuseStep 1394835 = 2092253) B2092253
theorem B2353313 : Blo 1393516 2353313 := bstep (se 2 (by rfl) ⟨882492, by rfl⟩ : syracuseStep 2353313 = 1764985) B1764985
theorem B1394851 : Blo 1393516 1394851 := bstep (se 1 (by rfl) ⟨1046138, by rfl⟩ : syracuseStep 1394851 = 2092277) B2092277
theorem B2091185 : Blo 1393516 2091185 := bstep (se 2 (by rfl) ⟨784194, by rfl⟩ : syracuseStep 2091185 = 1568389) B1568389
theorem B1394867 : Blo 1393516 1394867 := bstep (se 1 (by rfl) ⟨1046150, by rfl⟩ : syracuseStep 1394867 = 2092301) B2092301
theorem B2091203 : Blo 1393516 2091203 := bstep (se 1 (by rfl) ⟨1568402, by rfl⟩ : syracuseStep 2091203 = 3136805) B3136805
theorem B1394883 : Blo 1393516 1394883 := bstep (se 1 (by rfl) ⟨1046162, by rfl⟩ : syracuseStep 1394883 = 2092325) B2092325
theorem B3139793 : Blo 1393516 3139793 := bstep (se 2 (by rfl) ⟨1177422, by rfl⟩ : syracuseStep 3139793 = 2354845) B2354845
theorem B1394899 : Blo 1393516 1394899 := bstep (se 1 (by rfl) ⟨1046174, by rfl⟩ : syracuseStep 1394899 = 2092349) B2092349
theorem B2091233 : Blo 1393516 2091233 := bstep (se 2 (by rfl) ⟨784212, by rfl⟩ : syracuseStep 2091233 = 1568425) B1568425
theorem B1394915 : Blo 1393516 1394915 := bstep (se 1 (by rfl) ⟨1046186, by rfl⟩ : syracuseStep 1394915 = 2092373) B2092373
theorem B3139811 : Blo 1393516 3139811 := bstep (se 1 (by rfl) ⟨2354858, by rfl⟩ : syracuseStep 3139811 = 4709717) B4709717
theorem B2648305 : Blo 1393516 2648305 := bstep (se 2 (by rfl) ⟨993114, by rfl⟩ : syracuseStep 2648305 = 1986229) B1986229
theorem B2091251 : Blo 1393516 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B1394931 : Blo 1393516 1394931 := bstep (se 1 (by rfl) ⟨1046198, by rfl⟩ : syracuseStep 1394931 = 2092397) B2092397
theorem B1984771 : Blo 1393516 1984771 := bstep (se 1 (by rfl) ⟨1488578, by rfl⟩ : syracuseStep 1984771 = 2977157) B2977157
theorem B1394947 : Blo 1393516 1394947 := bstep (se 1 (by rfl) ⟨1046210, by rfl⟩ : syracuseStep 1394947 = 2092421) B2092421
theorem B2091281 : Blo 1393516 2091281 := bstep (se 2 (by rfl) ⟨784230, by rfl⟩ : syracuseStep 2091281 = 1568461) B1568461
theorem B1394963 : Blo 1393516 1394963 := bstep (se 1 (by rfl) ⟨1046222, by rfl⟩ : syracuseStep 1394963 = 2092445) B2092445
theorem B2353441 : Blo 1393516 2353441 := bstep (se 2 (by rfl) ⟨882540, by rfl⟩ : syracuseStep 2353441 = 1765081) B1765081
theorem B2091299 : Blo 1393516 2091299 := bstep (se 1 (by rfl) ⟨1568474, by rfl⟩ : syracuseStep 2091299 = 3136949) B3136949
theorem B1394979 : Blo 1393516 1394979 := bstep (se 1 (by rfl) ⟨1046234, by rfl⟩ : syracuseStep 1394979 = 2092469) B2092469
theorem B1394995 : Blo 1393516 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B2091329 : Blo 1393516 2091329 := bstep (se 2 (by rfl) ⟨784248, by rfl⟩ : syracuseStep 2091329 = 1568497) B1568497
theorem B2353475 : Blo 1393516 2353475 := bstep (se 1 (by rfl) ⟨1765106, by rfl⟩ : syracuseStep 2353475 = 3530213) B3530213
theorem B1395011 : Blo 1393516 1395011 := bstep (se 1 (by rfl) ⟨1046258, by rfl⟩ : syracuseStep 1395011 = 2092517) B2092517
theorem B7940429 : Blo 1393516 7940429 := bstep (se 3 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 7940429 = 2977661) B2977661
theorem B2091347 : Blo 1393516 2091347 := bstep (se 1 (by rfl) ⟨1568510, by rfl⟩ : syracuseStep 2091347 = 3137021) B3137021
theorem B1395027 : Blo 1393516 1395027 := bstep (se 1 (by rfl) ⟨1046270, by rfl⟩ : syracuseStep 1395027 = 2092541) B2092541
theorem B1395043 : Blo 1393516 1395043 := bstep (se 1 (by rfl) ⟨1046282, by rfl⟩ : syracuseStep 1395043 = 2092565) B2092565
theorem B2091377 : Blo 1393516 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B1395059 : Blo 1393516 1395059 := bstep (se 1 (by rfl) ⟨1046294, by rfl⟩ : syracuseStep 1395059 = 2092589) B2092589
theorem B2091395 : Blo 1393516 2091395 := bstep (se 1 (by rfl) ⟨1568546, by rfl⟩ : syracuseStep 2091395 = 3137093) B3137093
theorem B1395075 : Blo 1393516 1395075 := bstep (se 1 (by rfl) ⟨1046306, by rfl⟩ : syracuseStep 1395075 = 2092613) B2092613
theorem B1395091 : Blo 1393516 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B2091425 : Blo 1393516 2091425 := bstep (se 2 (by rfl) ⟨784284, by rfl⟩ : syracuseStep 2091425 = 1568569) B1568569
theorem B1395107 : Blo 1393516 1395107 := bstep (se 1 (by rfl) ⟨1046330, by rfl⟩ : syracuseStep 1395107 = 2092661) B2092661
theorem B2091443 : Blo 1393516 2091443 := bstep (se 1 (by rfl) ⟨1568582, by rfl⟩ : syracuseStep 2091443 = 3137165) B3137165
theorem B1395123 : Blo 1393516 1395123 := bstep (se 1 (by rfl) ⟨1046342, by rfl⟩ : syracuseStep 1395123 = 2092685) B2092685
theorem B2353603 : Blo 1393516 2353603 := bstep (se 1 (by rfl) ⟨1765202, by rfl⟩ : syracuseStep 2353603 = 3530405) B3530405
theorem B1395139 : Blo 1393516 1395139 := bstep (se 1 (by rfl) ⟨1046354, by rfl⟩ : syracuseStep 1395139 = 2092709) B2092709
theorem B2091473 : Blo 1393516 2091473 := bstep (se 2 (by rfl) ⟨784302, by rfl⟩ : syracuseStep 2091473 = 1568605) B1568605
theorem B1763795 : Blo 1393516 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1395155 : Blo 1393516 1395155 := bstep (se 1 (by rfl) ⟨1046366, by rfl⟩ : syracuseStep 1395155 = 2092733) B2092733
theorem B2091491 : Blo 1393516 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B1395171 : Blo 1393516 1395171 := bstep (se 1 (by rfl) ⟨1046378, by rfl⟩ : syracuseStep 1395171 = 2092757) B2092757
theorem B4704749 : Blo 1393516 4704749 := bstep (se 3 (by rfl) ⟨882140, by rfl⟩ : syracuseStep 4704749 = 1764281) B1764281
theorem B1395187 : Blo 1393516 1395187 := bstep (se 1 (by rfl) ⟨1046390, by rfl⟩ : syracuseStep 1395187 = 2092781) B2092781
theorem B2091521 : Blo 1393516 2091521 := bstep (se 2 (by rfl) ⟨784320, by rfl⟩ : syracuseStep 2091521 = 1568641) B1568641
theorem B1395203 : Blo 1393516 1395203 := bstep (se 1 (by rfl) ⟨1046402, by rfl⟩ : syracuseStep 1395203 = 2092805) B2092805
theorem B5294605 : Blo 1393516 5294605 := bstep (se 3 (by rfl) ⟨992738, by rfl⟩ : syracuseStep 5294605 = 1985477) B1985477
theorem B4237841 : Blo 1393516 4237841 := bstep (se 2 (by rfl) ⟨1589190, by rfl⟩ : syracuseStep 4237841 = 3178381) B3178381
theorem B2091539 : Blo 1393516 2091539 := bstep (se 1 (by rfl) ⟨1568654, by rfl⟩ : syracuseStep 2091539 = 3137309) B3137309
theorem B1395219 : Blo 1393516 1395219 := bstep (se 1 (by rfl) ⟨1046414, by rfl⟩ : syracuseStep 1395219 = 2092829) B2092829
theorem B4704803 : Blo 1393516 4704803 := bstep (se 1 (by rfl) ⟨3528602, by rfl⟩ : syracuseStep 4704803 = 7057205) B7057205
theorem B1395235 : Blo 1393516 1395235 := bstep (se 1 (by rfl) ⟨1046426, by rfl⟩ : syracuseStep 1395235 = 2092853) B2092853
theorem B2091569 : Blo 1393516 2091569 := bstep (se 2 (by rfl) ⟨784338, by rfl⟩ : syracuseStep 2091569 = 1568677) B1568677
theorem B1395251 : Blo 1393516 1395251 := bstep (se 1 (by rfl) ⟨1046438, by rfl⟩ : syracuseStep 1395251 = 2092877) B2092877
theorem B2091587 : Blo 1393516 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B1395267 : Blo 1393516 1395267 := bstep (se 1 (by rfl) ⟨1046450, by rfl⟩ : syracuseStep 1395267 = 2092901) B2092901
theorem B2353745 : Blo 1393516 2353745 := bstep (se 2 (by rfl) ⟨882654, by rfl⟩ : syracuseStep 2353745 = 1765309) B1765309
theorem B1395283 : Blo 1393516 1395283 := bstep (se 1 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 1395283 = 2092925) B2092925
theorem B2091617 : Blo 1393516 2091617 := bstep (se 2 (by rfl) ⟨784356, by rfl⟩ : syracuseStep 2091617 = 1568713) B1568713
theorem B1395299 : Blo 1393516 1395299 := bstep (se 1 (by rfl) ⟨1046474, by rfl⟩ : syracuseStep 1395299 = 2092949) B2092949
theorem B2091635 : Blo 1393516 2091635 := bstep (se 1 (by rfl) ⟨1568726, by rfl⟩ : syracuseStep 2091635 = 3137453) B3137453
theorem B1395315 : Blo 1393516 1395315 := bstep (se 1 (by rfl) ⟨1046486, by rfl⟩ : syracuseStep 1395315 = 2092973) B2092973
theorem B1395331 : Blo 1393516 1395331 := bstep (se 1 (by rfl) ⟨1046498, by rfl⟩ : syracuseStep 1395331 = 2092997) B2092997
theorem B2091665 : Blo 1393516 2091665 := bstep (se 2 (by rfl) ⟨784374, by rfl⟩ : syracuseStep 2091665 = 1568749) B1568749
theorem B1395347 : Blo 1393516 1395347 := bstep (se 1 (by rfl) ⟨1046510, by rfl⟩ : syracuseStep 1395347 = 2093021) B2093021
theorem B2091683 : Blo 1393516 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B1395363 : Blo 1393516 1395363 := bstep (se 1 (by rfl) ⟨1046522, by rfl⟩ : syracuseStep 1395363 = 2093045) B2093045
theorem B6703793 : Blo 1393516 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B1395379 : Blo 1393516 1395379 := bstep (se 1 (by rfl) ⟨1046534, by rfl⟩ : syracuseStep 1395379 = 2093069) B2093069
theorem B2091713 : Blo 1393516 2091713 := bstep (se 2 (by rfl) ⟨784392, by rfl⟩ : syracuseStep 2091713 = 1568785) B1568785
theorem B1395395 : Blo 1393516 1395395 := bstep (se 1 (by rfl) ⟨1046546, by rfl⟩ : syracuseStep 1395395 = 2093093) B2093093
theorem B2353873 : Blo 1393516 2353873 := bstep (se 2 (by rfl) ⟨882702, by rfl⟩ : syracuseStep 2353873 = 1765405) B1765405
theorem B2091731 : Blo 1393516 2091731 := bstep (se 1 (by rfl) ⟨1568798, by rfl⟩ : syracuseStep 2091731 = 3137597) B3137597
theorem B1395411 : Blo 1393516 1395411 := bstep (se 1 (by rfl) ⟨1046558, by rfl⟩ : syracuseStep 1395411 = 2093117) B2093117
theorem B1395427 : Blo 1393516 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B2755313 : Blo 1393516 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2091761 : Blo 1393516 2091761 := bstep (se 2 (by rfl) ⟨784410, by rfl⟩ : syracuseStep 2091761 = 1568821) B1568821
theorem B2353907 : Blo 1393516 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B3771121 : Blo 1393516 3771121 := bstep (se 2 (by rfl) ⟨1414170, by rfl⟩ : syracuseStep 3771121 = 2828341) B2828341
theorem B1395443 : Blo 1393516 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B2091779 : Blo 1393516 2091779 := bstep (se 1 (by rfl) ⟨1568834, by rfl⟩ : syracuseStep 2091779 = 3137669) B3137669
theorem B1395459 : Blo 1393516 1395459 := bstep (se 1 (by rfl) ⟨1046594, by rfl⟩ : syracuseStep 1395459 = 2093189) B2093189
theorem B7064333 : Blo 1393516 7064333 := bstep (se 3 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 7064333 = 2649125) B2649125
theorem B1395475 : Blo 1393516 1395475 := bstep (se 1 (by rfl) ⟨1046606, by rfl⟩ : syracuseStep 1395475 = 2093213) B2093213
theorem B2091809 : Blo 1393516 2091809 := bstep (se 2 (by rfl) ⟨784428, by rfl⟩ : syracuseStep 2091809 = 1568857) B1568857
theorem B1395491 : Blo 1393516 1395491 := bstep (se 1 (by rfl) ⟨1046618, by rfl⟩ : syracuseStep 1395491 = 2093237) B2093237
theorem B4705073 : Blo 1393516 4705073 := bstep (se 2 (by rfl) ⟨1764402, by rfl⟩ : syracuseStep 4705073 = 3528805) B3528805
theorem B2091827 : Blo 1393516 2091827 := bstep (se 1 (by rfl) ⟨1568870, by rfl⟩ : syracuseStep 2091827 = 3137741) B3137741
theorem B1395507 : Blo 1393516 1395507 := bstep (se 1 (by rfl) ⟨1046630, by rfl⟩ : syracuseStep 1395507 = 2093261) B2093261
theorem B8940365 : Blo 1393516 8940365 := bstep (se 3 (by rfl) ⟨1676318, by rfl⟩ : syracuseStep 8940365 = 3352637) B3352637
theorem B2091857 : Blo 1393516 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B2091875 : Blo 1393516 2091875 := bstep (se 1 (by rfl) ⟨1568906, by rfl⟩ : syracuseStep 2091875 = 3137813) B3137813
theorem B2354035 : Blo 1393516 2354035 := bstep (se 1 (by rfl) ⟨1765526, by rfl⟩ : syracuseStep 2354035 = 3531053) B3531053
theorem B2091905 : Blo 1393516 2091905 := bstep (se 2 (by rfl) ⟨784464, by rfl⟩ : syracuseStep 2091905 = 1568929) B1568929
theorem B2091923 : Blo 1393516 2091923 := bstep (se 1 (by rfl) ⟨1568942, by rfl⟩ : syracuseStep 2091923 = 3137885) B3137885
theorem B4025251 : Blo 1393516 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B2091953 : Blo 1393516 2091953 := bstep (se 2 (by rfl) ⟨784482, by rfl⟩ : syracuseStep 2091953 = 1568965) B1568965
theorem B2091971 : Blo 1393516 2091971 := bstep (se 1 (by rfl) ⟨1568978, by rfl⟩ : syracuseStep 2091971 = 3137957) B3137957
theorem B2092001 : Blo 1393516 2092001 := bstep (se 2 (by rfl) ⟨784500, by rfl⟩ : syracuseStep 2092001 = 1569001) B1569001
theorem B2092019 : Blo 1393516 2092019 := bstep (se 1 (by rfl) ⟨1569014, by rfl⟩ : syracuseStep 2092019 = 3138029) B3138029
theorem B2354177 : Blo 1393516 2354177 := bstep (se 2 (by rfl) ⟨882816, by rfl⟩ : syracuseStep 2354177 = 1765633) B1765633
theorem B2092049 : Blo 1393516 2092049 := bstep (se 2 (by rfl) ⟨784518, by rfl⟩ : syracuseStep 2092049 = 1569037) B1569037
theorem B2092067 : Blo 1393516 2092067 := bstep (se 1 (by rfl) ⟨1569050, by rfl⟩ : syracuseStep 2092067 = 3138101) B3138101
theorem B4467761 : Blo 1393516 4467761 := bstep (se 2 (by rfl) ⟨1675410, by rfl⟩ : syracuseStep 4467761 = 3350821) B3350821
theorem B8940593 : Blo 1393516 8940593 := bstep (se 2 (by rfl) ⟨3352722, by rfl⟩ : syracuseStep 8940593 = 6705445) B6705445
theorem B1567795 : Blo 1393516 1567795 := bstep (se 1 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 1567795 = 2351693) B2351693
theorem B2092097 : Blo 1393516 2092097 := bstep (se 2 (by rfl) ⟨784536, by rfl⟩ : syracuseStep 2092097 = 1569073) B1569073
theorem B2387009 : Blo 1393516 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B2092115 : Blo 1393516 2092115 := bstep (se 1 (by rfl) ⟨1569086, by rfl⟩ : syracuseStep 2092115 = 3138173) B3138173
theorem B5958755 : Blo 1393516 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B2092145 : Blo 1393516 2092145 := bstep (se 2 (by rfl) ⟨784554, by rfl⟩ : syracuseStep 2092145 = 1569109) B1569109
theorem B2354305 : Blo 1393516 2354305 := bstep (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) B1765729
theorem B2092163 : Blo 1393516 2092163 := bstep (se 1 (by rfl) ⟨1569122, by rfl⟩ : syracuseStep 2092163 = 3138245) B3138245
theorem B1764499 : Blo 1393516 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B2092193 : Blo 1393516 2092193 := bstep (se 2 (by rfl) ⟨784572, by rfl⟩ : syracuseStep 2092193 = 1569145) B1569145
theorem B2354339 : Blo 1393516 2354339 := bstep (se 1 (by rfl) ⟨1765754, by rfl⟩ : syracuseStep 2354339 = 3531509) B3531509
theorem B4238513 : Blo 1393516 4238513 := bstep (se 2 (by rfl) ⟨1589442, by rfl⟩ : syracuseStep 4238513 = 3178885) B3178885
theorem B2092211 : Blo 1393516 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B1567939 : Blo 1393516 1567939 := bstep (se 1 (by rfl) ⟨1175954, by rfl⟩ : syracuseStep 1567939 = 2351909) B2351909
theorem B2092241 : Blo 1393516 2092241 := bstep (se 2 (by rfl) ⟨784590, by rfl⟩ : syracuseStep 2092241 = 1569181) B1569181
theorem B2092259 : Blo 1393516 2092259 := bstep (se 1 (by rfl) ⟨1569194, by rfl⟩ : syracuseStep 2092259 = 3138389) B3138389
theorem B7941361 : Blo 1393516 7941361 := bstep (se 2 (by rfl) ⟨2978010, by rfl⟩ : syracuseStep 7941361 = 5956021) B5956021
theorem B1764595 : Blo 1393516 1764595 := bstep (se 1 (by rfl) ⟨1323446, by rfl⟩ : syracuseStep 1764595 = 2646893) B2646893
theorem B2092289 : Blo 1393516 2092289 := bstep (se 2 (by rfl) ⟨784608, by rfl⟩ : syracuseStep 2092289 = 1569217) B1569217
theorem B2092307 : Blo 1393516 2092307 := bstep (se 1 (by rfl) ⟨1569230, by rfl⟩ : syracuseStep 2092307 = 3138461) B3138461
theorem B3018019 : Blo 1393516 3018019 := bstep (se 1 (by rfl) ⟨2263514, by rfl⟩ : syracuseStep 3018019 = 4527029) B4527029
theorem B5295395 : Blo 1393516 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B2354467 : Blo 1393516 2354467 := bstep (se 1 (by rfl) ⟨1765850, by rfl⟩ : syracuseStep 2354467 = 3531701) B3531701
theorem B2092337 : Blo 1393516 2092337 := bstep (se 2 (by rfl) ⟨784626, by rfl⟩ : syracuseStep 2092337 = 1569253) B1569253
theorem B2092355 : Blo 1393516 2092355 := bstep (se 1 (by rfl) ⟨1569266, by rfl⟩ : syracuseStep 2092355 = 3138533) B3138533
theorem B4705613 : Blo 1393516 4705613 := bstep (se 3 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 4705613 = 1764605) B1764605
theorem B1568083 : Blo 1393516 1568083 := bstep (se 1 (by rfl) ⟨1176062, by rfl⟩ : syracuseStep 1568083 = 2352125) B2352125
theorem B2092385 : Blo 1393516 2092385 := bstep (se 2 (by rfl) ⟨784644, by rfl⟩ : syracuseStep 2092385 = 1569289) B1569289
theorem B2092403 : Blo 1393516 2092403 := bstep (se 1 (by rfl) ⟨1569302, by rfl⟩ : syracuseStep 2092403 = 3138605) B3138605
theorem B4705667 : Blo 1393516 4705667 := bstep (se 1 (by rfl) ⟨3529250, by rfl⟩ : syracuseStep 4705667 = 7058501) B7058501
theorem B2092433 : Blo 1393516 2092433 := bstep (se 2 (by rfl) ⟨784662, by rfl⟩ : syracuseStep 2092433 = 1569325) B1569325
theorem B2092451 : Blo 1393516 2092451 := bstep (se 1 (by rfl) ⟨1569338, by rfl⟩ : syracuseStep 2092451 = 3138677) B3138677
theorem B2354609 : Blo 1393516 2354609 := bstep (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) B1765957
theorem B2092481 : Blo 1393516 2092481 := bstep (se 2 (by rfl) ⟨784680, by rfl⟩ : syracuseStep 2092481 = 1569361) B1569361
theorem B2092499 : Blo 1393516 2092499 := bstep (se 1 (by rfl) ⟨1569374, by rfl⟩ : syracuseStep 2092499 = 3138749) B3138749
theorem B1568227 : Blo 1393516 1568227 := bstep (se 1 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 1568227 = 2352341) B2352341
theorem B7056881 : Blo 1393516 7056881 := bstep (se 2 (by rfl) ⟨2646330, by rfl⟩ : syracuseStep 7056881 = 5292661) B5292661
theorem B2092529 : Blo 1393516 2092529 := bstep (se 2 (by rfl) ⟨784698, by rfl⟩ : syracuseStep 2092529 = 1569397) B1569397
theorem B2092547 : Blo 1393516 2092547 := bstep (se 1 (by rfl) ⟨1569410, by rfl⟩ : syracuseStep 2092547 = 3138821) B3138821
theorem B2092577 : Blo 1393516 2092577 := bstep (se 2 (by rfl) ⟨784716, by rfl⟩ : syracuseStep 2092577 = 1569433) B1569433
theorem B2354737 : Blo 1393516 2354737 := bstep (se 2 (by rfl) ⟨883026, by rfl⟩ : syracuseStep 2354737 = 1766053) B1766053
theorem B2092595 : Blo 1393516 2092595 := bstep (se 1 (by rfl) ⟨1569446, by rfl⟩ : syracuseStep 2092595 = 3138893) B3138893
theorem B1986115 : Blo 1393516 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B2092625 : Blo 1393516 2092625 := bstep (se 2 (by rfl) ⟨784734, by rfl⟩ : syracuseStep 2092625 = 1569469) B1569469
theorem B2354771 : Blo 1393516 2354771 := bstep (se 1 (by rfl) ⟨1766078, by rfl⟩ : syracuseStep 2354771 = 3532157) B3532157
theorem B2092643 : Blo 1393516 2092643 := bstep (se 1 (by rfl) ⟨1569482, by rfl⟩ : syracuseStep 2092643 = 3138965) B3138965
theorem B4836977 : Blo 1393516 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B1568371 : Blo 1393516 1568371 := bstep (se 1 (by rfl) ⟨1176278, by rfl⟩ : syracuseStep 1568371 = 2352557) B2352557
theorem B2092673 : Blo 1393516 2092673 := bstep (se 2 (by rfl) ⟨784752, by rfl⟩ : syracuseStep 2092673 = 1569505) B1569505
theorem B4705937 : Blo 1393516 4705937 := bstep (se 2 (by rfl) ⟨1764726, by rfl⟩ : syracuseStep 4705937 = 3529453) B3529453
theorem B2092691 : Blo 1393516 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B2092721 : Blo 1393516 2092721 := bstep (se 2 (by rfl) ⟨784770, by rfl⟩ : syracuseStep 2092721 = 1569541) B1569541
theorem B2092739 : Blo 1393516 2092739 := bstep (se 1 (by rfl) ⟨1569554, by rfl⟩ : syracuseStep 2092739 = 3139109) B3139109
theorem B2354899 : Blo 1393516 2354899 := bstep (se 1 (by rfl) ⟨1766174, by rfl⟩ : syracuseStep 2354899 = 3532349) B3532349
theorem B2092769 : Blo 1393516 2092769 := bstep (se 2 (by rfl) ⟨784788, by rfl⟩ : syracuseStep 2092769 = 1569577) B1569577
theorem B1765091 : Blo 1393516 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B4468451 : Blo 1393516 4468451 := bstep (se 1 (by rfl) ⟨3351338, by rfl⟩ : syracuseStep 4468451 = 6702677) B6702677
theorem B2092787 : Blo 1393516 2092787 := bstep (se 1 (by rfl) ⟨1569590, by rfl⟩ : syracuseStep 2092787 = 3139181) B3139181
theorem B1568515 : Blo 1393516 1568515 := bstep (se 1 (by rfl) ⟨1176386, by rfl⟩ : syracuseStep 1568515 = 2352773) B2352773
theorem B2092817 : Blo 1393516 2092817 := bstep (se 2 (by rfl) ⟨784806, by rfl⟩ : syracuseStep 2092817 = 1569613) B1569613
theorem B2092835 : Blo 1393516 2092835 := bstep (se 1 (by rfl) ⟨1569626, by rfl⟩ : syracuseStep 2092835 = 3139253) B3139253
theorem B3968813 : Blo 1393516 3968813 := bstep (se 3 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 3968813 = 1488305) B1488305
theorem B2092865 : Blo 1393516 2092865 := bstep (se 2 (by rfl) ⟨784824, by rfl⟩ : syracuseStep 2092865 = 1569649) B1569649
theorem B2092883 : Blo 1393516 2092883 := bstep (se 1 (by rfl) ⟨1569662, by rfl⟩ : syracuseStep 2092883 = 3139325) B3139325
theorem B2092913 : Blo 1393516 2092913 := bstep (se 2 (by rfl) ⟨784842, by rfl⟩ : syracuseStep 2092913 = 1569685) B1569685
theorem B23842673 : Blo 1393516 23842673 := bstep (se 2 (by rfl) ⟨8941002, by rfl⟩ : syracuseStep 23842673 = 17882005) B17882005
theorem B2092931 : Blo 1393516 2092931 := bstep (se 1 (by rfl) ⟨1569698, by rfl⟩ : syracuseStep 2092931 = 3139397) B3139397
theorem B1568659 : Blo 1393516 1568659 := bstep (se 1 (by rfl) ⟨1176494, by rfl⟩ : syracuseStep 1568659 = 2352989) B2352989
theorem B2092961 : Blo 1393516 2092961 := bstep (se 2 (by rfl) ⟨784860, by rfl⟩ : syracuseStep 2092961 = 1569721) B1569721
theorem B2232227 : Blo 1393516 2232227 := bstep (se 1 (by rfl) ⟨1674170, by rfl⟩ : syracuseStep 2232227 = 3348341) B3348341
theorem B5296049 : Blo 1393516 5296049 := bstep (se 2 (by rfl) ⟨1986018, by rfl⟩ : syracuseStep 5296049 = 3972037) B3972037
theorem B2092979 : Blo 1393516 2092979 := bstep (se 1 (by rfl) ⟨1569734, by rfl⟩ : syracuseStep 2092979 = 3139469) B3139469
theorem B67858373 : Blo 1393516 67858373 := bstep (se 4 (by rfl) ⟨6361722, by rfl⟩ : syracuseStep 67858373 = 12723445) B12723445
theorem B2093009 : Blo 1393516 2093009 := bstep (se 2 (by rfl) ⟨784878, by rfl⟩ : syracuseStep 2093009 = 1569757) B1569757
theorem B3968995 : Blo 1393516 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B2093027 : Blo 1393516 2093027 := bstep (se 1 (by rfl) ⟨1569770, by rfl⟩ : syracuseStep 2093027 = 3139541) B3139541
theorem B14307313 : Blo 1393516 14307313 := bstep (se 2 (by rfl) ⟨5365242, by rfl⟩ : syracuseStep 14307313 = 10730485) B10730485
theorem B6705137 : Blo 1393516 6705137 := bstep (se 2 (by rfl) ⟨2514426, by rfl⟩ : syracuseStep 6705137 = 5028853) B5028853
theorem B2093057 : Blo 1393516 2093057 := bstep (se 2 (by rfl) ⟨784896, by rfl⟩ : syracuseStep 2093057 = 1569793) B1569793
theorem B2093075 : Blo 1393516 2093075 := bstep (se 1 (by rfl) ⟨1569806, by rfl⟩ : syracuseStep 2093075 = 3139613) B3139613
theorem B2232355 : Blo 1393516 2232355 := bstep (se 1 (by rfl) ⟨1674266, by rfl⟩ : syracuseStep 2232355 = 3348533) B3348533
theorem B3575843 : Blo 1393516 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B1568803 : Blo 1393516 1568803 := bstep (se 1 (by rfl) ⟨1176602, by rfl⟩ : syracuseStep 1568803 = 2353205) B2353205
theorem B2093105 : Blo 1393516 2093105 := bstep (se 2 (by rfl) ⟨784914, by rfl⟩ : syracuseStep 2093105 = 1569829) B1569829
theorem B2093123 : Blo 1393516 2093123 := bstep (se 1 (by rfl) ⟨1569842, by rfl⟩ : syracuseStep 2093123 = 3139685) B3139685
theorem B10047557 : Blo 1393516 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B2093153 : Blo 1393516 2093153 := bstep (se 2 (by rfl) ⟨784932, by rfl⟩ : syracuseStep 2093153 = 1569865) B1569865
theorem B2093171 : Blo 1393516 2093171 := bstep (se 1 (by rfl) ⟨1569878, by rfl⟩ : syracuseStep 2093171 = 3139757) B3139757
theorem B3969155 : Blo 1393516 3969155 := bstep (se 1 (by rfl) ⟨2976866, by rfl⟩ : syracuseStep 3969155 = 5953733) B5953733
theorem B2093201 : Blo 1393516 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B5091491 : Blo 1393516 5091491 := bstep (se 1 (by rfl) ⟨3818618, by rfl⟩ : syracuseStep 5091491 = 7637237) B7637237
theorem B2093219 : Blo 1393516 2093219 := bstep (se 1 (by rfl) ⟨1569914, by rfl⟩ : syracuseStep 2093219 = 3139829) B3139829
theorem B4706477 : Blo 1393516 4706477 := bstep (se 3 (by rfl) ⟨882464, by rfl⟩ : syracuseStep 4706477 = 1764929) B1764929
theorem B2232497 : Blo 1393516 2232497 := bstep (se 2 (by rfl) ⟨837186, by rfl⟩ : syracuseStep 2232497 = 1674373) B1674373
theorem B1568947 : Blo 1393516 1568947 := bstep (se 1 (by rfl) ⟨1176710, by rfl⟩ : syracuseStep 1568947 = 2353421) B2353421
theorem B2093249 : Blo 1393516 2093249 := bstep (se 2 (by rfl) ⟨784968, by rfl⟩ : syracuseStep 2093249 = 1569937) B1569937
theorem B2093267 : Blo 1393516 2093267 := bstep (se 1 (by rfl) ⟨1569950, by rfl⟩ : syracuseStep 2093267 = 3139901) B3139901
theorem B4706531 : Blo 1393516 4706531 := bstep (se 1 (by rfl) ⟨3529898, by rfl⟩ : syracuseStep 4706531 = 7059797) B7059797
theorem B67883285 : Blo 1393516 67883285 := bstep (se 6 (by rfl) ⟨1591014, by rfl⟩ : syracuseStep 67883285 = 3182029) B3182029
theorem B1569091 : Blo 1393516 1569091 := bstep (se 1 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 1569091 = 2353637) B2353637
theorem B1675603 : Blo 1393516 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B1765795 : Blo 1393516 1765795 := bstep (se 1 (by rfl) ⟨1324346, by rfl⟩ : syracuseStep 1765795 = 2648693) B2648693
theorem B2232785 : Blo 1393516 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B1569235 : Blo 1393516 1569235 := bstep (se 1 (by rfl) ⟨1176926, by rfl⟩ : syracuseStep 1569235 = 2353853) B2353853
theorem B4706801 : Blo 1393516 4706801 := bstep (se 2 (by rfl) ⟨1765050, by rfl⟩ : syracuseStep 4706801 = 3530101) B3530101
theorem B1765891 : Blo 1393516 1765891 := bstep (se 1 (by rfl) ⟨1324418, by rfl⟩ : syracuseStep 1765891 = 2648837) B2648837
theorem B1675795 : Blo 1393516 1675795 := bstep (se 1 (by rfl) ⟨1256846, by rfl⟩ : syracuseStep 1675795 = 2513693) B2513693
theorem B1569379 : Blo 1393516 1569379 := bstep (se 1 (by rfl) ⟨1177034, by rfl⟩ : syracuseStep 1569379 = 2354069) B2354069
theorem B7942819 : Blo 1393516 7942819 := bstep (se 1 (by rfl) ⟨5957114, by rfl⟩ : syracuseStep 7942819 = 11914229) B11914229
theorem B1569523 : Blo 1393516 1569523 := bstep (se 1 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 1569523 = 2354285) B2354285
theorem B3527459 : Blo 1393516 3527459 := bstep (se 1 (by rfl) ⟨2645594, by rfl⟩ : syracuseStep 3527459 = 5291189) B5291189
theorem B30143285 : Blo 1393516 30143285 := bstep (se 5 (by rfl) ⟨1412966, by rfl⟩ : syracuseStep 30143285 = 2825933) B2825933
theorem B15078257 : Blo 1393516 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B1569667 : Blo 1393516 1569667 := bstep (se 1 (by rfl) ⟨1177250, by rfl⟩ : syracuseStep 1569667 = 2354501) B2354501
theorem B7058339 : Blo 1393516 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B3527651 : Blo 1393516 3527651 := bstep (se 1 (by rfl) ⟨2645738, by rfl⟩ : syracuseStep 3527651 = 5291477) B5291477
theorem B4707341 : Blo 1393516 4707341 := bstep (se 3 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 4707341 = 1765253) B1765253
theorem B1569811 : Blo 1393516 1569811 := bstep (se 1 (by rfl) ⟨1177358, by rfl⟩ : syracuseStep 1569811 = 2354717) B2354717
theorem B1676323 : Blo 1393516 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B4707395 : Blo 1393516 4707395 := bstep (se 1 (by rfl) ⟨3530546, by rfl⟩ : syracuseStep 4707395 = 7061093) B7061093
theorem B1676419 : Blo 1393516 1676419 := bstep (se 1 (by rfl) ⟨1257314, by rfl⟩ : syracuseStep 1676419 = 2514629) B2514629
theorem B1569955 : Blo 1393516 1569955 := bstep (se 1 (by rfl) ⟨1177466, by rfl⟩ : syracuseStep 1569955 = 2354933) B2354933
theorem B3970225 : Blo 1393516 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B7943345 : Blo 1393516 7943345 := bstep (se 2 (by rfl) ⟨2978754, by rfl⟩ : syracuseStep 7943345 = 5957509) B5957509
theorem B4527341 : Blo 1393516 4527341 := bstep (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) B1697753
theorem B2233585 : Blo 1393516 2233585 := bstep (se 2 (by rfl) ⟨837594, by rfl⟩ : syracuseStep 2233585 = 1675189) B1675189
theorem B10589453 : Blo 1393516 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B2979139 : Blo 1393516 2979139 := bstep (se 1 (by rfl) ⟨2234354, by rfl⟩ : syracuseStep 2979139 = 4468709) B4468709
theorem B4707665 : Blo 1393516 4707665 := bstep (se 2 (by rfl) ⟨1765374, by rfl⟩ : syracuseStep 4707665 = 3530749) B3530749
theorem B5297507 : Blo 1393516 5297507 := bstep (se 1 (by rfl) ⟨3973130, by rfl⟩ : syracuseStep 5297507 = 7946261) B7946261
theorem B5297521 : Blo 1393516 5297521 := bstep (se 2 (by rfl) ⟨1986570, by rfl⟩ : syracuseStep 5297521 = 3973141) B3973141
theorem B4470221 : Blo 1393516 4470221 := bstep (se 3 (by rfl) ⟨838166, by rfl⟩ : syracuseStep 4470221 = 1676333) B1676333
theorem B4470349 : Blo 1393516 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B12719729 : Blo 1393516 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B7059149 : Blo 1393516 7059149 := bstep (se 3 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 7059149 = 2647181) B2647181
theorem B8165069 : Blo 1393516 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B4470605 : Blo 1393516 4470605 := bstep (se 3 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 4470605 = 1676477) B1676477
theorem B4708205 : Blo 1393516 4708205 := bstep (se 3 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 4708205 = 1765577) B1765577
theorem B3528593 : Blo 1393516 3528593 := bstep (se 2 (by rfl) ⟨1323222, by rfl⟩ : syracuseStep 3528593 = 2646445) B2646445
theorem B4708259 : Blo 1393516 4708259 := bstep (se 1 (by rfl) ⟨3531194, by rfl⟩ : syracuseStep 4708259 = 7062389) B7062389
theorem B3528643 : Blo 1393516 3528643 := bstep (se 1 (by rfl) ⟨2646482, by rfl⟩ : syracuseStep 3528643 = 5292965) B5292965
theorem B3135473 : Blo 1393516 3135473 := bstep (se 2 (by rfl) ⟨1175802, by rfl⟩ : syracuseStep 3135473 = 2351605) B2351605
theorem B11909105 : Blo 1393516 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B3135491 : Blo 1393516 3135491 := bstep (se 1 (by rfl) ⟨2351618, by rfl⟩ : syracuseStep 3135491 = 4703237) B4703237
theorem B1488899 : Blo 1393516 1488899 := bstep (se 1 (by rfl) ⟨1116674, by rfl⟩ : syracuseStep 1488899 = 2233349) B2233349
theorem B3528785 : Blo 1393516 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B2979985 : Blo 1393516 2979985 := bstep (se 2 (by rfl) ⟨1117494, by rfl⟩ : syracuseStep 2979985 = 2234989) B2234989
theorem B4708529 : Blo 1393516 4708529 := bstep (se 2 (by rfl) ⟨1765698, by rfl⟩ : syracuseStep 4708529 = 3531397) B3531397
theorem B1611955 : Blo 1393516 1611955 := bstep (se 1 (by rfl) ⟨1208966, by rfl⟩ : syracuseStep 1611955 = 2417933) B2417933
theorem B3135761 : Blo 1393516 3135761 := bstep (se 2 (by rfl) ⟨1175910, by rfl⟩ : syracuseStep 3135761 = 2351821) B2351821
theorem B3135779 : Blo 1393516 3135779 := bstep (se 1 (by rfl) ⟨2351834, by rfl⟩ : syracuseStep 3135779 = 4703669) B4703669
theorem B15890741 : Blo 1393516 15890741 := bstep (se 5 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 15890741 = 1489757) B1489757
theorem B2120035 : Blo 1393516 2120035 := bstep (se 1 (by rfl) ⟨1590026, by rfl⟩ : syracuseStep 2120035 = 3180053) B3180053
theorem B3971501 : Blo 1393516 3971501 := bstep (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) B1489313
theorem B2120113 : Blo 1393516 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B2234803 : Blo 1393516 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B13408739 : Blo 1393516 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B7158257 : Blo 1393516 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B3136049 : Blo 1393516 3136049 := bstep (se 2 (by rfl) ⟨1176018, by rfl⟩ : syracuseStep 3136049 = 2352037) B2352037
theorem B3136067 : Blo 1393516 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B3971683 : Blo 1393516 3971683 := bstep (se 1 (by rfl) ⟨2978762, by rfl⟩ : syracuseStep 3971683 = 5957525) B5957525
theorem B7944803 : Blo 1393516 7944803 := bstep (se 1 (by rfl) ⟨5958602, by rfl⟩ : syracuseStep 7944803 = 11917205) B11917205
theorem B3971729 : Blo 1393516 3971729 := bstep (se 2 (by rfl) ⟨1489398, by rfl⟩ : syracuseStep 3971729 = 2978797) B2978797
theorem B4709069 : Blo 1393516 4709069 := bstep (se 3 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 4709069 = 1765901) B1765901
theorem B4709123 : Blo 1393516 4709123 := bstep (se 1 (by rfl) ⟨3531842, by rfl⟩ : syracuseStep 4709123 = 7063685) B7063685
theorem B3767057 : Blo 1393516 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B5954381 : Blo 1393516 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B3136337 : Blo 1393516 3136337 := bstep (se 2 (by rfl) ⟨1176126, by rfl⟩ : syracuseStep 3136337 = 2352253) B2352253
theorem B3136355 : Blo 1393516 3136355 := bstep (se 1 (by rfl) ⟨2352266, by rfl⟩ : syracuseStep 3136355 = 4704533) B4704533
theorem B5954417 : Blo 1393516 5954417 := bstep (se 2 (by rfl) ⟨2232906, by rfl⟩ : syracuseStep 5954417 = 4465813) B4465813
theorem B5651363 : Blo 1393516 5651363 := bstep (se 1 (by rfl) ⟨4238522, by rfl⟩ : syracuseStep 5651363 = 8477045) B8477045
theorem B1489843 : Blo 1393516 1489843 := bstep (se 1 (by rfl) ⟨1117382, by rfl⟩ : syracuseStep 1489843 = 2234765) B2234765
theorem B5291021 : Blo 1393516 5291021 := bstep (se 3 (by rfl) ⟨992066, by rfl⟩ : syracuseStep 5291021 = 1984133) B1984133
theorem B4709393 : Blo 1393516 4709393 := bstep (se 2 (by rfl) ⟨1766022, by rfl⟩ : syracuseStep 4709393 = 3532045) B3532045
theorem B3529777 : Blo 1393516 3529777 := bstep (se 2 (by rfl) ⟨1323666, by rfl⟩ : syracuseStep 3529777 = 2647333) B2647333
theorem B1432643 : Blo 1393516 1432643 := bstep (se 1 (by rfl) ⟨1074482, by rfl⟩ : syracuseStep 1432643 = 2148965) B2148965
theorem B15285347 : Blo 1393516 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B3136625 : Blo 1393516 3136625 := bstep (se 2 (by rfl) ⟨1176234, by rfl⟩ : syracuseStep 3136625 = 2352469) B2352469
theorem B3136643 : Blo 1393516 3136643 := bstep (se 1 (by rfl) ⟨2352482, by rfl⟩ : syracuseStep 3136643 = 4704965) B4704965
theorem B8936675 : Blo 1393516 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B3349745 : Blo 1393516 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B3349763 : Blo 1393516 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B3530051 : Blo 1393516 3530051 := bstep (se 1 (by rfl) ⟨2647538, by rfl⟩ : syracuseStep 3530051 = 5295077) B5295077
theorem B2825617 : Blo 1393516 2825617 := bstep (se 2 (by rfl) ⟨1059606, by rfl⟩ : syracuseStep 2825617 = 2119213) B2119213
theorem B3136913 : Blo 1393516 3136913 := bstep (se 2 (by rfl) ⟨1176342, by rfl⟩ : syracuseStep 3136913 = 2352685) B2352685
theorem B3136931 : Blo 1393516 3136931 := bstep (se 1 (by rfl) ⟨2352698, by rfl⟩ : syracuseStep 3136931 = 4705397) B4705397
theorem B8052209 : Blo 1393516 8052209 := bstep (se 2 (by rfl) ⟨3019578, by rfl⟩ : syracuseStep 8052209 = 6039157) B6039157
theorem B2121203 : Blo 1393516 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B3530243 : Blo 1393516 3530243 := bstep (se 1 (by rfl) ⟨2647682, by rfl⟩ : syracuseStep 3530243 = 5295365) B5295365
theorem B10583621 : Blo 1393516 10583621 := bstep (se 4 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 10583621 = 1984429) B1984429
theorem B2645617 : Blo 1393516 2645617 := bstep (se 2 (by rfl) ⟨992106, by rfl⟩ : syracuseStep 2645617 = 1984213) B1984213
theorem B3137201 : Blo 1393516 3137201 := bstep (se 2 (by rfl) ⟨1176450, by rfl⟩ : syracuseStep 3137201 = 2352901) B2352901
theorem B3137219 : Blo 1393516 3137219 := bstep (se 1 (by rfl) ⟨2352914, by rfl⟩ : syracuseStep 3137219 = 4705829) B4705829
theorem B32202467 : Blo 1393516 32202467 := bstep (se 1 (by rfl) ⟨24151850, by rfl⟩ : syracuseStep 32202467 = 48303701) B48303701
theorem B19422989 : Blo 1393516 19422989 := bstep (se 3 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 19422989 = 7283621) B7283621
theorem B2645777 : Blo 1393516 2645777 := bstep (se 2 (by rfl) ⟨992166, by rfl⟩ : syracuseStep 2645777 = 1984333) B1984333
theorem B11648881 : Blo 1393516 11648881 := bstep (se 2 (by rfl) ⟨4368330, by rfl⟩ : syracuseStep 11648881 = 8736661) B8736661
theorem B3137489 : Blo 1393516 3137489 := bstep (se 2 (by rfl) ⟨1176558, by rfl⟩ : syracuseStep 3137489 = 2353117) B2353117
theorem B3137507 : Blo 1393516 3137507 := bstep (se 1 (by rfl) ⟨2353130, by rfl⟩ : syracuseStep 3137507 = 4706261) B4706261
theorem B2383895 : Blo 1393516 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B3137561 : Blo 1393516 3137561 := bstep (se 2 (by rfl) ⟨1176585, by rfl⟩ : syracuseStep 3137561 = 2353171) B2353171
theorem B7061579 : Blo 1393516 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B2646103 : Blo 1393516 2646103 := bstep (se 1 (by rfl) ⟨1984577, by rfl⟩ : syracuseStep 2646103 = 3969155) B3969155
theorem B3137651 : Blo 1393516 3137651 := bstep (se 1 (by rfl) ⟨2353238, by rfl⟩ : syracuseStep 3137651 = 4706477) B4706477
theorem B3137687 : Blo 1393516 3137687 := bstep (se 1 (by rfl) ⟨2353265, by rfl⟩ : syracuseStep 3137687 = 4706531) B4706531
theorem B6365357 : Blo 1393516 6365357 := bstep (se 3 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 6365357 = 2387009) B2387009
theorem B2646209 : Blo 1393516 2646209 := bstep (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) B1984657
theorem B3973313 : Blo 1393516 3973313 := bstep (se 2 (by rfl) ⟨1489992, by rfl⟩ : syracuseStep 3973313 = 2979985) B2979985
theorem B3178739 : Blo 1393516 3178739 := bstep (se 1 (by rfl) ⟨2384054, by rfl⟩ : syracuseStep 3178739 = 4768109) B4768109
theorem B3531073 : Blo 1393516 3531073 := bstep (se 2 (by rfl) ⟨1324152, by rfl⟩ : syracuseStep 3531073 = 2648305) B2648305
theorem B3137867 : Blo 1393516 3137867 := bstep (se 1 (by rfl) ⟨2353400, by rfl⟩ : syracuseStep 3137867 = 4706801) B4706801
theorem B2646361 : Blo 1393516 2646361 := bstep (se 2 (by rfl) ⟨992385, by rfl⟩ : syracuseStep 2646361 = 1984771) B1984771
theorem B3137921 : Blo 1393516 3137921 := bstep (se 2 (by rfl) ⟨1176720, by rfl⟩ : syracuseStep 3137921 = 2353441) B2353441
theorem B2826713 : Blo 1393516 2826713 := bstep (se 2 (by rfl) ⟨1060017, by rfl⟩ : syracuseStep 2826713 = 2120035) B2120035
theorem B60293645 : Blo 1393516 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B10584593 : Blo 1393516 10584593 := bstep (se 2 (by rfl) ⟨3969222, by rfl⟩ : syracuseStep 10584593 = 7938445) B7938445
theorem B2351639 : Blo 1393516 2351639 := bstep (se 1 (by rfl) ⟨1763729, by rfl⟩ : syracuseStep 2351639 = 3527459) B3527459
theorem B20095523 : Blo 1393516 20095523 := bstep (se 1 (by rfl) ⟨15071642, by rfl⟩ : syracuseStep 20095523 = 30143285) B30143285
theorem B10052171 : Blo 1393516 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B3138137 : Blo 1393516 3138137 := bstep (se 2 (by rfl) ⟨1176801, by rfl⟩ : syracuseStep 3138137 = 2353603) B2353603
theorem B2351767 : Blo 1393516 2351767 := bstep (se 1 (by rfl) ⟨1763825, by rfl⟩ : syracuseStep 2351767 = 3527651) B3527651
theorem B3138227 : Blo 1393516 3138227 := bstep (se 1 (by rfl) ⟨2353670, by rfl⟩ : syracuseStep 3138227 = 4707341) B4707341
theorem B3138263 : Blo 1393516 3138263 := bstep (se 1 (by rfl) ⟨2353697, by rfl⟩ : syracuseStep 3138263 = 4707395) B4707395
theorem B1393527 : Blo 1393516 1393527 := bstep (se 1 (by rfl) ⟨1045145, by rfl⟩ : syracuseStep 1393527 = 2090291) B2090291
theorem B1393547 : Blo 1393516 1393547 := bstep (se 1 (by rfl) ⟨1045160, by rfl⟩ : syracuseStep 1393547 = 2090321) B2090321
theorem B3138443 : Blo 1393516 3138443 := bstep (se 1 (by rfl) ⟨2353832, by rfl⟩ : syracuseStep 3138443 = 4707665) B4707665
theorem B1393559 : Blo 1393516 1393559 := bstep (se 1 (by rfl) ⟨1045169, by rfl⟩ : syracuseStep 1393559 = 2090339) B2090339
theorem B3531671 : Blo 1393516 3531671 := bstep (se 1 (by rfl) ⟨2648753, by rfl⟩ : syracuseStep 3531671 = 5297507) B5297507
theorem B1393579 : Blo 1393516 1393579 := bstep (se 1 (by rfl) ⟨1045184, by rfl⟩ : syracuseStep 1393579 = 2090369) B2090369
theorem B1393591 : Blo 1393516 1393591 := bstep (se 1 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 1393591 = 2090387) B2090387
theorem B3138497 : Blo 1393516 3138497 := bstep (se 2 (by rfl) ⟨1176936, by rfl⟩ : syracuseStep 3138497 = 2353873) B2353873
theorem B1393611 : Blo 1393516 1393611 := bstep (se 1 (by rfl) ⟨1045208, by rfl⟩ : syracuseStep 1393611 = 2090417) B2090417
theorem B1393623 : Blo 1393516 1393623 := bstep (se 1 (by rfl) ⟨1045217, by rfl⟩ : syracuseStep 1393623 = 2090435) B2090435
theorem B1393643 : Blo 1393516 1393643 := bstep (se 1 (by rfl) ⟨1045232, by rfl⟩ : syracuseStep 1393643 = 2090465) B2090465
theorem B1393655 : Blo 1393516 1393655 := bstep (se 1 (by rfl) ⟨1045241, by rfl⟩ : syracuseStep 1393655 = 2090483) B2090483
theorem B1393675 : Blo 1393516 1393675 := bstep (se 1 (by rfl) ⟨1045256, by rfl⟩ : syracuseStep 1393675 = 2090513) B2090513
theorem B128803861 : Blo 1393516 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B1393687 : Blo 1393516 1393687 := bstep (se 1 (by rfl) ⟨1045265, by rfl⟩ : syracuseStep 1393687 = 2090531) B2090531
theorem B1393707 : Blo 1393516 1393707 := bstep (se 1 (by rfl) ⟨1045280, by rfl⟩ : syracuseStep 1393707 = 2090561) B2090561
theorem B1393719 : Blo 1393516 1393719 := bstep (se 1 (by rfl) ⟨1045289, by rfl⟩ : syracuseStep 1393719 = 2090579) B2090579
theorem B1393739 : Blo 1393516 1393739 := bstep (se 1 (by rfl) ⟨1045304, by rfl⟩ : syracuseStep 1393739 = 2090609) B2090609
theorem B8479819 : Blo 1393516 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B1393751 : Blo 1393516 1393751 := bstep (se 1 (by rfl) ⟨1045313, by rfl⟩ : syracuseStep 1393751 = 2090627) B2090627
theorem B1393771 : Blo 1393516 1393771 := bstep (se 1 (by rfl) ⟨1045328, by rfl⟩ : syracuseStep 1393771 = 2090657) B2090657
theorem B1393783 : Blo 1393516 1393783 := bstep (se 1 (by rfl) ⟨1045337, by rfl⟩ : syracuseStep 1393783 = 2090675) B2090675
theorem B1393803 : Blo 1393516 1393803 := bstep (se 1 (by rfl) ⟨1045352, by rfl⟩ : syracuseStep 1393803 = 2090705) B2090705
theorem B1393815 : Blo 1393516 1393815 := bstep (se 1 (by rfl) ⟨1045361, by rfl⟩ : syracuseStep 1393815 = 2090723) B2090723
theorem B3138713 : Blo 1393516 3138713 := bstep (se 2 (by rfl) ⟨1177017, by rfl⟩ : syracuseStep 3138713 = 2354035) B2354035
theorem B1393835 : Blo 1393516 1393835 := bstep (se 1 (by rfl) ⟨1045376, by rfl⟩ : syracuseStep 1393835 = 2090753) B2090753
theorem B3769523 : Blo 1393516 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B1393847 : Blo 1393516 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B1393867 : Blo 1393516 1393867 := bstep (se 1 (by rfl) ⟨1045400, by rfl⟩ : syracuseStep 1393867 = 2090801) B2090801
theorem B1393879 : Blo 1393516 1393879 := bstep (se 1 (by rfl) ⟨1045409, by rfl⟩ : syracuseStep 1393879 = 2090819) B2090819
theorem B1885399 : Blo 1393516 1885399 := bstep (se 1 (by rfl) ⟨1414049, by rfl⟩ : syracuseStep 1885399 = 2828099) B2828099
theorem B5367001 : Blo 1393516 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B4703453 : Blo 1393516 4703453 := bstep (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) B1763795
theorem B1393899 : Blo 1393516 1393899 := bstep (se 1 (by rfl) ⟨1045424, by rfl⟩ : syracuseStep 1393899 = 2090849) B2090849
theorem B3138803 : Blo 1393516 3138803 := bstep (se 1 (by rfl) ⟨2354102, by rfl⟩ : syracuseStep 3138803 = 4708205) B4708205
theorem B1393911 : Blo 1393516 1393911 := bstep (se 1 (by rfl) ⟨1045433, by rfl⟩ : syracuseStep 1393911 = 2090867) B2090867
theorem B11912453 : Blo 1393516 11912453 := bstep (se 4 (by rfl) ⟨1116792, by rfl⟩ : syracuseStep 11912453 = 2233585) B2233585
theorem B1393931 : Blo 1393516 1393931 := bstep (se 1 (by rfl) ⟨1045448, by rfl⟩ : syracuseStep 1393931 = 2090897) B2090897
theorem B2352395 : Blo 1393516 2352395 := bstep (se 1 (by rfl) ⟨1764296, by rfl⟩ : syracuseStep 2352395 = 3528593) B3528593
theorem B1393943 : Blo 1393516 1393943 := bstep (se 1 (by rfl) ⟨1045457, by rfl⟩ : syracuseStep 1393943 = 2090915) B2090915
theorem B3138839 : Blo 1393516 3138839 := bstep (se 1 (by rfl) ⟨2354129, by rfl⟩ : syracuseStep 3138839 = 4708259) B4708259
theorem B1393963 : Blo 1393516 1393963 := bstep (se 1 (by rfl) ⟨1045472, by rfl⟩ : syracuseStep 1393963 = 2090945) B2090945
theorem B1393975 : Blo 1393516 1393975 := bstep (se 1 (by rfl) ⟨1045481, by rfl⟩ : syracuseStep 1393975 = 2090963) B2090963
theorem B2090315 : Blo 1393516 2090315 := bstep (se 1 (by rfl) ⟨1567736, by rfl⟩ : syracuseStep 2090315 = 3135473) B3135473
theorem B1393995 : Blo 1393516 1393995 := bstep (se 1 (by rfl) ⟨1045496, by rfl⟩ : syracuseStep 1393995 = 2090993) B2090993
theorem B7939403 : Blo 1393516 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B2090327 : Blo 1393516 2090327 := bstep (se 1 (by rfl) ⟨1567745, by rfl⟩ : syracuseStep 2090327 = 3135491) B3135491
theorem B1394007 : Blo 1393516 1394007 := bstep (se 1 (by rfl) ⟨1045505, by rfl⟩ : syracuseStep 1394007 = 2091011) B2091011
theorem B1394027 : Blo 1393516 1394027 := bstep (se 1 (by rfl) ⟨1045520, by rfl⟩ : syracuseStep 1394027 = 2091041) B2091041
theorem B42911093 : Blo 1393516 42911093 := bstep (se 5 (by rfl) ⟨2011457, by rfl⟩ : syracuseStep 42911093 = 4022915) B4022915
theorem B1394039 : Blo 1393516 1394039 := bstep (se 1 (by rfl) ⟨1045529, by rfl⟩ : syracuseStep 1394039 = 2091059) B2091059
theorem B1394059 : Blo 1393516 1394059 := bstep (se 1 (by rfl) ⟨1045544, by rfl⟩ : syracuseStep 1394059 = 2091089) B2091089
theorem B2352523 : Blo 1393516 2352523 := bstep (se 1 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 2352523 = 3528785) B3528785
theorem B1394071 : Blo 1393516 1394071 := bstep (se 1 (by rfl) ⟨1045553, by rfl⟩ : syracuseStep 1394071 = 2091107) B2091107
theorem B2090393 : Blo 1393516 2090393 := bstep (se 2 (by rfl) ⟨783897, by rfl⟩ : syracuseStep 2090393 = 1567795) B1567795
theorem B1394091 : Blo 1393516 1394091 := bstep (se 1 (by rfl) ⟨1045568, by rfl⟩ : syracuseStep 1394091 = 2091137) B2091137
theorem B1394103 : Blo 1393516 1394103 := bstep (se 1 (by rfl) ⟨1045577, by rfl⟩ : syracuseStep 1394103 = 2091155) B2091155
theorem B1394123 : Blo 1393516 1394123 := bstep (se 1 (by rfl) ⟨1045592, by rfl⟩ : syracuseStep 1394123 = 2091185) B2091185
theorem B3139019 : Blo 1393516 3139019 := bstep (se 1 (by rfl) ⟨2354264, by rfl⟩ : syracuseStep 3139019 = 4708529) B4708529
theorem B1394135 : Blo 1393516 1394135 := bstep (se 1 (by rfl) ⟨1045601, by rfl⟩ : syracuseStep 1394135 = 2091203) B2091203
theorem B1394155 : Blo 1393516 1394155 := bstep (se 1 (by rfl) ⟨1045616, by rfl⟩ : syracuseStep 1394155 = 2091233) B2091233
theorem B1394167 : Blo 1393516 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B3139073 : Blo 1393516 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B2090507 : Blo 1393516 2090507 := bstep (se 1 (by rfl) ⟨1567880, by rfl⟩ : syracuseStep 2090507 = 3135761) B3135761
theorem B1394187 : Blo 1393516 1394187 := bstep (se 1 (by rfl) ⟨1045640, by rfl⟩ : syracuseStep 1394187 = 2091281) B2091281
theorem B2090519 : Blo 1393516 2090519 := bstep (se 1 (by rfl) ⟨1567889, by rfl⟩ : syracuseStep 2090519 = 3135779) B3135779
theorem B1394199 : Blo 1393516 1394199 := bstep (se 1 (by rfl) ⟨1045649, by rfl⟩ : syracuseStep 1394199 = 2091299) B2091299
theorem B2352665 : Blo 1393516 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B10593827 : Blo 1393516 10593827 := bstep (se 1 (by rfl) ⟨7945370, by rfl⟩ : syracuseStep 10593827 = 15890741) B15890741
theorem B1394219 : Blo 1393516 1394219 := bstep (se 1 (by rfl) ⟨1045664, by rfl⟩ : syracuseStep 1394219 = 2091329) B2091329
theorem B5293619 : Blo 1393516 5293619 := bstep (se 1 (by rfl) ⟨3970214, by rfl⟩ : syracuseStep 5293619 = 7940429) B7940429
theorem B1394231 : Blo 1393516 1394231 := bstep (se 1 (by rfl) ⟨1045673, by rfl⟩ : syracuseStep 1394231 = 2091347) B2091347
theorem B5293633 : Blo 1393516 5293633 := bstep (se 2 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 5293633 = 3970225) B3970225
theorem B1394251 : Blo 1393516 1394251 := bstep (se 1 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 1394251 = 2091377) B2091377
theorem B1394263 : Blo 1393516 1394263 := bstep (se 1 (by rfl) ⟨1045697, by rfl⟩ : syracuseStep 1394263 = 2091395) B2091395
theorem B2090585 : Blo 1393516 2090585 := bstep (se 2 (by rfl) ⟨783969, by rfl⟩ : syracuseStep 2090585 = 1567939) B1567939
theorem B1394283 : Blo 1393516 1394283 := bstep (se 1 (by rfl) ⟨1045712, by rfl⟩ : syracuseStep 1394283 = 2091425) B2091425
theorem B2647667 : Blo 1393516 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B1394295 : Blo 1393516 1394295 := bstep (se 1 (by rfl) ⟨1045721, by rfl⟩ : syracuseStep 1394295 = 2091443) B2091443
theorem B1394315 : Blo 1393516 1394315 := bstep (se 1 (by rfl) ⟨1045736, by rfl⟩ : syracuseStep 1394315 = 2091473) B2091473
theorem B1394327 : Blo 1393516 1394327 := bstep (se 1 (by rfl) ⟨1045745, by rfl⟩ : syracuseStep 1394327 = 2091491) B2091491
theorem B8939159 : Blo 1393516 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B2352793 : Blo 1393516 2352793 := bstep (se 2 (by rfl) ⟨882297, by rfl⟩ : syracuseStep 2352793 = 1764595) B1764595
theorem B1394347 : Blo 1393516 1394347 := bstep (se 1 (by rfl) ⟨1045760, by rfl⟩ : syracuseStep 1394347 = 2091521) B2091521
theorem B1394359 : Blo 1393516 1394359 := bstep (se 1 (by rfl) ⟨1045769, by rfl⟩ : syracuseStep 1394359 = 2091539) B2091539
theorem B2090699 : Blo 1393516 2090699 := bstep (se 1 (by rfl) ⟨1568024, by rfl⟩ : syracuseStep 2090699 = 3136049) B3136049
theorem B1394379 : Blo 1393516 1394379 := bstep (se 1 (by rfl) ⟨1045784, by rfl⟩ : syracuseStep 1394379 = 2091569) B2091569
theorem B2090711 : Blo 1393516 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B1394391 : Blo 1393516 1394391 := bstep (se 1 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 1394391 = 2091587) B2091587
theorem B4024025 : Blo 1393516 4024025 := bstep (se 2 (by rfl) ⟨1509009, by rfl⟩ : syracuseStep 4024025 = 3018019) B3018019
theorem B3139289 : Blo 1393516 3139289 := bstep (se 2 (by rfl) ⟨1177233, by rfl⟩ : syracuseStep 3139289 = 2354467) B2354467
theorem B1394411 : Blo 1393516 1394411 := bstep (se 1 (by rfl) ⟨1045808, by rfl⟩ : syracuseStep 1394411 = 2091617) B2091617
theorem B1394423 : Blo 1393516 1394423 := bstep (se 1 (by rfl) ⟨1045817, by rfl⟩ : syracuseStep 1394423 = 2091635) B2091635
theorem B1394443 : Blo 1393516 1394443 := bstep (se 1 (by rfl) ⟨1045832, by rfl⟩ : syracuseStep 1394443 = 2091665) B2091665
theorem B2647819 : Blo 1393516 2647819 := bstep (se 1 (by rfl) ⟨1985864, by rfl⟩ : syracuseStep 2647819 = 3971729) B3971729
theorem B1394455 : Blo 1393516 1394455 := bstep (se 1 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 1394455 = 2091683) B2091683
theorem B2090777 : Blo 1393516 2090777 := bstep (se 2 (by rfl) ⟨784041, by rfl⟩ : syracuseStep 2090777 = 1568083) B1568083
theorem B1394475 : Blo 1393516 1394475 := bstep (se 1 (by rfl) ⟨1045856, by rfl⟩ : syracuseStep 1394475 = 2091713) B2091713
theorem B3139379 : Blo 1393516 3139379 := bstep (se 1 (by rfl) ⟨2354534, by rfl⟩ : syracuseStep 3139379 = 4709069) B4709069
theorem B1394487 : Blo 1393516 1394487 := bstep (se 1 (by rfl) ⟨1045865, by rfl⟩ : syracuseStep 1394487 = 2091731) B2091731
theorem B7063361 : Blo 1393516 7063361 := bstep (se 2 (by rfl) ⟨2648760, by rfl⟩ : syracuseStep 7063361 = 5297521) B5297521
theorem B1836875 : Blo 1393516 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1394507 : Blo 1393516 1394507 := bstep (se 1 (by rfl) ⟨1045880, by rfl⟩ : syracuseStep 1394507 = 2091761) B2091761
theorem B1394519 : Blo 1393516 1394519 := bstep (se 1 (by rfl) ⟨1045889, by rfl⟩ : syracuseStep 1394519 = 2091779) B2091779
theorem B3139415 : Blo 1393516 3139415 := bstep (se 1 (by rfl) ⟨2354561, by rfl⟩ : syracuseStep 3139415 = 4709123) B4709123
theorem B1394539 : Blo 1393516 1394539 := bstep (se 1 (by rfl) ⟨1045904, by rfl⟩ : syracuseStep 1394539 = 2091809) B2091809
theorem B1394551 : Blo 1393516 1394551 := bstep (se 1 (by rfl) ⟨1045913, by rfl⟩ : syracuseStep 1394551 = 2091827) B2091827
theorem B2090891 : Blo 1393516 2090891 := bstep (se 1 (by rfl) ⟨1568168, by rfl⟩ : syracuseStep 2090891 = 3136337) B3136337
theorem B1394571 : Blo 1393516 1394571 := bstep (se 1 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 1394571 = 2091857) B2091857
theorem B2090903 : Blo 1393516 2090903 := bstep (se 1 (by rfl) ⟨1568177, by rfl⟩ : syracuseStep 2090903 = 3136355) B3136355
theorem B1394583 : Blo 1393516 1394583 := bstep (se 1 (by rfl) ⟨1045937, by rfl⟩ : syracuseStep 1394583 = 2091875) B2091875
theorem B1394603 : Blo 1393516 1394603 := bstep (se 1 (by rfl) ⟨1045952, by rfl⟩ : syracuseStep 1394603 = 2091905) B2091905
theorem B1394615 : Blo 1393516 1394615 := bstep (se 1 (by rfl) ⟨1045961, by rfl⟩ : syracuseStep 1394615 = 2091923) B2091923
theorem B1394635 : Blo 1393516 1394635 := bstep (se 1 (by rfl) ⟨1045976, by rfl⟩ : syracuseStep 1394635 = 2091953) B2091953
theorem B1394647 : Blo 1393516 1394647 := bstep (se 1 (by rfl) ⟨1045985, by rfl⟩ : syracuseStep 1394647 = 2091971) B2091971
theorem B2090969 : Blo 1393516 2090969 := bstep (se 2 (by rfl) ⟨784113, by rfl⟩ : syracuseStep 2090969 = 1568227) B1568227
theorem B1394667 : Blo 1393516 1394667 := bstep (se 1 (by rfl) ⟨1046000, by rfl⟩ : syracuseStep 1394667 = 2092001) B2092001
theorem B1394679 : Blo 1393516 1394679 := bstep (se 1 (by rfl) ⟨1046009, by rfl⟩ : syracuseStep 1394679 = 2092019) B2092019
theorem B1394699 : Blo 1393516 1394699 := bstep (se 1 (by rfl) ⟨1046024, by rfl⟩ : syracuseStep 1394699 = 2092049) B2092049
theorem B3139595 : Blo 1393516 3139595 := bstep (se 1 (by rfl) ⟨2354696, by rfl⟩ : syracuseStep 3139595 = 4709393) B4709393
theorem B1394711 : Blo 1393516 1394711 := bstep (se 1 (by rfl) ⟨1046033, by rfl⟩ : syracuseStep 1394711 = 2092067) B2092067
theorem B1394731 : Blo 1393516 1394731 := bstep (se 1 (by rfl) ⟨1046048, by rfl⟩ : syracuseStep 1394731 = 2092097) B2092097
theorem B1394743 : Blo 1393516 1394743 := bstep (se 1 (by rfl) ⟨1046057, by rfl⟩ : syracuseStep 1394743 = 2092115) B2092115
theorem B3139649 : Blo 1393516 3139649 := bstep (se 2 (by rfl) ⟨1177368, by rfl⟩ : syracuseStep 3139649 = 2354737) B2354737
theorem B2091083 : Blo 1393516 2091083 := bstep (se 1 (by rfl) ⟨1568312, by rfl⟩ : syracuseStep 2091083 = 3136625) B3136625
theorem B1394763 : Blo 1393516 1394763 := bstep (se 1 (by rfl) ⟨1046072, by rfl⟩ : syracuseStep 1394763 = 2092145) B2092145
theorem B2091095 : Blo 1393516 2091095 := bstep (se 1 (by rfl) ⟨1568321, by rfl⟩ : syracuseStep 2091095 = 3136643) B3136643
theorem B1394775 : Blo 1393516 1394775 := bstep (se 1 (by rfl) ⟨1046081, by rfl⟩ : syracuseStep 1394775 = 2092163) B2092163
theorem B2648153 : Blo 1393516 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B1394795 : Blo 1393516 1394795 := bstep (se 1 (by rfl) ⟨1046096, by rfl⟩ : syracuseStep 1394795 = 2092193) B2092193
theorem B1394807 : Blo 1393516 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B1394827 : Blo 1393516 1394827 := bstep (se 1 (by rfl) ⟨1046120, by rfl⟩ : syracuseStep 1394827 = 2092241) B2092241
theorem B5957783 : Blo 1393516 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B1394839 : Blo 1393516 1394839 := bstep (se 1 (by rfl) ⟨1046129, by rfl⟩ : syracuseStep 1394839 = 2092259) B2092259
theorem B2091161 : Blo 1393516 2091161 := bstep (se 2 (by rfl) ⟨784185, by rfl⟩ : syracuseStep 2091161 = 1568371) B1568371
theorem B1394859 : Blo 1393516 1394859 := bstep (se 1 (by rfl) ⟨1046144, by rfl⟩ : syracuseStep 1394859 = 2092289) B2092289
theorem B1394871 : Blo 1393516 1394871 := bstep (se 1 (by rfl) ⟨1046153, by rfl⟩ : syracuseStep 1394871 = 2092307) B2092307
theorem B1394891 : Blo 1393516 1394891 := bstep (se 1 (by rfl) ⟨1046168, by rfl⟩ : syracuseStep 1394891 = 2092337) B2092337
theorem B2353367 : Blo 1393516 2353367 := bstep (se 1 (by rfl) ⟨1765025, by rfl⟩ : syracuseStep 2353367 = 3530051) B3530051
theorem B1394903 : Blo 1393516 1394903 := bstep (se 1 (by rfl) ⟨1046177, by rfl⟩ : syracuseStep 1394903 = 2092355) B2092355
theorem B1394923 : Blo 1393516 1394923 := bstep (se 1 (by rfl) ⟨1046192, by rfl⟩ : syracuseStep 1394923 = 2092385) B2092385
theorem B1394935 : Blo 1393516 1394935 := bstep (se 1 (by rfl) ⟨1046201, by rfl⟩ : syracuseStep 1394935 = 2092403) B2092403
theorem B11307269 : Blo 1393516 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B2091275 : Blo 1393516 2091275 := bstep (se 1 (by rfl) ⟨1568456, by rfl⟩ : syracuseStep 2091275 = 3136913) B3136913
theorem B1394955 : Blo 1393516 1394955 := bstep (se 1 (by rfl) ⟨1046216, by rfl⟩ : syracuseStep 1394955 = 2092433) B2092433
theorem B2091287 : Blo 1393516 2091287 := bstep (se 1 (by rfl) ⟨1568465, by rfl⟩ : syracuseStep 2091287 = 3136931) B3136931
theorem B1394967 : Blo 1393516 1394967 := bstep (se 1 (by rfl) ⟨1046225, by rfl⟩ : syracuseStep 1394967 = 2092451) B2092451
theorem B3139865 : Blo 1393516 3139865 := bstep (se 2 (by rfl) ⟨1177449, by rfl⟩ : syracuseStep 3139865 = 2354899) B2354899
theorem B1394987 : Blo 1393516 1394987 := bstep (se 1 (by rfl) ⟨1046240, by rfl⟩ : syracuseStep 1394987 = 2092481) B2092481
theorem B1394999 : Blo 1393516 1394999 := bstep (se 1 (by rfl) ⟨1046249, by rfl⟩ : syracuseStep 1394999 = 2092499) B2092499
theorem B4704587 : Blo 1393516 4704587 := bstep (se 1 (by rfl) ⟨3528440, by rfl⟩ : syracuseStep 4704587 = 7056881) B7056881
theorem B5368139 : Blo 1393516 5368139 := bstep (se 1 (by rfl) ⟨4026104, by rfl⟩ : syracuseStep 5368139 = 8052209) B8052209
theorem B1395019 : Blo 1393516 1395019 := bstep (se 1 (by rfl) ⟨1046264, by rfl⟩ : syracuseStep 1395019 = 2092529) B2092529
theorem B2353495 : Blo 1393516 2353495 := bstep (se 1 (by rfl) ⟨1765121, by rfl⟩ : syracuseStep 2353495 = 3530243) B3530243
theorem B2091353 : Blo 1393516 2091353 := bstep (se 2 (by rfl) ⟨784257, by rfl⟩ : syracuseStep 2091353 = 1568515) B1568515
theorem B1395031 : Blo 1393516 1395031 := bstep (se 1 (by rfl) ⟨1046273, by rfl⟩ : syracuseStep 1395031 = 2092547) B2092547
theorem B1395051 : Blo 1393516 1395051 := bstep (se 1 (by rfl) ⟨1046288, by rfl⟩ : syracuseStep 1395051 = 2092577) B2092577
theorem B1395063 : Blo 1393516 1395063 := bstep (se 1 (by rfl) ⟨1046297, by rfl⟩ : syracuseStep 1395063 = 2092595) B2092595
theorem B7055747 : Blo 1393516 7055747 := bstep (se 1 (by rfl) ⟨5291810, by rfl⟩ : syracuseStep 7055747 = 10583621) B10583621
theorem B1395083 : Blo 1393516 1395083 := bstep (se 1 (by rfl) ⟨1046312, by rfl⟩ : syracuseStep 1395083 = 2092625) B2092625
theorem B1395095 : Blo 1393516 1395095 := bstep (se 1 (by rfl) ⟨1046321, by rfl⟩ : syracuseStep 1395095 = 2092643) B2092643
theorem B1395115 : Blo 1393516 1395115 := bstep (se 1 (by rfl) ⟨1046336, by rfl⟩ : syracuseStep 1395115 = 2092673) B2092673
theorem B1395127 : Blo 1393516 1395127 := bstep (se 1 (by rfl) ⟨1046345, by rfl⟩ : syracuseStep 1395127 = 2092691) B2092691
theorem B2091467 : Blo 1393516 2091467 := bstep (se 1 (by rfl) ⟨1568600, by rfl⟩ : syracuseStep 2091467 = 3137201) B3137201
theorem B1395147 : Blo 1393516 1395147 := bstep (se 1 (by rfl) ⟨1046360, by rfl⟩ : syracuseStep 1395147 = 2092721) B2092721
theorem B2091479 : Blo 1393516 2091479 := bstep (se 1 (by rfl) ⟨1568609, by rfl⟩ : syracuseStep 2091479 = 3137219) B3137219
theorem B1395159 : Blo 1393516 1395159 := bstep (se 1 (by rfl) ⟨1046369, by rfl⟩ : syracuseStep 1395159 = 2092739) B2092739
theorem B6449629 : Blo 1393516 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B1395179 : Blo 1393516 1395179 := bstep (se 1 (by rfl) ⟨1046384, by rfl⟩ : syracuseStep 1395179 = 2092769) B2092769
theorem B1395191 : Blo 1393516 1395191 := bstep (se 1 (by rfl) ⟨1046393, by rfl⟩ : syracuseStep 1395191 = 2092787) B2092787
theorem B1763851 : Blo 1393516 1763851 := bstep (se 1 (by rfl) ⟨1322888, by rfl⟩ : syracuseStep 1763851 = 2645777) B2645777
theorem B1395211 : Blo 1393516 1395211 := bstep (se 1 (by rfl) ⟨1046408, by rfl⟩ : syracuseStep 1395211 = 2092817) B2092817
theorem B1395223 : Blo 1393516 1395223 := bstep (se 1 (by rfl) ⟨1046417, by rfl⟩ : syracuseStep 1395223 = 2092835) B2092835
theorem B2091545 : Blo 1393516 2091545 := bstep (se 2 (by rfl) ⟨784329, by rfl⟩ : syracuseStep 2091545 = 1568659) B1568659
theorem B1395243 : Blo 1393516 1395243 := bstep (se 1 (by rfl) ⟨1046432, by rfl⟩ : syracuseStep 1395243 = 2092865) B2092865
theorem B1395255 : Blo 1393516 1395255 := bstep (se 1 (by rfl) ⟨1046441, by rfl⟩ : syracuseStep 1395255 = 2092883) B2092883
theorem B1395275 : Blo 1393516 1395275 := bstep (se 1 (by rfl) ⟨1046456, by rfl⟩ : syracuseStep 1395275 = 2092913) B2092913
theorem B15895115 : Blo 1393516 15895115 := bstep (se 1 (by rfl) ⟨11921336, by rfl⟩ : syracuseStep 15895115 = 23842673) B23842673
theorem B1395287 : Blo 1393516 1395287 := bstep (se 1 (by rfl) ⟨1046465, by rfl⟩ : syracuseStep 1395287 = 2092931) B2092931
theorem B4704857 : Blo 1393516 4704857 := bstep (se 2 (by rfl) ⟨1764321, by rfl⟩ : syracuseStep 4704857 = 3528643) B3528643
theorem B1395307 : Blo 1393516 1395307 := bstep (se 1 (by rfl) ⟨1046480, by rfl⟩ : syracuseStep 1395307 = 2092961) B2092961
theorem B1395319 : Blo 1393516 1395319 := bstep (se 1 (by rfl) ⟨1046489, by rfl⟩ : syracuseStep 1395319 = 2092979) B2092979
theorem B45238915 : Blo 1393516 45238915 := bstep (se 1 (by rfl) ⟨33929186, by rfl⟩ : syracuseStep 45238915 = 67858373) B67858373
theorem B2091659 : Blo 1393516 2091659 := bstep (se 1 (by rfl) ⟨1568744, by rfl⟩ : syracuseStep 2091659 = 3137489) B3137489
theorem B1395339 : Blo 1393516 1395339 := bstep (se 1 (by rfl) ⟨1046504, by rfl⟩ : syracuseStep 1395339 = 2093009) B2093009
theorem B2091671 : Blo 1393516 2091671 := bstep (se 1 (by rfl) ⟨1568753, by rfl⟩ : syracuseStep 2091671 = 3137507) B3137507
theorem B1395351 : Blo 1393516 1395351 := bstep (se 1 (by rfl) ⟨1046513, by rfl⟩ : syracuseStep 1395351 = 2093027) B2093027
theorem B1395371 : Blo 1393516 1395371 := bstep (se 1 (by rfl) ⟨1046528, by rfl⟩ : syracuseStep 1395371 = 2093057) B2093057
theorem B1395383 : Blo 1393516 1395383 := bstep (se 1 (by rfl) ⟨1046537, by rfl⟩ : syracuseStep 1395383 = 2093075) B2093075
theorem B1395403 : Blo 1393516 1395403 := bstep (se 1 (by rfl) ⟨1046552, by rfl⟩ : syracuseStep 1395403 = 2093105) B2093105
theorem B2648791 : Blo 1393516 2648791 := bstep (se 1 (by rfl) ⟨1986593, by rfl⟩ : syracuseStep 2648791 = 3973187) B3973187
theorem B1395415 : Blo 1393516 1395415 := bstep (se 1 (by rfl) ⟨1046561, by rfl⟩ : syracuseStep 1395415 = 2093123) B2093123
theorem B2976473 : Blo 1393516 2976473 := bstep (se 2 (by rfl) ⟨1116177, by rfl⟩ : syracuseStep 2976473 = 2232355) B2232355
theorem B2091737 : Blo 1393516 2091737 := bstep (se 2 (by rfl) ⟨784401, by rfl⟩ : syracuseStep 2091737 = 1568803) B1568803
theorem B1395435 : Blo 1393516 1395435 := bstep (se 1 (by rfl) ⟨1046576, by rfl⟩ : syracuseStep 1395435 = 2093153) B2093153
theorem B1395447 : Blo 1393516 1395447 := bstep (se 1 (by rfl) ⟨1046585, by rfl⟩ : syracuseStep 1395447 = 2093171) B2093171
theorem B1395467 : Blo 1393516 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B3394327 : Blo 1393516 3394327 := bstep (se 1 (by rfl) ⟨2545745, by rfl⟩ : syracuseStep 3394327 = 5091491) B5091491
theorem B1764119 : Blo 1393516 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B1395479 : Blo 1393516 1395479 := bstep (se 1 (by rfl) ⟨1046609, by rfl⟩ : syracuseStep 1395479 = 2093219) B2093219
theorem B1395499 : Blo 1393516 1395499 := bstep (se 1 (by rfl) ⟨1046624, by rfl⟩ : syracuseStep 1395499 = 2093249) B2093249
theorem B1395511 : Blo 1393516 1395511 := bstep (se 1 (by rfl) ⟨1046633, by rfl⟩ : syracuseStep 1395511 = 2093267) B2093267
theorem B5024587 : Blo 1393516 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B2091851 : Blo 1393516 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B2091863 : Blo 1393516 2091863 := bstep (se 1 (by rfl) ⟨1568897, by rfl⟩ : syracuseStep 2091863 = 3137795) B3137795
theorem B3820381 : Blo 1393516 3820381 := bstep (se 3 (by rfl) ⟨716321, by rfl⟩ : syracuseStep 3820381 = 1432643) B1432643
theorem B45255523 : Blo 1393516 45255523 := bstep (se 1 (by rfl) ⟨33941642, by rfl⟩ : syracuseStep 45255523 = 67883285) B67883285
theorem B2149273 : Blo 1393516 2149273 := bstep (se 2 (by rfl) ⟨805977, by rfl⟩ : syracuseStep 2149273 = 1611955) B1611955
theorem B2091929 : Blo 1393516 2091929 := bstep (se 2 (by rfl) ⟨784473, by rfl⟩ : syracuseStep 2091929 = 1568947) B1568947
theorem B2354123 : Blo 1393516 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B1567723 : Blo 1393516 1567723 := bstep (se 1 (by rfl) ⟨1175792, by rfl⟩ : syracuseStep 1567723 = 2351585) B2351585
theorem B2092043 : Blo 1393516 2092043 := bstep (se 1 (by rfl) ⟨1569032, by rfl⟩ : syracuseStep 2092043 = 3138065) B3138065
theorem B2386955 : Blo 1393516 2386955 := bstep (se 1 (by rfl) ⟨1790216, by rfl⟩ : syracuseStep 2386955 = 3580433) B3580433
theorem B2092055 : Blo 1393516 2092055 := bstep (se 1 (by rfl) ⟨1569041, by rfl⟩ : syracuseStep 2092055 = 3138083) B3138083
theorem B2354251 : Blo 1393516 2354251 := bstep (se 1 (by rfl) ⟨1765688, by rfl⟩ : syracuseStep 2354251 = 3531377) B3531377
theorem B1567831 : Blo 1393516 1567831 := bstep (se 1 (by rfl) ⟨1175873, by rfl⟩ : syracuseStep 1567831 = 2351747) B2351747
theorem B2092121 : Blo 1393516 2092121 := bstep (se 2 (by rfl) ⟨784545, by rfl⟩ : syracuseStep 2092121 = 1569091) B1569091
theorem B2092235 : Blo 1393516 2092235 := bstep (se 1 (by rfl) ⟨1569176, by rfl⟩ : syracuseStep 2092235 = 3138353) B3138353
theorem B2092247 : Blo 1393516 2092247 := bstep (se 1 (by rfl) ⟨1569185, by rfl⟩ : syracuseStep 2092247 = 3138371) B3138371
theorem B2354393 : Blo 1393516 2354393 := bstep (se 2 (by rfl) ⟨882897, by rfl⟩ : syracuseStep 2354393 = 1765795) B1765795
theorem B1568011 : Blo 1393516 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B4705559 : Blo 1393516 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B2092313 : Blo 1393516 2092313 := bstep (se 2 (by rfl) ⟨784617, by rfl⟩ : syracuseStep 2092313 = 1569235) B1569235
theorem B2354521 : Blo 1393516 2354521 := bstep (se 2 (by rfl) ⟨882945, by rfl⟩ : syracuseStep 2354521 = 1765891) B1765891
theorem B8940901 : Blo 1393516 8940901 := bstep (se 4 (by rfl) ⟨838209, by rfl⟩ : syracuseStep 8940901 = 1676419) B1676419
theorem B1568119 : Blo 1393516 1568119 := bstep (se 1 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 1568119 = 2352179) B2352179
theorem B2092427 : Blo 1393516 2092427 := bstep (se 1 (by rfl) ⟨1569320, by rfl⟩ : syracuseStep 2092427 = 3138641) B3138641
theorem B4238743 : Blo 1393516 4238743 := bstep (se 1 (by rfl) ⟨3179057, by rfl⟩ : syracuseStep 4238743 = 6358115) B6358115
theorem B2092439 : Blo 1393516 2092439 := bstep (se 1 (by rfl) ⟨1569329, by rfl⟩ : syracuseStep 2092439 = 3138659) B3138659
theorem B5295563 : Blo 1393516 5295563 := bstep (se 1 (by rfl) ⟨3971672, by rfl⟩ : syracuseStep 5295563 = 7943345) B7943345
theorem B1764823 : Blo 1393516 1764823 := bstep (se 1 (by rfl) ⟨1323617, by rfl⟩ : syracuseStep 1764823 = 2647235) B2647235
theorem B5295577 : Blo 1393516 5295577 := bstep (se 2 (by rfl) ⟨1985841, by rfl⟩ : syracuseStep 5295577 = 3971683) B3971683
theorem B2092505 : Blo 1393516 2092505 := bstep (se 2 (by rfl) ⟨784689, by rfl⟩ : syracuseStep 2092505 = 1569379) B1569379
theorem B3018227 : Blo 1393516 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B4468247 : Blo 1393516 4468247 := bstep (se 1 (by rfl) ⟨3351185, by rfl⟩ : syracuseStep 4468247 = 6702371) B6702371
theorem B1568299 : Blo 1393516 1568299 := bstep (se 1 (by rfl) ⟨1176224, by rfl⟩ : syracuseStep 1568299 = 2352449) B2352449
theorem B2092619 : Blo 1393516 2092619 := bstep (se 1 (by rfl) ⟨1569464, by rfl⟩ : syracuseStep 2092619 = 3138929) B3138929
theorem B2092631 : Blo 1393516 2092631 := bstep (se 1 (by rfl) ⟨1569473, by rfl⟩ : syracuseStep 2092631 = 3138947) B3138947
theorem B24161885 : Blo 1393516 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B1568407 : Blo 1393516 1568407 := bstep (se 1 (by rfl) ⟨1176305, by rfl⟩ : syracuseStep 1568407 = 2352611) B2352611
theorem B4468375 : Blo 1393516 4468375 := bstep (se 1 (by rfl) ⟨3351281, by rfl⟩ : syracuseStep 4468375 = 6702563) B6702563
theorem B2092697 : Blo 1393516 2092697 := bstep (se 2 (by rfl) ⟨784761, by rfl⟩ : syracuseStep 2092697 = 1569523) B1569523
theorem B5025539 : Blo 1393516 5025539 := bstep (se 1 (by rfl) ⟨3769154, by rfl⟩ : syracuseStep 5025539 = 7538309) B7538309
theorem B2092811 : Blo 1393516 2092811 := bstep (se 1 (by rfl) ⟨1569608, by rfl⟩ : syracuseStep 2092811 = 3139217) B3139217
theorem B2092823 : Blo 1393516 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B4706099 : Blo 1393516 4706099 := bstep (se 1 (by rfl) ⟨3529574, by rfl⟩ : syracuseStep 4706099 = 7059149) B7059149
theorem B5443379 : Blo 1393516 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B1568587 : Blo 1393516 1568587 := bstep (se 1 (by rfl) ⟨1176440, by rfl⟩ : syracuseStep 1568587 = 2352881) B2352881
theorem B2092889 : Blo 1393516 2092889 := bstep (se 2 (by rfl) ⟨784833, by rfl⟩ : syracuseStep 2092889 = 1569667) B1569667
theorem B1986457 : Blo 1393516 1986457 := bstep (se 2 (by rfl) ⟨744921, by rfl⟩ : syracuseStep 1986457 = 1489843) B1489843
theorem B1568695 : Blo 1393516 1568695 := bstep (se 1 (by rfl) ⟨1176521, by rfl⟩ : syracuseStep 1568695 = 2353043) B2353043
theorem B2093003 : Blo 1393516 2093003 := bstep (se 1 (by rfl) ⟨1569752, by rfl⟩ : syracuseStep 2093003 = 3139505) B3139505
theorem B2093015 : Blo 1393516 2093015 := bstep (se 1 (by rfl) ⟨1569761, by rfl⟩ : syracuseStep 2093015 = 3139523) B3139523
theorem B2093081 : Blo 1393516 2093081 := bstep (se 2 (by rfl) ⟨784905, by rfl⟩ : syracuseStep 2093081 = 1569811) B1569811
theorem B4706369 : Blo 1393516 4706369 := bstep (se 2 (by rfl) ⟨1764888, by rfl⟩ : syracuseStep 4706369 = 3529777) B3529777
theorem B4239449 : Blo 1393516 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B1568875 : Blo 1393516 1568875 := bstep (se 1 (by rfl) ⟨1176656, by rfl⟩ : syracuseStep 1568875 = 2353313) B2353313
theorem B2093195 : Blo 1393516 2093195 := bstep (se 1 (by rfl) ⟨1569896, by rfl⟩ : syracuseStep 2093195 = 3139793) B3139793
theorem B2093207 : Blo 1393516 2093207 := bstep (se 1 (by rfl) ⟨1569905, by rfl⟩ : syracuseStep 2093207 = 3139811) B3139811
theorem B1568983 : Blo 1393516 1568983 := bstep (se 1 (by rfl) ⟨1176737, by rfl⟩ : syracuseStep 1568983 = 2353475) B2353475
theorem B2093273 : Blo 1393516 2093273 := bstep (se 2 (by rfl) ⟨784977, by rfl⟩ : syracuseStep 2093273 = 1569955) B1569955
theorem B10588481 : Blo 1393516 10588481 := bstep (se 2 (by rfl) ⟨3970680, by rfl⟩ : syracuseStep 10588481 = 7941361) B7941361
theorem B4772171 : Blo 1393516 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B1569163 : Blo 1393516 1569163 := bstep (se 1 (by rfl) ⟨1176872, by rfl⟩ : syracuseStep 1569163 = 2353745) B2353745
theorem B5296535 : Blo 1393516 5296535 := bstep (se 1 (by rfl) ⟨3972401, by rfl⟩ : syracuseStep 5296535 = 7944803) B7944803
theorem B4469195 : Blo 1393516 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B1569271 : Blo 1393516 1569271 := bstep (se 1 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 1569271 = 2353907) B2353907
theorem B2511371 : Blo 1393516 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B25432589 : Blo 1393516 25432589 := bstep (se 3 (by rfl) ⟨4768610, by rfl⟩ : syracuseStep 25432589 = 9537221) B9537221
theorem B3969587 : Blo 1393516 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B5960243 : Blo 1393516 5960243 := bstep (se 1 (by rfl) ⟨4470182, by rfl⟩ : syracuseStep 5960243 = 8940365) B8940365
theorem B3969611 : Blo 1393516 3969611 := bstep (se 1 (by rfl) ⟨2977208, by rfl⟩ : syracuseStep 3969611 = 5954417) B5954417
theorem B4706909 : Blo 1393516 4706909 := bstep (se 3 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 4706909 = 1765091) B1765091
theorem B11915869 : Blo 1393516 11915869 := bstep (se 3 (by rfl) ⟨2234225, by rfl⟩ : syracuseStep 11915869 = 4468451) B4468451
theorem B1569451 : Blo 1393516 1569451 := bstep (se 1 (by rfl) ⟨1177088, by rfl⟩ : syracuseStep 1569451 = 2354177) B2354177
theorem B3527347 : Blo 1393516 3527347 := bstep (se 1 (by rfl) ⟨2645510, by rfl⟩ : syracuseStep 3527347 = 5291021) B5291021
theorem B2978507 : Blo 1393516 2978507 := bstep (se 1 (by rfl) ⟨2233880, by rfl⟩ : syracuseStep 2978507 = 4467761) B4467761
theorem B5960395 : Blo 1393516 5960395 := bstep (se 1 (by rfl) ⟨4470296, by rfl⟩ : syracuseStep 5960395 = 8940593) B8940593
theorem B5960465 : Blo 1393516 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B1569559 : Blo 1393516 1569559 := bstep (se 1 (by rfl) ⟨1177169, by rfl⟩ : syracuseStep 1569559 = 2354339) B2354339
theorem B3527489 : Blo 1393516 3527489 := bstep (se 2 (by rfl) ⟨1322808, by rfl⟩ : syracuseStep 3527489 = 2645617) B2645617
theorem B2233163 : Blo 1393516 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2233175 : Blo 1393516 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B1569739 : Blo 1393516 1569739 := bstep (se 1 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 1569739 = 2354609) B2354609
theorem B1414135 : Blo 1393516 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B1569847 : Blo 1393516 1569847 := bstep (se 1 (by rfl) ⟨1177385, by rfl⟩ : syracuseStep 1569847 = 2354771) B2354771
theorem B3224651 : Blo 1393516 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B21468311 : Blo 1393516 21468311 := bstep (se 1 (by rfl) ⟨16101233, by rfl⟩ : syracuseStep 21468311 = 32202467) B32202467
theorem B12948659 : Blo 1393516 12948659 := bstep (se 1 (by rfl) ⟨9711494, by rfl⟩ : syracuseStep 12948659 = 19422989) B19422989
theorem B51573941 : Blo 1393516 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1488151 : Blo 1393516 1488151 := bstep (se 1 (by rfl) ⟨1116113, by rfl⟩ : syracuseStep 1488151 = 2232227) B2232227
theorem B17880365 : Blo 1393516 17880365 := bstep (se 3 (by rfl) ⟨3352568, by rfl⟩ : syracuseStep 17880365 = 6705137) B6705137
theorem B19076417 : Blo 1393516 19076417 := bstep (se 2 (by rfl) ⟨7153656, by rfl⟩ : syracuseStep 19076417 = 14307313) B14307313
theorem B3970397 : Blo 1393516 3970397 := bstep (se 3 (by rfl) ⟨744449, by rfl⟩ : syracuseStep 3970397 = 1488899) B1488899
theorem B6698371 : Blo 1393516 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B1488331 : Blo 1393516 1488331 := bstep (se 1 (by rfl) ⟨1116248, by rfl⟩ : syracuseStep 1488331 = 2232497) B2232497
theorem B2233867 : Blo 1393516 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B4838977 : Blo 1393516 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B5297795 : Blo 1393516 5297795 := bstep (se 1 (by rfl) ⟨3973346, by rfl⟩ : syracuseStep 5297795 = 7946693) B7946693
theorem B4708043 : Blo 1393516 4708043 := bstep (se 1 (by rfl) ⟨3531032, by rfl⟩ : syracuseStep 4708043 = 7062065) B7062065
theorem B2234137 : Blo 1393516 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B1611595 : Blo 1393516 1611595 := bstep (se 1 (by rfl) ⟨1208696, by rfl⟩ : syracuseStep 1611595 = 2417393) B2417393
theorem B2979737 : Blo 1393516 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B5953459 : Blo 1393516 5953459 := bstep (se 1 (by rfl) ⟨4465094, by rfl⟩ : syracuseStep 5953459 = 8930189) B8930189
theorem B4708313 : Blo 1393516 4708313 := bstep (se 2 (by rfl) ⟨1765617, by rfl⟩ : syracuseStep 4708313 = 3531235) B3531235
theorem B7059473 : Blo 1393516 7059473 := bstep (se 2 (by rfl) ⟨2647302, by rfl⟩ : syracuseStep 7059473 = 5294605) B5294605
theorem B2234393 : Blo 1393516 2234393 := bstep (se 2 (by rfl) ⟨837897, by rfl⟩ : syracuseStep 2234393 = 1675795) B1675795
theorem B3528755 : Blo 1393516 3528755 := bstep (se 1 (by rfl) ⟨2646566, by rfl⟩ : syracuseStep 3528755 = 5293133) B5293133
theorem B3135563 : Blo 1393516 3135563 := bstep (se 1 (by rfl) ⟨2351672, by rfl⟩ : syracuseStep 3135563 = 4703345) B4703345
theorem B3135617 : Blo 1393516 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B7059635 : Blo 1393516 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B10590425 : Blo 1393516 10590425 := bstep (se 2 (by rfl) ⟨3971409, by rfl⟩ : syracuseStep 10590425 = 7942819) B7942819
theorem B2980147 : Blo 1393516 2980147 := bstep (se 1 (by rfl) ⟨2235110, by rfl⟩ : syracuseStep 2980147 = 4470221) B4470221
theorem B5028161 : Blo 1393516 5028161 := bstep (se 2 (by rfl) ⟨1885560, by rfl⟩ : syracuseStep 5028161 = 3771121) B3771121
theorem B3135833 : Blo 1393516 3135833 := bstep (se 2 (by rfl) ⟨1175937, by rfl⟩ : syracuseStep 3135833 = 2351875) B2351875
theorem B3135923 : Blo 1393516 3135923 := bstep (se 1 (by rfl) ⟨2351942, by rfl⟩ : syracuseStep 3135923 = 4703885) B4703885
theorem B3135959 : Blo 1393516 3135959 := bstep (se 1 (by rfl) ⟨2351969, by rfl⟩ : syracuseStep 3135959 = 4703939) B4703939
theorem B5954093 : Blo 1393516 5954093 := bstep (se 3 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 5954093 = 2232785) B2232785
theorem B2980403 : Blo 1393516 2980403 := bstep (se 1 (by rfl) ⟨2235302, by rfl⟩ : syracuseStep 2980403 = 4470605) B4470605
theorem B3529291 : Blo 1393516 3529291 := bstep (se 1 (by rfl) ⟨2646968, by rfl⟩ : syracuseStep 3529291 = 5293937) B5293937
theorem B3136139 : Blo 1393516 3136139 := bstep (se 1 (by rfl) ⟨2352104, by rfl⟩ : syracuseStep 3136139 = 4704209) B4704209
theorem B4709015 : Blo 1393516 4709015 := bstep (se 1 (by rfl) ⟨3531761, by rfl⟩ : syracuseStep 4709015 = 7063523) B7063523
theorem B3136193 : Blo 1393516 3136193 := bstep (se 2 (by rfl) ⟨1176072, by rfl⟩ : syracuseStep 3136193 = 2352145) B2352145
theorem B3529433 : Blo 1393516 3529433 := bstep (se 2 (by rfl) ⟨1323537, by rfl⟩ : syracuseStep 3529433 = 2647075) B2647075
theorem B2235097 : Blo 1393516 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B2513729 : Blo 1393516 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B3136409 : Blo 1393516 3136409 := bstep (se 2 (by rfl) ⟨1176153, by rfl⟩ : syracuseStep 3136409 = 2352307) B2352307
theorem B3136499 : Blo 1393516 3136499 := bstep (se 1 (by rfl) ⟨2352374, by rfl⟩ : syracuseStep 3136499 = 4704749) B4704749
theorem B2825227 : Blo 1393516 2825227 := bstep (se 1 (by rfl) ⟨2118920, by rfl⟩ : syracuseStep 2825227 = 4237841) B4237841
theorem B3136535 : Blo 1393516 3136535 := bstep (se 1 (by rfl) ⟨2352401, by rfl⟩ : syracuseStep 3136535 = 4704803) B4704803
theorem B3972185 : Blo 1393516 3972185 := bstep (se 2 (by rfl) ⟨1489569, by rfl⟩ : syracuseStep 3972185 = 2979139) B2979139
theorem B4709555 : Blo 1393516 4709555 := bstep (se 1 (by rfl) ⟨3532166, by rfl⟩ : syracuseStep 4709555 = 7064333) B7064333
theorem B3767489 : Blo 1393516 3767489 := bstep (se 2 (by rfl) ⟨1412808, by rfl⟩ : syracuseStep 3767489 = 2825617) B2825617
theorem B3136715 : Blo 1393516 3136715 := bstep (se 1 (by rfl) ⟨2352536, by rfl⟩ : syracuseStep 3136715 = 4705073) B4705073
theorem B3136769 : Blo 1393516 3136769 := bstep (se 2 (by rfl) ⟨1176288, by rfl⟩ : syracuseStep 3136769 = 2352577) B2352577
theorem B3767575 : Blo 1393516 3767575 := bstep (se 1 (by rfl) ⟨2825681, by rfl⟩ : syracuseStep 3767575 = 5651363) B5651363
theorem B10190231 : Blo 1393516 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B3972503 : Blo 1393516 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B4709825 : Blo 1393516 4709825 := bstep (se 2 (by rfl) ⟨1766184, by rfl⟩ : syracuseStep 4709825 = 3532369) B3532369
theorem B2825675 : Blo 1393516 2825675 := bstep (se 1 (by rfl) ⟨2119256, by rfl⟩ : syracuseStep 2825675 = 4238513) B4238513
theorem B3136985 : Blo 1393516 3136985 := bstep (se 2 (by rfl) ⟨1176369, by rfl⟩ : syracuseStep 3136985 = 2352739) B2352739
theorem B3530263 : Blo 1393516 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B3137075 : Blo 1393516 3137075 := bstep (se 1 (by rfl) ⟨2352806, by rfl⟩ : syracuseStep 3137075 = 4705613) B4705613
theorem B3137111 : Blo 1393516 3137111 := bstep (se 1 (by rfl) ⟨2352833, by rfl⟩ : syracuseStep 3137111 = 4705667) B4705667
theorem B45244109 : Blo 1393516 45244109 := bstep (se 3 (by rfl) ⟨8483270, by rfl⟩ : syracuseStep 45244109 = 16966541) B16966541
theorem B3137291 : Blo 1393516 3137291 := bstep (se 1 (by rfl) ⟨2352968, by rfl⟩ : syracuseStep 3137291 = 4705937) B4705937
theorem B3137345 : Blo 1393516 3137345 := bstep (se 2 (by rfl) ⟨1176504, by rfl⟩ : syracuseStep 3137345 = 2353009) B2353009
theorem B15531841 : Blo 1393516 15531841 := bstep (se 2 (by rfl) ⟨5824440, by rfl⟩ : syracuseStep 15531841 = 11648881) B11648881
theorem B2645875 : Blo 1393516 2645875 := bstep (se 1 (by rfl) ⟨1984406, by rfl⟩ : syracuseStep 2645875 = 3968813) B3968813
theorem B3530699 : Blo 1393516 3530699 := bstep (se 1 (by rfl) ⟨2648024, by rfl⟩ : syracuseStep 3530699 = 5296049) B5296049
theorem B5291993 : Blo 1393516 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B1589263 : Blo 1393516 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B6365213 : Blo 1393516 6365213 := bstep (se 3 (by rfl) ⟨1193477, by rfl⟩ : syracuseStep 6365213 = 2386955) B2386955
theorem B3137579 : Blo 1393516 3137579 := bstep (se 1 (by rfl) ⟨2353184, by rfl⟩ : syracuseStep 3137579 = 4706369) B4706369
theorem B2826299 : Blo 1393516 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B4243571 : Blo 1393516 4243571 := bstep (se 1 (by rfl) ⟨3182678, by rfl⟩ : syracuseStep 4243571 = 6365357) B6365357
theorem B7061741 : Blo 1393516 7061741 := bstep (se 3 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 7061741 = 2648153) B2648153
theorem B3531023 : Blo 1393516 3531023 := bstep (se 1 (by rfl) ⟨2648267, by rfl⟩ : syracuseStep 3531023 = 5296535) B5296535
theorem B1884475 : Blo 1393516 1884475 := bstep (se 1 (by rfl) ⟨1413356, by rfl⟩ : syracuseStep 1884475 = 2826713) B2826713
theorem B3973495 : Blo 1393516 3973495 := bstep (se 1 (by rfl) ⟨2980121, by rfl⟩ : syracuseStep 3973495 = 5960243) B5960243
theorem B2646407 : Blo 1393516 2646407 := bstep (se 1 (by rfl) ⟨1984805, by rfl⟩ : syracuseStep 2646407 = 3969611) B3969611
theorem B6701447 : Blo 1393516 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B3137939 : Blo 1393516 3137939 := bstep (se 1 (by rfl) ⟨2353454, by rfl⟩ : syracuseStep 3137939 = 4706909) B4706909
theorem B3973529 : Blo 1393516 3973529 := bstep (se 2 (by rfl) ⟨1490073, by rfl⟩ : syracuseStep 3973529 = 2980147) B2980147
theorem B3137993 : Blo 1393516 3137993 := bstep (se 2 (by rfl) ⟨1176747, by rfl⟩ : syracuseStep 3137993 = 2353495) B2353495
theorem B3973643 : Blo 1393516 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B2351659 : Blo 1393516 2351659 := bstep (se 1 (by rfl) ⟨1763744, by rfl⟩ : syracuseStep 2351659 = 3527489) B3527489
theorem B2351801 : Blo 1393516 2351801 := bstep (se 2 (by rfl) ⟨881925, by rfl⟩ : syracuseStep 2351801 = 1763851) B1763851
theorem B14312207 : Blo 1393516 14312207 := bstep (se 1 (by rfl) ⟨10734155, by rfl⟩ : syracuseStep 14312207 = 21468311) B21468311
theorem B34382627 : Blo 1393516 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B60318553 : Blo 1393516 60318553 := bstep (se 2 (by rfl) ⟨22619457, by rfl⟩ : syracuseStep 60318553 = 45238915) B45238915
theorem B11920243 : Blo 1393516 11920243 := bstep (se 1 (by rfl) ⟨8940182, by rfl⟩ : syracuseStep 11920243 = 17880365) B17880365
theorem B1393543 : Blo 1393516 1393543 := bstep (se 1 (by rfl) ⟨1045157, by rfl⟩ : syracuseStep 1393543 = 2090315) B2090315
theorem B5292935 : Blo 1393516 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B1393551 : Blo 1393516 1393551 := bstep (se 1 (by rfl) ⟨1045163, by rfl⟩ : syracuseStep 1393551 = 2090327) B2090327
theorem B2646931 : Blo 1393516 2646931 := bstep (se 1 (by rfl) ⟨1985198, by rfl⟩ : syracuseStep 2646931 = 3970397) B3970397
theorem B4703129 : Blo 1393516 4703129 := bstep (se 2 (by rfl) ⟨1763673, by rfl⟩ : syracuseStep 4703129 = 3527347) B3527347
theorem B7947193 : Blo 1393516 7947193 := bstep (se 2 (by rfl) ⟨2980197, by rfl⟩ : syracuseStep 7947193 = 5960395) B5960395
theorem B1393595 : Blo 1393516 1393595 := bstep (se 1 (by rfl) ⟨1045196, by rfl⟩ : syracuseStep 1393595 = 2090393) B2090393
theorem B3531721 : Blo 1393516 3531721 := bstep (se 2 (by rfl) ⟨1324395, by rfl⟩ : syracuseStep 3531721 = 2648791) B2648791
theorem B1393671 : Blo 1393516 1393671 := bstep (se 1 (by rfl) ⟨1045253, by rfl⟩ : syracuseStep 1393671 = 2090507) B2090507
theorem B1393679 : Blo 1393516 1393679 := bstep (se 1 (by rfl) ⟨1045259, by rfl⟩ : syracuseStep 1393679 = 2090519) B2090519
theorem B7062551 : Blo 1393516 7062551 := bstep (se 1 (by rfl) ⟨5296913, by rfl⟩ : syracuseStep 7062551 = 10593827) B10593827
theorem B1393723 : Blo 1393516 1393723 := bstep (se 1 (by rfl) ⟨1045292, by rfl⟩ : syracuseStep 1393723 = 2090585) B2090585
theorem B10593341 : Blo 1393516 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B3531863 : Blo 1393516 3531863 := bstep (se 1 (by rfl) ⟨2648897, by rfl⟩ : syracuseStep 3531863 = 5297795) B5297795
theorem B11920517 : Blo 1393516 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B1393799 : Blo 1393516 1393799 := bstep (se 1 (by rfl) ⟨1045349, by rfl⟩ : syracuseStep 1393799 = 2090699) B2090699
theorem B3138695 : Blo 1393516 3138695 := bstep (se 1 (by rfl) ⟨2354021, by rfl⟩ : syracuseStep 3138695 = 4708043) B4708043
theorem B1393807 : Blo 1393516 1393807 := bstep (se 1 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 1393807 = 2090711) B2090711
theorem B1393851 : Blo 1393516 1393851 := bstep (se 1 (by rfl) ⟨1045388, by rfl⟩ : syracuseStep 1393851 = 2090777) B2090777
theorem B1393927 : Blo 1393516 1393927 := bstep (se 1 (by rfl) ⟨1045445, by rfl⟩ : syracuseStep 1393927 = 2090891) B2090891
theorem B1393935 : Blo 1393516 1393935 := bstep (se 1 (by rfl) ⟨1045451, by rfl⟩ : syracuseStep 1393935 = 2090903) B2090903
theorem B2090297 : Blo 1393516 2090297 := bstep (se 2 (by rfl) ⟨783861, by rfl⟩ : syracuseStep 2090297 = 1567723) B1567723
theorem B1393979 : Blo 1393516 1393979 := bstep (se 1 (by rfl) ⟨1045484, by rfl⟩ : syracuseStep 1393979 = 2090969) B2090969
theorem B3138875 : Blo 1393516 3138875 := bstep (se 1 (by rfl) ⟨2354156, by rfl⟩ : syracuseStep 3138875 = 4708313) B4708313
theorem B1885513 : Blo 1393516 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B171738481 : Blo 1393516 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B2352503 : Blo 1393516 2352503 := bstep (se 1 (by rfl) ⟨1764377, by rfl⟩ : syracuseStep 2352503 = 3528755) B3528755
theorem B2090375 : Blo 1393516 2090375 := bstep (se 1 (by rfl) ⟨1567781, by rfl⟩ : syracuseStep 2090375 = 3135563) B3135563
theorem B1394055 : Blo 1393516 1394055 := bstep (se 1 (by rfl) ⟨1045541, by rfl⟩ : syracuseStep 1394055 = 2091083) B2091083
theorem B1394063 : Blo 1393516 1394063 := bstep (se 1 (by rfl) ⟨1045547, by rfl⟩ : syracuseStep 1394063 = 2091095) B2091095
theorem B2090411 : Blo 1393516 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B11306425 : Blo 1393516 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B1394107 : Blo 1393516 1394107 := bstep (se 1 (by rfl) ⟨1045580, by rfl⟩ : syracuseStep 1394107 = 2091161) B2091161
theorem B3139001 : Blo 1393516 3139001 := bstep (se 2 (by rfl) ⟨1177125, by rfl⟩ : syracuseStep 3139001 = 2354251) B2354251
theorem B2090441 : Blo 1393516 2090441 := bstep (se 2 (by rfl) ⟨783915, by rfl⟩ : syracuseStep 2090441 = 1567831) B1567831
theorem B10585565 : Blo 1393516 10585565 := bstep (se 3 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 10585565 = 3969587) B3969587
theorem B7538179 : Blo 1393516 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B1394183 : Blo 1393516 1394183 := bstep (se 1 (by rfl) ⟨1045637, by rfl⟩ : syracuseStep 1394183 = 2091275) B2091275
theorem B1394191 : Blo 1393516 1394191 := bstep (se 1 (by rfl) ⟨1045643, by rfl⟩ : syracuseStep 1394191 = 2091287) B2091287
theorem B2090555 : Blo 1393516 2090555 := bstep (se 1 (by rfl) ⟨1567916, by rfl⟩ : syracuseStep 2090555 = 3135833) B3135833
theorem B1394235 : Blo 1393516 1394235 := bstep (se 1 (by rfl) ⟨1045676, by rfl⟩ : syracuseStep 1394235 = 2091353) B2091353
theorem B4703831 : Blo 1393516 4703831 := bstep (se 1 (by rfl) ⟨3527873, by rfl⟩ : syracuseStep 4703831 = 7055747) B7055747
theorem B2090615 : Blo 1393516 2090615 := bstep (se 1 (by rfl) ⟨1567961, by rfl⟩ : syracuseStep 2090615 = 3135923) B3135923
theorem B1394311 : Blo 1393516 1394311 := bstep (se 1 (by rfl) ⟨1045733, by rfl⟩ : syracuseStep 1394311 = 2091467) B2091467
theorem B2090639 : Blo 1393516 2090639 := bstep (se 1 (by rfl) ⟨1567979, by rfl⟩ : syracuseStep 2090639 = 3135959) B3135959
theorem B1394319 : Blo 1393516 1394319 := bstep (se 1 (by rfl) ⟨1045739, by rfl⟩ : syracuseStep 1394319 = 2091479) B2091479
theorem B2090681 : Blo 1393516 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B1394363 : Blo 1393516 1394363 := bstep (se 1 (by rfl) ⟨1045772, by rfl⟩ : syracuseStep 1394363 = 2091545) B2091545
theorem B5023433 : Blo 1393516 5023433 := bstep (se 2 (by rfl) ⟨1883787, by rfl⟩ : syracuseStep 5023433 = 3767575) B3767575
theorem B8595173 : Blo 1393516 8595173 := bstep (se 4 (by rfl) ⟨805797, by rfl⟩ : syracuseStep 8595173 = 1611595) B1611595
theorem B2090759 : Blo 1393516 2090759 := bstep (se 1 (by rfl) ⟨1568069, by rfl⟩ : syracuseStep 2090759 = 3136139) B3136139
theorem B1394439 : Blo 1393516 1394439 := bstep (se 1 (by rfl) ⟨1045829, by rfl⟩ : syracuseStep 1394439 = 2091659) B2091659
theorem B1394447 : Blo 1393516 1394447 := bstep (se 1 (by rfl) ⟨1045835, by rfl⟩ : syracuseStep 1394447 = 2091671) B2091671
theorem B3139343 : Blo 1393516 3139343 := bstep (se 1 (by rfl) ⟨2354507, by rfl⟩ : syracuseStep 3139343 = 4709015) B4709015
theorem B3139361 : Blo 1393516 3139361 := bstep (se 2 (by rfl) ⟨1177260, by rfl⟩ : syracuseStep 3139361 = 2354521) B2354521
theorem B2090795 : Blo 1393516 2090795 := bstep (se 1 (by rfl) ⟨1568096, by rfl⟩ : syracuseStep 2090795 = 3136193) B3136193
theorem B11921201 : Blo 1393516 11921201 := bstep (se 2 (by rfl) ⟨4470450, by rfl⟩ : syracuseStep 11921201 = 8940901) B8940901
theorem B2352955 : Blo 1393516 2352955 := bstep (se 1 (by rfl) ⟨1764716, by rfl⟩ : syracuseStep 2352955 = 3529433) B3529433
theorem B1394491 : Blo 1393516 1394491 := bstep (se 1 (by rfl) ⟨1045868, by rfl⟩ : syracuseStep 1394491 = 2091737) B2091737
theorem B2090825 : Blo 1393516 2090825 := bstep (se 2 (by rfl) ⟨784059, by rfl⟩ : syracuseStep 2090825 = 1568119) B1568119
theorem B8931161 : Blo 1393516 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B1394567 : Blo 1393516 1394567 := bstep (se 1 (by rfl) ⟨1045925, by rfl⟩ : syracuseStep 1394567 = 2091851) B2091851
theorem B1394575 : Blo 1393516 1394575 := bstep (se 1 (by rfl) ⟨1045931, by rfl⟩ : syracuseStep 1394575 = 2091863) B2091863
theorem B1984441 : Blo 1393516 1984441 := bstep (se 2 (by rfl) ⟨744165, by rfl⟩ : syracuseStep 1984441 = 1488331) B1488331
theorem B2090939 : Blo 1393516 2090939 := bstep (se 1 (by rfl) ⟨1568204, by rfl⟩ : syracuseStep 2090939 = 3136409) B3136409
theorem B1394619 : Blo 1393516 1394619 := bstep (se 1 (by rfl) ⟨1045964, by rfl⟩ : syracuseStep 1394619 = 2091929) B2091929
theorem B2353097 : Blo 1393516 2353097 := bstep (se 2 (by rfl) ⟨882411, by rfl⟩ : syracuseStep 2353097 = 1764823) B1764823
theorem B2090999 : Blo 1393516 2090999 := bstep (se 1 (by rfl) ⟨1568249, by rfl⟩ : syracuseStep 2090999 = 3136499) B3136499
theorem B1394695 : Blo 1393516 1394695 := bstep (se 1 (by rfl) ⟨1046021, by rfl⟩ : syracuseStep 1394695 = 2092043) B2092043
theorem B2091023 : Blo 1393516 2091023 := bstep (se 1 (by rfl) ⟨1568267, by rfl⟩ : syracuseStep 2091023 = 3136535) B3136535
theorem B1394703 : Blo 1393516 1394703 := bstep (se 1 (by rfl) ⟨1046027, by rfl⟩ : syracuseStep 1394703 = 2092055) B2092055
theorem B2091065 : Blo 1393516 2091065 := bstep (se 2 (by rfl) ⟨784149, by rfl⟩ : syracuseStep 2091065 = 1568299) B1568299
theorem B1394747 : Blo 1393516 1394747 := bstep (se 1 (by rfl) ⟨1046060, by rfl⟩ : syracuseStep 1394747 = 2092121) B2092121
theorem B2648123 : Blo 1393516 2648123 := bstep (se 1 (by rfl) ⟨1986092, by rfl⟩ : syracuseStep 2648123 = 3972185) B3972185
theorem B4704317 : Blo 1393516 4704317 := bstep (se 3 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 4704317 = 1764119) B1764119
theorem B3139703 : Blo 1393516 3139703 := bstep (se 1 (by rfl) ⟨2354777, by rfl⟩ : syracuseStep 3139703 = 4709555) B4709555
theorem B11462789 : Blo 1393516 11462789 := bstep (se 4 (by rfl) ⟨1074636, by rfl⟩ : syracuseStep 11462789 = 2149273) B2149273
theorem B2091143 : Blo 1393516 2091143 := bstep (se 1 (by rfl) ⟨1568357, by rfl⟩ : syracuseStep 2091143 = 3136715) B3136715
theorem B1394823 : Blo 1393516 1394823 := bstep (se 1 (by rfl) ⟨1046117, by rfl⟩ : syracuseStep 1394823 = 2092235) B2092235
theorem B1394831 : Blo 1393516 1394831 := bstep (se 1 (by rfl) ⟨1046123, by rfl⟩ : syracuseStep 1394831 = 2092247) B2092247
theorem B2091179 : Blo 1393516 2091179 := bstep (se 1 (by rfl) ⟨1568384, by rfl⟩ : syracuseStep 2091179 = 3136769) B3136769
theorem B1394875 : Blo 1393516 1394875 := bstep (se 1 (by rfl) ⟨1046156, by rfl⟩ : syracuseStep 1394875 = 2092313) B2092313
theorem B2091209 : Blo 1393516 2091209 := bstep (se 2 (by rfl) ⟨784203, by rfl⟩ : syracuseStep 2091209 = 1568407) B1568407
theorem B5957833 : Blo 1393516 5957833 := bstep (se 2 (by rfl) ⟨2234187, by rfl⟩ : syracuseStep 5957833 = 4468375) B4468375
theorem B1394951 : Blo 1393516 1394951 := bstep (se 1 (by rfl) ⟨1046213, by rfl⟩ : syracuseStep 1394951 = 2092427) B2092427
theorem B6793487 : Blo 1393516 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B1394959 : Blo 1393516 1394959 := bstep (se 1 (by rfl) ⟨1046219, by rfl⟩ : syracuseStep 1394959 = 2092439) B2092439
theorem B3139883 : Blo 1393516 3139883 := bstep (se 1 (by rfl) ⟨2354912, by rfl⟩ : syracuseStep 3139883 = 4709825) B4709825
theorem B2091323 : Blo 1393516 2091323 := bstep (se 1 (by rfl) ⟨1568492, by rfl⟩ : syracuseStep 2091323 = 3136985) B3136985
theorem B1395003 : Blo 1393516 1395003 := bstep (se 1 (by rfl) ⟨1046252, by rfl⟩ : syracuseStep 1395003 = 2092505) B2092505
theorem B2091383 : Blo 1393516 2091383 := bstep (se 1 (by rfl) ⟨1568537, by rfl⟩ : syracuseStep 2091383 = 3137075) B3137075
theorem B1395079 : Blo 1393516 1395079 := bstep (se 1 (by rfl) ⟨1046309, by rfl⟩ : syracuseStep 1395079 = 2092619) B2092619
theorem B2091407 : Blo 1393516 2091407 := bstep (se 1 (by rfl) ⟨1568555, by rfl⟩ : syracuseStep 2091407 = 3137111) B3137111
theorem B1395087 : Blo 1393516 1395087 := bstep (se 1 (by rfl) ⟨1046315, by rfl⟩ : syracuseStep 1395087 = 2092631) B2092631
theorem B16107923 : Blo 1393516 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B2091449 : Blo 1393516 2091449 := bstep (se 2 (by rfl) ⟨784293, by rfl⟩ : syracuseStep 2091449 = 1568587) B1568587
theorem B1395131 : Blo 1393516 1395131 := bstep (se 1 (by rfl) ⟨1046348, by rfl⟩ : syracuseStep 1395131 = 2092697) B2092697
theorem B2091527 : Blo 1393516 2091527 := bstep (se 1 (by rfl) ⟨1568645, by rfl⟩ : syracuseStep 2091527 = 3137291) B3137291
theorem B1395207 : Blo 1393516 1395207 := bstep (se 1 (by rfl) ⟨1046405, by rfl⟩ : syracuseStep 1395207 = 2092811) B2092811
theorem B1395215 : Blo 1393516 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B2648609 : Blo 1393516 2648609 := bstep (se 2 (by rfl) ⟨993228, by rfl⟩ : syracuseStep 2648609 = 1986457) B1986457
theorem B2091563 : Blo 1393516 2091563 := bstep (se 1 (by rfl) ⟨1568672, by rfl⟩ : syracuseStep 2091563 = 3137345) B3137345
theorem B1395259 : Blo 1393516 1395259 := bstep (se 1 (by rfl) ⟨1046444, by rfl⟩ : syracuseStep 1395259 = 2092889) B2092889
theorem B2091593 : Blo 1393516 2091593 := bstep (se 2 (by rfl) ⟨784347, by rfl⟩ : syracuseStep 2091593 = 1568695) B1568695
theorem B2353799 : Blo 1393516 2353799 := bstep (se 1 (by rfl) ⟨1765349, by rfl⟩ : syracuseStep 2353799 = 3530699) B3530699
theorem B1395335 : Blo 1393516 1395335 := bstep (se 1 (by rfl) ⟨1046501, by rfl⟩ : syracuseStep 1395335 = 2093003) B2093003
theorem B1395343 : Blo 1393516 1395343 := bstep (se 1 (by rfl) ⟨1046507, by rfl⟩ : syracuseStep 1395343 = 2093015) B2093015
theorem B2091707 : Blo 1393516 2091707 := bstep (se 1 (by rfl) ⟨1568780, by rfl⟩ : syracuseStep 2091707 = 3137561) B3137561
theorem B1395387 : Blo 1393516 1395387 := bstep (se 1 (by rfl) ⟨1046540, by rfl⟩ : syracuseStep 1395387 = 2093081) B2093081
theorem B2091767 : Blo 1393516 2091767 := bstep (se 1 (by rfl) ⟨1568825, by rfl⟩ : syracuseStep 2091767 = 3137651) B3137651
theorem B1395463 : Blo 1393516 1395463 := bstep (se 1 (by rfl) ⟨1046597, by rfl⟩ : syracuseStep 1395463 = 2093195) B2093195
theorem B2091791 : Blo 1393516 2091791 := bstep (se 1 (by rfl) ⟨1568843, by rfl⟩ : syracuseStep 2091791 = 3137687) B3137687
theorem B1395471 : Blo 1393516 1395471 := bstep (se 1 (by rfl) ⟨1046603, by rfl⟩ : syracuseStep 1395471 = 2093207) B2093207
theorem B2648875 : Blo 1393516 2648875 := bstep (se 1 (by rfl) ⟨1986656, by rfl⟩ : syracuseStep 2648875 = 3973313) B3973313
theorem B2091833 : Blo 1393516 2091833 := bstep (se 2 (by rfl) ⟨784437, by rfl⟩ : syracuseStep 2091833 = 1568875) B1568875
theorem B1395515 : Blo 1393516 1395515 := bstep (se 1 (by rfl) ⟨1046636, by rfl⟩ : syracuseStep 1395515 = 2093273) B2093273
theorem B2091911 : Blo 1393516 2091911 := bstep (se 1 (by rfl) ⟨1568933, by rfl⟩ : syracuseStep 2091911 = 3137867) B3137867
theorem B3181447 : Blo 1393516 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B2091947 : Blo 1393516 2091947 := bstep (se 1 (by rfl) ⟨1568960, by rfl⟩ : syracuseStep 2091947 = 3137921) B3137921
theorem B2091977 : Blo 1393516 2091977 := bstep (se 2 (by rfl) ⟨784491, by rfl⟩ : syracuseStep 2091977 = 1568983) B1568983
theorem B7056395 : Blo 1393516 7056395 := bstep (se 1 (by rfl) ⟨5292296, by rfl⟩ : syracuseStep 7056395 = 10584593) B10584593
theorem B1567759 : Blo 1393516 1567759 := bstep (se 1 (by rfl) ⟨1175819, by rfl⟩ : syracuseStep 1567759 = 2351639) B2351639
theorem B13397015 : Blo 1393516 13397015 := bstep (se 1 (by rfl) ⟨10047761, by rfl⟩ : syracuseStep 13397015 = 20095523) B20095523
theorem B2092091 : Blo 1393516 2092091 := bstep (se 1 (by rfl) ⟨1569068, by rfl⟩ : syracuseStep 2092091 = 3138137) B3138137
theorem B2092151 : Blo 1393516 2092151 := bstep (se 1 (by rfl) ⟨1569113, by rfl⟩ : syracuseStep 2092151 = 3138227) B3138227
theorem B1985671 : Blo 1393516 1985671 := bstep (se 1 (by rfl) ⟨1489253, by rfl⟩ : syracuseStep 1985671 = 2978507) B2978507
theorem B2092175 : Blo 1393516 2092175 := bstep (se 1 (by rfl) ⟨1569131, by rfl⟩ : syracuseStep 2092175 = 3138263) B3138263
theorem B7056557 : Blo 1393516 7056557 := bstep (se 3 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 7056557 = 2646209) B2646209
theorem B2092217 : Blo 1393516 2092217 := bstep (se 2 (by rfl) ⟨784581, by rfl⟩ : syracuseStep 2092217 = 1569163) B1569163
theorem B2092295 : Blo 1393516 2092295 := bstep (se 1 (by rfl) ⟨1569221, by rfl⟩ : syracuseStep 2092295 = 3138443) B3138443
theorem B2354447 : Blo 1393516 2354447 := bstep (se 1 (by rfl) ⟨1765835, by rfl⟩ : syracuseStep 2354447 = 3531671) B3531671
theorem B2092331 : Blo 1393516 2092331 := bstep (se 1 (by rfl) ⟨1569248, by rfl⟩ : syracuseStep 2092331 = 3138497) B3138497
theorem B2092361 : Blo 1393516 2092361 := bstep (se 2 (by rfl) ⟨784635, by rfl⟩ : syracuseStep 2092361 = 1569271) B1569271
theorem B4705721 : Blo 1393516 4705721 := bstep (se 2 (by rfl) ⟨1764645, by rfl⟩ : syracuseStep 4705721 = 3529291) B3529291
theorem B2092475 : Blo 1393516 2092475 := bstep (se 1 (by rfl) ⟨1569356, by rfl⟩ : syracuseStep 2092475 = 3138713) B3138713
theorem B15887825 : Blo 1393516 15887825 := bstep (se 2 (by rfl) ⟨5957934, by rfl⟩ : syracuseStep 15887825 = 11915869) B11915869
theorem B2092535 : Blo 1393516 2092535 := bstep (se 1 (by rfl) ⟨1569401, by rfl⟩ : syracuseStep 2092535 = 3138803) B3138803
theorem B7941635 : Blo 1393516 7941635 := bstep (se 1 (by rfl) ⟨5956226, by rfl⟩ : syracuseStep 7941635 = 11912453) B11912453
theorem B1568263 : Blo 1393516 1568263 := bstep (se 1 (by rfl) ⟨1176197, by rfl⟩ : syracuseStep 1568263 = 2352395) B2352395
theorem B2092559 : Blo 1393516 2092559 := bstep (se 1 (by rfl) ⟨1569419, by rfl⟩ : syracuseStep 2092559 = 3138839) B3138839
theorem B12717611 : Blo 1393516 12717611 := bstep (se 1 (by rfl) ⟨9538208, by rfl⟩ : syracuseStep 12717611 = 19076417) B19076417
theorem B2092601 : Blo 1393516 2092601 := bstep (se 2 (by rfl) ⟨784725, by rfl⟩ : syracuseStep 2092601 = 1569451) B1569451
theorem B2092679 : Blo 1393516 2092679 := bstep (se 1 (by rfl) ⟨1569509, by rfl⟩ : syracuseStep 2092679 = 3139019) B3139019
theorem B114429581 : Blo 1393516 114429581 := bstep (se 3 (by rfl) ⟨21455546, by rfl⟩ : syracuseStep 114429581 = 42911093) B42911093
theorem B2092715 : Blo 1393516 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B1568443 : Blo 1393516 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B4525769 : Blo 1393516 4525769 := bstep (se 2 (by rfl) ⟨1697163, by rfl⟩ : syracuseStep 4525769 = 3394327) B3394327
theorem B2092745 : Blo 1393516 2092745 := bstep (se 2 (by rfl) ⟨784779, by rfl⟩ : syracuseStep 2092745 = 1569559) B1569559
theorem B5959439 : Blo 1393516 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B10055461 : Blo 1393516 10055461 := bstep (se 4 (by rfl) ⟨942699, by rfl⟩ : syracuseStep 10055461 = 1885399) B1885399
theorem B2682683 : Blo 1393516 2682683 := bstep (se 1 (by rfl) ⟨2012012, by rfl⟩ : syracuseStep 2682683 = 4024025) B4024025
theorem B2092859 : Blo 1393516 2092859 := bstep (se 1 (by rfl) ⟨1569644, by rfl⟩ : syracuseStep 2092859 = 3139289) B3139289
theorem B2092919 : Blo 1393516 2092919 := bstep (se 1 (by rfl) ⟨1569689, by rfl⟩ : syracuseStep 2092919 = 3139379) B3139379
theorem B2092943 : Blo 1393516 2092943 := bstep (se 1 (by rfl) ⟨1569707, by rfl⟩ : syracuseStep 2092943 = 3139415) B3139415
theorem B2092985 : Blo 1393516 2092985 := bstep (se 2 (by rfl) ⟨784869, by rfl⟩ : syracuseStep 2092985 = 1569739) B1569739
theorem B1986491 : Blo 1393516 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B8048605 : Blo 1393516 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B2093063 : Blo 1393516 2093063 := bstep (se 1 (by rfl) ⟨1569797, by rfl⟩ : syracuseStep 2093063 = 3139595) B3139595
theorem B4706315 : Blo 1393516 4706315 := bstep (se 1 (by rfl) ⟨3529736, by rfl⟩ : syracuseStep 4706315 = 7059473) B7059473
theorem B6696989 : Blo 1393516 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B2093099 : Blo 1393516 2093099 := bstep (se 1 (by rfl) ⟨1569824, by rfl⟩ : syracuseStep 2093099 = 3139649) B3139649
theorem B2093129 : Blo 1393516 2093129 := bstep (se 2 (by rfl) ⟨784923, by rfl⟩ : syracuseStep 2093129 = 1569847) B1569847
theorem B4706423 : Blo 1393516 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B1568911 : Blo 1393516 1568911 := bstep (se 1 (by rfl) ⟨1176683, by rfl⟩ : syracuseStep 1568911 = 2353367) B2353367
theorem B2093243 : Blo 1393516 2093243 := bstep (se 1 (by rfl) ⟨1569932, by rfl⟩ : syracuseStep 2093243 = 3139865) B3139865
theorem B7156001 : Blo 1393516 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B3969395 : Blo 1393516 3969395 := bstep (se 1 (by rfl) ⟨2977046, by rfl⟩ : syracuseStep 3969395 = 5954093) B5954093
theorem B1986935 : Blo 1393516 1986935 := bstep (se 1 (by rfl) ⟨1490201, by rfl⟩ : syracuseStep 1986935 = 2980403) B2980403
theorem B10596743 : Blo 1393516 10596743 := bstep (se 1 (by rfl) ⟨7947557, by rfl⟩ : syracuseStep 10596743 = 15895115) B15895115
theorem B1675819 : Blo 1393516 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B1569415 : Blo 1393516 1569415 := bstep (se 1 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 1569415 = 2354123) B2354123
theorem B2978489 : Blo 1393516 2978489 := bstep (se 2 (by rfl) ⟨1116933, by rfl⟩ : syracuseStep 2978489 = 2233867) B2233867
theorem B4707017 : Blo 1393516 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B7058177 : Blo 1393516 7058177 := bstep (se 2 (by rfl) ⟨2646816, by rfl⟩ : syracuseStep 7058177 = 5293633) B5293633
theorem B6451969 : Blo 1393516 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B2511659 : Blo 1393516 2511659 := bstep (se 1 (by rfl) ⟨1883744, by rfl⟩ : syracuseStep 2511659 = 3767489) B3767489
theorem B1569595 : Blo 1393516 1569595 := bstep (se 1 (by rfl) ⟨1177196, by rfl⟩ : syracuseStep 1569595 = 2354393) B2354393
theorem B2978831 : Blo 1393516 2978831 := bstep (se 1 (by rfl) ⟨2234123, by rfl⟩ : syracuseStep 2978831 = 4468247) B4468247
theorem B2978849 : Blo 1393516 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B3527833 : Blo 1393516 3527833 := bstep (se 2 (by rfl) ⟨1322937, by rfl⟩ : syracuseStep 3527833 = 2645875) B2645875
theorem B3527995 : Blo 1393516 3527995 := bstep (se 1 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 3527995 = 5291993) B5291993
theorem B4707719 : Blo 1393516 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B3528137 : Blo 1393516 3528137 := bstep (se 2 (by rfl) ⟨1323051, by rfl⟩ : syracuseStep 3528137 = 2646103) B2646103
theorem B2119159 : Blo 1393516 2119159 := bstep (se 1 (by rfl) ⟨1589369, by rfl⟩ : syracuseStep 2119159 = 3178739) B3178739
theorem B8599069 : Blo 1393516 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B7058987 : Blo 1393516 7058987 := bstep (se 1 (by rfl) ⟨5294240, by rfl⟩ : syracuseStep 7058987 = 10588481) B10588481
theorem B40195763 : Blo 1393516 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B4708097 : Blo 1393516 4708097 := bstep (se 2 (by rfl) ⟨1765536, by rfl⟩ : syracuseStep 4708097 = 3531073) B3531073
theorem B3528481 : Blo 1393516 3528481 := bstep (se 2 (by rfl) ⟨1323180, by rfl⟩ : syracuseStep 3528481 = 2646361) B2646361
theorem B1488775 : Blo 1393516 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B8599505 : Blo 1393516 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B8632439 : Blo 1393516 8632439 := bstep (se 1 (by rfl) ⟨6474329, by rfl⟩ : syracuseStep 8632439 = 12948659) B12948659
theorem B2513015 : Blo 1393516 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B3135635 : Blo 1393516 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B13408429 : Blo 1393516 13408429 := bstep (se 3 (by rfl) ⟨2514080, by rfl⟩ : syracuseStep 13408429 = 5028161) B5028161
theorem B3135689 : Blo 1393516 3135689 := bstep (se 2 (by rfl) ⟨1175883, by rfl⟩ : syracuseStep 3135689 = 2351767) B2351767
theorem B3529079 : Blo 1393516 3529079 := bstep (se 1 (by rfl) ⟨2646809, by rfl⟩ : syracuseStep 3529079 = 5293619) B5293619
theorem B6699449 : Blo 1393516 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B60340697 : Blo 1393516 60340697 := bstep (se 2 (by rfl) ⟨22627761, by rfl⟩ : syracuseStep 60340697 = 45255523) B45255523
theorem B11917853 : Blo 1393516 11917853 := bstep (se 3 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 11917853 = 4469195) B4469195
theorem B4708907 : Blo 1393516 4708907 := bstep (se 1 (by rfl) ⟨3531680, by rfl⟩ : syracuseStep 4708907 = 7063361) B7063361
theorem B3766969 : Blo 1393516 3766969 := bstep (se 2 (by rfl) ⟨1412613, by rfl⟩ : syracuseStep 3766969 = 2825227) B2825227
theorem B1489595 : Blo 1393516 1489595 := bstep (se 1 (by rfl) ⟨1117196, by rfl⟩ : syracuseStep 1489595 = 2234393) B2234393
theorem B67820237 : Blo 1393516 67820237 := bstep (se 3 (by rfl) ⟨12716294, by rfl⟩ : syracuseStep 67820237 = 25432589) B25432589
theorem B3971855 : Blo 1393516 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B7936805 : Blo 1393516 7936805 := bstep (se 4 (by rfl) ⟨744075, by rfl⟩ : syracuseStep 7936805 = 1488151) B1488151
theorem B7060283 : Blo 1393516 7060283 := bstep (se 1 (by rfl) ⟨5295212, by rfl⟩ : syracuseStep 7060283 = 10590425) B10590425
theorem B3136391 : Blo 1393516 3136391 := bstep (se 1 (by rfl) ⟨2352293, by rfl⟩ : syracuseStep 3136391 = 4704587) B4704587
theorem B3578759 : Blo 1393516 3578759 := bstep (se 1 (by rfl) ⟨2684069, by rfl⟩ : syracuseStep 3578759 = 5368139) B5368139
theorem B7060445 : Blo 1393516 7060445 := bstep (se 3 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 7060445 = 2647667) B2647667
theorem B3136571 : Blo 1393516 3136571 := bstep (se 1 (by rfl) ⟨2352428, by rfl⟩ : syracuseStep 3136571 = 4704857) B4704857
theorem B3136697 : Blo 1393516 3136697 := bstep (se 2 (by rfl) ⟨1176261, by rfl⟩ : syracuseStep 3136697 = 2352523) B2352523
theorem B5651657 : Blo 1393516 5651657 := bstep (se 2 (by rfl) ⟨2119371, by rfl⟩ : syracuseStep 5651657 = 4238743) B4238743
theorem B7937261 : Blo 1393516 7937261 := bstep (se 3 (by rfl) ⟨1488236, by rfl⟩ : syracuseStep 7937261 = 2976473) B2976473
theorem B81501461 : Blo 1393516 81501461 := bstep (se 6 (by rfl) ⟨1910190, by rfl⟩ : syracuseStep 81501461 = 3820381) B3820381
theorem B7060769 : Blo 1393516 7060769 := bstep (se 2 (by rfl) ⟨2647788, by rfl⟩ : syracuseStep 7060769 = 5295577) B5295577
theorem B3137039 : Blo 1393516 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B4898333 : Blo 1393516 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B3137057 : Blo 1393516 3137057 := bstep (se 2 (by rfl) ⟨1176396, by rfl⟩ : syracuseStep 3137057 = 2352793) B2352793
theorem B5955133 : Blo 1393516 5955133 := bstep (se 3 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 5955133 = 2233175) B2233175
theorem B1883783 : Blo 1393516 1883783 := bstep (se 1 (by rfl) ⟨1412837, by rfl⟩ : syracuseStep 1883783 = 2825675) B2825675
theorem B3530375 : Blo 1393516 3530375 := bstep (se 1 (by rfl) ⟨2647781, by rfl⟩ : syracuseStep 3530375 = 5295563) B5295563
theorem B3530425 : Blo 1393516 3530425 := bstep (se 2 (by rfl) ⟨1323909, by rfl⟩ : syracuseStep 3530425 = 2647819) B2647819
theorem B20709121 : Blo 1393516 20709121 := bstep (se 2 (by rfl) ⟨7765920, by rfl⟩ : syracuseStep 20709121 = 15531841) B15531841
theorem B30162739 : Blo 1393516 30162739 := bstep (se 1 (by rfl) ⟨22622054, by rfl⟩ : syracuseStep 30162739 = 45244109) B45244109
theorem B3350359 : Blo 1393516 3350359 := bstep (se 1 (by rfl) ⟨2512769, by rfl⟩ : syracuseStep 3350359 = 5025539) B5025539
theorem B3137399 : Blo 1393516 3137399 := bstep (se 1 (by rfl) ⟨2353049, by rfl⟩ : syracuseStep 3137399 = 4706099) B4706099
theorem B3628919 : Blo 1393516 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B7937945 : Blo 1393516 7937945 := bstep (se 2 (by rfl) ⟨2976729, by rfl⟩ : syracuseStep 7937945 = 5953459) B5953459
theorem B3137543 : Blo 1393516 3137543 := bstep (se 1 (by rfl) ⟨2353157, by rfl⟩ : syracuseStep 3137543 = 4706315) B4706315
theorem B4464659 : Blo 1393516 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B4243475 : Blo 1393516 4243475 := bstep (se 1 (by rfl) ⟨3182606, by rfl⟩ : syracuseStep 4243475 = 6365213) B6365213
theorem B3137615 : Blo 1393516 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B7536797 : Blo 1393516 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B8937701 : Blo 1393516 8937701 := bstep (se 4 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 8937701 = 1675819) B1675819
theorem B2646263 : Blo 1393516 2646263 := bstep (se 1 (by rfl) ⟨1984697, by rfl⟩ : syracuseStep 2646263 = 3969395) B3969395
theorem B3138011 : Blo 1393516 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B22921751 : Blo 1393516 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B7062227 : Blo 1393516 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B7947011 : Blo 1393516 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B1393531 : Blo 1393516 1393531 := bstep (se 1 (by rfl) ⟨1045148, by rfl⟩ : syracuseStep 1393531 = 2090297) B2090297
theorem B1393583 : Blo 1393516 1393583 := bstep (se 1 (by rfl) ⟨1045187, by rfl⟩ : syracuseStep 1393583 = 2090375) B2090375
theorem B3138479 : Blo 1393516 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B1393607 : Blo 1393516 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B1393627 : Blo 1393516 1393627 := bstep (se 1 (by rfl) ⟨1045220, by rfl⟩ : syracuseStep 1393627 = 2090441) B2090441
theorem B2352091 : Blo 1393516 2352091 := bstep (se 1 (by rfl) ⟨1764068, by rfl⟩ : syracuseStep 2352091 = 3528137) B3528137
theorem B8602625 : Blo 1393516 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B1393703 : Blo 1393516 1393703 := bstep (se 1 (by rfl) ⟨1045277, by rfl⟩ : syracuseStep 1393703 = 2090555) B2090555
theorem B3531833 : Blo 1393516 3531833 := bstep (se 2 (by rfl) ⟨1324437, by rfl⟩ : syracuseStep 3531833 = 2648875) B2648875
theorem B1393743 : Blo 1393516 1393743 := bstep (se 1 (by rfl) ⟨1045307, by rfl⟩ : syracuseStep 1393743 = 2090615) B2090615
theorem B1393759 : Blo 1393516 1393759 := bstep (se 1 (by rfl) ⟨1045319, by rfl⟩ : syracuseStep 1393759 = 2090639) B2090639
theorem B26797175 : Blo 1393516 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1393787 : Blo 1393516 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B15893657 : Blo 1393516 15893657 := bstep (se 2 (by rfl) ⟨5960121, by rfl⟩ : syracuseStep 15893657 = 11920243) B11920243
theorem B3138731 : Blo 1393516 3138731 := bstep (se 1 (by rfl) ⟨2354048, by rfl⟩ : syracuseStep 3138731 = 4708097) B4708097
theorem B1393839 : Blo 1393516 1393839 := bstep (se 1 (by rfl) ⟨1045379, by rfl⟩ : syracuseStep 1393839 = 2090759) B2090759
theorem B1393863 : Blo 1393516 1393863 := bstep (se 1 (by rfl) ⟨1045397, by rfl⟩ : syracuseStep 1393863 = 2090795) B2090795
theorem B7947467 : Blo 1393516 7947467 := bstep (se 1 (by rfl) ⟨5960600, by rfl⟩ : syracuseStep 7947467 = 11921201) B11921201
theorem B1393883 : Blo 1393516 1393883 := bstep (se 1 (by rfl) ⟨1045412, by rfl⟩ : syracuseStep 1393883 = 2090825) B2090825
theorem B1393959 : Blo 1393516 1393959 := bstep (se 1 (by rfl) ⟨1045469, by rfl⟩ : syracuseStep 1393959 = 2090939) B2090939
theorem B1393999 : Blo 1393516 1393999 := bstep (se 1 (by rfl) ⟨1045499, by rfl⟩ : syracuseStep 1393999 = 2090999) B2090999
theorem B1394015 : Blo 1393516 1394015 := bstep (se 1 (by rfl) ⟨1045511, by rfl⟩ : syracuseStep 1394015 = 2091023) B2091023
theorem B2090345 : Blo 1393516 2090345 := bstep (se 2 (by rfl) ⟨783879, by rfl⟩ : syracuseStep 2090345 = 1567759) B1567759
theorem B1394043 : Blo 1393516 1394043 := bstep (se 1 (by rfl) ⟨1045532, by rfl⟩ : syracuseStep 1394043 = 2091065) B2091065
theorem B1394095 : Blo 1393516 1394095 := bstep (se 1 (by rfl) ⟨1045571, by rfl⟩ : syracuseStep 1394095 = 2091143) B2091143
theorem B2090423 : Blo 1393516 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B1394119 : Blo 1393516 1394119 := bstep (se 1 (by rfl) ⟨1045589, by rfl⟩ : syracuseStep 1394119 = 2091179) B2091179
theorem B2090459 : Blo 1393516 2090459 := bstep (se 1 (by rfl) ⟨1567844, by rfl⟩ : syracuseStep 2090459 = 3135689) B3135689
theorem B1394139 : Blo 1393516 1394139 := bstep (se 1 (by rfl) ⟨1045604, by rfl⟩ : syracuseStep 1394139 = 2091209) B2091209
theorem B2647561 : Blo 1393516 2647561 := bstep (se 2 (by rfl) ⟨992835, by rfl⟩ : syracuseStep 2647561 = 1985671) B1985671
theorem B4703777 : Blo 1393516 4703777 := bstep (se 2 (by rfl) ⟨1763916, by rfl⟩ : syracuseStep 4703777 = 3527833) B3527833
theorem B1394215 : Blo 1393516 1394215 := bstep (se 1 (by rfl) ⟨1045661, by rfl⟩ : syracuseStep 1394215 = 2091323) B2091323
theorem B2352719 : Blo 1393516 2352719 := bstep (se 1 (by rfl) ⟨1764539, by rfl⟩ : syracuseStep 2352719 = 3529079) B3529079
theorem B1394255 : Blo 1393516 1394255 := bstep (se 1 (by rfl) ⟨1045691, by rfl⟩ : syracuseStep 1394255 = 2091383) B2091383
theorem B1394271 : Blo 1393516 1394271 := bstep (se 1 (by rfl) ⟨1045703, by rfl⟩ : syracuseStep 1394271 = 2091407) B2091407
theorem B4466299 : Blo 1393516 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B1394299 : Blo 1393516 1394299 := bstep (se 1 (by rfl) ⟨1045724, by rfl⟩ : syracuseStep 1394299 = 2091449) B2091449
theorem B1394351 : Blo 1393516 1394351 := bstep (se 1 (by rfl) ⟨1045763, by rfl⟩ : syracuseStep 1394351 = 2091527) B2091527
theorem B5023421 : Blo 1393516 5023421 := bstep (se 3 (by rfl) ⟨941891, by rfl⟩ : syracuseStep 5023421 = 1883783) B1883783
theorem B1394375 : Blo 1393516 1394375 := bstep (se 1 (by rfl) ⟨1045781, by rfl⟩ : syracuseStep 1394375 = 2091563) B2091563
theorem B3139271 : Blo 1393516 3139271 := bstep (se 1 (by rfl) ⟨2354453, by rfl⟩ : syracuseStep 3139271 = 4708907) B4708907
theorem B1394395 : Blo 1393516 1394395 := bstep (se 1 (by rfl) ⟨1045796, by rfl⟩ : syracuseStep 1394395 = 2091593) B2091593
theorem B4703993 : Blo 1393516 4703993 := bstep (se 2 (by rfl) ⟨1763997, by rfl⟩ : syracuseStep 4703993 = 3527995) B3527995
theorem B1394471 : Blo 1393516 1394471 := bstep (se 1 (by rfl) ⟨1045853, by rfl⟩ : syracuseStep 1394471 = 2091707) B2091707
theorem B45213491 : Blo 1393516 45213491 := bstep (se 1 (by rfl) ⟨33910118, by rfl⟩ : syracuseStep 45213491 = 67820237) B67820237
theorem B228984641 : Blo 1393516 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B1394511 : Blo 1393516 1394511 := bstep (se 1 (by rfl) ⟨1045883, by rfl⟩ : syracuseStep 1394511 = 2091767) B2091767
theorem B1394527 : Blo 1393516 1394527 := bstep (se 1 (by rfl) ⟨1045895, by rfl⟩ : syracuseStep 1394527 = 2091791) B2091791
theorem B2647903 : Blo 1393516 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B1394555 : Blo 1393516 1394555 := bstep (se 1 (by rfl) ⟨1045916, by rfl⟩ : syracuseStep 1394555 = 2091833) B2091833
theorem B15075233 : Blo 1393516 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B2090927 : Blo 1393516 2090927 := bstep (se 1 (by rfl) ⟨1568195, by rfl⟩ : syracuseStep 2090927 = 3136391) B3136391
theorem B1394607 : Blo 1393516 1394607 := bstep (se 1 (by rfl) ⟨1045955, by rfl⟩ : syracuseStep 1394607 = 2091911) B2091911
theorem B2385839 : Blo 1393516 2385839 := bstep (se 1 (by rfl) ⟨1789379, by rfl⟩ : syracuseStep 2385839 = 3578759) B3578759
theorem B1394631 : Blo 1393516 1394631 := bstep (se 1 (by rfl) ⟨1045973, by rfl⟩ : syracuseStep 1394631 = 2091947) B2091947
theorem B1394651 : Blo 1393516 1394651 := bstep (se 1 (by rfl) ⟨1045988, by rfl⟩ : syracuseStep 1394651 = 2091977) B2091977
theorem B4704263 : Blo 1393516 4704263 := bstep (se 1 (by rfl) ⟨3528197, by rfl⟩ : syracuseStep 4704263 = 7056395) B7056395
theorem B2091017 : Blo 1393516 2091017 := bstep (se 2 (by rfl) ⟨784131, by rfl⟩ : syracuseStep 2091017 = 1568263) B1568263
theorem B8931343 : Blo 1393516 8931343 := bstep (se 1 (by rfl) ⟨6698507, by rfl⟩ : syracuseStep 8931343 = 13397015) B13397015
theorem B2091047 : Blo 1393516 2091047 := bstep (se 1 (by rfl) ⟨1568285, by rfl⟩ : syracuseStep 2091047 = 3136571) B3136571
theorem B1394727 : Blo 1393516 1394727 := bstep (se 1 (by rfl) ⟨1046045, by rfl⟩ : syracuseStep 1394727 = 2092091) B2092091
theorem B1394767 : Blo 1393516 1394767 := bstep (se 1 (by rfl) ⟨1046075, by rfl⟩ : syracuseStep 1394767 = 2092151) B2092151
theorem B7940177 : Blo 1393516 7940177 := bstep (se 2 (by rfl) ⟨2977566, by rfl⟩ : syracuseStep 7940177 = 5955133) B5955133
theorem B1394783 : Blo 1393516 1394783 := bstep (se 1 (by rfl) ⟨1046087, by rfl⟩ : syracuseStep 1394783 = 2092175) B2092175
theorem B4704371 : Blo 1393516 4704371 := bstep (se 1 (by rfl) ⟨3528278, by rfl⟩ : syracuseStep 4704371 = 7056557) B7056557
theorem B2091131 : Blo 1393516 2091131 := bstep (se 1 (by rfl) ⟨1568348, by rfl⟩ : syracuseStep 2091131 = 3136697) B3136697
theorem B1394811 : Blo 1393516 1394811 := bstep (se 1 (by rfl) ⟨1046108, by rfl⟩ : syracuseStep 1394811 = 2092217) B2092217
theorem B1394863 : Blo 1393516 1394863 := bstep (se 1 (by rfl) ⟨1046147, by rfl⟩ : syracuseStep 1394863 = 2092295) B2092295
theorem B1394887 : Blo 1393516 1394887 := bstep (se 1 (by rfl) ⟨1046165, by rfl⟩ : syracuseStep 1394887 = 2092331) B2092331
theorem B1394907 : Blo 1393516 1394907 := bstep (se 1 (by rfl) ⟨1046180, by rfl⟩ : syracuseStep 1394907 = 2092361) B2092361
theorem B23816429 : Blo 1393516 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B2091257 : Blo 1393516 2091257 := bstep (se 2 (by rfl) ⟨784221, by rfl⟩ : syracuseStep 2091257 = 1568443) B1568443
theorem B1394983 : Blo 1393516 1394983 := bstep (se 1 (by rfl) ⟨1046237, by rfl⟩ : syracuseStep 1394983 = 2092475) B2092475
theorem B9677117 : Blo 1393516 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B1395023 : Blo 1393516 1395023 := bstep (se 1 (by rfl) ⟨1046267, by rfl⟩ : syracuseStep 1395023 = 2092535) B2092535
theorem B5294423 : Blo 1393516 5294423 := bstep (se 1 (by rfl) ⟨3970817, by rfl⟩ : syracuseStep 5294423 = 7941635) B7941635
theorem B2091359 : Blo 1393516 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B1395039 : Blo 1393516 1395039 := bstep (se 1 (by rfl) ⟨1046279, by rfl⟩ : syracuseStep 1395039 = 2092559) B2092559
theorem B2091371 : Blo 1393516 2091371 := bstep (se 1 (by rfl) ⟨1568528, by rfl⟩ : syracuseStep 2091371 = 3137057) B3137057
theorem B1395067 : Blo 1393516 1395067 := bstep (se 1 (by rfl) ⟨1046300, by rfl⟩ : syracuseStep 1395067 = 2092601) B2092601
theorem B4704641 : Blo 1393516 4704641 := bstep (se 2 (by rfl) ⟨1764240, by rfl⟩ : syracuseStep 4704641 = 3528481) B3528481
theorem B40216985 : Blo 1393516 40216985 := bstep (se 2 (by rfl) ⟨15081369, by rfl⟩ : syracuseStep 40216985 = 30162739) B30162739
theorem B2353583 : Blo 1393516 2353583 := bstep (se 1 (by rfl) ⟨1765187, by rfl⟩ : syracuseStep 2353583 = 3530375) B3530375
theorem B1395119 : Blo 1393516 1395119 := bstep (se 1 (by rfl) ⟨1046339, by rfl⟩ : syracuseStep 1395119 = 2092679) B2092679
theorem B76286387 : Blo 1393516 76286387 := bstep (se 1 (by rfl) ⟨57214790, by rfl⟩ : syracuseStep 76286387 = 114429581) B114429581
theorem B1395143 : Blo 1393516 1395143 := bstep (se 1 (by rfl) ⟨1046357, by rfl⟩ : syracuseStep 1395143 = 2092715) B2092715
theorem B4467145 : Blo 1393516 4467145 := bstep (se 2 (by rfl) ⟨1675179, by rfl⟩ : syracuseStep 4467145 = 3350359) B3350359
theorem B3017179 : Blo 1393516 3017179 := bstep (se 1 (by rfl) ⟨2262884, by rfl⟩ : syracuseStep 3017179 = 4525769) B4525769
theorem B1395163 : Blo 1393516 1395163 := bstep (se 1 (by rfl) ⟨1046372, by rfl⟩ : syracuseStep 1395163 = 2092745) B2092745
theorem B1985033 : Blo 1393516 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B1788455 : Blo 1393516 1788455 := bstep (se 1 (by rfl) ⟨1341341, by rfl⟩ : syracuseStep 1788455 = 2682683) B2682683
theorem B1395239 : Blo 1393516 1395239 := bstep (se 1 (by rfl) ⟨1046429, by rfl⟩ : syracuseStep 1395239 = 2092859) B2092859
theorem B22932013 : Blo 1393516 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B2091599 : Blo 1393516 2091599 := bstep (se 1 (by rfl) ⟨1568699, by rfl⟩ : syracuseStep 2091599 = 3137399) B3137399
theorem B1395279 : Blo 1393516 1395279 := bstep (se 1 (by rfl) ⟨1046459, by rfl⟩ : syracuseStep 1395279 = 2092919) B2092919
theorem B1395295 : Blo 1393516 1395295 := bstep (se 1 (by rfl) ⟨1046471, by rfl⟩ : syracuseStep 1395295 = 2092943) B2092943
theorem B1395323 : Blo 1393516 1395323 := bstep (se 1 (by rfl) ⟨1046492, by rfl⟩ : syracuseStep 1395323 = 2092985) B2092985
theorem B1395375 : Blo 1393516 1395375 := bstep (se 1 (by rfl) ⟨1046531, by rfl⟩ : syracuseStep 1395375 = 2093063) B2093063
theorem B2091719 : Blo 1393516 2091719 := bstep (se 1 (by rfl) ⟨1568789, by rfl⟩ : syracuseStep 2091719 = 3137579) B3137579
theorem B1395399 : Blo 1393516 1395399 := bstep (se 1 (by rfl) ⟨1046549, by rfl⟩ : syracuseStep 1395399 = 2093099) B2093099
theorem B1395419 : Blo 1393516 1395419 := bstep (se 1 (by rfl) ⟨1046564, by rfl⟩ : syracuseStep 1395419 = 2093129) B2093129
theorem B2829047 : Blo 1393516 2829047 := bstep (se 1 (by rfl) ⟨2121785, by rfl⟩ : syracuseStep 2829047 = 4243571) B4243571
theorem B1395495 : Blo 1393516 1395495 := bstep (se 1 (by rfl) ⟨1046621, by rfl⟩ : syracuseStep 1395495 = 2093243) B2093243
theorem B2354015 : Blo 1393516 2354015 := bstep (se 1 (by rfl) ⟨1765511, by rfl⟩ : syracuseStep 2354015 = 3531023) B3531023
theorem B2091881 : Blo 1393516 2091881 := bstep (se 2 (by rfl) ⟨784455, by rfl⟩ : syracuseStep 2091881 = 1568911) B1568911
theorem B4770667 : Blo 1393516 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B17877905 : Blo 1393516 17877905 := bstep (se 2 (by rfl) ⟨6704214, by rfl⟩ : syracuseStep 17877905 = 13408429) B13408429
theorem B1764271 : Blo 1393516 1764271 := bstep (se 1 (by rfl) ⟨1323203, by rfl⟩ : syracuseStep 1764271 = 2646407) B2646407
theorem B4467631 : Blo 1393516 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B7064495 : Blo 1393516 7064495 := bstep (se 1 (by rfl) ⟨5298371, by rfl⟩ : syracuseStep 7064495 = 10596743) B10596743
theorem B2091959 : Blo 1393516 2091959 := bstep (se 1 (by rfl) ⟨1568969, by rfl⟩ : syracuseStep 2091959 = 3137939) B3137939
theorem B2649019 : Blo 1393516 2649019 := bstep (se 1 (by rfl) ⟨1986764, by rfl⟩ : syracuseStep 2649019 = 3973529) B3973529
theorem B2091995 : Blo 1393516 2091995 := bstep (se 1 (by rfl) ⟨1568996, by rfl⟩ : syracuseStep 2091995 = 3137993) B3137993
theorem B2649095 : Blo 1393516 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1567867 : Blo 1393516 1567867 := bstep (se 1 (by rfl) ⟨1175900, by rfl⟩ : syracuseStep 1567867 = 2351801) B2351801
theorem B4705451 : Blo 1393516 4705451 := bstep (se 1 (by rfl) ⟨3529088, by rfl⟩ : syracuseStep 4705451 = 7058177) B7058177
theorem B1674439 : Blo 1393516 1674439 := bstep (se 1 (by rfl) ⟨1255829, by rfl⟩ : syracuseStep 1674439 = 2511659) B2511659
theorem B1985887 : Blo 1393516 1985887 := bstep (se 1 (by rfl) ⟨1489415, by rfl⟩ : syracuseStep 1985887 = 2978831) B2978831
theorem B1985899 : Blo 1393516 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B2354575 : Blo 1393516 2354575 := bstep (se 1 (by rfl) ⟨1765931, by rfl⟩ : syracuseStep 2354575 = 3531863) B3531863
theorem B2092463 : Blo 1393516 2092463 := bstep (se 1 (by rfl) ⟨1569347, by rfl⟩ : syracuseStep 2092463 = 3138695) B3138695
theorem B2092553 : Blo 1393516 2092553 := bstep (se 2 (by rfl) ⟨784707, by rfl⟩ : syracuseStep 2092553 = 1569415) B1569415
theorem B2092583 : Blo 1393516 2092583 := bstep (se 1 (by rfl) ⟨1569437, by rfl⟩ : syracuseStep 2092583 = 3138875) B3138875
theorem B1568335 : Blo 1393516 1568335 := bstep (se 1 (by rfl) ⟨1176251, by rfl⟩ : syracuseStep 1568335 = 2352503) B2352503
theorem B2092667 : Blo 1393516 2092667 := bstep (se 1 (by rfl) ⟨1569500, by rfl⟩ : syracuseStep 2092667 = 3139001) B3139001
theorem B20090501 : Blo 1393516 20090501 := bstep (se 4 (by rfl) ⟨1883484, by rfl⟩ : syracuseStep 20090501 = 3766969) B3766969
theorem B7057043 : Blo 1393516 7057043 := bstep (se 1 (by rfl) ⟨5292782, by rfl⟩ : syracuseStep 7057043 = 10585565) B10585565
theorem B4705991 : Blo 1393516 4705991 := bstep (se 1 (by rfl) ⟨3529493, by rfl⟩ : syracuseStep 4705991 = 7058987) B7058987
theorem B2092793 : Blo 1393516 2092793 := bstep (se 2 (by rfl) ⟨784797, by rfl⟩ : syracuseStep 2092793 = 1569595) B1569595
theorem B80424737 : Blo 1393516 80424737 := bstep (se 2 (by rfl) ⟨30159276, by rfl⟩ : syracuseStep 80424737 = 60318553) B60318553
theorem B5730115 : Blo 1393516 5730115 := bstep (se 1 (by rfl) ⟨4297586, by rfl⟩ : syracuseStep 5730115 = 8595173) B8595173
theorem B2092895 : Blo 1393516 2092895 := bstep (se 1 (by rfl) ⟨1569671, by rfl⟩ : syracuseStep 2092895 = 3139343) B3139343
theorem B2092907 : Blo 1393516 2092907 := bstep (se 1 (by rfl) ⟨1569680, by rfl⟩ : syracuseStep 2092907 = 3139361) B3139361
theorem B10596257 : Blo 1393516 10596257 := bstep (se 2 (by rfl) ⟨3973596, by rfl⟩ : syracuseStep 10596257 = 7947193) B7947193
theorem B1568731 : Blo 1393516 1568731 := bstep (se 1 (by rfl) ⟨1176548, by rfl⟩ : syracuseStep 1568731 = 2353097) B2353097
theorem B1765415 : Blo 1393516 1765415 := bstep (se 1 (by rfl) ⟨1324061, by rfl⟩ : syracuseStep 1765415 = 2648123) B2648123
theorem B13062221 : Blo 1393516 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B5754959 : Blo 1393516 5754959 := bstep (se 1 (by rfl) ⟨4316219, by rfl⟩ : syracuseStep 5754959 = 8632439) B8632439
theorem B1675343 : Blo 1393516 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B2093135 : Blo 1393516 2093135 := bstep (se 1 (by rfl) ⟨1569851, by rfl⟩ : syracuseStep 2093135 = 3139703) B3139703
theorem B2093255 : Blo 1393516 2093255 := bstep (se 1 (by rfl) ⟨1569941, by rfl⟩ : syracuseStep 2093255 = 3139883) B3139883
theorem B40227131 : Blo 1393516 40227131 := bstep (se 1 (by rfl) ⟨30170348, by rfl⟩ : syracuseStep 40227131 = 60340697) B60340697
theorem B1765739 : Blo 1393516 1765739 := bstep (se 1 (by rfl) ⟨1324304, by rfl⟩ : syracuseStep 1765739 = 2648609) B2648609
theorem B1569199 : Blo 1393516 1569199 := bstep (se 1 (by rfl) ⟨1176899, by rfl⟩ : syracuseStep 1569199 = 2353799) B2353799
theorem B7942637 : Blo 1393516 7942637 := bstep (se 3 (by rfl) ⟨1489244, by rfl⟩ : syracuseStep 7942637 = 2978489) B2978489
theorem B4706855 : Blo 1393516 4706855 := bstep (se 1 (by rfl) ⟨3530141, by rfl⟩ : syracuseStep 4706855 = 7060283) B7060283
theorem B4706963 : Blo 1393516 4706963 := bstep (se 1 (by rfl) ⟨3530222, by rfl⟩ : syracuseStep 4706963 = 7060445) B7060445
theorem B11465425 : Blo 1393516 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B1569631 : Blo 1393516 1569631 := bstep (se 1 (by rfl) ⟨1177223, by rfl⟩ : syracuseStep 1569631 = 2354447) B2354447
theorem B54334307 : Blo 1393516 54334307 := bstep (se 1 (by rfl) ⟨40750730, by rfl⟩ : syracuseStep 54334307 = 81501461) B81501461
theorem B4707179 : Blo 1393516 4707179 := bstep (se 1 (by rfl) ⟨3530384, by rfl⟩ : syracuseStep 4707179 = 7060769) B7060769
theorem B4707233 : Blo 1393516 4707233 := bstep (se 2 (by rfl) ⟨1765212, by rfl⟩ : syracuseStep 4707233 = 3530425) B3530425
theorem B27612161 : Blo 1393516 27612161 := bstep (se 2 (by rfl) ⟨10354560, by rfl⟩ : syracuseStep 27612161 = 20709121) B20709121
theorem B13407281 : Blo 1393516 13407281 := bstep (se 2 (by rfl) ⟨5027730, by rfl⟩ : syracuseStep 13407281 = 10055461) B10055461
theorem B5297309 : Blo 1393516 5297309 := bstep (se 3 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 5297309 = 1986491) B1986491
theorem B4707827 : Blo 1393516 4707827 := bstep (se 1 (by rfl) ⟨3530870, by rfl⟩ : syracuseStep 4707827 = 7061741) B7061741
theorem B7943777 : Blo 1393516 7943777 := bstep (se 2 (by rfl) ⟨2978916, by rfl⟩ : syracuseStep 7943777 = 5957833) B5957833
theorem B33904277 : Blo 1393516 33904277 := bstep (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) B1589263
theorem B2512633 : Blo 1393516 2512633 := bstep (se 2 (by rfl) ⟨942237, by rfl⟩ : syracuseStep 2512633 = 1884475) B1884475
theorem B5297993 : Blo 1393516 5297993 := bstep (se 2 (by rfl) ⟨1986747, by rfl⟩ : syracuseStep 5297993 = 3973495) B3973495
theorem B9541471 : Blo 1393516 9541471 := bstep (se 1 (by rfl) ⟨7156103, by rfl⟩ : syracuseStep 9541471 = 14312207) B14312207
theorem B3528623 : Blo 1393516 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B3135419 : Blo 1393516 3135419 := bstep (se 1 (by rfl) ⟨2351564, by rfl⟩ : syracuseStep 3135419 = 4703129) B4703129
theorem B4708367 : Blo 1393516 4708367 := bstep (se 1 (by rfl) ⟨3531275, by rfl⟩ : syracuseStep 4708367 = 7062551) B7062551
theorem B3135545 : Blo 1393516 3135545 := bstep (se 2 (by rfl) ⟨1175829, by rfl⟩ : syracuseStep 3135545 = 2351659) B2351659
theorem B5298493 : Blo 1393516 5298493 := bstep (se 3 (by rfl) ⟨993467, by rfl⟩ : syracuseStep 5298493 = 1986935) B1986935
theorem B3135887 : Blo 1393516 3135887 := bstep (se 1 (by rfl) ⟨2351915, by rfl⟩ : syracuseStep 3135887 = 4703831) B4703831
theorem B3348955 : Blo 1393516 3348955 := bstep (se 1 (by rfl) ⟨2511716, by rfl⟩ : syracuseStep 3348955 = 5023433) B5023433
theorem B4241929 : Blo 1393516 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B3529241 : Blo 1393516 3529241 := bstep (se 2 (by rfl) ⟨1323465, by rfl⟩ : syracuseStep 3529241 = 2646931) B2646931
theorem B4708961 : Blo 1393516 4708961 := bstep (se 2 (by rfl) ⟨1765860, by rfl⟩ : syracuseStep 4708961 = 3531721) B3531721
theorem B3136211 : Blo 1393516 3136211 := bstep (se 1 (by rfl) ⟨2352158, by rfl⟩ : syracuseStep 3136211 = 4704317) B4704317
theorem B7641859 : Blo 1393516 7641859 := bstep (se 1 (by rfl) ⟨5731394, by rfl⟩ : syracuseStep 7641859 = 11462789) B11462789
theorem B4528991 : Blo 1393516 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B10738615 : Blo 1393516 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B7945235 : Blo 1393516 7945235 := bstep (se 1 (by rfl) ⟨5958926, by rfl⟩ : syracuseStep 7945235 = 11917853) B11917853
theorem B2514017 : Blo 1393516 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B3972253 : Blo 1393516 3972253 := bstep (se 3 (by rfl) ⟨744797, by rfl⟩ : syracuseStep 3972253 = 1489595) B1489595
theorem B5291203 : Blo 1393516 5291203 := bstep (se 1 (by rfl) ⟨3968402, by rfl⟩ : syracuseStep 5291203 = 7936805) B7936805
theorem B2825545 : Blo 1393516 2825545 := bstep (se 2 (by rfl) ⟨1059579, by rfl⟩ : syracuseStep 2825545 = 2119159) B2119159
theorem B10050905 : Blo 1393516 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B3767771 : Blo 1393516 3767771 := bstep (se 1 (by rfl) ⟨2825828, by rfl⟩ : syracuseStep 3767771 = 5651657) B5651657
theorem B5291507 : Blo 1393516 5291507 := bstep (se 1 (by rfl) ⟨3968630, by rfl⟩ : syracuseStep 5291507 = 7937261) B7937261
theorem B3137147 : Blo 1393516 3137147 := bstep (se 1 (by rfl) ⟨2352860, by rfl⟩ : syracuseStep 3137147 = 4705721) B4705721
theorem B10591883 : Blo 1393516 10591883 := bstep (se 1 (by rfl) ⟨7943912, by rfl⟩ : syracuseStep 10591883 = 15887825) B15887825
theorem B8478407 : Blo 1393516 8478407 := bstep (se 1 (by rfl) ⟨6358805, by rfl⟩ : syracuseStep 8478407 = 12717611) B12717611
theorem B3137273 : Blo 1393516 3137273 := bstep (se 2 (by rfl) ⟨1176477, by rfl⟩ : syracuseStep 3137273 = 2352955) B2352955
theorem B3972959 : Blo 1393516 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B2645921 : Blo 1393516 2645921 := bstep (se 2 (by rfl) ⟨992220, by rfl⟩ : syracuseStep 2645921 = 1984441) B1984441
theorem B5291963 : Blo 1393516 5291963 := bstep (se 1 (by rfl) ⟨3968972, by rfl⟩ : syracuseStep 5291963 = 7937945) B7937945
theorem B10731473 : Blo 1393516 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B8708147 : Blo 1393516 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B3137903 : Blo 1393516 3137903 := bstep (se 1 (by rfl) ⟨2353427, by rfl⟩ : syracuseStep 3137903 = 4706855) B4706855
theorem B3137975 : Blo 1393516 3137975 := bstep (se 1 (by rfl) ⟨2353481, by rfl⟩ : syracuseStep 3137975 = 4706963) B4706963
theorem B3138119 : Blo 1393516 3138119 := bstep (se 1 (by rfl) ⟨2353589, by rfl⟩ : syracuseStep 3138119 = 4707179) B4707179
theorem B5956193 : Blo 1393516 5956193 := bstep (se 2 (by rfl) ⟨2233572, by rfl⟩ : syracuseStep 5956193 = 4467145) B4467145
theorem B3138155 : Blo 1393516 3138155 := bstep (se 1 (by rfl) ⟨2353616, by rfl⟩ : syracuseStep 3138155 = 4707233) B4707233
theorem B18408107 : Blo 1393516 18408107 := bstep (se 1 (by rfl) ⟨13806080, by rfl⟩ : syracuseStep 18408107 = 27612161) B27612161
theorem B8938187 : Blo 1393516 8938187 := bstep (se 1 (by rfl) ⟨6703640, by rfl⟩ : syracuseStep 8938187 = 13407281) B13407281
theorem B3531539 : Blo 1393516 3531539 := bstep (se 1 (by rfl) ⟨2648654, by rfl⟩ : syracuseStep 3531539 = 5297309) B5297309
theorem B1393563 : Blo 1393516 1393563 := bstep (se 1 (by rfl) ⟨1045172, by rfl⟩ : syracuseStep 1393563 = 2090345) B2090345
theorem B15287233 : Blo 1393516 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B1393615 : Blo 1393516 1393615 := bstep (se 1 (by rfl) ⟨1045211, by rfl⟩ : syracuseStep 1393615 = 2090423) B2090423
theorem B1393639 : Blo 1393516 1393639 := bstep (se 1 (by rfl) ⟨1045229, by rfl⟩ : syracuseStep 1393639 = 2090459) B2090459
theorem B3138551 : Blo 1393516 3138551 := bstep (se 1 (by rfl) ⟨2353913, by rfl⟩ : syracuseStep 3138551 = 4707827) B4707827
theorem B8930341 : Blo 1393516 8930341 := bstep (se 4 (by rfl) ⟨837219, by rfl⟩ : syracuseStep 8930341 = 1674439) B1674439
theorem B22602851 : Blo 1393516 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B3531995 : Blo 1393516 3531995 := bstep (se 1 (by rfl) ⟨2648996, by rfl⟩ : syracuseStep 3531995 = 5297993) B5297993
theorem B2352361 : Blo 1393516 2352361 := bstep (se 2 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 2352361 = 1764271) B1764271
theorem B5956841 : Blo 1393516 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B3532025 : Blo 1393516 3532025 := bstep (se 2 (by rfl) ⟨1324509, by rfl⟩ : syracuseStep 3532025 = 2649019) B2649019
theorem B1393951 : Blo 1393516 1393951 := bstep (se 1 (by rfl) ⟨1045463, by rfl⟩ : syracuseStep 1393951 = 2090927) B2090927
theorem B2352415 : Blo 1393516 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B1590559 : Blo 1393516 1590559 := bstep (se 1 (by rfl) ⟨1192919, by rfl⟩ : syracuseStep 1590559 = 2385839) B2385839
theorem B2090279 : Blo 1393516 2090279 := bstep (se 1 (by rfl) ⟨1567709, by rfl⟩ : syracuseStep 2090279 = 3135419) B3135419
theorem B1394011 : Blo 1393516 1394011 := bstep (se 1 (by rfl) ⟨1045508, by rfl⟩ : syracuseStep 1394011 = 2091017) B2091017
theorem B3138911 : Blo 1393516 3138911 := bstep (se 1 (by rfl) ⟨2354183, by rfl⟩ : syracuseStep 3138911 = 4708367) B4708367
theorem B5293421 : Blo 1393516 5293421 := bstep (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) B1985033
theorem B1394031 : Blo 1393516 1394031 := bstep (se 1 (by rfl) ⟨1045523, by rfl⟩ : syracuseStep 1394031 = 2091047) B2091047
theorem B2090363 : Blo 1393516 2090363 := bstep (se 1 (by rfl) ⟨1567772, by rfl⟩ : syracuseStep 2090363 = 3135545) B3135545
theorem B5293451 : Blo 1393516 5293451 := bstep (se 1 (by rfl) ⟨3970088, by rfl⟩ : syracuseStep 5293451 = 7940177) B7940177
theorem B1394087 : Blo 1393516 1394087 := bstep (se 1 (by rfl) ⟨1045565, by rfl⟩ : syracuseStep 1394087 = 2091131) B2091131
theorem B4769213 : Blo 1393516 4769213 := bstep (se 3 (by rfl) ⟨894227, by rfl⟩ : syracuseStep 4769213 = 1788455) B1788455
theorem B15877619 : Blo 1393516 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B2090489 : Blo 1393516 2090489 := bstep (se 2 (by rfl) ⟨783933, by rfl⟩ : syracuseStep 2090489 = 1567867) B1567867
theorem B1394171 : Blo 1393516 1394171 := bstep (se 1 (by rfl) ⟨1045628, by rfl⟩ : syracuseStep 1394171 = 2091257) B2091257
theorem B1394239 : Blo 1393516 1394239 := bstep (se 1 (by rfl) ⟨1045679, by rfl⟩ : syracuseStep 1394239 = 2091359) B2091359
theorem B1394247 : Blo 1393516 1394247 := bstep (se 1 (by rfl) ⟨1045685, by rfl⟩ : syracuseStep 1394247 = 2091371) B2091371
theorem B7054937 : Blo 1393516 7054937 := bstep (se 2 (by rfl) ⟨2645601, by rfl⟩ : syracuseStep 7054937 = 5291203) B5291203
theorem B2090591 : Blo 1393516 2090591 := bstep (se 1 (by rfl) ⟨1567943, by rfl⟩ : syracuseStep 2090591 = 3135887) B3135887
theorem B50857591 : Blo 1393516 50857591 := bstep (se 1 (by rfl) ⟨38143193, by rfl⟩ : syracuseStep 50857591 = 76286387) B76286387
theorem B2352827 : Blo 1393516 2352827 := bstep (se 1 (by rfl) ⟨1764620, by rfl⟩ : syracuseStep 2352827 = 3529241) B3529241
theorem B1394399 : Blo 1393516 1394399 := bstep (se 1 (by rfl) ⟨1045799, by rfl⟩ : syracuseStep 1394399 = 2091599) B2091599
theorem B3139307 : Blo 1393516 3139307 := bstep (se 1 (by rfl) ⟨2354480, by rfl⟩ : syracuseStep 3139307 = 4708961) B4708961
theorem B1394479 : Blo 1393516 1394479 := bstep (se 1 (by rfl) ⟨1045859, by rfl⟩ : syracuseStep 1394479 = 2091719) B2091719
theorem B2090807 : Blo 1393516 2090807 := bstep (se 1 (by rfl) ⟨1568105, by rfl⟩ : syracuseStep 2090807 = 3136211) B3136211
theorem B2647865 : Blo 1393516 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B3139433 : Blo 1393516 3139433 := bstep (se 2 (by rfl) ⟨1177287, by rfl⟩ : syracuseStep 3139433 = 2354575) B2354575
theorem B1394587 : Blo 1393516 1394587 := bstep (se 1 (by rfl) ⟨1045940, by rfl⟩ : syracuseStep 1394587 = 2091881) B2091881
theorem B1394639 : Blo 1393516 1394639 := bstep (se 1 (by rfl) ⟨1045979, by rfl⟩ : syracuseStep 1394639 = 2091959) B2091959
theorem B1394663 : Blo 1393516 1394663 := bstep (se 1 (by rfl) ⟨1045997, by rfl⟩ : syracuseStep 1394663 = 2091995) B2091995
theorem B2091113 : Blo 1393516 2091113 := bstep (se 2 (by rfl) ⟨784167, by rfl⟩ : syracuseStep 2091113 = 1568335) B1568335
theorem B12077309 : Blo 1393516 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B1394975 : Blo 1393516 1394975 := bstep (se 1 (by rfl) ⟨1046231, by rfl⟩ : syracuseStep 1394975 = 2092463) B2092463
theorem B1395035 : Blo 1393516 1395035 := bstep (se 1 (by rfl) ⟨1046276, by rfl⟩ : syracuseStep 1395035 = 2092553) B2092553
theorem B1395055 : Blo 1393516 1395055 := bstep (se 1 (by rfl) ⟨1046291, by rfl⟩ : syracuseStep 1395055 = 2092583) B2092583
theorem B2091431 : Blo 1393516 2091431 := bstep (se 1 (by rfl) ⟨1568573, by rfl⟩ : syracuseStep 2091431 = 3137147) B3137147
theorem B1395111 : Blo 1393516 1395111 := bstep (se 1 (by rfl) ⟨1046333, by rfl⟩ : syracuseStep 1395111 = 2092667) B2092667
theorem B4704695 : Blo 1393516 4704695 := bstep (se 1 (by rfl) ⟨3528521, by rfl⟩ : syracuseStep 4704695 = 7057043) B7057043
theorem B16091621 : Blo 1393516 16091621 := bstep (se 4 (by rfl) ⟨1508589, by rfl⟩ : syracuseStep 16091621 = 3017179) B3017179
theorem B17861093 : Blo 1393516 17861093 := bstep (se 4 (by rfl) ⟨1674477, by rfl⟩ : syracuseStep 17861093 = 3348955) B3348955
theorem B2091515 : Blo 1393516 2091515 := bstep (se 1 (by rfl) ⟨1568636, by rfl⟩ : syracuseStep 2091515 = 3137273) B3137273
theorem B1395195 : Blo 1393516 1395195 := bstep (se 1 (by rfl) ⟨1046396, by rfl⟩ : syracuseStep 1395195 = 2092793) B2092793
theorem B2648639 : Blo 1393516 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B1395263 : Blo 1393516 1395263 := bstep (se 1 (by rfl) ⟨1046447, by rfl⟩ : syracuseStep 1395263 = 2092895) B2092895
theorem B1395271 : Blo 1393516 1395271 := bstep (se 1 (by rfl) ⟨1046453, by rfl⟩ : syracuseStep 1395271 = 2092907) B2092907
theorem B1763947 : Blo 1393516 1763947 := bstep (se 1 (by rfl) ⟨1322960, by rfl⟩ : syracuseStep 1763947 = 2645921) B2645921
theorem B7064171 : Blo 1393516 7064171 := bstep (se 1 (by rfl) ⟨5298128, by rfl⟩ : syracuseStep 7064171 = 10596257) B10596257
theorem B2091641 : Blo 1393516 2091641 := bstep (se 2 (by rfl) ⟨784365, by rfl⟩ : syracuseStep 2091641 = 1568731) B1568731
theorem B7154315 : Blo 1393516 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B22940333 : Blo 1393516 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B2091695 : Blo 1393516 2091695 := bstep (se 1 (by rfl) ⟨1568771, by rfl⟩ : syracuseStep 2091695 = 3137543) B3137543
theorem B2976439 : Blo 1393516 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B11315933 : Blo 1393516 11315933 := bstep (se 3 (by rfl) ⟨2121737, by rfl⟩ : syracuseStep 11315933 = 4243475) B4243475
theorem B3836639 : Blo 1393516 3836639 := bstep (se 1 (by rfl) ⟨2877479, by rfl⟩ : syracuseStep 3836639 = 5754959) B5754959
theorem B2091743 : Blo 1393516 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B1395423 : Blo 1393516 1395423 := bstep (se 1 (by rfl) ⟨1046567, by rfl⟩ : syracuseStep 1395423 = 2093135) B2093135
theorem B5024531 : Blo 1393516 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B1395503 : Blo 1393516 1395503 := bstep (se 1 (by rfl) ⟨1046627, by rfl⟩ : syracuseStep 1395503 = 2093255) B2093255
theorem B5958467 : Blo 1393516 5958467 := bstep (se 1 (by rfl) ⟨4468850, by rfl⟩ : syracuseStep 5958467 = 8937701) B8937701
theorem B1764175 : Blo 1393516 1764175 := bstep (se 1 (by rfl) ⟨1323131, by rfl⟩ : syracuseStep 1764175 = 2646263) B2646263
theorem B4467581 : Blo 1393516 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B6704045 : Blo 1393516 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B2092007 : Blo 1393516 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B5295091 : Blo 1393516 5295091 := bstep (se 1 (by rfl) ⟨3971318, by rfl⟩ : syracuseStep 5295091 = 7942637) B7942637
theorem B15281167 : Blo 1393516 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B7064657 : Blo 1393516 7064657 := bstep (se 2 (by rfl) ⟨2649246, by rfl⟩ : syracuseStep 7064657 = 5298493) B5298493
theorem B2092265 : Blo 1393516 2092265 := bstep (se 2 (by rfl) ⟨784599, by rfl⟩ : syracuseStep 2092265 = 1569199) B1569199
theorem B2092319 : Blo 1393516 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B5655905 : Blo 1393516 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B2354555 : Blo 1393516 2354555 := bstep (se 1 (by rfl) ⟨1765916, by rfl⟩ : syracuseStep 2354555 = 3531833) B3531833
theorem B30576017 : Blo 1393516 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B10595771 : Blo 1393516 10595771 := bstep (se 1 (by rfl) ⟨7946828, by rfl⟩ : syracuseStep 10595771 = 15893657) B15893657
theorem B2092487 : Blo 1393516 2092487 := bstep (se 1 (by rfl) ⟨1569365, by rfl⟩ : syracuseStep 2092487 = 3138731) B3138731
theorem B1568479 : Blo 1393516 1568479 := bstep (se 1 (by rfl) ⟨1176359, by rfl⟩ : syracuseStep 1568479 = 2352719) B2352719
theorem B5295851 : Blo 1393516 5295851 := bstep (se 1 (by rfl) ⟨3971888, by rfl⟩ : syracuseStep 5295851 = 7943777) B7943777
theorem B2092841 : Blo 1393516 2092841 := bstep (se 2 (by rfl) ⟨784815, by rfl⟩ : syracuseStep 2092841 = 1569631) B1569631
theorem B2092847 : Blo 1393516 2092847 := bstep (se 1 (by rfl) ⟨1569635, by rfl⟩ : syracuseStep 2092847 = 3139271) B3139271
theorem B30142327 : Blo 1393516 30142327 := bstep (se 1 (by rfl) ⟨22606745, by rfl⟩ : syracuseStep 30142327 = 45213491) B45213491
theorem B5296337 : Blo 1393516 5296337 := bstep (se 2 (by rfl) ⟨1986126, by rfl⟩ : syracuseStep 5296337 = 3972253) B3972253
theorem B6451411 : Blo 1393516 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B1569055 : Blo 1393516 1569055 := bstep (se 1 (by rfl) ⟨1176791, by rfl⟩ : syracuseStep 1569055 = 2353583) B2353583
theorem B1569343 : Blo 1393516 1569343 := bstep (se 1 (by rfl) ⟨1177007, by rfl⟩ : syracuseStep 1569343 = 2354015) B2354015
theorem B1766063 : Blo 1393516 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B5296823 : Blo 1393516 5296823 := bstep (se 1 (by rfl) ⟨3972617, by rfl⟩ : syracuseStep 5296823 = 7945235) B7945235
theorem B2511847 : Blo 1393516 2511847 := bstep (se 1 (by rfl) ⟨1883885, by rfl⟩ : syracuseStep 2511847 = 3767771) B3767771
theorem B3527671 : Blo 1393516 3527671 := bstep (se 1 (by rfl) ⟨2645753, by rfl⟩ : syracuseStep 3527671 = 5291507) B5291507
theorem B7640153 : Blo 1393516 7640153 := bstep (se 2 (by rfl) ⟨2865057, by rfl⟩ : syracuseStep 7640153 = 5730115) B5730115
theorem B3527975 : Blo 1393516 3527975 := bstep (se 1 (by rfl) ⟨2645981, by rfl⟩ : syracuseStep 3527975 = 5291963) B5291963
theorem B11908457 : Blo 1393516 11908457 := bstep (se 2 (by rfl) ⟨4465671, by rfl⟩ : syracuseStep 11908457 = 8931343) B8931343
theorem B4707773 : Blo 1393516 4707773 := bstep (se 3 (by rfl) ⟨882707, by rfl⟩ : syracuseStep 4707773 = 1765415) B1765415
theorem B26818087 : Blo 1393516 26818087 := bstep (se 1 (by rfl) ⟨20113565, by rfl⟩ : syracuseStep 26818087 = 40227131) B40227131
theorem B4708151 : Blo 1393516 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B5298007 : Blo 1393516 5298007 := bstep (se 1 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 5298007 = 7947011) B7947011
theorem B36222871 : Blo 1393516 36222871 := bstep (se 1 (by rfl) ⟨27167153, by rfl⟩ : syracuseStep 36222871 = 54334307) B54334307
theorem B17864783 : Blo 1393516 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B5298311 : Blo 1393516 5298311 := bstep (se 1 (by rfl) ⟨3973733, by rfl⟩ : syracuseStep 5298311 = 7947467) B7947467
theorem B4708637 : Blo 1393516 4708637 := bstep (se 3 (by rfl) ⟨882869, by rfl⟩ : syracuseStep 4708637 = 1765739) B1765739
theorem B10189145 : Blo 1393516 10189145 := bstep (se 2 (by rfl) ⟨3820929, by rfl⟩ : syracuseStep 10189145 = 7641859) B7641859
theorem B3135851 : Blo 1393516 3135851 := bstep (se 1 (by rfl) ⟨2351888, by rfl⟩ : syracuseStep 3135851 = 4703777) B4703777
theorem B3348947 : Blo 1393516 3348947 := bstep (se 1 (by rfl) ⟨2511710, by rfl⟩ : syracuseStep 3348947 = 5023421) B5023421
theorem B3135995 : Blo 1393516 3135995 := bstep (se 1 (by rfl) ⟨2351996, by rfl⟩ : syracuseStep 3135995 = 4703993) B4703993
theorem B152656427 : Blo 1393516 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B14318153 : Blo 1393516 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B10050155 : Blo 1393516 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B3136121 : Blo 1393516 3136121 := bstep (se 2 (by rfl) ⟨1176045, by rfl⟩ : syracuseStep 3136121 = 2352091) B2352091
theorem B3136175 : Blo 1393516 3136175 := bstep (se 1 (by rfl) ⟨2352131, by rfl⟩ : syracuseStep 3136175 = 4704263) B4704263
theorem B3136247 : Blo 1393516 3136247 := bstep (se 1 (by rfl) ⟨2352185, by rfl⟩ : syracuseStep 3136247 = 4704371) B4704371
theorem B3529615 : Blo 1393516 3529615 := bstep (se 1 (by rfl) ⟨2647211, by rfl⟩ : syracuseStep 3529615 = 5294423) B5294423
theorem B3136427 : Blo 1393516 3136427 := bstep (se 1 (by rfl) ⟨2352320, by rfl⟩ : syracuseStep 3136427 = 4704641) B4704641
theorem B26811323 : Blo 1393516 26811323 := bstep (se 1 (by rfl) ⟨20108492, by rfl⟩ : syracuseStep 26811323 = 40216985) B40216985
theorem B3767393 : Blo 1393516 3767393 := bstep (se 2 (by rfl) ⟨1412772, by rfl⟩ : syracuseStep 3767393 = 2825545) B2825545
theorem B10591397 : Blo 1393516 10591397 := bstep (se 4 (by rfl) ⟨992943, by rfl⟩ : syracuseStep 10591397 = 1985887) B1985887
theorem B25443557 : Blo 1393516 25443557 := bstep (se 4 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 25443557 = 4770667) B4770667
theorem B11918603 : Blo 1393516 11918603 := bstep (se 1 (by rfl) ⟨8938952, by rfl⟩ : syracuseStep 11918603 = 17877905) B17877905
theorem B4709663 : Blo 1393516 4709663 := bstep (se 1 (by rfl) ⟨3532247, by rfl⟩ : syracuseStep 4709663 = 7064495) B7064495
theorem B7544125 : Blo 1393516 7544125 := bstep (se 3 (by rfl) ⟨1414523, by rfl⟩ : syracuseStep 7544125 = 2829047) B2829047
theorem B3530081 : Blo 1393516 3530081 := bstep (se 2 (by rfl) ⟨1323780, by rfl⟩ : syracuseStep 3530081 = 2647561) B2647561
theorem B3136967 : Blo 1393516 3136967 := bstep (se 1 (by rfl) ⟨2352725, by rfl⟩ : syracuseStep 3136967 = 4705451) B4705451
theorem B5955065 : Blo 1393516 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B6700603 : Blo 1393516 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B3350177 : Blo 1393516 3350177 := bstep (se 2 (by rfl) ⟨1256316, by rfl⟩ : syracuseStep 3350177 = 2512633) B2512633
theorem B13393667 : Blo 1393516 13393667 := bstep (se 1 (by rfl) ⟨10045250, by rfl⟩ : syracuseStep 13393667 = 20090501) B20090501
theorem B7061255 : Blo 1393516 7061255 := bstep (se 1 (by rfl) ⟨5295941, by rfl⟩ : syracuseStep 7061255 = 10591883) B10591883
theorem B12721961 : Blo 1393516 12721961 := bstep (se 2 (by rfl) ⟨4770735, by rfl⟩ : syracuseStep 12721961 = 9541471) B9541471
theorem B3530537 : Blo 1393516 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B5652271 : Blo 1393516 5652271 := bstep (se 1 (by rfl) ⟨4239203, by rfl⟩ : syracuseStep 5652271 = 8478407) B8478407
theorem B3137327 : Blo 1393516 3137327 := bstep (se 1 (by rfl) ⟨2352995, by rfl⟩ : syracuseStep 3137327 = 4705991) B4705991
theorem B53616491 : Blo 1393516 53616491 := bstep (se 1 (by rfl) ⟨40212368, by rfl⟩ : syracuseStep 53616491 = 80424737) B80424737
theorem B3530891 : Blo 1393516 3530891 := bstep (se 1 (by rfl) ⟨2648168, by rfl⟩ : syracuseStep 3530891 = 5296337) B5296337
theorem B8601881 : Blo 1393516 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B12272071 : Blo 1393516 12272071 := bstep (se 1 (by rfl) ⟨9204053, by rfl⟩ : syracuseStep 12272071 = 18408107) B18408107
theorem B3531215 : Blo 1393516 3531215 := bstep (se 1 (by rfl) ⟨2648411, by rfl⟩ : syracuseStep 3531215 = 5296823) B5296823
theorem B15884909 : Blo 1393516 15884909 := bstep (se 3 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 15884909 = 5956841) B5956841
theorem B2351929 : Blo 1393516 2351929 := bstep (se 2 (by rfl) ⟨881973, by rfl⟩ : syracuseStep 2351929 = 1763947) B1763947
theorem B1393519 : Blo 1393516 1393519 := bstep (se 1 (by rfl) ⟨1045139, by rfl⟩ : syracuseStep 1393519 = 2090279) B2090279
theorem B2351983 : Blo 1393516 2351983 := bstep (se 1 (by rfl) ⟨1763987, by rfl⟩ : syracuseStep 2351983 = 3527975) B3527975
theorem B7938971 : Blo 1393516 7938971 := bstep (se 1 (by rfl) ⟨5954228, by rfl⟩ : syracuseStep 7938971 = 11908457) B11908457
theorem B1393575 : Blo 1393516 1393575 := bstep (se 1 (by rfl) ⟨1045181, by rfl⟩ : syracuseStep 1393575 = 2090363) B2090363
theorem B3138515 : Blo 1393516 3138515 := bstep (se 1 (by rfl) ⟨2353886, by rfl⟩ : syracuseStep 3138515 = 4707773) B4707773
theorem B10585079 : Blo 1393516 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B1393659 : Blo 1393516 1393659 := bstep (se 1 (by rfl) ⟨1045244, by rfl⟩ : syracuseStep 1393659 = 2090489) B2090489
theorem B4703291 : Blo 1393516 4703291 := bstep (se 1 (by rfl) ⟨3527468, by rfl⟩ : syracuseStep 4703291 = 7054937) B7054937
theorem B1393727 : Blo 1393516 1393727 := bstep (se 1 (by rfl) ⟨1045295, by rfl⟩ : syracuseStep 1393727 = 2090591) B2090591
theorem B2352233 : Blo 1393516 2352233 := bstep (se 2 (by rfl) ⟨882087, by rfl⟩ : syracuseStep 2352233 = 1764175) B1764175
theorem B1393871 : Blo 1393516 1393871 := bstep (se 1 (by rfl) ⟨1045403, by rfl⟩ : syracuseStep 1393871 = 2090807) B2090807
theorem B3138767 : Blo 1393516 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B20382977 : Blo 1393516 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B4703561 : Blo 1393516 4703561 := bstep (se 2 (by rfl) ⟨1763835, by rfl⟩ : syracuseStep 4703561 = 3527671) B3527671
theorem B1394075 : Blo 1393516 1394075 := bstep (se 1 (by rfl) ⟨1045556, by rfl⟩ : syracuseStep 1394075 = 2091113) B2091113
theorem B3532207 : Blo 1393516 3532207 := bstep (se 1 (by rfl) ⟨2649155, by rfl⟩ : syracuseStep 3532207 = 5298311) B5298311
theorem B7063037 : Blo 1393516 7063037 := bstep (se 3 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 7063037 = 2648639) B2648639
theorem B3139091 : Blo 1393516 3139091 := bstep (se 1 (by rfl) ⟨2354318, by rfl⟩ : syracuseStep 3139091 = 4708637) B4708637
theorem B6792763 : Blo 1393516 6792763 := bstep (se 1 (by rfl) ⟨5094572, by rfl⟩ : syracuseStep 6792763 = 10189145) B10189145
theorem B2090567 : Blo 1393516 2090567 := bstep (se 1 (by rfl) ⟨1567925, by rfl⟩ : syracuseStep 2090567 = 3135851) B3135851
theorem B1394287 : Blo 1393516 1394287 := bstep (se 1 (by rfl) ⟨1045715, by rfl⟩ : syracuseStep 1394287 = 2091431) B2091431
theorem B2090663 : Blo 1393516 2090663 := bstep (se 1 (by rfl) ⟨1567997, by rfl⟩ : syracuseStep 2090663 = 3135995) B3135995
theorem B1394343 : Blo 1393516 1394343 := bstep (se 1 (by rfl) ⟨1045757, by rfl⟩ : syracuseStep 1394343 = 2091515) B2091515
theorem B101770951 : Blo 1393516 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B9545435 : Blo 1393516 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B2090747 : Blo 1393516 2090747 := bstep (se 1 (by rfl) ⟨1568060, by rfl⟩ : syracuseStep 2090747 = 3136121) B3136121
theorem B1394427 : Blo 1393516 1394427 := bstep (se 1 (by rfl) ⟨1045820, by rfl⟩ : syracuseStep 1394427 = 2091641) B2091641
theorem B4769543 : Blo 1393516 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B2090783 : Blo 1393516 2090783 := bstep (se 1 (by rfl) ⟨1568087, by rfl⟩ : syracuseStep 2090783 = 3136175) B3136175
theorem B1394463 : Blo 1393516 1394463 := bstep (se 1 (by rfl) ⟨1045847, by rfl⟩ : syracuseStep 1394463 = 2091695) B2091695
theorem B2557759 : Blo 1393516 2557759 := bstep (se 1 (by rfl) ⟨1918319, by rfl⟩ : syracuseStep 2557759 = 3836639) B3836639
theorem B1394495 : Blo 1393516 1394495 := bstep (se 1 (by rfl) ⟨1045871, by rfl⟩ : syracuseStep 1394495 = 2091743) B2091743
theorem B2090831 : Blo 1393516 2090831 := bstep (se 1 (by rfl) ⟨1568123, by rfl⟩ : syracuseStep 2090831 = 3136247) B3136247
theorem B2090951 : Blo 1393516 2090951 := bstep (se 1 (by rfl) ⟨1568213, by rfl⟩ : syracuseStep 2090951 = 3136427) B3136427
theorem B1394671 : Blo 1393516 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B1394843 : Blo 1393516 1394843 := bstep (se 1 (by rfl) ⟨1046132, by rfl⟩ : syracuseStep 1394843 = 2092265) B2092265
theorem B1394879 : Blo 1393516 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B3139775 : Blo 1393516 3139775 := bstep (se 1 (by rfl) ⟨2354831, by rfl⟩ : syracuseStep 3139775 = 4709663) B4709663
theorem B2353387 : Blo 1393516 2353387 := bstep (se 1 (by rfl) ⟨1765040, by rfl⟩ : syracuseStep 2353387 = 3530081) B3530081
theorem B3770603 : Blo 1393516 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B20384011 : Blo 1393516 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B7063847 : Blo 1393516 7063847 := bstep (se 1 (by rfl) ⟨5297885, by rfl⟩ : syracuseStep 7063847 = 10595771) B10595771
theorem B2091305 : Blo 1393516 2091305 := bstep (se 2 (by rfl) ⟨784239, by rfl⟩ : syracuseStep 2091305 = 1568479) B1568479
theorem B2091311 : Blo 1393516 2091311 := bstep (se 1 (by rfl) ⟨1568483, by rfl⟩ : syracuseStep 2091311 = 3136967) B3136967
theorem B1394991 : Blo 1393516 1394991 := bstep (se 1 (by rfl) ⟨1046243, by rfl⟩ : syracuseStep 1394991 = 2092487) B2092487
theorem B7064009 : Blo 1393516 7064009 := bstep (se 2 (by rfl) ⟨2649003, by rfl⟩ : syracuseStep 7064009 = 5298007) B5298007
theorem B8481307 : Blo 1393516 8481307 := bstep (se 1 (by rfl) ⟨6360980, by rfl⟩ : syracuseStep 8481307 = 12721961) B12721961
theorem B2353691 : Blo 1393516 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B1395227 : Blo 1393516 1395227 := bstep (se 1 (by rfl) ⟨1046420, by rfl⟩ : syracuseStep 1395227 = 2092841) B2092841
theorem B2091551 : Blo 1393516 2091551 := bstep (se 1 (by rfl) ⟨1568663, by rfl⟩ : syracuseStep 2091551 = 3137327) B3137327
theorem B1395231 : Blo 1393516 1395231 := bstep (se 1 (by rfl) ⟨1046423, by rfl⟩ : syracuseStep 1395231 = 2092847) B2092847
theorem B35744327 : Blo 1393516 35744327 := bstep (se 1 (by rfl) ⟨26808245, by rfl⟩ : syracuseStep 35744327 = 53616491) B53616491
theorem B2091935 : Blo 1393516 2091935 := bstep (se 1 (by rfl) ⟨1568951, by rfl⟩ : syracuseStep 2091935 = 3137903) B3137903
theorem B2091983 : Blo 1393516 2091983 := bstep (se 1 (by rfl) ⟨1568987, by rfl⟩ : syracuseStep 2091983 = 3137975) B3137975
theorem B2092073 : Blo 1393516 2092073 := bstep (se 2 (by rfl) ⟨784527, by rfl⟩ : syracuseStep 2092073 = 1569055) B1569055
theorem B2092079 : Blo 1393516 2092079 := bstep (se 1 (by rfl) ⟨1569059, by rfl⟩ : syracuseStep 2092079 = 3138119) B3138119
theorem B2092103 : Blo 1393516 2092103 := bstep (se 1 (by rfl) ⟨1569077, by rfl⟩ : syracuseStep 2092103 = 3138155) B3138155
theorem B5958791 : Blo 1393516 5958791 := bstep (se 1 (by rfl) ⟨4469093, by rfl⟩ : syracuseStep 5958791 = 8938187) B8938187
theorem B2354359 : Blo 1393516 2354359 := bstep (se 1 (by rfl) ⟨1765769, by rfl⟩ : syracuseStep 2354359 = 3531539) B3531539
theorem B32206157 : Blo 1393516 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B2092367 : Blo 1393516 2092367 := bstep (se 1 (by rfl) ⟨1569275, by rfl⟩ : syracuseStep 2092367 = 3138551) B3138551
theorem B15068567 : Blo 1393516 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B2092457 : Blo 1393516 2092457 := bstep (se 2 (by rfl) ⟨784671, by rfl⟩ : syracuseStep 2092457 = 1569343) B1569343
theorem B2354663 : Blo 1393516 2354663 := bstep (se 1 (by rfl) ⟨1765997, by rfl⟩ : syracuseStep 2354663 = 3531995) B3531995
theorem B2354683 : Blo 1393516 2354683 := bstep (se 1 (by rfl) ⟨1766012, by rfl⟩ : syracuseStep 2354683 = 3532025) B3532025
theorem B2092607 : Blo 1393516 2092607 := bstep (se 1 (by rfl) ⟨1569455, by rfl⟩ : syracuseStep 2092607 = 3138911) B3138911
theorem B3968585 : Blo 1393516 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B1568551 : Blo 1393516 1568551 := bstep (se 1 (by rfl) ⟨1176413, by rfl⟩ : syracuseStep 1568551 = 2352827) B2352827
theorem B2092871 : Blo 1393516 2092871 := bstep (se 1 (by rfl) ⟨1569653, by rfl⟩ : syracuseStep 2092871 = 3139307) B3139307
theorem B12717901 : Blo 1393516 12717901 := bstep (se 3 (by rfl) ⟨2384606, by rfl⟩ : syracuseStep 12717901 = 4769213) B4769213
theorem B4706153 : Blo 1393516 4706153 := bstep (se 2 (by rfl) ⟨1764807, by rfl⟩ : syracuseStep 4706153 = 3529615) B3529615
theorem B1765243 : Blo 1393516 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B2092955 : Blo 1393516 2092955 := bstep (se 1 (by rfl) ⟨1569716, by rfl⟩ : syracuseStep 2092955 = 3139433) B3139433
theorem B11907121 : Blo 1393516 11907121 := bstep (se 2 (by rfl) ⟨4465170, by rfl⟩ : syracuseStep 11907121 = 8930341) B8930341
theorem B8482981 : Blo 1393516 8482981 := bstep (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) B1590559
theorem B2232631 : Blo 1393516 2232631 := bstep (se 1 (by rfl) ⟨1674473, by rfl⟩ : syracuseStep 2232631 = 3348947) B3348947
theorem B10727747 : Blo 1393516 10727747 := bstep (se 1 (by rfl) ⟨8045810, by rfl⟩ : syracuseStep 10727747 = 16091621) B16091621
theorem B11907395 : Blo 1393516 11907395 := bstep (se 1 (by rfl) ⟨8930546, by rfl⟩ : syracuseStep 11907395 = 17861093) B17861093
theorem B2978387 : Blo 1393516 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B4469363 : Blo 1393516 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B2511595 : Blo 1393516 2511595 := bstep (se 1 (by rfl) ⟨1883696, by rfl⟩ : syracuseStep 2511595 = 3767393) B3767393
theorem B8934137 : Blo 1393516 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B16962371 : Blo 1393516 16962371 := bstep (se 1 (by rfl) ⟨12721778, by rfl⟩ : syracuseStep 16962371 = 25443557) B25443557
theorem B67810121 : Blo 1393516 67810121 := bstep (se 2 (by rfl) ⟨25428795, by rfl⟩ : syracuseStep 67810121 = 50857591) B50857591
theorem B1569703 : Blo 1393516 1569703 := bstep (se 1 (by rfl) ⟨1177277, by rfl⟩ : syracuseStep 1569703 = 2354555) B2354555
theorem B3970043 : Blo 1393516 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B2233451 : Blo 1393516 2233451 := bstep (se 1 (by rfl) ⟨1675088, by rfl⟩ : syracuseStep 2233451 = 3350177) B3350177
theorem B4707503 : Blo 1393516 4707503 := bstep (se 1 (by rfl) ⟨3530627, by rfl⟩ : syracuseStep 4707503 = 7061255) B7061255
theorem B48297161 : Blo 1393516 48297161 := bstep (se 2 (by rfl) ⟨18111435, by rfl⟩ : syracuseStep 48297161 = 36222871) B36222871
theorem B5805431 : Blo 1393516 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B325998229 : Blo 1393516 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B3970795 : Blo 1393516 3970795 := bstep (se 1 (by rfl) ⟨2978096, by rfl⟩ : syracuseStep 3970795 = 5956193) B5956193
theorem B5093435 : Blo 1393516 5093435 := bstep (se 1 (by rfl) ⟨3820076, by rfl⟩ : syracuseStep 5093435 = 7640153) B7640153
theorem B3528947 : Blo 1393516 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B3528967 : Blo 1393516 3528967 := bstep (se 1 (by rfl) ⟨2646725, by rfl⟩ : syracuseStep 3528967 = 5293451) B5293451
theorem B3349129 : Blo 1393516 3349129 := bstep (se 2 (by rfl) ⟨1255923, by rfl⟩ : syracuseStep 3349129 = 2511847) B2511847
theorem B7060121 : Blo 1393516 7060121 := bstep (se 2 (by rfl) ⟨2647545, by rfl⟩ : syracuseStep 7060121 = 5295091) B5295091
theorem B11909855 : Blo 1393516 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B3136463 : Blo 1393516 3136463 := bstep (se 1 (by rfl) ⟨2352347, by rfl⟩ : syracuseStep 3136463 = 4704695) B4704695
theorem B3136481 : Blo 1393516 3136481 := bstep (se 2 (by rfl) ⟨1176180, by rfl⟩ : syracuseStep 3136481 = 2352361) B2352361
theorem B3136553 : Blo 1393516 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B6700103 : Blo 1393516 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B4709447 : Blo 1393516 4709447 := bstep (se 1 (by rfl) ⟨3532085, by rfl⟩ : syracuseStep 4709447 = 7064171) B7064171
theorem B10058833 : Blo 1393516 10058833 := bstep (se 2 (by rfl) ⟨3772062, by rfl⟩ : syracuseStep 10058833 = 7544125) B7544125
theorem B15293555 : Blo 1393516 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B4709501 : Blo 1393516 4709501 := bstep (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) B1766063
theorem B7543955 : Blo 1393516 7543955 := bstep (se 1 (by rfl) ⟨5657966, by rfl⟩ : syracuseStep 7543955 = 11315933) B11315933
theorem B3349687 : Blo 1393516 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B3972311 : Blo 1393516 3972311 := bstep (se 1 (by rfl) ⟨2979233, by rfl⟩ : syracuseStep 3972311 = 5958467) B5958467
theorem B17874215 : Blo 1393516 17874215 := bstep (se 1 (by rfl) ⟨13405661, by rfl⟩ : syracuseStep 17874215 = 26811323) B26811323
theorem B35757449 : Blo 1393516 35757449 := bstep (se 2 (by rfl) ⟨13409043, by rfl⟩ : syracuseStep 35757449 = 26818087) B26818087
theorem B4709771 : Blo 1393516 4709771 := bstep (se 1 (by rfl) ⟨3532328, by rfl⟩ : syracuseStep 4709771 = 7064657) B7064657
theorem B7060931 : Blo 1393516 7060931 := bstep (se 1 (by rfl) ⟨5295698, by rfl⟩ : syracuseStep 7060931 = 10591397) B10591397
theorem B7945735 : Blo 1393516 7945735 := bstep (se 1 (by rfl) ⟨5959301, by rfl⟩ : syracuseStep 7945735 = 11918603) B11918603
theorem B7536361 : Blo 1393516 7536361 := bstep (se 2 (by rfl) ⟨2826135, by rfl⟩ : syracuseStep 7536361 = 5652271) B5652271
theorem B3530567 : Blo 1393516 3530567 := bstep (se 1 (by rfl) ⟨2647925, by rfl⟩ : syracuseStep 3530567 = 5295851) B5295851
theorem B40189769 : Blo 1393516 40189769 := bstep (se 2 (by rfl) ⟨15071163, by rfl⟩ : syracuseStep 40189769 = 30142327) B30142327
theorem B8929111 : Blo 1393516 8929111 := bstep (se 1 (by rfl) ⟨6696833, by rfl⟩ : syracuseStep 8929111 = 13393667) B13393667
theorem B15876161 : Blo 1393516 15876161 := bstep (se 2 (by rfl) ⟨5953560, by rfl⟩ : syracuseStep 15876161 = 11907121) B11907121
theorem B7151831 : Blo 1393516 7151831 := bstep (se 1 (by rfl) ⟨5363873, by rfl⟩ : syracuseStep 7151831 = 10727747) B10727747
theorem B7938263 : Blo 1393516 7938263 := bstep (se 1 (by rfl) ⟨5953697, by rfl⟩ : syracuseStep 7938263 = 11907395) B11907395
theorem B5955869 : Blo 1393516 5955869 := bstep (se 3 (by rfl) ⟨1116725, by rfl⟩ : syracuseStep 5955869 = 2233451) B2233451
theorem B3137849 : Blo 1393516 3137849 := bstep (se 2 (by rfl) ⟨1176693, by rfl⟩ : syracuseStep 3137849 = 2353387) B2353387
theorem B5956091 : Blo 1393516 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B5292647 : Blo 1393516 5292647 := bstep (se 1 (by rfl) ⟨3969485, by rfl⟩ : syracuseStep 5292647 = 7938971) B7938971
theorem B2646695 : Blo 1393516 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B22938349 : Blo 1393516 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B3138335 : Blo 1393516 3138335 := bstep (se 1 (by rfl) ⟨2353751, by rfl⟩ : syracuseStep 3138335 = 4707503) B4707503
theorem B4465505 : Blo 1393516 4465505 := bstep (se 2 (by rfl) ⟨1674564, by rfl⟩ : syracuseStep 4465505 = 3349129) B3349129
theorem B1393711 : Blo 1393516 1393711 := bstep (se 1 (by rfl) ⟨1045283, by rfl⟩ : syracuseStep 1393711 = 2090567) B2090567
theorem B1393775 : Blo 1393516 1393775 := bstep (se 1 (by rfl) ⟨1045331, by rfl⟩ : syracuseStep 1393775 = 2090663) B2090663
theorem B1393831 : Blo 1393516 1393831 := bstep (se 1 (by rfl) ⟨1045373, by rfl⟩ : syracuseStep 1393831 = 2090747) B2090747
theorem B3179695 : Blo 1393516 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B1393855 : Blo 1393516 1393855 := bstep (se 1 (by rfl) ⟨1045391, by rfl⟩ : syracuseStep 1393855 = 2090783) B2090783
theorem B1393887 : Blo 1393516 1393887 := bstep (se 1 (by rfl) ⟨1045415, by rfl⟩ : syracuseStep 1393887 = 2090831) B2090831
theorem B1393967 : Blo 1393516 1393967 := bstep (se 1 (by rfl) ⟨1045475, by rfl⟩ : syracuseStep 1393967 = 2090951) B2090951
theorem B13411777 : Blo 1393516 13411777 := bstep (se 2 (by rfl) ⟨5029416, by rfl⟩ : syracuseStep 13411777 = 10058833) B10058833
theorem B2352631 : Blo 1393516 2352631 := bstep (se 1 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 2352631 = 3528947) B3528947
theorem B1394203 : Blo 1393516 1394203 := bstep (se 1 (by rfl) ⟨1045652, by rfl⟩ : syracuseStep 1394203 = 2091305) B2091305
theorem B1394207 : Blo 1393516 1394207 := bstep (se 1 (by rfl) ⟨1045655, by rfl⟩ : syracuseStep 1394207 = 2091311) B2091311
theorem B4466249 : Blo 1393516 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B3139145 : Blo 1393516 3139145 := bstep (se 2 (by rfl) ⟨1177179, by rfl⟩ : syracuseStep 3139145 = 2354359) B2354359
theorem B1394367 : Blo 1393516 1394367 := bstep (se 1 (by rfl) ⟨1045775, by rfl⟩ : syracuseStep 1394367 = 2091551) B2091551
theorem B7939903 : Blo 1393516 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B1394623 : Blo 1393516 1394623 := bstep (se 1 (by rfl) ⟨1045967, by rfl⟩ : syracuseStep 1394623 = 2091935) B2091935
theorem B2090975 : Blo 1393516 2090975 := bstep (se 1 (by rfl) ⟨1568231, by rfl⟩ : syracuseStep 2090975 = 3136463) B3136463
theorem B1394655 : Blo 1393516 1394655 := bstep (se 1 (by rfl) ⟨1045991, by rfl⟩ : syracuseStep 1394655 = 2091983) B2091983
theorem B2090987 : Blo 1393516 2090987 := bstep (se 1 (by rfl) ⟨1568240, by rfl⟩ : syracuseStep 2090987 = 3136481) B3136481
theorem B3139577 : Blo 1393516 3139577 := bstep (se 2 (by rfl) ⟨1177341, by rfl⟩ : syracuseStep 3139577 = 2354683) B2354683
theorem B10594313 : Blo 1393516 10594313 := bstep (se 2 (by rfl) ⟨3972867, by rfl⟩ : syracuseStep 10594313 = 7945735) B7945735
theorem B2091035 : Blo 1393516 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B1394715 : Blo 1393516 1394715 := bstep (se 1 (by rfl) ⟨1046036, by rfl⟩ : syracuseStep 1394715 = 2092073) B2092073
theorem B1394719 : Blo 1393516 1394719 := bstep (se 1 (by rfl) ⟨1046039, by rfl⟩ : syracuseStep 1394719 = 2092079) B2092079
theorem B4466735 : Blo 1393516 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B1394735 : Blo 1393516 1394735 := bstep (se 1 (by rfl) ⟨1046051, by rfl⟩ : syracuseStep 1394735 = 2092103) B2092103
theorem B3139631 : Blo 1393516 3139631 := bstep (se 1 (by rfl) ⟨2354723, by rfl⟩ : syracuseStep 3139631 = 4709447) B4709447
theorem B3139667 : Blo 1393516 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B2648207 : Blo 1393516 2648207 := bstep (se 1 (by rfl) ⟨1986155, by rfl⟩ : syracuseStep 2648207 = 3972311) B3972311
theorem B1394911 : Blo 1393516 1394911 := bstep (se 1 (by rfl) ⟨1046183, by rfl⟩ : syracuseStep 1394911 = 2092367) B2092367
theorem B135694601 : Blo 1393516 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B3139847 : Blo 1393516 3139847 := bstep (se 1 (by rfl) ⟨2354885, by rfl⟩ : syracuseStep 3139847 = 4709771) B4709771
theorem B10045711 : Blo 1393516 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B1394971 : Blo 1393516 1394971 := bstep (se 1 (by rfl) ⟨1046228, by rfl⟩ : syracuseStep 1394971 = 2092457) B2092457
theorem B5294393 : Blo 1393516 5294393 := bstep (se 2 (by rfl) ⟨1985397, by rfl⟩ : syracuseStep 5294393 = 3970795) B3970795
theorem B1395071 : Blo 1393516 1395071 := bstep (se 1 (by rfl) ⟨1046303, by rfl⟩ : syracuseStep 1395071 = 2092607) B2092607
theorem B2091401 : Blo 1393516 2091401 := bstep (se 2 (by rfl) ⟨784275, by rfl⟩ : syracuseStep 2091401 = 1568551) B1568551
theorem B3410345 : Blo 1393516 3410345 := bstep (se 2 (by rfl) ⟨1278879, by rfl⟩ : syracuseStep 3410345 = 2557759) B2557759
theorem B11905481 : Blo 1393516 11905481 := bstep (se 2 (by rfl) ⟨4464555, by rfl⟩ : syracuseStep 11905481 = 8929111) B8929111
theorem B2353657 : Blo 1393516 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B2353711 : Blo 1393516 2353711 := bstep (se 1 (by rfl) ⟨1765283, by rfl⟩ : syracuseStep 2353711 = 3530567) B3530567
theorem B1395247 : Blo 1393516 1395247 := bstep (se 1 (by rfl) ⟨1046435, by rfl⟩ : syracuseStep 1395247 = 2092871) B2092871
theorem B1395303 : Blo 1393516 1395303 := bstep (se 1 (by rfl) ⟨1046477, by rfl⟩ : syracuseStep 1395303 = 2092955) B2092955
theorem B2353927 : Blo 1393516 2353927 := bstep (se 1 (by rfl) ⟨1765445, by rfl⟩ : syracuseStep 2353927 = 3530891) B3530891
theorem B2354143 : Blo 1393516 2354143 := bstep (se 1 (by rfl) ⟨1765607, by rfl⟩ : syracuseStep 2354143 = 3531215) B3531215
theorem B4705289 : Blo 1393516 4705289 := bstep (se 2 (by rfl) ⟨1764483, by rfl⟩ : syracuseStep 4705289 = 3528967) B3528967
theorem B1985591 : Blo 1393516 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B2976841 : Blo 1393516 2976841 := bstep (se 2 (by rfl) ⟨1116315, by rfl⟩ : syracuseStep 2976841 = 2232631) B2232631
theorem B11308247 : Blo 1393516 11308247 := bstep (se 1 (by rfl) ⟨8481185, by rfl⟩ : syracuseStep 11308247 = 16962371) B16962371
theorem B45206747 : Blo 1393516 45206747 := bstep (se 1 (by rfl) ⟨33905060, by rfl⟩ : syracuseStep 45206747 = 67810121) B67810121
theorem B16362761 : Blo 1393516 16362761 := bstep (se 2 (by rfl) ⟨6136035, by rfl⟩ : syracuseStep 16362761 = 12272071) B12272071
theorem B2092343 : Blo 1393516 2092343 := bstep (se 1 (by rfl) ⟨1569257, by rfl⟩ : syracuseStep 2092343 = 3138515) B3138515
theorem B7056719 : Blo 1393516 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B11308409 : Blo 1393516 11308409 := bstep (se 2 (by rfl) ⟨4240653, by rfl⟩ : syracuseStep 11308409 = 8481307) B8481307
theorem B1568155 : Blo 1393516 1568155 := bstep (se 1 (by rfl) ⟨1176116, by rfl⟩ : syracuseStep 1568155 = 2352233) B2352233
theorem B32198107 : Blo 1393516 32198107 := bstep (se 1 (by rfl) ⟨24148580, by rfl⟩ : syracuseStep 32198107 = 48297161) B48297161
theorem B2092511 : Blo 1393516 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B3870287 : Blo 1393516 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B2092727 : Blo 1393516 2092727 := bstep (se 1 (by rfl) ⟨1569545, by rfl⟩ : syracuseStep 2092727 = 3139091) B3139091
theorem B2092937 : Blo 1393516 2092937 := bstep (se 2 (by rfl) ⟨784851, by rfl⟩ : syracuseStep 2092937 = 1569703) B1569703
theorem B3395623 : Blo 1393516 3395623 := bstep (se 1 (by rfl) ⟨2546717, by rfl⟩ : syracuseStep 3395623 = 5093435) B5093435
theorem B2093183 : Blo 1393516 2093183 := bstep (se 1 (by rfl) ⟨1569887, by rfl⟩ : syracuseStep 2093183 = 3139775) B3139775
theorem B1569127 : Blo 1393516 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B4706747 : Blo 1393516 4706747 := bstep (se 1 (by rfl) ⟨3530060, by rfl⟩ : syracuseStep 4706747 = 7060121) B7060121
theorem B10195703 : Blo 1393516 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B9057017 : Blo 1393516 9057017 := bstep (se 2 (by rfl) ⟨3396381, by rfl⟩ : syracuseStep 9057017 = 6792763) B6792763
theorem B11916143 : Blo 1393516 11916143 := bstep (se 1 (by rfl) ⟨8937107, by rfl⟩ : syracuseStep 11916143 = 17874215) B17874215
theorem B434664305 : Blo 1393516 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B4707287 : Blo 1393516 4707287 := bstep (se 1 (by rfl) ⟨3530465, by rfl⟩ : syracuseStep 4707287 = 7060931) B7060931
theorem B10048481 : Blo 1393516 10048481 := bstep (se 2 (by rfl) ⟨3768180, by rfl⟩ : syracuseStep 10048481 = 7536361) B7536361
theorem B1569775 : Blo 1393516 1569775 := bstep (se 1 (by rfl) ⟨1177331, by rfl⟩ : syracuseStep 1569775 = 2354663) B2354663
theorem B26793179 : Blo 1393516 26793179 := bstep (se 1 (by rfl) ⟨20094884, by rfl⟩ : syracuseStep 26793179 = 40189769) B40189769
theorem B11310641 : Blo 1393516 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B27178681 : Blo 1393516 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B10589939 : Blo 1393516 10589939 := bstep (se 1 (by rfl) ⟨7942454, by rfl⟩ : syracuseStep 10589939 = 15884909) B15884909
theorem B2979575 : Blo 1393516 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B3135527 : Blo 1393516 3135527 := bstep (se 1 (by rfl) ⟨2351645, by rfl⟩ : syracuseStep 3135527 = 4703291) B4703291
theorem B13588651 : Blo 1393516 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B3135707 : Blo 1393516 3135707 := bstep (se 1 (by rfl) ⟨2351780, by rfl⟩ : syracuseStep 3135707 = 4703561) B4703561
theorem B3348793 : Blo 1393516 3348793 := bstep (se 2 (by rfl) ⟨1255797, by rfl⟩ : syracuseStep 3348793 = 2511595) B2511595
theorem B4708691 : Blo 1393516 4708691 := bstep (se 1 (by rfl) ⟨3531518, by rfl⟩ : syracuseStep 4708691 = 7063037) B7063037
theorem B3135905 : Blo 1393516 3135905 := bstep (se 2 (by rfl) ⟨1175964, by rfl⟩ : syracuseStep 3135905 = 2351929) B2351929
theorem B6363623 : Blo 1393516 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B3135977 : Blo 1393516 3135977 := bstep (se 2 (by rfl) ⟨1175991, by rfl⟩ : syracuseStep 3135977 = 2351983) B2351983
theorem B2513735 : Blo 1393516 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B4709231 : Blo 1393516 4709231 := bstep (se 1 (by rfl) ⟨3531923, by rfl⟩ : syracuseStep 4709231 = 7063847) B7063847
theorem B4709339 : Blo 1393516 4709339 := bstep (se 1 (by rfl) ⟨3532004, by rfl⟩ : syracuseStep 4709339 = 7064009) B7064009
theorem B23829551 : Blo 1393516 23829551 := bstep (se 1 (by rfl) ⟨17872163, by rfl⟩ : syracuseStep 23829551 = 35744327) B35744327
theorem B4709609 : Blo 1393516 4709609 := bstep (se 2 (by rfl) ⟨1766103, by rfl⟩ : syracuseStep 4709609 = 3532207) B3532207
theorem B3972527 : Blo 1393516 3972527 := bstep (se 1 (by rfl) ⟨2979395, by rfl⟩ : syracuseStep 3972527 = 5958791) B5958791
theorem B5029303 : Blo 1393516 5029303 := bstep (se 1 (by rfl) ⟨3771977, by rfl⟩ : syracuseStep 5029303 = 7543955) B7543955
theorem B21470771 : Blo 1393516 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B23838299 : Blo 1393516 23838299 := bstep (se 1 (by rfl) ⟨17878724, by rfl⟩ : syracuseStep 23838299 = 35757449) B35757449
theorem B2645723 : Blo 1393516 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B16957201 : Blo 1393516 16957201 := bstep (se 2 (by rfl) ⟨6358950, by rfl⟩ : syracuseStep 16957201 = 12717901) B12717901
theorem B3137435 : Blo 1393516 3137435 := bstep (se 1 (by rfl) ⟨2353076, by rfl⟩ : syracuseStep 3137435 = 4706153) B4706153
theorem B10584107 : Blo 1393516 10584107 := bstep (se 1 (by rfl) ⟨7938080, by rfl⟩ : syracuseStep 10584107 = 15876161) B15876161
theorem B4767887 : Blo 1393516 4767887 := bstep (se 1 (by rfl) ⟨3575915, by rfl⟩ : syracuseStep 4767887 = 7151831) B7151831
theorem B5292175 : Blo 1393516 5292175 := bstep (se 1 (by rfl) ⟨3969131, by rfl⟩ : syracuseStep 5292175 = 7938263) B7938263
theorem B3137831 : Blo 1393516 3137831 := bstep (se 1 (by rfl) ⟨2353373, by rfl⟩ : syracuseStep 3137831 = 4706747) B4706747
theorem B4465057 : Blo 1393516 4465057 := bstep (se 2 (by rfl) ⟨1674396, by rfl⟩ : syracuseStep 4465057 = 3348793) B3348793
theorem B6038011 : Blo 1393516 6038011 := bstep (se 1 (by rfl) ⟨4528508, by rfl⟩ : syracuseStep 6038011 = 9057017) B9057017
theorem B289776203 : Blo 1393516 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B3138191 : Blo 1393516 3138191 := bstep (se 1 (by rfl) ⟨2353643, by rfl⟩ : syracuseStep 3138191 = 4707287) B4707287
theorem B3138209 : Blo 1393516 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B3138281 : Blo 1393516 3138281 := bstep (se 2 (by rfl) ⟨1176855, by rfl⟩ : syracuseStep 3138281 = 2353711) B2353711
theorem B3138569 : Blo 1393516 3138569 := bstep (se 2 (by rfl) ⟨1176963, by rfl⟩ : syracuseStep 3138569 = 2353927) B2353927
theorem B3138857 : Blo 1393516 3138857 := bstep (se 2 (by rfl) ⟨1177071, by rfl⟩ : syracuseStep 3138857 = 2354143) B2354143
theorem B1393983 : Blo 1393516 1393983 := bstep (se 1 (by rfl) ⟨1045487, by rfl⟩ : syracuseStep 1393983 = 2090975) B2090975
theorem B1393991 : Blo 1393516 1393991 := bstep (se 1 (by rfl) ⟨1045493, by rfl⟩ : syracuseStep 1393991 = 2090987) B2090987
theorem B7062875 : Blo 1393516 7062875 := bstep (se 1 (by rfl) ⟨5297156, by rfl⟩ : syracuseStep 7062875 = 10594313) B10594313
theorem B1394023 : Blo 1393516 1394023 := bstep (se 1 (by rfl) ⟨1045517, by rfl⟩ : syracuseStep 1394023 = 2091035) B2091035
theorem B2090351 : Blo 1393516 2090351 := bstep (se 1 (by rfl) ⟨1567763, by rfl⟩ : syracuseStep 2090351 = 3135527) B3135527
theorem B53577125 : Blo 1393516 53577125 := bstep (se 4 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 53577125 = 10045711) B10045711
theorem B2090471 : Blo 1393516 2090471 := bstep (se 1 (by rfl) ⟨1567853, by rfl⟩ : syracuseStep 2090471 = 3135707) B3135707
theorem B3139127 : Blo 1393516 3139127 := bstep (se 1 (by rfl) ⟨2354345, by rfl⟩ : syracuseStep 3139127 = 4708691) B4708691
theorem B1394267 : Blo 1393516 1394267 := bstep (se 1 (by rfl) ⟨1045700, by rfl⟩ : syracuseStep 1394267 = 2091401) B2091401
theorem B2090603 : Blo 1393516 2090603 := bstep (se 1 (by rfl) ⟨1567952, by rfl⟩ : syracuseStep 2090603 = 3135905) B3135905
theorem B2090651 : Blo 1393516 2090651 := bstep (se 1 (by rfl) ⟨1567988, by rfl⟩ : syracuseStep 2090651 = 3135977) B3135977
theorem B2090873 : Blo 1393516 2090873 := bstep (se 2 (by rfl) ⟨784077, by rfl⟩ : syracuseStep 2090873 = 1568155) B1568155
theorem B7055261 : Blo 1393516 7055261 := bstep (se 3 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 7055261 = 2645723) B2645723
theorem B3139487 : Blo 1393516 3139487 := bstep (se 1 (by rfl) ⟨2354615, by rfl⟩ : syracuseStep 3139487 = 4709231) B4709231
theorem B3139559 : Blo 1393516 3139559 := bstep (se 1 (by rfl) ⟨2354669, by rfl⟩ : syracuseStep 3139559 = 4709339) B4709339
theorem B15886367 : Blo 1393516 15886367 := bstep (se 1 (by rfl) ⟨11914775, by rfl⟩ : syracuseStep 15886367 = 23829551) B23829551
theorem B7538831 : Blo 1393516 7538831 := bstep (se 1 (by rfl) ⟨5654123, by rfl⟩ : syracuseStep 7538831 = 11308247) B11308247
theorem B3139739 : Blo 1393516 3139739 := bstep (se 1 (by rfl) ⟨2354804, by rfl⟩ : syracuseStep 3139739 = 4709609) B4709609
theorem B1394895 : Blo 1393516 1394895 := bstep (se 1 (by rfl) ⟨1046171, by rfl⟩ : syracuseStep 1394895 = 2092343) B2092343
theorem B4704479 : Blo 1393516 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B7538939 : Blo 1393516 7538939 := bstep (se 1 (by rfl) ⟨5654204, by rfl⟩ : syracuseStep 7538939 = 11308409) B11308409
theorem B2648351 : Blo 1393516 2648351 := bstep (se 1 (by rfl) ⟨1986263, by rfl⟩ : syracuseStep 2648351 = 3972527) B3972527
theorem B1395007 : Blo 1393516 1395007 := bstep (se 1 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 1395007 = 2092511) B2092511
theorem B14313847 : Blo 1393516 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B10586537 : Blo 1393516 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B1395151 : Blo 1393516 1395151 := bstep (se 1 (by rfl) ⟨1046363, by rfl⟩ : syracuseStep 1395151 = 2092727) B2092727
theorem B1395291 : Blo 1393516 1395291 := bstep (se 1 (by rfl) ⟨1046468, by rfl⟩ : syracuseStep 1395291 = 2092937) B2092937
theorem B2091623 : Blo 1393516 2091623 := bstep (se 1 (by rfl) ⟨1568717, by rfl⟩ : syracuseStep 2091623 = 3137435) B3137435
theorem B1395455 : Blo 1393516 1395455 := bstep (se 1 (by rfl) ⟨1046591, by rfl⟩ : syracuseStep 1395455 = 2093183) B2093183
theorem B5294909 : Blo 1393516 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B2091899 : Blo 1393516 2091899 := bstep (se 1 (by rfl) ⟨1568924, by rfl⟩ : syracuseStep 2091899 = 3137849) B3137849
theorem B2092169 : Blo 1393516 2092169 := bstep (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) B1569127
theorem B2092223 : Blo 1393516 2092223 := bstep (se 1 (by rfl) ⟨1569167, by rfl⟩ : syracuseStep 2092223 = 3138335) B3138335
theorem B2977003 : Blo 1393516 2977003 := bstep (se 1 (by rfl) ⟨2232752, by rfl⟩ : syracuseStep 2977003 = 4465505) B4465505
theorem B17862119 : Blo 1393516 17862119 := bstep (se 1 (by rfl) ⟨13396589, by rfl⟩ : syracuseStep 17862119 = 26793179) B26793179
theorem B30584465 : Blo 1393516 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B7540427 : Blo 1393516 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B2977499 : Blo 1393516 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B2092763 : Blo 1393516 2092763 := bstep (se 1 (by rfl) ⟨1569572, by rfl⟩ : syracuseStep 2092763 = 3139145) B3139145
theorem B1986383 : Blo 1393516 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B16969661 : Blo 1393516 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B2093033 : Blo 1393516 2093033 := bstep (se 2 (by rfl) ⟨784887, by rfl⟩ : syracuseStep 2093033 = 1569775) B1569775
theorem B2093051 : Blo 1393516 2093051 := bstep (se 1 (by rfl) ⟨1569788, by rfl⟩ : syracuseStep 2093051 = 3139577) B3139577
theorem B2977823 : Blo 1393516 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B2093087 : Blo 1393516 2093087 := bstep (se 1 (by rfl) ⟨1569815, by rfl⟩ : syracuseStep 2093087 = 3139631) B3139631
theorem B2093111 : Blo 1393516 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B1765471 : Blo 1393516 1765471 := bstep (se 1 (by rfl) ⟨1324103, by rfl⟩ : syracuseStep 1765471 = 2648207) B2648207
theorem B3969121 : Blo 1393516 3969121 := bstep (se 2 (by rfl) ⟨1488420, by rfl⟩ : syracuseStep 3969121 = 2976841) B2976841
theorem B2093231 : Blo 1393516 2093231 := bstep (se 1 (by rfl) ⟨1569923, by rfl⟩ : syracuseStep 2093231 = 3139847) B3139847
theorem B4239593 : Blo 1393516 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B2273563 : Blo 1393516 2273563 := bstep (se 1 (by rfl) ⟨1705172, by rfl⟩ : syracuseStep 2273563 = 3410345) B3410345
theorem B7057853 : Blo 1393516 7057853 := bstep (se 3 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 7057853 = 2646695) B2646695
theorem B1675823 : Blo 1393516 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B6705737 : Blo 1393516 6705737 := bstep (se 2 (by rfl) ⟨2514651, by rfl⟩ : syracuseStep 6705737 = 5029303) B5029303
theorem B42930809 : Blo 1393516 42930809 := bstep (se 2 (by rfl) ⟨16099053, by rfl⟩ : syracuseStep 42930809 = 32198107) B32198107
theorem B36238241 : Blo 1393516 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B4527497 : Blo 1393516 4527497 := bstep (se 2 (by rfl) ⟨1697811, by rfl⟩ : syracuseStep 4527497 = 3395623) B3395623
theorem B174536117 : Blo 1393516 174536117 := bstep (se 5 (by rfl) ⟨8181380, by rfl⟩ : syracuseStep 174536117 = 16362761) B16362761
theorem B3970579 : Blo 1393516 3970579 := bstep (se 1 (by rfl) ⟨2977934, by rfl⟩ : syracuseStep 3970579 = 5955869) B5955869
theorem B18118201 : Blo 1393516 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B3970727 : Blo 1393516 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B3528431 : Blo 1393516 3528431 := bstep (se 1 (by rfl) ⟨2646323, by rfl⟩ : syracuseStep 3528431 = 5292647) B5292647
theorem B6797135 : Blo 1393516 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B7944095 : Blo 1393516 7944095 := bstep (se 1 (by rfl) ⟨5958071, by rfl⟩ : syracuseStep 7944095 = 11916143) B11916143
theorem B6698987 : Blo 1393516 6698987 := bstep (se 1 (by rfl) ⟨5024240, by rfl⟩ : syracuseStep 6698987 = 10048481) B10048481
theorem B7059959 : Blo 1393516 7059959 := bstep (se 1 (by rfl) ⟨5294969, by rfl⟩ : syracuseStep 7059959 = 10589939) B10589939
theorem B90463067 : Blo 1393516 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B3529595 : Blo 1393516 3529595 := bstep (se 1 (by rfl) ⟨2647196, by rfl⟩ : syracuseStep 3529595 = 5294393) B5294393
theorem B7936987 : Blo 1393516 7936987 := bstep (se 1 (by rfl) ⟨5952740, by rfl⟩ : syracuseStep 7936987 = 11905481) B11905481
theorem B17882369 : Blo 1393516 17882369 := bstep (se 2 (by rfl) ⟨6705888, by rfl⟩ : syracuseStep 17882369 = 13411777) B13411777
theorem B3136841 : Blo 1393516 3136841 := bstep (se 2 (by rfl) ⟨1176315, by rfl⟩ : syracuseStep 3136841 = 2352631) B2352631
theorem B3136859 : Blo 1393516 3136859 := bstep (se 1 (by rfl) ⟨2352644, by rfl⟩ : syracuseStep 3136859 = 4705289) B4705289
theorem B30137831 : Blo 1393516 30137831 := bstep (se 1 (by rfl) ⟨22603373, by rfl⟩ : syracuseStep 30137831 = 45206747) B45206747
theorem B22609601 : Blo 1393516 22609601 := bstep (se 2 (by rfl) ⟨8478600, by rfl⟩ : syracuseStep 22609601 = 16957201) B16957201
theorem B2580191 : Blo 1393516 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B15892199 : Blo 1393516 15892199 := bstep (se 1 (by rfl) ⟨11919149, by rfl⟩ : syracuseStep 15892199 = 23838299) B23838299
theorem B3178591 : Blo 1393516 3178591 := bstep (se 1 (by rfl) ⟨2383943, by rfl⟩ : syracuseStep 3178591 = 4767887) B4767887
theorem B5292161 : Blo 1393516 5292161 := bstep (se 2 (by rfl) ⟨1984560, by rfl⟩ : syracuseStep 5292161 = 3969121) B3969121
theorem B2826395 : Blo 1393516 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B3031417 : Blo 1393516 3031417 := bstep (se 2 (by rfl) ⟨1136781, by rfl⟩ : syracuseStep 3031417 = 2273563) B2273563
theorem B193184135 : Blo 1393516 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B24158827 : Blo 1393516 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B1393567 : Blo 1393516 1393567 := bstep (se 1 (by rfl) ⟨1045175, by rfl⟩ : syracuseStep 1393567 = 2090351) B2090351
theorem B35718083 : Blo 1393516 35718083 := bstep (se 1 (by rfl) ⟨26788562, by rfl⟩ : syracuseStep 35718083 = 53577125) B53577125
theorem B1393647 : Blo 1393516 1393647 := bstep (se 1 (by rfl) ⟨1045235, by rfl⟩ : syracuseStep 1393647 = 2090471) B2090471
theorem B1393735 : Blo 1393516 1393735 := bstep (se 1 (by rfl) ⟨1045301, by rfl⟩ : syracuseStep 1393735 = 2090603) B2090603
theorem B1393767 : Blo 1393516 1393767 := bstep (se 1 (by rfl) ⟨1045325, by rfl⟩ : syracuseStep 1393767 = 2090651) B2090651
theorem B2647151 : Blo 1393516 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B2352287 : Blo 1393516 2352287 := bstep (se 1 (by rfl) ⟨1764215, by rfl⟩ : syracuseStep 2352287 = 3528431) B3528431
theorem B4531423 : Blo 1393516 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B1393915 : Blo 1393516 1393915 := bstep (se 1 (by rfl) ⟨1045436, by rfl⟩ : syracuseStep 1393915 = 2090873) B2090873
theorem B4703507 : Blo 1393516 4703507 := bstep (se 1 (by rfl) ⟨3527630, by rfl⟩ : syracuseStep 4703507 = 7055261) B7055261
theorem B4465991 : Blo 1393516 4465991 := bstep (se 1 (by rfl) ⟨3349493, by rfl⟩ : syracuseStep 4465991 = 6698987) B6698987
theorem B1394415 : Blo 1393516 1394415 := bstep (se 1 (by rfl) ⟨1045811, by rfl⟩ : syracuseStep 1394415 = 2091623) B2091623
theorem B2353063 : Blo 1393516 2353063 := bstep (se 1 (by rfl) ⟨1764797, by rfl⟩ : syracuseStep 2353063 = 3529595) B3529595
theorem B1394599 : Blo 1393516 1394599 := bstep (se 1 (by rfl) ⟨1045949, by rfl⟩ : syracuseStep 1394599 = 2091899) B2091899
theorem B5294105 : Blo 1393516 5294105 := bstep (se 2 (by rfl) ⟨1985289, by rfl⟩ : syracuseStep 5294105 = 3970579) B3970579
theorem B1394779 : Blo 1393516 1394779 := bstep (se 1 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 1394779 = 2092169) B2092169
theorem B1394815 : Blo 1393516 1394815 := bstep (se 1 (by rfl) ⟨1046111, by rfl⟩ : syracuseStep 1394815 = 2092223) B2092223
theorem B11921579 : Blo 1393516 11921579 := bstep (se 1 (by rfl) ⟨8941184, by rfl⟩ : syracuseStep 11921579 = 17882369) B17882369
theorem B2091227 : Blo 1393516 2091227 := bstep (se 1 (by rfl) ⟨1568420, by rfl⟩ : syracuseStep 2091227 = 3136841) B3136841
theorem B2091239 : Blo 1393516 2091239 := bstep (se 1 (by rfl) ⟨1568429, by rfl⟩ : syracuseStep 2091239 = 3136859) B3136859
theorem B1984999 : Blo 1393516 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B1395175 : Blo 1393516 1395175 := bstep (se 1 (by rfl) ⟨1046381, by rfl⟩ : syracuseStep 1395175 = 2092763) B2092763
theorem B10594799 : Blo 1393516 10594799 := bstep (se 1 (by rfl) ⟨7946099, by rfl⟩ : syracuseStep 10594799 = 15892199) B15892199
theorem B1395355 : Blo 1393516 1395355 := bstep (se 1 (by rfl) ⟨1046516, by rfl⟩ : syracuseStep 1395355 = 2093033) B2093033
theorem B1395367 : Blo 1393516 1395367 := bstep (se 1 (by rfl) ⟨1046525, by rfl⟩ : syracuseStep 1395367 = 2093051) B2093051
theorem B1395391 : Blo 1393516 1395391 := bstep (se 1 (by rfl) ⟨1046543, by rfl⟩ : syracuseStep 1395391 = 2093087) B2093087
theorem B7056071 : Blo 1393516 7056071 := bstep (se 1 (by rfl) ⟨5292053, by rfl⟩ : syracuseStep 7056071 = 10584107) B10584107
theorem B1395407 : Blo 1393516 1395407 := bstep (se 1 (by rfl) ⟨1046555, by rfl⟩ : syracuseStep 1395407 = 2093111) B2093111
theorem B7940861 : Blo 1393516 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B1395487 : Blo 1393516 1395487 := bstep (se 1 (by rfl) ⟨1046615, by rfl⟩ : syracuseStep 1395487 = 2093231) B2093231
theorem B2353961 : Blo 1393516 2353961 := bstep (se 2 (by rfl) ⟨882735, by rfl⟩ : syracuseStep 2353961 = 1765471) B1765471
theorem B7056233 : Blo 1393516 7056233 := bstep (se 2 (by rfl) ⟨2646087, by rfl⟩ : syracuseStep 7056233 = 5292175) B5292175
theorem B2091887 : Blo 1393516 2091887 := bstep (se 1 (by rfl) ⟨1568915, by rfl⟩ : syracuseStep 2091887 = 3137831) B3137831
theorem B4705235 : Blo 1393516 4705235 := bstep (se 1 (by rfl) ⟨3528926, by rfl⟩ : syracuseStep 4705235 = 7057853) B7057853
theorem B2092127 : Blo 1393516 2092127 := bstep (se 1 (by rfl) ⟨1569095, by rfl⟩ : syracuseStep 2092127 = 3138191) B3138191
theorem B2092139 : Blo 1393516 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B2092187 : Blo 1393516 2092187 := bstep (se 1 (by rfl) ⟨1569140, by rfl⟩ : syracuseStep 2092187 = 3138281) B3138281
theorem B2092379 : Blo 1393516 2092379 := bstep (se 1 (by rfl) ⟨1569284, by rfl⟩ : syracuseStep 2092379 = 3138569) B3138569
theorem B2092571 : Blo 1393516 2092571 := bstep (se 1 (by rfl) ⟨1569428, by rfl⟩ : syracuseStep 2092571 = 3138857) B3138857
theorem B3018331 : Blo 1393516 3018331 := bstep (se 1 (by rfl) ⟨2263748, by rfl⟩ : syracuseStep 3018331 = 4527497) B4527497
theorem B2092751 : Blo 1393516 2092751 := bstep (se 1 (by rfl) ⟨1569563, by rfl⟩ : syracuseStep 2092751 = 3139127) B3139127
theorem B5296063 : Blo 1393516 5296063 := bstep (se 1 (by rfl) ⟨3972047, by rfl⟩ : syracuseStep 5296063 = 7944095) B7944095
theorem B2092991 : Blo 1393516 2092991 := bstep (se 1 (by rfl) ⟨1569743, by rfl⟩ : syracuseStep 2092991 = 3139487) B3139487
theorem B2093039 : Blo 1393516 2093039 := bstep (se 1 (by rfl) ⟨1569779, by rfl⟩ : syracuseStep 2093039 = 3139559) B3139559
theorem B5025887 : Blo 1393516 5025887 := bstep (se 1 (by rfl) ⟨3769415, by rfl⟩ : syracuseStep 5025887 = 7538831) B7538831
theorem B2093159 : Blo 1393516 2093159 := bstep (se 1 (by rfl) ⟨1569869, by rfl⟩ : syracuseStep 2093159 = 3139739) B3139739
theorem B4468861 : Blo 1393516 4468861 := bstep (se 3 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 4468861 = 1675823) B1675823
theorem B5025959 : Blo 1393516 5025959 := bstep (se 1 (by rfl) ⟨3769469, by rfl⟩ : syracuseStep 5025959 = 7538939) B7538939
theorem B1765567 : Blo 1393516 1765567 := bstep (se 1 (by rfl) ⟨1324175, by rfl⟩ : syracuseStep 1765567 = 2648351) B2648351
theorem B7057691 : Blo 1393516 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B3969337 : Blo 1393516 3969337 := bstep (se 2 (by rfl) ⟨1488501, by rfl⟩ : syracuseStep 3969337 = 2977003) B2977003
theorem B4706639 : Blo 1393516 4706639 := bstep (se 1 (by rfl) ⟨3529979, by rfl⟩ : syracuseStep 4706639 = 7059959) B7059959
theorem B5297021 : Blo 1393516 5297021 := bstep (se 3 (by rfl) ⟨993191, by rfl⟩ : syracuseStep 5297021 = 1986383) B1986383
theorem B20091887 : Blo 1393516 20091887 := bstep (se 1 (by rfl) ⟨15068915, by rfl⟩ : syracuseStep 20091887 = 30137831) B30137831
theorem B11908079 : Blo 1393516 11908079 := bstep (se 1 (by rfl) ⟨8931059, by rfl⟩ : syracuseStep 11908079 = 17862119) B17862119
theorem B5026951 : Blo 1393516 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B4470491 : Blo 1393516 4470491 := bstep (se 1 (by rfl) ⟨3352868, by rfl⟩ : syracuseStep 4470491 = 6705737) B6705737
theorem B28620539 : Blo 1393516 28620539 := bstep (se 1 (by rfl) ⟨21465404, by rfl⟩ : syracuseStep 28620539 = 42930809) B42930809
theorem B19085129 : Blo 1393516 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B5953409 : Blo 1393516 5953409 := bstep (se 2 (by rfl) ⟨2232528, by rfl⟩ : syracuseStep 5953409 = 4465057) B4465057
theorem B8050681 : Blo 1393516 8050681 := bstep (se 2 (by rfl) ⟨3019005, by rfl⟩ : syracuseStep 8050681 = 6038011) B6038011
theorem B4708583 : Blo 1393516 4708583 := bstep (se 1 (by rfl) ⟨3531437, by rfl⟩ : syracuseStep 4708583 = 7062875) B7062875
theorem B116357411 : Blo 1393516 116357411 := bstep (se 1 (by rfl) ⟨87268058, by rfl⟩ : syracuseStep 116357411 = 174536117) B174536117
theorem B10582649 : Blo 1393516 10582649 := bstep (se 2 (by rfl) ⟨3968493, by rfl⟩ : syracuseStep 10582649 = 7936987) B7936987
theorem B10590911 : Blo 1393516 10590911 := bstep (se 1 (by rfl) ⟨7943183, by rfl⟩ : syracuseStep 10590911 = 15886367) B15886367
theorem B3136319 : Blo 1393516 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B3529939 : Blo 1393516 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B60308711 : Blo 1393516 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B24157601 : Blo 1393516 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B20389643 : Blo 1393516 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B15073067 : Blo 1393516 15073067 := bstep (se 1 (by rfl) ⟨11304800, by rfl⟩ : syracuseStep 15073067 = 22609601) B22609601
theorem B1720127 : Blo 1393516 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B11313107 : Blo 1393516 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B3350591 : Blo 1393516 3350591 := bstep (se 1 (by rfl) ⟨2512943, by rfl⟩ : syracuseStep 3350591 = 5025887) B5025887
theorem B1884263 : Blo 1393516 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B3350639 : Blo 1393516 3350639 := bstep (se 1 (by rfl) ⟨2512979, by rfl⟩ : syracuseStep 3350639 = 5025959) B5025959
theorem B3137759 : Blo 1393516 3137759 := bstep (se 1 (by rfl) ⟨2353319, by rfl⟩ : syracuseStep 3137759 = 4706639) B4706639
theorem B5292449 : Blo 1393516 5292449 := bstep (se 2 (by rfl) ⟨1984668, by rfl⟩ : syracuseStep 5292449 = 3969337) B3969337
theorem B3531347 : Blo 1393516 3531347 := bstep (se 1 (by rfl) ⟨2648510, by rfl⟩ : syracuseStep 3531347 = 5297021) B5297021
theorem B2646665 : Blo 1393516 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B13394591 : Blo 1393516 13394591 := bstep (se 1 (by rfl) ⟨10045943, by rfl⟩ : syracuseStep 13394591 = 20091887) B20091887
theorem B7938719 : Blo 1393516 7938719 := bstep (se 1 (by rfl) ⟨5954039, by rfl⟩ : syracuseStep 7938719 = 11908079) B11908079
theorem B32211769 : Blo 1393516 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B19080359 : Blo 1393516 19080359 := bstep (se 1 (by rfl) ⟨14310269, by rfl⟩ : syracuseStep 19080359 = 28620539) B28620539
theorem B12723419 : Blo 1393516 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B7947719 : Blo 1393516 7947719 := bstep (se 1 (by rfl) ⟨5960789, by rfl⟩ : syracuseStep 7947719 = 11921579) B11921579
theorem B1394151 : Blo 1393516 1394151 := bstep (se 1 (by rfl) ⟨1045613, by rfl⟩ : syracuseStep 1394151 = 2091227) B2091227
theorem B1394159 : Blo 1393516 1394159 := bstep (se 1 (by rfl) ⟨1045619, by rfl⟩ : syracuseStep 1394159 = 2091239) B2091239
theorem B3139055 : Blo 1393516 3139055 := bstep (se 1 (by rfl) ⟨2354291, by rfl⟩ : syracuseStep 3139055 = 4708583) B4708583
theorem B6702601 : Blo 1393516 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B77571607 : Blo 1393516 77571607 := bstep (se 1 (by rfl) ⟨58178705, by rfl⟩ : syracuseStep 77571607 = 116357411) B116357411
theorem B7063199 : Blo 1393516 7063199 := bstep (se 1 (by rfl) ⟨5297399, by rfl⟩ : syracuseStep 7063199 = 10594799) B10594799
theorem B7055099 : Blo 1393516 7055099 := bstep (se 1 (by rfl) ⟨5291324, by rfl⟩ : syracuseStep 7055099 = 10582649) B10582649
theorem B4704047 : Blo 1393516 4704047 := bstep (se 1 (by rfl) ⟨3528035, by rfl⟩ : syracuseStep 4704047 = 7056071) B7056071
theorem B5293907 : Blo 1393516 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B2090879 : Blo 1393516 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B4704155 : Blo 1393516 4704155 := bstep (se 1 (by rfl) ⟨3528116, by rfl⟩ : syracuseStep 4704155 = 7056233) B7056233
theorem B1394591 : Blo 1393516 1394591 := bstep (se 1 (by rfl) ⟨1045943, by rfl⟩ : syracuseStep 1394591 = 2091887) B2091887
theorem B1394751 : Blo 1393516 1394751 := bstep (se 1 (by rfl) ⟨1046063, by rfl⟩ : syracuseStep 1394751 = 2092127) B2092127
theorem B1394759 : Blo 1393516 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B1394791 : Blo 1393516 1394791 := bstep (se 1 (by rfl) ⟨1046093, by rfl⟩ : syracuseStep 1394791 = 2092187) B2092187
theorem B4024441 : Blo 1393516 4024441 := bstep (se 2 (by rfl) ⟨1509165, by rfl⟩ : syracuseStep 4024441 = 3018331) B3018331
theorem B1394919 : Blo 1393516 1394919 := bstep (se 1 (by rfl) ⟨1046189, by rfl⟩ : syracuseStep 1394919 = 2092379) B2092379
theorem B1395047 : Blo 1393516 1395047 := bstep (se 1 (by rfl) ⟨1046285, by rfl⟩ : syracuseStep 1395047 = 2092571) B2092571
theorem B1395167 : Blo 1393516 1395167 := bstep (se 1 (by rfl) ⟨1046375, by rfl⟩ : syracuseStep 1395167 = 2092751) B2092751
theorem B13593095 : Blo 1393516 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B1395327 : Blo 1393516 1395327 := bstep (se 1 (by rfl) ⟨1046495, by rfl⟩ : syracuseStep 1395327 = 2092991) B2092991
theorem B1395359 : Blo 1393516 1395359 := bstep (se 1 (by rfl) ⟨1046519, by rfl⟩ : syracuseStep 1395359 = 2093039) B2093039
theorem B10734241 : Blo 1393516 10734241 := bstep (se 2 (by rfl) ⟨4025340, by rfl⟩ : syracuseStep 10734241 = 8050681) B8050681
theorem B1395439 : Blo 1393516 1395439 := bstep (se 1 (by rfl) ⟨1046579, by rfl⟩ : syracuseStep 1395439 = 2093159) B2093159
theorem B4705127 : Blo 1393516 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B2354089 : Blo 1393516 2354089 := bstep (se 2 (by rfl) ⟨882783, by rfl⟩ : syracuseStep 2354089 = 1765567) B1765567
theorem B128789423 : Blo 1393516 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B16952485 : Blo 1393516 16952485 := bstep (se 4 (by rfl) ⟨1589295, by rfl⟩ : syracuseStep 16952485 = 3178591) B3178591
theorem B23833925 : Blo 1393516 23833925 := bstep (se 4 (by rfl) ⟨2234430, by rfl⟩ : syracuseStep 23833925 = 4468861) B4468861
theorem B1764767 : Blo 1393516 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B1568191 : Blo 1393516 1568191 := bstep (se 1 (by rfl) ⟨1176143, by rfl⟩ : syracuseStep 1568191 = 2352287) B2352287
theorem B2977327 : Blo 1393516 2977327 := bstep (se 1 (by rfl) ⟨2232995, by rfl⟩ : syracuseStep 2977327 = 4465991) B4465991
theorem B3968939 : Blo 1393516 3968939 := bstep (se 1 (by rfl) ⟨2976704, by rfl⟩ : syracuseStep 3968939 = 5953409) B5953409
theorem B4706585 : Blo 1393516 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B6041897 : Blo 1393516 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B1569307 : Blo 1393516 1569307 := bstep (se 1 (by rfl) ⟨1176980, by rfl⟩ : syracuseStep 1569307 = 2353961) B2353961
theorem B16167557 : Blo 1393516 16167557 := bstep (se 4 (by rfl) ⟨1515708, by rfl⟩ : syracuseStep 16167557 = 3031417) B3031417
theorem B10048711 : Blo 1393516 10048711 := bstep (se 1 (by rfl) ⟨7536533, by rfl⟩ : syracuseStep 10048711 = 15073067) B15073067
theorem B7542071 : Blo 1393516 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B3528107 : Blo 1393516 3528107 := bstep (se 1 (by rfl) ⟨2646080, by rfl⟩ : syracuseStep 3528107 = 5292161) B5292161
theorem B23812055 : Blo 1393516 23812055 := bstep (se 1 (by rfl) ⟨17859041, by rfl⟩ : syracuseStep 23812055 = 35718083) B35718083
theorem B3135671 : Blo 1393516 3135671 := bstep (se 1 (by rfl) ⟨2351753, by rfl⟩ : syracuseStep 3135671 = 4703507) B4703507
theorem B2980327 : Blo 1393516 2980327 := bstep (se 1 (by rfl) ⟨2235245, by rfl⟩ : syracuseStep 2980327 = 4470491) B4470491
theorem B3529403 : Blo 1393516 3529403 := bstep (se 1 (by rfl) ⟨2647052, by rfl⟩ : syracuseStep 3529403 = 5294105) B5294105
theorem B7060607 : Blo 1393516 7060607 := bstep (se 1 (by rfl) ⟨5295455, by rfl⟩ : syracuseStep 7060607 = 10590911) B10590911
theorem B3136823 : Blo 1393516 3136823 := bstep (se 1 (by rfl) ⟨2352617, by rfl⟩ : syracuseStep 3136823 = 4705235) B4705235
theorem B40205807 : Blo 1393516 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B4587005 : Blo 1393516 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B16105067 : Blo 1393516 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B3137417 : Blo 1393516 3137417 := bstep (se 2 (by rfl) ⟨1176531, by rfl⟩ : syracuseStep 3137417 = 2353063) B2353063
theorem B7061417 : Blo 1393516 7061417 := bstep (se 2 (by rfl) ⟨2648031, by rfl⟩ : syracuseStep 7061417 = 5296063) B5296063
theorem B5365921 : Blo 1393516 5365921 := bstep (se 2 (by rfl) ⟨2012220, by rfl⟩ : syracuseStep 5365921 = 4024441) B4024441
theorem B3137723 : Blo 1393516 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B8929727 : Blo 1393516 8929727 := bstep (se 1 (by rfl) ⟨6697295, by rfl⟩ : syracuseStep 8929727 = 13394591) B13394591
theorem B5292479 : Blo 1393516 5292479 := bstep (se 1 (by rfl) ⟨3969359, by rfl⟩ : syracuseStep 5292479 = 7938719) B7938719
theorem B3973769 : Blo 1393516 3973769 := bstep (se 2 (by rfl) ⟨1490163, by rfl⟩ : syracuseStep 3973769 = 2980327) B2980327
theorem B14312321 : Blo 1393516 14312321 := bstep (se 2 (by rfl) ⟨5367120, by rfl⟩ : syracuseStep 14312321 = 10734241) B10734241
theorem B2352071 : Blo 1393516 2352071 := bstep (se 1 (by rfl) ⟨1764053, by rfl⟩ : syracuseStep 2352071 = 3528107) B3528107
theorem B4703399 : Blo 1393516 4703399 := bstep (se 1 (by rfl) ⟨3527549, by rfl⟩ : syracuseStep 4703399 = 7055099) B7055099
theorem B3138785 : Blo 1393516 3138785 := bstep (se 2 (by rfl) ⟨1177044, by rfl⟩ : syracuseStep 3138785 = 2354089) B2354089
theorem B1393919 : Blo 1393516 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B2090447 : Blo 1393516 2090447 := bstep (se 1 (by rfl) ⟨1567835, by rfl⟩ : syracuseStep 2090447 = 3135671) B3135671
theorem B22603313 : Blo 1393516 22603313 := bstep (se 2 (by rfl) ⟨8476242, by rfl⟩ : syracuseStep 22603313 = 16952485) B16952485
theorem B9062063 : Blo 1393516 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B2352935 : Blo 1393516 2352935 := bstep (se 1 (by rfl) ⟨1764701, by rfl⟩ : syracuseStep 2352935 = 3529403) B3529403
theorem B2090921 : Blo 1393516 2090921 := bstep (se 2 (by rfl) ⟨784095, by rfl⟩ : syracuseStep 2090921 = 1568191) B1568191
theorem B2091215 : Blo 1393516 2091215 := bstep (se 1 (by rfl) ⟨1568411, by rfl⟩ : syracuseStep 2091215 = 3136823) B3136823
theorem B3058003 : Blo 1393516 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B2091611 : Blo 1393516 2091611 := bstep (se 1 (by rfl) ⟨1568708, by rfl⟩ : syracuseStep 2091611 = 3137417) B3137417
theorem B2091839 : Blo 1393516 2091839 := bstep (se 1 (by rfl) ⟨1568879, by rfl⟩ : syracuseStep 2091839 = 3137759) B3137759
theorem B15879077 : Blo 1393516 15879077 := bstep (se 4 (by rfl) ⟨1488663, by rfl⟩ : syracuseStep 15879077 = 2977327) B2977327
theorem B5024701 : Blo 1393516 5024701 := bstep (se 3 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 5024701 = 1884263) B1884263
theorem B2354231 : Blo 1393516 2354231 := bstep (se 1 (by rfl) ⟨1765673, by rfl⟩ : syracuseStep 2354231 = 3531347) B3531347
theorem B1764443 : Blo 1393516 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B2092409 : Blo 1393516 2092409 := bstep (se 2 (by rfl) ⟨784653, by rfl⟩ : syracuseStep 2092409 = 1569307) B1569307
theorem B2092703 : Blo 1393516 2092703 := bstep (se 1 (by rfl) ⟨1569527, by rfl⟩ : syracuseStep 2092703 = 3139055) B3139055
theorem B4706045 : Blo 1393516 4706045 := bstep (se 3 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 4706045 = 1764767) B1764767
theorem B13398281 : Blo 1393516 13398281 := bstep (se 2 (by rfl) ⟨5024355, by rfl⟩ : syracuseStep 13398281 = 10048711) B10048711
theorem B103428809 : Blo 1393516 103428809 := bstep (se 2 (by rfl) ⟨38785803, by rfl⟩ : syracuseStep 103428809 = 77571607) B77571607
theorem B4707071 : Blo 1393516 4707071 := bstep (se 1 (by rfl) ⟨3530303, by rfl⟩ : syracuseStep 4707071 = 7060607) B7060607
theorem B15889283 : Blo 1393516 15889283 := bstep (se 1 (by rfl) ⟨11916962, by rfl⟩ : syracuseStep 15889283 = 23833925) B23833925
theorem B10736711 : Blo 1393516 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B4707611 : Blo 1393516 4707611 := bstep (se 1 (by rfl) ⟨3530708, by rfl⟩ : syracuseStep 4707611 = 7061417) B7061417
theorem B2233727 : Blo 1393516 2233727 := bstep (se 1 (by rfl) ⟨1675295, by rfl⟩ : syracuseStep 2233727 = 3350591) B3350591
theorem B2233759 : Blo 1393516 2233759 := bstep (se 1 (by rfl) ⟨1675319, by rfl⟩ : syracuseStep 2233759 = 3350639) B3350639
theorem B4027931 : Blo 1393516 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B3528299 : Blo 1393516 3528299 := bstep (se 1 (by rfl) ⟨2646224, by rfl⟩ : syracuseStep 3528299 = 5292449) B5292449
theorem B33929117 : Blo 1393516 33929117 := bstep (se 3 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 33929117 = 12723419) B12723419
theorem B12720239 : Blo 1393516 12720239 := bstep (se 1 (by rfl) ⟨9540179, by rfl⟩ : syracuseStep 12720239 = 19080359) B19080359
theorem B5028047 : Blo 1393516 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B5298479 : Blo 1393516 5298479 := bstep (se 1 (by rfl) ⟨3973859, by rfl⟩ : syracuseStep 5298479 = 7947719) B7947719
theorem B42949025 : Blo 1393516 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B4708799 : Blo 1393516 4708799 := bstep (se 1 (by rfl) ⟨3531599, by rfl⟩ : syracuseStep 4708799 = 7063199) B7063199
theorem B3136031 : Blo 1393516 3136031 := bstep (se 1 (by rfl) ⟨2352023, by rfl⟩ : syracuseStep 3136031 = 4704047) B4704047
theorem B3529271 : Blo 1393516 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B3136103 : Blo 1393516 3136103 := bstep (se 1 (by rfl) ⟨2352077, by rfl⟩ : syracuseStep 3136103 = 4704155) B4704155
theorem B15874703 : Blo 1393516 15874703 := bstep (se 1 (by rfl) ⟨11906027, by rfl⟩ : syracuseStep 15874703 = 23812055) B23812055
theorem B43113485 : Blo 1393516 43113485 := bstep (se 3 (by rfl) ⟨8083778, by rfl⟩ : syracuseStep 43113485 = 16167557) B16167557
theorem B3136751 : Blo 1393516 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B85859615 : Blo 1393516 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B8936801 : Blo 1393516 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B26803871 : Blo 1393516 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B2645959 : Blo 1393516 2645959 := bstep (se 1 (by rfl) ⟨1984469, by rfl⟩ : syracuseStep 2645959 = 3968939) B3968939
theorem B68952539 : Blo 1393516 68952539 := bstep (se 1 (by rfl) ⟨51714404, by rfl⟩ : syracuseStep 68952539 = 103428809) B103428809
theorem B3138047 : Blo 1393516 3138047 := bstep (se 1 (by rfl) ⟨2353535, by rfl⟩ : syracuseStep 3138047 = 4707071) B4707071
theorem B10592855 : Blo 1393516 10592855 := bstep (se 1 (by rfl) ⟨7944641, by rfl⟩ : syracuseStep 10592855 = 15889283) B15889283
theorem B3138407 : Blo 1393516 3138407 := bstep (se 1 (by rfl) ⟨2353805, by rfl⟩ : syracuseStep 3138407 = 4707611) B4707611
theorem B1393631 : Blo 1393516 1393631 := bstep (se 1 (by rfl) ⟨1045223, by rfl⟩ : syracuseStep 1393631 = 2090447) B2090447
theorem B2352199 : Blo 1393516 2352199 := bstep (se 1 (by rfl) ⟨1764149, by rfl⟩ : syracuseStep 2352199 = 3528299) B3528299
theorem B22619411 : Blo 1393516 22619411 := bstep (se 1 (by rfl) ⟨16964558, by rfl⟩ : syracuseStep 22619411 = 33929117) B33929117
theorem B1393947 : Blo 1393516 1393947 := bstep (se 1 (by rfl) ⟨1045460, by rfl⟩ : syracuseStep 1393947 = 2090921) B2090921
theorem B8480159 : Blo 1393516 8480159 := bstep (se 1 (by rfl) ⟨6360119, by rfl⟩ : syracuseStep 8480159 = 12720239) B12720239
theorem B1394143 : Blo 1393516 1394143 := bstep (se 1 (by rfl) ⟨1045607, by rfl⟩ : syracuseStep 1394143 = 2091215) B2091215
theorem B3352031 : Blo 1393516 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B3532319 : Blo 1393516 3532319 := bstep (se 1 (by rfl) ⟨2649239, by rfl⟩ : syracuseStep 3532319 = 5298479) B5298479
theorem B28632683 : Blo 1393516 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B3139199 : Blo 1393516 3139199 := bstep (se 1 (by rfl) ⟨2354399, by rfl⟩ : syracuseStep 3139199 = 4708799) B4708799
theorem B2090687 : Blo 1393516 2090687 := bstep (se 1 (by rfl) ⟨1568015, by rfl⟩ : syracuseStep 2090687 = 3136031) B3136031
theorem B2352847 : Blo 1393516 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B1394407 : Blo 1393516 1394407 := bstep (se 1 (by rfl) ⟨1045805, by rfl⟩ : syracuseStep 1394407 = 2091611) B2091611
theorem B2090735 : Blo 1393516 2090735 := bstep (se 1 (by rfl) ⟨1568051, by rfl⟩ : syracuseStep 2090735 = 3136103) B3136103
theorem B1394559 : Blo 1393516 1394559 := bstep (se 1 (by rfl) ⟨1045919, by rfl⟩ : syracuseStep 1394559 = 2091839) B2091839
theorem B10586051 : Blo 1393516 10586051 := bstep (se 1 (by rfl) ⟨7939538, by rfl⟩ : syracuseStep 10586051 = 15879077) B15879077
theorem B2091167 : Blo 1393516 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B57239743 : Blo 1393516 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B5957867 : Blo 1393516 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B1394939 : Blo 1393516 1394939 := bstep (se 1 (by rfl) ⟨1046204, by rfl⟩ : syracuseStep 1394939 = 2092409) B2092409
theorem B17869247 : Blo 1393516 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B1395135 : Blo 1393516 1395135 := bstep (se 1 (by rfl) ⟨1046351, by rfl⟩ : syracuseStep 1395135 = 2092703) B2092703
theorem B114969293 : Blo 1393516 114969293 := bstep (se 3 (by rfl) ⟨21556742, by rfl⟩ : syracuseStep 114969293 = 43113485) B43113485
theorem B2091815 : Blo 1393516 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B8932187 : Blo 1393516 8932187 := bstep (se 1 (by rfl) ⟨6699140, by rfl⟩ : syracuseStep 8932187 = 13398281) B13398281
theorem B7154561 : Blo 1393516 7154561 := bstep (se 2 (by rfl) ⟨2682960, by rfl⟩ : syracuseStep 7154561 = 5365921) B5365921
theorem B4705181 : Blo 1393516 4705181 := bstep (se 3 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 4705181 = 1764443) B1764443
theorem B2649179 : Blo 1393516 2649179 := bstep (se 1 (by rfl) ⟨1986884, by rfl⟩ : syracuseStep 2649179 = 3973769) B3973769
theorem B1568047 : Blo 1393516 1568047 := bstep (se 1 (by rfl) ⟨1176035, by rfl⟩ : syracuseStep 1568047 = 2352071) B2352071
theorem B2092523 : Blo 1393516 2092523 := bstep (se 1 (by rfl) ⟨1569392, by rfl⟩ : syracuseStep 2092523 = 3138785) B3138785
theorem B15068875 : Blo 1393516 15068875 := bstep (se 1 (by rfl) ⟨11301656, by rfl⟩ : syracuseStep 15068875 = 22603313) B22603313
theorem B6041375 : Blo 1393516 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B1568623 : Blo 1393516 1568623 := bstep (se 1 (by rfl) ⟨1176467, by rfl⟩ : syracuseStep 1568623 = 2352935) B2352935
theorem B2978345 : Blo 1393516 2978345 := bstep (se 2 (by rfl) ⟨1116879, by rfl⟩ : syracuseStep 2978345 = 2233759) B2233759
theorem B1569487 : Blo 1393516 1569487 := bstep (se 1 (by rfl) ⟨1177115, by rfl⟩ : syracuseStep 1569487 = 2354231) B2354231
theorem B3527945 : Blo 1393516 3527945 := bstep (se 2 (by rfl) ⟨1322979, by rfl⟩ : syracuseStep 3527945 = 2645959) B2645959
theorem B5953151 : Blo 1393516 5953151 := bstep (se 1 (by rfl) ⟨4464863, by rfl⟩ : syracuseStep 5953151 = 8929727) B8929727
theorem B3528319 : Blo 1393516 3528319 := bstep (se 1 (by rfl) ⟨2646239, by rfl⟩ : syracuseStep 3528319 = 5292479) B5292479
theorem B9541547 : Blo 1393516 9541547 := bstep (se 1 (by rfl) ⟨7156160, by rfl⟩ : syracuseStep 9541547 = 14312321) B14312321
theorem B7157807 : Blo 1393516 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B3135599 : Blo 1393516 3135599 := bstep (se 1 (by rfl) ⟨2351699, by rfl⟩ : syracuseStep 3135599 = 4703399) B4703399
theorem B1489151 : Blo 1393516 1489151 := bstep (se 1 (by rfl) ⟨1116863, by rfl⟩ : syracuseStep 1489151 = 2233727) B2233727
theorem B2685287 : Blo 1393516 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B6699601 : Blo 1393516 6699601 := bstep (se 2 (by rfl) ⟨2512350, by rfl⟩ : syracuseStep 6699601 = 5024701) B5024701
theorem B10583135 : Blo 1393516 10583135 := bstep (se 1 (by rfl) ⟨7937351, by rfl⟩ : syracuseStep 10583135 = 15874703) B15874703
theorem B16309349 : Blo 1393516 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B3137363 : Blo 1393516 3137363 := bstep (se 1 (by rfl) ⟨2353022, by rfl⟩ : syracuseStep 3137363 = 4706045) B4706045
theorem B7061903 : Blo 1393516 7061903 := bstep (se 1 (by rfl) ⟨5296427, by rfl⟩ : syracuseStep 7061903 = 10592855) B10592855
theorem B2351963 : Blo 1393516 2351963 := bstep (se 1 (by rfl) ⟨1763972, by rfl⟩ : syracuseStep 2351963 = 3527945) B3527945
theorem B5653439 : Blo 1393516 5653439 := bstep (se 1 (by rfl) ⟨4240079, by rfl⟩ : syracuseStep 5653439 = 8480159) B8480159
theorem B19088455 : Blo 1393516 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B1393791 : Blo 1393516 1393791 := bstep (se 1 (by rfl) ⟨1045343, by rfl⟩ : syracuseStep 1393791 = 2090687) B2090687
theorem B1393823 : Blo 1393516 1393823 := bstep (se 1 (by rfl) ⟨1045367, by rfl⟩ : syracuseStep 1393823 = 2090735) B2090735
theorem B2090399 : Blo 1393516 2090399 := bstep (se 1 (by rfl) ⟨1567799, by rfl⟩ : syracuseStep 2090399 = 3135599) B3135599
theorem B1394111 : Blo 1393516 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B11912831 : Blo 1393516 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B2090729 : Blo 1393516 2090729 := bstep (se 2 (by rfl) ⟨784023, by rfl⟩ : syracuseStep 2090729 = 1568047) B1568047
theorem B76646195 : Blo 1393516 76646195 := bstep (se 1 (by rfl) ⟨57484646, by rfl⟩ : syracuseStep 76646195 = 114969293) B114969293
theorem B1394543 : Blo 1393516 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B4769707 : Blo 1393516 4769707 := bstep (se 1 (by rfl) ⟨3577280, by rfl⟩ : syracuseStep 4769707 = 7154561) B7154561
theorem B7055423 : Blo 1393516 7055423 := bstep (se 1 (by rfl) ⟨5291567, by rfl⟩ : syracuseStep 7055423 = 10583135) B10583135
theorem B10872899 : Blo 1393516 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B4704425 : Blo 1393516 4704425 := bstep (se 2 (by rfl) ⟨1764159, by rfl⟩ : syracuseStep 4704425 = 3528319) B3528319
theorem B1395015 : Blo 1393516 1395015 := bstep (se 1 (by rfl) ⟨1046261, by rfl⟩ : syracuseStep 1395015 = 2092523) B2092523
theorem B2091497 : Blo 1393516 2091497 := bstep (se 2 (by rfl) ⟨784311, by rfl⟩ : syracuseStep 2091497 = 1568623) B1568623
theorem B2091575 : Blo 1393516 2091575 := bstep (se 1 (by rfl) ⟨1568681, by rfl⟩ : syracuseStep 2091575 = 3137363) B3137363
theorem B76319657 : Blo 1393516 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B45968359 : Blo 1393516 45968359 := bstep (se 1 (by rfl) ⟨34476269, by rfl⟩ : syracuseStep 45968359 = 68952539) B68952539
theorem B2092031 : Blo 1393516 2092031 := bstep (se 1 (by rfl) ⟨1569023, by rfl⟩ : syracuseStep 2092031 = 3138047) B3138047
theorem B1985563 : Blo 1393516 1985563 := bstep (se 1 (by rfl) ⟨1489172, by rfl⟩ : syracuseStep 1985563 = 2978345) B2978345
theorem B2092271 : Blo 1393516 2092271 := bstep (se 1 (by rfl) ⟨1569203, by rfl⟩ : syracuseStep 2092271 = 3138407) B3138407
theorem B2092649 : Blo 1393516 2092649 := bstep (se 2 (by rfl) ⟨784743, by rfl⟩ : syracuseStep 2092649 = 1569487) B1569487
theorem B2354879 : Blo 1393516 2354879 := bstep (se 1 (by rfl) ⟨1766159, by rfl⟩ : syracuseStep 2354879 = 3532319) B3532319
theorem B3968767 : Blo 1393516 3968767 := bstep (se 1 (by rfl) ⟨2976575, by rfl⟩ : syracuseStep 3968767 = 5953151) B5953151
theorem B2092799 : Blo 1393516 2092799 := bstep (se 1 (by rfl) ⟨1569599, by rfl⟩ : syracuseStep 2092799 = 3139199) B3139199
theorem B6361031 : Blo 1393516 6361031 := bstep (se 1 (by rfl) ⟨4770773, by rfl⟩ : syracuseStep 6361031 = 9541547) B9541547
theorem B7057367 : Blo 1393516 7057367 := bstep (se 1 (by rfl) ⟨5293025, by rfl⟩ : syracuseStep 7057367 = 10586051) B10586051
theorem B4771871 : Blo 1393516 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B1790191 : Blo 1393516 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B1766119 : Blo 1393516 1766119 := bstep (se 1 (by rfl) ⟨1324589, by rfl⟩ : syracuseStep 1766119 = 2649179) B2649179
theorem B20091833 : Blo 1393516 20091833 := bstep (se 2 (by rfl) ⟨7534437, by rfl⟩ : syracuseStep 20091833 = 15068875) B15068875
theorem B4027583 : Blo 1393516 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B35731205 : Blo 1393516 35731205 := bstep (se 4 (by rfl) ⟨3349800, by rfl⟩ : syracuseStep 35731205 = 6699601) B6699601
theorem B3971069 : Blo 1393516 3971069 := bstep (se 3 (by rfl) ⟨744575, by rfl⟩ : syracuseStep 3971069 = 1489151) B1489151
theorem B15079607 : Blo 1393516 15079607 := bstep (se 1 (by rfl) ⟨11309705, by rfl⟩ : syracuseStep 15079607 = 22619411) B22619411
theorem B2234687 : Blo 1393516 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B3136265 : Blo 1393516 3136265 := bstep (se 2 (by rfl) ⟨1176099, by rfl⟩ : syracuseStep 3136265 = 2352199) B2352199
theorem B3971911 : Blo 1393516 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B5954791 : Blo 1393516 5954791 := bstep (se 1 (by rfl) ⟨4466093, by rfl⟩ : syracuseStep 5954791 = 8932187) B8932187
theorem B3136787 : Blo 1393516 3136787 := bstep (se 1 (by rfl) ⟨2352590, by rfl⟩ : syracuseStep 3136787 = 4705181) B4705181
theorem B3137129 : Blo 1393516 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B10740221 : Blo 1393516 10740221 := bstep (se 3 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 10740221 = 4027583) B4027583
theorem B13394555 : Blo 1393516 13394555 := bstep (se 1 (by rfl) ⟨10045916, by rfl⟩ : syracuseStep 13394555 = 20091833) B20091833
theorem B3768959 : Blo 1393516 3768959 := bstep (se 1 (by rfl) ⟨2826719, by rfl⟩ : syracuseStep 3768959 = 5653439) B5653439
theorem B1393599 : Blo 1393516 1393599 := bstep (se 1 (by rfl) ⟨1045199, by rfl⟩ : syracuseStep 1393599 = 2090399) B2090399
theorem B1393819 : Blo 1393516 1393819 := bstep (se 1 (by rfl) ⟨1045364, by rfl⟩ : syracuseStep 1393819 = 2090729) B2090729
theorem B2647379 : Blo 1393516 2647379 := bstep (se 1 (by rfl) ⟨1985534, by rfl⟩ : syracuseStep 2647379 = 3971069) B3971069
theorem B2647417 : Blo 1393516 2647417 := bstep (se 2 (by rfl) ⟨992781, by rfl⟩ : syracuseStep 2647417 = 1985563) B1985563
theorem B4703615 : Blo 1393516 4703615 := bstep (se 1 (by rfl) ⟨3527711, by rfl⟩ : syracuseStep 4703615 = 7055423) B7055423
theorem B10053071 : Blo 1393516 10053071 := bstep (se 1 (by rfl) ⟨7539803, by rfl⟩ : syracuseStep 10053071 = 15079607) B15079607
theorem B7939721 : Blo 1393516 7939721 := bstep (se 2 (by rfl) ⟨2977395, by rfl⟩ : syracuseStep 7939721 = 5954791) B5954791
theorem B1394331 : Blo 1393516 1394331 := bstep (se 1 (by rfl) ⟨1045748, by rfl⟩ : syracuseStep 1394331 = 2091497) B2091497
theorem B1394383 : Blo 1393516 1394383 := bstep (se 1 (by rfl) ⟨1045787, by rfl⟩ : syracuseStep 1394383 = 2091575) B2091575
theorem B2090843 : Blo 1393516 2090843 := bstep (se 1 (by rfl) ⟨1568132, by rfl⟩ : syracuseStep 2090843 = 3136265) B3136265
theorem B1394687 : Blo 1393516 1394687 := bstep (se 1 (by rfl) ⟨1046015, by rfl⟩ : syracuseStep 1394687 = 2092031) B2092031
theorem B1394847 : Blo 1393516 1394847 := bstep (se 1 (by rfl) ⟨1046135, by rfl⟩ : syracuseStep 1394847 = 2092271) B2092271
theorem B2091191 : Blo 1393516 2091191 := bstep (se 1 (by rfl) ⟨1568393, by rfl⟩ : syracuseStep 2091191 = 3136787) B3136787
theorem B2091419 : Blo 1393516 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B1395099 : Blo 1393516 1395099 := bstep (se 1 (by rfl) ⟨1046324, by rfl⟩ : syracuseStep 1395099 = 2092649) B2092649
theorem B1395199 : Blo 1393516 1395199 := bstep (se 1 (by rfl) ⟨1046399, by rfl⟩ : syracuseStep 1395199 = 2092799) B2092799
theorem B6359609 : Blo 1393516 6359609 := bstep (se 2 (by rfl) ⟨2384853, by rfl⟩ : syracuseStep 6359609 = 4769707) B4769707
theorem B4704911 : Blo 1393516 4704911 := bstep (se 1 (by rfl) ⟨3528683, by rfl⟩ : syracuseStep 4704911 = 7057367) B7057367
theorem B3181247 : Blo 1393516 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B2386921 : Blo 1393516 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B1567975 : Blo 1393516 1567975 := bstep (se 1 (by rfl) ⟨1175981, by rfl⟩ : syracuseStep 1567975 = 2351963) B2351963
theorem B5959165 : Blo 1393516 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B2354825 : Blo 1393516 2354825 := bstep (se 2 (by rfl) ⟨883059, by rfl⟩ : syracuseStep 2354825 = 1766119) B1766119
theorem B7941887 : Blo 1393516 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B5295881 : Blo 1393516 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B51097463 : Blo 1393516 51097463 := bstep (se 1 (by rfl) ⟨38323097, by rfl⟩ : syracuseStep 51097463 = 76646195) B76646195
theorem B1569919 : Blo 1393516 1569919 := bstep (se 1 (by rfl) ⟨1177439, by rfl⟩ : syracuseStep 1569919 = 2354879) B2354879
theorem B16962749 : Blo 1393516 16962749 := bstep (se 3 (by rfl) ⟨3180515, by rfl⟩ : syracuseStep 16962749 = 6361031) B6361031
theorem B4707935 : Blo 1393516 4707935 := bstep (se 1 (by rfl) ⟨3530951, by rfl⟩ : syracuseStep 4707935 = 7061903) B7061903
theorem B23820803 : Blo 1393516 23820803 := bstep (se 1 (by rfl) ⟨17865602, by rfl⟩ : syracuseStep 23820803 = 35731205) B35731205
theorem B61291145 : Blo 1393516 61291145 := bstep (se 2 (by rfl) ⟨22984179, by rfl⟩ : syracuseStep 61291145 = 45968359) B45968359
theorem B7248599 : Blo 1393516 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B25451273 : Blo 1393516 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B3136283 : Blo 1393516 3136283 := bstep (se 1 (by rfl) ⟨2352212, by rfl⟩ : syracuseStep 3136283 = 4704425) B4704425
theorem B50879771 : Blo 1393516 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B5291689 : Blo 1393516 5291689 := bstep (se 2 (by rfl) ⟨1984383, by rfl⟩ : syracuseStep 5291689 = 3968767) B3968767
theorem B7160147 : Blo 1393516 7160147 := bstep (se 1 (by rfl) ⟨5370110, by rfl⟩ : syracuseStep 7160147 = 10740221) B10740221
theorem B8929703 : Blo 1393516 8929703 := bstep (se 1 (by rfl) ⟨6697277, by rfl⟩ : syracuseStep 8929703 = 13394555) B13394555
theorem B6702047 : Blo 1393516 6702047 := bstep (se 1 (by rfl) ⟨5026535, by rfl⟩ : syracuseStep 6702047 = 10053071) B10053071
theorem B3138623 : Blo 1393516 3138623 := bstep (se 1 (by rfl) ⟨2353967, by rfl⟩ : syracuseStep 3138623 = 4707935) B4707935
theorem B5293147 : Blo 1393516 5293147 := bstep (se 1 (by rfl) ⟨3969860, by rfl⟩ : syracuseStep 5293147 = 7939721) B7939721
theorem B1393895 : Blo 1393516 1393895 := bstep (se 1 (by rfl) ⟨1045421, by rfl⟩ : syracuseStep 1393895 = 2090843) B2090843
theorem B1394127 : Blo 1393516 1394127 := bstep (se 1 (by rfl) ⟨1045595, by rfl⟩ : syracuseStep 1394127 = 2091191) B2091191
theorem B1394279 : Blo 1393516 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B2090633 : Blo 1393516 2090633 := bstep (se 2 (by rfl) ⟨783987, by rfl⟩ : syracuseStep 2090633 = 1567975) B1567975
theorem B2090855 : Blo 1393516 2090855 := bstep (se 1 (by rfl) ⟨1568141, by rfl⟩ : syracuseStep 2090855 = 3136283) B3136283
theorem B7055585 : Blo 1393516 7055585 := bstep (se 2 (by rfl) ⟨2645844, by rfl⟩ : syracuseStep 7055585 = 5291689) B5291689
theorem B5294591 : Blo 1393516 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B34064975 : Blo 1393516 34064975 := bstep (se 1 (by rfl) ⟨25548731, by rfl⟩ : syracuseStep 34064975 = 51097463) B51097463
theorem B11308499 : Blo 1393516 11308499 := bstep (se 1 (by rfl) ⟨8481374, by rfl⟩ : syracuseStep 11308499 = 16962749) B16962749
theorem B1764919 : Blo 1393516 1764919 := bstep (se 1 (by rfl) ⟨1323689, by rfl⟩ : syracuseStep 1764919 = 2647379) B2647379
theorem B3182561 : Blo 1393516 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B2093225 : Blo 1393516 2093225 := bstep (se 2 (by rfl) ⟨784959, by rfl⟩ : syracuseStep 2093225 = 1569919) B1569919
theorem B15880535 : Blo 1393516 15880535 := bstep (se 1 (by rfl) ⟨11910401, by rfl⟩ : syracuseStep 15880535 = 23820803) B23820803
theorem B4239739 : Blo 1393516 4239739 := bstep (se 1 (by rfl) ⟨3179804, by rfl⟩ : syracuseStep 4239739 = 6359609) B6359609
theorem B33919847 : Blo 1393516 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B1569883 : Blo 1393516 1569883 := bstep (se 1 (by rfl) ⟨1177412, by rfl⟩ : syracuseStep 1569883 = 2354825) B2354825
theorem B2512639 : Blo 1393516 2512639 := bstep (se 1 (by rfl) ⟨1884479, by rfl⟩ : syracuseStep 2512639 = 3768959) B3768959
theorem B3135743 : Blo 1393516 3135743 := bstep (se 1 (by rfl) ⟨2351807, by rfl⟩ : syracuseStep 3135743 = 4703615) B4703615
theorem B40860763 : Blo 1393516 40860763 := bstep (se 1 (by rfl) ⟨30645572, by rfl⟩ : syracuseStep 40860763 = 61291145) B61291145
theorem B3136607 : Blo 1393516 3136607 := bstep (se 1 (by rfl) ⟨2352455, by rfl⟩ : syracuseStep 3136607 = 4704911) B4704911
theorem B2120831 : Blo 1393516 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B4832399 : Blo 1393516 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B3529889 : Blo 1393516 3529889 := bstep (se 2 (by rfl) ⟨1323708, by rfl⟩ : syracuseStep 3529889 = 2647417) B2647417
theorem B7945553 : Blo 1393516 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B67870061 : Blo 1393516 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B3530587 : Blo 1393516 3530587 := bstep (se 1 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 3530587 = 5295881) B5295881
theorem B12886397 : Blo 1393516 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B217924069 : Blo 1393516 217924069 := bstep (se 4 (by rfl) ⟨20430381, by rfl⟩ : syracuseStep 217924069 = 40860763) B40860763
theorem B5652985 : Blo 1393516 5652985 := bstep (se 2 (by rfl) ⟨2119869, by rfl⟩ : syracuseStep 5652985 = 4239739) B4239739
theorem B1393755 : Blo 1393516 1393755 := bstep (se 1 (by rfl) ⟨1045316, by rfl⟩ : syracuseStep 1393755 = 2090633) B2090633
theorem B1393903 : Blo 1393516 1393903 := bstep (se 1 (by rfl) ⟨1045427, by rfl⟩ : syracuseStep 1393903 = 2090855) B2090855
theorem B4703723 : Blo 1393516 4703723 := bstep (se 1 (by rfl) ⟨3527792, by rfl⟩ : syracuseStep 4703723 = 7055585) B7055585
theorem B2090495 : Blo 1393516 2090495 := bstep (se 1 (by rfl) ⟨1567871, by rfl⟩ : syracuseStep 2090495 = 3135743) B3135743
theorem B22709983 : Blo 1393516 22709983 := bstep (se 1 (by rfl) ⟨17032487, by rfl⟩ : syracuseStep 22709983 = 34064975) B34064975
theorem B2091071 : Blo 1393516 2091071 := bstep (se 1 (by rfl) ⟨1568303, by rfl⟩ : syracuseStep 2091071 = 3136607) B3136607
theorem B2353225 : Blo 1393516 2353225 := bstep (se 2 (by rfl) ⟨882459, by rfl⟩ : syracuseStep 2353225 = 1764919) B1764919
theorem B2353259 : Blo 1393516 2353259 := bstep (se 1 (by rfl) ⟨1764944, by rfl⟩ : syracuseStep 2353259 = 3529889) B3529889
theorem B45246707 : Blo 1393516 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B7538999 : Blo 1393516 7538999 := bstep (se 1 (by rfl) ⟨5654249, by rfl⟩ : syracuseStep 7538999 = 11308499) B11308499
theorem B1395483 : Blo 1393516 1395483 := bstep (se 1 (by rfl) ⟨1046612, by rfl⟩ : syracuseStep 1395483 = 2093225) B2093225
theorem B10587023 : Blo 1393516 10587023 := bstep (se 1 (by rfl) ⟨7940267, by rfl⟩ : syracuseStep 10587023 = 15880535) B15880535
theorem B22613231 : Blo 1393516 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B4468031 : Blo 1393516 4468031 := bstep (se 1 (by rfl) ⟨3351023, by rfl⟩ : syracuseStep 4468031 = 6702047) B6702047
theorem B2092415 : Blo 1393516 2092415 := bstep (se 1 (by rfl) ⟨1569311, by rfl⟩ : syracuseStep 2092415 = 3138623) B3138623
theorem B7057529 : Blo 1393516 7057529 := bstep (se 2 (by rfl) ⟨2646573, by rfl⟩ : syracuseStep 7057529 = 5293147) B5293147
theorem B2093177 : Blo 1393516 2093177 := bstep (se 2 (by rfl) ⟨784941, by rfl⟩ : syracuseStep 2093177 = 1569883) B1569883
theorem B1413887 : Blo 1393516 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B5297035 : Blo 1393516 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B4707449 : Blo 1393516 4707449 := bstep (se 2 (by rfl) ⟨1765293, by rfl⟩ : syracuseStep 4707449 = 3530587) B3530587
theorem B4773431 : Blo 1393516 4773431 := bstep (se 1 (by rfl) ⟨3580073, by rfl⟩ : syracuseStep 4773431 = 7160147) B7160147
theorem B5953135 : Blo 1393516 5953135 := bstep (se 1 (by rfl) ⟨4464851, by rfl⟩ : syracuseStep 5953135 = 8929703) B8929703
theorem B13400741 : Blo 1393516 13400741 := bstep (se 4 (by rfl) ⟨1256319, by rfl⟩ : syracuseStep 13400741 = 2512639) B2512639
theorem B3529727 : Blo 1393516 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B2121707 : Blo 1393516 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B3137633 : Blo 1393516 3137633 := bstep (se 2 (by rfl) ⟨1176612, by rfl⟩ : syracuseStep 3137633 = 2353225) B2353225
theorem B7537313 : Blo 1393516 7537313 := bstep (se 2 (by rfl) ⟨2826492, by rfl⟩ : syracuseStep 7537313 = 5652985) B5652985
theorem B3138299 : Blo 1393516 3138299 := bstep (se 1 (by rfl) ⟨2353724, by rfl⟩ : syracuseStep 3138299 = 4707449) B4707449
theorem B20103997 : Blo 1393516 20103997 := bstep (se 3 (by rfl) ⟨3769499, by rfl⟩ : syracuseStep 20103997 = 7538999) B7538999
theorem B1393663 : Blo 1393516 1393663 := bstep (se 1 (by rfl) ⟨1045247, by rfl⟩ : syracuseStep 1393663 = 2090495) B2090495
theorem B7062713 : Blo 1393516 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B1394047 : Blo 1393516 1394047 := bstep (se 1 (by rfl) ⟨1045535, by rfl⟩ : syracuseStep 1394047 = 2091071) B2091071
theorem B30164471 : Blo 1393516 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B2353151 : Blo 1393516 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B15075487 : Blo 1393516 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B1394943 : Blo 1393516 1394943 := bstep (se 1 (by rfl) ⟨1046207, by rfl⟩ : syracuseStep 1394943 = 2092415) B2092415
theorem B30279977 : Blo 1393516 30279977 := bstep (se 2 (by rfl) ⟨11354991, by rfl⟩ : syracuseStep 30279977 = 22709983) B22709983
theorem B4705019 : Blo 1393516 4705019 := bstep (se 1 (by rfl) ⟨3528764, by rfl⟩ : syracuseStep 4705019 = 7057529) B7057529
theorem B1395451 : Blo 1393516 1395451 := bstep (se 1 (by rfl) ⟨1046588, by rfl⟩ : syracuseStep 1395451 = 2093177) B2093177
theorem B290565425 : Blo 1393516 290565425 := bstep (se 2 (by rfl) ⟨108962034, by rfl⟩ : syracuseStep 290565425 = 217924069) B217924069
theorem B3182287 : Blo 1393516 3182287 := bstep (se 1 (by rfl) ⟨2386715, by rfl⟩ : syracuseStep 3182287 = 4773431) B4773431
theorem B1568839 : Blo 1393516 1568839 := bstep (se 1 (by rfl) ⟨1176629, by rfl⟩ : syracuseStep 1568839 = 2353259) B2353259
theorem B8933827 : Blo 1393516 8933827 := bstep (se 1 (by rfl) ⟨6700370, by rfl⟩ : syracuseStep 8933827 = 13400741) B13400741
theorem B7058015 : Blo 1393516 7058015 := bstep (se 1 (by rfl) ⟨5293511, by rfl⟩ : syracuseStep 7058015 = 10587023) B10587023
theorem B2978687 : Blo 1393516 2978687 := bstep (se 1 (by rfl) ⟨2234015, by rfl⟩ : syracuseStep 2978687 = 4468031) B4468031
theorem B1414471 : Blo 1393516 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B8590931 : Blo 1393516 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B3135815 : Blo 1393516 3135815 := bstep (se 1 (by rfl) ⟨2351861, by rfl⟩ : syracuseStep 3135815 = 4703723) B4703723
theorem B7937513 : Blo 1393516 7937513 := bstep (se 2 (by rfl) ⟨2976567, by rfl⟩ : syracuseStep 7937513 = 5953135) B5953135
theorem B15081461 : Blo 1393516 15081461 := bstep (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) B1413887
theorem B11911769 : Blo 1393516 11911769 := bstep (se 2 (by rfl) ⟨4466913, by rfl⟩ : syracuseStep 11911769 = 8933827) B8933827
theorem B774841133 : Blo 1393516 774841133 := bstep (se 3 (by rfl) ⟨145282712, by rfl⟩ : syracuseStep 774841133 = 290565425) B290565425
theorem B5727287 : Blo 1393516 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B26805329 : Blo 1393516 26805329 := bstep (se 2 (by rfl) ⟨10051998, by rfl⟩ : syracuseStep 26805329 = 20103997) B20103997
theorem B20186651 : Blo 1393516 20186651 := bstep (se 1 (by rfl) ⟨15139988, by rfl⟩ : syracuseStep 20186651 = 30279977) B30279977
theorem B2090543 : Blo 1393516 2090543 := bstep (se 1 (by rfl) ⟨1567907, by rfl⟩ : syracuseStep 2090543 = 3135815) B3135815
theorem B1885961 : Blo 1393516 1885961 := bstep (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) B1414471
theorem B10054307 : Blo 1393516 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B2091755 : Blo 1393516 2091755 := bstep (se 1 (by rfl) ⟨1568816, by rfl⟩ : syracuseStep 2091755 = 3137633) B3137633
theorem B2091785 : Blo 1393516 2091785 := bstep (se 2 (by rfl) ⟨784419, by rfl⟩ : syracuseStep 2091785 = 1568839) B1568839
theorem B4705343 : Blo 1393516 4705343 := bstep (se 1 (by rfl) ⟨3529007, by rfl⟩ : syracuseStep 4705343 = 7058015) B7058015
theorem B2092199 : Blo 1393516 2092199 := bstep (se 1 (by rfl) ⟨1569149, by rfl⟩ : syracuseStep 2092199 = 3138299) B3138299
theorem B1985791 : Blo 1393516 1985791 := bstep (se 1 (by rfl) ⟨1489343, by rfl⟩ : syracuseStep 1985791 = 2978687) B2978687
theorem B1568767 : Blo 1393516 1568767 := bstep (se 1 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 1568767 = 2353151) B2353151
theorem B20099501 : Blo 1393516 20099501 := bstep (se 3 (by rfl) ⟨3768656, by rfl⟩ : syracuseStep 20099501 = 7537313) B7537313
theorem B20100649 : Blo 1393516 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B4708475 : Blo 1393516 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B20109647 : Blo 1393516 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B3136679 : Blo 1393516 3136679 := bstep (se 1 (by rfl) ⟨2352509, by rfl⟩ : syracuseStep 3136679 = 4705019) B4705019
theorem B4243049 : Blo 1393516 4243049 := bstep (se 2 (by rfl) ⟨1591143, by rfl⟩ : syracuseStep 4243049 = 3182287) B3182287
theorem B5291675 : Blo 1393516 5291675 := bstep (se 1 (by rfl) ⟨3968756, by rfl⟩ : syracuseStep 5291675 = 7937513) B7937513
theorem B3818191 : Blo 1393516 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B1393695 : Blo 1393516 1393695 := bstep (se 1 (by rfl) ⟨1045271, by rfl⟩ : syracuseStep 1393695 = 2090543) B2090543
theorem B3138983 : Blo 1393516 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B2647721 : Blo 1393516 2647721 := bstep (se 2 (by rfl) ⟨992895, by rfl⟩ : syracuseStep 2647721 = 1985791) B1985791
theorem B6702871 : Blo 1393516 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B1394503 : Blo 1393516 1394503 := bstep (se 1 (by rfl) ⟨1045877, by rfl⟩ : syracuseStep 1394503 = 2091755) B2091755
theorem B1394523 : Blo 1393516 1394523 := bstep (se 1 (by rfl) ⟨1045892, by rfl⟩ : syracuseStep 1394523 = 2091785) B2091785
theorem B2091119 : Blo 1393516 2091119 := bstep (se 1 (by rfl) ⟨1568339, by rfl⟩ : syracuseStep 2091119 = 3136679) B3136679
theorem B1394799 : Blo 1393516 1394799 := bstep (se 1 (by rfl) ⟨1046099, by rfl⟩ : syracuseStep 1394799 = 2092199) B2092199
theorem B2828699 : Blo 1393516 2828699 := bstep (se 1 (by rfl) ⟨2121524, by rfl⟩ : syracuseStep 2828699 = 4243049) B4243049
theorem B2091689 : Blo 1393516 2091689 := bstep (se 2 (by rfl) ⟨784383, by rfl⟩ : syracuseStep 2091689 = 1568767) B1568767
theorem B7941179 : Blo 1393516 7941179 := bstep (se 1 (by rfl) ⟨5955884, by rfl⟩ : syracuseStep 7941179 = 11911769) B11911769
theorem B17870219 : Blo 1393516 17870219 := bstep (se 1 (by rfl) ⟨13402664, by rfl⟩ : syracuseStep 17870219 = 26805329) B26805329
theorem B13406431 : Blo 1393516 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B26800865 : Blo 1393516 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B3527783 : Blo 1393516 3527783 := bstep (se 1 (by rfl) ⟨2645837, by rfl⟩ : syracuseStep 3527783 = 5291675) B5291675
theorem B13399667 : Blo 1393516 13399667 := bstep (se 1 (by rfl) ⟨10049750, by rfl⟩ : syracuseStep 13399667 = 20099501) B20099501
theorem B516560755 : Blo 1393516 516560755 := bstep (se 1 (by rfl) ⟨387420566, by rfl⟩ : syracuseStep 516560755 = 774841133) B774841133
theorem B13457767 : Blo 1393516 13457767 := bstep (se 1 (by rfl) ⟨10093325, by rfl⟩ : syracuseStep 13457767 = 20186651) B20186651
theorem B5029229 : Blo 1393516 5029229 := bstep (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) B1885961
theorem B3136895 : Blo 1393516 3136895 := bstep (se 1 (by rfl) ⟨2352671, by rfl⟩ : syracuseStep 3136895 = 4705343) B4705343
theorem B17875241 : Blo 1393516 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B17867243 : Blo 1393516 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B2351855 : Blo 1393516 2351855 := bstep (se 1 (by rfl) ⟨1763891, by rfl⟩ : syracuseStep 2351855 = 3527783) B3527783
theorem B13411277 : Blo 1393516 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B1394079 : Blo 1393516 1394079 := bstep (se 1 (by rfl) ⟨1045559, by rfl⟩ : syracuseStep 1394079 = 2091119) B2091119
theorem B1885799 : Blo 1393516 1885799 := bstep (se 1 (by rfl) ⟨1414349, by rfl⟩ : syracuseStep 1885799 = 2828699) B2828699
theorem B1394459 : Blo 1393516 1394459 := bstep (se 1 (by rfl) ⟨1045844, by rfl⟩ : syracuseStep 1394459 = 2091689) B2091689
theorem B5294119 : Blo 1393516 5294119 := bstep (se 1 (by rfl) ⟨3970589, by rfl⟩ : syracuseStep 5294119 = 7941179) B7941179
theorem B2091263 : Blo 1393516 2091263 := bstep (se 1 (by rfl) ⟨1568447, by rfl⟩ : syracuseStep 2091263 = 3136895) B3136895
theorem B11913479 : Blo 1393516 11913479 := bstep (se 1 (by rfl) ⟨8935109, by rfl⟩ : syracuseStep 11913479 = 17870219) B17870219
theorem B17943689 : Blo 1393516 17943689 := bstep (se 2 (by rfl) ⟨6728883, by rfl⟩ : syracuseStep 17943689 = 13457767) B13457767
theorem B5090921 : Blo 1393516 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B2092655 : Blo 1393516 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B8933111 : Blo 1393516 8933111 := bstep (se 1 (by rfl) ⟨6699833, by rfl⟩ : syracuseStep 8933111 = 13399667) B13399667
theorem B1765147 : Blo 1393516 1765147 := bstep (se 1 (by rfl) ⟨1323860, by rfl⟩ : syracuseStep 1765147 = 2647721) B2647721
theorem B688747673 : Blo 1393516 688747673 := bstep (se 2 (by rfl) ⟨258280377, by rfl⟩ : syracuseStep 688747673 = 516560755) B516560755
theorem B8937161 : Blo 1393516 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B11911495 : Blo 1393516 11911495 := bstep (se 1 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 11911495 = 17867243) B17867243
theorem B1394175 : Blo 1393516 1394175 := bstep (se 1 (by rfl) ⟨1045631, by rfl⟩ : syracuseStep 1394175 = 2091263) B2091263
theorem B11962459 : Blo 1393516 11962459 := bstep (se 1 (by rfl) ⟨8971844, by rfl⟩ : syracuseStep 11962459 = 17943689) B17943689
theorem B2353529 : Blo 1393516 2353529 := bstep (se 2 (by rfl) ⟨882573, by rfl⟩ : syracuseStep 2353529 = 1765147) B1765147
theorem B3393947 : Blo 1393516 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B1395103 : Blo 1393516 1395103 := bstep (se 1 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 1395103 = 2092655) B2092655
theorem B5958107 : Blo 1393516 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B1567903 : Blo 1393516 1567903 := bstep (se 1 (by rfl) ⟨1175927, by rfl⟩ : syracuseStep 1567903 = 2351855) B2351855
theorem B8940851 : Blo 1393516 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B459165115 : Blo 1393516 459165115 := bstep (se 1 (by rfl) ⟨344373836, by rfl⟩ : syracuseStep 459165115 = 688747673) B688747673
theorem B7942319 : Blo 1393516 7942319 := bstep (se 1 (by rfl) ⟨5956739, by rfl⟩ : syracuseStep 7942319 = 11913479) B11913479
theorem B7058825 : Blo 1393516 7058825 := bstep (se 2 (by rfl) ⟨2647059, by rfl⟩ : syracuseStep 7058825 = 5294119) B5294119
theorem B11916827 : Blo 1393516 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B5028797 : Blo 1393516 5028797 := bstep (se 3 (by rfl) ⟨942899, by rfl⟩ : syracuseStep 5028797 = 1885799) B1885799
theorem B5955407 : Blo 1393516 5955407 := bstep (se 1 (by rfl) ⟨4466555, by rfl⟩ : syracuseStep 5955407 = 8933111) B8933111
theorem B15949945 : Blo 1393516 15949945 := bstep (se 2 (by rfl) ⟨5981229, by rfl⟩ : syracuseStep 15949945 = 11962459) B11962459
theorem B2090537 : Blo 1393516 2090537 := bstep (se 2 (by rfl) ⟨783951, by rfl⟩ : syracuseStep 2090537 = 1567903) B1567903
theorem B3352531 : Blo 1393516 3352531 := bstep (se 1 (by rfl) ⟨2514398, by rfl⟩ : syracuseStep 3352531 = 5028797) B5028797
theorem B5294879 : Blo 1393516 5294879 := bstep (se 1 (by rfl) ⟨3971159, by rfl⟩ : syracuseStep 5294879 = 7942319) B7942319
theorem B4705883 : Blo 1393516 4705883 := bstep (se 1 (by rfl) ⟨3529412, by rfl⟩ : syracuseStep 4705883 = 7058825) B7058825
theorem B1569019 : Blo 1393516 1569019 := bstep (se 1 (by rfl) ⟨1176764, by rfl⟩ : syracuseStep 1569019 = 2353529) B2353529
theorem B5960567 : Blo 1393516 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B3970271 : Blo 1393516 3970271 := bstep (se 1 (by rfl) ⟨2977703, by rfl⟩ : syracuseStep 3970271 = 5955407) B5955407
theorem B15881993 : Blo 1393516 15881993 := bstep (se 2 (by rfl) ⟨5955747, by rfl⟩ : syracuseStep 15881993 = 11911495) B11911495
theorem B7944551 : Blo 1393516 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B9050525 : Blo 1393516 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B3972071 : Blo 1393516 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B612220153 : Blo 1393516 612220153 := bstep (se 2 (by rfl) ⟨229582557, by rfl⟩ : syracuseStep 612220153 = 459165115) B459165115
theorem B21266593 : Blo 1393516 21266593 := bstep (se 2 (by rfl) ⟨7974972, by rfl⟩ : syracuseStep 21266593 = 15949945) B15949945
theorem B3973711 : Blo 1393516 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B2646847 : Blo 1393516 2646847 := bstep (se 1 (by rfl) ⟨1985135, by rfl⟩ : syracuseStep 2646847 = 3970271) B3970271
theorem B1393691 : Blo 1393516 1393691 := bstep (se 1 (by rfl) ⟨1045268, by rfl⟩ : syracuseStep 1393691 = 2090537) B2090537
theorem B816293537 : Blo 1393516 816293537 := bstep (se 2 (by rfl) ⟨306110076, by rfl⟩ : syracuseStep 816293537 = 612220153) B612220153
theorem B2648047 : Blo 1393516 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B2092025 : Blo 1393516 2092025 := bstep (se 2 (by rfl) ⟨784509, by rfl⟩ : syracuseStep 2092025 = 1569019) B1569019
theorem B10587995 : Blo 1393516 10587995 := bstep (se 1 (by rfl) ⟨7940996, by rfl⟩ : syracuseStep 10587995 = 15881993) B15881993
theorem B5296367 : Blo 1393516 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B6033683 : Blo 1393516 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B4470041 : Blo 1393516 4470041 := bstep (se 2 (by rfl) ⟨1676265, by rfl⟩ : syracuseStep 4470041 = 3352531) B3352531
theorem B3529919 : Blo 1393516 3529919 := bstep (se 1 (by rfl) ⟨2647439, by rfl⟩ : syracuseStep 3529919 = 5294879) B5294879
theorem B3137255 : Blo 1393516 3137255 := bstep (se 1 (by rfl) ⟨2352941, by rfl⟩ : syracuseStep 3137255 = 4705883) B4705883
theorem B3530911 : Blo 1393516 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B4022455 : Blo 1393516 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B544195691 : Blo 1393516 544195691 := bstep (se 1 (by rfl) ⟨408146768, by rfl⟩ : syracuseStep 544195691 = 816293537) B816293537
theorem B1394683 : Blo 1393516 1394683 := bstep (se 1 (by rfl) ⟨1046012, by rfl⟩ : syracuseStep 1394683 = 2092025) B2092025
theorem B2353279 : Blo 1393516 2353279 := bstep (se 1 (by rfl) ⟨1764959, by rfl⟩ : syracuseStep 2353279 = 3529919) B3529919
theorem B2091503 : Blo 1393516 2091503 := bstep (se 1 (by rfl) ⟨1568627, by rfl⟩ : syracuseStep 2091503 = 3137255) B3137255
theorem B113421829 : Blo 1393516 113421829 := bstep (se 4 (by rfl) ⟨10633296, by rfl⟩ : syracuseStep 113421829 = 21266593) B21266593
theorem B7058663 : Blo 1393516 7058663 := bstep (se 1 (by rfl) ⟨5293997, by rfl⟩ : syracuseStep 7058663 = 10587995) B10587995
theorem B5298281 : Blo 1393516 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B2980027 : Blo 1393516 2980027 := bstep (se 1 (by rfl) ⟨2235020, by rfl⟩ : syracuseStep 2980027 = 4470041) B4470041
theorem B3529129 : Blo 1393516 3529129 := bstep (se 2 (by rfl) ⟨1323423, by rfl⟩ : syracuseStep 3529129 = 2646847) B2646847
theorem B3530729 : Blo 1393516 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B3137705 : Blo 1393516 3137705 := bstep (se 2 (by rfl) ⟨1176639, by rfl⟩ : syracuseStep 3137705 = 2353279) B2353279
theorem B3973369 : Blo 1393516 3973369 := bstep (se 2 (by rfl) ⟨1490013, by rfl⟩ : syracuseStep 3973369 = 2980027) B2980027
theorem B3532187 : Blo 1393516 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B1394335 : Blo 1393516 1394335 := bstep (se 1 (by rfl) ⟨1045751, by rfl⟩ : syracuseStep 1394335 = 2091503) B2091503
theorem B2353819 : Blo 1393516 2353819 := bstep (se 1 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 2353819 = 3530729) B3530729
theorem B4705505 : Blo 1393516 4705505 := bstep (se 2 (by rfl) ⟨1764564, by rfl⟩ : syracuseStep 4705505 = 3529129) B3529129
theorem B4705775 : Blo 1393516 4705775 := bstep (se 1 (by rfl) ⟨3529331, by rfl⟩ : syracuseStep 4705775 = 7058663) B7058663
theorem B151229105 : Blo 1393516 151229105 := bstep (se 2 (by rfl) ⟨56710914, by rfl⟩ : syracuseStep 151229105 = 113421829) B113421829
theorem B4707881 : Blo 1393516 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B5363273 : Blo 1393516 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B362797127 : Blo 1393516 362797127 := bstep (se 1 (by rfl) ⟨272097845, by rfl⟩ : syracuseStep 362797127 = 544195691) B544195691
theorem B100819403 : Blo 1393516 100819403 := bstep (se 1 (by rfl) ⟨75614552, by rfl⟩ : syracuseStep 100819403 = 151229105) B151229105
theorem B3138425 : Blo 1393516 3138425 := bstep (se 2 (by rfl) ⟨1176909, by rfl⟩ : syracuseStep 3138425 = 2353819) B2353819
theorem B3138587 : Blo 1393516 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B2091803 : Blo 1393516 2091803 := bstep (se 1 (by rfl) ⟨1568852, by rfl⟩ : syracuseStep 2091803 = 3137705) B3137705
theorem B2354791 : Blo 1393516 2354791 := bstep (se 1 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 2354791 = 3532187) B3532187
theorem B3575515 : Blo 1393516 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B241864751 : Blo 1393516 241864751 := bstep (se 1 (by rfl) ⟨181398563, by rfl⟩ : syracuseStep 241864751 = 362797127) B362797127
theorem B5297825 : Blo 1393516 5297825 := bstep (se 2 (by rfl) ⟨1986684, by rfl⟩ : syracuseStep 5297825 = 3973369) B3973369
theorem B3137003 : Blo 1393516 3137003 := bstep (se 1 (by rfl) ⟨2352752, by rfl⟩ : syracuseStep 3137003 = 4705505) B4705505
theorem B3137183 : Blo 1393516 3137183 := bstep (se 1 (by rfl) ⟨2352887, by rfl⟩ : syracuseStep 3137183 = 4705775) B4705775
theorem B161243167 : Blo 1393516 161243167 := bstep (se 1 (by rfl) ⟨120932375, by rfl⟩ : syracuseStep 161243167 = 241864751) B241864751
theorem B3531883 : Blo 1393516 3531883 := bstep (se 1 (by rfl) ⟨2648912, by rfl⟩ : syracuseStep 3531883 = 5297825) B5297825
theorem B1394535 : Blo 1393516 1394535 := bstep (se 1 (by rfl) ⟨1045901, by rfl⟩ : syracuseStep 1394535 = 2091803) B2091803
theorem B3139721 : Blo 1393516 3139721 := bstep (se 2 (by rfl) ⟨1177395, by rfl⟩ : syracuseStep 3139721 = 2354791) B2354791
theorem B2091335 : Blo 1393516 2091335 := bstep (se 1 (by rfl) ⟨1568501, by rfl⟩ : syracuseStep 2091335 = 3137003) B3137003
theorem B2091455 : Blo 1393516 2091455 := bstep (se 1 (by rfl) ⟨1568591, by rfl⟩ : syracuseStep 2091455 = 3137183) B3137183
theorem B2092283 : Blo 1393516 2092283 := bstep (se 1 (by rfl) ⟨1569212, by rfl⟩ : syracuseStep 2092283 = 3138425) B3138425
theorem B2092391 : Blo 1393516 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B67212935 : Blo 1393516 67212935 := bstep (se 1 (by rfl) ⟨50409701, by rfl⟩ : syracuseStep 67212935 = 100819403) B100819403
theorem B4767353 : Blo 1393516 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3439854229 : Blo 1393516 3439854229 := bstep (se 6 (by rfl) ⟨80621583, by rfl⟩ : syracuseStep 3439854229 = 161243167) B161243167
theorem B1394223 : Blo 1393516 1394223 := bstep (se 1 (by rfl) ⟨1045667, by rfl⟩ : syracuseStep 1394223 = 2091335) B2091335
theorem B1394303 : Blo 1393516 1394303 := bstep (se 1 (by rfl) ⟨1045727, by rfl⟩ : syracuseStep 1394303 = 2091455) B2091455
theorem B1394855 : Blo 1393516 1394855 := bstep (se 1 (by rfl) ⟨1046141, by rfl⟩ : syracuseStep 1394855 = 2092283) B2092283
theorem B1394927 : Blo 1393516 1394927 := bstep (se 1 (by rfl) ⟨1046195, by rfl⟩ : syracuseStep 1394927 = 2092391) B2092391
theorem B2093147 : Blo 1393516 2093147 := bstep (se 1 (by rfl) ⟨1569860, by rfl⟩ : syracuseStep 2093147 = 3139721) B3139721
theorem B44808623 : Blo 1393516 44808623 := bstep (se 1 (by rfl) ⟨33606467, by rfl⟩ : syracuseStep 44808623 = 67212935) B67212935
theorem B4709177 : Blo 1393516 4709177 := bstep (se 2 (by rfl) ⟨1765941, by rfl⟩ : syracuseStep 4709177 = 3531883) B3531883
theorem B3178235 : Blo 1393516 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B4586472305 : Blo 1393516 4586472305 := bstep (se 2 (by rfl) ⟨1719927114, by rfl⟩ : syracuseStep 4586472305 = 3439854229) B3439854229
theorem B3139451 : Blo 1393516 3139451 := bstep (se 1 (by rfl) ⟨2354588, by rfl⟩ : syracuseStep 3139451 = 4709177) B4709177
theorem B1395431 : Blo 1393516 1395431 := bstep (se 1 (by rfl) ⟨1046573, by rfl⟩ : syracuseStep 1395431 = 2093147) B2093147
theorem B29872415 : Blo 1393516 29872415 := bstep (se 1 (by rfl) ⟨22404311, by rfl⟩ : syracuseStep 29872415 = 44808623) B44808623
theorem B8475293 : Blo 1393516 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B19914943 : Blo 1393516 19914943 := bstep (se 1 (by rfl) ⟨14936207, by rfl⟩ : syracuseStep 19914943 = 29872415) B29872415
theorem B3057648203 : Blo 1393516 3057648203 := bstep (se 1 (by rfl) ⟨2293236152, by rfl⟩ : syracuseStep 3057648203 = 4586472305) B4586472305
theorem B2092967 : Blo 1393516 2092967 := bstep (se 1 (by rfl) ⟨1569725, by rfl⟩ : syracuseStep 2092967 = 3139451) B3139451
theorem B5650195 : Blo 1393516 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B8153728541 : Blo 1393516 8153728541 := bstep (se 3 (by rfl) ⟨1528824101, by rfl⟩ : syracuseStep 8153728541 = 3057648203) B3057648203
theorem B1395311 : Blo 1393516 1395311 := bstep (se 1 (by rfl) ⟨1046483, by rfl⟩ : syracuseStep 1395311 = 2092967) B2092967
theorem B26553257 : Blo 1393516 26553257 := bstep (se 2 (by rfl) ⟨9957471, by rfl⟩ : syracuseStep 26553257 = 19914943) B19914943
theorem B7533593 : Blo 1393516 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B5022395 : Blo 1393516 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B5435819027 : Blo 1393516 5435819027 := bstep (se 1 (by rfl) ⟨4076864270, by rfl⟩ : syracuseStep 5435819027 = 8153728541) B8153728541
theorem B17702171 : Blo 1393516 17702171 := bstep (se 1 (by rfl) ⟨13276628, by rfl⟩ : syracuseStep 17702171 = 26553257) B26553257
theorem B3623879351 : Blo 1393516 3623879351 := bstep (se 1 (by rfl) ⟨2717909513, by rfl⟩ : syracuseStep 3623879351 = 5435819027) B5435819027
theorem B11801447 : Blo 1393516 11801447 := bstep (se 1 (by rfl) ⟨8851085, by rfl⟩ : syracuseStep 11801447 = 17702171) B17702171
theorem B3348263 : Blo 1393516 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B2415919567 : Blo 1393516 2415919567 := bstep (se 1 (by rfl) ⟨1811939675, by rfl⟩ : syracuseStep 2415919567 = 3623879351) B3623879351
theorem B7867631 : Blo 1393516 7867631 := bstep (se 1 (by rfl) ⟨5900723, by rfl⟩ : syracuseStep 7867631 = 11801447) B11801447
theorem B8928701 : Blo 1393516 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B3221226089 : Blo 1393516 3221226089 := bstep (se 2 (by rfl) ⟨1207959783, by rfl⟩ : syracuseStep 3221226089 = 2415919567) B2415919567
theorem B5245087 : Blo 1393516 5245087 := bstep (se 1 (by rfl) ⟨3933815, by rfl⟩ : syracuseStep 5245087 = 7867631) B7867631
theorem B5952467 : Blo 1393516 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B2147484059 : Blo 1393516 2147484059 := bstep (se 1 (by rfl) ⟨1610613044, by rfl⟩ : syracuseStep 2147484059 = 3221226089) B3221226089
theorem B15873245 : Blo 1393516 15873245 := bstep (se 3 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 15873245 = 5952467) B5952467
theorem B6993449 : Blo 1393516 6993449 := bstep (se 2 (by rfl) ⟨2622543, by rfl⟩ : syracuseStep 6993449 = 5245087) B5245087
theorem B4662299 : Blo 1393516 4662299 := bstep (se 1 (by rfl) ⟨3496724, by rfl⟩ : syracuseStep 4662299 = 6993449) B6993449
theorem B1431656039 : Blo 1393516 1431656039 := bstep (se 1 (by rfl) ⟨1073742029, by rfl⟩ : syracuseStep 1431656039 = 2147484059) B2147484059
theorem B10582163 : Blo 1393516 10582163 := bstep (se 1 (by rfl) ⟨7936622, by rfl⟩ : syracuseStep 10582163 = 15873245) B15873245
theorem B7054775 : Blo 1393516 7054775 := bstep (se 1 (by rfl) ⟨5291081, by rfl⟩ : syracuseStep 7054775 = 10582163) B10582163
theorem B954437359 : Blo 1393516 954437359 := bstep (se 1 (by rfl) ⟨715828019, by rfl⟩ : syracuseStep 954437359 = 1431656039) B1431656039
theorem B12432797 : Blo 1393516 12432797 := bstep (se 3 (by rfl) ⟨2331149, by rfl⟩ : syracuseStep 12432797 = 4662299) B4662299
theorem B4703183 : Blo 1393516 4703183 := bstep (se 1 (by rfl) ⟨3527387, by rfl⟩ : syracuseStep 4703183 = 7054775) B7054775
theorem B1272583145 : Blo 1393516 1272583145 := bstep (se 2 (by rfl) ⟨477218679, by rfl⟩ : syracuseStep 1272583145 = 954437359) B954437359
theorem B8288531 : Blo 1393516 8288531 := bstep (se 1 (by rfl) ⟨6216398, by rfl⟩ : syracuseStep 8288531 = 12432797) B12432797
theorem B848388763 : Blo 1393516 848388763 := bstep (se 1 (by rfl) ⟨636291572, by rfl⟩ : syracuseStep 848388763 = 1272583145) B1272583145
theorem B5525687 : Blo 1393516 5525687 := bstep (se 1 (by rfl) ⟨4144265, by rfl⟩ : syracuseStep 5525687 = 8288531) B8288531
theorem B3135455 : Blo 1393516 3135455 := bstep (se 1 (by rfl) ⟨2351591, by rfl⟩ : syracuseStep 3135455 = 4703183) B4703183
theorem B1131185017 : Blo 1393516 1131185017 := bstep (se 2 (by rfl) ⟨424194381, by rfl⟩ : syracuseStep 1131185017 = 848388763) B848388763
theorem B2090303 : Blo 1393516 2090303 := bstep (se 1 (by rfl) ⟨1567727, by rfl⟩ : syracuseStep 2090303 = 3135455) B3135455
theorem B3683791 : Blo 1393516 3683791 := bstep (se 1 (by rfl) ⟨2762843, by rfl⟩ : syracuseStep 3683791 = 5525687) B5525687
theorem B1393535 : Blo 1393516 1393535 := bstep (se 1 (by rfl) ⟨1045151, by rfl⟩ : syracuseStep 1393535 = 2090303) B2090303
theorem B1508246689 : Blo 1393516 1508246689 := bstep (se 2 (by rfl) ⟨565592508, by rfl⟩ : syracuseStep 1508246689 = 1131185017) B1131185017
theorem B4911721 : Blo 1393516 4911721 := bstep (se 2 (by rfl) ⟨1841895, by rfl⟩ : syracuseStep 4911721 = 3683791) B3683791
theorem B26195845 : Blo 1393516 26195845 := bstep (se 4 (by rfl) ⟨2455860, by rfl⟩ : syracuseStep 26195845 = 4911721) B4911721
theorem B2010995585 : Blo 1393516 2010995585 := bstep (se 2 (by rfl) ⟨754123344, by rfl⟩ : syracuseStep 2010995585 = 1508246689) B1508246689
theorem B1340663723 : Blo 1393516 1340663723 := bstep (se 1 (by rfl) ⟨1005497792, by rfl⟩ : syracuseStep 1340663723 = 2010995585) B2010995585
theorem B34927793 : Blo 1393516 34927793 := bstep (se 2 (by rfl) ⟨13097922, by rfl⟩ : syracuseStep 34927793 = 26195845) B26195845
theorem B23285195 : Blo 1393516 23285195 := bstep (se 1 (by rfl) ⟨17463896, by rfl⟩ : syracuseStep 23285195 = 34927793) B34927793
theorem B893775815 : Blo 1393516 893775815 := bstep (se 1 (by rfl) ⟨670331861, by rfl⟩ : syracuseStep 893775815 = 1340663723) B1340663723
theorem B595850543 : Blo 1393516 595850543 := bstep (se 1 (by rfl) ⟨446887907, by rfl⟩ : syracuseStep 595850543 = 893775815) B893775815
theorem B15523463 : Blo 1393516 15523463 := bstep (se 1 (by rfl) ⟨11642597, by rfl⟩ : syracuseStep 15523463 = 23285195) B23285195
theorem B41395901 : Blo 1393516 41395901 := bstep (se 3 (by rfl) ⟨7761731, by rfl⟩ : syracuseStep 41395901 = 15523463) B15523463
theorem B397233695 : Blo 1393516 397233695 := bstep (se 1 (by rfl) ⟨297925271, by rfl⟩ : syracuseStep 397233695 = 595850543) B595850543
theorem B110389069 : Blo 1393516 110389069 := bstep (se 3 (by rfl) ⟨20697950, by rfl⟩ : syracuseStep 110389069 = 41395901) B41395901
theorem B264822463 : Blo 1393516 264822463 := bstep (se 1 (by rfl) ⟨198616847, by rfl⟩ : syracuseStep 264822463 = 397233695) B397233695
theorem B1412386469 : Blo 1393516 1412386469 := bstep (se 4 (by rfl) ⟨132411231, by rfl⟩ : syracuseStep 1412386469 = 264822463) B264822463
theorem B147185425 : Blo 1393516 147185425 := bstep (se 2 (by rfl) ⟨55194534, by rfl⟩ : syracuseStep 147185425 = 110389069) B110389069
theorem B941590979 : Blo 1393516 941590979 := bstep (se 1 (by rfl) ⟨706193234, by rfl⟩ : syracuseStep 941590979 = 1412386469) B1412386469
theorem B196247233 : Blo 1393516 196247233 := bstep (se 2 (by rfl) ⟨73592712, by rfl⟩ : syracuseStep 196247233 = 147185425) B147185425
theorem B261662977 : Blo 1393516 261662977 := bstep (se 2 (by rfl) ⟨98123616, by rfl⟩ : syracuseStep 261662977 = 196247233) B196247233
theorem B627727319 : Blo 1393516 627727319 := bstep (se 1 (by rfl) ⟨470795489, by rfl⟩ : syracuseStep 627727319 = 941590979) B941590979
theorem B1395535877 : Blo 1393516 1395535877 := bstep (se 4 (by rfl) ⟨130831488, by rfl⟩ : syracuseStep 1395535877 = 261662977) B261662977
theorem B418484879 : Blo 1393516 418484879 := bstep (se 1 (by rfl) ⟨313863659, by rfl⟩ : syracuseStep 418484879 = 627727319) B627727319
theorem B930357251 : Blo 1393516 930357251 := bstep (se 1 (by rfl) ⟨697767938, by rfl⟩ : syracuseStep 930357251 = 1395535877) B1395535877
theorem B278989919 : Blo 1393516 278989919 := bstep (se 1 (by rfl) ⟨209242439, by rfl⟩ : syracuseStep 278989919 = 418484879) B418484879
theorem B185993279 : Blo 1393516 185993279 := bstep (se 1 (by rfl) ⟨139494959, by rfl⟩ : syracuseStep 185993279 = 278989919) B278989919
theorem B620238167 : Blo 1393516 620238167 := bstep (se 1 (by rfl) ⟨465178625, by rfl⟩ : syracuseStep 620238167 = 930357251) B930357251
theorem B413492111 : Blo 1393516 413492111 := bstep (se 1 (by rfl) ⟨310119083, by rfl⟩ : syracuseStep 413492111 = 620238167) B620238167
theorem B123995519 : Blo 1393516 123995519 := bstep (se 1 (by rfl) ⟨92996639, by rfl⟩ : syracuseStep 123995519 = 185993279) B185993279
theorem B275661407 : Blo 1393516 275661407 := bstep (se 1 (by rfl) ⟨206746055, by rfl⟩ : syracuseStep 275661407 = 413492111) B413492111
theorem B82663679 : Blo 1393516 82663679 := bstep (se 1 (by rfl) ⟨61997759, by rfl⟩ : syracuseStep 82663679 = 123995519) B123995519
theorem B55109119 : Blo 1393516 55109119 := bstep (se 1 (by rfl) ⟨41331839, by rfl⟩ : syracuseStep 55109119 = 82663679) B82663679
theorem B183774271 : Blo 1393516 183774271 := bstep (se 1 (by rfl) ⟨137830703, by rfl⟩ : syracuseStep 183774271 = 275661407) B275661407
theorem B245032361 : Blo 1393516 245032361 := bstep (se 2 (by rfl) ⟨91887135, by rfl⟩ : syracuseStep 245032361 = 183774271) B183774271
theorem B73478825 : Blo 1393516 73478825 := bstep (se 2 (by rfl) ⟨27554559, by rfl⟩ : syracuseStep 73478825 = 55109119) B55109119
theorem B48985883 : Blo 1393516 48985883 := bstep (se 1 (by rfl) ⟨36739412, by rfl⟩ : syracuseStep 48985883 = 73478825) B73478825
theorem B163354907 : Blo 1393516 163354907 := bstep (se 1 (by rfl) ⟨122516180, by rfl⟩ : syracuseStep 163354907 = 245032361) B245032361
theorem B435613085 : Blo 1393516 435613085 := bstep (se 3 (by rfl) ⟨81677453, by rfl⟩ : syracuseStep 435613085 = 163354907) B163354907
theorem B32657255 : Blo 1393516 32657255 := bstep (se 1 (by rfl) ⟨24492941, by rfl⟩ : syracuseStep 32657255 = 48985883) B48985883
theorem B290408723 : Blo 1393516 290408723 := bstep (se 1 (by rfl) ⟨217806542, by rfl⟩ : syracuseStep 290408723 = 435613085) B435613085
theorem B21771503 : Blo 1393516 21771503 := bstep (se 1 (by rfl) ⟨16328627, by rfl⟩ : syracuseStep 21771503 = 32657255) B32657255
theorem B193605815 : Blo 1393516 193605815 := bstep (se 1 (by rfl) ⟨145204361, by rfl⟩ : syracuseStep 193605815 = 290408723) B290408723
theorem B14514335 : Blo 1393516 14514335 := bstep (se 1 (by rfl) ⟨10885751, by rfl⟩ : syracuseStep 14514335 = 21771503) B21771503
theorem B9676223 : Blo 1393516 9676223 := bstep (se 1 (by rfl) ⟨7257167, by rfl⟩ : syracuseStep 9676223 = 14514335) B14514335
theorem B516282173 : Blo 1393516 516282173 := bstep (se 3 (by rfl) ⟨96802907, by rfl⟩ : syracuseStep 516282173 = 193605815) B193605815
theorem B344188115 : Blo 1393516 344188115 := bstep (se 1 (by rfl) ⟨258141086, by rfl⟩ : syracuseStep 344188115 = 516282173) B516282173
theorem B6450815 : Blo 1393516 6450815 := bstep (se 1 (by rfl) ⟨4838111, by rfl⟩ : syracuseStep 6450815 = 9676223) B9676223
theorem B229458743 : Blo 1393516 229458743 := bstep (se 1 (by rfl) ⟨172094057, by rfl⟩ : syracuseStep 229458743 = 344188115) B344188115
theorem B4300543 : Blo 1393516 4300543 := bstep (se 1 (by rfl) ⟨3225407, by rfl⟩ : syracuseStep 4300543 = 6450815) B6450815
theorem B152972495 : Blo 1393516 152972495 := bstep (se 1 (by rfl) ⟨114729371, by rfl⟩ : syracuseStep 152972495 = 229458743) B229458743
theorem B22936229 : Blo 1393516 22936229 := bstep (se 4 (by rfl) ⟨2150271, by rfl⟩ : syracuseStep 22936229 = 4300543) B4300543
theorem B15290819 : Blo 1393516 15290819 := bstep (se 1 (by rfl) ⟨11468114, by rfl⟩ : syracuseStep 15290819 = 22936229) B22936229
theorem B101981663 : Blo 1393516 101981663 := bstep (se 1 (by rfl) ⟨76486247, by rfl⟩ : syracuseStep 101981663 = 152972495) B152972495
theorem B67987775 : Blo 1393516 67987775 := bstep (se 1 (by rfl) ⟨50990831, by rfl⟩ : syracuseStep 67987775 = 101981663) B101981663
theorem B10193879 : Blo 1393516 10193879 := bstep (se 1 (by rfl) ⟨7645409, by rfl⟩ : syracuseStep 10193879 = 15290819) B15290819
theorem B6795919 : Blo 1393516 6795919 := bstep (se 1 (by rfl) ⟨5096939, by rfl⟩ : syracuseStep 6795919 = 10193879) B10193879
theorem B45325183 : Blo 1393516 45325183 := bstep (se 1 (by rfl) ⟨33993887, by rfl⟩ : syracuseStep 45325183 = 67987775) B67987775
theorem B60433577 : Blo 1393516 60433577 := bstep (se 2 (by rfl) ⟨22662591, by rfl⟩ : syracuseStep 60433577 = 45325183) B45325183
theorem B36244901 : Blo 1393516 36244901 := bstep (se 4 (by rfl) ⟨3397959, by rfl⟩ : syracuseStep 36244901 = 6795919) B6795919
theorem B40289051 : Blo 1393516 40289051 := bstep (se 1 (by rfl) ⟨30216788, by rfl⟩ : syracuseStep 40289051 = 60433577) B60433577
theorem B24163267 : Blo 1393516 24163267 := bstep (se 1 (by rfl) ⟨18122450, by rfl⟩ : syracuseStep 24163267 = 36244901) B36244901
theorem B26859367 : Blo 1393516 26859367 := bstep (se 1 (by rfl) ⟨20144525, by rfl⟩ : syracuseStep 26859367 = 40289051) B40289051
theorem B32217689 : Blo 1393516 32217689 := bstep (se 2 (by rfl) ⟨12081633, by rfl⟩ : syracuseStep 32217689 = 24163267) B24163267
theorem B35812489 : Blo 1393516 35812489 := bstep (se 2 (by rfl) ⟨13429683, by rfl⟩ : syracuseStep 35812489 = 26859367) B26859367
theorem B21478459 : Blo 1393516 21478459 := bstep (se 1 (by rfl) ⟨16108844, by rfl⟩ : syracuseStep 21478459 = 32217689) B32217689
theorem B28637945 : Blo 1393516 28637945 := bstep (se 2 (by rfl) ⟨10739229, by rfl⟩ : syracuseStep 28637945 = 21478459) B21478459
theorem B47749985 : Blo 1393516 47749985 := bstep (se 2 (by rfl) ⟨17906244, by rfl⟩ : syracuseStep 47749985 = 35812489) B35812489
theorem B19091963 : Blo 1393516 19091963 := bstep (se 1 (by rfl) ⟨14318972, by rfl⟩ : syracuseStep 19091963 = 28637945) B28637945
theorem B31833323 : Blo 1393516 31833323 := bstep (se 1 (by rfl) ⟨23874992, by rfl⟩ : syracuseStep 31833323 = 47749985) B47749985
theorem B21222215 : Blo 1393516 21222215 := bstep (se 1 (by rfl) ⟨15916661, by rfl⟩ : syracuseStep 21222215 = 31833323) B31833323
theorem B12727975 : Blo 1393516 12727975 := bstep (se 1 (by rfl) ⟨9545981, by rfl⟩ : syracuseStep 12727975 = 19091963) B19091963
theorem B14148143 : Blo 1393516 14148143 := bstep (se 1 (by rfl) ⟨10611107, by rfl⟩ : syracuseStep 14148143 = 21222215) B21222215
theorem B16970633 : Blo 1393516 16970633 := bstep (se 2 (by rfl) ⟨6363987, by rfl⟩ : syracuseStep 16970633 = 12727975) B12727975
theorem B150913525 : Blo 1393516 150913525 := bstep (se 5 (by rfl) ⟨7074071, by rfl⟩ : syracuseStep 150913525 = 14148143) B14148143
theorem B11313755 : Blo 1393516 11313755 := bstep (se 1 (by rfl) ⟨8485316, by rfl⟩ : syracuseStep 11313755 = 16970633) B16970633
theorem B7542503 : Blo 1393516 7542503 := bstep (se 1 (by rfl) ⟨5656877, by rfl⟩ : syracuseStep 7542503 = 11313755) B11313755
theorem B201218033 : Blo 1393516 201218033 := bstep (se 2 (by rfl) ⟨75456762, by rfl⟩ : syracuseStep 201218033 = 150913525) B150913525
theorem B536581421 : Blo 1393516 536581421 := bstep (se 3 (by rfl) ⟨100609016, by rfl⟩ : syracuseStep 536581421 = 201218033) B201218033
theorem B5028335 : Blo 1393516 5028335 := bstep (se 1 (by rfl) ⟨3771251, by rfl⟩ : syracuseStep 5028335 = 7542503) B7542503
theorem B357720947 : Blo 1393516 357720947 := bstep (se 1 (by rfl) ⟨268290710, by rfl⟩ : syracuseStep 357720947 = 536581421) B536581421
theorem B3352223 : Blo 1393516 3352223 := bstep (se 1 (by rfl) ⟨2514167, by rfl⟩ : syracuseStep 3352223 = 5028335) B5028335
theorem B8939261 : Blo 1393516 8939261 := bstep (se 3 (by rfl) ⟨1676111, by rfl⟩ : syracuseStep 8939261 = 3352223) B3352223
theorem B238480631 : Blo 1393516 238480631 := bstep (se 1 (by rfl) ⟨178860473, by rfl⟩ : syracuseStep 238480631 = 357720947) B357720947
theorem B5959507 : Blo 1393516 5959507 := bstep (se 1 (by rfl) ⟨4469630, by rfl⟩ : syracuseStep 5959507 = 8939261) B8939261
theorem B158987087 : Blo 1393516 158987087 := bstep (se 1 (by rfl) ⟨119240315, by rfl⟩ : syracuseStep 158987087 = 238480631) B238480631
theorem B105991391 : Blo 1393516 105991391 := bstep (se 1 (by rfl) ⟨79493543, by rfl⟩ : syracuseStep 105991391 = 158987087) B158987087
theorem B7946009 : Blo 1393516 7946009 := bstep (se 2 (by rfl) ⟨2979753, by rfl⟩ : syracuseStep 7946009 = 5959507) B5959507
theorem B70660927 : Blo 1393516 70660927 := bstep (se 1 (by rfl) ⟨52995695, by rfl⟩ : syracuseStep 70660927 = 105991391) B105991391
theorem B5297339 : Blo 1393516 5297339 := bstep (se 1 (by rfl) ⟨3973004, by rfl⟩ : syracuseStep 5297339 = 7946009) B7946009
theorem B3531559 : Blo 1393516 3531559 := bstep (se 1 (by rfl) ⟨2648669, by rfl⟩ : syracuseStep 3531559 = 5297339) B5297339
theorem B94214569 : Blo 1393516 94214569 := bstep (se 2 (by rfl) ⟨35330463, by rfl⟩ : syracuseStep 94214569 = 70660927) B70660927
theorem B125619425 : Blo 1393516 125619425 := bstep (se 2 (by rfl) ⟨47107284, by rfl⟩ : syracuseStep 125619425 = 94214569) B94214569
theorem B4708745 : Blo 1393516 4708745 := bstep (se 2 (by rfl) ⟨1765779, by rfl⟩ : syracuseStep 4708745 = 3531559) B3531559
theorem B3139163 : Blo 1393516 3139163 := bstep (se 1 (by rfl) ⟨2354372, by rfl⟩ : syracuseStep 3139163 = 4708745) B4708745
theorem B83746283 : Blo 1393516 83746283 := bstep (se 1 (by rfl) ⟨62809712, by rfl⟩ : syracuseStep 83746283 = 125619425) B125619425
theorem B223323421 : Blo 1393516 223323421 := bstep (se 3 (by rfl) ⟨41873141, by rfl⟩ : syracuseStep 223323421 = 83746283) B83746283
theorem B2092775 : Blo 1393516 2092775 := bstep (se 1 (by rfl) ⟨1569581, by rfl⟩ : syracuseStep 2092775 = 3139163) B3139163
theorem B297764561 : Blo 1393516 297764561 := bstep (se 2 (by rfl) ⟨111661710, by rfl⟩ : syracuseStep 297764561 = 223323421) B223323421
theorem B1395183 : Blo 1393516 1395183 := bstep (se 1 (by rfl) ⟨1046387, by rfl⟩ : syracuseStep 1395183 = 2092775) B2092775
theorem B198509707 : Blo 1393516 198509707 := bstep (se 1 (by rfl) ⟨148882280, by rfl⟩ : syracuseStep 198509707 = 297764561) B297764561
theorem B264679609 : Blo 1393516 264679609 := bstep (se 2 (by rfl) ⟨99254853, by rfl⟩ : syracuseStep 264679609 = 198509707) B198509707
theorem B352906145 : Blo 1393516 352906145 := bstep (se 2 (by rfl) ⟨132339804, by rfl⟩ : syracuseStep 352906145 = 264679609) B264679609
theorem B235270763 : Blo 1393516 235270763 := bstep (se 1 (by rfl) ⟨176453072, by rfl⟩ : syracuseStep 235270763 = 352906145) B352906145
theorem B156847175 : Blo 1393516 156847175 := bstep (se 1 (by rfl) ⟨117635381, by rfl⟩ : syracuseStep 156847175 = 235270763) B235270763
theorem B104564783 : Blo 1393516 104564783 := bstep (se 1 (by rfl) ⟨78423587, by rfl⟩ : syracuseStep 104564783 = 156847175) B156847175
theorem B69709855 : Blo 1393516 69709855 := bstep (se 1 (by rfl) ⟨52282391, by rfl⟩ : syracuseStep 69709855 = 104564783) B104564783
theorem B92946473 : Blo 1393516 92946473 := bstep (se 2 (by rfl) ⟨34854927, by rfl⟩ : syracuseStep 92946473 = 69709855) B69709855
theorem B61964315 : Blo 1393516 61964315 := bstep (se 1 (by rfl) ⟨46473236, by rfl⟩ : syracuseStep 61964315 = 92946473) B92946473
theorem B41309543 : Blo 1393516 41309543 := bstep (se 1 (by rfl) ⟨30982157, by rfl⟩ : syracuseStep 41309543 = 61964315) B61964315
theorem B27539695 : Blo 1393516 27539695 := bstep (se 1 (by rfl) ⟨20654771, by rfl⟩ : syracuseStep 27539695 = 41309543) B41309543
theorem B146878373 : Blo 1393516 146878373 := bstep (se 4 (by rfl) ⟨13769847, by rfl⟩ : syracuseStep 146878373 = 27539695) B27539695
theorem B391675661 : Blo 1393516 391675661 := bstep (se 3 (by rfl) ⟨73439186, by rfl⟩ : syracuseStep 391675661 = 146878373) B146878373
theorem B261117107 : Blo 1393516 261117107 := bstep (se 1 (by rfl) ⟨195837830, by rfl⟩ : syracuseStep 261117107 = 391675661) B391675661
theorem B174078071 : Blo 1393516 174078071 := bstep (se 1 (by rfl) ⟨130558553, by rfl⟩ : syracuseStep 174078071 = 261117107) B261117107
theorem B116052047 : Blo 1393516 116052047 := bstep (se 1 (by rfl) ⟨87039035, by rfl⟩ : syracuseStep 116052047 = 174078071) B174078071
theorem B77368031 : Blo 1393516 77368031 := bstep (se 1 (by rfl) ⟨58026023, by rfl⟩ : syracuseStep 77368031 = 116052047) B116052047
theorem B51578687 : Blo 1393516 51578687 := bstep (se 1 (by rfl) ⟨38684015, by rfl⟩ : syracuseStep 51578687 = 77368031) B77368031
theorem B34385791 : Blo 1393516 34385791 := bstep (se 1 (by rfl) ⟨25789343, by rfl⟩ : syracuseStep 34385791 = 51578687) B51578687
theorem B45847721 : Blo 1393516 45847721 := bstep (se 2 (by rfl) ⟨17192895, by rfl⟩ : syracuseStep 45847721 = 34385791) B34385791
theorem B30565147 : Blo 1393516 30565147 := bstep (se 1 (by rfl) ⟨22923860, by rfl⟩ : syracuseStep 30565147 = 45847721) B45847721
theorem B40753529 : Blo 1393516 40753529 := bstep (se 2 (by rfl) ⟨15282573, by rfl⟩ : syracuseStep 40753529 = 30565147) B30565147
theorem B27169019 : Blo 1393516 27169019 := bstep (se 1 (by rfl) ⟨20376764, by rfl⟩ : syracuseStep 27169019 = 40753529) B40753529
theorem B18112679 : Blo 1393516 18112679 := bstep (se 1 (by rfl) ⟨13584509, by rfl⟩ : syracuseStep 18112679 = 27169019) B27169019
theorem B12075119 : Blo 1393516 12075119 := bstep (se 1 (by rfl) ⟨9056339, by rfl⟩ : syracuseStep 12075119 = 18112679) B18112679
theorem B8050079 : Blo 1393516 8050079 := bstep (se 1 (by rfl) ⟨6037559, by rfl⟩ : syracuseStep 8050079 = 12075119) B12075119
theorem B5366719 : Blo 1393516 5366719 := bstep (se 1 (by rfl) ⟨4025039, by rfl⟩ : syracuseStep 5366719 = 8050079) B8050079
theorem B7155625 : Blo 1393516 7155625 := bstep (se 2 (by rfl) ⟨2683359, by rfl⟩ : syracuseStep 7155625 = 5366719) B5366719
theorem B9540833 : Blo 1393516 9540833 := bstep (se 2 (by rfl) ⟨3577812, by rfl⟩ : syracuseStep 9540833 = 7155625) B7155625
theorem B25442221 : Blo 1393516 25442221 := bstep (se 3 (by rfl) ⟨4770416, by rfl⟩ : syracuseStep 25442221 = 9540833) B9540833
theorem B33922961 : Blo 1393516 33922961 := bstep (se 2 (by rfl) ⟨12721110, by rfl⟩ : syracuseStep 33922961 = 25442221) B25442221
theorem B22615307 : Blo 1393516 22615307 := bstep (se 1 (by rfl) ⟨16961480, by rfl⟩ : syracuseStep 22615307 = 33922961) B33922961
theorem B15076871 : Blo 1393516 15076871 := bstep (se 1 (by rfl) ⟨11307653, by rfl⟩ : syracuseStep 15076871 = 22615307) B22615307
theorem B10051247 : Blo 1393516 10051247 := bstep (se 1 (by rfl) ⟨7538435, by rfl⟩ : syracuseStep 10051247 = 15076871) B15076871
theorem B26803325 : Blo 1393516 26803325 := bstep (se 3 (by rfl) ⟨5025623, by rfl⟩ : syracuseStep 26803325 = 10051247) B10051247
theorem B17868883 : Blo 1393516 17868883 := bstep (se 1 (by rfl) ⟨13401662, by rfl⟩ : syracuseStep 17868883 = 26803325) B26803325
theorem B23825177 : Blo 1393516 23825177 := bstep (se 2 (by rfl) ⟨8934441, by rfl⟩ : syracuseStep 23825177 = 17868883) B17868883
theorem B15883451 : Blo 1393516 15883451 := bstep (se 1 (by rfl) ⟨11912588, by rfl⟩ : syracuseStep 15883451 = 23825177) B23825177
theorem B10588967 : Blo 1393516 10588967 := bstep (se 1 (by rfl) ⟨7941725, by rfl⟩ : syracuseStep 10588967 = 15883451) B15883451
theorem B7059311 : Blo 1393516 7059311 := bstep (se 1 (by rfl) ⟨5294483, by rfl⟩ : syracuseStep 7059311 = 10588967) B10588967
theorem B4706207 : Blo 1393516 4706207 := bstep (se 1 (by rfl) ⟨3529655, by rfl⟩ : syracuseStep 4706207 = 7059311) B7059311
theorem B3137471 : Blo 1393516 3137471 := bstep (se 1 (by rfl) ⟨2353103, by rfl⟩ : syracuseStep 3137471 = 4706207) B4706207
theorem B2091647 : Blo 1393516 2091647 := bstep (se 1 (by rfl) ⟨1568735, by rfl⟩ : syracuseStep 2091647 = 3137471) B3137471
theorem B1394431 : Blo 1393516 1394431 := bstep (se 1 (by rfl) ⟨1045823, by rfl⟩ : syracuseStep 1394431 = 2091647) B2091647

theorem C0 (j : ℕ) (h1 : 348379 ≤ j) (h2 : j ≤ 348878) : Blo 1393516 (4 * j + 3) := by
  interval_cases j
  · exact B1393519
  · exact B1393523
  · exact B1393527
  · exact B1393531
  · exact B1393535
  · exact B1393539
  · exact B1393543
  · exact B1393547
  · exact B1393551
  · exact B1393555
  · exact B1393559
  · exact B1393563
  · exact B1393567
  · exact B1393571
  · exact B1393575
  · exact B1393579
  · exact B1393583
  · exact B1393587
  · exact B1393591
  · exact B1393595
  · exact B1393599
  · exact B1393603
  · exact B1393607
  · exact B1393611
  · exact B1393615
  · exact B1393619
  · exact B1393623
  · exact B1393627
  · exact B1393631
  · exact B1393635
  · exact B1393639
  · exact B1393643
  · exact B1393647
  · exact B1393651
  · exact B1393655
  · exact B1393659
  · exact B1393663
  · exact B1393667
  · exact B1393671
  · exact B1393675
  · exact B1393679
  · exact B1393683
  · exact B1393687
  · exact B1393691
  · exact B1393695
  · exact B1393699
  · exact B1393703
  · exact B1393707
  · exact B1393711
  · exact B1393715
  · exact B1393719
  · exact B1393723
  · exact B1393727
  · exact B1393731
  · exact B1393735
  · exact B1393739
  · exact B1393743
  · exact B1393747
  · exact B1393751
  · exact B1393755
  · exact B1393759
  · exact B1393763
  · exact B1393767
  · exact B1393771
  · exact B1393775
  · exact B1393779
  · exact B1393783
  · exact B1393787
  · exact B1393791
  · exact B1393795
  · exact B1393799
  · exact B1393803
  · exact B1393807
  · exact B1393811
  · exact B1393815
  · exact B1393819
  · exact B1393823
  · exact B1393827
  · exact B1393831
  · exact B1393835
  · exact B1393839
  · exact B1393843
  · exact B1393847
  · exact B1393851
  · exact B1393855
  · exact B1393859
  · exact B1393863
  · exact B1393867
  · exact B1393871
  · exact B1393875
  · exact B1393879
  · exact B1393883
  · exact B1393887
  · exact B1393891
  · exact B1393895
  · exact B1393899
  · exact B1393903
  · exact B1393907
  · exact B1393911
  · exact B1393915
  · exact B1393919
  · exact B1393923
  · exact B1393927
  · exact B1393931
  · exact B1393935
  · exact B1393939
  · exact B1393943
  · exact B1393947
  · exact B1393951
  · exact B1393955
  · exact B1393959
  · exact B1393963
  · exact B1393967
  · exact B1393971
  · exact B1393975
  · exact B1393979
  · exact B1393983
  · exact B1393987
  · exact B1393991
  · exact B1393995
  · exact B1393999
  · exact B1394003
  · exact B1394007
  · exact B1394011
  · exact B1394015
  · exact B1394019
  · exact B1394023
  · exact B1394027
  · exact B1394031
  · exact B1394035
  · exact B1394039
  · exact B1394043
  · exact B1394047
  · exact B1394051
  · exact B1394055
  · exact B1394059
  · exact B1394063
  · exact B1394067
  · exact B1394071
  · exact B1394075
  · exact B1394079
  · exact B1394083
  · exact B1394087
  · exact B1394091
  · exact B1394095
  · exact B1394099
  · exact B1394103
  · exact B1394107
  · exact B1394111
  · exact B1394115
  · exact B1394119
  · exact B1394123
  · exact B1394127
  · exact B1394131
  · exact B1394135
  · exact B1394139
  · exact B1394143
  · exact B1394147
  · exact B1394151
  · exact B1394155
  · exact B1394159
  · exact B1394163
  · exact B1394167
  · exact B1394171
  · exact B1394175
  · exact B1394179
  · exact B1394183
  · exact B1394187
  · exact B1394191
  · exact B1394195
  · exact B1394199
  · exact B1394203
  · exact B1394207
  · exact B1394211
  · exact B1394215
  · exact B1394219
  · exact B1394223
  · exact B1394227
  · exact B1394231
  · exact B1394235
  · exact B1394239
  · exact B1394243
  · exact B1394247
  · exact B1394251
  · exact B1394255
  · exact B1394259
  · exact B1394263
  · exact B1394267
  · exact B1394271
  · exact B1394275
  · exact B1394279
  · exact B1394283
  · exact B1394287
  · exact B1394291
  · exact B1394295
  · exact B1394299
  · exact B1394303
  · exact B1394307
  · exact B1394311
  · exact B1394315
  · exact B1394319
  · exact B1394323
  · exact B1394327
  · exact B1394331
  · exact B1394335
  · exact B1394339
  · exact B1394343
  · exact B1394347
  · exact B1394351
  · exact B1394355
  · exact B1394359
  · exact B1394363
  · exact B1394367
  · exact B1394371
  · exact B1394375
  · exact B1394379
  · exact B1394383
  · exact B1394387
  · exact B1394391
  · exact B1394395
  · exact B1394399
  · exact B1394403
  · exact B1394407
  · exact B1394411
  · exact B1394415
  · exact B1394419
  · exact B1394423
  · exact B1394427
  · exact B1394431
  · exact B1394435
  · exact B1394439
  · exact B1394443
  · exact B1394447
  · exact B1394451
  · exact B1394455
  · exact B1394459
  · exact B1394463
  · exact B1394467
  · exact B1394471
  · exact B1394475
  · exact B1394479
  · exact B1394483
  · exact B1394487
  · exact B1394491
  · exact B1394495
  · exact B1394499
  · exact B1394503
  · exact B1394507
  · exact B1394511
  · exact B1394515
  · exact B1394519
  · exact B1394523
  · exact B1394527
  · exact B1394531
  · exact B1394535
  · exact B1394539
  · exact B1394543
  · exact B1394547
  · exact B1394551
  · exact B1394555
  · exact B1394559
  · exact B1394563
  · exact B1394567
  · exact B1394571
  · exact B1394575
  · exact B1394579
  · exact B1394583
  · exact B1394587
  · exact B1394591
  · exact B1394595
  · exact B1394599
  · exact B1394603
  · exact B1394607
  · exact B1394611
  · exact B1394615
  · exact B1394619
  · exact B1394623
  · exact B1394627
  · exact B1394631
  · exact B1394635
  · exact B1394639
  · exact B1394643
  · exact B1394647
  · exact B1394651
  · exact B1394655
  · exact B1394659
  · exact B1394663
  · exact B1394667
  · exact B1394671
  · exact B1394675
  · exact B1394679
  · exact B1394683
  · exact B1394687
  · exact B1394691
  · exact B1394695
  · exact B1394699
  · exact B1394703
  · exact B1394707
  · exact B1394711
  · exact B1394715
  · exact B1394719
  · exact B1394723
  · exact B1394727
  · exact B1394731
  · exact B1394735
  · exact B1394739
  · exact B1394743
  · exact B1394747
  · exact B1394751
  · exact B1394755
  · exact B1394759
  · exact B1394763
  · exact B1394767
  · exact B1394771
  · exact B1394775
  · exact B1394779
  · exact B1394783
  · exact B1394787
  · exact B1394791
  · exact B1394795
  · exact B1394799
  · exact B1394803
  · exact B1394807
  · exact B1394811
  · exact B1394815
  · exact B1394819
  · exact B1394823
  · exact B1394827
  · exact B1394831
  · exact B1394835
  · exact B1394839
  · exact B1394843
  · exact B1394847
  · exact B1394851
  · exact B1394855
  · exact B1394859
  · exact B1394863
  · exact B1394867
  · exact B1394871
  · exact B1394875
  · exact B1394879
  · exact B1394883
  · exact B1394887
  · exact B1394891
  · exact B1394895
  · exact B1394899
  · exact B1394903
  · exact B1394907
  · exact B1394911
  · exact B1394915
  · exact B1394919
  · exact B1394923
  · exact B1394927
  · exact B1394931
  · exact B1394935
  · exact B1394939
  · exact B1394943
  · exact B1394947
  · exact B1394951
  · exact B1394955
  · exact B1394959
  · exact B1394963
  · exact B1394967
  · exact B1394971
  · exact B1394975
  · exact B1394979
  · exact B1394983
  · exact B1394987
  · exact B1394991
  · exact B1394995
  · exact B1394999
  · exact B1395003
  · exact B1395007
  · exact B1395011
  · exact B1395015
  · exact B1395019
  · exact B1395023
  · exact B1395027
  · exact B1395031
  · exact B1395035
  · exact B1395039
  · exact B1395043
  · exact B1395047
  · exact B1395051
  · exact B1395055
  · exact B1395059
  · exact B1395063
  · exact B1395067
  · exact B1395071
  · exact B1395075
  · exact B1395079
  · exact B1395083
  · exact B1395087
  · exact B1395091
  · exact B1395095
  · exact B1395099
  · exact B1395103
  · exact B1395107
  · exact B1395111
  · exact B1395115
  · exact B1395119
  · exact B1395123
  · exact B1395127
  · exact B1395131
  · exact B1395135
  · exact B1395139
  · exact B1395143
  · exact B1395147
  · exact B1395151
  · exact B1395155
  · exact B1395159
  · exact B1395163
  · exact B1395167
  · exact B1395171
  · exact B1395175
  · exact B1395179
  · exact B1395183
  · exact B1395187
  · exact B1395191
  · exact B1395195
  · exact B1395199
  · exact B1395203
  · exact B1395207
  · exact B1395211
  · exact B1395215
  · exact B1395219
  · exact B1395223
  · exact B1395227
  · exact B1395231
  · exact B1395235
  · exact B1395239
  · exact B1395243
  · exact B1395247
  · exact B1395251
  · exact B1395255
  · exact B1395259
  · exact B1395263
  · exact B1395267
  · exact B1395271
  · exact B1395275
  · exact B1395279
  · exact B1395283
  · exact B1395287
  · exact B1395291
  · exact B1395295
  · exact B1395299
  · exact B1395303
  · exact B1395307
  · exact B1395311
  · exact B1395315
  · exact B1395319
  · exact B1395323
  · exact B1395327
  · exact B1395331
  · exact B1395335
  · exact B1395339
  · exact B1395343
  · exact B1395347
  · exact B1395351
  · exact B1395355
  · exact B1395359
  · exact B1395363
  · exact B1395367
  · exact B1395371
  · exact B1395375
  · exact B1395379
  · exact B1395383
  · exact B1395387
  · exact B1395391
  · exact B1395395
  · exact B1395399
  · exact B1395403
  · exact B1395407
  · exact B1395411
  · exact B1395415
  · exact B1395419
  · exact B1395423
  · exact B1395427
  · exact B1395431
  · exact B1395435
  · exact B1395439
  · exact B1395443
  · exact B1395447
  · exact B1395451
  · exact B1395455
  · exact B1395459
  · exact B1395463
  · exact B1395467
  · exact B1395471
  · exact B1395475
  · exact B1395479
  · exact B1395483
  · exact B1395487
  · exact B1395491
  · exact B1395495
  · exact B1395499
  · exact B1395503
  · exact B1395507
  · exact B1395511
  · exact B1395515

theorem solution (m : ℕ) (hlo : 1393516 ≤ m) (hhi : m ≤ 1395516) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 348379 ≤ j := by omega
    have hj2 : j ≤ 348878 := by omega
    have hb : Blo 1393516 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
