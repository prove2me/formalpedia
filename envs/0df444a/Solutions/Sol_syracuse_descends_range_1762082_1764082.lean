-- Prove2me | solution 1 for syracuse_descends_range_1762082_1764082
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:39:31.712179+00:00
-- url     : https://prove2.me/submissions/873fd59b-b40e-457e-a4c3-369fc5b385af

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


theorem B5947397 : Blo 1762082 5947397 := bbase (se 4 (by rfl) ⟨557568, by rfl⟩ : syracuseStep 5947397 = 1115137) (by norm_num)
theorem B2646029 : Blo 1762082 2646029 := bbase (se 3 (by rfl) ⟨496130, by rfl⟩ : syracuseStep 2646029 = 992261) (by norm_num)
theorem B3964949 : Blo 1762082 3964949 := bbase (se 6 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 3964949 = 185857) (by norm_num)
theorem B1982497 : Blo 1762082 1982497 := bbase (se 2 (by rfl) ⟨743436, by rfl⟩ : syracuseStep 1982497 = 1486873) (by norm_num)
theorem B2646053 : Blo 1762082 2646053 := bbase (se 4 (by rfl) ⟨248067, by rfl⟩ : syracuseStep 2646053 = 496135) (by norm_num)
theorem B2646077 : Blo 1762082 2646077 := bbase (se 3 (by rfl) ⟨496139, by rfl⟩ : syracuseStep 2646077 = 992279) (by norm_num)
theorem B1982533 : Blo 1762082 1982533 := bbase (se 4 (by rfl) ⟨185862, by rfl⟩ : syracuseStep 1982533 = 371725) (by norm_num)
theorem B2973773 : Blo 1762082 2973773 := bbase (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) (by norm_num)
theorem B2646101 : Blo 1762082 2646101 := bbase (se 8 (by rfl) ⟨15504, by rfl⟩ : syracuseStep 2646101 = 31009) (by norm_num)
theorem B3965021 : Blo 1762082 3965021 := bbase (se 3 (by rfl) ⟨743441, by rfl⟩ : syracuseStep 3965021 = 1486883) (by norm_num)
theorem B5021797 : Blo 1762082 5021797 := bbase (se 4 (by rfl) ⟨470793, by rfl⟩ : syracuseStep 5021797 = 941587) (by norm_num)
theorem B1982569 : Blo 1762082 1982569 := bbase (se 2 (by rfl) ⟨743463, by rfl⟩ : syracuseStep 1982569 = 1486927) (by norm_num)
theorem B1982605 : Blo 1762082 1982605 := bbase (se 3 (by rfl) ⟨371738, by rfl⟩ : syracuseStep 1982605 = 743477) (by norm_num)
theorem B3965093 : Blo 1762082 3965093 := bbase (se 4 (by rfl) ⟨371727, by rfl⟩ : syracuseStep 3965093 = 743455) (by norm_num)
theorem B1982641 : Blo 1762082 1982641 := bbase (se 2 (by rfl) ⟨743490, by rfl⟩ : syracuseStep 1982641 = 1486981) (by norm_num)
theorem B4464821 : Blo 1762082 4464821 := bbase (se 5 (by rfl) ⟨209288, by rfl⟩ : syracuseStep 4464821 = 418577) (by norm_num)
theorem B2973901 : Blo 1762082 2973901 := bbase (se 3 (by rfl) ⟨557606, by rfl⟩ : syracuseStep 2973901 = 1115213) (by norm_num)
theorem B1982677 : Blo 1762082 1982677 := bbase (se 7 (by rfl) ⟨23234, by rfl⟩ : syracuseStep 1982677 = 46469) (by norm_num)
theorem B2384101 : Blo 1762082 2384101 := bbase (se 4 (by rfl) ⟨223509, by rfl⟩ : syracuseStep 2384101 = 447019) (by norm_num)
theorem B3965165 : Blo 1762082 3965165 := bbase (se 3 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 3965165 = 1486937) (by norm_num)
theorem B3391733 : Blo 1762082 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B1982713 : Blo 1762082 1982713 := bbase (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) (by norm_num)
theorem B1982749 : Blo 1762082 1982749 := bbase (se 3 (by rfl) ⟨371765, by rfl⟩ : syracuseStep 1982749 = 743531) (by norm_num)
theorem B2973989 : Blo 1762082 2973989 := bbase (se 4 (by rfl) ⟨278811, by rfl⟩ : syracuseStep 2973989 = 557623) (by norm_num)
theorem B3965237 : Blo 1762082 3965237 := bbase (se 5 (by rfl) ⟨185870, by rfl⟩ : syracuseStep 3965237 = 371741) (by norm_num)
theorem B1909045 : Blo 1762082 1909045 := bbase (se 5 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 1909045 = 178973) (by norm_num)
theorem B1982785 : Blo 1762082 1982785 := bbase (se 2 (by rfl) ⟨743544, by rfl⟩ : syracuseStep 1982785 = 1487089) (by norm_num)
theorem B1982821 : Blo 1762082 1982821 := bbase (se 4 (by rfl) ⟨185889, by rfl⟩ : syracuseStep 1982821 = 371779) (by norm_num)
theorem B17170805 : Blo 1762082 17170805 := bbase (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) (by norm_num)
theorem B3965309 : Blo 1762082 3965309 := bbase (se 3 (by rfl) ⟨743495, by rfl⟩ : syracuseStep 3965309 = 1486991) (by norm_num)
theorem B1982857 : Blo 1762082 1982857 := bbase (se 2 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 1982857 = 1487143) (by norm_num)
theorem B10043797 : Blo 1762082 10043797 := bbase (se 6 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 10043797 = 470803) (by norm_num)
theorem B2146721 : Blo 1762082 2146721 := bbase (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) (by norm_num)
theorem B2974117 : Blo 1762082 2974117 := bbase (se 4 (by rfl) ⟨278823, by rfl⟩ : syracuseStep 2974117 = 557647) (by norm_num)
theorem B1982893 : Blo 1762082 1982893 := bbase (se 3 (by rfl) ⟨371792, by rfl⟩ : syracuseStep 1982893 = 743585) (by norm_num)
theorem B5947829 : Blo 1762082 5947829 := bbase (se 5 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 5947829 = 557609) (by norm_num)
theorem B3965381 : Blo 1762082 3965381 := bbase (se 4 (by rfl) ⟨371754, by rfl⟩ : syracuseStep 3965381 = 743509) (by norm_num)
theorem B1982929 : Blo 1762082 1982929 := bbase (se 2 (by rfl) ⟨743598, by rfl⟩ : syracuseStep 1982929 = 1487197) (by norm_num)
theorem B1982965 : Blo 1762082 1982965 := bbase (se 5 (by rfl) ⟨92951, by rfl⟩ : syracuseStep 1982965 = 185903) (by norm_num)
theorem B2974205 : Blo 1762082 2974205 := bbase (se 3 (by rfl) ⟨557663, by rfl⟩ : syracuseStep 2974205 = 1115327) (by norm_num)
theorem B3965453 : Blo 1762082 3965453 := bbase (se 3 (by rfl) ⟨743522, by rfl⟩ : syracuseStep 3965453 = 1487045) (by norm_num)
theorem B3310093 : Blo 1762082 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B4465165 : Blo 1762082 4465165 := bbase (se 3 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 4465165 = 1674437) (by norm_num)
theorem B29000213 : Blo 1762082 29000213 := bbase (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) (by norm_num)
theorem B1983001 : Blo 1762082 1983001 := bbase (se 2 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 1983001 = 1487251) (by norm_num)
theorem B1983037 : Blo 1762082 1983037 := bbase (se 3 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 1983037 = 743639) (by norm_num)
theorem B3965525 : Blo 1762082 3965525 := bbase (se 8 (by rfl) ⟨23235, by rfl⟩ : syracuseStep 3965525 = 46471) (by norm_num)
theorem B1983073 : Blo 1762082 1983073 := bbase (se 2 (by rfl) ⟨743652, by rfl⟩ : syracuseStep 1983073 = 1487305) (by norm_num)
theorem B2974333 : Blo 1762082 2974333 := bbase (se 3 (by rfl) ⟨557687, by rfl⟩ : syracuseStep 2974333 = 1115375) (by norm_num)
theorem B4465277 : Blo 1762082 4465277 := bbase (se 3 (by rfl) ⟨837239, by rfl⟩ : syracuseStep 4465277 = 1674479) (by norm_num)
theorem B1983109 : Blo 1762082 1983109 := bbase (se 4 (by rfl) ⟨185916, by rfl⟩ : syracuseStep 1983109 = 371833) (by norm_num)
theorem B8929925 : Blo 1762082 8929925 := bbase (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) (by norm_num)
theorem B3965597 : Blo 1762082 3965597 := bbase (se 3 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 3965597 = 1487099) (by norm_num)
theorem B1983145 : Blo 1762082 1983145 := bbase (se 2 (by rfl) ⟨743679, by rfl⟩ : syracuseStep 1983145 = 1487359) (by norm_num)
theorem B1983181 : Blo 1762082 1983181 := bbase (se 3 (by rfl) ⟨371846, by rfl⟩ : syracuseStep 1983181 = 743693) (by norm_num)
theorem B3572437 : Blo 1762082 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B2974421 : Blo 1762082 2974421 := bbase (se 7 (by rfl) ⟨34856, by rfl⟩ : syracuseStep 2974421 = 69713) (by norm_num)
theorem B6439637 : Blo 1762082 6439637 := bbase (se 7 (by rfl) ⟨75464, by rfl⟩ : syracuseStep 6439637 = 150929) (by norm_num)
theorem B13394645 : Blo 1762082 13394645 := bbase (se 7 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 13394645 = 313937) (by norm_num)
theorem B3965669 : Blo 1762082 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B1983217 : Blo 1762082 1983217 := bbase (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) (by norm_num)
theorem B2679565 : Blo 1762082 2679565 := bbase (se 3 (by rfl) ⟨502418, by rfl⟩ : syracuseStep 2679565 = 1004837) (by norm_num)
theorem B1983253 : Blo 1762082 1983253 := bbase (se 6 (by rfl) ⟨46482, by rfl⟩ : syracuseStep 1983253 = 92965) (by norm_num)
theorem B3965741 : Blo 1762082 3965741 := bbase (se 3 (by rfl) ⟨743576, by rfl⟩ : syracuseStep 3965741 = 1487153) (by norm_num)
theorem B1786681 : Blo 1762082 1786681 := bbase (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) (by norm_num)
theorem B1983289 : Blo 1762082 1983289 := bbase (se 2 (by rfl) ⟨743733, by rfl⟩ : syracuseStep 1983289 = 1487467) (by norm_num)
theorem B2974549 : Blo 1762082 2974549 := bbase (se 9 (by rfl) ⟨8714, by rfl⟩ : syracuseStep 2974549 = 17429) (by norm_num)
theorem B1983325 : Blo 1762082 1983325 := bbase (se 3 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 1983325 = 743747) (by norm_num)
theorem B5948261 : Blo 1762082 5948261 := bbase (se 4 (by rfl) ⟨557649, by rfl⟩ : syracuseStep 5948261 = 1115299) (by norm_num)
theorem B3965813 : Blo 1762082 3965813 := bbase (se 5 (by rfl) ⟨185897, by rfl⟩ : syracuseStep 3965813 = 371795) (by norm_num)
theorem B1983361 : Blo 1762082 1983361 := bbase (se 2 (by rfl) ⟨743760, by rfl⟩ : syracuseStep 1983361 = 1487521) (by norm_num)
theorem B3015557 : Blo 1762082 3015557 := bbase (se 4 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 3015557 = 565417) (by norm_num)
theorem B1983397 : Blo 1762082 1983397 := bbase (se 4 (by rfl) ⟨185943, by rfl⟩ : syracuseStep 1983397 = 371887) (by norm_num)
theorem B2974637 : Blo 1762082 2974637 := bbase (se 3 (by rfl) ⟨557744, by rfl⟩ : syracuseStep 2974637 = 1115489) (by norm_num)
theorem B3965885 : Blo 1762082 3965885 := bbase (se 3 (by rfl) ⟨743603, by rfl⟩ : syracuseStep 3965885 = 1487207) (by norm_num)
theorem B1983433 : Blo 1762082 1983433 := bbase (se 2 (by rfl) ⟨743787, by rfl⟩ : syracuseStep 1983433 = 1487575) (by norm_num)
theorem B1983469 : Blo 1762082 1983469 := bbase (se 3 (by rfl) ⟨371900, by rfl⟩ : syracuseStep 1983469 = 743801) (by norm_num)
theorem B3965957 : Blo 1762082 3965957 := bbase (se 4 (by rfl) ⟨371808, by rfl⟩ : syracuseStep 3965957 = 743617) (by norm_num)
theorem B1983505 : Blo 1762082 1983505 := bbase (se 2 (by rfl) ⟨743814, by rfl⟩ : syracuseStep 1983505 = 1487629) (by norm_num)
theorem B8471573 : Blo 1762082 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B10322965 : Blo 1762082 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B8922149 : Blo 1762082 8922149 := bbase (se 4 (by rfl) ⟨836451, by rfl⟩ : syracuseStep 8922149 = 1672903) (by norm_num)
theorem B2974765 : Blo 1762082 2974765 := bbase (se 3 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 2974765 = 1115537) (by norm_num)
theorem B1983541 : Blo 1762082 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B3966029 : Blo 1762082 3966029 := bbase (se 3 (by rfl) ⟨743630, by rfl⟩ : syracuseStep 3966029 = 1487261) (by norm_num)
theorem B1983577 : Blo 1762082 1983577 := bbase (se 2 (by rfl) ⟨743841, by rfl⟩ : syracuseStep 1983577 = 1487683) (by norm_num)
theorem B13386869 : Blo 1762082 13386869 := bbase (se 5 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 13386869 = 1255019) (by norm_num)
theorem B1983613 : Blo 1762082 1983613 := bbase (se 3 (by rfl) ⟨371927, by rfl⟩ : syracuseStep 1983613 = 743855) (by norm_num)
theorem B2974853 : Blo 1762082 2974853 := bbase (se 4 (by rfl) ⟨278892, by rfl⟩ : syracuseStep 2974853 = 557785) (by norm_num)
theorem B4236421 : Blo 1762082 4236421 := bbase (se 4 (by rfl) ⟨397164, by rfl⟩ : syracuseStep 4236421 = 794329) (by norm_num)
theorem B3966101 : Blo 1762082 3966101 := bbase (se 6 (by rfl) ⟨92955, by rfl⟩ : syracuseStep 3966101 = 185911) (by norm_num)
theorem B1787029 : Blo 1762082 1787029 := bbase (se 6 (by rfl) ⟨41883, by rfl⟩ : syracuseStep 1787029 = 83767) (by norm_num)
theorem B1983649 : Blo 1762082 1983649 := bbase (se 2 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 1983649 = 1487737) (by norm_num)
theorem B5022901 : Blo 1762082 5022901 := bbase (se 5 (by rfl) ⟨235448, by rfl⟩ : syracuseStep 5022901 = 470897) (by norm_num)
theorem B1983685 : Blo 1762082 1983685 := bbase (se 4 (by rfl) ⟨185970, by rfl⟩ : syracuseStep 1983685 = 371941) (by norm_num)
theorem B3966173 : Blo 1762082 3966173 := bbase (se 3 (by rfl) ⟨743657, by rfl⟩ : syracuseStep 3966173 = 1487315) (by norm_num)
theorem B1983721 : Blo 1762082 1983721 := bbase (se 2 (by rfl) ⟨743895, by rfl⟩ : syracuseStep 1983721 = 1487791) (by norm_num)
theorem B2974981 : Blo 1762082 2974981 := bbase (se 4 (by rfl) ⟨278904, by rfl⟩ : syracuseStep 2974981 = 557809) (by norm_num)
theorem B1983757 : Blo 1762082 1983757 := bbase (se 3 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 1983757 = 743909) (by norm_num)
theorem B5948693 : Blo 1762082 5948693 := bbase (se 6 (by rfl) ⟨139422, by rfl⟩ : syracuseStep 5948693 = 278845) (by norm_num)
theorem B3966245 : Blo 1762082 3966245 := bbase (se 4 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 3966245 = 743671) (by norm_num)
theorem B1983793 : Blo 1762082 1983793 := bbase (se 2 (by rfl) ⟨743922, by rfl⟩ : syracuseStep 1983793 = 1487845) (by norm_num)
theorem B1787221 : Blo 1762082 1787221 := bbase (se 12 (by rfl) ⟨654, by rfl⟩ : syracuseStep 1787221 = 1309) (by norm_num)
theorem B1983829 : Blo 1762082 1983829 := bbase (se 12 (by rfl) ⟨726, by rfl⟩ : syracuseStep 1983829 = 1453) (by norm_num)
theorem B2975069 : Blo 1762082 2975069 := bbase (se 3 (by rfl) ⟨557825, by rfl⟩ : syracuseStep 2975069 = 1115651) (by norm_num)
theorem B3966317 : Blo 1762082 3966317 := bbase (se 3 (by rfl) ⟨743684, by rfl⟩ : syracuseStep 3966317 = 1487369) (by norm_num)
theorem B15066485 : Blo 1762082 15066485 := bbase (se 5 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 15066485 = 1412483) (by norm_num)
theorem B1983865 : Blo 1762082 1983865 := bbase (se 2 (by rfl) ⟨743949, by rfl⟩ : syracuseStep 1983865 = 1487899) (by norm_num)
theorem B9528725 : Blo 1762082 9528725 := bbase (se 6 (by rfl) ⟨223329, by rfl⟩ : syracuseStep 9528725 = 446659) (by norm_num)
theorem B1983901 : Blo 1762082 1983901 := bbase (se 3 (by rfl) ⟨371981, by rfl⟩ : syracuseStep 1983901 = 743963) (by norm_num)
theorem B2680229 : Blo 1762082 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B5727653 : Blo 1762082 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B3966389 : Blo 1762082 3966389 := bbase (se 5 (by rfl) ⟨185924, by rfl⟩ : syracuseStep 3966389 = 371849) (by norm_num)
theorem B1983937 : Blo 1762082 1983937 := bbase (se 2 (by rfl) ⟨743976, by rfl⟩ : syracuseStep 1983937 = 1487953) (by norm_num)
theorem B2975197 : Blo 1762082 2975197 := bbase (se 3 (by rfl) ⟨557849, by rfl⟩ : syracuseStep 2975197 = 1115699) (by norm_num)
theorem B1983973 : Blo 1762082 1983973 := bbase (se 4 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 1983973 = 371995) (by norm_num)
theorem B3966461 : Blo 1762082 3966461 := bbase (se 3 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 3966461 = 1487423) (by norm_num)
theorem B1984009 : Blo 1762082 1984009 := bbase (se 2 (by rfl) ⟨744003, by rfl⟩ : syracuseStep 1984009 = 1488007) (by norm_num)
theorem B5359141 : Blo 1762082 5359141 := bbase (se 4 (by rfl) ⟨502419, by rfl⟩ : syracuseStep 5359141 = 1004839) (by norm_num)
theorem B1984045 : Blo 1762082 1984045 := bbase (se 3 (by rfl) ⟨372008, by rfl⟩ : syracuseStep 1984045 = 744017) (by norm_num)
theorem B2975285 : Blo 1762082 2975285 := bbase (se 5 (by rfl) ⟨139466, by rfl⟩ : syracuseStep 2975285 = 278933) (by norm_num)
theorem B3966533 : Blo 1762082 3966533 := bbase (se 4 (by rfl) ⟨371862, by rfl⟩ : syracuseStep 3966533 = 743725) (by norm_num)
theorem B1984081 : Blo 1762082 1984081 := bbase (se 2 (by rfl) ⟨744030, by rfl⟩ : syracuseStep 1984081 = 1488061) (by norm_num)
theorem B1984117 : Blo 1762082 1984117 := bbase (se 5 (by rfl) ⟨93005, by rfl⟩ : syracuseStep 1984117 = 186011) (by norm_num)
theorem B3966605 : Blo 1762082 3966605 := bbase (se 3 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 3966605 = 1487477) (by norm_num)
theorem B4236941 : Blo 1762082 4236941 := bbase (se 3 (by rfl) ⟨794426, by rfl⟩ : syracuseStep 4236941 = 1588853) (by norm_num)
theorem B1984153 : Blo 1762082 1984153 := bbase (se 2 (by rfl) ⟨744057, by rfl⟩ : syracuseStep 1984153 = 1488115) (by norm_num)
theorem B2975413 : Blo 1762082 2975413 := bbase (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) (by norm_num)
theorem B1984189 : Blo 1762082 1984189 := bbase (se 3 (by rfl) ⟨372035, by rfl⟩ : syracuseStep 1984189 = 744071) (by norm_num)
theorem B5949125 : Blo 1762082 5949125 := bbase (se 4 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 5949125 = 1115461) (by norm_num)
theorem B5646037 : Blo 1762082 5646037 := bbase (se 7 (by rfl) ⟨66164, by rfl⟩ : syracuseStep 5646037 = 132329) (by norm_num)
theorem B3966677 : Blo 1762082 3966677 := bbase (se 7 (by rfl) ⟨46484, by rfl⟩ : syracuseStep 3966677 = 92969) (by norm_num)
theorem B1984225 : Blo 1762082 1984225 := bbase (se 2 (by rfl) ⟨744084, by rfl⟩ : syracuseStep 1984225 = 1488169) (by norm_num)
theorem B1984261 : Blo 1762082 1984261 := bbase (se 4 (by rfl) ⟨186024, by rfl⟩ : syracuseStep 1984261 = 372049) (by norm_num)
theorem B2975501 : Blo 1762082 2975501 := bbase (se 3 (by rfl) ⟨557906, by rfl⟩ : syracuseStep 2975501 = 1115813) (by norm_num)
theorem B3966749 : Blo 1762082 3966749 := bbase (se 3 (by rfl) ⟨743765, by rfl⟩ : syracuseStep 3966749 = 1487531) (by norm_num)
theorem B2262817 : Blo 1762082 2262817 := bbase (se 2 (by rfl) ⟨848556, by rfl⟩ : syracuseStep 2262817 = 1697113) (by norm_num)
theorem B1984297 : Blo 1762082 1984297 := bbase (se 2 (by rfl) ⟨744111, by rfl⟩ : syracuseStep 1984297 = 1488223) (by norm_num)
theorem B1984333 : Blo 1762082 1984333 := bbase (se 3 (by rfl) ⟨372062, by rfl⟩ : syracuseStep 1984333 = 744125) (by norm_num)
theorem B3966821 : Blo 1762082 3966821 := bbase (se 4 (by rfl) ⟨371889, by rfl⟩ : syracuseStep 3966821 = 743779) (by norm_num)
theorem B6694757 : Blo 1762082 6694757 := bbase (se 4 (by rfl) ⟨627633, by rfl⟩ : syracuseStep 6694757 = 1255267) (by norm_num)
theorem B1984369 : Blo 1762082 1984369 := bbase (se 2 (by rfl) ⟨744138, by rfl⟩ : syracuseStep 1984369 = 1488277) (by norm_num)
theorem B2975629 : Blo 1762082 2975629 := bbase (se 3 (by rfl) ⟨557930, by rfl⟩ : syracuseStep 2975629 = 1115861) (by norm_num)
theorem B1984405 : Blo 1762082 1984405 := bbase (se 6 (by rfl) ⟨46509, by rfl⟩ : syracuseStep 1984405 = 93019) (by norm_num)
theorem B3966893 : Blo 1762082 3966893 := bbase (se 3 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 3966893 = 1487585) (by norm_num)
theorem B2230193 : Blo 1762082 2230193 := bbase (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) (by norm_num)
theorem B1984441 : Blo 1762082 1984441 := bbase (se 2 (by rfl) ⟨744165, by rfl⟩ : syracuseStep 1984441 = 1488331) (by norm_num)
theorem B1984477 : Blo 1762082 1984477 := bbase (se 3 (by rfl) ⟨372089, by rfl⟩ : syracuseStep 1984477 = 744179) (by norm_num)
theorem B2975717 : Blo 1762082 2975717 := bbase (se 4 (by rfl) ⟨278973, by rfl⟩ : syracuseStep 2975717 = 557947) (by norm_num)
theorem B2230249 : Blo 1762082 2230249 := bbase (se 2 (by rfl) ⟨836343, by rfl⟩ : syracuseStep 2230249 = 1672687) (by norm_num)
theorem B3966965 : Blo 1762082 3966965 := bbase (se 5 (by rfl) ⟨185951, by rfl⟩ : syracuseStep 3966965 = 371903) (by norm_num)
theorem B1984513 : Blo 1762082 1984513 := bbase (se 2 (by rfl) ⟨744192, by rfl⟩ : syracuseStep 1984513 = 1488385) (by norm_num)
theorem B4237325 : Blo 1762082 4237325 := bbase (se 3 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 4237325 = 1588997) (by norm_num)
theorem B1984549 : Blo 1762082 1984549 := bbase (se 4 (by rfl) ⟨186051, by rfl⟩ : syracuseStep 1984549 = 372103) (by norm_num)
theorem B3967037 : Blo 1762082 3967037 := bbase (se 3 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 3967037 = 1487639) (by norm_num)
theorem B4237373 : Blo 1762082 4237373 := bbase (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) (by norm_num)
theorem B4237381 : Blo 1762082 4237381 := bbase (se 4 (by rfl) ⟨397254, by rfl⟩ : syracuseStep 4237381 = 794509) (by norm_num)
theorem B2230345 : Blo 1762082 2230345 := bbase (se 2 (by rfl) ⟨836379, by rfl⟩ : syracuseStep 2230345 = 1672759) (by norm_num)
theorem B1984585 : Blo 1762082 1984585 := bbase (se 2 (by rfl) ⟨744219, by rfl⟩ : syracuseStep 1984585 = 1488439) (by norm_num)
theorem B2975845 : Blo 1762082 2975845 := bbase (se 4 (by rfl) ⟨278985, by rfl⟩ : syracuseStep 2975845 = 557971) (by norm_num)
theorem B5949557 : Blo 1762082 5949557 := bbase (se 5 (by rfl) ⟨278885, by rfl⟩ : syracuseStep 5949557 = 557771) (by norm_num)
theorem B3967109 : Blo 1762082 3967109 := bbase (se 4 (by rfl) ⟨371916, by rfl⟩ : syracuseStep 3967109 = 743833) (by norm_num)
theorem B6695045 : Blo 1762082 6695045 := bbase (se 4 (by rfl) ⟨627660, by rfl⟩ : syracuseStep 6695045 = 1255321) (by norm_num)
theorem B5646485 : Blo 1762082 5646485 := bbase (se 6 (by rfl) ⟨132339, by rfl⟩ : syracuseStep 5646485 = 264679) (by norm_num)
theorem B7530661 : Blo 1762082 7530661 := bbase (se 4 (by rfl) ⟨705999, by rfl⟩ : syracuseStep 7530661 = 1411999) (by norm_num)
theorem B2975933 : Blo 1762082 2975933 := bbase (se 3 (by rfl) ⟨557987, by rfl⟩ : syracuseStep 2975933 = 1115975) (by norm_num)
theorem B3967181 : Blo 1762082 3967181 := bbase (se 3 (by rfl) ⟨743846, by rfl⟩ : syracuseStep 3967181 = 1487693) (by norm_num)
theorem B2509013 : Blo 1762082 2509013 := bbase (se 7 (by rfl) ⟨29402, by rfl⟩ : syracuseStep 2509013 = 58805) (by norm_num)
theorem B2230517 : Blo 1762082 2230517 := bbase (se 5 (by rfl) ⟨104555, by rfl⟩ : syracuseStep 2230517 = 209111) (by norm_num)
theorem B3967253 : Blo 1762082 3967253 := bbase (se 6 (by rfl) ⟨92982, by rfl⟩ : syracuseStep 3967253 = 185965) (by norm_num)
theorem B2509093 : Blo 1762082 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B2230573 : Blo 1762082 2230573 := bbase (se 3 (by rfl) ⟨418232, by rfl⟩ : syracuseStep 2230573 = 836465) (by norm_num)
theorem B8923445 : Blo 1762082 8923445 := bbase (se 5 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 8923445 = 836573) (by norm_num)
theorem B2976061 : Blo 1762082 2976061 := bbase (se 3 (by rfl) ⟨558011, by rfl⟩ : syracuseStep 2976061 = 1116023) (by norm_num)
theorem B8472917 : Blo 1762082 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B10045781 : Blo 1762082 10045781 := bbase (se 10 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 10045781 = 29431) (by norm_num)
theorem B3967325 : Blo 1762082 3967325 := bbase (se 3 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 3967325 = 1487747) (by norm_num)
theorem B2230669 : Blo 1762082 2230669 := bbase (se 3 (by rfl) ⟨418250, by rfl⟩ : syracuseStep 2230669 = 836501) (by norm_num)
theorem B2976149 : Blo 1762082 2976149 := bbase (se 6 (by rfl) ⟨69753, by rfl⟩ : syracuseStep 2976149 = 139507) (by norm_num)
theorem B2509213 : Blo 1762082 2509213 := bbase (se 3 (by rfl) ⟨470477, by rfl⟩ : syracuseStep 2509213 = 940955) (by norm_num)
theorem B3967397 : Blo 1762082 3967397 := bbase (se 4 (by rfl) ⟨371943, by rfl⟩ : syracuseStep 3967397 = 743887) (by norm_num)
theorem B3574253 : Blo 1762082 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B3967469 : Blo 1762082 3967469 := bbase (se 3 (by rfl) ⟨743900, by rfl⟩ : syracuseStep 3967469 = 1487801) (by norm_num)
theorem B2509309 : Blo 1762082 2509309 := bbase (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) (by norm_num)
theorem B2976277 : Blo 1762082 2976277 := bbase (se 6 (by rfl) ⟨69756, by rfl⟩ : syracuseStep 2976277 = 139513) (by norm_num)
theorem B5802533 : Blo 1762082 5802533 := bbase (se 4 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 5802533 = 1087975) (by norm_num)
theorem B5949989 : Blo 1762082 5949989 := bbase (se 4 (by rfl) ⟨557811, by rfl⟩ : syracuseStep 5949989 = 1115623) (by norm_num)
theorem B3967541 : Blo 1762082 3967541 := bbase (se 5 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 3967541 = 371957) (by norm_num)
theorem B2230841 : Blo 1762082 2230841 := bbase (se 2 (by rfl) ⟨836565, by rfl⟩ : syracuseStep 2230841 = 1673131) (by norm_num)
theorem B2976365 : Blo 1762082 2976365 := bbase (se 3 (by rfl) ⟨558068, by rfl⟩ : syracuseStep 2976365 = 1116137) (by norm_num)
theorem B2230897 : Blo 1762082 2230897 := bbase (se 2 (by rfl) ⟨836586, by rfl⟩ : syracuseStep 2230897 = 1673173) (by norm_num)
theorem B3967613 : Blo 1762082 3967613 := bbase (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) (by norm_num)
theorem B3967685 : Blo 1762082 3967685 := bbase (se 4 (by rfl) ⟨371970, by rfl⟩ : syracuseStep 3967685 = 743941) (by norm_num)
theorem B2230993 : Blo 1762082 2230993 := bbase (se 2 (by rfl) ⟨836622, by rfl⟩ : syracuseStep 2230993 = 1673245) (by norm_num)
theorem B2976493 : Blo 1762082 2976493 := bbase (se 3 (by rfl) ⟨558092, by rfl⟩ : syracuseStep 2976493 = 1116185) (by norm_num)
theorem B3967757 : Blo 1762082 3967757 := bbase (se 3 (by rfl) ⟨743954, by rfl⟩ : syracuseStep 3967757 = 1487909) (by norm_num)
theorem B2976581 : Blo 1762082 2976581 := bbase (se 4 (by rfl) ⟨279054, by rfl⟩ : syracuseStep 2976581 = 558109) (by norm_num)
theorem B3345229 : Blo 1762082 3345229 := bbase (se 3 (by rfl) ⟨627230, by rfl⟩ : syracuseStep 3345229 = 1254461) (by norm_num)
theorem B3967829 : Blo 1762082 3967829 := bbase (se 9 (by rfl) ⟨11624, by rfl⟩ : syracuseStep 3967829 = 23249) (by norm_num)
theorem B2231165 : Blo 1762082 2231165 := bbase (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) (by norm_num)
theorem B3967901 : Blo 1762082 3967901 := bbase (se 3 (by rfl) ⟨743981, by rfl⟩ : syracuseStep 3967901 = 1487963) (by norm_num)
theorem B2231221 : Blo 1762082 2231221 := bbase (se 5 (by rfl) ⟨104588, by rfl⟩ : syracuseStep 2231221 = 209177) (by norm_num)
theorem B2976709 : Blo 1762082 2976709 := bbase (se 4 (by rfl) ⟨279066, by rfl⟩ : syracuseStep 2976709 = 558133) (by norm_num)
theorem B5950421 : Blo 1762082 5950421 := bbase (se 7 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 5950421 = 139463) (by norm_num)
theorem B3967973 : Blo 1762082 3967973 := bbase (se 4 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 3967973 = 743995) (by norm_num)
theorem B2509805 : Blo 1762082 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B2231317 : Blo 1762082 2231317 := bbase (se 6 (by rfl) ⟨52296, by rfl⟩ : syracuseStep 2231317 = 104593) (by norm_num)
theorem B2976797 : Blo 1762082 2976797 := bbase (se 3 (by rfl) ⟨558149, by rfl⟩ : syracuseStep 2976797 = 1116299) (by norm_num)
theorem B3968045 : Blo 1762082 3968045 := bbase (se 3 (by rfl) ⟨744008, by rfl⟩ : syracuseStep 3968045 = 1488017) (by norm_num)
theorem B4238381 : Blo 1762082 4238381 := bbase (se 3 (by rfl) ⟨794696, by rfl⟩ : syracuseStep 4238381 = 1589393) (by norm_num)
theorem B3968117 : Blo 1762082 3968117 := bbase (se 5 (by rfl) ⟨186005, by rfl⟩ : syracuseStep 3968117 = 372011) (by norm_num)
theorem B3345533 : Blo 1762082 3345533 := bbase (se 3 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 3345533 = 1254575) (by norm_num)
theorem B3968189 : Blo 1762082 3968189 := bbase (se 3 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 3968189 = 1488071) (by norm_num)
theorem B2231489 : Blo 1762082 2231489 := bbase (se 2 (by rfl) ⟨836808, by rfl⟩ : syracuseStep 2231489 = 1673617) (by norm_num)
theorem B4238573 : Blo 1762082 4238573 := bbase (se 3 (by rfl) ⟨794732, by rfl⟩ : syracuseStep 4238573 = 1589465) (by norm_num)
theorem B2231545 : Blo 1762082 2231545 := bbase (se 2 (by rfl) ⟨836829, by rfl⟩ : syracuseStep 2231545 = 1673659) (by norm_num)
theorem B3968261 : Blo 1762082 3968261 := bbase (se 4 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 3968261 = 744049) (by norm_num)
theorem B6696229 : Blo 1762082 6696229 := bbase (se 4 (by rfl) ⟨627771, by rfl⟩ : syracuseStep 6696229 = 1255543) (by norm_num)
theorem B3968333 : Blo 1762082 3968333 := bbase (se 3 (by rfl) ⟨744062, by rfl⟩ : syracuseStep 3968333 = 1488125) (by norm_num)
theorem B4828501 : Blo 1762082 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B2231641 : Blo 1762082 2231641 := bbase (se 2 (by rfl) ⟨836865, by rfl⟩ : syracuseStep 2231641 = 1673731) (by norm_num)
theorem B2116957 : Blo 1762082 2116957 := bbase (se 3 (by rfl) ⟨396929, by rfl⟩ : syracuseStep 2116957 = 793859) (by norm_num)
theorem B5950853 : Blo 1762082 5950853 := bbase (se 4 (by rfl) ⟨557892, by rfl⟩ : syracuseStep 5950853 = 1115785) (by norm_num)
theorem B3968405 : Blo 1762082 3968405 := bbase (se 6 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 3968405 = 186019) (by norm_num)
theorem B10177973 : Blo 1762082 10177973 := bbase (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) (by norm_num)
theorem B7146949 : Blo 1762082 7146949 := bbase (se 4 (by rfl) ⟨670026, by rfl⟩ : syracuseStep 7146949 = 1340053) (by norm_num)
theorem B3968477 : Blo 1762082 3968477 := bbase (se 3 (by rfl) ⟨744089, by rfl⟩ : syracuseStep 3968477 = 1488179) (by norm_num)
theorem B11292149 : Blo 1762082 11292149 := bbase (se 5 (by rfl) ⟨529319, by rfl⟩ : syracuseStep 11292149 = 1058639) (by norm_num)
theorem B2231813 : Blo 1762082 2231813 := bbase (se 4 (by rfl) ⟨209232, by rfl⟩ : syracuseStep 2231813 = 418465) (by norm_num)
theorem B2510357 : Blo 1762082 2510357 := bbase (se 6 (by rfl) ⟨58836, by rfl⟩ : syracuseStep 2510357 = 117673) (by norm_num)
theorem B3968549 : Blo 1762082 3968549 := bbase (se 4 (by rfl) ⟨372051, by rfl⟩ : syracuseStep 3968549 = 744103) (by norm_num)
theorem B2231869 : Blo 1762082 2231869 := bbase (se 3 (by rfl) ⟨418475, by rfl⟩ : syracuseStep 2231869 = 836951) (by norm_num)
theorem B8924741 : Blo 1762082 8924741 := bbase (se 4 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 8924741 = 1673389) (by norm_num)
theorem B6696533 : Blo 1762082 6696533 := bbase (se 8 (by rfl) ⟨39237, by rfl⟩ : syracuseStep 6696533 = 78475) (by norm_num)
theorem B3968621 : Blo 1762082 3968621 := bbase (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) (by norm_num)
theorem B7532149 : Blo 1762082 7532149 := bbase (se 5 (by rfl) ⟨353069, by rfl⟩ : syracuseStep 7532149 = 706139) (by norm_num)
theorem B7532165 : Blo 1762082 7532165 := bbase (se 4 (by rfl) ⟨706140, by rfl⟩ : syracuseStep 7532165 = 1412281) (by norm_num)
theorem B2231965 : Blo 1762082 2231965 := bbase (se 3 (by rfl) ⟨418493, by rfl⟩ : syracuseStep 2231965 = 836987) (by norm_num)
theorem B3968693 : Blo 1762082 3968693 := bbase (se 5 (by rfl) ⟨186032, by rfl⟩ : syracuseStep 3968693 = 372065) (by norm_num)
theorem B2117341 : Blo 1762082 2117341 := bbase (se 3 (by rfl) ⟨397001, by rfl⟩ : syracuseStep 2117341 = 794003) (by norm_num)
theorem B2117345 : Blo 1762082 2117345 := bbase (se 2 (by rfl) ⟨794004, by rfl⟩ : syracuseStep 2117345 = 1588009) (by norm_num)
theorem B6352613 : Blo 1762082 6352613 := bbase (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) (by norm_num)
theorem B8474341 : Blo 1762082 8474341 := bbase (se 4 (by rfl) ⟨794469, by rfl⟩ : syracuseStep 8474341 = 1588939) (by norm_num)
theorem B4460285 : Blo 1762082 4460285 := bbase (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) (by norm_num)
theorem B3968765 : Blo 1762082 3968765 := bbase (se 3 (by rfl) ⟨744143, by rfl⟩ : syracuseStep 3968765 = 1488287) (by norm_num)
theorem B5951285 : Blo 1762082 5951285 := bbase (se 5 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 5951285 = 557933) (by norm_num)
theorem B3968837 : Blo 1762082 3968837 := bbase (se 4 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 3968837 = 744157) (by norm_num)
theorem B2232137 : Blo 1762082 2232137 := bbase (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) (by norm_num)
theorem B3346285 : Blo 1762082 3346285 := bbase (se 3 (by rfl) ⟨627428, by rfl⟩ : syracuseStep 3346285 = 1254857) (by norm_num)
theorem B6352757 : Blo 1762082 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B2232193 : Blo 1762082 2232193 := bbase (se 2 (by rfl) ⟨837072, by rfl⟩ : syracuseStep 2232193 = 1674145) (by norm_num)
theorem B3968909 : Blo 1762082 3968909 := bbase (se 3 (by rfl) ⟨744170, by rfl⟩ : syracuseStep 3968909 = 1488341) (by norm_num)
theorem B6115285 : Blo 1762082 6115285 := bbase (se 7 (by rfl) ⟨71663, by rfl⟩ : syracuseStep 6115285 = 143327) (by norm_num)
theorem B3968981 : Blo 1762082 3968981 := bbase (se 7 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 3968981 = 93023) (by norm_num)
theorem B2232289 : Blo 1762082 2232289 := bbase (se 2 (by rfl) ⟨837108, by rfl⟩ : syracuseStep 2232289 = 1674217) (by norm_num)
theorem B3346429 : Blo 1762082 3346429 := bbase (se 3 (by rfl) ⟨627455, by rfl⟩ : syracuseStep 3346429 = 1254911) (by norm_num)
theorem B3764237 : Blo 1762082 3764237 := bbase (se 3 (by rfl) ⟨705794, by rfl⟩ : syracuseStep 3764237 = 1411589) (by norm_num)
theorem B3969053 : Blo 1762082 3969053 := bbase (se 3 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 3969053 = 1488395) (by norm_num)
theorem B4460629 : Blo 1762082 4460629 := bbase (se 8 (by rfl) ⟨26136, by rfl⟩ : syracuseStep 4460629 = 52273) (by norm_num)
theorem B3969125 : Blo 1762082 3969125 := bbase (se 4 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 3969125 = 744211) (by norm_num)
theorem B2117749 : Blo 1762082 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B7245941 : Blo 1762082 7245941 := bbase (se 5 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 7245941 = 679307) (by norm_num)
theorem B2232461 : Blo 1762082 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B3346589 : Blo 1762082 3346589 := bbase (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) (by norm_num)
theorem B4460741 : Blo 1762082 4460741 := bbase (se 4 (by rfl) ⟨418194, by rfl⟩ : syracuseStep 4460741 = 836389) (by norm_num)
theorem B2232517 : Blo 1762082 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B5951717 : Blo 1762082 5951717 := bbase (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) (by norm_num)
theorem B3764477 : Blo 1762082 3764477 := bbase (se 3 (by rfl) ⟨705839, by rfl⟩ : syracuseStep 3764477 = 1411679) (by norm_num)
theorem B2511109 : Blo 1762082 2511109 := bbase (se 4 (by rfl) ⟨235416, by rfl⟩ : syracuseStep 2511109 = 470833) (by norm_num)
theorem B2232613 : Blo 1762082 2232613 := bbase (se 4 (by rfl) ⟨209307, by rfl⟩ : syracuseStep 2232613 = 418615) (by norm_num)
theorem B3346733 : Blo 1762082 3346733 := bbase (se 3 (by rfl) ⟨627512, by rfl⟩ : syracuseStep 3346733 = 1255025) (by norm_num)
theorem B85766485 : Blo 1762082 85766485 := bbase (se 10 (by rfl) ⟨125634, by rfl⟩ : syracuseStep 85766485 = 251269) (by norm_num)
theorem B5648741 : Blo 1762082 5648741 := bbase (se 4 (by rfl) ⟨529569, by rfl⟩ : syracuseStep 5648741 = 1059139) (by norm_num)
theorem B4460933 : Blo 1762082 4460933 := bbase (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) (by norm_num)
theorem B2822717 : Blo 1762082 2822717 := bbase (se 3 (by rfl) ⟨529259, by rfl⟩ : syracuseStep 2822717 = 1058519) (by norm_num)
theorem B3347021 : Blo 1762082 3347021 := bbase (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) (by norm_num)
theorem B2863717 : Blo 1762082 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B5952149 : Blo 1762082 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B2822845 : Blo 1762082 2822845 := bbase (se 3 (by rfl) ⟨529283, by rfl⟩ : syracuseStep 2822845 = 1058567) (by norm_num)
theorem B4461277 : Blo 1762082 4461277 := bbase (se 3 (by rfl) ⟨836489, by rfl⟩ : syracuseStep 4461277 = 1672979) (by norm_num)
theorem B3347173 : Blo 1762082 3347173 := bbase (se 4 (by rfl) ⟨313797, by rfl⟩ : syracuseStep 3347173 = 627595) (by norm_num)
theorem B3764981 : Blo 1762082 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B3764989 : Blo 1762082 3764989 := bbase (se 3 (by rfl) ⟨705935, by rfl⟩ : syracuseStep 3764989 = 1411871) (by norm_num)
theorem B4461389 : Blo 1762082 4461389 := bbase (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) (by norm_num)
theorem B8926037 : Blo 1762082 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B4461581 : Blo 1762082 4461581 := bbase (se 3 (by rfl) ⟨836546, by rfl⟩ : syracuseStep 4461581 = 1673093) (by norm_num)
theorem B3347477 : Blo 1762082 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B4830245 : Blo 1762082 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B12710965 : Blo 1762082 12710965 := bbase (se 5 (by rfl) ⟨595826, by rfl⟩ : syracuseStep 12710965 = 1191653) (by norm_num)
theorem B5952581 : Blo 1762082 5952581 := bbase (se 4 (by rfl) ⟨558054, by rfl⟩ : syracuseStep 5952581 = 1116109) (by norm_num)
theorem B2643125 : Blo 1762082 2643125 := bbase (se 5 (by rfl) ⟨123896, by rfl⟩ : syracuseStep 2643125 = 247793) (by norm_num)
theorem B2643149 : Blo 1762082 2643149 := bbase (se 3 (by rfl) ⟨495590, by rfl⟩ : syracuseStep 2643149 = 991181) (by norm_num)
theorem B2643173 : Blo 1762082 2643173 := bbase (se 4 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 2643173 = 495595) (by norm_num)
theorem B2643197 : Blo 1762082 2643197 := bbase (se 3 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 2643197 = 991199) (by norm_num)
theorem B2643221 : Blo 1762082 2643221 := bbase (se 6 (by rfl) ⟨61950, by rfl⟩ : syracuseStep 2643221 = 123901) (by norm_num)
theorem B2643245 : Blo 1762082 2643245 := bbase (se 3 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 2643245 = 991217) (by norm_num)
theorem B12711221 : Blo 1762082 12711221 := bbase (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) (by norm_num)
theorem B2643269 : Blo 1762082 2643269 := bbase (se 4 (by rfl) ⟨247806, by rfl⟩ : syracuseStep 2643269 = 495613) (by norm_num)
theorem B2643293 : Blo 1762082 2643293 := bbase (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) (by norm_num)
theorem B4461925 : Blo 1762082 4461925 := bbase (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) (by norm_num)
theorem B2643317 : Blo 1762082 2643317 := bbase (se 5 (by rfl) ⟨123905, by rfl⟩ : syracuseStep 2643317 = 247811) (by norm_num)
theorem B2643341 : Blo 1762082 2643341 := bbase (se 3 (by rfl) ⟨495626, by rfl⟩ : syracuseStep 2643341 = 991253) (by norm_num)
theorem B5019029 : Blo 1762082 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B6034837 : Blo 1762082 6034837 := bbase (se 6 (by rfl) ⟨141441, by rfl⟩ : syracuseStep 6034837 = 282883) (by norm_num)
theorem B2643365 : Blo 1762082 2643365 := bbase (se 4 (by rfl) ⟨247815, by rfl⟩ : syracuseStep 2643365 = 495631) (by norm_num)
theorem B3175861 : Blo 1762082 3175861 := bbase (se 5 (by rfl) ⟨148868, by rfl⟩ : syracuseStep 3175861 = 297737) (by norm_num)
theorem B11302325 : Blo 1762082 11302325 := bbase (se 5 (by rfl) ⟨529796, by rfl⟩ : syracuseStep 11302325 = 1059593) (by norm_num)
theorem B2643389 : Blo 1762082 2643389 := bbase (se 3 (by rfl) ⟨495635, by rfl⟩ : syracuseStep 2643389 = 991271) (by norm_num)
theorem B2643413 : Blo 1762082 2643413 := bbase (se 7 (by rfl) ⟨30977, by rfl⟩ : syracuseStep 2643413 = 61955) (by norm_num)
theorem B4462037 : Blo 1762082 4462037 := bbase (se 7 (by rfl) ⟨52289, by rfl⟩ : syracuseStep 4462037 = 104579) (by norm_num)
theorem B2119133 : Blo 1762082 2119133 := bbase (se 3 (by rfl) ⟨397337, by rfl⟩ : syracuseStep 2119133 = 794675) (by norm_num)
theorem B2823653 : Blo 1762082 2823653 := bbase (se 4 (by rfl) ⟨264717, by rfl⟩ : syracuseStep 2823653 = 529435) (by norm_num)
theorem B2643437 : Blo 1762082 2643437 := bbase (se 3 (by rfl) ⟨495644, by rfl⟩ : syracuseStep 2643437 = 991289) (by norm_num)
theorem B5953013 : Blo 1762082 5953013 := bbase (se 5 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 5953013 = 558095) (by norm_num)
theorem B2643461 : Blo 1762082 2643461 := bbase (se 4 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 2643461 = 495649) (by norm_num)
theorem B2643485 : Blo 1762082 2643485 := bbase (se 3 (by rfl) ⟨495653, by rfl⟩ : syracuseStep 2643485 = 991307) (by norm_num)
theorem B2643509 : Blo 1762082 2643509 := bbase (se 5 (by rfl) ⟨123914, by rfl⟩ : syracuseStep 2643509 = 247829) (by norm_num)
theorem B2643533 : Blo 1762082 2643533 := bbase (se 3 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 2643533 = 991325) (by norm_num)
theorem B2643557 : Blo 1762082 2643557 := bbase (se 4 (by rfl) ⟨247833, by rfl⟩ : syracuseStep 2643557 = 495667) (by norm_num)
theorem B3487349 : Blo 1762082 3487349 := bbase (se 5 (by rfl) ⟨163469, by rfl⟩ : syracuseStep 3487349 = 326939) (by norm_num)
theorem B2643581 : Blo 1762082 2643581 := bbase (se 3 (by rfl) ⟨495671, by rfl⟩ : syracuseStep 2643581 = 991343) (by norm_num)
theorem B2545277 : Blo 1762082 2545277 := bbase (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) (by norm_num)
theorem B2643605 : Blo 1762082 2643605 := bbase (se 6 (by rfl) ⟨61959, by rfl⟩ : syracuseStep 2643605 = 123919) (by norm_num)
theorem B4019861 : Blo 1762082 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B4462229 : Blo 1762082 4462229 := bbase (se 6 (by rfl) ⟨104583, by rfl⟩ : syracuseStep 4462229 = 209167) (by norm_num)
theorem B2643629 : Blo 1762082 2643629 := bbase (se 3 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 2643629 = 991361) (by norm_num)
theorem B2643653 : Blo 1762082 2643653 := bbase (se 4 (by rfl) ⟨247842, by rfl⟩ : syracuseStep 2643653 = 495685) (by norm_num)
theorem B2643677 : Blo 1762082 2643677 := bbase (se 3 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 2643677 = 991379) (by norm_num)
theorem B2643701 : Blo 1762082 2643701 := bbase (se 5 (by rfl) ⟨123923, by rfl⟩ : syracuseStep 2643701 = 247847) (by norm_num)
theorem B2823941 : Blo 1762082 2823941 := bbase (se 4 (by rfl) ⟨264744, by rfl⟩ : syracuseStep 2823941 = 529489) (by norm_num)
theorem B3348229 : Blo 1762082 3348229 := bbase (se 4 (by rfl) ⟨313896, by rfl⟩ : syracuseStep 3348229 = 627793) (by norm_num)
theorem B2643725 : Blo 1762082 2643725 := bbase (se 3 (by rfl) ⟨495698, by rfl⟩ : syracuseStep 2643725 = 991397) (by norm_num)
theorem B2643749 : Blo 1762082 2643749 := bbase (se 4 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 2643749 = 495703) (by norm_num)
theorem B2643773 : Blo 1762082 2643773 := bbase (se 3 (by rfl) ⟨495707, by rfl⟩ : syracuseStep 2643773 = 991415) (by norm_num)
theorem B2643797 : Blo 1762082 2643797 := bbase (se 9 (by rfl) ⟨7745, by rfl⟩ : syracuseStep 2643797 = 15491) (by norm_num)
theorem B7534421 : Blo 1762082 7534421 := bbase (se 9 (by rfl) ⟨22073, by rfl⟩ : syracuseStep 7534421 = 44147) (by norm_num)
theorem B3766117 : Blo 1762082 3766117 := bbase (se 4 (by rfl) ⟨353073, by rfl⟩ : syracuseStep 3766117 = 706147) (by norm_num)
theorem B3307373 : Blo 1762082 3307373 := bbase (se 3 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 3307373 = 1240265) (by norm_num)
theorem B1881965 : Blo 1762082 1881965 := bbase (se 3 (by rfl) ⟨352868, by rfl⟩ : syracuseStep 1881965 = 705737) (by norm_num)
theorem B2643821 : Blo 1762082 2643821 := bbase (se 3 (by rfl) ⟨495716, by rfl⟩ : syracuseStep 2643821 = 991433) (by norm_num)
theorem B2643845 : Blo 1762082 2643845 := bbase (se 4 (by rfl) ⟨247860, by rfl⟩ : syracuseStep 2643845 = 495721) (by norm_num)
theorem B3348373 : Blo 1762082 3348373 := bbase (se 6 (by rfl) ⟨78477, by rfl⟩ : syracuseStep 3348373 = 156955) (by norm_num)
theorem B2643869 : Blo 1762082 2643869 := bbase (se 3 (by rfl) ⟨495725, by rfl⟩ : syracuseStep 2643869 = 991451) (by norm_num)
theorem B5953445 : Blo 1762082 5953445 := bbase (se 4 (by rfl) ⟨558135, by rfl⟩ : syracuseStep 5953445 = 1116271) (by norm_num)
theorem B2643893 : Blo 1762082 2643893 := bbase (se 5 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 2643893 = 247865) (by norm_num)
theorem B2643917 : Blo 1762082 2643917 := bbase (se 3 (by rfl) ⟨495734, by rfl⟩ : syracuseStep 2643917 = 991469) (by norm_num)
theorem B2381797 : Blo 1762082 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B2643941 : Blo 1762082 2643941 := bbase (se 4 (by rfl) ⟨247869, by rfl⟩ : syracuseStep 2643941 = 495739) (by norm_num)
theorem B4462573 : Blo 1762082 4462573 := bbase (se 3 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 4462573 = 1673465) (by norm_num)
theorem B2643965 : Blo 1762082 2643965 := bbase (se 3 (by rfl) ⟨495743, by rfl⟩ : syracuseStep 2643965 = 991487) (by norm_num)
theorem B12056597 : Blo 1762082 12056597 := bbase (se 6 (by rfl) ⟨282576, by rfl⟩ : syracuseStep 12056597 = 565153) (by norm_num)
theorem B2643989 : Blo 1762082 2643989 := bbase (se 6 (by rfl) ⟨61968, by rfl⟩ : syracuseStep 2643989 = 123937) (by norm_num)
theorem B1882153 : Blo 1762082 1882153 := bbase (se 2 (by rfl) ⟨705807, by rfl⟩ : syracuseStep 1882153 = 1411615) (by norm_num)
theorem B2644013 : Blo 1762082 2644013 := bbase (se 3 (by rfl) ⟨495752, by rfl⟩ : syracuseStep 2644013 = 991505) (by norm_num)
theorem B6690869 : Blo 1762082 6690869 := bbase (se 5 (by rfl) ⟨313634, by rfl⟩ : syracuseStep 6690869 = 627269) (by norm_num)
theorem B3348533 : Blo 1762082 3348533 := bbase (se 5 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 3348533 = 313925) (by norm_num)
theorem B2644037 : Blo 1762082 2644037 := bbase (se 4 (by rfl) ⟨247878, by rfl⟩ : syracuseStep 2644037 = 495757) (by norm_num)
theorem B12064853 : Blo 1762082 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B2644061 : Blo 1762082 2644061 := bbase (se 3 (by rfl) ⟨495761, by rfl⟩ : syracuseStep 2644061 = 991523) (by norm_num)
theorem B4462685 : Blo 1762082 4462685 := bbase (se 3 (by rfl) ⟨836753, by rfl⟩ : syracuseStep 4462685 = 1673507) (by norm_num)
theorem B8927333 : Blo 1762082 8927333 := bbase (se 4 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 8927333 = 1673875) (by norm_num)
theorem B2644085 : Blo 1762082 2644085 := bbase (se 5 (by rfl) ⟨123941, by rfl⟩ : syracuseStep 2644085 = 247883) (by norm_num)
theorem B2644109 : Blo 1762082 2644109 := bbase (se 3 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 2644109 = 991541) (by norm_num)
theorem B2644133 : Blo 1762082 2644133 := bbase (se 4 (by rfl) ⟨247887, by rfl⟩ : syracuseStep 2644133 = 495775) (by norm_num)
theorem B2824357 : Blo 1762082 2824357 := bbase (se 4 (by rfl) ⟨264783, by rfl⟩ : syracuseStep 2824357 = 529567) (by norm_num)
theorem B2644157 : Blo 1762082 2644157 := bbase (se 3 (by rfl) ⟨495779, by rfl⟩ : syracuseStep 2644157 = 991559) (by norm_num)
theorem B9173189 : Blo 1762082 9173189 := bbase (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) (by norm_num)
theorem B3348677 : Blo 1762082 3348677 := bbase (se 4 (by rfl) ⟨313938, by rfl⟩ : syracuseStep 3348677 = 627877) (by norm_num)
theorem B2644181 : Blo 1762082 2644181 := bbase (se 7 (by rfl) ⟨30986, by rfl⟩ : syracuseStep 2644181 = 61973) (by norm_num)
theorem B13760725 : Blo 1762082 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B3766493 : Blo 1762082 3766493 := bbase (se 3 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 3766493 = 1412435) (by norm_num)
theorem B2644205 : Blo 1762082 2644205 := bbase (se 3 (by rfl) ⟨495788, by rfl⟩ : syracuseStep 2644205 = 991577) (by norm_num)
theorem B8583413 : Blo 1762082 8583413 := bbase (se 5 (by rfl) ⟨402347, by rfl⟩ : syracuseStep 8583413 = 804695) (by norm_num)
theorem B2644229 : Blo 1762082 2644229 := bbase (se 4 (by rfl) ⟨247896, by rfl⟩ : syracuseStep 2644229 = 495793) (by norm_num)
theorem B2644253 : Blo 1762082 2644253 := bbase (se 3 (by rfl) ⟨495797, by rfl⟩ : syracuseStep 2644253 = 991595) (by norm_num)
theorem B4462877 : Blo 1762082 4462877 := bbase (se 3 (by rfl) ⟨836789, by rfl⟩ : syracuseStep 4462877 = 1673579) (by norm_num)
theorem B2644277 : Blo 1762082 2644277 := bbase (se 5 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 2644277 = 247901) (by norm_num)
theorem B2644301 : Blo 1762082 2644301 := bbase (se 3 (by rfl) ⟨495806, by rfl⟩ : syracuseStep 2644301 = 991613) (by norm_num)
theorem B6691157 : Blo 1762082 6691157 := bbase (se 10 (by rfl) ⟨9801, by rfl⟩ : syracuseStep 6691157 = 19603) (by norm_num)
theorem B2644325 : Blo 1762082 2644325 := bbase (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) (by norm_num)
theorem B2644349 : Blo 1762082 2644349 := bbase (se 3 (by rfl) ⟨495815, by rfl⟩ : syracuseStep 2644349 = 991631) (by norm_num)
theorem B2644373 : Blo 1762082 2644373 := bbase (se 6 (by rfl) ⟨61977, by rfl⟩ : syracuseStep 2644373 = 123955) (by norm_num)
theorem B2644397 : Blo 1762082 2644397 := bbase (se 3 (by rfl) ⟨495824, by rfl⟩ : syracuseStep 2644397 = 991649) (by norm_num)
theorem B6355381 : Blo 1762082 6355381 := bbase (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) (by norm_num)
theorem B2644421 : Blo 1762082 2644421 := bbase (se 4 (by rfl) ⟨247914, by rfl⟩ : syracuseStep 2644421 = 495829) (by norm_num)
theorem B15063509 : Blo 1762082 15063509 := bbase (se 7 (by rfl) ⟨176525, by rfl⟩ : syracuseStep 15063509 = 353051) (by norm_num)
theorem B2644445 : Blo 1762082 2644445 := bbase (se 3 (by rfl) ⟨495833, by rfl⟩ : syracuseStep 2644445 = 991667) (by norm_num)
theorem B3348965 : Blo 1762082 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B2644469 : Blo 1762082 2644469 := bbase (se 5 (by rfl) ⟨123959, by rfl⟩ : syracuseStep 2644469 = 247919) (by norm_num)
theorem B2644493 : Blo 1762082 2644493 := bbase (se 3 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 2644493 = 991685) (by norm_num)
theorem B2644517 : Blo 1762082 2644517 := bbase (se 4 (by rfl) ⟨247923, by rfl⟩ : syracuseStep 2644517 = 495847) (by norm_num)
theorem B5020213 : Blo 1762082 5020213 := bbase (se 5 (by rfl) ⟨235322, by rfl⟩ : syracuseStep 5020213 = 470645) (by norm_num)
theorem B2644541 : Blo 1762082 2644541 := bbase (se 3 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 2644541 = 991703) (by norm_num)
theorem B6355525 : Blo 1762082 6355525 := bbase (se 4 (by rfl) ⟨595830, by rfl⟩ : syracuseStep 6355525 = 1191661) (by norm_num)
theorem B2644565 : Blo 1762082 2644565 := bbase (se 8 (by rfl) ⟨15495, by rfl⟩ : syracuseStep 2644565 = 30991) (by norm_num)
theorem B2644589 : Blo 1762082 2644589 := bbase (se 3 (by rfl) ⟨495860, by rfl⟩ : syracuseStep 2644589 = 991721) (by norm_num)
theorem B4233845 : Blo 1762082 4233845 := bbase (se 5 (by rfl) ⟨198461, by rfl⟩ : syracuseStep 4233845 = 396923) (by norm_num)
theorem B4463221 : Blo 1762082 4463221 := bbase (se 5 (by rfl) ⟨209213, by rfl⟩ : syracuseStep 4463221 = 418427) (by norm_num)
theorem B3177085 : Blo 1762082 3177085 := bbase (se 3 (by rfl) ⟨595703, by rfl⟩ : syracuseStep 3177085 = 1191407) (by norm_num)
theorem B2644613 : Blo 1762082 2644613 := bbase (se 4 (by rfl) ⟨247932, by rfl⟩ : syracuseStep 2644613 = 495865) (by norm_num)
theorem B2644637 : Blo 1762082 2644637 := bbase (se 3 (by rfl) ⟨495869, by rfl⟩ : syracuseStep 2644637 = 991739) (by norm_num)
theorem B2644661 : Blo 1762082 2644661 := bbase (se 5 (by rfl) ⟨123968, by rfl⟩ : syracuseStep 2644661 = 247937) (by norm_num)
theorem B2644685 : Blo 1762082 2644685 := bbase (se 3 (by rfl) ⟨495878, by rfl⟩ : syracuseStep 2644685 = 991757) (by norm_num)
theorem B5020373 : Blo 1762082 5020373 := bbase (se 7 (by rfl) ⟨58832, by rfl⟩ : syracuseStep 5020373 = 117665) (by norm_num)
theorem B2644709 : Blo 1762082 2644709 := bbase (se 4 (by rfl) ⟨247941, by rfl⟩ : syracuseStep 2644709 = 495883) (by norm_num)
theorem B4463333 : Blo 1762082 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B2644733 : Blo 1762082 2644733 := bbase (se 3 (by rfl) ⟨495887, by rfl⟩ : syracuseStep 2644733 = 991775) (by norm_num)
theorem B2644757 : Blo 1762082 2644757 := bbase (se 6 (by rfl) ⟨61986, by rfl⟩ : syracuseStep 2644757 = 123973) (by norm_num)
theorem B23214869 : Blo 1762082 23214869 := bbase (se 6 (by rfl) ⟨544098, by rfl⟩ : syracuseStep 23214869 = 1088197) (by norm_num)
theorem B3177245 : Blo 1762082 3177245 := bbase (se 3 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 3177245 = 1191467) (by norm_num)
theorem B2644781 : Blo 1762082 2644781 := bbase (se 3 (by rfl) ⟨495896, by rfl⟩ : syracuseStep 2644781 = 991793) (by norm_num)
theorem B2644805 : Blo 1762082 2644805 := bbase (se 4 (by rfl) ⟨247950, by rfl⟩ : syracuseStep 2644805 = 495901) (by norm_num)
theorem B32168789 : Blo 1762082 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B2644829 : Blo 1762082 2644829 := bbase (se 3 (by rfl) ⟨495905, by rfl⟩ : syracuseStep 2644829 = 991811) (by norm_num)
theorem B1882973 : Blo 1762082 1882973 := bbase (se 3 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 1882973 = 706115) (by norm_num)
theorem B2644853 : Blo 1762082 2644853 := bbase (se 5 (by rfl) ⟨123977, by rfl⟩ : syracuseStep 2644853 = 247955) (by norm_num)
theorem B2644877 : Blo 1762082 2644877 := bbase (se 3 (by rfl) ⟨495914, by rfl⟩ : syracuseStep 2644877 = 991829) (by norm_num)
theorem B2644901 : Blo 1762082 2644901 := bbase (se 4 (by rfl) ⟨247959, by rfl⟩ : syracuseStep 2644901 = 495919) (by norm_num)
theorem B4463525 : Blo 1762082 4463525 := bbase (se 4 (by rfl) ⟨418455, by rfl⟩ : syracuseStep 4463525 = 836911) (by norm_num)
theorem B2644925 : Blo 1762082 2644925 := bbase (se 3 (by rfl) ⟨495923, by rfl⟩ : syracuseStep 2644925 = 991847) (by norm_num)
theorem B5020613 : Blo 1762082 5020613 := bbase (se 4 (by rfl) ⟨470682, by rfl⟩ : syracuseStep 5020613 = 941365) (by norm_num)
theorem B2644949 : Blo 1762082 2644949 := bbase (se 7 (by rfl) ⟨30995, by rfl⟩ : syracuseStep 2644949 = 61991) (by norm_num)
theorem B2644973 : Blo 1762082 2644973 := bbase (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) (by norm_num)
theorem B2644997 : Blo 1762082 2644997 := bbase (se 4 (by rfl) ⟨247968, by rfl⟩ : syracuseStep 2644997 = 495937) (by norm_num)
theorem B2645021 : Blo 1762082 2645021 := bbase (se 3 (by rfl) ⟨495941, by rfl⟩ : syracuseStep 2645021 = 991883) (by norm_num)
theorem B2645045 : Blo 1762082 2645045 := bbase (se 5 (by rfl) ⟨123986, by rfl⟩ : syracuseStep 2645045 = 247973) (by norm_num)
theorem B2645069 : Blo 1762082 2645069 := bbase (se 3 (by rfl) ⟨495950, by rfl⟩ : syracuseStep 2645069 = 991901) (by norm_num)
theorem B2825293 : Blo 1762082 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B6200405 : Blo 1762082 6200405 := bbase (se 8 (by rfl) ⟨36330, by rfl⟩ : syracuseStep 6200405 = 72661) (by norm_num)
theorem B2645093 : Blo 1762082 2645093 := bbase (se 4 (by rfl) ⟨247977, by rfl⟩ : syracuseStep 2645093 = 495955) (by norm_num)
theorem B2645117 : Blo 1762082 2645117 := bbase (se 3 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 2645117 = 991919) (by norm_num)
theorem B5020805 : Blo 1762082 5020805 := bbase (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) (by norm_num)
theorem B2645141 : Blo 1762082 2645141 := bbase (se 6 (by rfl) ⟨61995, by rfl⟩ : syracuseStep 2645141 = 123991) (by norm_num)
theorem B2645165 : Blo 1762082 2645165 := bbase (se 3 (by rfl) ⟨495968, by rfl⟩ : syracuseStep 2645165 = 991937) (by norm_num)
theorem B2645189 : Blo 1762082 2645189 := bbase (se 4 (by rfl) ⟨247986, by rfl⟩ : syracuseStep 2645189 = 495973) (by norm_num)
theorem B2645213 : Blo 1762082 2645213 := bbase (se 3 (by rfl) ⟨495977, by rfl⟩ : syracuseStep 2645213 = 991955) (by norm_num)
theorem B8043749 : Blo 1762082 8043749 := bbase (se 4 (by rfl) ⟨754101, by rfl⟩ : syracuseStep 8043749 = 1508203) (by norm_num)
theorem B10042613 : Blo 1762082 10042613 := bbase (se 5 (by rfl) ⟨470747, by rfl⟩ : syracuseStep 10042613 = 941495) (by norm_num)
theorem B2645237 : Blo 1762082 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B4463869 : Blo 1762082 4463869 := bbase (se 3 (by rfl) ⟨836975, by rfl⟩ : syracuseStep 4463869 = 1673951) (by norm_num)
theorem B2645261 : Blo 1762082 2645261 := bbase (se 3 (by rfl) ⟨495986, by rfl⟩ : syracuseStep 2645261 = 991973) (by norm_num)
theorem B1883417 : Blo 1762082 1883417 := bbase (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) (by norm_num)
theorem B2645285 : Blo 1762082 2645285 := bbase (se 4 (by rfl) ⟨247995, by rfl⟩ : syracuseStep 2645285 = 495991) (by norm_num)
theorem B2645309 : Blo 1762082 2645309 := bbase (se 3 (by rfl) ⟨495995, by rfl⟩ : syracuseStep 2645309 = 991991) (by norm_num)
theorem B2645333 : Blo 1762082 2645333 := bbase (se 11 (by rfl) ⟨1937, by rfl⟩ : syracuseStep 2645333 = 3875) (by norm_num)
theorem B4021613 : Blo 1762082 4021613 := bbase (se 3 (by rfl) ⟨754052, by rfl⟩ : syracuseStep 4021613 = 1508105) (by norm_num)
theorem B4463981 : Blo 1762082 4463981 := bbase (se 3 (by rfl) ⟨836996, by rfl⟩ : syracuseStep 4463981 = 1673993) (by norm_num)
theorem B2645357 : Blo 1762082 2645357 := bbase (se 3 (by rfl) ⟨496004, by rfl⟩ : syracuseStep 2645357 = 992009) (by norm_num)
theorem B4234613 : Blo 1762082 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B8928629 : Blo 1762082 8928629 := bbase (se 5 (by rfl) ⟨418529, by rfl⟩ : syracuseStep 8928629 = 837059) (by norm_num)
theorem B2645381 : Blo 1762082 2645381 := bbase (se 4 (by rfl) ⟨248004, by rfl⟩ : syracuseStep 2645381 = 496009) (by norm_num)
theorem B2645405 : Blo 1762082 2645405 := bbase (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) (by norm_num)
theorem B2645429 : Blo 1762082 2645429 := bbase (se 5 (by rfl) ⟨124004, by rfl⟩ : syracuseStep 2645429 = 248009) (by norm_num)
theorem B2645453 : Blo 1762082 2645453 := bbase (se 3 (by rfl) ⟨496022, by rfl⟩ : syracuseStep 2645453 = 992045) (by norm_num)
theorem B2645477 : Blo 1762082 2645477 := bbase (se 4 (by rfl) ⟨248013, by rfl⟩ : syracuseStep 2645477 = 496027) (by norm_num)
theorem B6692341 : Blo 1762082 6692341 := bbase (se 5 (by rfl) ⟨313703, by rfl⟩ : syracuseStep 6692341 = 627407) (by norm_num)
theorem B2645501 : Blo 1762082 2645501 := bbase (se 3 (by rfl) ⟨496031, by rfl⟩ : syracuseStep 2645501 = 992063) (by norm_num)
theorem B1883665 : Blo 1762082 1883665 := bbase (se 2 (by rfl) ⟨706374, by rfl⟩ : syracuseStep 1883665 = 1412749) (by norm_num)
theorem B2645525 : Blo 1762082 2645525 := bbase (se 6 (by rfl) ⟨62004, by rfl⟩ : syracuseStep 2645525 = 124009) (by norm_num)
theorem B4464173 : Blo 1762082 4464173 := bbase (se 3 (by rfl) ⟨837032, by rfl⟩ : syracuseStep 4464173 = 1674065) (by norm_num)
theorem B2645549 : Blo 1762082 2645549 := bbase (se 3 (by rfl) ⟨496040, by rfl⟩ : syracuseStep 2645549 = 992081) (by norm_num)
theorem B2645573 : Blo 1762082 2645573 := bbase (se 4 (by rfl) ⟨248022, by rfl⟩ : syracuseStep 2645573 = 496045) (by norm_num)
theorem B2645597 : Blo 1762082 2645597 := bbase (se 3 (by rfl) ⟨496049, by rfl⟩ : syracuseStep 2645597 = 992099) (by norm_num)
theorem B9051749 : Blo 1762082 9051749 := bbase (se 4 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 9051749 = 1697203) (by norm_num)
theorem B2645621 : Blo 1762082 2645621 := bbase (se 5 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 2645621 = 248027) (by norm_num)
theorem B2645645 : Blo 1762082 2645645 := bbase (se 3 (by rfl) ⟨496058, by rfl⟩ : syracuseStep 2645645 = 992117) (by norm_num)
theorem B14294677 : Blo 1762082 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B2645669 : Blo 1762082 2645669 := bbase (se 4 (by rfl) ⟨248031, by rfl⟩ : syracuseStep 2645669 = 496063) (by norm_num)
theorem B2645693 : Blo 1762082 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B7528133 : Blo 1762082 7528133 := bbase (se 4 (by rfl) ⟨705762, by rfl⟩ : syracuseStep 7528133 = 1411525) (by norm_num)
theorem B2645717 : Blo 1762082 2645717 := bbase (se 7 (by rfl) ⟨31004, by rfl⟩ : syracuseStep 2645717 = 62009) (by norm_num)
theorem B2645741 : Blo 1762082 2645741 := bbase (se 3 (by rfl) ⟨496076, by rfl⟩ : syracuseStep 2645741 = 992153) (by norm_num)
theorem B2645765 : Blo 1762082 2645765 := bbase (se 4 (by rfl) ⟨248040, by rfl⟩ : syracuseStep 2645765 = 496081) (by norm_num)
theorem B8920853 : Blo 1762082 8920853 := bbase (se 6 (by rfl) ⟨209082, by rfl⟩ : syracuseStep 8920853 = 418165) (by norm_num)
theorem B2645789 : Blo 1762082 2645789 := bbase (se 3 (by rfl) ⟨496085, by rfl⟩ : syracuseStep 2645789 = 992171) (by norm_num)
theorem B6692645 : Blo 1762082 6692645 := bbase (se 4 (by rfl) ⟨627435, by rfl⟩ : syracuseStep 6692645 = 1254871) (by norm_num)
theorem B2645813 : Blo 1762082 2645813 := bbase (se 5 (by rfl) ⟨124022, by rfl⟩ : syracuseStep 2645813 = 248045) (by norm_num)
theorem B3964733 : Blo 1762082 3964733 := bbase (se 3 (by rfl) ⟨743387, by rfl⟩ : syracuseStep 3964733 = 1486775) (by norm_num)
theorem B7151429 : Blo 1762082 7151429 := bbase (se 4 (by rfl) ⟨670446, by rfl⟩ : syracuseStep 7151429 = 1340893) (by norm_num)
theorem B2645837 : Blo 1762082 2645837 := bbase (se 3 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 2645837 = 992189) (by norm_num)
theorem B3178325 : Blo 1762082 3178325 := bbase (se 9 (by rfl) ⟨9311, by rfl⟩ : syracuseStep 3178325 = 18623) (by norm_num)
theorem B2645861 : Blo 1762082 2645861 := bbase (se 4 (by rfl) ⟨248049, by rfl⟩ : syracuseStep 2645861 = 496099) (by norm_num)
theorem B2973557 : Blo 1762082 2973557 := bbase (se 5 (by rfl) ⟨139385, by rfl⟩ : syracuseStep 2973557 = 278771) (by norm_num)
theorem B2645885 : Blo 1762082 2645885 := bbase (se 3 (by rfl) ⟨496103, by rfl⟩ : syracuseStep 2645885 = 992207) (by norm_num)
theorem B3964805 : Blo 1762082 3964805 := bbase (se 4 (by rfl) ⟨371700, by rfl⟩ : syracuseStep 3964805 = 743401) (by norm_num)
theorem B4464517 : Blo 1762082 4464517 := bbase (se 4 (by rfl) ⟨418548, by rfl⟩ : syracuseStep 4464517 = 837097) (by norm_num)
theorem B1982353 : Blo 1762082 1982353 := bbase (se 2 (by rfl) ⟨743382, by rfl⟩ : syracuseStep 1982353 = 1486765) (by norm_num)
theorem B2645909 : Blo 1762082 2645909 := bbase (se 6 (by rfl) ⟨62013, by rfl⟩ : syracuseStep 2645909 = 124027) (by norm_num)
theorem B2645933 : Blo 1762082 2645933 := bbase (se 3 (by rfl) ⟨496112, by rfl⟩ : syracuseStep 2645933 = 992225) (by norm_num)
theorem B1982389 : Blo 1762082 1982389 := bbase (se 5 (by rfl) ⟨92924, by rfl⟩ : syracuseStep 1982389 = 185849) (by norm_num)
theorem B7528373 : Blo 1762082 7528373 := bbase (se 5 (by rfl) ⟨352892, by rfl⟩ : syracuseStep 7528373 = 705785) (by norm_num)
theorem B2645957 : Blo 1762082 2645957 := bbase (se 4 (by rfl) ⟨248058, by rfl⟩ : syracuseStep 2645957 = 496117) (by norm_num)
theorem B3964877 : Blo 1762082 3964877 := bbase (se 3 (by rfl) ⟨743414, by rfl⟩ : syracuseStep 3964877 = 1486829) (by norm_num)
theorem B1982425 : Blo 1762082 1982425 := bbase (se 2 (by rfl) ⟨743409, by rfl⟩ : syracuseStep 1982425 = 1486819) (by norm_num)
theorem B2645981 : Blo 1762082 2645981 := bbase (se 3 (by rfl) ⟨496121, by rfl⟩ : syracuseStep 2645981 = 992243) (by norm_num)
theorem B3178469 : Blo 1762082 3178469 := bbase (se 4 (by rfl) ⟨297981, by rfl⟩ : syracuseStep 3178469 = 595963) (by norm_num)
theorem B2973685 : Blo 1762082 2973685 := bbase (se 5 (by rfl) ⟨139391, by rfl⟩ : syracuseStep 2973685 = 278783) (by norm_num)
theorem B4464629 : Blo 1762082 4464629 := bbase (se 5 (by rfl) ⟨209279, by rfl⟩ : syracuseStep 4464629 = 418559) (by norm_num)
theorem B2646005 : Blo 1762082 2646005 := bbase (se 5 (by rfl) ⟨124031, by rfl⟩ : syracuseStep 2646005 = 248063) (by norm_num)
theorem B1982461 : Blo 1762082 1982461 := bbase (se 3 (by rfl) ⟨371711, by rfl⟩ : syracuseStep 1982461 = 743423) (by norm_num)
theorem B2646017 : Blo 1762082 2646017 := bstep (se 2 (by rfl) ⟨992256, by rfl⟩ : syracuseStep 2646017 = 1984513) B1984513
theorem B3964931 : Blo 1762082 3964931 := bstep (se 1 (by rfl) ⟨2973698, by rfl⟩ : syracuseStep 3964931 = 5947397) B5947397
theorem B2646035 : Blo 1762082 2646035 := bstep (se 1 (by rfl) ⟨1984526, by rfl⟩ : syracuseStep 2646035 = 3969053) B3969053
theorem B2646065 : Blo 1762082 2646065 := bstep (se 2 (by rfl) ⟨992274, by rfl⟩ : syracuseStep 2646065 = 1984549) B1984549
theorem B1982515 : Blo 1762082 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B2646083 : Blo 1762082 2646083 := bstep (se 1 (by rfl) ⟨1984562, by rfl⟩ : syracuseStep 2646083 = 3969125) B3969125
theorem B2973793 : Blo 1762082 2973793 := bstep (se 2 (by rfl) ⟨1115172, by rfl⟩ : syracuseStep 2973793 = 2230345) B2230345
theorem B2646113 : Blo 1762082 2646113 := bstep (se 2 (by rfl) ⟨992292, by rfl⟩ : syracuseStep 2646113 = 1984585) B1984585
theorem B5947505 : Blo 1762082 5947505 := bstep (se 2 (by rfl) ⟨2230314, by rfl⟩ : syracuseStep 5947505 = 4460629) B4460629
theorem B2973827 : Blo 1762082 2973827 := bstep (se 1 (by rfl) ⟨2230370, by rfl⟩ : syracuseStep 2973827 = 4460741) B4460741
theorem B2261155 : Blo 1762082 2261155 := bstep (se 1 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 2261155 = 3391733) B3391733
theorem B1982659 : Blo 1762082 1982659 := bstep (se 1 (by rfl) ⟨1486994, by rfl⟩ : syracuseStep 1982659 = 2973989) B2973989
theorem B28582085 : Blo 1762082 28582085 := bstep (se 4 (by rfl) ⟨2679570, by rfl⟩ : syracuseStep 28582085 = 5359141) B5359141
theorem B2973955 : Blo 1762082 2973955 := bstep (se 1 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 2973955 = 4460933) B4460933
theorem B3965201 : Blo 1762082 3965201 := bstep (se 2 (by rfl) ⟨1486950, by rfl⟩ : syracuseStep 3965201 = 2973901) B2973901
theorem B3965219 : Blo 1762082 3965219 := bstep (se 1 (by rfl) ⟨2973914, by rfl⟩ : syracuseStep 3965219 = 5947829) B5947829
theorem B3178801 : Blo 1762082 3178801 := bstep (se 2 (by rfl) ⟨1192050, by rfl⟩ : syracuseStep 3178801 = 2384101) B2384101
theorem B1982803 : Blo 1762082 1982803 := bstep (se 1 (by rfl) ⟨1487102, by rfl⟩ : syracuseStep 1982803 = 2974205) B2974205
theorem B19333475 : Blo 1762082 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B2974097 : Blo 1762082 2974097 := bstep (se 2 (by rfl) ⟨1115286, by rfl⟩ : syracuseStep 2974097 = 2230573) B2230573
theorem B1982947 : Blo 1762082 1982947 := bstep (se 1 (by rfl) ⟨1487210, by rfl⟩ : syracuseStep 1982947 = 2974421) B2974421
theorem B4293091 : Blo 1762082 4293091 := bstep (se 1 (by rfl) ⟨3219818, by rfl⟩ : syracuseStep 4293091 = 6439637) B6439637
theorem B8929763 : Blo 1762082 8929763 := bstep (se 1 (by rfl) ⟨6697322, by rfl⟩ : syracuseStep 8929763 = 13394645) B13394645
theorem B24461837 : Blo 1762082 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B2974225 : Blo 1762082 2974225 := bstep (se 2 (by rfl) ⟨1115334, by rfl⟩ : syracuseStep 2974225 = 2230669) B2230669
theorem B3965489 : Blo 1762082 3965489 := bstep (se 2 (by rfl) ⟨1487058, by rfl⟩ : syracuseStep 3965489 = 2974117) B2974117
theorem B2974259 : Blo 1762082 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B3965507 : Blo 1762082 3965507 := bstep (se 1 (by rfl) ⟨2974130, by rfl⟩ : syracuseStep 3965507 = 5948261) B5948261
theorem B1983091 : Blo 1762082 1983091 := bstep (se 1 (by rfl) ⟨1487318, by rfl⟩ : syracuseStep 1983091 = 2974637) B2974637
theorem B22889101 : Blo 1762082 22889101 := bstep (se 3 (by rfl) ⟨4291706, by rfl⟩ : syracuseStep 22889101 = 8583413) B8583413
theorem B5948045 : Blo 1762082 5948045 := bstep (se 3 (by rfl) ⟨1115258, by rfl⟩ : syracuseStep 5948045 = 2230517) B2230517
theorem B2974387 : Blo 1762082 2974387 := bstep (se 1 (by rfl) ⟨2230790, by rfl⟩ : syracuseStep 2974387 = 4461581) B4461581
theorem B5948099 : Blo 1762082 5948099 := bstep (se 1 (by rfl) ⟨4461074, by rfl⟩ : syracuseStep 5948099 = 8922149) B8922149
theorem B3220163 : Blo 1762082 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B6693617 : Blo 1762082 6693617 := bstep (se 2 (by rfl) ⟨2510106, by rfl⟩ : syracuseStep 6693617 = 5020213) B5020213
theorem B1983235 : Blo 1762082 1983235 := bstep (se 1 (by rfl) ⟨1487426, by rfl⟩ : syracuseStep 1983235 = 2974853) B2974853
theorem B1762083 : Blo 1762082 1762083 := bstep (se 1 (by rfl) ⟨1321562, by rfl⟩ : syracuseStep 1762083 = 2643125) B2643125
theorem B1762099 : Blo 1762082 1762099 := bstep (se 1 (by rfl) ⟨1321574, by rfl⟩ : syracuseStep 1762099 = 2643149) B2643149
theorem B2974529 : Blo 1762082 2974529 := bstep (se 2 (by rfl) ⟨1115448, by rfl⟩ : syracuseStep 2974529 = 2230897) B2230897
theorem B1762115 : Blo 1762082 1762115 := bstep (se 1 (by rfl) ⟨1321586, by rfl⟩ : syracuseStep 1762115 = 2643173) B2643173
theorem B3965777 : Blo 1762082 3965777 := bstep (se 2 (by rfl) ⟨1487166, by rfl⟩ : syracuseStep 3965777 = 2974333) B2974333
theorem B4236113 : Blo 1762082 4236113 := bstep (se 2 (by rfl) ⟨1588542, by rfl⟩ : syracuseStep 4236113 = 3177085) B3177085
theorem B1762131 : Blo 1762082 1762131 := bstep (se 1 (by rfl) ⟨1321598, by rfl⟩ : syracuseStep 1762131 = 2643197) B2643197
theorem B1762147 : Blo 1762082 1762147 := bstep (se 1 (by rfl) ⟨1321610, by rfl⟩ : syracuseStep 1762147 = 2643221) B2643221
theorem B3965795 : Blo 1762082 3965795 := bstep (se 1 (by rfl) ⟨2974346, by rfl⟩ : syracuseStep 3965795 = 5948693) B5948693
theorem B1762163 : Blo 1762082 1762163 := bstep (se 1 (by rfl) ⟨1321622, by rfl⟩ : syracuseStep 1762163 = 2643245) B2643245
theorem B1762179 : Blo 1762082 1762179 := bstep (se 1 (by rfl) ⟨1321634, by rfl⟩ : syracuseStep 1762179 = 2643269) B2643269
theorem B1762195 : Blo 1762082 1762195 := bstep (se 1 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 1762195 = 2643293) B2643293
theorem B1983379 : Blo 1762082 1983379 := bstep (se 1 (by rfl) ⟨1487534, by rfl⟩ : syracuseStep 1983379 = 2975069) B2975069
theorem B1762211 : Blo 1762082 1762211 := bstep (se 1 (by rfl) ⟨1321658, by rfl⟩ : syracuseStep 1762211 = 2643317) B2643317
theorem B10044323 : Blo 1762082 10044323 := bstep (se 1 (by rfl) ⟨7533242, by rfl⟩ : syracuseStep 10044323 = 15066485) B15066485
theorem B1762227 : Blo 1762082 1762227 := bstep (se 1 (by rfl) ⟨1321670, by rfl⟩ : syracuseStep 1762227 = 2643341) B2643341
theorem B2974657 : Blo 1762082 2974657 := bstep (se 2 (by rfl) ⟨1115496, by rfl⟩ : syracuseStep 2974657 = 2230993) B2230993
theorem B1762243 : Blo 1762082 1762243 := bstep (se 1 (by rfl) ⟨1321682, by rfl⟩ : syracuseStep 1762243 = 2643365) B2643365
theorem B3818435 : Blo 1762082 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B5948369 : Blo 1762082 5948369 := bstep (se 2 (by rfl) ⟨2230638, by rfl⟩ : syracuseStep 5948369 = 4461277) B4461277
theorem B1762259 : Blo 1762082 1762259 := bstep (se 1 (by rfl) ⟨1321694, by rfl⟩ : syracuseStep 1762259 = 2643389) B2643389
theorem B1762275 : Blo 1762082 1762275 := bstep (se 1 (by rfl) ⟨1321706, by rfl⟩ : syracuseStep 1762275 = 2643413) B2643413
theorem B2974691 : Blo 1762082 2974691 := bstep (se 1 (by rfl) ⟨2231018, by rfl⟩ : syracuseStep 2974691 = 4462037) B4462037
theorem B1762291 : Blo 1762082 1762291 := bstep (se 1 (by rfl) ⟨1321718, by rfl⟩ : syracuseStep 1762291 = 2643437) B2643437
theorem B1762307 : Blo 1762082 1762307 := bstep (se 1 (by rfl) ⟨1321730, by rfl⟩ : syracuseStep 1762307 = 2643461) B2643461
theorem B3572753 : Blo 1762082 3572753 := bstep (se 2 (by rfl) ⟨1339782, by rfl⟩ : syracuseStep 3572753 = 2679565) B2679565
theorem B1762323 : Blo 1762082 1762323 := bstep (se 1 (by rfl) ⟨1321742, by rfl⟩ : syracuseStep 1762323 = 2643485) B2643485
theorem B1762339 : Blo 1762082 1762339 := bstep (se 1 (by rfl) ⟨1321754, by rfl⟩ : syracuseStep 1762339 = 2643509) B2643509
theorem B1983523 : Blo 1762082 1983523 := bstep (se 1 (by rfl) ⟨1487642, by rfl⟩ : syracuseStep 1983523 = 2975285) B2975285
theorem B1762355 : Blo 1762082 1762355 := bstep (se 1 (by rfl) ⟨1321766, by rfl⟩ : syracuseStep 1762355 = 2643533) B2643533
theorem B1762371 : Blo 1762082 1762371 := bstep (se 1 (by rfl) ⟨1321778, by rfl⟩ : syracuseStep 1762371 = 2643557) B2643557
theorem B1762387 : Blo 1762082 1762387 := bstep (se 1 (by rfl) ⟨1321790, by rfl⟩ : syracuseStep 1762387 = 2643581) B2643581
theorem B1762403 : Blo 1762082 1762403 := bstep (se 1 (by rfl) ⟨1321802, by rfl⟩ : syracuseStep 1762403 = 2643605) B2643605
theorem B2679907 : Blo 1762082 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B2974819 : Blo 1762082 2974819 := bstep (se 1 (by rfl) ⟨2231114, by rfl⟩ : syracuseStep 2974819 = 4462229) B4462229
theorem B3966065 : Blo 1762082 3966065 := bstep (se 2 (by rfl) ⟨1487274, by rfl⟩ : syracuseStep 3966065 = 2974549) B2974549
theorem B1762419 : Blo 1762082 1762419 := bstep (se 1 (by rfl) ⟨1321814, by rfl⟩ : syracuseStep 1762419 = 2643629) B2643629
theorem B1762435 : Blo 1762082 1762435 := bstep (se 1 (by rfl) ⟨1321826, by rfl⟩ : syracuseStep 1762435 = 2643653) B2643653
theorem B3966083 : Blo 1762082 3966083 := bstep (se 1 (by rfl) ⟨2974562, by rfl⟩ : syracuseStep 3966083 = 5949125) B5949125
theorem B1762451 : Blo 1762082 1762451 := bstep (se 1 (by rfl) ⟨1321838, by rfl⟩ : syracuseStep 1762451 = 2643677) B2643677
theorem B1762467 : Blo 1762082 1762467 := bstep (se 1 (by rfl) ⟨1321850, by rfl⟩ : syracuseStep 1762467 = 2643701) B2643701
theorem B1762483 : Blo 1762082 1762483 := bstep (se 1 (by rfl) ⟨1321862, by rfl⟩ : syracuseStep 1762483 = 2643725) B2643725
theorem B1983667 : Blo 1762082 1983667 := bstep (se 1 (by rfl) ⟨1487750, by rfl⟩ : syracuseStep 1983667 = 2975501) B2975501
theorem B1762499 : Blo 1762082 1762499 := bstep (se 1 (by rfl) ⟨1321874, by rfl⟩ : syracuseStep 1762499 = 2643749) B2643749
theorem B1762515 : Blo 1762082 1762515 := bstep (se 1 (by rfl) ⟨1321886, by rfl⟩ : syracuseStep 1762515 = 2643773) B2643773
theorem B1762531 : Blo 1762082 1762531 := bstep (se 1 (by rfl) ⟨1321898, by rfl⟩ : syracuseStep 1762531 = 2643797) B2643797
theorem B5022947 : Blo 1762082 5022947 := bstep (se 1 (by rfl) ⟨3767210, by rfl⟩ : syracuseStep 5022947 = 7534421) B7534421
theorem B2974961 : Blo 1762082 2974961 := bstep (se 2 (by rfl) ⟨1115610, by rfl⟩ : syracuseStep 2974961 = 2231221) B2231221
theorem B1762547 : Blo 1762082 1762547 := bstep (se 1 (by rfl) ⟨1321910, by rfl⟩ : syracuseStep 1762547 = 2643821) B2643821
theorem B1762563 : Blo 1762082 1762563 := bstep (se 1 (by rfl) ⟨1321922, by rfl⟩ : syracuseStep 1762563 = 2643845) B2643845
theorem B8930573 : Blo 1762082 8930573 := bstep (se 3 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 8930573 = 3348965) B3348965
theorem B1762579 : Blo 1762082 1762579 := bstep (se 1 (by rfl) ⟨1321934, by rfl⟩ : syracuseStep 1762579 = 2643869) B2643869
theorem B1762595 : Blo 1762082 1762595 := bstep (se 1 (by rfl) ⟨1321946, by rfl⟩ : syracuseStep 1762595 = 2643893) B2643893
theorem B1762611 : Blo 1762082 1762611 := bstep (se 1 (by rfl) ⟨1321958, by rfl⟩ : syracuseStep 1762611 = 2643917) B2643917
theorem B1762627 : Blo 1762082 1762627 := bstep (se 1 (by rfl) ⟨1321970, by rfl⟩ : syracuseStep 1762627 = 2643941) B2643941
theorem B1983811 : Blo 1762082 1983811 := bstep (se 1 (by rfl) ⟨1487858, by rfl⟩ : syracuseStep 1983811 = 2975717) B2975717
theorem B1762643 : Blo 1762082 1762643 := bstep (se 1 (by rfl) ⟨1321982, by rfl⟩ : syracuseStep 1762643 = 2643965) B2643965
theorem B8037731 : Blo 1762082 8037731 := bstep (se 1 (by rfl) ⟨6028298, by rfl⟩ : syracuseStep 8037731 = 12056597) B12056597
theorem B1762659 : Blo 1762082 1762659 := bstep (se 1 (by rfl) ⟨1321994, by rfl⟩ : syracuseStep 1762659 = 2643989) B2643989
theorem B2975089 : Blo 1762082 2975089 := bstep (se 2 (by rfl) ⟨1115658, by rfl⟩ : syracuseStep 2975089 = 2231317) B2231317
theorem B13763953 : Blo 1762082 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B1762675 : Blo 1762082 1762675 := bstep (se 1 (by rfl) ⟨1322006, by rfl⟩ : syracuseStep 1762675 = 2644013) B2644013
theorem B1762691 : Blo 1762082 1762691 := bstep (se 1 (by rfl) ⟨1322018, by rfl⟩ : syracuseStep 1762691 = 2644037) B2644037
theorem B6694285 : Blo 1762082 6694285 := bstep (se 3 (by rfl) ⟨1255178, by rfl⟩ : syracuseStep 6694285 = 2510357) B2510357
theorem B3966353 : Blo 1762082 3966353 := bstep (se 2 (by rfl) ⟨1487382, by rfl⟩ : syracuseStep 3966353 = 2974765) B2974765
theorem B1762707 : Blo 1762082 1762707 := bstep (se 1 (by rfl) ⟨1322030, by rfl⟩ : syracuseStep 1762707 = 2644061) B2644061
theorem B2975123 : Blo 1762082 2975123 := bstep (se 1 (by rfl) ⟨2231342, by rfl⟩ : syracuseStep 2975123 = 4462685) B4462685
theorem B1762723 : Blo 1762082 1762723 := bstep (se 1 (by rfl) ⟨1322042, by rfl⟩ : syracuseStep 1762723 = 2644085) B2644085
theorem B3966371 : Blo 1762082 3966371 := bstep (se 1 (by rfl) ⟨2974778, by rfl⟩ : syracuseStep 3966371 = 5949557) B5949557
theorem B1762739 : Blo 1762082 1762739 := bstep (se 1 (by rfl) ⟨1322054, by rfl⟩ : syracuseStep 1762739 = 2644109) B2644109
theorem B1762755 : Blo 1762082 1762755 := bstep (se 1 (by rfl) ⟨1322066, by rfl⟩ : syracuseStep 1762755 = 2644133) B2644133
theorem B1762771 : Blo 1762082 1762771 := bstep (se 1 (by rfl) ⟨1322078, by rfl⟩ : syracuseStep 1762771 = 2644157) B2644157
theorem B1983955 : Blo 1762082 1983955 := bstep (se 1 (by rfl) ⟨1487966, by rfl⟩ : syracuseStep 1983955 = 2975933) B2975933
theorem B1762787 : Blo 1762082 1762787 := bstep (se 1 (by rfl) ⟨1322090, by rfl⟩ : syracuseStep 1762787 = 2644181) B2644181
theorem B5948909 : Blo 1762082 5948909 := bstep (se 3 (by rfl) ⟨1115420, by rfl⟩ : syracuseStep 5948909 = 2230841) B2230841
theorem B1762803 : Blo 1762082 1762803 := bstep (se 1 (by rfl) ⟨1322102, by rfl⟩ : syracuseStep 1762803 = 2644205) B2644205
theorem B1762819 : Blo 1762082 1762819 := bstep (se 1 (by rfl) ⟨1322114, by rfl⟩ : syracuseStep 1762819 = 2644229) B2644229
theorem B1762835 : Blo 1762082 1762835 := bstep (se 1 (by rfl) ⟨1322126, by rfl⟩ : syracuseStep 1762835 = 2644253) B2644253
theorem B2975251 : Blo 1762082 2975251 := bstep (se 1 (by rfl) ⟨2231438, by rfl⟩ : syracuseStep 2975251 = 4462877) B4462877
theorem B5948963 : Blo 1762082 5948963 := bstep (se 1 (by rfl) ⟨4461722, by rfl⟩ : syracuseStep 5948963 = 8923445) B8923445
theorem B1762851 : Blo 1762082 1762851 := bstep (se 1 (by rfl) ⟨1322138, by rfl⟩ : syracuseStep 1762851 = 2644277) B2644277
theorem B1762867 : Blo 1762082 1762867 := bstep (se 1 (by rfl) ⟨1322150, by rfl⟩ : syracuseStep 1762867 = 2644301) B2644301
theorem B1762883 : Blo 1762082 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B1762899 : Blo 1762082 1762899 := bstep (se 1 (by rfl) ⟨1322174, by rfl⟩ : syracuseStep 1762899 = 2644349) B2644349
theorem B1762915 : Blo 1762082 1762915 := bstep (se 1 (by rfl) ⟨1322186, by rfl⟩ : syracuseStep 1762915 = 2644373) B2644373
theorem B1984099 : Blo 1762082 1984099 := bstep (se 1 (by rfl) ⟨1488074, by rfl⟩ : syracuseStep 1984099 = 2976149) B2976149
theorem B1762931 : Blo 1762082 1762931 := bstep (se 1 (by rfl) ⟨1322198, by rfl⟩ : syracuseStep 1762931 = 2644397) B2644397
theorem B1762947 : Blo 1762082 1762947 := bstep (se 1 (by rfl) ⟨1322210, by rfl⟩ : syracuseStep 1762947 = 2644421) B2644421
theorem B9528965 : Blo 1762082 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B1762963 : Blo 1762082 1762963 := bstep (se 1 (by rfl) ⟨1322222, by rfl⟩ : syracuseStep 1762963 = 2644445) B2644445
theorem B2975393 : Blo 1762082 2975393 := bstep (se 2 (by rfl) ⟨1115772, by rfl⟩ : syracuseStep 2975393 = 2231545) B2231545
theorem B1762979 : Blo 1762082 1762979 := bstep (se 1 (by rfl) ⟨1322234, by rfl⟩ : syracuseStep 1762979 = 2644469) B2644469
theorem B3966641 : Blo 1762082 3966641 := bstep (se 2 (by rfl) ⟨1487490, by rfl⟩ : syracuseStep 3966641 = 2974981) B2974981
theorem B1762995 : Blo 1762082 1762995 := bstep (se 1 (by rfl) ⟨1322246, by rfl⟩ : syracuseStep 1762995 = 2644493) B2644493
theorem B3868355 : Blo 1762082 3868355 := bstep (se 1 (by rfl) ⟨2901266, by rfl⟩ : syracuseStep 3868355 = 5802533) B5802533
theorem B3966659 : Blo 1762082 3966659 := bstep (se 1 (by rfl) ⟨2974994, by rfl⟩ : syracuseStep 3966659 = 5949989) B5949989
theorem B1763011 : Blo 1762082 1763011 := bstep (se 1 (by rfl) ⟨1322258, by rfl⟩ : syracuseStep 1763011 = 2644517) B2644517
theorem B1763027 : Blo 1762082 1763027 := bstep (se 1 (by rfl) ⟨1322270, by rfl⟩ : syracuseStep 1763027 = 2644541) B2644541
theorem B1763043 : Blo 1762082 1763043 := bstep (se 1 (by rfl) ⟨1322282, by rfl⟩ : syracuseStep 1763043 = 2644565) B2644565
theorem B1763059 : Blo 1762082 1763059 := bstep (se 1 (by rfl) ⟨1322294, by rfl⟩ : syracuseStep 1763059 = 2644589) B2644589
theorem B1984243 : Blo 1762082 1984243 := bstep (se 1 (by rfl) ⟨1488182, by rfl⟩ : syracuseStep 1984243 = 2976365) B2976365
theorem B1763075 : Blo 1762082 1763075 := bstep (se 1 (by rfl) ⟨1322306, by rfl⟩ : syracuseStep 1763075 = 2644613) B2644613
theorem B1763091 : Blo 1762082 1763091 := bstep (se 1 (by rfl) ⟨1322318, by rfl⟩ : syracuseStep 1763091 = 2644637) B2644637
theorem B2975521 : Blo 1762082 2975521 := bstep (se 2 (by rfl) ⟨1115820, by rfl⟩ : syracuseStep 2975521 = 2231641) B2231641
theorem B1763107 : Blo 1762082 1763107 := bstep (se 1 (by rfl) ⟨1322330, by rfl⟩ : syracuseStep 1763107 = 2644661) B2644661
theorem B5949233 : Blo 1762082 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B1763123 : Blo 1762082 1763123 := bstep (se 1 (by rfl) ⟨1322342, by rfl⟩ : syracuseStep 1763123 = 2644685) B2644685
theorem B1763139 : Blo 1762082 1763139 := bstep (se 1 (by rfl) ⟨1322354, by rfl⟩ : syracuseStep 1763139 = 2644709) B2644709
theorem B2975555 : Blo 1762082 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B1763155 : Blo 1762082 1763155 := bstep (se 1 (by rfl) ⟨1322366, by rfl⟩ : syracuseStep 1763155 = 2644733) B2644733
theorem B1763171 : Blo 1762082 1763171 := bstep (se 1 (by rfl) ⟨1322378, by rfl⟩ : syracuseStep 1763171 = 2644757) B2644757
theorem B15476579 : Blo 1762082 15476579 := bstep (se 1 (by rfl) ⟨11607434, by rfl⟩ : syracuseStep 15476579 = 23214869) B23214869
theorem B8046449 : Blo 1762082 8046449 := bstep (se 2 (by rfl) ⟨3017418, by rfl⟩ : syracuseStep 8046449 = 6034837) B6034837
theorem B1763187 : Blo 1762082 1763187 := bstep (se 1 (by rfl) ⟨1322390, by rfl⟩ : syracuseStep 1763187 = 2644781) B2644781
theorem B1763203 : Blo 1762082 1763203 := bstep (se 1 (by rfl) ⟨1322402, by rfl⟩ : syracuseStep 1763203 = 2644805) B2644805
theorem B1984387 : Blo 1762082 1984387 := bstep (se 1 (by rfl) ⟨1488290, by rfl⟩ : syracuseStep 1984387 = 2976581) B2976581
theorem B1763219 : Blo 1762082 1763219 := bstep (se 1 (by rfl) ⟨1322414, by rfl⟩ : syracuseStep 1763219 = 2644829) B2644829
theorem B1763235 : Blo 1762082 1763235 := bstep (se 1 (by rfl) ⟨1322426, by rfl⟩ : syracuseStep 1763235 = 2644853) B2644853
theorem B9529265 : Blo 1762082 9529265 := bstep (se 2 (by rfl) ⟨3573474, by rfl⟩ : syracuseStep 9529265 = 7146949) B7146949
theorem B1763251 : Blo 1762082 1763251 := bstep (se 1 (by rfl) ⟨1322438, by rfl⟩ : syracuseStep 1763251 = 2644877) B2644877
theorem B1763267 : Blo 1762082 1763267 := bstep (se 1 (by rfl) ⟨1322450, by rfl⟩ : syracuseStep 1763267 = 2644901) B2644901
theorem B2975683 : Blo 1762082 2975683 := bstep (se 1 (by rfl) ⟨2231762, by rfl⟩ : syracuseStep 2975683 = 4463525) B4463525
theorem B3966929 : Blo 1762082 3966929 := bstep (se 2 (by rfl) ⟨1487598, by rfl⟩ : syracuseStep 3966929 = 2975197) B2975197
theorem B1763283 : Blo 1762082 1763283 := bstep (se 1 (by rfl) ⟨1322462, by rfl⟩ : syracuseStep 1763283 = 2644925) B2644925
theorem B3966947 : Blo 1762082 3966947 := bstep (se 1 (by rfl) ⟨2975210, by rfl⟩ : syracuseStep 3966947 = 5950421) B5950421
theorem B1763299 : Blo 1762082 1763299 := bstep (se 1 (by rfl) ⟨1322474, by rfl⟩ : syracuseStep 1763299 = 2644949) B2644949
theorem B8923121 : Blo 1762082 8923121 := bstep (se 2 (by rfl) ⟨3346170, by rfl⟩ : syracuseStep 8923121 = 6692341) B6692341
theorem B1763315 : Blo 1762082 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B1763331 : Blo 1762082 1763331 := bstep (se 1 (by rfl) ⟨1322498, by rfl⟩ : syracuseStep 1763331 = 2644997) B2644997
theorem B7530509 : Blo 1762082 7530509 := bstep (se 3 (by rfl) ⟨1411970, by rfl⟩ : syracuseStep 7530509 = 2823941) B2823941
theorem B1763347 : Blo 1762082 1763347 := bstep (se 1 (by rfl) ⟨1322510, by rfl⟩ : syracuseStep 1763347 = 2645021) B2645021
theorem B1984531 : Blo 1762082 1984531 := bstep (se 1 (by rfl) ⟨1488398, by rfl⟩ : syracuseStep 1984531 = 2976797) B2976797
theorem B1763363 : Blo 1762082 1763363 := bstep (se 1 (by rfl) ⟨1322522, by rfl⟩ : syracuseStep 1763363 = 2645045) B2645045
theorem B1763379 : Blo 1762082 1763379 := bstep (se 1 (by rfl) ⟨1322534, by rfl⟩ : syracuseStep 1763379 = 2645069) B2645069
theorem B1763395 : Blo 1762082 1763395 := bstep (se 1 (by rfl) ⟨1322546, by rfl⟩ : syracuseStep 1763395 = 2645093) B2645093
theorem B2975825 : Blo 1762082 2975825 := bstep (se 2 (by rfl) ⟨1115934, by rfl⟩ : syracuseStep 2975825 = 2231869) B2231869
theorem B2230355 : Blo 1762082 2230355 := bstep (se 1 (by rfl) ⟨1672766, by rfl⟩ : syracuseStep 2230355 = 3345533) B3345533
theorem B1763411 : Blo 1762082 1763411 := bstep (se 1 (by rfl) ⟨1322558, by rfl⟩ : syracuseStep 1763411 = 2645117) B2645117
theorem B1763427 : Blo 1762082 1763427 := bstep (se 1 (by rfl) ⟨1322570, by rfl⟩ : syracuseStep 1763427 = 2645141) B2645141
theorem B1763443 : Blo 1762082 1763443 := bstep (se 1 (by rfl) ⟨1322582, by rfl⟩ : syracuseStep 1763443 = 2645165) B2645165
theorem B1763459 : Blo 1762082 1763459 := bstep (se 1 (by rfl) ⟨1322594, by rfl⟩ : syracuseStep 1763459 = 2645189) B2645189
theorem B1763475 : Blo 1762082 1763475 := bstep (se 1 (by rfl) ⟨1322606, by rfl⟩ : syracuseStep 1763475 = 2645213) B2645213
theorem B6695075 : Blo 1762082 6695075 := bstep (se 1 (by rfl) ⟨5021306, by rfl⟩ : syracuseStep 6695075 = 10042613) B10042613
theorem B1763491 : Blo 1762082 1763491 := bstep (se 1 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 1763491 = 2645237) B2645237
theorem B1763507 : Blo 1762082 1763507 := bstep (se 1 (by rfl) ⟨1322630, by rfl⟩ : syracuseStep 1763507 = 2645261) B2645261
theorem B1763523 : Blo 1762082 1763523 := bstep (se 1 (by rfl) ⟨1322642, by rfl⟩ : syracuseStep 1763523 = 2645285) B2645285
theorem B2975953 : Blo 1762082 2975953 := bstep (se 2 (by rfl) ⟨1115982, by rfl⟩ : syracuseStep 2975953 = 2231965) B2231965
theorem B1763539 : Blo 1762082 1763539 := bstep (se 1 (by rfl) ⟨1322654, by rfl⟩ : syracuseStep 1763539 = 2645309) B2645309
theorem B1763555 : Blo 1762082 1763555 := bstep (se 1 (by rfl) ⟨1322666, by rfl⟩ : syracuseStep 1763555 = 2645333) B2645333
theorem B3967217 : Blo 1762082 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B2681075 : Blo 1762082 2681075 := bstep (se 1 (by rfl) ⟨2010806, by rfl⟩ : syracuseStep 2681075 = 4021613) B4021613
theorem B2975987 : Blo 1762082 2975987 := bstep (se 1 (by rfl) ⟨2231990, by rfl⟩ : syracuseStep 2975987 = 4463981) B4463981
theorem B1763571 : Blo 1762082 1763571 := bstep (se 1 (by rfl) ⟨1322678, by rfl⟩ : syracuseStep 1763571 = 2645357) B2645357
theorem B3967235 : Blo 1762082 3967235 := bstep (se 1 (by rfl) ⟨2975426, by rfl⟩ : syracuseStep 3967235 = 5950853) B5950853
theorem B1763587 : Blo 1762082 1763587 := bstep (se 1 (by rfl) ⟨1322690, by rfl⟩ : syracuseStep 1763587 = 2645381) B2645381
theorem B1763603 : Blo 1762082 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B6785315 : Blo 1762082 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B1763619 : Blo 1762082 1763619 := bstep (se 1 (by rfl) ⟨1322714, by rfl⟩ : syracuseStep 1763619 = 2645429) B2645429
theorem B11299121 : Blo 1762082 11299121 := bstep (se 2 (by rfl) ⟨4237170, by rfl⟩ : syracuseStep 11299121 = 8474341) B8474341
theorem B1763635 : Blo 1762082 1763635 := bstep (se 1 (by rfl) ⟨1322726, by rfl⟩ : syracuseStep 1763635 = 2645453) B2645453
theorem B1763651 : Blo 1762082 1763651 := bstep (se 1 (by rfl) ⟨1322738, by rfl⟩ : syracuseStep 1763651 = 2645477) B2645477
theorem B5949773 : Blo 1762082 5949773 := bstep (se 3 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 5949773 = 2231165) B2231165
theorem B1763667 : Blo 1762082 1763667 := bstep (se 1 (by rfl) ⟨1322750, by rfl⟩ : syracuseStep 1763667 = 2645501) B2645501
theorem B1763683 : Blo 1762082 1763683 := bstep (se 1 (by rfl) ⟨1322762, by rfl⟩ : syracuseStep 1763683 = 2645525) B2645525
theorem B2976115 : Blo 1762082 2976115 := bstep (se 1 (by rfl) ⟨2232086, by rfl⟩ : syracuseStep 2976115 = 4464173) B4464173
theorem B1763699 : Blo 1762082 1763699 := bstep (se 1 (by rfl) ⟨1322774, by rfl⟩ : syracuseStep 1763699 = 2645549) B2645549
theorem B5949827 : Blo 1762082 5949827 := bstep (se 1 (by rfl) ⟨4462370, by rfl⟩ : syracuseStep 5949827 = 8924741) B8924741
theorem B1763715 : Blo 1762082 1763715 := bstep (se 1 (by rfl) ⟨1322786, by rfl⟩ : syracuseStep 1763715 = 2645573) B2645573
theorem B3017089 : Blo 1762082 3017089 := bstep (se 2 (by rfl) ⟨1131408, by rfl⟩ : syracuseStep 3017089 = 2262817) B2262817
theorem B1763731 : Blo 1762082 1763731 := bstep (se 1 (by rfl) ⟨1322798, by rfl⟩ : syracuseStep 1763731 = 2645597) B2645597
theorem B1763747 : Blo 1762082 1763747 := bstep (se 1 (by rfl) ⟨1322810, by rfl⟩ : syracuseStep 1763747 = 2645621) B2645621
theorem B1763763 : Blo 1762082 1763763 := bstep (se 1 (by rfl) ⟨1322822, by rfl⟩ : syracuseStep 1763763 = 2645645) B2645645
theorem B1763779 : Blo 1762082 1763779 := bstep (se 1 (by rfl) ⟨1322834, by rfl⟩ : syracuseStep 1763779 = 2645669) B2645669
theorem B1763795 : Blo 1762082 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1763811 : Blo 1762082 1763811 := bstep (se 1 (by rfl) ⟨1322858, by rfl⟩ : syracuseStep 1763811 = 2645717) B2645717
theorem B1763827 : Blo 1762082 1763827 := bstep (se 1 (by rfl) ⟨1322870, by rfl⟩ : syracuseStep 1763827 = 2645741) B2645741
theorem B2976257 : Blo 1762082 2976257 := bstep (se 2 (by rfl) ⟨1116096, by rfl⟩ : syracuseStep 2976257 = 2232193) B2232193
theorem B1763843 : Blo 1762082 1763843 := bstep (se 1 (by rfl) ⟨1322882, by rfl⟩ : syracuseStep 1763843 = 2645765) B2645765
theorem B3967505 : Blo 1762082 3967505 := bstep (se 2 (by rfl) ⟨1487814, by rfl⟩ : syracuseStep 3967505 = 2975629) B2975629
theorem B1763859 : Blo 1762082 1763859 := bstep (se 1 (by rfl) ⟨1322894, by rfl⟩ : syracuseStep 1763859 = 2645789) B2645789
theorem B3967523 : Blo 1762082 3967523 := bstep (se 1 (by rfl) ⟨2975642, by rfl⟩ : syracuseStep 3967523 = 5951285) B5951285
theorem B1763875 : Blo 1762082 1763875 := bstep (se 1 (by rfl) ⟨1322906, by rfl⟩ : syracuseStep 1763875 = 2645813) B2645813
theorem B1763891 : Blo 1762082 1763891 := bstep (se 1 (by rfl) ⟨1322918, by rfl⟩ : syracuseStep 1763891 = 2645837) B2645837
theorem B1763907 : Blo 1762082 1763907 := bstep (se 1 (by rfl) ⟨1322930, by rfl⟩ : syracuseStep 1763907 = 2645861) B2645861
theorem B1763923 : Blo 1762082 1763923 := bstep (se 1 (by rfl) ⟨1322942, by rfl⟩ : syracuseStep 1763923 = 2645885) B2645885
theorem B1763939 : Blo 1762082 1763939 := bstep (se 1 (by rfl) ⟨1322954, by rfl⟩ : syracuseStep 1763939 = 2645909) B2645909
theorem B8153713 : Blo 1762082 8153713 := bstep (se 2 (by rfl) ⟨3057642, by rfl⟩ : syracuseStep 8153713 = 6115285) B6115285
theorem B1763955 : Blo 1762082 1763955 := bstep (se 1 (by rfl) ⟨1322966, by rfl⟩ : syracuseStep 1763955 = 2645933) B2645933
theorem B2976385 : Blo 1762082 2976385 := bstep (se 2 (by rfl) ⟨1116144, by rfl⟩ : syracuseStep 2976385 = 2232289) B2232289
theorem B1763971 : Blo 1762082 1763971 := bstep (se 1 (by rfl) ⟨1322978, by rfl⟩ : syracuseStep 1763971 = 2645957) B2645957
theorem B5950097 : Blo 1762082 5950097 := bstep (se 2 (by rfl) ⟨2231286, by rfl⟩ : syracuseStep 5950097 = 4462573) B4462573
theorem B1763987 : Blo 1762082 1763987 := bstep (se 1 (by rfl) ⟨1322990, by rfl⟩ : syracuseStep 1763987 = 2645981) B2645981
theorem B2976419 : Blo 1762082 2976419 := bstep (se 1 (by rfl) ⟨2232314, by rfl⟩ : syracuseStep 2976419 = 4464629) B4464629
theorem B1764003 : Blo 1762082 1764003 := bstep (se 1 (by rfl) ⟨1323002, by rfl⟩ : syracuseStep 1764003 = 2646005) B2646005
theorem B1764019 : Blo 1762082 1764019 := bstep (se 1 (by rfl) ⟨1323014, by rfl⟩ : syracuseStep 1764019 = 2646029) B2646029
theorem B1764035 : Blo 1762082 1764035 := bstep (se 1 (by rfl) ⟨1323026, by rfl⟩ : syracuseStep 1764035 = 2646053) B2646053
theorem B10037965 : Blo 1762082 10037965 := bstep (se 3 (by rfl) ⟨1882118, by rfl⟩ : syracuseStep 10037965 = 3764237) B3764237
theorem B1764051 : Blo 1762082 1764051 := bstep (se 1 (by rfl) ⟨1323038, by rfl⟩ : syracuseStep 1764051 = 2646077) B2646077
theorem B2509537 : Blo 1762082 2509537 := bstep (se 2 (by rfl) ⟨941076, by rfl⟩ : syracuseStep 2509537 = 1882153) B1882153
theorem B1764067 : Blo 1762082 1764067 := bstep (se 1 (by rfl) ⟨1323050, by rfl⟩ : syracuseStep 1764067 = 2646101) B2646101
theorem B10046213 : Blo 1762082 10046213 := bstep (se 4 (by rfl) ⟨941832, by rfl⟩ : syracuseStep 10046213 = 1883665) B1883665
theorem B2231059 : Blo 1762082 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B2976547 : Blo 1762082 2976547 := bstep (se 1 (by rfl) ⟨2232410, by rfl⟩ : syracuseStep 2976547 = 4464821) B4464821
theorem B3967793 : Blo 1762082 3967793 := bstep (se 2 (by rfl) ⟨1487922, by rfl⟩ : syracuseStep 3967793 = 2975845) B2975845
theorem B6695729 : Blo 1762082 6695729 := bstep (se 2 (by rfl) ⟨2510898, by rfl⟩ : syracuseStep 6695729 = 5021797) B5021797
theorem B3967811 : Blo 1762082 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B11299661 : Blo 1762082 11299661 := bstep (se 3 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 11299661 = 4237373) B4237373
theorem B2509651 : Blo 1762082 2509651 := bstep (se 1 (by rfl) ⟨1882238, by rfl⟩ : syracuseStep 2509651 = 3764477) B3764477
theorem B2231155 : Blo 1762082 2231155 := bstep (se 1 (by rfl) ⟨1673366, by rfl⟩ : syracuseStep 2231155 = 3346733) B3346733
theorem B11447203 : Blo 1762082 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B2976689 : Blo 1762082 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B20089781 : Blo 1762082 20089781 := bstep (se 5 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 20089781 = 1883417) B1883417
theorem B13388813 : Blo 1762082 13388813 := bstep (se 3 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 13388813 = 5020805) B5020805
theorem B3345457 : Blo 1762082 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B2976817 : Blo 1762082 2976817 := bstep (se 2 (by rfl) ⟨1116306, by rfl⟩ : syracuseStep 2976817 = 2232613) B2232613
theorem B3968081 : Blo 1762082 3968081 := bstep (se 2 (by rfl) ⟨1488030, by rfl⟩ : syracuseStep 3968081 = 2976061) B2976061
theorem B2976851 : Blo 1762082 2976851 := bstep (se 1 (by rfl) ⟨2232638, by rfl⟩ : syracuseStep 2976851 = 4465277) B4465277
theorem B3968099 : Blo 1762082 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B114355313 : Blo 1762082 114355313 := bstep (se 2 (by rfl) ⟨42883242, by rfl⟩ : syracuseStep 114355313 = 85766485) B85766485
theorem B5950637 : Blo 1762082 5950637 := bstep (se 3 (by rfl) ⟨1115744, by rfl⟩ : syracuseStep 5950637 = 2231489) B2231489
theorem B3345617 : Blo 1762082 3345617 := bstep (se 2 (by rfl) ⟨1254606, by rfl⟩ : syracuseStep 3345617 = 2509213) B2509213
theorem B5950691 : Blo 1762082 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B8473841 : Blo 1762082 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B2010371 : Blo 1762082 2010371 := bstep (se 1 (by rfl) ⟨1507778, by rfl⟩ : syracuseStep 2010371 = 3015557) B3015557
theorem B5647715 : Blo 1762082 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B2231651 : Blo 1762082 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B3968369 : Blo 1762082 3968369 := bstep (se 2 (by rfl) ⟨1488138, by rfl⟩ : syracuseStep 3968369 = 2976277) B2976277
theorem B3968387 : Blo 1762082 3968387 := bstep (se 1 (by rfl) ⟨2976290, by rfl⟩ : syracuseStep 3968387 = 5952581) B5952581
theorem B8924579 : Blo 1762082 8924579 := bstep (se 1 (by rfl) ⟨6693434, by rfl⟩ : syracuseStep 8924579 = 13386869) B13386869
theorem B8474033 : Blo 1762082 8474033 := bstep (se 2 (by rfl) ⟨3177762, by rfl⟩ : syracuseStep 8474033 = 6355525) B6355525
theorem B9530821 : Blo 1762082 9530821 := bstep (se 4 (by rfl) ⟨893514, by rfl⟩ : syracuseStep 9530821 = 1787029) B1787029
theorem B5950961 : Blo 1762082 5950961 := bstep (se 2 (by rfl) ⟨2231610, by rfl⟩ : syracuseStep 5950961 = 4463221) B4463221
theorem B8474147 : Blo 1762082 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B3763793 : Blo 1762082 3763793 := bstep (se 2 (by rfl) ⟨1411422, by rfl⟩ : syracuseStep 3763793 = 2822845) B2822845
theorem B3346019 : Blo 1762082 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B4763249 : Blo 1762082 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B11292301 : Blo 1762082 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B3968657 : Blo 1762082 3968657 := bstep (se 2 (by rfl) ⟨1488246, by rfl⟩ : syracuseStep 3968657 = 2976493) B2976493
theorem B3968675 : Blo 1762082 3968675 := bstep (se 1 (by rfl) ⟨2976506, by rfl⟩ : syracuseStep 3968675 = 5953013) B5953013
theorem B7147277 : Blo 1762082 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B4460305 : Blo 1762082 4460305 := bstep (se 2 (by rfl) ⟨1672614, by rfl⟩ : syracuseStep 4460305 = 3345229) B3345229
theorem B35278645 : Blo 1762082 35278645 := bstep (se 5 (by rfl) ⟨1653686, by rfl⟩ : syracuseStep 35278645 = 3307373) B3307373
theorem B3968945 : Blo 1762082 3968945 := bstep (se 2 (by rfl) ⟨1488354, by rfl⟩ : syracuseStep 3968945 = 2976709) B2976709
theorem B3968963 : Blo 1762082 3968963 := bstep (se 1 (by rfl) ⟨2976722, by rfl⟩ : syracuseStep 3968963 = 5953445) B5953445
theorem B5951501 : Blo 1762082 5951501 := bstep (se 3 (by rfl) ⟨1115906, by rfl⟩ : syracuseStep 5951501 = 2231813) B2231813
theorem B4460579 : Blo 1762082 4460579 := bstep (se 1 (by rfl) ⟨3345434, by rfl⟩ : syracuseStep 4460579 = 6690869) B6690869
theorem B2232355 : Blo 1762082 2232355 := bstep (se 1 (by rfl) ⟨1674266, by rfl⟩ : syracuseStep 2232355 = 3348533) B3348533
theorem B5951555 : Blo 1762082 5951555 := bstep (se 1 (by rfl) ⟨4463666, by rfl⟩ : syracuseStep 5951555 = 8927333) B8927333
theorem B3764323 : Blo 1762082 3764323 := bstep (se 1 (by rfl) ⟨2823242, by rfl⟩ : syracuseStep 3764323 = 5646485) B5646485
theorem B2232451 : Blo 1762082 2232451 := bstep (se 1 (by rfl) ⟨1674338, by rfl⟩ : syracuseStep 2232451 = 3348677) B3348677
theorem B2510995 : Blo 1762082 2510995 := bstep (se 1 (by rfl) ⟨1883246, by rfl⟩ : syracuseStep 2510995 = 3766493) B3766493
theorem B5648561 : Blo 1762082 5648561 := bstep (se 2 (by rfl) ⟨2118210, by rfl⟩ : syracuseStep 5648561 = 4236421) B4236421
theorem B8925389 : Blo 1762082 8925389 := bstep (se 3 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 8925389 = 3347021) B3347021
theorem B4460771 : Blo 1762082 4460771 := bstep (se 1 (by rfl) ⟨3345578, by rfl⟩ : syracuseStep 4460771 = 6691157) B6691157
theorem B5648611 : Blo 1762082 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B6697187 : Blo 1762082 6697187 := bstep (se 1 (by rfl) ⟨5022890, by rfl⟩ : syracuseStep 6697187 = 10045781) B10045781
theorem B6697201 : Blo 1762082 6697201 := bstep (se 2 (by rfl) ⟨2511450, by rfl⟩ : syracuseStep 6697201 = 5022901) B5022901
theorem B6787405 : Blo 1762082 6787405 := bstep (se 3 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 6787405 = 2545277) B2545277
theorem B5951825 : Blo 1762082 5951825 := bstep (se 2 (by rfl) ⟨2231934, by rfl⟩ : syracuseStep 5951825 = 4463869) B4463869
theorem B2822563 : Blo 1762082 2822563 := bstep (se 1 (by rfl) ⟨2116922, by rfl⟩ : syracuseStep 2822563 = 4233845) B4233845
theorem B2822609 : Blo 1762082 2822609 := bstep (se 2 (by rfl) ⟨1058478, by rfl⟩ : syracuseStep 2822609 = 2116957) B2116957
theorem B3346915 : Blo 1762082 3346915 := bstep (se 1 (by rfl) ⟨2510186, by rfl⟩ : syracuseStep 3346915 = 5020373) B5020373
theorem B2118163 : Blo 1762082 2118163 := bstep (se 1 (by rfl) ⟨1588622, by rfl⟩ : syracuseStep 2118163 = 3177245) B3177245
theorem B3347075 : Blo 1762082 3347075 := bstep (se 1 (by rfl) ⟨2510306, by rfl⟩ : syracuseStep 3347075 = 5020613) B5020613
theorem B10039949 : Blo 1762082 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B4133603 : Blo 1762082 4133603 := bstep (se 1 (by rfl) ⟨3100202, by rfl⟩ : syracuseStep 4133603 = 6200405) B6200405
theorem B61092629 : Blo 1762082 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B5362499 : Blo 1762082 5362499 := bstep (se 1 (by rfl) ⟨4021874, by rfl⟩ : syracuseStep 5362499 = 8043749) B8043749
theorem B5952365 : Blo 1762082 5952365 := bstep (se 3 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 5952365 = 2232137) B2232137
theorem B19059569 : Blo 1762082 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B5952419 : Blo 1762082 5952419 := bstep (se 1 (by rfl) ⟨4464314, by rfl⟩ : syracuseStep 5952419 = 8928629) B8928629
theorem B5018573 : Blo 1762082 5018573 := bstep (se 3 (by rfl) ⟨940982, by rfl⟩ : syracuseStep 5018573 = 1881965) B1881965
theorem B2823121 : Blo 1762082 2823121 := bstep (se 2 (by rfl) ⟨1058670, by rfl⟩ : syracuseStep 2823121 = 2117341) B2117341
theorem B6034499 : Blo 1762082 6034499 := bstep (se 1 (by rfl) ⟨4525874, by rfl⟩ : syracuseStep 6034499 = 9051749) B9051749
theorem B5018755 : Blo 1762082 5018755 := bstep (se 1 (by rfl) ⟨3764066, by rfl⟩ : syracuseStep 5018755 = 7528133) B7528133
theorem B4461713 : Blo 1762082 4461713 := bstep (se 2 (by rfl) ⟨1673142, by rfl⟩ : syracuseStep 4461713 = 3346285) B3346285
theorem B5952689 : Blo 1762082 5952689 := bstep (se 2 (by rfl) ⟨2232258, by rfl⟩ : syracuseStep 5952689 = 4464517) B4464517
theorem B2643137 : Blo 1762082 2643137 := bstep (se 2 (by rfl) ⟨991176, by rfl⟩ : syracuseStep 2643137 = 1982353) B1982353
theorem B4461763 : Blo 1762082 4461763 := bstep (se 1 (by rfl) ⟨3346322, by rfl⟩ : syracuseStep 4461763 = 6692645) B6692645
theorem B2643155 : Blo 1762082 2643155 := bstep (se 1 (by rfl) ⟨1982366, by rfl⟩ : syracuseStep 2643155 = 3964733) B3964733
theorem B2118883 : Blo 1762082 2118883 := bstep (se 1 (by rfl) ⟨1589162, by rfl⟩ : syracuseStep 2118883 = 3178325) B3178325
theorem B2643185 : Blo 1762082 2643185 := bstep (se 2 (by rfl) ⟨991194, by rfl⟩ : syracuseStep 2643185 = 1982389) B1982389
theorem B2643203 : Blo 1762082 2643203 := bstep (se 1 (by rfl) ⟨1982402, by rfl⟩ : syracuseStep 2643203 = 3964805) B3964805
theorem B2643233 : Blo 1762082 2643233 := bstep (se 2 (by rfl) ⟨991212, by rfl⟩ : syracuseStep 2643233 = 1982425) B1982425
theorem B5018915 : Blo 1762082 5018915 := bstep (se 1 (by rfl) ⟨3764186, by rfl⟩ : syracuseStep 5018915 = 7528373) B7528373
theorem B3175729 : Blo 1762082 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B2643251 : Blo 1762082 2643251 := bstep (se 1 (by rfl) ⟨1982438, by rfl⟩ : syracuseStep 2643251 = 3964877) B3964877
theorem B2118979 : Blo 1762082 2118979 := bstep (se 1 (by rfl) ⟨1589234, by rfl⟩ : syracuseStep 2118979 = 3178469) B3178469
theorem B13382981 : Blo 1762082 13382981 := bstep (se 4 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 13382981 = 2509309) B2509309
theorem B2643281 : Blo 1762082 2643281 := bstep (se 2 (by rfl) ⟨991230, by rfl⟩ : syracuseStep 2643281 = 1982461) B1982461
theorem B4461905 : Blo 1762082 4461905 := bstep (se 2 (by rfl) ⟨1673214, by rfl⟩ : syracuseStep 4461905 = 3346429) B3346429
theorem B2643299 : Blo 1762082 2643299 := bstep (se 1 (by rfl) ⟨1982474, by rfl⟩ : syracuseStep 2643299 = 3964949) B3964949
theorem B2643329 : Blo 1762082 2643329 := bstep (se 2 (by rfl) ⟨991248, by rfl⟩ : syracuseStep 2643329 = 1982497) B1982497
theorem B2643347 : Blo 1762082 2643347 := bstep (se 1 (by rfl) ⟨1982510, by rfl⟩ : syracuseStep 2643347 = 3965021) B3965021
theorem B2643377 : Blo 1762082 2643377 := bstep (se 2 (by rfl) ⟨991266, by rfl⟩ : syracuseStep 2643377 = 1982533) B1982533
theorem B5649841 : Blo 1762082 5649841 := bstep (se 2 (by rfl) ⟨2118690, by rfl⟩ : syracuseStep 5649841 = 4237381) B4237381
theorem B2643395 : Blo 1762082 2643395 := bstep (se 1 (by rfl) ⟨1982546, by rfl⟩ : syracuseStep 2643395 = 3965093) B3965093
theorem B2643425 : Blo 1762082 2643425 := bstep (se 2 (by rfl) ⟨991284, by rfl⟩ : syracuseStep 2643425 = 1982569) B1982569
theorem B2823665 : Blo 1762082 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B2643443 : Blo 1762082 2643443 := bstep (se 1 (by rfl) ⟨1982582, by rfl⟩ : syracuseStep 2643443 = 3965165) B3965165
theorem B2643473 : Blo 1762082 2643473 := bstep (se 2 (by rfl) ⟨991302, by rfl⟩ : syracuseStep 2643473 = 1982605) B1982605
theorem B2643491 : Blo 1762082 2643491 := bstep (se 1 (by rfl) ⟨1982618, by rfl⟩ : syracuseStep 2643491 = 3965237) B3965237
theorem B10040881 : Blo 1762082 10040881 := bstep (se 2 (by rfl) ⟨3765330, by rfl⟩ : syracuseStep 10040881 = 7530661) B7530661
theorem B3765809 : Blo 1762082 3765809 := bstep (se 2 (by rfl) ⟨1412178, by rfl⟩ : syracuseStep 3765809 = 2824357) B2824357
theorem B2643521 : Blo 1762082 2643521 := bstep (se 2 (by rfl) ⟨991320, by rfl⟩ : syracuseStep 2643521 = 1982641) B1982641
theorem B3765827 : Blo 1762082 3765827 := bstep (se 1 (by rfl) ⟨2824370, by rfl⟩ : syracuseStep 3765827 = 5648741) B5648741
theorem B2643539 : Blo 1762082 2643539 := bstep (se 1 (by rfl) ⟨1982654, by rfl⟩ : syracuseStep 2643539 = 3965309) B3965309
theorem B2643569 : Blo 1762082 2643569 := bstep (se 2 (by rfl) ⟨991338, by rfl⟩ : syracuseStep 2643569 = 1982677) B1982677
theorem B18347633 : Blo 1762082 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B2643587 : Blo 1762082 2643587 := bstep (se 1 (by rfl) ⟨1982690, by rfl⟩ : syracuseStep 2643587 = 3965381) B3965381
theorem B2643617 : Blo 1762082 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B3348145 : Blo 1762082 3348145 := bstep (se 2 (by rfl) ⟨1255554, by rfl⟩ : syracuseStep 3348145 = 2511109) B2511109
theorem B2643635 : Blo 1762082 2643635 := bstep (se 1 (by rfl) ⟨1982726, by rfl⟩ : syracuseStep 2643635 = 3965453) B3965453
theorem B5953229 : Blo 1762082 5953229 := bstep (se 3 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 5953229 = 2232461) B2232461
theorem B2643665 : Blo 1762082 2643665 := bstep (se 2 (by rfl) ⟨991374, by rfl⟩ : syracuseStep 2643665 = 1982749) B1982749
theorem B1881811 : Blo 1762082 1881811 := bstep (se 1 (by rfl) ⟨1411358, by rfl⟩ : syracuseStep 1881811 = 2822717) B2822717
theorem B2643683 : Blo 1762082 2643683 := bstep (se 1 (by rfl) ⟨1982762, by rfl⟩ : syracuseStep 2643683 = 3965525) B3965525
theorem B2545393 : Blo 1762082 2545393 := bstep (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) B1909045
theorem B2643713 : Blo 1762082 2643713 := bstep (se 2 (by rfl) ⟨991392, by rfl⟩ : syracuseStep 2643713 = 1982785) B1982785
theorem B5953283 : Blo 1762082 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B2643731 : Blo 1762082 2643731 := bstep (se 1 (by rfl) ⟨1982798, by rfl⟩ : syracuseStep 2643731 = 3965597) B3965597
theorem B2643761 : Blo 1762082 2643761 := bstep (se 2 (by rfl) ⟨991410, by rfl⟩ : syracuseStep 2643761 = 1982821) B1982821
theorem B2643779 : Blo 1762082 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B2643809 : Blo 1762082 2643809 := bstep (se 2 (by rfl) ⟨991428, by rfl⟩ : syracuseStep 2643809 = 1982857) B1982857
theorem B13391729 : Blo 1762082 13391729 := bstep (se 2 (by rfl) ⟨5021898, by rfl⟩ : syracuseStep 13391729 = 10043797) B10043797
theorem B2643827 : Blo 1762082 2643827 := bstep (se 1 (by rfl) ⟨1982870, by rfl⟩ : syracuseStep 2643827 = 3965741) B3965741
theorem B6690701 : Blo 1762082 6690701 := bstep (se 3 (by rfl) ⟨1254506, by rfl⟩ : syracuseStep 6690701 = 2509013) B2509013
theorem B2643857 : Blo 1762082 2643857 := bstep (se 2 (by rfl) ⟨991446, by rfl⟩ : syracuseStep 2643857 = 1982893) B1982893
theorem B2643875 : Blo 1762082 2643875 := bstep (se 1 (by rfl) ⟨1982906, by rfl⟩ : syracuseStep 2643875 = 3965813) B3965813
theorem B2643905 : Blo 1762082 2643905 := bstep (se 2 (by rfl) ⟨991464, by rfl⟩ : syracuseStep 2643905 = 1982929) B1982929
theorem B11302861 : Blo 1762082 11302861 := bstep (se 3 (by rfl) ⟨2119286, by rfl⟩ : syracuseStep 11302861 = 4238573) B4238573
theorem B2643923 : Blo 1762082 2643923 := bstep (se 1 (by rfl) ⟨1982942, by rfl⟩ : syracuseStep 2643923 = 3965885) B3965885
theorem B2643953 : Blo 1762082 2643953 := bstep (se 2 (by rfl) ⟨991482, by rfl⟩ : syracuseStep 2643953 = 1982965) B1982965
theorem B2643971 : Blo 1762082 2643971 := bstep (se 1 (by rfl) ⟨1982978, by rfl⟩ : syracuseStep 2643971 = 3965957) B3965957
theorem B4413457 : Blo 1762082 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B5953553 : Blo 1762082 5953553 := bstep (se 2 (by rfl) ⟨2232582, by rfl⟩ : syracuseStep 5953553 = 4465165) B4465165
theorem B2644001 : Blo 1762082 2644001 := bstep (se 2 (by rfl) ⟨991500, by rfl⟩ : syracuseStep 2644001 = 1983001) B1983001
theorem B2644019 : Blo 1762082 2644019 := bstep (se 1 (by rfl) ⟨1983014, by rfl⟩ : syracuseStep 2644019 = 3966029) B3966029
theorem B2644049 : Blo 1762082 2644049 := bstep (se 2 (by rfl) ⟨991518, by rfl⟩ : syracuseStep 2644049 = 1983037) B1983037
theorem B2644067 : Blo 1762082 2644067 := bstep (se 1 (by rfl) ⟨1983050, by rfl⟩ : syracuseStep 2644067 = 3966101) B3966101
theorem B2644097 : Blo 1762082 2644097 := bstep (se 2 (by rfl) ⟨991536, by rfl⟩ : syracuseStep 2644097 = 1983073) B1983073
theorem B2644115 : Blo 1762082 2644115 := bstep (se 1 (by rfl) ⟨1983086, by rfl⟩ : syracuseStep 2644115 = 3966173) B3966173
theorem B2644145 : Blo 1762082 2644145 := bstep (se 2 (by rfl) ⟨991554, by rfl⟩ : syracuseStep 2644145 = 1983109) B1983109
theorem B2644163 : Blo 1762082 2644163 := bstep (se 1 (by rfl) ⟨1983122, by rfl⟩ : syracuseStep 2644163 = 3966245) B3966245
theorem B2644193 : Blo 1762082 2644193 := bstep (se 2 (by rfl) ⟨991572, by rfl⟩ : syracuseStep 2644193 = 1983145) B1983145
theorem B2644211 : Blo 1762082 2644211 := bstep (se 1 (by rfl) ⟨1983158, by rfl⟩ : syracuseStep 2644211 = 3966317) B3966317
theorem B2644241 : Blo 1762082 2644241 := bstep (se 2 (by rfl) ⟨991590, by rfl⟩ : syracuseStep 2644241 = 1983181) B1983181
theorem B2644259 : Blo 1762082 2644259 := bstep (se 1 (by rfl) ⟨1983194, by rfl⟩ : syracuseStep 2644259 = 3966389) B3966389
theorem B7534883 : Blo 1762082 7534883 := bstep (se 1 (by rfl) ⟨5651162, by rfl⟩ : syracuseStep 7534883 = 11302325) B11302325
theorem B4462897 : Blo 1762082 4462897 := bstep (se 2 (by rfl) ⟨1673586, by rfl⟩ : syracuseStep 4462897 = 3347173) B3347173
theorem B2644289 : Blo 1762082 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B1882435 : Blo 1762082 1882435 := bstep (se 1 (by rfl) ⟨1411826, by rfl⟩ : syracuseStep 1882435 = 2823653) B2823653
theorem B5019985 : Blo 1762082 5019985 := bstep (se 2 (by rfl) ⟨1882494, by rfl⟩ : syracuseStep 5019985 = 3764989) B3764989
theorem B2644307 : Blo 1762082 2644307 := bstep (se 1 (by rfl) ⟨1983230, by rfl⟩ : syracuseStep 2644307 = 3966461) B3966461
theorem B2644337 : Blo 1762082 2644337 := bstep (se 2 (by rfl) ⟨991626, by rfl⟩ : syracuseStep 2644337 = 1983253) B1983253
theorem B2644355 : Blo 1762082 2644355 := bstep (se 1 (by rfl) ⟨1983266, by rfl⟩ : syracuseStep 2644355 = 3966533) B3966533
theorem B25409933 : Blo 1762082 25409933 := bstep (se 3 (by rfl) ⟨4764362, by rfl⟩ : syracuseStep 25409933 = 9528725) B9528725
theorem B2644385 : Blo 1762082 2644385 := bstep (se 2 (by rfl) ⟨991644, by rfl⟩ : syracuseStep 2644385 = 1983289) B1983289
theorem B2324899 : Blo 1762082 2324899 := bstep (se 1 (by rfl) ⟨1743674, by rfl⟩ : syracuseStep 2324899 = 3487349) B3487349
theorem B5724589 : Blo 1762082 5724589 := bstep (se 3 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 5724589 = 2146721) B2146721
theorem B2644403 : Blo 1762082 2644403 := bstep (se 1 (by rfl) ⟨1983302, by rfl⟩ : syracuseStep 2644403 = 3966605) B3966605
theorem B2824627 : Blo 1762082 2824627 := bstep (se 1 (by rfl) ⟨2118470, by rfl⟩ : syracuseStep 2824627 = 4236941) B4236941
theorem B2644433 : Blo 1762082 2644433 := bstep (se 2 (by rfl) ⟨991662, by rfl⟩ : syracuseStep 2644433 = 1983325) B1983325
theorem B2644451 : Blo 1762082 2644451 := bstep (se 1 (by rfl) ⟨1983338, by rfl⟩ : syracuseStep 2644451 = 3966677) B3966677
theorem B2644481 : Blo 1762082 2644481 := bstep (se 2 (by rfl) ⟨991680, by rfl⟩ : syracuseStep 2644481 = 1983361) B1983361
theorem B2644499 : Blo 1762082 2644499 := bstep (se 1 (by rfl) ⟨1983374, by rfl⟩ : syracuseStep 2644499 = 3966749) B3966749
theorem B2644529 : Blo 1762082 2644529 := bstep (se 2 (by rfl) ⟨991698, by rfl⟩ : syracuseStep 2644529 = 1983397) B1983397
theorem B77290037 : Blo 1762082 77290037 := bstep (se 5 (by rfl) ⟨3622970, by rfl⟩ : syracuseStep 77290037 = 7245941) B7245941
theorem B2644547 : Blo 1762082 2644547 := bstep (se 1 (by rfl) ⟨1983410, by rfl⟩ : syracuseStep 2644547 = 3966821) B3966821
theorem B4463171 : Blo 1762082 4463171 := bstep (se 1 (by rfl) ⟨3347378, by rfl⟩ : syracuseStep 4463171 = 6694757) B6694757
theorem B5651021 : Blo 1762082 5651021 := bstep (se 3 (by rfl) ⟨1059566, by rfl⟩ : syracuseStep 5651021 = 2119133) B2119133
theorem B2644577 : Blo 1762082 2644577 := bstep (se 2 (by rfl) ⟨991716, by rfl⟩ : syracuseStep 2644577 = 1983433) B1983433
theorem B2644595 : Blo 1762082 2644595 := bstep (se 1 (by rfl) ⟨1983446, by rfl⟩ : syracuseStep 2644595 = 3966893) B3966893
theorem B2644625 : Blo 1762082 2644625 := bstep (se 2 (by rfl) ⟨991734, by rfl⟩ : syracuseStep 2644625 = 1983469) B1983469
theorem B2644643 : Blo 1762082 2644643 := bstep (se 1 (by rfl) ⟨1983482, by rfl⟩ : syracuseStep 2644643 = 3966965) B3966965
theorem B2824883 : Blo 1762082 2824883 := bstep (se 1 (by rfl) ⟨2118662, by rfl⟩ : syracuseStep 2824883 = 4237325) B4237325
theorem B2644673 : Blo 1762082 2644673 := bstep (se 2 (by rfl) ⟨991752, by rfl⟩ : syracuseStep 2644673 = 1983505) B1983505
theorem B2644691 : Blo 1762082 2644691 := bstep (se 1 (by rfl) ⟨1983518, by rfl⟩ : syracuseStep 2644691 = 3967037) B3967037
theorem B8043235 : Blo 1762082 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B2644721 : Blo 1762082 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B16947953 : Blo 1762082 16947953 := bstep (se 2 (by rfl) ⟨6355482, by rfl⟩ : syracuseStep 16947953 = 12710965) B12710965
theorem B2644739 : Blo 1762082 2644739 := bstep (se 1 (by rfl) ⟨1983554, by rfl⟩ : syracuseStep 2644739 = 3967109) B3967109
theorem B4463363 : Blo 1762082 4463363 := bstep (se 1 (by rfl) ⟨3347522, by rfl⟩ : syracuseStep 4463363 = 6695045) B6695045
theorem B3767057 : Blo 1762082 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2644769 : Blo 1762082 2644769 := bstep (se 2 (by rfl) ⟨991788, by rfl⟩ : syracuseStep 2644769 = 1983577) B1983577
theorem B2644787 : Blo 1762082 2644787 := bstep (se 1 (by rfl) ⟨1983590, by rfl⟩ : syracuseStep 2644787 = 3967181) B3967181
theorem B2644817 : Blo 1762082 2644817 := bstep (se 2 (by rfl) ⟨991806, by rfl⟩ : syracuseStep 2644817 = 1983613) B1983613
theorem B2644835 : Blo 1762082 2644835 := bstep (se 1 (by rfl) ⟨1983626, by rfl⟩ : syracuseStep 2644835 = 3967253) B3967253
theorem B2644865 : Blo 1762082 2644865 := bstep (se 2 (by rfl) ⟨991824, by rfl⟩ : syracuseStep 2644865 = 1983649) B1983649
theorem B2644883 : Blo 1762082 2644883 := bstep (se 1 (by rfl) ⟨1983662, by rfl⟩ : syracuseStep 2644883 = 3967325) B3967325
theorem B2644913 : Blo 1762082 2644913 := bstep (se 2 (by rfl) ⟨991842, by rfl⟩ : syracuseStep 2644913 = 1983685) B1983685
theorem B2644931 : Blo 1762082 2644931 := bstep (se 1 (by rfl) ⟨1983698, by rfl⟩ : syracuseStep 2644931 = 3967397) B3967397
theorem B2644961 : Blo 1762082 2644961 := bstep (se 2 (by rfl) ⟨991860, by rfl⟩ : syracuseStep 2644961 = 1983721) B1983721
theorem B10042339 : Blo 1762082 10042339 := bstep (se 1 (by rfl) ⟨7531754, by rfl⟩ : syracuseStep 10042339 = 15063509) B15063509
theorem B2382835 : Blo 1762082 2382835 := bstep (se 1 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 2382835 = 3574253) B3574253
theorem B2644979 : Blo 1762082 2644979 := bstep (se 1 (by rfl) ⟨1983734, by rfl⟩ : syracuseStep 2644979 = 3967469) B3967469
theorem B2645009 : Blo 1762082 2645009 := bstep (se 2 (by rfl) ⟨991878, by rfl⟩ : syracuseStep 2645009 = 1983757) B1983757
theorem B2645027 : Blo 1762082 2645027 := bstep (se 1 (by rfl) ⟨1983770, by rfl⟩ : syracuseStep 2645027 = 3967541) B3967541
theorem B8928305 : Blo 1762082 8928305 := bstep (se 2 (by rfl) ⟨3348114, by rfl⟩ : syracuseStep 8928305 = 6696229) B6696229
theorem B2645057 : Blo 1762082 2645057 := bstep (se 2 (by rfl) ⟨991896, by rfl⟩ : syracuseStep 2645057 = 1983793) B1983793
theorem B2645075 : Blo 1762082 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B6438001 : Blo 1762082 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B2382961 : Blo 1762082 2382961 := bstep (se 2 (by rfl) ⟨893610, by rfl⟩ : syracuseStep 2382961 = 1787221) B1787221
theorem B2645105 : Blo 1762082 2645105 := bstep (se 2 (by rfl) ⟨991914, by rfl⟩ : syracuseStep 2645105 = 1983829) B1983829
theorem B2645123 : Blo 1762082 2645123 := bstep (se 1 (by rfl) ⟨1983842, by rfl⟩ : syracuseStep 2645123 = 3967685) B3967685
theorem B2645153 : Blo 1762082 2645153 := bstep (se 2 (by rfl) ⟨991932, by rfl⟩ : syracuseStep 2645153 = 1983865) B1983865
theorem B2645171 : Blo 1762082 2645171 := bstep (se 1 (by rfl) ⟨1983878, by rfl⟩ : syracuseStep 2645171 = 3967757) B3967757
theorem B2645201 : Blo 1762082 2645201 := bstep (se 2 (by rfl) ⟨991950, by rfl⟩ : syracuseStep 2645201 = 1983901) B1983901
theorem B21445859 : Blo 1762082 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B2645219 : Blo 1762082 2645219 := bstep (se 1 (by rfl) ⟨1983914, by rfl⟩ : syracuseStep 2645219 = 3967829) B3967829
theorem B4234481 : Blo 1762082 4234481 := bstep (se 2 (by rfl) ⟨1587930, by rfl⟩ : syracuseStep 4234481 = 3175861) B3175861
theorem B2645249 : Blo 1762082 2645249 := bstep (se 2 (by rfl) ⟨991968, by rfl⟩ : syracuseStep 2645249 = 1983937) B1983937
theorem B2645267 : Blo 1762082 2645267 := bstep (se 1 (by rfl) ⟨1983950, by rfl⟩ : syracuseStep 2645267 = 3967901) B3967901
theorem B2645297 : Blo 1762082 2645297 := bstep (se 2 (by rfl) ⟨991986, by rfl⟩ : syracuseStep 2645297 = 1983973) B1983973
theorem B2645315 : Blo 1762082 2645315 := bstep (se 1 (by rfl) ⟨1983986, by rfl⟩ : syracuseStep 2645315 = 3967973) B3967973
theorem B2645345 : Blo 1762082 2645345 := bstep (se 2 (by rfl) ⟨992004, by rfl⟩ : syracuseStep 2645345 = 1984009) B1984009
theorem B2645363 : Blo 1762082 2645363 := bstep (se 1 (by rfl) ⟨1984022, by rfl⟩ : syracuseStep 2645363 = 3968045) B3968045
theorem B2825587 : Blo 1762082 2825587 := bstep (se 1 (by rfl) ⟨2119190, by rfl⟩ : syracuseStep 2825587 = 4238381) B4238381
theorem B2645393 : Blo 1762082 2645393 := bstep (se 2 (by rfl) ⟨992022, by rfl⟩ : syracuseStep 2645393 = 1984045) B1984045
theorem B2645411 : Blo 1762082 2645411 := bstep (se 1 (by rfl) ⟨1984058, by rfl⟩ : syracuseStep 2645411 = 3968117) B3968117
theorem B2645441 : Blo 1762082 2645441 := bstep (se 2 (by rfl) ⟨992040, by rfl⟩ : syracuseStep 2645441 = 1984081) B1984081
theorem B2645459 : Blo 1762082 2645459 := bstep (se 1 (by rfl) ⟨1984094, by rfl⟩ : syracuseStep 2645459 = 3968189) B3968189
theorem B10042865 : Blo 1762082 10042865 := bstep (se 2 (by rfl) ⟨3766074, by rfl⟩ : syracuseStep 10042865 = 7532149) B7532149
theorem B2645489 : Blo 1762082 2645489 := bstep (se 2 (by rfl) ⟨992058, by rfl⟩ : syracuseStep 2645489 = 1984117) B1984117
theorem B2645507 : Blo 1762082 2645507 := bstep (se 1 (by rfl) ⟨1984130, by rfl⟩ : syracuseStep 2645507 = 3968261) B3968261
theorem B2645537 : Blo 1762082 2645537 := bstep (se 2 (by rfl) ⟨992076, by rfl⟩ : syracuseStep 2645537 = 1984153) B1984153
theorem B2645555 : Blo 1762082 2645555 := bstep (se 1 (by rfl) ⟨1984166, by rfl⟩ : syracuseStep 2645555 = 3968333) B3968333
theorem B5021261 : Blo 1762082 5021261 := bstep (se 3 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 5021261 = 1882973) B1882973
theorem B2645585 : Blo 1762082 2645585 := bstep (se 2 (by rfl) ⟨992094, by rfl⟩ : syracuseStep 2645585 = 1984189) B1984189
theorem B2645603 : Blo 1762082 2645603 := bstep (se 1 (by rfl) ⟨1984202, by rfl⟩ : syracuseStep 2645603 = 3968405) B3968405
theorem B7528049 : Blo 1762082 7528049 := bstep (se 2 (by rfl) ⟨2823018, by rfl⟩ : syracuseStep 7528049 = 5646037) B5646037
theorem B2645633 : Blo 1762082 2645633 := bstep (se 2 (by rfl) ⟨992112, by rfl⟩ : syracuseStep 2645633 = 1984225) B1984225
theorem B2645651 : Blo 1762082 2645651 := bstep (se 1 (by rfl) ⟨1984238, by rfl⟩ : syracuseStep 2645651 = 3968477) B3968477
theorem B7528099 : Blo 1762082 7528099 := bstep (se 1 (by rfl) ⟨5646074, by rfl⟩ : syracuseStep 7528099 = 11292149) B11292149
theorem B4464305 : Blo 1762082 4464305 := bstep (se 2 (by rfl) ⟨1674114, by rfl⟩ : syracuseStep 4464305 = 3348229) B3348229
theorem B2645681 : Blo 1762082 2645681 := bstep (se 2 (by rfl) ⟨992130, by rfl⟩ : syracuseStep 2645681 = 1984261) B1984261
theorem B22585013 : Blo 1762082 22585013 := bstep (se 5 (by rfl) ⟨1058672, by rfl⟩ : syracuseStep 22585013 = 2117345) B2117345
theorem B2645699 : Blo 1762082 2645699 := bstep (se 1 (by rfl) ⟨1984274, by rfl⟩ : syracuseStep 2645699 = 3968549) B3968549
theorem B2645729 : Blo 1762082 2645729 := bstep (se 2 (by rfl) ⟨992148, by rfl⟩ : syracuseStep 2645729 = 1984297) B1984297
theorem B4464355 : Blo 1762082 4464355 := bstep (se 1 (by rfl) ⟨3348266, by rfl⟩ : syracuseStep 4464355 = 6696533) B6696533
theorem B2645747 : Blo 1762082 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B5021443 : Blo 1762082 5021443 := bstep (se 1 (by rfl) ⟨3766082, by rfl⟩ : syracuseStep 5021443 = 7532165) B7532165
theorem B2645777 : Blo 1762082 2645777 := bstep (se 2 (by rfl) ⟨992166, by rfl⟩ : syracuseStep 2645777 = 1984333) B1984333
theorem B2645795 : Blo 1762082 2645795 := bstep (se 1 (by rfl) ⟨1984346, by rfl⟩ : syracuseStep 2645795 = 3968693) B3968693
theorem B5947181 : Blo 1762082 5947181 := bstep (se 3 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 5947181 = 2230193) B2230193
theorem B5021489 : Blo 1762082 5021489 := bstep (se 2 (by rfl) ⟨1883058, by rfl⟩ : syracuseStep 5021489 = 3766117) B3766117
theorem B2645825 : Blo 1762082 2645825 := bstep (se 2 (by rfl) ⟨992184, by rfl⟩ : syracuseStep 2645825 = 1984369) B1984369
theorem B4235075 : Blo 1762082 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B2973523 : Blo 1762082 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B2645843 : Blo 1762082 2645843 := bstep (se 1 (by rfl) ⟨1984382, by rfl⟩ : syracuseStep 2645843 = 3968765) B3968765
theorem B5947235 : Blo 1762082 5947235 := bstep (se 1 (by rfl) ⟨4460426, by rfl⟩ : syracuseStep 5947235 = 8920853) B8920853
theorem B4464497 : Blo 1762082 4464497 := bstep (se 2 (by rfl) ⟨1674186, by rfl⟩ : syracuseStep 4464497 = 3348373) B3348373
theorem B2645873 : Blo 1762082 2645873 := bstep (se 2 (by rfl) ⟨992202, by rfl⟩ : syracuseStep 2645873 = 1984405) B1984405
theorem B4767619 : Blo 1762082 4767619 := bstep (se 1 (by rfl) ⟨3575714, by rfl⟩ : syracuseStep 4767619 = 7151429) B7151429
theorem B2645891 : Blo 1762082 2645891 := bstep (se 1 (by rfl) ⟨1984418, by rfl⟩ : syracuseStep 2645891 = 3968837) B3968837
theorem B2645921 : Blo 1762082 2645921 := bstep (se 2 (by rfl) ⟨992220, by rfl⟩ : syracuseStep 2645921 = 1984441) B1984441
theorem B1982371 : Blo 1762082 1982371 := bstep (se 1 (by rfl) ⟨1486778, by rfl⟩ : syracuseStep 1982371 = 2973557) B2973557
theorem B4235171 : Blo 1762082 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B2645939 : Blo 1762082 2645939 := bstep (se 1 (by rfl) ⟨1984454, by rfl⟩ : syracuseStep 2645939 = 3968909) B3968909
theorem B6692813 : Blo 1762082 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B2645969 : Blo 1762082 2645969 := bstep (se 2 (by rfl) ⟨992238, by rfl⟩ : syracuseStep 2645969 = 1984477) B1984477
theorem B2973665 : Blo 1762082 2973665 := bstep (se 2 (by rfl) ⟨1115124, by rfl⟩ : syracuseStep 2973665 = 2230249) B2230249
theorem B2645987 : Blo 1762082 2645987 := bstep (se 1 (by rfl) ⟨1984490, by rfl⟩ : syracuseStep 2645987 = 3968981) B3968981
theorem B3964913 : Blo 1762082 3964913 := bstep (se 2 (by rfl) ⟨1486842, by rfl⟩ : syracuseStep 3964913 = 2973685) B2973685
theorem B2973719 : Blo 1762082 2973719 := bstep (se 1 (by rfl) ⟨2230289, by rfl⟩ : syracuseStep 2973719 = 4460579) B4460579
theorem B2646041 : Blo 1762082 2646041 := bstep (se 2 (by rfl) ⟨992265, by rfl⟩ : syracuseStep 2646041 = 1984531) B1984531
theorem B3965003 : Blo 1762082 3965003 := bstep (se 1 (by rfl) ⟨2973752, by rfl⟩ : syracuseStep 3965003 = 5947505) B5947505
theorem B1982551 : Blo 1762082 1982551 := bstep (se 1 (by rfl) ⟨1486913, by rfl⟩ : syracuseStep 1982551 = 2973827) B2973827
theorem B3965057 : Blo 1762082 3965057 := bstep (se 2 (by rfl) ⟨1486896, by rfl⟩ : syracuseStep 3965057 = 2973793) B2973793
theorem B19054723 : Blo 1762082 19054723 := bstep (se 1 (by rfl) ⟨14291042, by rfl⟩ : syracuseStep 19054723 = 28582085) B28582085
theorem B2973847 : Blo 1762082 2973847 := bstep (se 1 (by rfl) ⟨2230385, by rfl⟩ : syracuseStep 2973847 = 4460771) B4460771
theorem B4464791 : Blo 1762082 4464791 := bstep (se 1 (by rfl) ⟨3348593, by rfl⟩ : syracuseStep 4464791 = 6697187) B6697187
theorem B38109365 : Blo 1762082 38109365 := bstep (se 5 (by rfl) ⟨1786376, by rfl⟩ : syracuseStep 38109365 = 3572753) B3572753
theorem B3014873 : Blo 1762082 3014873 := bstep (se 2 (by rfl) ⟨1130577, by rfl⟩ : syracuseStep 3014873 = 2261155) B2261155
theorem B5947613 : Blo 1762082 5947613 := bstep (se 3 (by rfl) ⟨1115177, by rfl⟩ : syracuseStep 5947613 = 2230355) B2230355
theorem B1982731 : Blo 1762082 1982731 := bstep (se 1 (by rfl) ⟨1487048, by rfl⟩ : syracuseStep 1982731 = 2974097) B2974097
theorem B8929601 : Blo 1762082 8929601 := bstep (se 2 (by rfl) ⟨3348600, by rfl⟩ : syracuseStep 8929601 = 6697201) B6697201
theorem B3965273 : Blo 1762082 3965273 := bstep (se 2 (by rfl) ⟨1486977, by rfl⟩ : syracuseStep 3965273 = 2973955) B2973955
theorem B1982839 : Blo 1762082 1982839 := bstep (se 1 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 1982839 = 2974259) B2974259
theorem B3965363 : Blo 1762082 3965363 := bstep (se 1 (by rfl) ⟨2974022, by rfl⟩ : syracuseStep 3965363 = 5948045) B5948045
theorem B6693299 : Blo 1762082 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B6693313 : Blo 1762082 6693313 := bstep (se 2 (by rfl) ⟨2509992, by rfl⟩ : syracuseStep 6693313 = 5019985) B5019985
theorem B3965399 : Blo 1762082 3965399 := bstep (se 1 (by rfl) ⟨2974049, by rfl⟩ : syracuseStep 3965399 = 5948099) B5948099
theorem B2146775 : Blo 1762082 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B1983019 : Blo 1762082 1983019 := bstep (se 1 (by rfl) ⟨1487264, by rfl⟩ : syracuseStep 1983019 = 2974529) B2974529
theorem B12706379 : Blo 1762082 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B3965579 : Blo 1762082 3965579 := bstep (se 1 (by rfl) ⟨2974184, by rfl⟩ : syracuseStep 3965579 = 5948369) B5948369
theorem B1983127 : Blo 1762082 1983127 := bstep (se 1 (by rfl) ⟨1487345, by rfl⟩ : syracuseStep 1983127 = 2974691) B2974691
theorem B3965633 : Blo 1762082 3965633 := bstep (se 2 (by rfl) ⟨1487112, by rfl⟩ : syracuseStep 3965633 = 2974225) B2974225
theorem B4022999 : Blo 1762082 4022999 := bstep (se 1 (by rfl) ⟨3017249, by rfl⟩ : syracuseStep 4022999 = 6034499) B6034499
theorem B2974475 : Blo 1762082 2974475 := bstep (se 1 (by rfl) ⟨2230856, by rfl⟩ : syracuseStep 2974475 = 4461713) B4461713
theorem B1762091 : Blo 1762082 1762091 := bstep (se 1 (by rfl) ⟨1321568, by rfl⟩ : syracuseStep 1762091 = 2643137) B2643137
theorem B1762103 : Blo 1762082 1762103 := bstep (se 1 (by rfl) ⟨1321577, by rfl⟩ : syracuseStep 1762103 = 2643155) B2643155
theorem B1762123 : Blo 1762082 1762123 := bstep (se 1 (by rfl) ⟨1321592, by rfl⟩ : syracuseStep 1762123 = 2643185) B2643185
theorem B1983307 : Blo 1762082 1983307 := bstep (se 1 (by rfl) ⟨1487480, by rfl⟩ : syracuseStep 1983307 = 2974961) B2974961
theorem B1762135 : Blo 1762082 1762135 := bstep (se 1 (by rfl) ⟨1321601, by rfl⟩ : syracuseStep 1762135 = 2643203) B2643203
theorem B1762155 : Blo 1762082 1762155 := bstep (se 1 (by rfl) ⟨1321616, by rfl⟩ : syracuseStep 1762155 = 2643233) B2643233
theorem B1762167 : Blo 1762082 1762167 := bstep (se 1 (by rfl) ⟨1321625, by rfl⟩ : syracuseStep 1762167 = 2643251) B2643251
theorem B8921987 : Blo 1762082 8921987 := bstep (se 1 (by rfl) ⟨6691490, by rfl⟩ : syracuseStep 8921987 = 13382981) B13382981
theorem B1762187 : Blo 1762082 1762187 := bstep (se 1 (by rfl) ⟨1321640, by rfl⟩ : syracuseStep 1762187 = 2643281) B2643281
theorem B2974603 : Blo 1762082 2974603 := bstep (se 1 (by rfl) ⟨2230952, by rfl⟩ : syracuseStep 2974603 = 4461905) B4461905
theorem B5358487 : Blo 1762082 5358487 := bstep (se 1 (by rfl) ⟨4018865, by rfl⟩ : syracuseStep 5358487 = 8037731) B8037731
theorem B1762199 : Blo 1762082 1762199 := bstep (se 1 (by rfl) ⟨1321649, by rfl⟩ : syracuseStep 1762199 = 2643299) B2643299
theorem B3965849 : Blo 1762082 3965849 := bstep (se 2 (by rfl) ⟨1487193, by rfl⟩ : syracuseStep 3965849 = 2974387) B2974387
theorem B1762219 : Blo 1762082 1762219 := bstep (se 1 (by rfl) ⟨1321664, by rfl⟩ : syracuseStep 1762219 = 2643329) B2643329
theorem B1762231 : Blo 1762082 1762231 := bstep (se 1 (by rfl) ⟨1321673, by rfl⟩ : syracuseStep 1762231 = 2643347) B2643347
theorem B1983415 : Blo 1762082 1983415 := bstep (se 1 (by rfl) ⟨1487561, by rfl⟩ : syracuseStep 1983415 = 2975123) B2975123
theorem B1762251 : Blo 1762082 1762251 := bstep (se 1 (by rfl) ⟨1321688, by rfl⟩ : syracuseStep 1762251 = 2643377) B2643377
theorem B1762263 : Blo 1762082 1762263 := bstep (se 1 (by rfl) ⟨1321697, by rfl⟩ : syracuseStep 1762263 = 2643395) B2643395
theorem B1762283 : Blo 1762082 1762283 := bstep (se 1 (by rfl) ⟨1321712, by rfl⟩ : syracuseStep 1762283 = 2643425) B2643425
theorem B3965939 : Blo 1762082 3965939 := bstep (se 1 (by rfl) ⟨2974454, by rfl⟩ : syracuseStep 3965939 = 5948909) B5948909
theorem B1762295 : Blo 1762082 1762295 := bstep (se 1 (by rfl) ⟨1321721, by rfl⟩ : syracuseStep 1762295 = 2643443) B2643443
theorem B1762315 : Blo 1762082 1762315 := bstep (se 1 (by rfl) ⟨1321736, by rfl⟩ : syracuseStep 1762315 = 2643473) B2643473
theorem B67748885 : Blo 1762082 67748885 := bstep (se 6 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 67748885 = 3175729) B3175729
theorem B1762327 : Blo 1762082 1762327 := bstep (se 1 (by rfl) ⟨1321745, by rfl⟩ : syracuseStep 1762327 = 2643491) B2643491
theorem B3965975 : Blo 1762082 3965975 := bstep (se 1 (by rfl) ⟨2974481, by rfl⟩ : syracuseStep 3965975 = 5948963) B5948963
theorem B2974745 : Blo 1762082 2974745 := bstep (se 2 (by rfl) ⟨1115529, by rfl⟩ : syracuseStep 2974745 = 2231059) B2231059
theorem B1762347 : Blo 1762082 1762347 := bstep (se 1 (by rfl) ⟨1321760, by rfl⟩ : syracuseStep 1762347 = 2643521) B2643521
theorem B1762359 : Blo 1762082 1762359 := bstep (se 1 (by rfl) ⟨1321769, by rfl⟩ : syracuseStep 1762359 = 2643539) B2643539
theorem B1762379 : Blo 1762082 1762379 := bstep (se 1 (by rfl) ⟨1321784, by rfl⟩ : syracuseStep 1762379 = 2643569) B2643569
theorem B12231755 : Blo 1762082 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B1762391 : Blo 1762082 1762391 := bstep (se 1 (by rfl) ⟨1321793, by rfl⟩ : syracuseStep 1762391 = 2643587) B2643587
theorem B10036325 : Blo 1762082 10036325 := bstep (se 4 (by rfl) ⟨940905, by rfl⟩ : syracuseStep 10036325 = 1881811) B1881811
theorem B1762411 : Blo 1762082 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1983595 : Blo 1762082 1983595 := bstep (se 1 (by rfl) ⟨1487696, by rfl⟩ : syracuseStep 1983595 = 2975393) B2975393
theorem B1762423 : Blo 1762082 1762423 := bstep (se 1 (by rfl) ⟨1321817, by rfl⟩ : syracuseStep 1762423 = 2643635) B2643635
theorem B1762443 : Blo 1762082 1762443 := bstep (se 1 (by rfl) ⟨1321832, by rfl⟩ : syracuseStep 1762443 = 2643665) B2643665
theorem B1762455 : Blo 1762082 1762455 := bstep (se 1 (by rfl) ⟨1321841, by rfl⟩ : syracuseStep 1762455 = 2643683) B2643683
theorem B2974873 : Blo 1762082 2974873 := bstep (se 2 (by rfl) ⟨1115577, by rfl⟩ : syracuseStep 2974873 = 2231155) B2231155
theorem B1762475 : Blo 1762082 1762475 := bstep (se 1 (by rfl) ⟨1321856, by rfl⟩ : syracuseStep 1762475 = 2643713) B2643713
theorem B1762487 : Blo 1762082 1762487 := bstep (se 1 (by rfl) ⟨1321865, by rfl⟩ : syracuseStep 1762487 = 2643731) B2643731
theorem B1762507 : Blo 1762082 1762507 := bstep (se 1 (by rfl) ⟨1321880, by rfl⟩ : syracuseStep 1762507 = 2643761) B2643761
theorem B3966155 : Blo 1762082 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B1762519 : Blo 1762082 1762519 := bstep (se 1 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 1762519 = 2643779) B2643779
theorem B15262937 : Blo 1762082 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B1983703 : Blo 1762082 1983703 := bstep (se 1 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 1983703 = 2975555) B2975555
theorem B1762539 : Blo 1762082 1762539 := bstep (se 1 (by rfl) ⟨1321904, by rfl⟩ : syracuseStep 1762539 = 2643809) B2643809
theorem B1762551 : Blo 1762082 1762551 := bstep (se 1 (by rfl) ⟨1321913, by rfl⟩ : syracuseStep 1762551 = 2643827) B2643827
theorem B3966209 : Blo 1762082 3966209 := bstep (se 2 (by rfl) ⟨1487328, by rfl⟩ : syracuseStep 3966209 = 2974657) B2974657
theorem B1762571 : Blo 1762082 1762571 := bstep (se 1 (by rfl) ⟨1321928, by rfl⟩ : syracuseStep 1762571 = 2643857) B2643857
theorem B1762583 : Blo 1762082 1762583 := bstep (se 1 (by rfl) ⟨1321937, by rfl⟩ : syracuseStep 1762583 = 2643875) B2643875
theorem B1762603 : Blo 1762082 1762603 := bstep (se 1 (by rfl) ⟨1321952, by rfl⟩ : syracuseStep 1762603 = 2643905) B2643905
theorem B7529773 : Blo 1762082 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B1762615 : Blo 1762082 1762615 := bstep (se 1 (by rfl) ⟨1321961, by rfl⟩ : syracuseStep 1762615 = 2643923) B2643923
theorem B5948747 : Blo 1762082 5948747 := bstep (se 1 (by rfl) ⟨4461560, by rfl⟩ : syracuseStep 5948747 = 8923121) B8923121
theorem B1762635 : Blo 1762082 1762635 := bstep (se 1 (by rfl) ⟨1321976, by rfl⟩ : syracuseStep 1762635 = 2643953) B2643953
theorem B1762647 : Blo 1762082 1762647 := bstep (se 1 (by rfl) ⟨1321985, by rfl⟩ : syracuseStep 1762647 = 2643971) B2643971
theorem B1762667 : Blo 1762082 1762667 := bstep (se 1 (by rfl) ⟨1322000, by rfl⟩ : syracuseStep 1762667 = 2644001) B2644001
theorem B1762679 : Blo 1762082 1762679 := bstep (se 1 (by rfl) ⟨1322009, by rfl⟩ : syracuseStep 1762679 = 2644019) B2644019
theorem B1762699 : Blo 1762082 1762699 := bstep (se 1 (by rfl) ⟨1322024, by rfl⟩ : syracuseStep 1762699 = 2644049) B2644049
theorem B1983883 : Blo 1762082 1983883 := bstep (se 1 (by rfl) ⟨1487912, by rfl⟩ : syracuseStep 1983883 = 2975825) B2975825
theorem B1762711 : Blo 1762082 1762711 := bstep (se 1 (by rfl) ⟨1322033, by rfl⟩ : syracuseStep 1762711 = 2644067) B2644067
theorem B1762731 : Blo 1762082 1762731 := bstep (se 1 (by rfl) ⟨1322048, by rfl⟩ : syracuseStep 1762731 = 2644097) B2644097
theorem B1762743 : Blo 1762082 1762743 := bstep (se 1 (by rfl) ⟨1322057, by rfl⟩ : syracuseStep 1762743 = 2644115) B2644115
theorem B1762763 : Blo 1762082 1762763 := bstep (se 1 (by rfl) ⟨1322072, by rfl⟩ : syracuseStep 1762763 = 2644145) B2644145
theorem B1762775 : Blo 1762082 1762775 := bstep (se 1 (by rfl) ⟨1322081, by rfl⟩ : syracuseStep 1762775 = 2644163) B2644163
theorem B3573209 : Blo 1762082 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B3966425 : Blo 1762082 3966425 := bstep (se 2 (by rfl) ⟨1487409, by rfl⟩ : syracuseStep 3966425 = 2974819) B2974819
theorem B1762795 : Blo 1762082 1762795 := bstep (se 1 (by rfl) ⟨1322096, by rfl⟩ : syracuseStep 1762795 = 2644193) B2644193
theorem B1762807 : Blo 1762082 1762807 := bstep (se 1 (by rfl) ⟨1322105, by rfl⟩ : syracuseStep 1762807 = 2644211) B2644211
theorem B1787383 : Blo 1762082 1787383 := bstep (se 1 (by rfl) ⟨1340537, by rfl⟩ : syracuseStep 1787383 = 2681075) B2681075
theorem B1983991 : Blo 1762082 1983991 := bstep (se 1 (by rfl) ⟨1487993, by rfl⟩ : syracuseStep 1983991 = 2975987) B2975987
theorem B1762827 : Blo 1762082 1762827 := bstep (se 1 (by rfl) ⟨1322120, by rfl⟩ : syracuseStep 1762827 = 2644241) B2644241
theorem B1762839 : Blo 1762082 1762839 := bstep (se 1 (by rfl) ⟨1322129, by rfl⟩ : syracuseStep 1762839 = 2644259) B2644259
theorem B4523543 : Blo 1762082 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B5023255 : Blo 1762082 5023255 := bstep (se 1 (by rfl) ⟨3767441, by rfl⟩ : syracuseStep 5023255 = 7534883) B7534883
theorem B1762859 : Blo 1762082 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B10036781 : Blo 1762082 10036781 := bstep (se 3 (by rfl) ⟨1881896, by rfl⟩ : syracuseStep 10036781 = 3763793) B3763793
theorem B3966515 : Blo 1762082 3966515 := bstep (se 1 (by rfl) ⟨2974886, by rfl⟩ : syracuseStep 3966515 = 5949773) B5949773
theorem B1762871 : Blo 1762082 1762871 := bstep (se 1 (by rfl) ⟨1322153, by rfl⟩ : syracuseStep 1762871 = 2644307) B2644307
theorem B1762891 : Blo 1762082 1762891 := bstep (se 1 (by rfl) ⟨1322168, by rfl⟩ : syracuseStep 1762891 = 2644337) B2644337
theorem B1762903 : Blo 1762082 1762903 := bstep (se 1 (by rfl) ⟨1322177, by rfl⟩ : syracuseStep 1762903 = 2644355) B2644355
theorem B3966551 : Blo 1762082 3966551 := bstep (se 1 (by rfl) ⟨2974913, by rfl⟩ : syracuseStep 3966551 = 5949827) B5949827
theorem B5949017 : Blo 1762082 5949017 := bstep (se 2 (by rfl) ⟨2230881, by rfl⟩ : syracuseStep 5949017 = 4461763) B4461763
theorem B1762923 : Blo 1762082 1762923 := bstep (se 1 (by rfl) ⟨1322192, by rfl⟩ : syracuseStep 1762923 = 2644385) B2644385
theorem B1762935 : Blo 1762082 1762935 := bstep (se 1 (by rfl) ⟨1322201, by rfl⟩ : syracuseStep 1762935 = 2644403) B2644403
theorem B1762955 : Blo 1762082 1762955 := bstep (se 1 (by rfl) ⟨1322216, by rfl⟩ : syracuseStep 1762955 = 2644433) B2644433
theorem B1762967 : Blo 1762082 1762967 := bstep (se 1 (by rfl) ⟨1322225, by rfl⟩ : syracuseStep 1762967 = 2644451) B2644451
theorem B1762987 : Blo 1762082 1762987 := bstep (se 1 (by rfl) ⟨1322240, by rfl⟩ : syracuseStep 1762987 = 2644481) B2644481
theorem B1984171 : Blo 1762082 1984171 := bstep (se 1 (by rfl) ⟨1488128, by rfl⟩ : syracuseStep 1984171 = 2976257) B2976257
theorem B1762999 : Blo 1762082 1762999 := bstep (se 1 (by rfl) ⟨1322249, by rfl⟩ : syracuseStep 1762999 = 2644499) B2644499
theorem B1763019 : Blo 1762082 1763019 := bstep (se 1 (by rfl) ⟨1322264, by rfl⟩ : syracuseStep 1763019 = 2644529) B2644529
theorem B1763031 : Blo 1762082 1763031 := bstep (se 1 (by rfl) ⟨1322273, by rfl⟩ : syracuseStep 1763031 = 2644547) B2644547
theorem B2975447 : Blo 1762082 2975447 := bstep (se 1 (by rfl) ⟨2231585, by rfl⟩ : syracuseStep 2975447 = 4463171) B4463171
theorem B1763051 : Blo 1762082 1763051 := bstep (se 1 (by rfl) ⟨1322288, by rfl⟩ : syracuseStep 1763051 = 2644577) B2644577
theorem B1763063 : Blo 1762082 1763063 := bstep (se 1 (by rfl) ⟨1322297, by rfl⟩ : syracuseStep 1763063 = 2644595) B2644595
theorem B3966731 : Blo 1762082 3966731 := bstep (se 1 (by rfl) ⟨2975048, by rfl⟩ : syracuseStep 3966731 = 5950097) B5950097
theorem B1763083 : Blo 1762082 1763083 := bstep (se 1 (by rfl) ⟨1322312, by rfl⟩ : syracuseStep 1763083 = 2644625) B2644625
theorem B1763095 : Blo 1762082 1763095 := bstep (se 1 (by rfl) ⟨1322321, by rfl⟩ : syracuseStep 1763095 = 2644643) B2644643
theorem B1984279 : Blo 1762082 1984279 := bstep (se 1 (by rfl) ⟨1488209, by rfl⟩ : syracuseStep 1984279 = 2976419) B2976419
theorem B1763115 : Blo 1762082 1763115 := bstep (se 1 (by rfl) ⟨1322336, by rfl⟩ : syracuseStep 1763115 = 2644673) B2644673
theorem B1763127 : Blo 1762082 1763127 := bstep (se 1 (by rfl) ⟨1322345, by rfl⟩ : syracuseStep 1763127 = 2644691) B2644691
theorem B3966785 : Blo 1762082 3966785 := bstep (se 2 (by rfl) ⟨1487544, by rfl⟩ : syracuseStep 3966785 = 2975089) B2975089
theorem B18351937 : Blo 1762082 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B1763147 : Blo 1762082 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B11298635 : Blo 1762082 11298635 := bstep (se 1 (by rfl) ⟨8473976, by rfl⟩ : syracuseStep 11298635 = 16947953) B16947953
theorem B1763159 : Blo 1762082 1763159 := bstep (se 1 (by rfl) ⟨1322369, by rfl⟩ : syracuseStep 1763159 = 2644739) B2644739
theorem B2975575 : Blo 1762082 2975575 := bstep (se 1 (by rfl) ⟨2231681, by rfl⟩ : syracuseStep 2975575 = 4463363) B4463363
theorem B10315613 : Blo 1762082 10315613 := bstep (se 3 (by rfl) ⟨1934177, by rfl⟩ : syracuseStep 10315613 = 3868355) B3868355
theorem B1763179 : Blo 1762082 1763179 := bstep (se 1 (by rfl) ⟨1322384, by rfl⟩ : syracuseStep 1763179 = 2644769) B2644769
theorem B1763191 : Blo 1762082 1763191 := bstep (se 1 (by rfl) ⟨1322393, by rfl⟩ : syracuseStep 1763191 = 2644787) B2644787
theorem B1763211 : Blo 1762082 1763211 := bstep (se 1 (by rfl) ⟨1322408, by rfl⟩ : syracuseStep 1763211 = 2644817) B2644817
theorem B1763223 : Blo 1762082 1763223 := bstep (se 1 (by rfl) ⟨1322417, by rfl⟩ : syracuseStep 1763223 = 2644835) B2644835
theorem B1763243 : Blo 1762082 1763243 := bstep (se 1 (by rfl) ⟨1322432, by rfl⟩ : syracuseStep 1763243 = 2644865) B2644865
theorem B12707761 : Blo 1762082 12707761 := bstep (se 2 (by rfl) ⟨4765410, by rfl⟩ : syracuseStep 12707761 = 9530821) B9530821
theorem B1763255 : Blo 1762082 1763255 := bstep (se 1 (by rfl) ⟨1322441, by rfl⟩ : syracuseStep 1763255 = 2644883) B2644883
theorem B1763275 : Blo 1762082 1763275 := bstep (se 1 (by rfl) ⟨1322456, by rfl⟩ : syracuseStep 1763275 = 2644913) B2644913
theorem B1984459 : Blo 1762082 1984459 := bstep (se 1 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 1984459 = 2976689) B2976689
theorem B1763287 : Blo 1762082 1763287 := bstep (se 1 (by rfl) ⟨1322465, by rfl⟩ : syracuseStep 1763287 = 2644931) B2644931
theorem B1763307 : Blo 1762082 1763307 := bstep (se 1 (by rfl) ⟨1322480, by rfl⟩ : syracuseStep 1763307 = 2644961) B2644961
theorem B1763319 : Blo 1762082 1763319 := bstep (se 1 (by rfl) ⟨1322489, by rfl⟩ : syracuseStep 1763319 = 2644979) B2644979
theorem B16091141 : Blo 1762082 16091141 := bstep (se 4 (by rfl) ⟨1508544, by rfl⟩ : syracuseStep 16091141 = 3017089) B3017089
theorem B1763339 : Blo 1762082 1763339 := bstep (se 1 (by rfl) ⟨1322504, by rfl⟩ : syracuseStep 1763339 = 2645009) B2645009
theorem B1763351 : Blo 1762082 1763351 := bstep (se 1 (by rfl) ⟨1322513, by rfl⟩ : syracuseStep 1763351 = 2645027) B2645027
theorem B3967001 : Blo 1762082 3967001 := bstep (se 2 (by rfl) ⟨1487625, by rfl⟩ : syracuseStep 3967001 = 2975251) B2975251
theorem B1763371 : Blo 1762082 1763371 := bstep (se 1 (by rfl) ⟨1322528, by rfl⟩ : syracuseStep 1763371 = 2645057) B2645057
theorem B1763383 : Blo 1762082 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B1984567 : Blo 1762082 1984567 := bstep (se 1 (by rfl) ⟨1488425, by rfl⟩ : syracuseStep 1984567 = 2976851) B2976851
theorem B13387841 : Blo 1762082 13387841 := bstep (se 2 (by rfl) ⟨5020440, by rfl⟩ : syracuseStep 13387841 = 10040881) B10040881
theorem B76236875 : Blo 1762082 76236875 := bstep (se 1 (by rfl) ⟨57177656, by rfl⟩ : syracuseStep 76236875 = 114355313) B114355313
theorem B1763403 : Blo 1762082 1763403 := bstep (se 1 (by rfl) ⟨1322552, by rfl⟩ : syracuseStep 1763403 = 2645105) B2645105
theorem B1763415 : Blo 1762082 1763415 := bstep (se 1 (by rfl) ⟨1322561, by rfl⟩ : syracuseStep 1763415 = 2645123) B2645123
theorem B1763435 : Blo 1762082 1763435 := bstep (se 1 (by rfl) ⟨1322576, by rfl⟩ : syracuseStep 1763435 = 2645153) B2645153
theorem B3967091 : Blo 1762082 3967091 := bstep (se 1 (by rfl) ⟨2975318, by rfl⟩ : syracuseStep 3967091 = 5950637) B5950637
theorem B1763447 : Blo 1762082 1763447 := bstep (se 1 (by rfl) ⟨1322585, by rfl⟩ : syracuseStep 1763447 = 2645171) B2645171
theorem B2230411 : Blo 1762082 2230411 := bstep (se 1 (by rfl) ⟨1672808, by rfl⟩ : syracuseStep 2230411 = 3345617) B3345617
theorem B1763467 : Blo 1762082 1763467 := bstep (se 1 (by rfl) ⟨1322600, by rfl⟩ : syracuseStep 1763467 = 2645201) B2645201
theorem B14297239 : Blo 1762082 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B3967127 : Blo 1762082 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B1763479 : Blo 1762082 1763479 := bstep (se 1 (by rfl) ⟨1322609, by rfl⟩ : syracuseStep 1763479 = 2645219) B2645219
theorem B1763499 : Blo 1762082 1763499 := bstep (se 1 (by rfl) ⟨1322624, by rfl⟩ : syracuseStep 1763499 = 2645249) B2645249
theorem B1763511 : Blo 1762082 1763511 := bstep (se 1 (by rfl) ⟨1322633, by rfl⟩ : syracuseStep 1763511 = 2645267) B2645267
theorem B1763531 : Blo 1762082 1763531 := bstep (se 1 (by rfl) ⟨1322648, by rfl⟩ : syracuseStep 1763531 = 2645297) B2645297
theorem B1763543 : Blo 1762082 1763543 := bstep (se 1 (by rfl) ⟨1322657, by rfl⟩ : syracuseStep 1763543 = 2645315) B2645315
theorem B10037465 : Blo 1762082 10037465 := bstep (se 2 (by rfl) ⟨3764049, by rfl⟩ : syracuseStep 10037465 = 7528099) B7528099
theorem B1763563 : Blo 1762082 1763563 := bstep (se 1 (by rfl) ⟨1322672, by rfl⟩ : syracuseStep 1763563 = 2645345) B2645345
theorem B1763575 : Blo 1762082 1763575 := bstep (se 1 (by rfl) ⟨1322681, by rfl⟩ : syracuseStep 1763575 = 2645363) B2645363
theorem B30132485 : Blo 1762082 30132485 := bstep (se 4 (by rfl) ⟨2824920, by rfl⟩ : syracuseStep 30132485 = 5649841) B5649841
theorem B1763595 : Blo 1762082 1763595 := bstep (se 1 (by rfl) ⟨1322696, by rfl⟩ : syracuseStep 1763595 = 2645393) B2645393
theorem B5949719 : Blo 1762082 5949719 := bstep (se 1 (by rfl) ⟨4462289, by rfl⟩ : syracuseStep 5949719 = 8924579) B8924579
theorem B1763607 : Blo 1762082 1763607 := bstep (se 1 (by rfl) ⟨1322705, by rfl⟩ : syracuseStep 1763607 = 2645411) B2645411
theorem B1763627 : Blo 1762082 1763627 := bstep (se 1 (by rfl) ⟨1322720, by rfl⟩ : syracuseStep 1763627 = 2645441) B2645441
theorem B1763639 : Blo 1762082 1763639 := bstep (se 1 (by rfl) ⟨1322729, by rfl⟩ : syracuseStep 1763639 = 2645459) B2645459
theorem B3393857 : Blo 1762082 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B3967307 : Blo 1762082 3967307 := bstep (se 1 (by rfl) ⟨2975480, by rfl⟩ : syracuseStep 3967307 = 5950961) B5950961
theorem B6695243 : Blo 1762082 6695243 := bstep (se 1 (by rfl) ⟨5021432, by rfl⟩ : syracuseStep 6695243 = 10042865) B10042865
theorem B1763659 : Blo 1762082 1763659 := bstep (se 1 (by rfl) ⟨1322744, by rfl⟩ : syracuseStep 1763659 = 2645489) B2645489
theorem B1763671 : Blo 1762082 1763671 := bstep (se 1 (by rfl) ⟨1322753, by rfl⟩ : syracuseStep 1763671 = 2645507) B2645507
theorem B6695257 : Blo 1762082 6695257 := bstep (se 2 (by rfl) ⟨2510721, by rfl⟩ : syracuseStep 6695257 = 5021443) B5021443
theorem B1763691 : Blo 1762082 1763691 := bstep (se 1 (by rfl) ⟨1322768, by rfl⟩ : syracuseStep 1763691 = 2645537) B2645537
theorem B1763703 : Blo 1762082 1763703 := bstep (se 1 (by rfl) ⟨1322777, by rfl⟩ : syracuseStep 1763703 = 2645555) B2645555
theorem B3967361 : Blo 1762082 3967361 := bstep (se 2 (by rfl) ⟨1487760, by rfl⟩ : syracuseStep 3967361 = 2975521) B2975521
theorem B1763723 : Blo 1762082 1763723 := bstep (se 1 (by rfl) ⟨1322792, by rfl⟩ : syracuseStep 1763723 = 2645585) B2645585
theorem B2230679 : Blo 1762082 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B1763735 : Blo 1762082 1763735 := bstep (se 1 (by rfl) ⟨1322801, by rfl⟩ : syracuseStep 1763735 = 2645603) B2645603
theorem B1763755 : Blo 1762082 1763755 := bstep (se 1 (by rfl) ⟨1322816, by rfl⟩ : syracuseStep 1763755 = 2645633) B2645633
theorem B1763767 : Blo 1762082 1763767 := bstep (se 1 (by rfl) ⟨1322825, by rfl⟩ : syracuseStep 1763767 = 2645651) B2645651
theorem B2976203 : Blo 1762082 2976203 := bstep (se 1 (by rfl) ⟨2232152, by rfl⟩ : syracuseStep 2976203 = 4464305) B4464305
theorem B1763787 : Blo 1762082 1763787 := bstep (se 1 (by rfl) ⟨1322840, by rfl⟩ : syracuseStep 1763787 = 2645681) B2645681
theorem B1763799 : Blo 1762082 1763799 := bstep (se 1 (by rfl) ⟨1322849, by rfl⟩ : syracuseStep 1763799 = 2645699) B2645699
theorem B1763819 : Blo 1762082 1763819 := bstep (se 1 (by rfl) ⟨1322864, by rfl⟩ : syracuseStep 1763819 = 2645729) B2645729
theorem B1763831 : Blo 1762082 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B1763851 : Blo 1762082 1763851 := bstep (se 1 (by rfl) ⟨1322888, by rfl⟩ : syracuseStep 1763851 = 2645777) B2645777
theorem B1763863 : Blo 1762082 1763863 := bstep (se 1 (by rfl) ⟨1322897, by rfl⟩ : syracuseStep 1763863 = 2645795) B2645795
theorem B1763883 : Blo 1762082 1763883 := bstep (se 1 (by rfl) ⟨1322912, by rfl⟩ : syracuseStep 1763883 = 2645825) B2645825
theorem B1763895 : Blo 1762082 1763895 := bstep (se 1 (by rfl) ⟨1322921, by rfl⟩ : syracuseStep 1763895 = 2645843) B2645843
theorem B2976331 : Blo 1762082 2976331 := bstep (se 1 (by rfl) ⟨2232248, by rfl⟩ : syracuseStep 2976331 = 4464497) B4464497
theorem B1763915 : Blo 1762082 1763915 := bstep (se 1 (by rfl) ⟨1322936, by rfl⟩ : syracuseStep 1763915 = 2645873) B2645873
theorem B1763927 : Blo 1762082 1763927 := bstep (se 1 (by rfl) ⟨1322945, by rfl⟩ : syracuseStep 1763927 = 2645891) B2645891
theorem B3967577 : Blo 1762082 3967577 := bstep (se 2 (by rfl) ⟨1487841, by rfl⟩ : syracuseStep 3967577 = 2975683) B2975683
theorem B1763947 : Blo 1762082 1763947 := bstep (se 1 (by rfl) ⟨1322960, by rfl⟩ : syracuseStep 1763947 = 2645921) B2645921
theorem B1763959 : Blo 1762082 1763959 := bstep (se 1 (by rfl) ⟨1322969, by rfl⟩ : syracuseStep 1763959 = 2645939) B2645939
theorem B1763979 : Blo 1762082 1763979 := bstep (se 1 (by rfl) ⟨1322984, by rfl⟩ : syracuseStep 1763979 = 2645969) B2645969
theorem B1763991 : Blo 1762082 1763991 := bstep (se 1 (by rfl) ⟨1322993, by rfl⟩ : syracuseStep 1763991 = 2645987) B2645987
theorem B1764011 : Blo 1762082 1764011 := bstep (se 1 (by rfl) ⟨1323008, by rfl⟩ : syracuseStep 1764011 = 2646017) B2646017
theorem B3967667 : Blo 1762082 3967667 := bstep (se 1 (by rfl) ⟨2975750, by rfl⟩ : syracuseStep 3967667 = 5951501) B5951501
theorem B1764023 : Blo 1762082 1764023 := bstep (se 1 (by rfl) ⟨1323017, by rfl⟩ : syracuseStep 1764023 = 2646035) B2646035
theorem B1764043 : Blo 1762082 1764043 := bstep (se 1 (by rfl) ⟨1323032, by rfl⟩ : syracuseStep 1764043 = 2646065) B2646065
theorem B3967703 : Blo 1762082 3967703 := bstep (se 1 (by rfl) ⟨2975777, by rfl⟩ : syracuseStep 3967703 = 5951555) B5951555
theorem B2976473 : Blo 1762082 2976473 := bstep (se 2 (by rfl) ⟨1116177, by rfl⟩ : syracuseStep 2976473 = 2232355) B2232355
theorem B1764055 : Blo 1762082 1764055 := bstep (se 1 (by rfl) ⟨1323041, by rfl⟩ : syracuseStep 1764055 = 2646083) B2646083
theorem B1764075 : Blo 1762082 1764075 := bstep (se 1 (by rfl) ⟨1323056, by rfl⟩ : syracuseStep 1764075 = 2646113) B2646113
theorem B23538437 : Blo 1762082 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B5950259 : Blo 1762082 5950259 := bstep (se 1 (by rfl) ⟨4462694, by rfl⟩ : syracuseStep 5950259 = 8925389) B8925389
theorem B2976601 : Blo 1762082 2976601 := bstep (se 2 (by rfl) ⟨1116225, by rfl⟩ : syracuseStep 2976601 = 2232451) B2232451
theorem B3967883 : Blo 1762082 3967883 := bstep (se 1 (by rfl) ⟨2975912, by rfl⟩ : syracuseStep 3967883 = 5951825) B5951825
theorem B12888983 : Blo 1762082 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B3967937 : Blo 1762082 3967937 := bstep (se 2 (by rfl) ⟨1487976, by rfl⟩ : syracuseStep 3967937 = 2975953) B2975953
theorem B7531481 : Blo 1762082 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B5950529 : Blo 1762082 5950529 := bstep (se 2 (by rfl) ⟨2231448, by rfl⟩ : syracuseStep 5950529 = 4462897) B4462897
theorem B4238401 : Blo 1762082 4238401 := bstep (se 2 (by rfl) ⟨1589400, by rfl⟩ : syracuseStep 4238401 = 3178801) B3178801
theorem B2231383 : Blo 1762082 2231383 := bstep (se 1 (by rfl) ⟨1673537, by rfl⟩ : syracuseStep 2231383 = 3347075) B3347075
theorem B2509913 : Blo 1762082 2509913 := bstep (se 2 (by rfl) ⟨941217, by rfl⟩ : syracuseStep 2509913 = 1882435) B1882435
theorem B3968153 : Blo 1762082 3968153 := bstep (se 2 (by rfl) ⟨1488057, by rfl⟩ : syracuseStep 3968153 = 2976115) B2976115
theorem B3574999 : Blo 1762082 3574999 := bstep (se 1 (by rfl) ⟨2681249, by rfl⟩ : syracuseStep 3574999 = 5362499) B5362499
theorem B3763417 : Blo 1762082 3763417 := bstep (se 2 (by rfl) ⟨1411281, by rfl⟩ : syracuseStep 3763417 = 2822563) B2822563
theorem B3099865 : Blo 1762082 3099865 := bstep (se 2 (by rfl) ⟨1162449, by rfl⟩ : syracuseStep 3099865 = 2324899) B2324899
theorem B3968243 : Blo 1762082 3968243 := bstep (se 1 (by rfl) ⟨2976182, by rfl⟩ : syracuseStep 3968243 = 5952365) B5952365
theorem B43486469 : Blo 1762082 43486469 := bstep (se 4 (by rfl) ⟨4076856, by rfl⟩ : syracuseStep 43486469 = 8153713) B8153713
theorem B6696215 : Blo 1762082 6696215 := bstep (se 1 (by rfl) ⟨5022161, by rfl⟩ : syracuseStep 6696215 = 10044323) B10044323
theorem B3968279 : Blo 1762082 3968279 := bstep (se 1 (by rfl) ⟨2976209, by rfl⟩ : syracuseStep 3968279 = 5952419) B5952419
theorem B3345715 : Blo 1762082 3345715 := bstep (se 1 (by rfl) ⟨2509286, by rfl⟩ : syracuseStep 3345715 = 5018573) B5018573
theorem B3968459 : Blo 1762082 3968459 := bstep (se 1 (by rfl) ⟨2976344, by rfl⟩ : syracuseStep 3968459 = 5952689) B5952689
theorem B3968513 : Blo 1762082 3968513 := bstep (se 2 (by rfl) ⟨1488192, by rfl⟩ : syracuseStep 3968513 = 2976385) B2976385
theorem B30518801 : Blo 1762082 30518801 := bstep (se 2 (by rfl) ⟨11444550, by rfl⟩ : syracuseStep 30518801 = 22889101) B22889101
theorem B3345943 : Blo 1762082 3345943 := bstep (se 1 (by rfl) ⟨2509457, by rfl⟩ : syracuseStep 3345943 = 5018915) B5018915
theorem B5951069 : Blo 1762082 5951069 := bstep (se 3 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 5951069 = 2231651) B2231651
theorem B3346049 : Blo 1762082 3346049 := bstep (se 2 (by rfl) ⟨1254768, by rfl⟩ : syracuseStep 3346049 = 2509537) B2509537
theorem B2510551 : Blo 1762082 2510551 := bstep (se 1 (by rfl) ⟨1882913, by rfl⟩ : syracuseStep 2510551 = 3765827) B3765827
theorem B3968729 : Blo 1762082 3968729 := bstep (se 2 (by rfl) ⟨1488273, by rfl⟩ : syracuseStep 3968729 = 2976547) B2976547
theorem B6352643 : Blo 1762082 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B3346201 : Blo 1762082 3346201 := bstep (se 2 (by rfl) ⟨1254825, by rfl⟩ : syracuseStep 3346201 = 2509651) B2509651
theorem B3968819 : Blo 1762082 3968819 := bstep (se 1 (by rfl) ⟨2976614, by rfl⟩ : syracuseStep 3968819 = 5953229) B5953229
theorem B3968855 : Blo 1762082 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B10317719 : Blo 1762082 10317719 := bstep (se 1 (by rfl) ⟨7738289, by rfl⟩ : syracuseStep 10317719 = 15476579) B15476579
theorem B4460467 : Blo 1762082 4460467 := bstep (se 1 (by rfl) ⟨3345350, by rfl⟩ : syracuseStep 4460467 = 6690701) B6690701
theorem B3764161 : Blo 1762082 3764161 := bstep (se 2 (by rfl) ⟨1411560, by rfl⟩ : syracuseStep 3764161 = 2823121) B2823121
theorem B6352843 : Blo 1762082 6352843 := bstep (se 1 (by rfl) ⟨4764632, by rfl⟩ : syracuseStep 6352843 = 9529265) B9529265
theorem B13389785 : Blo 1762082 13389785 := bstep (se 2 (by rfl) ⟨5021169, by rfl⟩ : syracuseStep 13389785 = 10042339) B10042339
theorem B3969035 : Blo 1762082 3969035 := bstep (se 1 (by rfl) ⟨2976776, by rfl⟩ : syracuseStep 3969035 = 5953553) B5953553
theorem B4460609 : Blo 1762082 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B3969089 : Blo 1762082 3969089 := bstep (se 2 (by rfl) ⟨1488408, by rfl⟩ : syracuseStep 3969089 = 2976817) B2976817
theorem B7532747 : Blo 1762082 7532747 := bstep (se 1 (by rfl) ⟨5649560, by rfl⟩ : syracuseStep 7532747 = 11299121) B11299121
theorem B11301221 : Blo 1762082 11301221 := bstep (se 4 (by rfl) ⟨1059489, by rfl⟩ : syracuseStep 11301221 = 2118979) B2118979
theorem B6697475 : Blo 1762082 6697475 := bstep (se 1 (by rfl) ⟨5023106, by rfl⟩ : syracuseStep 6697475 = 10046213) B10046213
theorem B2511371 : Blo 1762082 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B8925713 : Blo 1762082 8925713 := bstep (se 2 (by rfl) ⟨3347142, by rfl⟩ : syracuseStep 8925713 = 6694285) B6694285
theorem B7533107 : Blo 1762082 7533107 := bstep (se 1 (by rfl) ⟨5649830, by rfl⟩ : syracuseStep 7533107 = 11299661) B11299661
theorem B11022941 : Blo 1762082 11022941 := bstep (se 3 (by rfl) ⟨2066801, by rfl⟩ : syracuseStep 11022941 = 4133603) B4133603
theorem B15069797 : Blo 1762082 15069797 := bstep (se 4 (by rfl) ⟨1412793, by rfl⟩ : syracuseStep 15069797 = 2825587) B2825587
theorem B8925875 : Blo 1762082 8925875 := bstep (se 1 (by rfl) ⟨6694406, by rfl⟩ : syracuseStep 8925875 = 13388813) B13388813
theorem B5952203 : Blo 1762082 5952203 := bstep (se 1 (by rfl) ⟨4464152, by rfl⟩ : syracuseStep 5952203 = 8928305) B8928305
theorem B2822987 : Blo 1762082 2822987 := bstep (se 1 (by rfl) ⟨2117240, by rfl⟩ : syracuseStep 2822987 = 4234481) B4234481
theorem B5649227 : Blo 1762082 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B3765143 : Blo 1762082 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B5649355 : Blo 1762082 5649355 := bstep (se 1 (by rfl) ⟨4237016, by rfl⟩ : syracuseStep 5649355 = 8474033) B8474033
theorem B5952473 : Blo 1762082 5952473 := bstep (se 2 (by rfl) ⟨2232177, by rfl⟩ : syracuseStep 5952473 = 4464355) B4464355
theorem B5649431 : Blo 1762082 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B3347507 : Blo 1762082 3347507 := bstep (se 1 (by rfl) ⟨2510630, by rfl⟩ : syracuseStep 3347507 = 5021261) B5021261
theorem B3175499 : Blo 1762082 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B5018699 : Blo 1762082 5018699 := bstep (se 1 (by rfl) ⟨3764024, by rfl⟩ : syracuseStep 5018699 = 7528049) B7528049
theorem B11293789 : Blo 1762082 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B4764851 : Blo 1762082 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B3347659 : Blo 1762082 3347659 := bstep (se 1 (by rfl) ⟨2510744, by rfl⟩ : syracuseStep 3347659 = 5021489) B5021489
theorem B2823383 : Blo 1762082 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B2643161 : Blo 1762082 2643161 := bstep (se 2 (by rfl) ⟨991185, by rfl⟩ : syracuseStep 2643161 = 1982371) B1982371
theorem B15070481 : Blo 1762082 15070481 := bstep (se 2 (by rfl) ⟨5651430, by rfl⟩ : syracuseStep 15070481 = 11302861) B11302861
theorem B4461875 : Blo 1762082 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B2643275 : Blo 1762082 2643275 := bstep (se 1 (by rfl) ⟨1982456, by rfl⟩ : syracuseStep 2643275 = 3964913) B3964913
theorem B2643287 : Blo 1762082 2643287 := bstep (se 1 (by rfl) ⟨1982465, by rfl⟩ : syracuseStep 2643287 = 3964931) B3964931
theorem B21443957 : Blo 1762082 21443957 := bstep (se 5 (by rfl) ⟨1005185, by rfl⟩ : syracuseStep 21443957 = 2010371) B2010371
theorem B2643353 : Blo 1762082 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B3765707 : Blo 1762082 3765707 := bstep (se 1 (by rfl) ⟨2824280, by rfl⟩ : syracuseStep 3765707 = 5648561) B5648561
theorem B5019097 : Blo 1762082 5019097 := bstep (se 2 (by rfl) ⟨1882161, by rfl⟩ : syracuseStep 5019097 = 3764323) B3764323
theorem B2643467 : Blo 1762082 2643467 := bstep (se 1 (by rfl) ⟨1982600, by rfl⟩ : syracuseStep 2643467 = 3965201) B3965201
theorem B2643479 : Blo 1762082 2643479 := bstep (se 1 (by rfl) ⟨1982609, by rfl⟩ : syracuseStep 2643479 = 3965219) B3965219
theorem B3347993 : Blo 1762082 3347993 := bstep (se 2 (by rfl) ⟨1255497, by rfl⟩ : syracuseStep 3347993 = 2510995) B2510995
theorem B2643545 : Blo 1762082 2643545 := bstep (se 2 (by rfl) ⟨991329, by rfl⟩ : syracuseStep 2643545 = 1982659) B1982659
theorem B1881739 : Blo 1762082 1881739 := bstep (se 1 (by rfl) ⟨1411304, by rfl⟩ : syracuseStep 1881739 = 2822609) B2822609
theorem B5953175 : Blo 1762082 5953175 := bstep (se 1 (by rfl) ⟨4464881, by rfl⟩ : syracuseStep 5953175 = 8929763) B8929763
theorem B16307891 : Blo 1762082 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B2643659 : Blo 1762082 2643659 := bstep (se 1 (by rfl) ⟨1982744, by rfl⟩ : syracuseStep 2643659 = 3965489) B3965489
theorem B2643671 : Blo 1762082 2643671 := bstep (se 1 (by rfl) ⟨1982753, by rfl⟩ : syracuseStep 2643671 = 3965507) B3965507
theorem B9049873 : Blo 1762082 9049873 := bstep (se 2 (by rfl) ⟨3393702, by rfl⟩ : syracuseStep 9049873 = 6787405) B6787405
theorem B2643737 : Blo 1762082 2643737 := bstep (se 2 (by rfl) ⟨991401, by rfl⟩ : syracuseStep 2643737 = 1982803) B1982803
theorem B4462411 : Blo 1762082 4462411 := bstep (se 1 (by rfl) ⟨3346808, by rfl⟩ : syracuseStep 4462411 = 6693617) B6693617
theorem B40728419 : Blo 1762082 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B2643851 : Blo 1762082 2643851 := bstep (se 1 (by rfl) ⟨1982888, by rfl⟩ : syracuseStep 2643851 = 3965777) B3965777
theorem B2824075 : Blo 1762082 2824075 := bstep (se 1 (by rfl) ⟨2118056, by rfl⟩ : syracuseStep 2824075 = 4236113) B4236113
theorem B7632785 : Blo 1762082 7632785 := bstep (se 2 (by rfl) ⟨2862294, by rfl⟩ : syracuseStep 7632785 = 5724589) B5724589
theorem B2643863 : Blo 1762082 2643863 := bstep (se 1 (by rfl) ⟨1982897, by rfl⟩ : syracuseStep 2643863 = 3965795) B3965795
theorem B3766169 : Blo 1762082 3766169 := bstep (se 2 (by rfl) ⟨1412313, by rfl⟩ : syracuseStep 3766169 = 2824627) B2824627
theorem B2643929 : Blo 1762082 2643929 := bstep (se 2 (by rfl) ⟨991473, by rfl⟩ : syracuseStep 2643929 = 1982947) B1982947
theorem B5724121 : Blo 1762082 5724121 := bstep (se 2 (by rfl) ⟨2146545, by rfl⟩ : syracuseStep 5724121 = 4293091) B4293091
theorem B4462553 : Blo 1762082 4462553 := bstep (se 2 (by rfl) ⟨1673457, by rfl⟩ : syracuseStep 4462553 = 3346915) B3346915
theorem B2824217 : Blo 1762082 2824217 := bstep (se 2 (by rfl) ⟨1059081, by rfl⟩ : syracuseStep 2824217 = 2118163) B2118163
theorem B2644043 : Blo 1762082 2644043 := bstep (se 1 (by rfl) ⟨1983032, by rfl⟩ : syracuseStep 2644043 = 3966065) B3966065
theorem B2644055 : Blo 1762082 2644055 := bstep (se 1 (by rfl) ⟨1983041, by rfl⟩ : syracuseStep 2644055 = 3966083) B3966083
theorem B3348631 : Blo 1762082 3348631 := bstep (se 1 (by rfl) ⟨2511473, by rfl⟩ : syracuseStep 3348631 = 5022947) B5022947
theorem B2644121 : Blo 1762082 2644121 := bstep (se 2 (by rfl) ⟨991545, by rfl⟩ : syracuseStep 2644121 = 1983091) B1983091
theorem B5953715 : Blo 1762082 5953715 := bstep (se 1 (by rfl) ⟨4465286, by rfl⟩ : syracuseStep 5953715 = 8930573) B8930573
theorem B2644235 : Blo 1762082 2644235 := bstep (se 1 (by rfl) ⟨1983176, by rfl⟩ : syracuseStep 2644235 = 3966353) B3966353
theorem B13383953 : Blo 1762082 13383953 := bstep (se 2 (by rfl) ⟨5018982, by rfl⟩ : syracuseStep 13383953 = 10037965) B10037965
theorem B2644247 : Blo 1762082 2644247 := bstep (se 1 (by rfl) ⟨1983185, by rfl⟩ : syracuseStep 2644247 = 3966371) B3966371
theorem B2644313 : Blo 1762082 2644313 := bstep (se 2 (by rfl) ⟨991617, by rfl⟩ : syracuseStep 2644313 = 1983235) B1983235
theorem B2644427 : Blo 1762082 2644427 := bstep (se 1 (by rfl) ⟨1983320, by rfl⟩ : syracuseStep 2644427 = 3966641) B3966641
theorem B2644439 : Blo 1762082 2644439 := bstep (se 1 (by rfl) ⟨1983329, by rfl⟩ : syracuseStep 2644439 = 3966659) B3966659
theorem B2644505 : Blo 1762082 2644505 := bstep (se 2 (by rfl) ⟨991689, by rfl⟩ : syracuseStep 2644505 = 1983379) B1983379
theorem B8927819 : Blo 1762082 8927819 := bstep (se 1 (by rfl) ⟨6695864, by rfl⟩ : syracuseStep 8927819 = 13391729) B13391729
theorem B5364299 : Blo 1762082 5364299 := bstep (se 1 (by rfl) ⟨4023224, by rfl⟩ : syracuseStep 5364299 = 8046449) B8046449
theorem B2644619 : Blo 1762082 2644619 := bstep (se 1 (by rfl) ⟨1983464, by rfl⟩ : syracuseStep 2644619 = 3966929) B3966929
theorem B2644631 : Blo 1762082 2644631 := bstep (se 1 (by rfl) ⟨1983473, by rfl⟩ : syracuseStep 2644631 = 3966947) B3966947
theorem B3177113 : Blo 1762082 3177113 := bstep (se 2 (by rfl) ⟨1191417, by rfl⟩ : syracuseStep 3177113 = 2382835) B2382835
theorem B5020339 : Blo 1762082 5020339 := bstep (se 1 (by rfl) ⟨3765254, by rfl⟩ : syracuseStep 5020339 = 7530509) B7530509
theorem B2644697 : Blo 1762082 2644697 := bstep (se 2 (by rfl) ⟨991761, by rfl⟩ : syracuseStep 2644697 = 1983523) B1983523
theorem B4463383 : Blo 1762082 4463383 := bstep (se 1 (by rfl) ⟨3347537, by rfl⟩ : syracuseStep 4463383 = 6695075) B6695075
theorem B10042157 : Blo 1762082 10042157 := bstep (se 3 (by rfl) ⟨1882904, by rfl⟩ : syracuseStep 10042157 = 3765809) B3765809
theorem B8584001 : Blo 1762082 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B3177281 : Blo 1762082 3177281 := bstep (se 2 (by rfl) ⟨1191480, by rfl⟩ : syracuseStep 3177281 = 2382961) B2382961
theorem B2644811 : Blo 1762082 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B2644823 : Blo 1762082 2644823 := bstep (se 1 (by rfl) ⟨1983617, by rfl⟩ : syracuseStep 2644823 = 3967235) B3967235
theorem B6691673 : Blo 1762082 6691673 := bstep (se 2 (by rfl) ⟨2509377, by rfl⟩ : syracuseStep 6691673 = 5018755) B5018755
theorem B2644889 : Blo 1762082 2644889 := bstep (se 2 (by rfl) ⟨991833, by rfl⟩ : syracuseStep 2644889 = 1983667) B1983667
theorem B16939955 : Blo 1762082 16939955 := bstep (se 1 (by rfl) ⟨12704966, by rfl⟩ : syracuseStep 16939955 = 25409933) B25409933
theorem B2825177 : Blo 1762082 2825177 := bstep (se 2 (by rfl) ⟨1059441, by rfl⟩ : syracuseStep 2825177 = 2118883) B2118883
theorem B2645003 : Blo 1762082 2645003 := bstep (se 1 (by rfl) ⟨1983752, by rfl⟩ : syracuseStep 2645003 = 3967505) B3967505
theorem B2645015 : Blo 1762082 2645015 := bstep (se 1 (by rfl) ⟨1983761, by rfl⟩ : syracuseStep 2645015 = 3967523) B3967523
theorem B51526691 : Blo 1762082 51526691 := bstep (se 1 (by rfl) ⟨38645018, by rfl⟩ : syracuseStep 51526691 = 77290037) B77290037
theorem B3767347 : Blo 1762082 3767347 := bstep (se 1 (by rfl) ⟨2825510, by rfl⟩ : syracuseStep 3767347 = 5651021) B5651021
theorem B2645081 : Blo 1762082 2645081 := bstep (se 2 (by rfl) ⟨991905, by rfl⟩ : syracuseStep 2645081 = 1983811) B1983811
theorem B1883255 : Blo 1762082 1883255 := bstep (se 1 (by rfl) ⟨1412441, by rfl⟩ : syracuseStep 1883255 = 2824883) B2824883
theorem B2645195 : Blo 1762082 2645195 := bstep (se 1 (by rfl) ⟨1983896, by rfl⟩ : syracuseStep 2645195 = 3967793) B3967793
theorem B4463819 : Blo 1762082 4463819 := bstep (se 1 (by rfl) ⟨3347864, by rfl⟩ : syracuseStep 4463819 = 6695729) B6695729
theorem B2645207 : Blo 1762082 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B2645273 : Blo 1762082 2645273 := bstep (se 2 (by rfl) ⟨991977, by rfl⟩ : syracuseStep 2645273 = 1983955) B1983955
theorem B13393187 : Blo 1762082 13393187 := bstep (se 1 (by rfl) ⟨10044890, by rfl⟩ : syracuseStep 13393187 = 20089781) B20089781
theorem B2645387 : Blo 1762082 2645387 := bstep (se 1 (by rfl) ⟨1984040, by rfl⟩ : syracuseStep 2645387 = 3968081) B3968081
theorem B171589013 : Blo 1762082 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B2645399 : Blo 1762082 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B2645465 : Blo 1762082 2645465 := bstep (se 2 (by rfl) ⟨992049, by rfl⟩ : syracuseStep 2645465 = 1984099) B1984099
theorem B15056401 : Blo 1762082 15056401 := bstep (se 2 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 15056401 = 11292301) B11292301
theorem B4464193 : Blo 1762082 4464193 := bstep (se 2 (by rfl) ⟨1674072, by rfl⟩ : syracuseStep 4464193 = 3348145) B3348145
theorem B2645579 : Blo 1762082 2645579 := bstep (se 1 (by rfl) ⟨1984184, by rfl⟩ : syracuseStep 2645579 = 3968369) B3968369
theorem B2645591 : Blo 1762082 2645591 := bstep (se 1 (by rfl) ⟨1984193, by rfl⟩ : syracuseStep 2645591 = 3968387) B3968387
theorem B2645657 : Blo 1762082 2645657 := bstep (se 2 (by rfl) ⟨992121, by rfl⟩ : syracuseStep 2645657 = 1984243) B1984243
theorem B5947073 : Blo 1762082 5947073 := bstep (se 2 (by rfl) ⟨2230152, by rfl⟩ : syracuseStep 5947073 = 4460305) B4460305
theorem B47038193 : Blo 1762082 47038193 := bstep (se 2 (by rfl) ⟨17639322, by rfl⟩ : syracuseStep 47038193 = 35278645) B35278645
theorem B2645771 : Blo 1762082 2645771 := bstep (se 1 (by rfl) ⟨1984328, by rfl⟩ : syracuseStep 2645771 = 3968657) B3968657
theorem B2645783 : Blo 1762082 2645783 := bstep (se 1 (by rfl) ⟨1984337, by rfl⟩ : syracuseStep 2645783 = 3968675) B3968675
theorem B3964697 : Blo 1762082 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B15056675 : Blo 1762082 15056675 := bstep (se 1 (by rfl) ⟨11292506, by rfl⟩ : syracuseStep 15056675 = 22585013) B22585013
theorem B6356825 : Blo 1762082 6356825 := bstep (se 2 (by rfl) ⟨2383809, by rfl⟩ : syracuseStep 6356825 = 4767619) B4767619
theorem B2645849 : Blo 1762082 2645849 := bstep (se 2 (by rfl) ⟨992193, by rfl⟩ : syracuseStep 2645849 = 1984387) B1984387
theorem B10182493 : Blo 1762082 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B3964787 : Blo 1762082 3964787 := bstep (se 1 (by rfl) ⟨2973590, by rfl⟩ : syracuseStep 3964787 = 5947181) B5947181
theorem B3964823 : Blo 1762082 3964823 := bstep (se 1 (by rfl) ⟨2973617, by rfl⟩ : syracuseStep 3964823 = 5947235) B5947235
theorem B2645963 : Blo 1762082 2645963 := bstep (se 1 (by rfl) ⟨1984472, by rfl⟩ : syracuseStep 2645963 = 3968945) B3968945
theorem B2645975 : Blo 1762082 2645975 := bstep (se 1 (by rfl) ⟨1984481, by rfl⟩ : syracuseStep 2645975 = 3968963) B3968963
theorem B1982443 : Blo 1762082 1982443 := bstep (se 1 (by rfl) ⟨1486832, by rfl⟩ : syracuseStep 1982443 = 2973665) B2973665
theorem B2646023 : Blo 1762082 2646023 := bstep (se 1 (by rfl) ⟨1984517, by rfl⟩ : syracuseStep 2646023 = 3969035) B3969035
theorem B1982479 : Blo 1762082 1982479 := bstep (se 1 (by rfl) ⟨1486859, by rfl⟩ : syracuseStep 1982479 = 2973719) B2973719
theorem B2973739 : Blo 1762082 2973739 := bstep (se 1 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 2973739 = 4460609) B4460609
theorem B2646059 : Blo 1762082 2646059 := bstep (se 1 (by rfl) ⟨1984544, by rfl⟩ : syracuseStep 2646059 = 3969089) B3969089
theorem B171638837 : Blo 1762082 171638837 := bstep (se 5 (by rfl) ⟨8045570, by rfl⟩ : syracuseStep 171638837 = 16091141) B16091141
theorem B15065149 : Blo 1762082 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B2646089 : Blo 1762082 2646089 := bstep (se 2 (by rfl) ⟨992283, by rfl⟩ : syracuseStep 2646089 = 1984567) B1984567
theorem B5021831 : Blo 1762082 5021831 := bstep (se 1 (by rfl) ⟨3766373, by rfl⟩ : syracuseStep 5021831 = 7532747) B7532747
theorem B3965075 : Blo 1762082 3965075 := bstep (se 1 (by rfl) ⟨2973806, by rfl⟩ : syracuseStep 3965075 = 5947613) B5947613
theorem B2973881 : Blo 1762082 2973881 := bstep (se 2 (by rfl) ⟨1115205, by rfl⟩ : syracuseStep 2973881 = 2230411) B2230411
theorem B3965129 : Blo 1762082 3965129 := bstep (se 2 (by rfl) ⟨1486923, by rfl⟩ : syracuseStep 3965129 = 2973847) B2973847
theorem B4464841 : Blo 1762082 4464841 := bstep (se 2 (by rfl) ⟨1674315, by rfl⟩ : syracuseStep 4464841 = 3348631) B3348631
theorem B6693101 : Blo 1762082 6693101 := bstep (se 3 (by rfl) ⟨1254956, by rfl⟩ : syracuseStep 6693101 = 2509913) B2509913
theorem B5022013 : Blo 1762082 5022013 := bstep (se 3 (by rfl) ⟨941627, by rfl⟩ : syracuseStep 5022013 = 1883255) B1883255
theorem B4464983 : Blo 1762082 4464983 := bstep (se 1 (by rfl) ⟨3348737, by rfl⟩ : syracuseStep 4464983 = 6697475) B6697475
theorem B5022071 : Blo 1762082 5022071 := bstep (se 1 (by rfl) ⟨3766553, by rfl⟩ : syracuseStep 5022071 = 7533107) B7533107
theorem B8470919 : Blo 1762082 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B1982983 : Blo 1762082 1982983 := bstep (se 1 (by rfl) ⟨1487237, by rfl⟩ : syracuseStep 1982983 = 2974475) B2974475
theorem B7529021 : Blo 1762082 7529021 := bstep (se 3 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 7529021 = 2823383) B2823383
theorem B5947991 : Blo 1762082 5947991 := bstep (se 1 (by rfl) ⟨4460993, by rfl⟩ : syracuseStep 5947991 = 8921987) B8921987
theorem B1983163 : Blo 1762082 1983163 := bstep (se 1 (by rfl) ⟨1487372, by rfl⟩ : syracuseStep 1983163 = 2974745) B2974745
theorem B76251941 : Blo 1762082 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B1762107 : Blo 1762082 1762107 := bstep (se 1 (by rfl) ⟨1321580, by rfl⟩ : syracuseStep 1762107 = 2643161) B2643161
theorem B10175291 : Blo 1762082 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B2974583 : Blo 1762082 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B1762183 : Blo 1762082 1762183 := bstep (se 1 (by rfl) ⟨1321637, by rfl⟩ : syracuseStep 1762183 = 2643275) B2643275
theorem B3965831 : Blo 1762082 3965831 := bstep (se 1 (by rfl) ⟨2974373, by rfl⟩ : syracuseStep 3965831 = 5948747) B5948747
theorem B1762191 : Blo 1762082 1762191 := bstep (se 1 (by rfl) ⟨1321643, by rfl⟩ : syracuseStep 1762191 = 2643287) B2643287
theorem B6693785 : Blo 1762082 6693785 := bstep (se 2 (by rfl) ⟨2510169, by rfl⟩ : syracuseStep 6693785 = 5020339) B5020339
theorem B14295971 : Blo 1762082 14295971 := bstep (se 1 (by rfl) ⟨10721978, by rfl⟩ : syracuseStep 14295971 = 21443957) B21443957
theorem B1762235 : Blo 1762082 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B1762311 : Blo 1762082 1762311 := bstep (se 1 (by rfl) ⟨1321733, by rfl⟩ : syracuseStep 1762311 = 2643467) B2643467
theorem B1762319 : Blo 1762082 1762319 := bstep (se 1 (by rfl) ⟨1321739, by rfl⟩ : syracuseStep 1762319 = 2643479) B2643479
theorem B3015695 : Blo 1762082 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B1762363 : Blo 1762082 1762363 := bstep (se 1 (by rfl) ⟨1321772, by rfl⟩ : syracuseStep 1762363 = 2643545) B2643545
theorem B3966011 : Blo 1762082 3966011 := bstep (se 1 (by rfl) ⟨2974508, by rfl⟩ : syracuseStep 3966011 = 5949017) B5949017
theorem B5948477 : Blo 1762082 5948477 := bstep (se 3 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 5948477 = 2230679) B2230679
theorem B10871927 : Blo 1762082 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B1762439 : Blo 1762082 1762439 := bstep (se 1 (by rfl) ⟨1321829, by rfl⟩ : syracuseStep 1762439 = 2643659) B2643659
theorem B1762447 : Blo 1762082 1762447 := bstep (se 1 (by rfl) ⟨1321835, by rfl⟩ : syracuseStep 1762447 = 2643671) B2643671
theorem B1983631 : Blo 1762082 1983631 := bstep (se 1 (by rfl) ⟨1487723, by rfl⟩ : syracuseStep 1983631 = 2975447) B2975447
theorem B3966137 : Blo 1762082 3966137 := bstep (se 2 (by rfl) ⟨1487301, by rfl⟩ : syracuseStep 3966137 = 2974603) B2974603
theorem B1762491 : Blo 1762082 1762491 := bstep (se 1 (by rfl) ⟨1321868, by rfl⟩ : syracuseStep 1762491 = 2643737) B2643737
theorem B7144649 : Blo 1762082 7144649 := bstep (se 2 (by rfl) ⟨2679243, by rfl⟩ : syracuseStep 7144649 = 5358487) B5358487
theorem B1762567 : Blo 1762082 1762567 := bstep (se 1 (by rfl) ⟨1321925, by rfl⟩ : syracuseStep 1762567 = 2643851) B2643851
theorem B5088523 : Blo 1762082 5088523 := bstep (se 1 (by rfl) ⟨3816392, by rfl⟩ : syracuseStep 5088523 = 7632785) B7632785
theorem B1762575 : Blo 1762082 1762575 := bstep (se 1 (by rfl) ⟨1321931, by rfl⟩ : syracuseStep 1762575 = 2643863) B2643863
theorem B1762619 : Blo 1762082 1762619 := bstep (se 1 (by rfl) ⟨1321964, by rfl⟩ : syracuseStep 1762619 = 2643929) B2643929
theorem B2975035 : Blo 1762082 2975035 := bstep (se 1 (by rfl) ⟨2231276, by rfl⟩ : syracuseStep 2975035 = 4462553) B4462553
theorem B1762695 : Blo 1762082 1762695 := bstep (se 1 (by rfl) ⟨1322021, by rfl⟩ : syracuseStep 1762695 = 2644043) B2644043
theorem B50824583 : Blo 1762082 50824583 := bstep (se 1 (by rfl) ⟨38118437, by rfl⟩ : syracuseStep 50824583 = 76236875) B76236875
theorem B1762703 : Blo 1762082 1762703 := bstep (se 1 (by rfl) ⟨1322027, by rfl⟩ : syracuseStep 1762703 = 2644055) B2644055
theorem B5023129 : Blo 1762082 5023129 := bstep (se 2 (by rfl) ⟨1883673, by rfl⟩ : syracuseStep 5023129 = 3767347) B3767347
theorem B1762747 : Blo 1762082 1762747 := bstep (se 1 (by rfl) ⟨1322060, by rfl⟩ : syracuseStep 1762747 = 2644121) B2644121
theorem B2975177 : Blo 1762082 2975177 := bstep (se 2 (by rfl) ⟨1115691, by rfl⟩ : syracuseStep 2975177 = 2231383) B2231383
theorem B15058385 : Blo 1762082 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B20088323 : Blo 1762082 20088323 := bstep (se 1 (by rfl) ⟨15066242, by rfl⟩ : syracuseStep 20088323 = 30132485) B30132485
theorem B1762823 : Blo 1762082 1762823 := bstep (se 1 (by rfl) ⟨1322117, by rfl⟩ : syracuseStep 1762823 = 2644235) B2644235
theorem B8922635 : Blo 1762082 8922635 := bstep (se 1 (by rfl) ⟨6691976, by rfl⟩ : syracuseStep 8922635 = 13383953) B13383953
theorem B3966479 : Blo 1762082 3966479 := bstep (se 1 (by rfl) ⟨2974859, by rfl⟩ : syracuseStep 3966479 = 5949719) B5949719
theorem B1762831 : Blo 1762082 1762831 := bstep (se 1 (by rfl) ⟨1322123, by rfl⟩ : syracuseStep 1762831 = 2644247) B2644247
theorem B3966497 : Blo 1762082 3966497 := bstep (se 2 (by rfl) ⟨1487436, by rfl⟩ : syracuseStep 3966497 = 2974873) B2974873
theorem B1762875 : Blo 1762082 1762875 := bstep (se 1 (by rfl) ⟨1322156, by rfl⟩ : syracuseStep 1762875 = 2644313) B2644313
theorem B29394509 : Blo 1762082 29394509 := bstep (se 3 (by rfl) ⟨5511470, by rfl⟩ : syracuseStep 29394509 = 11022941) B11022941
theorem B1762951 : Blo 1762082 1762951 := bstep (se 1 (by rfl) ⟨1322213, by rfl⟩ : syracuseStep 1762951 = 2644427) B2644427
theorem B1984135 : Blo 1762082 1984135 := bstep (se 1 (by rfl) ⟨1488101, by rfl⟩ : syracuseStep 1984135 = 2976203) B2976203
theorem B1762959 : Blo 1762082 1762959 := bstep (se 1 (by rfl) ⟨1322219, by rfl⟩ : syracuseStep 1762959 = 2644439) B2644439
theorem B8922797 : Blo 1762082 8922797 := bstep (se 3 (by rfl) ⟨1673024, by rfl⟩ : syracuseStep 8922797 = 3346049) B3346049
theorem B1763003 : Blo 1762082 1763003 := bstep (se 1 (by rfl) ⟨1322252, by rfl⟩ : syracuseStep 1763003 = 2644505) B2644505
theorem B1763079 : Blo 1762082 1763079 := bstep (se 1 (by rfl) ⟨1322309, by rfl⟩ : syracuseStep 1763079 = 2644619) B2644619
theorem B1763087 : Blo 1762082 1763087 := bstep (se 1 (by rfl) ⟨1322315, by rfl⟩ : syracuseStep 1763087 = 2644631) B2644631
theorem B1763131 : Blo 1762082 1763131 := bstep (se 1 (by rfl) ⟨1322348, by rfl⟩ : syracuseStep 1763131 = 2644697) B2644697
theorem B1984315 : Blo 1762082 1984315 := bstep (se 1 (by rfl) ⟨1488236, by rfl⟩ : syracuseStep 1984315 = 2976473) B2976473
theorem B6694771 : Blo 1762082 6694771 := bstep (se 1 (by rfl) ⟨5021078, by rfl⟩ : syracuseStep 6694771 = 10042157) B10042157
theorem B3966839 : Blo 1762082 3966839 := bstep (se 1 (by rfl) ⟨2975129, by rfl⟩ : syracuseStep 3966839 = 5950259) B5950259
theorem B1763207 : Blo 1762082 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B1763215 : Blo 1762082 1763215 := bstep (se 1 (by rfl) ⟨1322411, by rfl⟩ : syracuseStep 1763215 = 2644823) B2644823
theorem B1763259 : Blo 1762082 1763259 := bstep (se 1 (by rfl) ⟨1322444, by rfl⟩ : syracuseStep 1763259 = 2644889) B2644889
theorem B1763335 : Blo 1762082 1763335 := bstep (se 1 (by rfl) ⟨1322501, by rfl⟩ : syracuseStep 1763335 = 2645003) B2645003
theorem B1763343 : Blo 1762082 1763343 := bstep (se 1 (by rfl) ⟨1322507, by rfl⟩ : syracuseStep 1763343 = 2645015) B2645015
theorem B34351127 : Blo 1762082 34351127 := bstep (se 1 (by rfl) ⟨25763345, by rfl⟩ : syracuseStep 34351127 = 51526691) B51526691
theorem B3967019 : Blo 1762082 3967019 := bstep (se 1 (by rfl) ⟨2975264, by rfl⟩ : syracuseStep 3967019 = 5950529) B5950529
theorem B1763387 : Blo 1762082 1763387 := bstep (se 1 (by rfl) ⟨1322540, by rfl⟩ : syracuseStep 1763387 = 2645081) B2645081
theorem B1763463 : Blo 1762082 1763463 := bstep (se 1 (by rfl) ⟨1322597, by rfl⟩ : syracuseStep 1763463 = 2645195) B2645195
theorem B2975879 : Blo 1762082 2975879 := bstep (se 1 (by rfl) ⟨2231909, by rfl⟩ : syracuseStep 2975879 = 4463819) B4463819
theorem B1763471 : Blo 1762082 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B2508985 : Blo 1762082 2508985 := bstep (se 2 (by rfl) ⟨940869, by rfl⟩ : syracuseStep 2508985 = 1881739) B1881739
theorem B1763515 : Blo 1762082 1763515 := bstep (se 1 (by rfl) ⟨1322636, by rfl⟩ : syracuseStep 1763515 = 2645273) B2645273
theorem B22898933 : Blo 1762082 22898933 := bstep (se 5 (by rfl) ⟨1073387, by rfl⟩ : syracuseStep 22898933 = 2146775) B2146775
theorem B1763591 : Blo 1762082 1763591 := bstep (se 1 (by rfl) ⟨1322693, by rfl⟩ : syracuseStep 1763591 = 2645387) B2645387
theorem B1763599 : Blo 1762082 1763599 := bstep (se 1 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 1763599 = 2645399) B2645399
theorem B1763643 : Blo 1762082 1763643 := bstep (se 1 (by rfl) ⟨1322732, by rfl⟩ : syracuseStep 1763643 = 2645465) B2645465
theorem B1763719 : Blo 1762082 1763719 := bstep (se 1 (by rfl) ⟨1322789, by rfl⟩ : syracuseStep 1763719 = 2645579) B2645579
theorem B1763727 : Blo 1762082 1763727 := bstep (se 1 (by rfl) ⟨1322795, by rfl⟩ : syracuseStep 1763727 = 2645591) B2645591
theorem B3967379 : Blo 1762082 3967379 := bstep (se 1 (by rfl) ⟨2975534, by rfl⟩ : syracuseStep 3967379 = 5951069) B5951069
theorem B5949881 : Blo 1762082 5949881 := bstep (se 2 (by rfl) ⟨2231205, by rfl⟩ : syracuseStep 5949881 = 4462411) B4462411
theorem B1763771 : Blo 1762082 1763771 := bstep (se 1 (by rfl) ⟨1322828, by rfl⟩ : syracuseStep 1763771 = 2645657) B2645657
theorem B3967433 : Blo 1762082 3967433 := bstep (se 2 (by rfl) ⟨1487787, by rfl⟩ : syracuseStep 3967433 = 2975575) B2975575
theorem B13576657 : Blo 1762082 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1763847 : Blo 1762082 1763847 := bstep (se 1 (by rfl) ⟨1322885, by rfl⟩ : syracuseStep 1763847 = 2645771) B2645771
theorem B1763855 : Blo 1762082 1763855 := bstep (se 1 (by rfl) ⟨1322891, by rfl⟩ : syracuseStep 1763855 = 2645783) B2645783
theorem B10037783 : Blo 1762082 10037783 := bstep (se 1 (by rfl) ⟨7528337, by rfl⟩ : syracuseStep 10037783 = 15056675) B15056675
theorem B4237883 : Blo 1762082 4237883 := bstep (se 1 (by rfl) ⟨3178412, by rfl⟩ : syracuseStep 4237883 = 6356825) B6356825
theorem B1763899 : Blo 1762082 1763899 := bstep (se 1 (by rfl) ⟨1322924, by rfl⟩ : syracuseStep 1763899 = 2645849) B2645849
theorem B16943681 : Blo 1762082 16943681 := bstep (se 2 (by rfl) ⟨6353880, by rfl⟩ : syracuseStep 16943681 = 12707761) B12707761
theorem B1763975 : Blo 1762082 1763975 := bstep (se 1 (by rfl) ⟨1322981, by rfl⟩ : syracuseStep 1763975 = 2645963) B2645963
theorem B1763983 : Blo 1762082 1763983 := bstep (se 1 (by rfl) ⟨1322987, by rfl⟩ : syracuseStep 1763983 = 2645975) B2645975
theorem B1764027 : Blo 1762082 1764027 := bstep (se 1 (by rfl) ⟨1323020, by rfl⟩ : syracuseStep 1764027 = 2646041) B2646041
theorem B2976527 : Blo 1762082 2976527 := bstep (se 1 (by rfl) ⟨2232395, by rfl⟩ : syracuseStep 2976527 = 4464791) B4464791
theorem B25406243 : Blo 1762082 25406243 := bstep (se 1 (by rfl) ⟨19054682, by rfl⟩ : syracuseStep 25406243 = 38109365) B38109365
theorem B2009915 : Blo 1762082 2009915 := bstep (se 1 (by rfl) ⟨1507436, by rfl⟩ : syracuseStep 2009915 = 3014873) B3014873
theorem B25406297 : Blo 1762082 25406297 := bstep (se 2 (by rfl) ⟨9527361, by rfl⟩ : syracuseStep 25406297 = 19054723) B19054723
theorem B5950475 : Blo 1762082 5950475 := bstep (se 1 (by rfl) ⟨4462856, by rfl⟩ : syracuseStep 5950475 = 8925713) B8925713
theorem B10046531 : Blo 1762082 10046531 := bstep (se 1 (by rfl) ⟨7534898, by rfl⟩ : syracuseStep 10046531 = 15069797) B15069797
theorem B5950583 : Blo 1762082 5950583 := bstep (se 1 (by rfl) ⟨4462937, by rfl⟩ : syracuseStep 5950583 = 8925875) B8925875
theorem B3968135 : Blo 1762082 3968135 := bstep (se 1 (by rfl) ⟨2976101, by rfl⟩ : syracuseStep 3968135 = 5952203) B5952203
theorem B2681999 : Blo 1762082 2681999 := bstep (se 1 (by rfl) ⟨2011499, by rfl⟩ : syracuseStep 2681999 = 4022999) B4022999
theorem B8924417 : Blo 1762082 8924417 := bstep (se 2 (by rfl) ⟨3346656, by rfl⟩ : syracuseStep 8924417 = 6693313) B6693313
theorem B3968315 : Blo 1762082 3968315 := bstep (se 1 (by rfl) ⟨2976236, by rfl⟩ : syracuseStep 3968315 = 5952473) B5952473
theorem B45165923 : Blo 1762082 45165923 := bstep (se 1 (by rfl) ⟨33874442, by rfl⟩ : syracuseStep 45165923 = 67748885) B67748885
theorem B2116999 : Blo 1762082 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B3345799 : Blo 1762082 3345799 := bstep (se 1 (by rfl) ⟨2509349, by rfl⟩ : syracuseStep 3345799 = 5018699) B5018699
theorem B8154503 : Blo 1762082 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B3968441 : Blo 1762082 3968441 := bstep (se 2 (by rfl) ⟨1488165, by rfl⟩ : syracuseStep 3968441 = 2976331) B2976331
theorem B10046987 : Blo 1762082 10046987 := bstep (se 1 (by rfl) ⟨7535240, by rfl⟩ : syracuseStep 10046987 = 15070481) B15070481
theorem B2510471 : Blo 1762082 2510471 := bstep (se 1 (by rfl) ⟨1882853, by rfl⟩ : syracuseStep 2510471 = 3765707) B3765707
theorem B5951177 : Blo 1762082 5951177 := bstep (se 2 (by rfl) ⟨2231691, by rfl⟩ : syracuseStep 5951177 = 4463383) B4463383
theorem B3968783 : Blo 1762082 3968783 := bstep (se 1 (by rfl) ⟨2976587, by rfl⟩ : syracuseStep 3968783 = 5953175) B5953175
theorem B3968801 : Blo 1762082 3968801 := bstep (se 2 (by rfl) ⟨1488300, by rfl⟩ : syracuseStep 3968801 = 2976601) B2976601
theorem B19066661 : Blo 1762082 19066661 := bstep (se 4 (by rfl) ⟨1787499, by rfl⟩ : syracuseStep 19066661 = 3574999) B3574999
theorem B7532423 : Blo 1762082 7532423 := bstep (se 1 (by rfl) ⟨5649317, by rfl⟩ : syracuseStep 7532423 = 11298635) B11298635
theorem B27152279 : Blo 1762082 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B7532473 : Blo 1762082 7532473 := bstep (se 2 (by rfl) ⟨2824677, by rfl⟩ : syracuseStep 7532473 = 5649355) B5649355
theorem B2510779 : Blo 1762082 2510779 := bstep (se 1 (by rfl) ⟨1883084, by rfl⟩ : syracuseStep 2510779 = 3766169) B3766169
theorem B6696989 : Blo 1762082 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B8925227 : Blo 1762082 8925227 := bstep (se 1 (by rfl) ⟨6693920, by rfl⟩ : syracuseStep 8925227 = 13387841) B13387841
theorem B3969143 : Blo 1762082 3969143 := bstep (se 1 (by rfl) ⟨2976857, by rfl⟩ : syracuseStep 3969143 = 5953715) B5953715
theorem B5017889 : Blo 1762082 5017889 := bstep (se 2 (by rfl) ⟨1881708, by rfl⟩ : syracuseStep 5017889 = 3763417) B3763417
theorem B4133153 : Blo 1762082 4133153 := bstep (se 2 (by rfl) ⟨1549932, by rfl⟩ : syracuseStep 4133153 = 3099865) B3099865
theorem B5951879 : Blo 1762082 5951879 := bstep (se 1 (by rfl) ⟨4463909, by rfl⟩ : syracuseStep 5951879 = 8927819) B8927819
theorem B3576199 : Blo 1762082 3576199 := bstep (se 1 (by rfl) ⟨2682149, by rfl⟩ : syracuseStep 3576199 = 5364299) B5364299
theorem B10039697 : Blo 1762082 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B4460953 : Blo 1762082 4460953 := bstep (se 2 (by rfl) ⟨1672857, by rfl⟩ : syracuseStep 4460953 = 3345715) B3345715
theorem B15692291 : Blo 1762082 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B5722667 : Blo 1762082 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B2118187 : Blo 1762082 2118187 := bstep (se 1 (by rfl) ⟨1588640, by rfl⟩ : syracuseStep 2118187 = 3177281) B3177281
theorem B4461115 : Blo 1762082 4461115 := bstep (se 1 (by rfl) ⟨3345836, by rfl⟩ : syracuseStep 4461115 = 6691673) B6691673
theorem B11293303 : Blo 1762082 11293303 := bstep (se 1 (by rfl) ⟨8469977, by rfl⟩ : syracuseStep 11293303 = 16939955) B16939955
theorem B20075201 : Blo 1762082 20075201 := bstep (se 2 (by rfl) ⟨7528200, by rfl⟩ : syracuseStep 20075201 = 15056401) B15056401
theorem B4461257 : Blo 1762082 4461257 := bstep (se 2 (by rfl) ⟨1672971, by rfl⟩ : syracuseStep 4461257 = 3345943) B3345943
theorem B6697673 : Blo 1762082 6697673 := bstep (se 2 (by rfl) ⟨2511627, by rfl⟩ : syracuseStep 6697673 = 5023255) B5023255
theorem B15061733 : Blo 1762082 15061733 := bstep (se 4 (by rfl) ⟨1412037, by rfl⟩ : syracuseStep 15061733 = 2824075) B2824075
theorem B5952257 : Blo 1762082 5952257 := bstep (se 2 (by rfl) ⟨2232096, by rfl⟩ : syracuseStep 5952257 = 4464193) B4464193
theorem B3347401 : Blo 1762082 3347401 := bstep (se 2 (by rfl) ⟨1255275, by rfl⟩ : syracuseStep 3347401 = 2510551) B2510551
theorem B20345867 : Blo 1762082 20345867 := bstep (se 1 (by rfl) ⟨15259400, by rfl⟩ : syracuseStep 20345867 = 30518801) B30518801
theorem B4461601 : Blo 1762082 4461601 := bstep (se 2 (by rfl) ⟨1673100, by rfl⟩ : syracuseStep 4461601 = 3346201) B3346201
theorem B10040381 : Blo 1762082 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B2643131 : Blo 1762082 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B20083949 : Blo 1762082 20083949 := bstep (se 3 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 20083949 = 7531481) B7531481
theorem B7533805 : Blo 1762082 7533805 := bstep (se 3 (by rfl) ⟨1412588, by rfl⟩ : syracuseStep 7533805 = 2825177) B2825177
theorem B2643191 : Blo 1762082 2643191 := bstep (se 1 (by rfl) ⟨1982393, by rfl⟩ : syracuseStep 2643191 = 3964787) B3964787
theorem B5018881 : Blo 1762082 5018881 := bstep (se 2 (by rfl) ⟨1882080, by rfl⟩ : syracuseStep 5018881 = 3764161) B3764161
theorem B2643215 : Blo 1762082 2643215 := bstep (se 1 (by rfl) ⟨1982411, by rfl⟩ : syracuseStep 2643215 = 3964823) B3964823
theorem B6878479 : Blo 1762082 6878479 := bstep (se 1 (by rfl) ⟨5158859, by rfl⟩ : syracuseStep 6878479 = 10317719) B10317719
theorem B7632161 : Blo 1762082 7632161 := bstep (se 2 (by rfl) ⟨2862060, by rfl⟩ : syracuseStep 7632161 = 5724121) B5724121
theorem B2643257 : Blo 1762082 2643257 := bstep (se 2 (by rfl) ⟨991221, by rfl⟩ : syracuseStep 2643257 = 1982443) B1982443
theorem B8926523 : Blo 1762082 8926523 := bstep (se 1 (by rfl) ⟨6694892, by rfl⟩ : syracuseStep 8926523 = 13389785) B13389785
theorem B2643335 : Blo 1762082 2643335 := bstep (se 1 (by rfl) ⟨1982501, by rfl⟩ : syracuseStep 2643335 = 3965003) B3965003
theorem B2643371 : Blo 1762082 2643371 := bstep (se 1 (by rfl) ⟨1982528, by rfl⟩ : syracuseStep 2643371 = 3965057) B3965057
theorem B2643401 : Blo 1762082 2643401 := bstep (se 2 (by rfl) ⟨991275, by rfl⟩ : syracuseStep 2643401 = 1982551) B1982551
theorem B8926685 : Blo 1762082 8926685 := bstep (se 3 (by rfl) ⟨1673753, by rfl⟩ : syracuseStep 8926685 = 3347507) B3347507
theorem B5953067 : Blo 1762082 5953067 := bstep (se 1 (by rfl) ⟨4464800, by rfl⟩ : syracuseStep 5953067 = 8929601) B8929601
theorem B2643515 : Blo 1762082 2643515 := bstep (se 1 (by rfl) ⟨1982636, by rfl⟩ : syracuseStep 2643515 = 3965273) B3965273
theorem B7534147 : Blo 1762082 7534147 := bstep (se 1 (by rfl) ⟨5650610, by rfl⟩ : syracuseStep 7534147 = 11301221) B11301221
theorem B2643575 : Blo 1762082 2643575 := bstep (se 1 (by rfl) ⟨1982681, by rfl⟩ : syracuseStep 2643575 = 3965363) B3965363
theorem B4462199 : Blo 1762082 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B2643599 : Blo 1762082 2643599 := bstep (se 1 (by rfl) ⟨1982699, by rfl⟩ : syracuseStep 2643599 = 3965399) B3965399
theorem B2643641 : Blo 1762082 2643641 := bstep (se 2 (by rfl) ⟨991365, by rfl⟩ : syracuseStep 2643641 = 1982731) B1982731
theorem B2643719 : Blo 1762082 2643719 := bstep (se 1 (by rfl) ⟨1982789, by rfl⟩ : syracuseStep 2643719 = 3965579) B3965579
theorem B8927009 : Blo 1762082 8927009 := bstep (se 2 (by rfl) ⟨3347628, by rfl⟩ : syracuseStep 8927009 = 6695257) B6695257
theorem B2643755 : Blo 1762082 2643755 := bstep (se 1 (by rfl) ⟨1982816, by rfl⟩ : syracuseStep 2643755 = 3965633) B3965633
theorem B2643785 : Blo 1762082 2643785 := bstep (se 2 (by rfl) ⟨991419, by rfl⟩ : syracuseStep 2643785 = 1982839) B1982839
theorem B1881991 : Blo 1762082 1881991 := bstep (se 1 (by rfl) ⟨1411493, by rfl⟩ : syracuseStep 1881991 = 2822987) B2822987
theorem B3766151 : Blo 1762082 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B2643899 : Blo 1762082 2643899 := bstep (se 1 (by rfl) ⟨1982924, by rfl⟩ : syracuseStep 2643899 = 3965849) B3965849
theorem B2643959 : Blo 1762082 2643959 := bstep (se 1 (by rfl) ⟨1982969, by rfl⟩ : syracuseStep 2643959 = 3965939) B3965939
theorem B2643983 : Blo 1762082 2643983 := bstep (se 1 (by rfl) ⟨1982987, by rfl⟩ : syracuseStep 2643983 = 3965975) B3965975
theorem B2644025 : Blo 1762082 2644025 := bstep (se 2 (by rfl) ⟨991509, by rfl⟩ : syracuseStep 2644025 = 1983019) B1983019
theorem B6690883 : Blo 1762082 6690883 := bstep (se 1 (by rfl) ⟨5018162, by rfl⟩ : syracuseStep 6690883 = 10036325) B10036325
theorem B3176567 : Blo 1762082 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B2644103 : Blo 1762082 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B2644139 : Blo 1762082 2644139 := bstep (se 1 (by rfl) ⟨1983104, by rfl⟩ : syracuseStep 2644139 = 3966209) B3966209
theorem B9050285 : Blo 1762082 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B2644169 : Blo 1762082 2644169 := bstep (se 2 (by rfl) ⟨991563, by rfl⟩ : syracuseStep 2644169 = 1983127) B1983127
theorem B2382139 : Blo 1762082 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B2644283 : Blo 1762082 2644283 := bstep (se 1 (by rfl) ⟨1983212, by rfl⟩ : syracuseStep 2644283 = 3966425) B3966425
theorem B6691187 : Blo 1762082 6691187 := bstep (se 1 (by rfl) ⟨5018390, by rfl⟩ : syracuseStep 6691187 = 10036781) B10036781
theorem B2644343 : Blo 1762082 2644343 := bstep (se 1 (by rfl) ⟨1983257, by rfl⟩ : syracuseStep 2644343 = 3966515) B3966515
theorem B2644367 : Blo 1762082 2644367 := bstep (se 1 (by rfl) ⟨1983275, by rfl⟩ : syracuseStep 2644367 = 3966551) B3966551
theorem B2644409 : Blo 1762082 2644409 := bstep (se 2 (by rfl) ⟨991653, by rfl⟩ : syracuseStep 2644409 = 1983307) B1983307
theorem B2644487 : Blo 1762082 2644487 := bstep (se 1 (by rfl) ⟨1983365, by rfl⟩ : syracuseStep 2644487 = 3966731) B3966731
theorem B2644523 : Blo 1762082 2644523 := bstep (se 1 (by rfl) ⟨1983392, by rfl⟩ : syracuseStep 2644523 = 3966785) B3966785
theorem B2644553 : Blo 1762082 2644553 := bstep (se 2 (by rfl) ⟨991707, by rfl⟩ : syracuseStep 2644553 = 1983415) B1983415
theorem B2644667 : Blo 1762082 2644667 := bstep (se 1 (by rfl) ⟨1983500, by rfl⟩ : syracuseStep 2644667 = 3967001) B3967001
theorem B1882811 : Blo 1762082 1882811 := bstep (se 1 (by rfl) ⟨1412108, by rfl⟩ : syracuseStep 1882811 = 2824217) B2824217
theorem B8927981 : Blo 1762082 8927981 := bstep (se 3 (by rfl) ⟨1673996, by rfl⟩ : syracuseStep 8927981 = 3347993) B3347993
theorem B2644727 : Blo 1762082 2644727 := bstep (se 1 (by rfl) ⟨1983545, by rfl⟩ : syracuseStep 2644727 = 3967091) B3967091
theorem B5651201 : Blo 1762082 5651201 := bstep (se 2 (by rfl) ⟨2119200, by rfl⟩ : syracuseStep 5651201 = 4238401) B4238401
theorem B2644751 : Blo 1762082 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B2644793 : Blo 1762082 2644793 := bstep (se 2 (by rfl) ⟨991797, by rfl⟩ : syracuseStep 2644793 = 1983595) B1983595
theorem B6691643 : Blo 1762082 6691643 := bstep (se 1 (by rfl) ⟨5018732, by rfl⟩ : syracuseStep 6691643 = 10037465) B10037465
theorem B2644871 : Blo 1762082 2644871 := bstep (se 1 (by rfl) ⟨1983653, by rfl⟩ : syracuseStep 2644871 = 3967307) B3967307
theorem B4463495 : Blo 1762082 4463495 := bstep (se 1 (by rfl) ⟨3347621, by rfl⟩ : syracuseStep 4463495 = 6695243) B6695243
theorem B2644907 : Blo 1762082 2644907 := bstep (se 1 (by rfl) ⟨1983680, by rfl⟩ : syracuseStep 2644907 = 3967361) B3967361
theorem B33889205 : Blo 1762082 33889205 := bstep (se 5 (by rfl) ⟨1588556, by rfl⟩ : syracuseStep 33889205 = 3177113) B3177113
theorem B4463545 : Blo 1762082 4463545 := bstep (se 2 (by rfl) ⟨1673829, by rfl⟩ : syracuseStep 4463545 = 3347659) B3347659
theorem B2644937 : Blo 1762082 2644937 := bstep (se 2 (by rfl) ⟨991851, by rfl⟩ : syracuseStep 2644937 = 1983703) B1983703
theorem B97876997 : Blo 1762082 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B2645051 : Blo 1762082 2645051 := bstep (se 1 (by rfl) ⟨1983788, by rfl⟩ : syracuseStep 2645051 = 3967577) B3967577
theorem B2645111 : Blo 1762082 2645111 := bstep (se 1 (by rfl) ⟨1983833, by rfl⟩ : syracuseStep 2645111 = 3967667) B3967667
theorem B2645135 : Blo 1762082 2645135 := bstep (se 1 (by rfl) ⟨1983851, by rfl⟩ : syracuseStep 2645135 = 3967703) B3967703
theorem B2645177 : Blo 1762082 2645177 := bstep (se 2 (by rfl) ⟨991941, by rfl⟩ : syracuseStep 2645177 = 1983883) B1983883
theorem B2645255 : Blo 1762082 2645255 := bstep (se 1 (by rfl) ⟨1983941, by rfl⟩ : syracuseStep 2645255 = 3967883) B3967883
theorem B8592655 : Blo 1762082 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B6692129 : Blo 1762082 6692129 := bstep (se 2 (by rfl) ⟨2509548, by rfl⟩ : syracuseStep 6692129 = 5019097) B5019097
theorem B2645291 : Blo 1762082 2645291 := bstep (se 1 (by rfl) ⟨1983968, by rfl⟩ : syracuseStep 2645291 = 3967937) B3967937
theorem B2383177 : Blo 1762082 2383177 := bstep (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) B1787383
theorem B2645321 : Blo 1762082 2645321 := bstep (se 2 (by rfl) ⟨991995, by rfl⟩ : syracuseStep 2645321 = 1983991) B1983991
theorem B2645435 : Blo 1762082 2645435 := bstep (se 1 (by rfl) ⟨1984076, by rfl⟩ : syracuseStep 2645435 = 3968153) B3968153
theorem B2645495 : Blo 1762082 2645495 := bstep (se 1 (by rfl) ⟨1984121, by rfl⟩ : syracuseStep 2645495 = 3968243) B3968243
theorem B28990979 : Blo 1762082 28990979 := bstep (se 1 (by rfl) ⟨21743234, by rfl⟩ : syracuseStep 28990979 = 43486469) B43486469
theorem B4464143 : Blo 1762082 4464143 := bstep (se 1 (by rfl) ⟨3348107, by rfl⟩ : syracuseStep 4464143 = 6696215) B6696215
theorem B2645519 : Blo 1762082 2645519 := bstep (se 1 (by rfl) ⟨1984139, by rfl⟩ : syracuseStep 2645519 = 3968279) B3968279
theorem B8928791 : Blo 1762082 8928791 := bstep (se 1 (by rfl) ⟨6696593, by rfl⟩ : syracuseStep 8928791 = 13393187) B13393187
theorem B2645561 : Blo 1762082 2645561 := bstep (se 2 (by rfl) ⟨992085, by rfl⟩ : syracuseStep 2645561 = 1984171) B1984171
theorem B27508301 : Blo 1762082 27508301 := bstep (se 3 (by rfl) ⟨5157806, by rfl⟩ : syracuseStep 27508301 = 10315613) B10315613
theorem B114392675 : Blo 1762082 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B2645639 : Blo 1762082 2645639 := bstep (se 1 (by rfl) ⟨1984229, by rfl⟩ : syracuseStep 2645639 = 3968459) B3968459
theorem B2645675 : Blo 1762082 2645675 := bstep (se 1 (by rfl) ⟨1984256, by rfl⟩ : syracuseStep 2645675 = 3968513) B3968513
theorem B12066497 : Blo 1762082 12066497 := bstep (se 2 (by rfl) ⟨4524936, by rfl⟩ : syracuseStep 12066497 = 9049873) B9049873
theorem B2645705 : Blo 1762082 2645705 := bstep (se 2 (by rfl) ⟨992139, by rfl⟩ : syracuseStep 2645705 = 1984279) B1984279
theorem B3964715 : Blo 1762082 3964715 := bstep (se 1 (by rfl) ⟨2973536, by rfl⟩ : syracuseStep 3964715 = 5947073) B5947073
theorem B2645819 : Blo 1762082 2645819 := bstep (se 1 (by rfl) ⟨1984364, by rfl⟩ : syracuseStep 2645819 = 3968729) B3968729
theorem B31358795 : Blo 1762082 31358795 := bstep (se 1 (by rfl) ⟨23519096, by rfl⟩ : syracuseStep 31358795 = 47038193) B47038193
theorem B4235095 : Blo 1762082 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B2645879 : Blo 1762082 2645879 := bstep (se 1 (by rfl) ⟨1984409, by rfl⟩ : syracuseStep 2645879 = 3968819) B3968819
theorem B2645903 : Blo 1762082 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B5947289 : Blo 1762082 5947289 := bstep (se 2 (by rfl) ⟨2230233, by rfl⟩ : syracuseStep 5947289 = 4460467) B4460467
theorem B8470457 : Blo 1762082 8470457 := bstep (se 2 (by rfl) ⟨3176421, by rfl⟩ : syracuseStep 8470457 = 6352843) B6352843
theorem B2645945 : Blo 1762082 2645945 := bstep (se 2 (by rfl) ⟨992229, by rfl⟩ : syracuseStep 2645945 = 1984459) B1984459
theorem B4464659 : Blo 1762082 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B114425891 : Blo 1762082 114425891 := bstep (se 1 (by rfl) ⟨85819418, by rfl⟩ : syracuseStep 114425891 = 171638837) B171638837
theorem B3964985 : Blo 1762082 3964985 := bstep (se 2 (by rfl) ⟨1486869, by rfl⟩ : syracuseStep 3964985 = 2973739) B2973739
theorem B2646095 : Blo 1762082 2646095 := bstep (se 1 (by rfl) ⟨1984571, by rfl⟩ : syracuseStep 2646095 = 3969143) B3969143
theorem B20086865 : Blo 1762082 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B8921177 : Blo 1762082 8921177 := bstep (se 2 (by rfl) ⟨3345441, by rfl⟩ : syracuseStep 8921177 = 6690883) B6690883
theorem B1982587 : Blo 1762082 1982587 := bstep (se 1 (by rfl) ⟨1486940, by rfl⟩ : syracuseStep 1982587 = 2973881) B2973881
theorem B6693131 : Blo 1762082 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B10461527 : Blo 1762082 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B3965327 : Blo 1762082 3965327 := bstep (se 1 (by rfl) ⟨2973995, by rfl⟩ : syracuseStep 3965327 = 5947991) B5947991
theorem B2974171 : Blo 1762082 2974171 := bstep (se 1 (by rfl) ⟨2230628, by rfl⟩ : syracuseStep 2974171 = 4461257) B4461257
theorem B4465115 : Blo 1762082 4465115 := bstep (se 1 (by rfl) ⟨3348836, by rfl⟩ : syracuseStep 4465115 = 6697673) B6697673
theorem B4768265 : Blo 1762082 4768265 := bstep (se 2 (by rfl) ⟨1788099, by rfl⟩ : syracuseStep 4768265 = 3576199) B3576199
theorem B5947937 : Blo 1762082 5947937 := bstep (se 2 (by rfl) ⟨2230476, by rfl⟩ : syracuseStep 5947937 = 4460953) B4460953
theorem B6783527 : Blo 1762082 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1983055 : Blo 1762082 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B21439093 : Blo 1762082 21439093 := bstep (se 5 (by rfl) ⟨1004957, by rfl⟩ : syracuseStep 21439093 = 2009915) B2009915
theorem B3965651 : Blo 1762082 3965651 := bstep (se 1 (by rfl) ⟨2974238, by rfl⟩ : syracuseStep 3965651 = 5948477) B5948477
theorem B6693587 : Blo 1762082 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B5948153 : Blo 1762082 5948153 := bstep (se 2 (by rfl) ⟨2230557, by rfl⟩ : syracuseStep 5948153 = 4461115) B4461115
theorem B1762087 : Blo 1762082 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B15057737 : Blo 1762082 15057737 := bstep (se 2 (by rfl) ⟨5646651, by rfl⟩ : syracuseStep 15057737 = 11293303) B11293303
theorem B1762127 : Blo 1762082 1762127 := bstep (se 1 (by rfl) ⟨1321595, by rfl⟩ : syracuseStep 1762127 = 2643191) B2643191
theorem B1762143 : Blo 1762082 1762143 := bstep (se 1 (by rfl) ⟨1321607, by rfl⟩ : syracuseStep 1762143 = 2643215) B2643215
theorem B5088107 : Blo 1762082 5088107 := bstep (se 1 (by rfl) ⟨3816080, by rfl⟩ : syracuseStep 5088107 = 7632161) B7632161
theorem B1762171 : Blo 1762082 1762171 := bstep (se 1 (by rfl) ⟨1321628, by rfl⟩ : syracuseStep 1762171 = 2643257) B2643257
theorem B1762223 : Blo 1762082 1762223 := bstep (se 1 (by rfl) ⟨1321667, by rfl⟩ : syracuseStep 1762223 = 2643335) B2643335
theorem B33883055 : Blo 1762082 33883055 := bstep (se 1 (by rfl) ⟨25412291, by rfl⟩ : syracuseStep 33883055 = 50824583) B50824583
theorem B1762247 : Blo 1762082 1762247 := bstep (se 1 (by rfl) ⟨1321685, by rfl⟩ : syracuseStep 1762247 = 2643371) B2643371
theorem B1762267 : Blo 1762082 1762267 := bstep (se 1 (by rfl) ⟨1321700, by rfl⟩ : syracuseStep 1762267 = 2643401) B2643401
theorem B1983451 : Blo 1762082 1983451 := bstep (se 1 (by rfl) ⟨1487588, by rfl⟩ : syracuseStep 1983451 = 2975177) B2975177
theorem B5948423 : Blo 1762082 5948423 := bstep (se 1 (by rfl) ⟨4461317, by rfl⟩ : syracuseStep 5948423 = 8922635) B8922635
theorem B1762343 : Blo 1762082 1762343 := bstep (se 1 (by rfl) ⟨1321757, by rfl⟩ : syracuseStep 1762343 = 2643515) B2643515
theorem B1762383 : Blo 1762082 1762383 := bstep (se 1 (by rfl) ⟨1321787, by rfl⟩ : syracuseStep 1762383 = 2643575) B2643575
theorem B2974799 : Blo 1762082 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B1762399 : Blo 1762082 1762399 := bstep (se 1 (by rfl) ⟨1321799, by rfl⟩ : syracuseStep 1762399 = 2643599) B2643599
theorem B5948531 : Blo 1762082 5948531 := bstep (se 1 (by rfl) ⟨4461398, by rfl⟩ : syracuseStep 5948531 = 8922797) B8922797
theorem B1762427 : Blo 1762082 1762427 := bstep (se 1 (by rfl) ⟨1321820, by rfl⟩ : syracuseStep 1762427 = 2643641) B2643641
theorem B1762479 : Blo 1762082 1762479 := bstep (se 1 (by rfl) ⟨1321859, by rfl⟩ : syracuseStep 1762479 = 2643719) B2643719
theorem B1762503 : Blo 1762082 1762503 := bstep (se 1 (by rfl) ⟨1321877, by rfl⟩ : syracuseStep 1762503 = 2643755) B2643755
theorem B1762523 : Blo 1762082 1762523 := bstep (se 1 (by rfl) ⟨1321892, by rfl⟩ : syracuseStep 1762523 = 2643785) B2643785
theorem B1762599 : Blo 1762082 1762599 := bstep (se 1 (by rfl) ⟨1321949, by rfl⟩ : syracuseStep 1762599 = 2643899) B2643899
theorem B1762639 : Blo 1762082 1762639 := bstep (se 1 (by rfl) ⟨1321979, by rfl⟩ : syracuseStep 1762639 = 2643959) B2643959
theorem B1762655 : Blo 1762082 1762655 := bstep (se 1 (by rfl) ⟨1321991, by rfl⟩ : syracuseStep 1762655 = 2643983) B2643983
theorem B1762683 : Blo 1762082 1762683 := bstep (se 1 (by rfl) ⟨1322012, by rfl⟩ : syracuseStep 1762683 = 2644025) B2644025
theorem B5948801 : Blo 1762082 5948801 := bstep (se 2 (by rfl) ⟨2230800, by rfl⟩ : syracuseStep 5948801 = 4461601) B4461601
theorem B1762735 : Blo 1762082 1762735 := bstep (se 1 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 1762735 = 2644103) B2644103
theorem B1983919 : Blo 1762082 1983919 := bstep (se 1 (by rfl) ⟨1487939, by rfl⟩ : syracuseStep 1983919 = 2975879) B2975879
theorem B1762759 : Blo 1762082 1762759 := bstep (se 1 (by rfl) ⟨1322069, by rfl⟩ : syracuseStep 1762759 = 2644139) B2644139
theorem B1762779 : Blo 1762082 1762779 := bstep (se 1 (by rfl) ⟨1322084, by rfl⟩ : syracuseStep 1762779 = 2644169) B2644169
theorem B1762855 : Blo 1762082 1762855 := bstep (se 1 (by rfl) ⟨1322141, by rfl⟩ : syracuseStep 1762855 = 2644283) B2644283
theorem B1762895 : Blo 1762082 1762895 := bstep (se 1 (by rfl) ⟨1322171, by rfl⟩ : syracuseStep 1762895 = 2644343) B2644343
theorem B1762911 : Blo 1762082 1762911 := bstep (se 1 (by rfl) ⟨1322183, by rfl⟩ : syracuseStep 1762911 = 2644367) B2644367
theorem B3966587 : Blo 1762082 3966587 := bstep (se 1 (by rfl) ⟨2974940, by rfl⟩ : syracuseStep 3966587 = 5949881) B5949881
theorem B1762939 : Blo 1762082 1762939 := bstep (se 1 (by rfl) ⟨1322204, by rfl⟩ : syracuseStep 1762939 = 2644409) B2644409
theorem B10045073 : Blo 1762082 10045073 := bstep (se 2 (by rfl) ⟨3766902, by rfl⟩ : syracuseStep 10045073 = 7533805) B7533805
theorem B1762991 : Blo 1762082 1762991 := bstep (se 1 (by rfl) ⟨1322243, by rfl⟩ : syracuseStep 1762991 = 2644487) B2644487
theorem B6784697 : Blo 1762082 6784697 := bstep (se 2 (by rfl) ⟨2544261, by rfl⟩ : syracuseStep 6784697 = 5088523) B5088523
theorem B6694589 : Blo 1762082 6694589 := bstep (se 3 (by rfl) ⟨1255235, by rfl⟩ : syracuseStep 6694589 = 2510471) B2510471
theorem B1763015 : Blo 1762082 1763015 := bstep (se 1 (by rfl) ⟨1322261, by rfl⟩ : syracuseStep 1763015 = 2644523) B2644523
theorem B1763035 : Blo 1762082 1763035 := bstep (se 1 (by rfl) ⟨1322276, by rfl⟩ : syracuseStep 1763035 = 2644553) B2644553
theorem B3966713 : Blo 1762082 3966713 := bstep (se 2 (by rfl) ⟨1487517, by rfl⟩ : syracuseStep 3966713 = 2975035) B2975035
theorem B1763111 : Blo 1762082 1763111 := bstep (se 1 (by rfl) ⟨1322333, by rfl⟩ : syracuseStep 1763111 = 2644667) B2644667
theorem B1763151 : Blo 1762082 1763151 := bstep (se 1 (by rfl) ⟨1322363, by rfl⟩ : syracuseStep 1763151 = 2644727) B2644727
theorem B1763167 : Blo 1762082 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1984351 : Blo 1762082 1984351 := bstep (se 1 (by rfl) ⟨1488263, by rfl⟩ : syracuseStep 1984351 = 2976527) B2976527
theorem B1763195 : Blo 1762082 1763195 := bstep (se 1 (by rfl) ⟨1322396, by rfl⟩ : syracuseStep 1763195 = 2644793) B2644793
theorem B1763247 : Blo 1762082 1763247 := bstep (se 1 (by rfl) ⟨1322435, by rfl⟩ : syracuseStep 1763247 = 2644871) B2644871
theorem B2975663 : Blo 1762082 2975663 := bstep (se 1 (by rfl) ⟨2231747, by rfl⟩ : syracuseStep 2975663 = 4463495) B4463495
theorem B1763271 : Blo 1762082 1763271 := bstep (se 1 (by rfl) ⟨1322453, by rfl⟩ : syracuseStep 1763271 = 2644907) B2644907
theorem B1763291 : Blo 1762082 1763291 := bstep (se 1 (by rfl) ⟨1322468, by rfl⟩ : syracuseStep 1763291 = 2644937) B2644937
theorem B65251331 : Blo 1762082 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B3966983 : Blo 1762082 3966983 := bstep (se 1 (by rfl) ⟨2975237, by rfl⟩ : syracuseStep 3966983 = 5950475) B5950475
theorem B11290661 : Blo 1762082 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B1763367 : Blo 1762082 1763367 := bstep (se 1 (by rfl) ⟨1322525, by rfl⟩ : syracuseStep 1763367 = 2645051) B2645051
theorem B3967055 : Blo 1762082 3967055 := bstep (se 1 (by rfl) ⟨2975291, by rfl⟩ : syracuseStep 3967055 = 5950583) B5950583
theorem B1763407 : Blo 1762082 1763407 := bstep (se 1 (by rfl) ⟨1322555, by rfl⟩ : syracuseStep 1763407 = 2645111) B2645111
theorem B10045529 : Blo 1762082 10045529 := bstep (se 2 (by rfl) ⟨3767073, by rfl⟩ : syracuseStep 10045529 = 7534147) B7534147
theorem B1763423 : Blo 1762082 1763423 := bstep (se 1 (by rfl) ⟨1322567, by rfl⟩ : syracuseStep 1763423 = 2645135) B2645135
theorem B1787999 : Blo 1762082 1787999 := bstep (se 1 (by rfl) ⟨1340999, by rfl⟩ : syracuseStep 1787999 = 2681999) B2681999
theorem B1763451 : Blo 1762082 1763451 := bstep (se 1 (by rfl) ⟨1322588, by rfl⟩ : syracuseStep 1763451 = 2645177) B2645177
theorem B5949611 : Blo 1762082 5949611 := bstep (se 1 (by rfl) ⟨4462208, by rfl⟩ : syracuseStep 5949611 = 8924417) B8924417
theorem B1763503 : Blo 1762082 1763503 := bstep (se 1 (by rfl) ⟨1322627, by rfl⟩ : syracuseStep 1763503 = 2645255) B2645255
theorem B1763527 : Blo 1762082 1763527 := bstep (se 1 (by rfl) ⟨1322645, by rfl⟩ : syracuseStep 1763527 = 2645291) B2645291
theorem B1763547 : Blo 1762082 1763547 := bstep (se 1 (by rfl) ⟨1322660, by rfl⟩ : syracuseStep 1763547 = 2645321) B2645321
theorem B1763623 : Blo 1762082 1763623 := bstep (se 1 (by rfl) ⟨1322717, by rfl⟩ : syracuseStep 1763623 = 2645435) B2645435
theorem B1763663 : Blo 1762082 1763663 := bstep (se 1 (by rfl) ⟨1322747, by rfl⟩ : syracuseStep 1763663 = 2645495) B2645495
theorem B19327319 : Blo 1762082 19327319 := bstep (se 1 (by rfl) ⟨14495489, by rfl⟩ : syracuseStep 19327319 = 28990979) B28990979
theorem B2976095 : Blo 1762082 2976095 := bstep (se 1 (by rfl) ⟨2232071, by rfl⟩ : syracuseStep 2976095 = 4464143) B4464143
theorem B1763679 : Blo 1762082 1763679 := bstep (se 1 (by rfl) ⟨1322759, by rfl⟩ : syracuseStep 1763679 = 2645519) B2645519
theorem B1763707 : Blo 1762082 1763707 := bstep (se 1 (by rfl) ⟨1322780, by rfl⟩ : syracuseStep 1763707 = 2645561) B2645561
theorem B76261783 : Blo 1762082 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B1763759 : Blo 1762082 1763759 := bstep (se 1 (by rfl) ⟨1322819, by rfl⟩ : syracuseStep 1763759 = 2645639) B2645639
theorem B1763783 : Blo 1762082 1763783 := bstep (se 1 (by rfl) ⟨1322837, by rfl⟩ : syracuseStep 1763783 = 2645675) B2645675
theorem B5646793 : Blo 1762082 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B3967451 : Blo 1762082 3967451 := bstep (se 1 (by rfl) ⟨2975588, by rfl⟩ : syracuseStep 3967451 = 5951177) B5951177
theorem B1763803 : Blo 1762082 1763803 := bstep (se 1 (by rfl) ⟨1322852, by rfl⟩ : syracuseStep 1763803 = 2645705) B2645705
theorem B2509321 : Blo 1762082 2509321 := bstep (se 2 (by rfl) ⟨940995, by rfl⟩ : syracuseStep 2509321 = 1881991) B1881991
theorem B1763879 : Blo 1762082 1763879 := bstep (se 1 (by rfl) ⟨1322909, by rfl⟩ : syracuseStep 1763879 = 2645819) B2645819
theorem B1763919 : Blo 1762082 1763919 := bstep (se 1 (by rfl) ⟨1322939, by rfl⟩ : syracuseStep 1763919 = 2645879) B2645879
theorem B1763935 : Blo 1762082 1763935 := bstep (se 1 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 1763935 = 2645903) B2645903
theorem B5646971 : Blo 1762082 5646971 := bstep (se 1 (by rfl) ⟨4235228, by rfl⟩ : syracuseStep 5646971 = 8470457) B8470457
theorem B1763963 : Blo 1762082 1763963 := bstep (se 1 (by rfl) ⟨1322972, by rfl⟩ : syracuseStep 1763963 = 2645945) B2645945
theorem B1764015 : Blo 1762082 1764015 := bstep (se 1 (by rfl) ⟨1323011, by rfl⟩ : syracuseStep 1764015 = 2646023) B2646023
theorem B5950151 : Blo 1762082 5950151 := bstep (se 1 (by rfl) ⟨4462613, by rfl⟩ : syracuseStep 5950151 = 8925227) B8925227
theorem B1764039 : Blo 1762082 1764039 := bstep (se 1 (by rfl) ⟨1323029, by rfl⟩ : syracuseStep 1764039 = 2646059) B2646059
theorem B1764059 : Blo 1762082 1764059 := bstep (se 1 (by rfl) ⟨1323044, by rfl⟩ : syracuseStep 1764059 = 2646089) B2646089
theorem B2976655 : Blo 1762082 2976655 := bstep (se 1 (by rfl) ⟨2232491, by rfl⟩ : syracuseStep 2976655 = 4464983) B4464983
theorem B3345313 : Blo 1762082 3345313 := bstep (se 2 (by rfl) ⟨1254492, by rfl⟩ : syracuseStep 3345313 = 2508985) B2508985
theorem B5647279 : Blo 1762082 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B3967919 : Blo 1762082 3967919 := bstep (se 1 (by rfl) ⟨2975939, by rfl⟩ : syracuseStep 3967919 = 5951879) B5951879
theorem B6696017 : Blo 1762082 6696017 := bstep (se 2 (by rfl) ⟨2511006, by rfl⟩ : syracuseStep 6696017 = 5022013) B5022013
theorem B3968171 : Blo 1762082 3968171 := bstep (se 1 (by rfl) ⟨2976128, by rfl⟩ : syracuseStep 3968171 = 5952257) B5952257
theorem B50834627 : Blo 1762082 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B2010463 : Blo 1762082 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B13381037 : Blo 1762082 13381037 := bstep (se 3 (by rfl) ⟨2508944, by rfl⟩ : syracuseStep 13381037 = 5017889) B5017889
theorem B11021741 : Blo 1762082 11021741 := bstep (se 3 (by rfl) ⟨2066576, by rfl⟩ : syracuseStep 11021741 = 4133153) B4133153
theorem B4763099 : Blo 1762082 4763099 := bstep (se 1 (by rfl) ⟨3572324, by rfl⟩ : syracuseStep 4763099 = 7144649) B7144649
theorem B13389299 : Blo 1762082 13389299 := bstep (se 1 (by rfl) ⟨10041974, by rfl⟩ : syracuseStep 13389299 = 20083949) B20083949
theorem B5951015 : Blo 1762082 5951015 := bstep (se 1 (by rfl) ⟨4463261, by rfl⟩ : syracuseStep 5951015 = 8926523) B8926523
theorem B10038923 : Blo 1762082 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B5951123 : Blo 1762082 5951123 := bstep (se 1 (by rfl) ⟨4463342, by rfl⟩ : syracuseStep 5951123 = 8926685) B8926685
theorem B3968711 : Blo 1762082 3968711 := bstep (se 1 (by rfl) ⟨2976533, by rfl⟩ : syracuseStep 3968711 = 5953067) B5953067
theorem B5951339 : Blo 1762082 5951339 := bstep (se 1 (by rfl) ⟨4463504, by rfl⟩ : syracuseStep 5951339 = 8927009) B8927009
theorem B5951393 : Blo 1762082 5951393 := bstep (se 2 (by rfl) ⟨2231772, by rfl⟩ : syracuseStep 5951393 = 4463545) B4463545
theorem B2510767 : Blo 1762082 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B22900751 : Blo 1762082 22900751 := bstep (se 1 (by rfl) ⟨17175563, by rfl⟩ : syracuseStep 22900751 = 34351127) B34351127
theorem B2117711 : Blo 1762082 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B6033523 : Blo 1762082 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B15265955 : Blo 1762082 15265955 := bstep (se 1 (by rfl) ⟨11449466, by rfl⟩ : syracuseStep 15265955 = 22898933) B22898933
theorem B78385357 : Blo 1762082 78385357 := bstep (se 3 (by rfl) ⟨14697254, by rfl⟩ : syracuseStep 78385357 = 29394509) B29394509
theorem B4460791 : Blo 1762082 4460791 := bstep (se 1 (by rfl) ⟨3345593, by rfl⟩ : syracuseStep 4460791 = 6691187) B6691187
theorem B9171305 : Blo 1762082 9171305 := bstep (se 2 (by rfl) ⟨3439239, by rfl⟩ : syracuseStep 9171305 = 6878479) B6878479
theorem B11456873 : Blo 1762082 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B5951987 : Blo 1762082 5951987 := bstep (se 1 (by rfl) ⟨4463990, by rfl⟩ : syracuseStep 5951987 = 8927981) B8927981
theorem B4461065 : Blo 1762082 4461065 := bstep (se 2 (by rfl) ⟨1672899, by rfl⟩ : syracuseStep 4461065 = 3345799) B3345799
theorem B16937495 : Blo 1762082 16937495 := bstep (se 1 (by rfl) ⟨12703121, by rfl⟩ : syracuseStep 16937495 = 25406243) B25406243
theorem B6697505 : Blo 1762082 6697505 := bstep (se 2 (by rfl) ⟨2511564, by rfl⟩ : syracuseStep 6697505 = 5023129) B5023129
theorem B4461095 : Blo 1762082 4461095 := bstep (se 1 (by rfl) ⟨3345821, by rfl⟩ : syracuseStep 4461095 = 6691643) B6691643
theorem B16937531 : Blo 1762082 16937531 := bstep (se 1 (by rfl) ⟨12703148, by rfl⟩ : syracuseStep 16937531 = 25406297) B25406297
theorem B6697687 : Blo 1762082 6697687 := bstep (se 1 (by rfl) ⟨5023265, by rfl⟩ : syracuseStep 6697687 = 10046531) B10046531
theorem B4461419 : Blo 1762082 4461419 := bstep (se 1 (by rfl) ⟨3346064, by rfl⟩ : syracuseStep 4461419 = 6692129) B6692129
theorem B30110615 : Blo 1762082 30110615 := bstep (se 1 (by rfl) ⟨22582961, by rfl⟩ : syracuseStep 30110615 = 45165923) B45165923
theorem B5436335 : Blo 1762082 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B6697991 : Blo 1762082 6697991 := bstep (se 1 (by rfl) ⟨5023493, by rfl⟩ : syracuseStep 6697991 = 10046987) B10046987
theorem B5952527 : Blo 1762082 5952527 := bstep (se 1 (by rfl) ⟨4464395, by rfl⟩ : syracuseStep 5952527 = 8928791) B8928791
theorem B18338867 : Blo 1762082 18338867 := bstep (se 1 (by rfl) ⟨13754150, by rfl⟩ : syracuseStep 18338867 = 27508301) B27508301
theorem B38122589 : Blo 1762082 38122589 := bstep (se 3 (by rfl) ⟨7147985, by rfl⟩ : syracuseStep 38122589 = 14295971) B14295971
theorem B8926361 : Blo 1762082 8926361 := bstep (se 2 (by rfl) ⟨3347385, by rfl⟩ : syracuseStep 8926361 = 6694771) B6694771
theorem B12711107 : Blo 1762082 12711107 := bstep (se 1 (by rfl) ⟨9533330, by rfl⟩ : syracuseStep 12711107 = 19066661) B19066661
theorem B2643143 : Blo 1762082 2643143 := bstep (se 1 (by rfl) ⟨1982357, by rfl⟩ : syracuseStep 2643143 = 3964715) B3964715
theorem B3347705 : Blo 1762082 3347705 := bstep (se 2 (by rfl) ⟨1255389, by rfl⟩ : syracuseStep 3347705 = 2510779) B2510779
theorem B18101519 : Blo 1762082 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B2643305 : Blo 1762082 2643305 := bstep (se 2 (by rfl) ⟨991239, by rfl⟩ : syracuseStep 2643305 = 1982479) B1982479
theorem B3347887 : Blo 1762082 3347887 := bstep (se 1 (by rfl) ⟨2510915, by rfl⟩ : syracuseStep 3347887 = 5021831) B5021831
theorem B2643383 : Blo 1762082 2643383 := bstep (se 1 (by rfl) ⟨1982537, by rfl⟩ : syracuseStep 2643383 = 3965075) B3965075
theorem B2643419 : Blo 1762082 2643419 := bstep (se 1 (by rfl) ⟨1982564, by rfl⟩ : syracuseStep 2643419 = 3965129) B3965129
theorem B4462067 : Blo 1762082 4462067 := bstep (se 1 (by rfl) ⟨3346550, by rfl⟩ : syracuseStep 4462067 = 6693101) B6693101
theorem B3348047 : Blo 1762082 3348047 := bstep (se 1 (by rfl) ⟨2511035, by rfl⟩ : syracuseStep 3348047 = 5022071) B5022071
theorem B5953121 : Blo 1762082 5953121 := bstep (se 2 (by rfl) ⟨2232420, by rfl⟩ : syracuseStep 5953121 = 4464841) B4464841
theorem B3815111 : Blo 1762082 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B5019347 : Blo 1762082 5019347 := bstep (se 1 (by rfl) ⟨3764510, by rfl⟩ : syracuseStep 5019347 = 7529021) B7529021
theorem B3176185 : Blo 1762082 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B13383467 : Blo 1762082 13383467 := bstep (se 1 (by rfl) ⟨10037600, by rfl⟩ : syracuseStep 13383467 = 20075201) B20075201
theorem B10041155 : Blo 1762082 10041155 := bstep (se 1 (by rfl) ⟨7530866, by rfl⟩ : syracuseStep 10041155 = 15061733) B15061733
theorem B2643887 : Blo 1762082 2643887 := bstep (se 1 (by rfl) ⟨1982915, by rfl⟩ : syracuseStep 2643887 = 3965831) B3965831
theorem B4462523 : Blo 1762082 4462523 := bstep (se 1 (by rfl) ⟨3346892, by rfl⟩ : syracuseStep 4462523 = 6693785) B6693785
theorem B18102209 : Blo 1762082 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B13563911 : Blo 1762082 13563911 := bstep (se 1 (by rfl) ⟨10172933, by rfl⟩ : syracuseStep 13563911 = 20345867) B20345867
theorem B2643977 : Blo 1762082 2643977 := bstep (se 2 (by rfl) ⟨991491, by rfl⟩ : syracuseStep 2643977 = 1982983) B1982983
theorem B2644007 : Blo 1762082 2644007 := bstep (se 1 (by rfl) ⟨1983005, by rfl⟩ : syracuseStep 2644007 = 3966011) B3966011
theorem B2824249 : Blo 1762082 2824249 := bstep (se 2 (by rfl) ⟨1059093, by rfl⟩ : syracuseStep 2824249 = 2118187) B2118187
theorem B7247951 : Blo 1762082 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B2644091 : Blo 1762082 2644091 := bstep (se 1 (by rfl) ⟨1983068, by rfl⟩ : syracuseStep 2644091 = 3966137) B3966137
theorem B2644217 : Blo 1762082 2644217 := bstep (se 2 (by rfl) ⟨991581, by rfl⟩ : syracuseStep 2644217 = 1983163) B1983163
theorem B13392215 : Blo 1762082 13392215 := bstep (se 1 (by rfl) ⟨10044161, by rfl⟩ : syracuseStep 13392215 = 20088323) B20088323
theorem B2644319 : Blo 1762082 2644319 := bstep (se 1 (by rfl) ⟨1983239, by rfl⟩ : syracuseStep 2644319 = 3966479) B3966479
theorem B2644331 : Blo 1762082 2644331 := bstep (se 1 (by rfl) ⟨1983248, by rfl⟩ : syracuseStep 2644331 = 3966497) B3966497
theorem B2644559 : Blo 1762082 2644559 := bstep (se 1 (by rfl) ⟨1983419, by rfl⟩ : syracuseStep 2644559 = 3966839) B3966839
theorem B4463201 : Blo 1762082 4463201 := bstep (se 2 (by rfl) ⟨1673700, by rfl⟩ : syracuseStep 4463201 = 3347401) B3347401
theorem B2644679 : Blo 1762082 2644679 := bstep (se 1 (by rfl) ⟨1983509, by rfl⟩ : syracuseStep 2644679 = 3967019) B3967019
theorem B2644841 : Blo 1762082 2644841 := bstep (se 2 (by rfl) ⟨991815, by rfl⟩ : syracuseStep 2644841 = 1983631) B1983631
theorem B2644919 : Blo 1762082 2644919 := bstep (se 1 (by rfl) ⟨1983689, by rfl⟩ : syracuseStep 2644919 = 3967379) B3967379
theorem B2644955 : Blo 1762082 2644955 := bstep (se 1 (by rfl) ⟨1983716, by rfl⟩ : syracuseStep 2644955 = 3967433) B3967433
theorem B6691841 : Blo 1762082 6691841 := bstep (se 2 (by rfl) ⟨2509440, by rfl⟩ : syracuseStep 6691841 = 5018881) B5018881
theorem B6691855 : Blo 1762082 6691855 := bstep (se 1 (by rfl) ⟨5018891, by rfl⟩ : syracuseStep 6691855 = 10037783) B10037783
theorem B2825255 : Blo 1762082 2825255 := bstep (se 1 (by rfl) ⟨2118941, by rfl⟩ : syracuseStep 2825255 = 4237883) B4237883
theorem B11295787 : Blo 1762082 11295787 := bstep (se 1 (by rfl) ⟨8471840, by rfl⟩ : syracuseStep 11295787 = 16943681) B16943681
theorem B3177569 : Blo 1762082 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B5020829 : Blo 1762082 5020829 := bstep (se 3 (by rfl) ⟨941405, by rfl⟩ : syracuseStep 5020829 = 1882811) B1882811
theorem B3767467 : Blo 1762082 3767467 := bstep (se 1 (by rfl) ⟨2825600, by rfl⟩ : syracuseStep 3767467 = 5651201) B5651201
theorem B22592803 : Blo 1762082 22592803 := bstep (se 1 (by rfl) ⟨16944602, by rfl⟩ : syracuseStep 22592803 = 33889205) B33889205
theorem B2645423 : Blo 1762082 2645423 := bstep (se 1 (by rfl) ⟨1984067, by rfl⟩ : syracuseStep 2645423 = 3968135) B3968135
theorem B2645513 : Blo 1762082 2645513 := bstep (se 2 (by rfl) ⟨992067, by rfl⟩ : syracuseStep 2645513 = 1984135) B1984135
theorem B83623453 : Blo 1762082 83623453 := bstep (se 3 (by rfl) ⟨15679397, by rfl⟩ : syracuseStep 83623453 = 31358795) B31358795
theorem B2645543 : Blo 1762082 2645543 := bstep (se 1 (by rfl) ⟨1984157, by rfl⟩ : syracuseStep 2645543 = 3968315) B3968315
theorem B2645627 : Blo 1762082 2645627 := bstep (se 1 (by rfl) ⟨1984220, by rfl⟩ : syracuseStep 2645627 = 3968441) B3968441
theorem B2645753 : Blo 1762082 2645753 := bstep (se 2 (by rfl) ⟨992157, by rfl⟩ : syracuseStep 2645753 = 1984315) B1984315
theorem B8044331 : Blo 1762082 8044331 := bstep (se 1 (by rfl) ⟨6033248, by rfl⟩ : syracuseStep 8044331 = 12066497) B12066497
theorem B2645855 : Blo 1762082 2645855 := bstep (se 1 (by rfl) ⟨1984391, by rfl⟩ : syracuseStep 2645855 = 3968783) B3968783
theorem B2645867 : Blo 1762082 2645867 := bstep (se 1 (by rfl) ⟨1984400, by rfl⟩ : syracuseStep 2645867 = 3968801) B3968801
theorem B10043297 : Blo 1762082 10043297 := bstep (se 2 (by rfl) ⟨3766236, by rfl⟩ : syracuseStep 10043297 = 7532473) B7532473
theorem B5021615 : Blo 1762082 5021615 := bstep (se 1 (by rfl) ⟨3766211, by rfl⟩ : syracuseStep 5021615 = 7532423) B7532423
theorem B3964859 : Blo 1762082 3964859 := bstep (se 1 (by rfl) ⟨2973644, by rfl⟩ : syracuseStep 3964859 = 5947289) B5947289
theorem B76283927 : Blo 1762082 76283927 := bstep (se 1 (by rfl) ⟨57212945, by rfl⟩ : syracuseStep 76283927 = 114425891) B114425891
theorem B5947451 : Blo 1762082 5947451 := bstep (se 1 (by rfl) ⟨4460588, by rfl⟩ : syracuseStep 5947451 = 8921177) B8921177
theorem B8044697 : Blo 1762082 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B4767997 : Blo 1762082 4767997 := bstep (se 3 (by rfl) ⟨893999, by rfl⟩ : syracuseStep 4767997 = 1787999) B1787999
theorem B104513809 : Blo 1762082 104513809 := bstep (se 2 (by rfl) ⟨39192678, by rfl⟩ : syracuseStep 104513809 = 78385357) B78385357
theorem B5947721 : Blo 1762082 5947721 := bstep (se 2 (by rfl) ⟨2230395, by rfl⟩ : syracuseStep 5947721 = 4460791) B4460791
theorem B2974043 : Blo 1762082 2974043 := bstep (se 1 (by rfl) ⟨2230532, by rfl⟩ : syracuseStep 2974043 = 4461065) B4461065
theorem B3965291 : Blo 1762082 3965291 := bstep (se 1 (by rfl) ⟨2973968, by rfl⟩ : syracuseStep 3965291 = 5947937) B5947937
theorem B4465003 : Blo 1762082 4465003 := bstep (se 1 (by rfl) ⟨3348752, by rfl⟩ : syracuseStep 4465003 = 6697505) B6697505
theorem B2974063 : Blo 1762082 2974063 := bstep (se 1 (by rfl) ⟨2230547, by rfl⟩ : syracuseStep 2974063 = 4461095) B4461095
theorem B3965435 : Blo 1762082 3965435 := bstep (se 1 (by rfl) ⟨2974076, by rfl⟩ : syracuseStep 3965435 = 5948153) B5948153
theorem B2974279 : Blo 1762082 2974279 := bstep (se 1 (by rfl) ⟨2230709, by rfl⟩ : syracuseStep 2974279 = 4461419) B4461419
theorem B7529057 : Blo 1762082 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B3965561 : Blo 1762082 3965561 := bstep (se 2 (by rfl) ⟨1487085, by rfl⟩ : syracuseStep 3965561 = 2974171) B2974171
theorem B3965615 : Blo 1762082 3965615 := bstep (se 1 (by rfl) ⟨2974211, by rfl⟩ : syracuseStep 3965615 = 5948423) B5948423
theorem B4465327 : Blo 1762082 4465327 := bstep (se 1 (by rfl) ⟨3348995, by rfl⟩ : syracuseStep 4465327 = 6697991) B6697991
theorem B1983199 : Blo 1762082 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B3965687 : Blo 1762082 3965687 := bstep (se 1 (by rfl) ⟨2974265, by rfl⟩ : syracuseStep 3965687 = 5948531) B5948531
theorem B1762095 : Blo 1762082 1762095 := bstep (se 1 (by rfl) ⟨1321571, by rfl⟩ : syracuseStep 1762095 = 2643143) B2643143
theorem B12067679 : Blo 1762082 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B1762203 : Blo 1762082 1762203 := bstep (se 1 (by rfl) ⟨1321652, by rfl⟩ : syracuseStep 1762203 = 2643305) B2643305
theorem B3965867 : Blo 1762082 3965867 := bstep (se 1 (by rfl) ⟨2974400, by rfl⟩ : syracuseStep 3965867 = 5948801) B5948801
theorem B8930249 : Blo 1762082 8930249 := bstep (se 2 (by rfl) ⟨3348843, by rfl⟩ : syracuseStep 8930249 = 6697687) B6697687
theorem B1762255 : Blo 1762082 1762255 := bstep (se 1 (by rfl) ⟨1321691, by rfl⟩ : syracuseStep 1762255 = 2643383) B2643383
theorem B1762279 : Blo 1762082 1762279 := bstep (se 1 (by rfl) ⟨1321709, by rfl⟩ : syracuseStep 1762279 = 2643419) B2643419
theorem B2974711 : Blo 1762082 2974711 := bstep (se 1 (by rfl) ⟨2231033, by rfl⟩ : syracuseStep 2974711 = 4462067) B4462067
theorem B4523131 : Blo 1762082 4523131 := bstep (se 1 (by rfl) ⟨3392348, by rfl⟩ : syracuseStep 4523131 = 6784697) B6784697
theorem B8922311 : Blo 1762082 8922311 := bstep (se 1 (by rfl) ⟨6691733, by rfl⟩ : syracuseStep 8922311 = 13383467) B13383467
theorem B6694103 : Blo 1762082 6694103 := bstep (se 1 (by rfl) ⟨5020577, by rfl⟩ : syracuseStep 6694103 = 10041155) B10041155
theorem B7529705 : Blo 1762082 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B1762591 : Blo 1762082 1762591 := bstep (se 1 (by rfl) ⟨1321943, by rfl⟩ : syracuseStep 1762591 = 2643887) B2643887
theorem B1983775 : Blo 1762082 1983775 := bstep (se 1 (by rfl) ⟨1487831, by rfl⟩ : syracuseStep 1983775 = 2975663) B2975663
theorem B2975015 : Blo 1762082 2975015 := bstep (se 1 (by rfl) ⟨2231261, by rfl⟩ : syracuseStep 2975015 = 4462523) B4462523
theorem B43500887 : Blo 1762082 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B1762651 : Blo 1762082 1762651 := bstep (se 1 (by rfl) ⟨1321988, by rfl⟩ : syracuseStep 1762651 = 2643977) B2643977
theorem B8922473 : Blo 1762082 8922473 := bstep (se 2 (by rfl) ⟨3345927, by rfl⟩ : syracuseStep 8922473 = 6691855) B6691855
theorem B12715373 : Blo 1762082 12715373 := bstep (se 3 (by rfl) ⟨2384132, by rfl⟩ : syracuseStep 12715373 = 4768265) B4768265
theorem B1762671 : Blo 1762082 1762671 := bstep (se 1 (by rfl) ⟨1322003, by rfl⟩ : syracuseStep 1762671 = 2644007) B2644007
theorem B1762727 : Blo 1762082 1762727 := bstep (se 1 (by rfl) ⟨1322045, by rfl⟩ : syracuseStep 1762727 = 2644091) B2644091
theorem B18089405 : Blo 1762082 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B3966407 : Blo 1762082 3966407 := bstep (se 1 (by rfl) ⟨2974805, by rfl⟩ : syracuseStep 3966407 = 5949611) B5949611
theorem B1762811 : Blo 1762082 1762811 := bstep (se 1 (by rfl) ⟨1322108, by rfl⟩ : syracuseStep 1762811 = 2644217) B2644217
theorem B5023289 : Blo 1762082 5023289 := bstep (se 2 (by rfl) ⟨1883733, by rfl⟩ : syracuseStep 5023289 = 3767467) B3767467
theorem B1762879 : Blo 1762082 1762879 := bstep (se 1 (by rfl) ⟨1322159, by rfl⟩ : syracuseStep 1762879 = 2644319) B2644319
theorem B1984063 : Blo 1762082 1984063 := bstep (se 1 (by rfl) ⟨1488047, by rfl⟩ : syracuseStep 1984063 = 2976095) B2976095
theorem B1762887 : Blo 1762082 1762887 := bstep (se 1 (by rfl) ⟨1322165, by rfl⟩ : syracuseStep 1762887 = 2644331) B2644331
theorem B30123737 : Blo 1762082 30123737 := bstep (se 2 (by rfl) ⟨11296401, by rfl⟩ : syracuseStep 30123737 = 22592803) B22592803
theorem B1763039 : Blo 1762082 1763039 := bstep (se 1 (by rfl) ⟨1322279, by rfl⟩ : syracuseStep 1763039 = 2644559) B2644559
theorem B2975467 : Blo 1762082 2975467 := bstep (se 1 (by rfl) ⟨2231600, by rfl⟩ : syracuseStep 2975467 = 4463201) B4463201
theorem B3966767 : Blo 1762082 3966767 := bstep (se 1 (by rfl) ⟨2975075, by rfl⟩ : syracuseStep 3966767 = 5950151) B5950151
theorem B1763119 : Blo 1762082 1763119 := bstep (se 1 (by rfl) ⟨1322339, by rfl⟩ : syracuseStep 1763119 = 2644679) B2644679
theorem B1763227 : Blo 1762082 1763227 := bstep (se 1 (by rfl) ⟨1322420, by rfl⟩ : syracuseStep 1763227 = 2644841) B2644841
theorem B1763279 : Blo 1762082 1763279 := bstep (se 1 (by rfl) ⟨1322459, by rfl⟩ : syracuseStep 1763279 = 2644919) B2644919
theorem B1763303 : Blo 1762082 1763303 := bstep (se 1 (by rfl) ⟨1322477, by rfl⟩ : syracuseStep 1763303 = 2644955) B2644955
theorem B13568285 : Blo 1762082 13568285 := bstep (se 3 (by rfl) ⟨2544053, by rfl⟩ : syracuseStep 13568285 = 5088107) B5088107
theorem B1763615 : Blo 1762082 1763615 := bstep (se 1 (by rfl) ⟨1322711, by rfl⟩ : syracuseStep 1763615 = 2645423) B2645423
theorem B1763675 : Blo 1762082 1763675 := bstep (se 1 (by rfl) ⟨1322756, by rfl⟩ : syracuseStep 1763675 = 2645513) B2645513
theorem B3967343 : Blo 1762082 3967343 := bstep (se 1 (by rfl) ⟨2975507, by rfl⟩ : syracuseStep 3967343 = 5951015) B5951015
theorem B1763695 : Blo 1762082 1763695 := bstep (se 1 (by rfl) ⟨1322771, by rfl⟩ : syracuseStep 1763695 = 2645543) B2645543
theorem B1763751 : Blo 1762082 1763751 := bstep (se 1 (by rfl) ⟨1322813, by rfl⟩ : syracuseStep 1763751 = 2645627) B2645627
theorem B3967415 : Blo 1762082 3967415 := bstep (se 1 (by rfl) ⟨2975561, by rfl⟩ : syracuseStep 3967415 = 5951123) B5951123
theorem B1763835 : Blo 1762082 1763835 := bstep (se 1 (by rfl) ⟨1322876, by rfl⟩ : syracuseStep 1763835 = 2645753) B2645753
theorem B1763903 : Blo 1762082 1763903 := bstep (se 1 (by rfl) ⟨1322927, by rfl⟩ : syracuseStep 1763903 = 2645855) B2645855
theorem B3967559 : Blo 1762082 3967559 := bstep (se 1 (by rfl) ⟨2975669, by rfl⟩ : syracuseStep 3967559 = 5951339) B5951339
theorem B1763911 : Blo 1762082 1763911 := bstep (se 1 (by rfl) ⟨1322933, by rfl⟩ : syracuseStep 1763911 = 2645867) B2645867
theorem B3967595 : Blo 1762082 3967595 := bstep (se 1 (by rfl) ⟨2975696, by rfl⟩ : syracuseStep 3967595 = 5951393) B5951393
theorem B6695531 : Blo 1762082 6695531 := bstep (se 1 (by rfl) ⟨5021648, by rfl⟩ : syracuseStep 6695531 = 10043297) B10043297
theorem B2976439 : Blo 1762082 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B1764063 : Blo 1762082 1764063 := bstep (se 1 (by rfl) ⟨1323047, by rfl⟩ : syracuseStep 1764063 = 2646095) B2646095
theorem B5647229 : Blo 1762082 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B6974351 : Blo 1762082 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B6114203 : Blo 1762082 6114203 := bstep (se 1 (by rfl) ⟨4585652, by rfl⟩ : syracuseStep 6114203 = 9171305) B9171305
theorem B7637915 : Blo 1762082 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B8473517 : Blo 1762082 8473517 := bstep (se 3 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 8473517 = 3177569) B3177569
theorem B2976743 : Blo 1762082 2976743 := bstep (se 1 (by rfl) ⟨2232557, by rfl⟩ : syracuseStep 2976743 = 4465115) B4465115
theorem B3967991 : Blo 1762082 3967991 := bstep (se 1 (by rfl) ⟨2975993, by rfl⟩ : syracuseStep 3967991 = 5951987) B5951987
theorem B11291663 : Blo 1762082 11291663 := bstep (se 1 (by rfl) ⟨8468747, by rfl⟩ : syracuseStep 11291663 = 16937495) B16937495
theorem B11291687 : Blo 1762082 11291687 := bstep (se 1 (by rfl) ⟨8468765, by rfl⟩ : syracuseStep 11291687 = 16937531) B16937531
theorem B40709213 : Blo 1762082 40709213 := bstep (se 3 (by rfl) ⟨7632977, by rfl⟩ : syracuseStep 40709213 = 15265955) B15265955
theorem B101682377 : Blo 1762082 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B10038491 : Blo 1762082 10038491 := bstep (se 1 (by rfl) ⟨7528868, by rfl⟩ : syracuseStep 10038491 = 15057737) B15057737
theorem B20073743 : Blo 1762082 20073743 := bstep (se 1 (by rfl) ⟨15055307, by rfl⟩ : syracuseStep 20073743 = 30110615) B30110615
theorem B1783966997 : Blo 1762082 1783966997 := bstep (se 6 (by rfl) ⟨41811726, by rfl⟩ : syracuseStep 1783966997 = 83623453) B83623453
theorem B22588703 : Blo 1762082 22588703 := bstep (se 1 (by rfl) ⟨16941527, by rfl⟩ : syracuseStep 22588703 = 33883055) B33883055
theorem B3968351 : Blo 1762082 3968351 := bstep (se 1 (by rfl) ⟨2976263, by rfl⟩ : syracuseStep 3968351 = 5952527) B5952527
theorem B3345761 : Blo 1762082 3345761 := bstep (se 2 (by rfl) ⟨1254660, by rfl⟩ : syracuseStep 3345761 = 2509321) B2509321
theorem B12225911 : Blo 1762082 12225911 := bstep (se 1 (by rfl) ⟨9169433, by rfl⟩ : syracuseStep 12225911 = 18338867) B18338867
theorem B25415059 : Blo 1762082 25415059 := bstep (se 1 (by rfl) ⟨19061294, by rfl⟩ : syracuseStep 25415059 = 38122589) B38122589
theorem B5950907 : Blo 1762082 5950907 := bstep (se 1 (by rfl) ⟨4463180, by rfl⟩ : syracuseStep 5950907 = 8926361) B8926361
theorem B8474071 : Blo 1762082 8474071 := bstep (se 1 (by rfl) ⟨6355553, by rfl⟩ : syracuseStep 8474071 = 12711107) B12711107
theorem B28585457 : Blo 1762082 28585457 := bstep (se 2 (by rfl) ⟨10719546, by rfl⟩ : syracuseStep 28585457 = 21439093) B21439093
theorem B2231803 : Blo 1762082 2231803 := bstep (se 1 (by rfl) ⟨1673852, by rfl⟩ : syracuseStep 2231803 = 3347705) B3347705
theorem B2232031 : Blo 1762082 2232031 := bstep (se 1 (by rfl) ⟨1674023, by rfl⟩ : syracuseStep 2232031 = 3348047) B3348047
theorem B3968747 : Blo 1762082 3968747 := bstep (se 1 (by rfl) ⟨2976560, by rfl⟩ : syracuseStep 3968747 = 5953121) B5953121
theorem B6696715 : Blo 1762082 6696715 := bstep (se 1 (by rfl) ⟨5022536, by rfl⟩ : syracuseStep 6696715 = 10045073) B10045073
theorem B2543407 : Blo 1762082 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B3968873 : Blo 1762082 3968873 := bstep (se 2 (by rfl) ⟨1488327, by rfl⟩ : syracuseStep 3968873 = 2976655) B2976655
theorem B4460417 : Blo 1762082 4460417 := bstep (se 2 (by rfl) ⟨1672656, by rfl⟩ : syracuseStep 4460417 = 3345313) B3345313
theorem B15061049 : Blo 1762082 15061049 := bstep (se 2 (by rfl) ⟨5647893, by rfl⟩ : syracuseStep 15061049 = 11295787) B11295787
theorem B6697019 : Blo 1762082 6697019 := bstep (se 1 (by rfl) ⟨5022764, by rfl⟩ : syracuseStep 6697019 = 10045529) B10045529
theorem B3764647 : Blo 1762082 3764647 := bstep (se 1 (by rfl) ⟨2823485, by rfl⟩ : syracuseStep 3764647 = 5646971) B5646971
theorem B4461227 : Blo 1762082 4461227 := bstep (se 1 (by rfl) ⟨3345920, by rfl⟩ : syracuseStep 4461227 = 6691841) B6691841
theorem B193090229 : Blo 1762082 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B3347219 : Blo 1762082 3347219 := bstep (se 1 (by rfl) ⟨2510414, by rfl⟩ : syracuseStep 3347219 = 5020829) B5020829
theorem B21451549 : Blo 1762082 21451549 := bstep (se 3 (by rfl) ⟨4022165, by rfl⟩ : syracuseStep 21451549 = 8044331) B8044331
theorem B13390757 : Blo 1762082 13390757 := bstep (se 4 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 13390757 = 2510767) B2510767
theorem B3175399 : Blo 1762082 3175399 := bstep (se 1 (by rfl) ⟨2381549, by rfl⟩ : syracuseStep 3175399 = 4763099) B4763099
theorem B8926199 : Blo 1762082 8926199 := bstep (se 1 (by rfl) ⟨6694649, by rfl⟩ : syracuseStep 8926199 = 13389299) B13389299
theorem B14496893 : Blo 1762082 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B3347743 : Blo 1762082 3347743 := bstep (se 1 (by rfl) ⟨2510807, by rfl⟩ : syracuseStep 3347743 = 5021615) B5021615
theorem B2643239 : Blo 1762082 2643239 := bstep (se 1 (by rfl) ⟨1982429, by rfl⟩ : syracuseStep 2643239 = 3964859) B3964859
theorem B15267167 : Blo 1762082 15267167 := bstep (se 1 (by rfl) ⟨11450375, by rfl⟩ : syracuseStep 15267167 = 22900751) B22900751
theorem B2643323 : Blo 1762082 2643323 := bstep (se 1 (by rfl) ⟨1982492, by rfl⟩ : syracuseStep 2643323 = 3964985) B3964985
theorem B13391243 : Blo 1762082 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B3765665 : Blo 1762082 3765665 := bstep (se 2 (by rfl) ⟨1412124, by rfl⟩ : syracuseStep 3765665 = 2824249) B2824249
theorem B2643449 : Blo 1762082 2643449 := bstep (se 2 (by rfl) ⟨991293, by rfl⟩ : syracuseStep 2643449 = 1982587) B1982587
theorem B4462087 : Blo 1762082 4462087 := bstep (se 1 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 4462087 = 6693131) B6693131
theorem B2643551 : Blo 1762082 2643551 := bstep (se 1 (by rfl) ⟨1982663, by rfl⟩ : syracuseStep 2643551 = 3965327) B3965327
theorem B2643767 : Blo 1762082 2643767 := bstep (se 1 (by rfl) ⟨1982825, by rfl⟩ : syracuseStep 2643767 = 3965651) B3965651
theorem B4462391 : Blo 1762082 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B2644073 : Blo 1762082 2644073 := bstep (se 2 (by rfl) ⟨991527, by rfl⟩ : syracuseStep 2644073 = 1983055) B1983055
theorem B2644391 : Blo 1762082 2644391 := bstep (se 1 (by rfl) ⟨1983293, by rfl⟩ : syracuseStep 2644391 = 3966587) B3966587
theorem B4463059 : Blo 1762082 4463059 := bstep (se 1 (by rfl) ⟨3347294, by rfl⟩ : syracuseStep 4463059 = 6694589) B6694589
theorem B2644475 : Blo 1762082 2644475 := bstep (se 1 (by rfl) ⟨1983356, by rfl⟩ : syracuseStep 2644475 = 3966713) B3966713
theorem B2644601 : Blo 1762082 2644601 := bstep (se 2 (by rfl) ⟨991725, by rfl⟩ : syracuseStep 2644601 = 1983451) B1983451
theorem B9042607 : Blo 1762082 9042607 := bstep (se 1 (by rfl) ⟨6781955, by rfl⟩ : syracuseStep 9042607 = 13563911) B13563911
theorem B2644655 : Blo 1762082 2644655 := bstep (se 1 (by rfl) ⟨1983491, by rfl⟩ : syracuseStep 2644655 = 3966983) B3966983
theorem B7527107 : Blo 1762082 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B2644703 : Blo 1762082 2644703 := bstep (se 1 (by rfl) ⟨1983527, by rfl⟩ : syracuseStep 2644703 = 3967055) B3967055
theorem B4831967 : Blo 1762082 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B12884879 : Blo 1762082 12884879 := bstep (se 1 (by rfl) ⟨9663659, by rfl⟩ : syracuseStep 12884879 = 19327319) B19327319
theorem B8928143 : Blo 1762082 8928143 := bstep (se 1 (by rfl) ⟨6696107, by rfl⟩ : syracuseStep 8928143 = 13392215) B13392215
theorem B2644967 : Blo 1762082 2644967 := bstep (se 1 (by rfl) ⟨1983725, by rfl⟩ : syracuseStep 2644967 = 3967451) B3967451
theorem B10722469 : Blo 1762082 10722469 := bstep (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) B2010463
theorem B13384925 : Blo 1762082 13384925 := bstep (se 3 (by rfl) ⟨2509673, by rfl⟩ : syracuseStep 13384925 = 5019347) B5019347
theorem B2645225 : Blo 1762082 2645225 := bstep (se 2 (by rfl) ⟨991959, by rfl⟩ : syracuseStep 2645225 = 1983919) B1983919
theorem B4463849 : Blo 1762082 4463849 := bstep (se 2 (by rfl) ⟨1673943, by rfl⟩ : syracuseStep 4463849 = 3347887) B3347887
theorem B2645279 : Blo 1762082 2645279 := bstep (se 1 (by rfl) ⟨1983959, by rfl⟩ : syracuseStep 2645279 = 3967919) B3967919
theorem B1883503 : Blo 1762082 1883503 := bstep (se 1 (by rfl) ⟨1412627, by rfl⟩ : syracuseStep 1883503 = 2825255) B2825255
theorem B4464011 : Blo 1762082 4464011 := bstep (se 1 (by rfl) ⟨3348008, by rfl⟩ : syracuseStep 4464011 = 6696017) B6696017
theorem B2645447 : Blo 1762082 2645447 := bstep (se 1 (by rfl) ⟨1984085, by rfl⟩ : syracuseStep 2645447 = 3968171) B3968171
theorem B33889751 : Blo 1762082 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B8920691 : Blo 1762082 8920691 := bstep (se 1 (by rfl) ⟨6690518, by rfl⟩ : syracuseStep 8920691 = 13381037) B13381037
theorem B7347827 : Blo 1762082 7347827 := bstep (se 1 (by rfl) ⟨5510870, by rfl⟩ : syracuseStep 7347827 = 11021741) B11021741
theorem B4234913 : Blo 1762082 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B6692615 : Blo 1762082 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B2645801 : Blo 1762082 2645801 := bstep (se 2 (by rfl) ⟨992175, by rfl⟩ : syracuseStep 2645801 = 1984351) B1984351
theorem B2645807 : Blo 1762082 2645807 := bstep (se 1 (by rfl) ⟨1984355, by rfl⟩ : syracuseStep 2645807 = 3968711) B3968711
theorem B50855951 : Blo 1762082 50855951 := bstep (se 1 (by rfl) ⟨38141963, by rfl⟩ : syracuseStep 50855951 = 76283927) B76283927
theorem B3964967 : Blo 1762082 3964967 := bstep (se 1 (by rfl) ⟨2973725, by rfl⟩ : syracuseStep 3964967 = 5947451) B5947451
theorem B4464679 : Blo 1762082 4464679 := bstep (se 1 (by rfl) ⟨3348509, by rfl⟩ : syracuseStep 4464679 = 6697019) B6697019
theorem B3965147 : Blo 1762082 3965147 := bstep (se 1 (by rfl) ⟨2973860, by rfl⟩ : syracuseStep 3965147 = 5947721) B5947721
theorem B1982695 : Blo 1762082 1982695 := bstep (se 1 (by rfl) ⟨1487021, by rfl⟩ : syracuseStep 1982695 = 2974043) B2974043
theorem B6357329 : Blo 1762082 6357329 := bstep (se 2 (by rfl) ⟨2383998, by rfl⟩ : syracuseStep 6357329 = 4767997) B4767997
theorem B2974151 : Blo 1762082 2974151 := bstep (se 1 (by rfl) ⟨2230613, by rfl⟩ : syracuseStep 2974151 = 4461227) B4461227
theorem B3965417 : Blo 1762082 3965417 := bstep (se 2 (by rfl) ⟨1487031, by rfl⟩ : syracuseStep 3965417 = 2974063) B2974063
theorem B8045119 : Blo 1762082 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B3965705 : Blo 1762082 3965705 := bstep (se 2 (by rfl) ⟨1487139, by rfl⟩ : syracuseStep 3965705 = 2974279) B2974279
theorem B5948207 : Blo 1762082 5948207 := bstep (se 1 (by rfl) ⟨4461155, by rfl⟩ : syracuseStep 5948207 = 8922311) B8922311
theorem B1762159 : Blo 1762082 1762159 := bstep (se 1 (by rfl) ⟨1321619, by rfl⟩ : syracuseStep 1762159 = 2643239) B2643239
theorem B1983343 : Blo 1762082 1983343 := bstep (se 1 (by rfl) ⟨1487507, by rfl⟩ : syracuseStep 1983343 = 2975015) B2975015
theorem B29000591 : Blo 1762082 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B5948315 : Blo 1762082 5948315 := bstep (se 1 (by rfl) ⟨4461236, by rfl⟩ : syracuseStep 5948315 = 8922473) B8922473
theorem B48227237 : Blo 1762082 48227237 := bstep (se 4 (by rfl) ⟨4521303, by rfl⟩ : syracuseStep 48227237 = 9042607) B9042607
theorem B1762215 : Blo 1762082 1762215 := bstep (se 1 (by rfl) ⟨1321661, by rfl⟩ : syracuseStep 1762215 = 2643323) B2643323
theorem B12059603 : Blo 1762082 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B1762299 : Blo 1762082 1762299 := bstep (se 1 (by rfl) ⟨1321724, by rfl⟩ : syracuseStep 1762299 = 2643449) B2643449
theorem B1762367 : Blo 1762082 1762367 := bstep (se 1 (by rfl) ⟨1321775, by rfl⟩ : syracuseStep 1762367 = 2643551) B2643551
theorem B1762511 : Blo 1762082 1762511 := bstep (se 1 (by rfl) ⟨1321883, by rfl⟩ : syracuseStep 1762511 = 2643767) B2643767
theorem B2974927 : Blo 1762082 2974927 := bstep (se 1 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 2974927 = 4462391) B4462391
theorem B3966281 : Blo 1762082 3966281 := bstep (se 2 (by rfl) ⟨1487355, by rfl⟩ : syracuseStep 3966281 = 2974711) B2974711
theorem B1762715 : Blo 1762082 1762715 := bstep (se 1 (by rfl) ⟨1322036, by rfl⟩ : syracuseStep 1762715 = 2644073) B2644073
theorem B6030841 : Blo 1762082 6030841 := bstep (se 2 (by rfl) ⟨2261565, by rfl⟩ : syracuseStep 6030841 = 4523131) B4523131
theorem B9045523 : Blo 1762082 9045523 := bstep (se 1 (by rfl) ⟨6784142, by rfl⟩ : syracuseStep 9045523 = 13568285) B13568285
theorem B14296625 : Blo 1762082 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B1762927 : Blo 1762082 1762927 := bstep (se 1 (by rfl) ⟨1322195, by rfl⟩ : syracuseStep 1762927 = 2644391) B2644391
theorem B1762983 : Blo 1762082 1762983 := bstep (se 1 (by rfl) ⟨1322237, by rfl⟩ : syracuseStep 1762983 = 2644475) B2644475
theorem B1763067 : Blo 1762082 1763067 := bstep (se 1 (by rfl) ⟨1322300, by rfl⟩ : syracuseStep 1763067 = 2644601) B2644601
theorem B1763103 : Blo 1762082 1763103 := bstep (se 1 (by rfl) ⟨1322327, by rfl⟩ : syracuseStep 1763103 = 2644655) B2644655
theorem B1763135 : Blo 1762082 1763135 := bstep (se 1 (by rfl) ⟨1322351, by rfl⟩ : syracuseStep 1763135 = 2644703) B2644703
theorem B3221311 : Blo 1762082 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B20072285 : Blo 1762082 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B11298761 : Blo 1762082 11298761 := bstep (se 2 (by rfl) ⟨4237035, by rfl⟩ : syracuseStep 11298761 = 8474071) B8474071
theorem B1763311 : Blo 1762082 1763311 := bstep (se 1 (by rfl) ⟨1322483, by rfl⟩ : syracuseStep 1763311 = 2644967) B2644967
theorem B1984495 : Blo 1762082 1984495 := bstep (se 1 (by rfl) ⟨1488371, by rfl⟩ : syracuseStep 1984495 = 2976743) B2976743
theorem B2975737 : Blo 1762082 2975737 := bstep (se 2 (by rfl) ⟨1115901, by rfl⟩ : syracuseStep 2975737 = 2231803) B2231803
theorem B5949449 : Blo 1762082 5949449 := bstep (se 2 (by rfl) ⟨2231043, by rfl⟩ : syracuseStep 5949449 = 4462087) B4462087
theorem B8923283 : Blo 1762082 8923283 := bstep (se 1 (by rfl) ⟨6692462, by rfl⟩ : syracuseStep 8923283 = 13384925) B13384925
theorem B1763483 : Blo 1762082 1763483 := bstep (se 1 (by rfl) ⟨1322612, by rfl⟩ : syracuseStep 1763483 = 2645225) B2645225
theorem B2975899 : Blo 1762082 2975899 := bstep (se 1 (by rfl) ⟨2231924, by rfl⟩ : syracuseStep 2975899 = 4463849) B4463849
theorem B15059135 : Blo 1762082 15059135 := bstep (se 1 (by rfl) ⟨11294351, by rfl⟩ : syracuseStep 15059135 = 22588703) B22588703
theorem B1763519 : Blo 1762082 1763519 := bstep (se 1 (by rfl) ⟨1322639, by rfl⟩ : syracuseStep 1763519 = 2645279) B2645279
theorem B2230507 : Blo 1762082 2230507 := bstep (se 1 (by rfl) ⟨1672880, by rfl⟩ : syracuseStep 2230507 = 3345761) B3345761
theorem B2976007 : Blo 1762082 2976007 := bstep (se 1 (by rfl) ⟨2232005, by rfl⟩ : syracuseStep 2976007 = 4464011) B4464011
theorem B3967271 : Blo 1762082 3967271 := bstep (se 1 (by rfl) ⟨2975453, by rfl⟩ : syracuseStep 3967271 = 5950907) B5950907
theorem B2976041 : Blo 1762082 2976041 := bstep (se 2 (by rfl) ⟨1116015, by rfl⟩ : syracuseStep 2976041 = 2232031) B2232031
theorem B1763631 : Blo 1762082 1763631 := bstep (se 1 (by rfl) ⟨1322723, by rfl⟩ : syracuseStep 1763631 = 2645447) B2645447
theorem B3967289 : Blo 1762082 3967289 := bstep (se 2 (by rfl) ⟨1487733, by rfl⟩ : syracuseStep 3967289 = 2975467) B2975467
theorem B19056971 : Blo 1762082 19056971 := bstep (se 1 (by rfl) ⟨14292728, by rfl⟩ : syracuseStep 19056971 = 28585457) B28585457
theorem B34359677 : Blo 1762082 34359677 := bstep (se 3 (by rfl) ⟨6442439, by rfl⟩ : syracuseStep 34359677 = 12884879) B12884879
theorem B20367773 : Blo 1762082 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B1763867 : Blo 1762082 1763867 := bstep (se 1 (by rfl) ⟨1322900, by rfl⟩ : syracuseStep 1763867 = 2645801) B2645801
theorem B1763871 : Blo 1762082 1763871 := bstep (se 1 (by rfl) ⟨1322903, by rfl⟩ : syracuseStep 1763871 = 2645807) B2645807
theorem B2231479 : Blo 1762082 2231479 := bstep (se 1 (by rfl) ⟨1673609, by rfl⟩ : syracuseStep 2231479 = 3347219) B3347219
theorem B5950745 : Blo 1762082 5950745 := bstep (se 2 (by rfl) ⟨2231529, by rfl⟩ : syracuseStep 5950745 = 4463059) B4463059
theorem B5950799 : Blo 1762082 5950799 := bstep (se 1 (by rfl) ⟨4463099, by rfl⟩ : syracuseStep 5950799 = 8926199) B8926199
theorem B10178111 : Blo 1762082 10178111 := bstep (se 1 (by rfl) ⟨7633583, by rfl⟩ : syracuseStep 10178111 = 15267167) B15267167
theorem B3968585 : Blo 1762082 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B2510443 : Blo 1762082 2510443 := bstep (se 1 (by rfl) ⟨1882832, by rfl⟩ : syracuseStep 2510443 = 3765665) B3765665
theorem B28602065 : Blo 1762082 28602065 := bstep (se 2 (by rfl) ⟨10725774, by rfl⟩ : syracuseStep 28602065 = 21451549) B21451549
theorem B20082491 : Blo 1762082 20082491 := bstep (se 1 (by rfl) ⟨15061868, by rfl⟩ : syracuseStep 20082491 = 30123737) B30123737
theorem B2511337 : Blo 1762082 2511337 := bstep (se 2 (by rfl) ⟨941751, by rfl⟩ : syracuseStep 2511337 = 1883503) B1883503
theorem B33886745 : Blo 1762082 33886745 := bstep (se 2 (by rfl) ⟨12707529, by rfl⟩ : syracuseStep 33886745 = 25415059) B25415059
theorem B3764819 : Blo 1762082 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B5952095 : Blo 1762082 5952095 := bstep (se 1 (by rfl) ⟨4464071, by rfl⟩ : syracuseStep 5952095 = 8928143) B8928143
theorem B4649567 : Blo 1762082 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B4076135 : Blo 1762082 4076135 := bstep (se 1 (by rfl) ⟨3057101, by rfl⟩ : syracuseStep 4076135 = 6114203) B6114203
theorem B5649011 : Blo 1762082 5649011 := bstep (se 1 (by rfl) ⟨4236758, by rfl⟩ : syracuseStep 5649011 = 8473517) B8473517
theorem B13382495 : Blo 1762082 13382495 := bstep (se 1 (by rfl) ⟨10036871, by rfl⟩ : syracuseStep 13382495 = 20073743) B20073743
theorem B1189311331 : Blo 1762082 1189311331 := bstep (se 1 (by rfl) ⟨891983498, by rfl⟩ : syracuseStep 1189311331 = 1783966997) B1783966997
theorem B2823275 : Blo 1762082 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B4461743 : Blo 1762082 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B10040699 : Blo 1762082 10040699 := bstep (se 1 (by rfl) ⟨7530524, by rfl⟩ : syracuseStep 10040699 = 15061049) B15061049
theorem B2643527 : Blo 1762082 2643527 := bstep (se 1 (by rfl) ⟨1982645, by rfl⟩ : syracuseStep 2643527 = 3965291) B3965291
theorem B2643623 : Blo 1762082 2643623 := bstep (se 1 (by rfl) ⟨1982717, by rfl⟩ : syracuseStep 2643623 = 3965435) B3965435
theorem B139351745 : Blo 1762082 139351745 := bstep (se 2 (by rfl) ⟨52256904, by rfl⟩ : syracuseStep 139351745 = 104513809) B104513809
theorem B5019371 : Blo 1762082 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B21452525 : Blo 1762082 21452525 := bstep (se 3 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 21452525 = 8044697) B8044697
theorem B2643707 : Blo 1762082 2643707 := bstep (se 1 (by rfl) ⟨1982780, by rfl⟩ : syracuseStep 2643707 = 3965561) B3965561
theorem B2643743 : Blo 1762082 2643743 := bstep (se 1 (by rfl) ⟨1982807, by rfl⟩ : syracuseStep 2643743 = 3965615) B3965615
theorem B128726819 : Blo 1762082 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B5953337 : Blo 1762082 5953337 := bstep (se 2 (by rfl) ⟨2232501, by rfl⟩ : syracuseStep 5953337 = 4465003) B4465003
theorem B2643791 : Blo 1762082 2643791 := bstep (se 1 (by rfl) ⟨1982843, by rfl⟩ : syracuseStep 2643791 = 3965687) B3965687
theorem B1254029141 : Blo 1762082 1254029141 := bstep (se 9 (by rfl) ⟨3673913, by rfl⟩ : syracuseStep 1254029141 = 7347827) B7347827
theorem B8927171 : Blo 1762082 8927171 := bstep (se 1 (by rfl) ⟨6695378, by rfl⟩ : syracuseStep 8927171 = 13390757) B13390757
theorem B2643911 : Blo 1762082 2643911 := bstep (se 1 (by rfl) ⟨1982933, by rfl⟩ : syracuseStep 2643911 = 3965867) B3965867
theorem B5953499 : Blo 1762082 5953499 := bstep (se 1 (by rfl) ⟨4465124, by rfl⟩ : syracuseStep 5953499 = 8930249) B8930249
theorem B9664595 : Blo 1762082 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B4462735 : Blo 1762082 4462735 := bstep (se 1 (by rfl) ⟨3347051, by rfl⟩ : syracuseStep 4462735 = 6694103) B6694103
theorem B5019803 : Blo 1762082 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B5953769 : Blo 1762082 5953769 := bstep (se 2 (by rfl) ⟨2232663, by rfl⟩ : syracuseStep 5953769 = 4465327) B4465327
theorem B8476915 : Blo 1762082 8476915 := bstep (se 1 (by rfl) ⟨6357686, by rfl⟩ : syracuseStep 8476915 = 12715373) B12715373
theorem B8927495 : Blo 1762082 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B2644265 : Blo 1762082 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B2644271 : Blo 1762082 2644271 := bstep (se 1 (by rfl) ⟨1983203, by rfl⟩ : syracuseStep 2644271 = 3966407) B3966407
theorem B32602429 : Blo 1762082 32602429 := bstep (se 3 (by rfl) ⟨6112955, by rfl⟩ : syracuseStep 32602429 = 12225911) B12225911
theorem B3348859 : Blo 1762082 3348859 := bstep (se 1 (by rfl) ⟨2511644, by rfl⟩ : syracuseStep 3348859 = 5023289) B5023289
theorem B2644511 : Blo 1762082 2644511 := bstep (se 1 (by rfl) ⟨1983383, by rfl⟩ : syracuseStep 2644511 = 3966767) B3966767
theorem B4233865 : Blo 1762082 4233865 := bstep (se 2 (by rfl) ⟨1587699, by rfl⟩ : syracuseStep 4233865 = 3175399) B3175399
theorem B2644895 : Blo 1762082 2644895 := bstep (se 1 (by rfl) ⟨1983671, by rfl⟩ : syracuseStep 2644895 = 3967343) B3967343
theorem B13564837 : Blo 1762082 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B2644943 : Blo 1762082 2644943 := bstep (se 1 (by rfl) ⟨1983707, by rfl⟩ : syracuseStep 2644943 = 3967415) B3967415
theorem B2645033 : Blo 1762082 2645033 := bstep (se 2 (by rfl) ⟨991887, by rfl⟩ : syracuseStep 2645033 = 1983775) B1983775
theorem B4463657 : Blo 1762082 4463657 := bstep (se 2 (by rfl) ⟨1673871, by rfl⟩ : syracuseStep 4463657 = 3347743) B3347743
theorem B2645039 : Blo 1762082 2645039 := bstep (se 1 (by rfl) ⟨1983779, by rfl⟩ : syracuseStep 2645039 = 3967559) B3967559
theorem B2645063 : Blo 1762082 2645063 := bstep (se 1 (by rfl) ⟨1983797, by rfl⟩ : syracuseStep 2645063 = 3967595) B3967595
theorem B4463687 : Blo 1762082 4463687 := bstep (se 1 (by rfl) ⟨3347765, by rfl⟩ : syracuseStep 4463687 = 6695531) B6695531
theorem B2645327 : Blo 1762082 2645327 := bstep (se 1 (by rfl) ⟨1983995, by rfl⟩ : syracuseStep 2645327 = 3967991) B3967991
theorem B7527775 : Blo 1762082 7527775 := bstep (se 1 (by rfl) ⟨5645831, by rfl⟩ : syracuseStep 7527775 = 11291663) B11291663
theorem B7527791 : Blo 1762082 7527791 := bstep (se 1 (by rfl) ⟨5645843, by rfl⟩ : syracuseStep 7527791 = 11291687) B11291687
theorem B27139475 : Blo 1762082 27139475 := bstep (se 1 (by rfl) ⟨20354606, by rfl⟩ : syracuseStep 27139475 = 40709213) B40709213
theorem B2645417 : Blo 1762082 2645417 := bstep (se 2 (by rfl) ⟨992031, by rfl⟩ : syracuseStep 2645417 = 1984063) B1984063
theorem B67788251 : Blo 1762082 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B6692327 : Blo 1762082 6692327 := bstep (se 1 (by rfl) ⟨5019245, by rfl⟩ : syracuseStep 6692327 = 10038491) B10038491
theorem B20078117 : Blo 1762082 20078117 := bstep (se 4 (by rfl) ⟨1882323, by rfl⟩ : syracuseStep 20078117 = 3764647) B3764647
theorem B2645567 : Blo 1762082 2645567 := bstep (se 1 (by rfl) ⟨1984175, by rfl⟩ : syracuseStep 2645567 = 3968351) B3968351
theorem B22593167 : Blo 1762082 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B8928953 : Blo 1762082 8928953 := bstep (se 2 (by rfl) ⟨3348357, by rfl⟩ : syracuseStep 8928953 = 6696715) B6696715
theorem B5947127 : Blo 1762082 5947127 := bstep (se 1 (by rfl) ⟨4460345, by rfl⟩ : syracuseStep 5947127 = 8920691) B8920691
theorem B2645831 : Blo 1762082 2645831 := bstep (se 1 (by rfl) ⟨1984373, by rfl⟩ : syracuseStep 2645831 = 3968747) B3968747
theorem B2645915 : Blo 1762082 2645915 := bstep (se 1 (by rfl) ⟨1984436, by rfl⟩ : syracuseStep 2645915 = 3968873) B3968873
theorem B2973611 : Blo 1762082 2973611 := bstep (se 1 (by rfl) ⟨2230208, by rfl⟩ : syracuseStep 2973611 = 4460417) B4460417
theorem B7528733 : Blo 1762082 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B1982767 : Blo 1762082 1982767 := bstep (se 1 (by rfl) ⟨1487075, by rfl⟩ : syracuseStep 1982767 = 2974151) B2974151
theorem B2974009 : Blo 1762082 2974009 := bstep (se 2 (by rfl) ⟨1115253, by rfl⟩ : syracuseStep 2974009 = 2230507) B2230507
theorem B4465145 : Blo 1762082 4465145 := bstep (se 2 (by rfl) ⟨1674429, by rfl⟩ : syracuseStep 4465145 = 3348859) B3348859
theorem B3965471 : Blo 1762082 3965471 := bstep (se 1 (by rfl) ⟨2974103, by rfl⟩ : syracuseStep 3965471 = 5948207) B5948207
theorem B8921663 : Blo 1762082 8921663 := bstep (se 1 (by rfl) ⟨6691247, by rfl⟩ : syracuseStep 8921663 = 13382495) B13382495
theorem B19333727 : Blo 1762082 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B3965543 : Blo 1762082 3965543 := bstep (se 1 (by rfl) ⟨2974157, by rfl⟩ : syracuseStep 3965543 = 5948315) B5948315
theorem B2974495 : Blo 1762082 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B5645153 : Blo 1762082 5645153 := bstep (se 2 (by rfl) ⟨2116932, by rfl⟩ : syracuseStep 5645153 = 4233865) B4233865
theorem B6693799 : Blo 1762082 6693799 := bstep (se 1 (by rfl) ⟨5020349, by rfl⟩ : syracuseStep 6693799 = 10040699) B10040699
theorem B1762351 : Blo 1762082 1762351 := bstep (se 1 (by rfl) ⟨1321763, by rfl⟩ : syracuseStep 1762351 = 2643527) B2643527
theorem B1762415 : Blo 1762082 1762415 := bstep (se 1 (by rfl) ⟨1321811, by rfl⟩ : syracuseStep 1762415 = 2643623) B2643623
theorem B1762471 : Blo 1762082 1762471 := bstep (se 1 (by rfl) ⟨1321853, by rfl⟩ : syracuseStep 1762471 = 2643707) B2643707
theorem B1762495 : Blo 1762082 1762495 := bstep (se 1 (by rfl) ⟨1321871, by rfl⟩ : syracuseStep 1762495 = 2643743) B2643743
theorem B1762527 : Blo 1762082 1762527 := bstep (se 1 (by rfl) ⟨1321895, by rfl⟩ : syracuseStep 1762527 = 2643791) B2643791
theorem B1762607 : Blo 1762082 1762607 := bstep (se 1 (by rfl) ⟨1321955, by rfl⟩ : syracuseStep 1762607 = 2643911) B2643911
theorem B3966299 : Blo 1762082 3966299 := bstep (se 1 (by rfl) ⟨2974724, by rfl⟩ : syracuseStep 3966299 = 5949449) B5949449
theorem B5948855 : Blo 1762082 5948855 := bstep (se 1 (by rfl) ⟨4461641, by rfl⟩ : syracuseStep 5948855 = 8923283) B8923283
theorem B1762843 : Blo 1762082 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B1984027 : Blo 1762082 1984027 := bstep (se 1 (by rfl) ⟨1488020, by rfl⟩ : syracuseStep 1984027 = 2976041) B2976041
theorem B1762847 : Blo 1762082 1762847 := bstep (se 1 (by rfl) ⟨1322135, by rfl⟩ : syracuseStep 1762847 = 2644271) B2644271
theorem B2975305 : Blo 1762082 2975305 := bstep (se 2 (by rfl) ⟨1115739, by rfl⟩ : syracuseStep 2975305 = 2231479) B2231479
theorem B22906451 : Blo 1762082 22906451 := bstep (se 1 (by rfl) ⟨17179838, by rfl⟩ : syracuseStep 22906451 = 34359677) B34359677
theorem B3966569 : Blo 1762082 3966569 := bstep (se 2 (by rfl) ⟨1487463, by rfl⟩ : syracuseStep 3966569 = 2974927) B2974927
theorem B1763007 : Blo 1762082 1763007 := bstep (se 1 (by rfl) ⟨1322255, by rfl⟩ : syracuseStep 1763007 = 2644511) B2644511
theorem B10037033 : Blo 1762082 10037033 := bstep (se 2 (by rfl) ⟨3763887, by rfl⟩ : syracuseStep 10037033 = 7527775) B7527775
theorem B1763263 : Blo 1762082 1763263 := bstep (se 1 (by rfl) ⟨1322447, by rfl⟩ : syracuseStep 1763263 = 2644895) B2644895
theorem B1763295 : Blo 1762082 1763295 := bstep (se 1 (by rfl) ⟨1322471, by rfl⟩ : syracuseStep 1763295 = 2644943) B2644943
theorem B12060697 : Blo 1762082 12060697 := bstep (se 2 (by rfl) ⟨4522761, by rfl⟩ : syracuseStep 12060697 = 9045523) B9045523
theorem B1763355 : Blo 1762082 1763355 := bstep (se 1 (by rfl) ⟨1322516, by rfl⟩ : syracuseStep 1763355 = 2645033) B2645033
theorem B2975771 : Blo 1762082 2975771 := bstep (se 1 (by rfl) ⟨2231828, by rfl⟩ : syracuseStep 2975771 = 4463657) B4463657
theorem B1763359 : Blo 1762082 1763359 := bstep (se 1 (by rfl) ⟨1322519, by rfl⟩ : syracuseStep 1763359 = 2645039) B2645039
theorem B1763375 : Blo 1762082 1763375 := bstep (se 1 (by rfl) ⟨1322531, by rfl⟩ : syracuseStep 1763375 = 2645063) B2645063
theorem B2975791 : Blo 1762082 2975791 := bstep (se 1 (by rfl) ⟨2231843, by rfl⟩ : syracuseStep 2975791 = 4463687) B4463687
theorem B3967163 : Blo 1762082 3967163 := bstep (se 1 (by rfl) ⟨2975372, by rfl⟩ : syracuseStep 3967163 = 5950745) B5950745
theorem B3967199 : Blo 1762082 3967199 := bstep (se 1 (by rfl) ⟨2975399, by rfl⟩ : syracuseStep 3967199 = 5950799) B5950799
theorem B1763551 : Blo 1762082 1763551 := bstep (se 1 (by rfl) ⟨1322663, by rfl⟩ : syracuseStep 1763551 = 2645327) B2645327
theorem B1763611 : Blo 1762082 1763611 := bstep (se 1 (by rfl) ⟨1322708, by rfl⟩ : syracuseStep 1763611 = 2645417) B2645417
theorem B6785407 : Blo 1762082 6785407 := bstep (se 1 (by rfl) ⟨5089055, by rfl⟩ : syracuseStep 6785407 = 10178111) B10178111
theorem B1763711 : Blo 1762082 1763711 := bstep (se 1 (by rfl) ⟨1322783, by rfl⟩ : syracuseStep 1763711 = 2645567) B2645567
theorem B4295081 : Blo 1762082 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B13388327 : Blo 1762082 13388327 := bstep (se 1 (by rfl) ⟨10041245, by rfl⟩ : syracuseStep 13388327 = 20082491) B20082491
theorem B1763887 : Blo 1762082 1763887 := bstep (se 1 (by rfl) ⟨1322915, by rfl⟩ : syracuseStep 1763887 = 2645831) B2645831
theorem B1763943 : Blo 1762082 1763943 := bstep (se 1 (by rfl) ⟨1322957, by rfl⟩ : syracuseStep 1763943 = 2645915) B2645915
theorem B3967649 : Blo 1762082 3967649 := bstep (se 2 (by rfl) ⟨1487868, by rfl⟩ : syracuseStep 3967649 = 2975737) B2975737
theorem B5950313 : Blo 1762082 5950313 := bstep (se 2 (by rfl) ⟨2231367, by rfl⟩ : syracuseStep 5950313 = 4462735) B4462735
theorem B3967865 : Blo 1762082 3967865 := bstep (se 2 (by rfl) ⟨1487949, by rfl⟩ : syracuseStep 3967865 = 2975899) B2975899
theorem B4238219 : Blo 1762082 4238219 := bstep (se 1 (by rfl) ⟨3178664, by rfl⟩ : syracuseStep 4238219 = 6357329) B6357329
theorem B3968009 : Blo 1762082 3968009 := bstep (se 2 (by rfl) ⟨1488003, by rfl⟩ : syracuseStep 3968009 = 2976007) B2976007
theorem B2509879 : Blo 1762082 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B3968063 : Blo 1762082 3968063 := bstep (se 1 (by rfl) ⟨2976047, by rfl⟩ : syracuseStep 3968063 = 5952095) B5952095
theorem B43469905 : Blo 1762082 43469905 := bstep (se 2 (by rfl) ⟨16301214, by rfl⟩ : syracuseStep 43469905 = 32602429) B32602429
theorem B8039735 : Blo 1762082 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B10726825 : Blo 1762082 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B50818589 : Blo 1762082 50818589 := bstep (se 3 (by rfl) ⟨9528485, by rfl⟩ : syracuseStep 50818589 = 19056971) B19056971
theorem B9531083 : Blo 1762082 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B92901163 : Blo 1762082 92901163 := bstep (se 1 (by rfl) ⟨69675872, by rfl⟩ : syracuseStep 92901163 = 139351745) B139351745
theorem B3346247 : Blo 1762082 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B3968891 : Blo 1762082 3968891 := bstep (se 1 (by rfl) ⟨2976668, by rfl⟩ : syracuseStep 3968891 = 5953337) B5953337
theorem B13381523 : Blo 1762082 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B5951447 : Blo 1762082 5951447 := bstep (se 1 (by rfl) ⟨4463585, by rfl⟩ : syracuseStep 5951447 = 8927171) B8927171
theorem B7532507 : Blo 1762082 7532507 := bstep (se 1 (by rfl) ⟨5649380, by rfl⟩ : syracuseStep 7532507 = 11298761) B11298761
theorem B3968999 : Blo 1762082 3968999 := bstep (se 1 (by rfl) ⟨2976749, by rfl⟩ : syracuseStep 3968999 = 5953499) B5953499
theorem B6443063 : Blo 1762082 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B3346535 : Blo 1762082 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B10039423 : Blo 1762082 10039423 := bstep (se 1 (by rfl) ⟨7529567, by rfl⟩ : syracuseStep 10039423 = 15059135) B15059135
theorem B3969179 : Blo 1762082 3969179 := bstep (se 1 (by rfl) ⟨2976884, by rfl⟩ : syracuseStep 3969179 = 5953769) B5953769
theorem B5951663 : Blo 1762082 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B12398845 : Blo 1762082 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B13578515 : Blo 1762082 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B8041121 : Blo 1762082 8041121 := bstep (se 2 (by rfl) ⟨3015420, by rfl⟩ : syracuseStep 8041121 = 6030841) B6030841
theorem B3347257 : Blo 1762082 3347257 := bstep (se 2 (by rfl) ⟨1255221, by rfl⟩ : syracuseStep 3347257 = 2510443) B2510443
theorem B3344077709 : Blo 1762082 3344077709 := bstep (se 3 (by rfl) ⟨627014570, by rfl⟩ : syracuseStep 3344077709 = 1254029141) B1254029141
theorem B5018527 : Blo 1762082 5018527 := bstep (se 1 (by rfl) ⟨3763895, by rfl⟩ : syracuseStep 5018527 = 7527791) B7527791
theorem B18092983 : Blo 1762082 18092983 := bstep (se 1 (by rfl) ⟨13569737, by rfl⟩ : syracuseStep 18092983 = 27139475) B27139475
theorem B45192167 : Blo 1762082 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B4461551 : Blo 1762082 4461551 := bstep (se 1 (by rfl) ⟨3346163, by rfl⟩ : syracuseStep 4461551 = 6692327) B6692327
theorem B15062111 : Blo 1762082 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B5952635 : Blo 1762082 5952635 := bstep (se 1 (by rfl) ⟨4464476, by rfl⟩ : syracuseStep 5952635 = 8928953) B8928953
theorem B19068043 : Blo 1762082 19068043 := bstep (se 1 (by rfl) ⟨14301032, by rfl⟩ : syracuseStep 19068043 = 28602065) B28602065
theorem B33903967 : Blo 1762082 33903967 := bstep (se 1 (by rfl) ⟨25427975, by rfl⟩ : syracuseStep 33903967 = 50855951) B50855951
theorem B2643311 : Blo 1762082 2643311 := bstep (se 1 (by rfl) ⟨1982483, by rfl⟩ : syracuseStep 2643311 = 3964967) B3964967
theorem B5952905 : Blo 1762082 5952905 := bstep (se 2 (by rfl) ⟨2232339, by rfl⟩ : syracuseStep 5952905 = 4464679) B4464679
theorem B2643431 : Blo 1762082 2643431 := bstep (se 1 (by rfl) ⟨1982573, by rfl⟩ : syracuseStep 2643431 = 3965147) B3965147
theorem B2643593 : Blo 1762082 2643593 := bstep (se 2 (by rfl) ⟨991347, by rfl⟩ : syracuseStep 2643593 = 1982695) B1982695
theorem B11302553 : Blo 1762082 11302553 := bstep (se 2 (by rfl) ⟨4238457, by rfl⟩ : syracuseStep 11302553 = 8476915) B8476915
theorem B2643611 : Blo 1762082 2643611 := bstep (se 1 (by rfl) ⟨1982708, by rfl⟩ : syracuseStep 2643611 = 3965417) B3965417
theorem B22591163 : Blo 1762082 22591163 := bstep (se 1 (by rfl) ⟨16943372, by rfl⟩ : syracuseStep 22591163 = 33886745) B33886745
theorem B3766007 : Blo 1762082 3766007 := bstep (se 1 (by rfl) ⟨2824505, by rfl⟩ : syracuseStep 3766007 = 5649011) B5649011
theorem B2643803 : Blo 1762082 2643803 := bstep (se 1 (by rfl) ⟨1982852, by rfl⟩ : syracuseStep 2643803 = 3965705) B3965705
theorem B32151491 : Blo 1762082 32151491 := bstep (se 1 (by rfl) ⟨24113618, by rfl⟩ : syracuseStep 32151491 = 48227237) B48227237
theorem B3348449 : Blo 1762082 3348449 := bstep (se 2 (by rfl) ⟨1255668, by rfl⟩ : syracuseStep 3348449 = 2511337) B2511337
theorem B2644187 : Blo 1762082 2644187 := bstep (se 1 (by rfl) ⟨1983140, by rfl⟩ : syracuseStep 2644187 = 3966281) B3966281
theorem B1585748441 : Blo 1762082 1585748441 := bstep (se 2 (by rfl) ⟨594655665, by rfl⟩ : syracuseStep 1585748441 = 1189311331) B1189311331
theorem B2644457 : Blo 1762082 2644457 := bstep (se 2 (by rfl) ⟨991671, by rfl⟩ : syracuseStep 2644457 = 1983343) B1983343
theorem B14301683 : Blo 1762082 14301683 := bstep (se 1 (by rfl) ⟨10726262, by rfl⟩ : syracuseStep 14301683 = 21452525) B21452525
theorem B85817879 : Blo 1762082 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B18086449 : Blo 1762082 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B2644847 : Blo 1762082 2644847 := bstep (se 1 (by rfl) ⟨1983635, by rfl⟩ : syracuseStep 2644847 = 3967271) B3967271
theorem B2644859 : Blo 1762082 2644859 := bstep (se 1 (by rfl) ⟨1983644, by rfl⟩ : syracuseStep 2644859 = 3967289) B3967289
theorem B173915093 : Blo 1762082 173915093 := bstep (se 7 (by rfl) ⟨2038067, by rfl⟩ : syracuseStep 173915093 = 4076135) B4076135
theorem B13385411 : Blo 1762082 13385411 := bstep (se 1 (by rfl) ⟨10039058, by rfl⟩ : syracuseStep 13385411 = 20078117) B20078117
theorem B2645723 : Blo 1762082 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B3964751 : Blo 1762082 3964751 := bstep (se 1 (by rfl) ⟨2973563, by rfl⟩ : syracuseStep 3964751 = 5947127) B5947127
theorem B1982407 : Blo 1762082 1982407 := bstep (se 1 (by rfl) ⟨1486805, by rfl⟩ : syracuseStep 1982407 = 2973611) B2973611
theorem B2645993 : Blo 1762082 2645993 := bstep (se 2 (by rfl) ⟨992247, by rfl⟩ : syracuseStep 2645993 = 1984495) B1984495
theorem B16080929 : Blo 1762082 16080929 := bstep (se 2 (by rfl) ⟨6030348, by rfl⟩ : syracuseStep 16080929 = 12060697) B12060697
theorem B2646119 : Blo 1762082 2646119 := bstep (se 1 (by rfl) ⟨1984589, by rfl⟩ : syracuseStep 2646119 = 3969179) B3969179
theorem B13385897 : Blo 1762082 13385897 := bstep (se 2 (by rfl) ⟨5019711, by rfl⟩ : syracuseStep 13385897 = 10039423) B10039423
theorem B9052343 : Blo 1762082 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B16531793 : Blo 1762082 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B5947775 : Blo 1762082 5947775 := bstep (se 1 (by rfl) ⟨4460831, by rfl⟩ : syracuseStep 5947775 = 8921663) B8921663
theorem B3965345 : Blo 1762082 3965345 := bstep (se 2 (by rfl) ⟨1487004, by rfl⟩ : syracuseStep 3965345 = 2974009) B2974009
theorem B2974367 : Blo 1762082 2974367 := bstep (se 1 (by rfl) ⟨2230775, by rfl⟩ : syracuseStep 2974367 = 4461551) B4461551
theorem B1762207 : Blo 1762082 1762207 := bstep (se 1 (by rfl) ⟨1321655, by rfl⟩ : syracuseStep 1762207 = 2643311) B2643311
theorem B3965903 : Blo 1762082 3965903 := bstep (se 1 (by rfl) ⟨2974427, by rfl⟩ : syracuseStep 3965903 = 5948855) B5948855
theorem B1762287 : Blo 1762082 1762287 := bstep (se 1 (by rfl) ⟨1321715, by rfl⟩ : syracuseStep 1762287 = 2643431) B2643431
theorem B3965993 : Blo 1762082 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B15270967 : Blo 1762082 15270967 := bstep (se 1 (by rfl) ⟨11453225, by rfl⟩ : syracuseStep 15270967 = 22906451) B22906451
theorem B1762395 : Blo 1762082 1762395 := bstep (se 1 (by rfl) ⟨1321796, by rfl⟩ : syracuseStep 1762395 = 2643593) B2643593
theorem B1762407 : Blo 1762082 1762407 := bstep (se 1 (by rfl) ⟨1321805, by rfl⟩ : syracuseStep 1762407 = 2643611) B2643611
theorem B1762535 : Blo 1762082 1762535 := bstep (se 1 (by rfl) ⟨1321901, by rfl⟩ : syracuseStep 1762535 = 2643803) B2643803
theorem B1983847 : Blo 1762082 1983847 := bstep (se 1 (by rfl) ⟨1487885, by rfl⟩ : syracuseStep 1983847 = 2975771) B2975771
theorem B57959873 : Blo 1762082 57959873 := bstep (se 2 (by rfl) ⟨21734952, by rfl⟩ : syracuseStep 57959873 = 43469905) B43469905
theorem B1762791 : Blo 1762082 1762791 := bstep (se 1 (by rfl) ⟨1322093, by rfl⟩ : syracuseStep 1762791 = 2644187) B2644187
theorem B1762971 : Blo 1762082 1762971 := bstep (se 1 (by rfl) ⟨1322228, by rfl⟩ : syracuseStep 1762971 = 2644457) B2644457
theorem B45205289 : Blo 1762082 45205289 := bstep (se 2 (by rfl) ⟨16951983, by rfl⟩ : syracuseStep 45205289 = 33903967) B33903967
theorem B3966875 : Blo 1762082 3966875 := bstep (se 1 (by rfl) ⟨2975156, by rfl⟩ : syracuseStep 3966875 = 5950313) B5950313
theorem B1763231 : Blo 1762082 1763231 := bstep (se 1 (by rfl) ⟨1322423, by rfl⟩ : syracuseStep 1763231 = 2644847) B2644847
theorem B1763239 : Blo 1762082 1763239 := bstep (se 1 (by rfl) ⟨1322429, by rfl⟩ : syracuseStep 1763239 = 2644859) B2644859
theorem B115943395 : Blo 1762082 115943395 := bstep (se 1 (by rfl) ⟨86957546, by rfl⟩ : syracuseStep 115943395 = 173915093) B173915093
theorem B3967073 : Blo 1762082 3967073 := bstep (se 2 (by rfl) ⟨1487652, by rfl⟩ : syracuseStep 3967073 = 2975305) B2975305
theorem B5359823 : Blo 1762082 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B8923607 : Blo 1762082 8923607 := bstep (se 1 (by rfl) ⟨6692705, by rfl⟩ : syracuseStep 8923607 = 13385411) B13385411
theorem B1763815 : Blo 1762082 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B2230831 : Blo 1762082 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B3967631 : Blo 1762082 3967631 := bstep (se 1 (by rfl) ⟨2975723, by rfl⟩ : syracuseStep 3967631 = 5951447) B5951447
theorem B1763995 : Blo 1762082 1763995 := bstep (se 1 (by rfl) ⟨1322996, by rfl⟩ : syracuseStep 1763995 = 2645993) B2645993
theorem B4295375 : Blo 1762082 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B3967721 : Blo 1762082 3967721 := bstep (se 2 (by rfl) ⟨1487895, by rfl⟩ : syracuseStep 3967721 = 2975791) B2975791
theorem B3967775 : Blo 1762082 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B8924093 : Blo 1762082 8924093 := bstep (se 3 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 8924093 = 3346535) B3346535
theorem B2976763 : Blo 1762082 2976763 := bstep (se 1 (by rfl) ⟨2232572, by rfl⟩ : syracuseStep 2976763 = 4465145) B4465145
theorem B12889151 : Blo 1762082 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B5360747 : Blo 1762082 5360747 := bstep (se 1 (by rfl) ⟨4020560, by rfl⟩ : syracuseStep 5360747 = 8041121) B8041121
theorem B9047209 : Blo 1762082 9047209 := bstep (se 2 (by rfl) ⟨3392703, by rfl⟩ : syracuseStep 9047209 = 6785407) B6785407
theorem B3763435 : Blo 1762082 3763435 := bstep (se 1 (by rfl) ⟨2822576, by rfl⟩ : syracuseStep 3763435 = 5645153) B5645153
theorem B3968423 : Blo 1762082 3968423 := bstep (se 1 (by rfl) ⟨2976317, by rfl⟩ : syracuseStep 3968423 = 5952635) B5952635
theorem B3968603 : Blo 1762082 3968603 := bstep (se 1 (by rfl) ⟨2976452, by rfl⟩ : syracuseStep 3968603 = 5952905) B5952905
theorem B15060775 : Blo 1762082 15060775 := bstep (se 1 (by rfl) ⟨11295581, by rfl⟩ : syracuseStep 15060775 = 22591163) B22591163
theorem B2510671 : Blo 1762082 2510671 := bstep (se 1 (by rfl) ⟨1883003, by rfl⟩ : syracuseStep 2510671 = 3766007) B3766007
theorem B8925065 : Blo 1762082 8925065 := bstep (se 2 (by rfl) ⟨3346899, by rfl⟩ : syracuseStep 8925065 = 6693799) B6693799
theorem B21434327 : Blo 1762082 21434327 := bstep (se 1 (by rfl) ⟨16075745, by rfl⟩ : syracuseStep 21434327 = 32151491) B32151491
theorem B2232299 : Blo 1762082 2232299 := bstep (se 1 (by rfl) ⟨1674224, by rfl⟩ : syracuseStep 2232299 = 3348449) B3348449
theorem B3346505 : Blo 1762082 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B25424057 : Blo 1762082 25424057 := bstep (se 2 (by rfl) ⟨9534021, by rfl⟩ : syracuseStep 25424057 = 19068043) B19068043
theorem B2863387 : Blo 1762082 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B1057165627 : Blo 1762082 1057165627 := bstep (se 1 (by rfl) ⟨792874220, by rfl⟩ : syracuseStep 1057165627 = 1585748441) B1585748441
theorem B8925551 : Blo 1762082 8925551 := bstep (se 1 (by rfl) ⟨6694163, by rfl⟩ : syracuseStep 8925551 = 13388327) B13388327
theorem B33879059 : Blo 1762082 33879059 := bstep (se 1 (by rfl) ⟨25409294, by rfl⟩ : syracuseStep 33879059 = 50818589) B50818589
theorem B123868217 : Blo 1762082 123868217 := bstep (se 2 (by rfl) ⟨46450581, by rfl⟩ : syracuseStep 123868217 = 92901163) B92901163
theorem B6354055 : Blo 1762082 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B2643167 : Blo 1762082 2643167 := bstep (se 1 (by rfl) ⟨1982375, by rfl⟩ : syracuseStep 2643167 = 3964751) B3964751
theorem B2643209 : Blo 1762082 2643209 := bstep (se 2 (by rfl) ⟨991203, by rfl⟩ : syracuseStep 2643209 = 1982407) B1982407
theorem B5019155 : Blo 1762082 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B2643647 : Blo 1762082 2643647 := bstep (se 1 (by rfl) ⟨1982735, by rfl⟩ : syracuseStep 2643647 = 3965471) B3965471
theorem B2643689 : Blo 1762082 2643689 := bstep (se 2 (by rfl) ⟨991383, by rfl⟩ : syracuseStep 2643689 = 1982767) B1982767
theorem B2643695 : Blo 1762082 2643695 := bstep (se 1 (by rfl) ⟨1982771, by rfl⟩ : syracuseStep 2643695 = 3965543) B3965543
theorem B2229385139 : Blo 1762082 2229385139 := bstep (se 1 (by rfl) ⟨1672038854, by rfl⟩ : syracuseStep 2229385139 = 3344077709) B3344077709
theorem B30128111 : Blo 1762082 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B10041407 : Blo 1762082 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B24115265 : Blo 1762082 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B2644199 : Blo 1762082 2644199 := bstep (se 1 (by rfl) ⟨1983149, by rfl⟩ : syracuseStep 2644199 = 3966299) B3966299
theorem B2644379 : Blo 1762082 2644379 := bstep (se 1 (by rfl) ⟨1983284, by rfl⟩ : syracuseStep 2644379 = 3966569) B3966569
theorem B4463009 : Blo 1762082 4463009 := bstep (se 2 (by rfl) ⟨1673628, by rfl⟩ : syracuseStep 4463009 = 3347257) B3347257
theorem B7535035 : Blo 1762082 7535035 := bstep (se 1 (by rfl) ⟨5651276, by rfl⟩ : syracuseStep 7535035 = 11302553) B11302553
theorem B6691355 : Blo 1762082 6691355 := bstep (se 1 (by rfl) ⟨5018516, by rfl⟩ : syracuseStep 6691355 = 10037033) B10037033
theorem B6691369 : Blo 1762082 6691369 := bstep (se 2 (by rfl) ⟨2509263, by rfl⟩ : syracuseStep 6691369 = 5018527) B5018527
theorem B24123977 : Blo 1762082 24123977 := bstep (se 2 (by rfl) ⟨9046491, by rfl⟩ : syracuseStep 24123977 = 18092983) B18092983
theorem B2644775 : Blo 1762082 2644775 := bstep (se 1 (by rfl) ⟨1983581, by rfl⟩ : syracuseStep 2644775 = 3967163) B3967163
theorem B2644799 : Blo 1762082 2644799 := bstep (se 1 (by rfl) ⟨1983599, by rfl⟩ : syracuseStep 2644799 = 3967199) B3967199
theorem B9534455 : Blo 1762082 9534455 := bstep (se 1 (by rfl) ⟨7150841, by rfl⟩ : syracuseStep 9534455 = 14301683) B14301683
theorem B57211919 : Blo 1762082 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B2645099 : Blo 1762082 2645099 := bstep (se 1 (by rfl) ⟨1983824, by rfl⟩ : syracuseStep 2645099 = 3967649) B3967649
theorem B14302433 : Blo 1762082 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B2645243 : Blo 1762082 2645243 := bstep (se 1 (by rfl) ⟨1983932, by rfl⟩ : syracuseStep 2645243 = 3967865) B3967865
theorem B2825479 : Blo 1762082 2825479 := bstep (se 1 (by rfl) ⟨2119109, by rfl⟩ : syracuseStep 2825479 = 4238219) B4238219
theorem B2645339 : Blo 1762082 2645339 := bstep (se 1 (by rfl) ⟨1984004, by rfl⟩ : syracuseStep 2645339 = 3968009) B3968009
theorem B2645369 : Blo 1762082 2645369 := bstep (se 2 (by rfl) ⟨992013, by rfl⟩ : syracuseStep 2645369 = 1984027) B1984027
theorem B2645375 : Blo 1762082 2645375 := bstep (se 1 (by rfl) ⟨1984031, by rfl⟩ : syracuseStep 2645375 = 3968063) B3968063
theorem B2645927 : Blo 1762082 2645927 := bstep (se 1 (by rfl) ⟨1984445, by rfl⟩ : syracuseStep 2645927 = 3968891) B3968891
theorem B8921015 : Blo 1762082 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B5021671 : Blo 1762082 5021671 := bstep (se 1 (by rfl) ⟨3766253, by rfl⟩ : syracuseStep 5021671 = 7532507) B7532507
theorem B2645999 : Blo 1762082 2645999 := bstep (se 1 (by rfl) ⟨1984499, by rfl⟩ : syracuseStep 2645999 = 3968999) B3968999
theorem B16949371 : Blo 1762082 16949371 := bstep (se 1 (by rfl) ⟨12712028, by rfl⟩ : syracuseStep 16949371 = 25424057) B25424057
theorem B3965183 : Blo 1762082 3965183 := bstep (se 1 (by rfl) ⟨2973887, by rfl⟩ : syracuseStep 3965183 = 5947775) B5947775
theorem B3817849 : Blo 1762082 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B1982911 : Blo 1762082 1982911 := bstep (se 1 (by rfl) ⟨1487183, by rfl⟩ : syracuseStep 1982911 = 2974367) B2974367
theorem B22586039 : Blo 1762082 22586039 := bstep (se 1 (by rfl) ⟨16939529, by rfl⟩ : syracuseStep 22586039 = 33879059) B33879059
theorem B8921825 : Blo 1762082 8921825 := bstep (se 2 (by rfl) ⟨3345684, by rfl⟩ : syracuseStep 8921825 = 6691369) B6691369
theorem B2974441 : Blo 1762082 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B1762111 : Blo 1762082 1762111 := bstep (se 1 (by rfl) ⟨1321583, by rfl⟩ : syracuseStep 1762111 = 2643167) B2643167
theorem B1762139 : Blo 1762082 1762139 := bstep (se 1 (by rfl) ⟨1321604, by rfl⟩ : syracuseStep 1762139 = 2643209) B2643209
theorem B57181301 : Blo 1762082 57181301 := bstep (se 5 (by rfl) ⟨2680373, by rfl⟩ : syracuseStep 57181301 = 5360747) B5360747
theorem B1762431 : Blo 1762082 1762431 := bstep (se 1 (by rfl) ⟨1321823, by rfl⟩ : syracuseStep 1762431 = 2643647) B2643647
theorem B1762459 : Blo 1762082 1762459 := bstep (se 1 (by rfl) ⟨1321844, by rfl⟩ : syracuseStep 1762459 = 2643689) B2643689
theorem B1762463 : Blo 1762082 1762463 := bstep (se 1 (by rfl) ⟨1321847, by rfl⟩ : syracuseStep 1762463 = 2643695) B2643695
theorem B6694271 : Blo 1762082 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B3573215 : Blo 1762082 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1762799 : Blo 1762082 1762799 := bstep (se 1 (by rfl) ⟨1322099, by rfl⟩ : syracuseStep 1762799 = 2644199) B2644199
theorem B8472073 : Blo 1762082 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B1762919 : Blo 1762082 1762919 := bstep (se 1 (by rfl) ⟨1322189, by rfl⟩ : syracuseStep 1762919 = 2644379) B2644379
theorem B2975339 : Blo 1762082 2975339 := bstep (se 1 (by rfl) ⟨2231504, by rfl⟩ : syracuseStep 2975339 = 4463009) B4463009
theorem B5949071 : Blo 1762082 5949071 := bstep (se 1 (by rfl) ⟨4461803, by rfl⟩ : syracuseStep 5949071 = 8923607) B8923607
theorem B16082651 : Blo 1762082 16082651 := bstep (se 1 (by rfl) ⟨12061988, by rfl⟩ : syracuseStep 16082651 = 24123977) B24123977
theorem B1763183 : Blo 1762082 1763183 := bstep (se 1 (by rfl) ⟨1322387, by rfl⟩ : syracuseStep 1763183 = 2644775) B2644775
theorem B1763199 : Blo 1762082 1763199 := bstep (se 1 (by rfl) ⟨1322399, by rfl⟩ : syracuseStep 1763199 = 2644799) B2644799
theorem B5949395 : Blo 1762082 5949395 := bstep (se 1 (by rfl) ⟨4462046, by rfl⟩ : syracuseStep 5949395 = 8924093) B8924093
theorem B1763399 : Blo 1762082 1763399 := bstep (se 1 (by rfl) ⟨1322549, by rfl⟩ : syracuseStep 1763399 = 2645099) B2645099
theorem B1763495 : Blo 1762082 1763495 := bstep (se 1 (by rfl) ⟨1322621, by rfl⟩ : syracuseStep 1763495 = 2645243) B2645243
theorem B1763559 : Blo 1762082 1763559 := bstep (se 1 (by rfl) ⟨1322669, by rfl⟩ : syracuseStep 1763559 = 2645339) B2645339
theorem B1763579 : Blo 1762082 1763579 := bstep (se 1 (by rfl) ⟨1322684, by rfl⟩ : syracuseStep 1763579 = 2645369) B2645369
theorem B1763583 : Blo 1762082 1763583 := bstep (se 1 (by rfl) ⟨1322687, by rfl⟩ : syracuseStep 1763583 = 2645375) B2645375
theorem B20081033 : Blo 1762082 20081033 := bstep (se 2 (by rfl) ⟨7530387, by rfl⟩ : syracuseStep 20081033 = 15060775) B15060775
theorem B5950043 : Blo 1762082 5950043 := bstep (se 1 (by rfl) ⟨4462532, by rfl⟩ : syracuseStep 5950043 = 8925065) B8925065
theorem B1763951 : Blo 1762082 1763951 := bstep (se 1 (by rfl) ⟨1322963, by rfl⟩ : syracuseStep 1763951 = 2645927) B2645927
theorem B6695561 : Blo 1762082 6695561 := bstep (se 2 (by rfl) ⟨2510835, by rfl⟩ : syracuseStep 6695561 = 5021671) B5021671
theorem B14289551 : Blo 1762082 14289551 := bstep (se 1 (by rfl) ⟨10717163, by rfl⟩ : syracuseStep 14289551 = 21434327) B21434327
theorem B1763999 : Blo 1762082 1763999 := bstep (se 1 (by rfl) ⟨1322999, by rfl⟩ : syracuseStep 1763999 = 2645999) B2645999
theorem B2231003 : Blo 1762082 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B1764079 : Blo 1762082 1764079 := bstep (se 1 (by rfl) ⟨1323059, by rfl⟩ : syracuseStep 1764079 = 2646119) B2646119
theorem B8923931 : Blo 1762082 8923931 := bstep (se 1 (by rfl) ⟨6692948, by rfl⟩ : syracuseStep 8923931 = 13385897) B13385897
theorem B11021195 : Blo 1762082 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B5950367 : Blo 1762082 5950367 := bstep (se 1 (by rfl) ⟨4462775, by rfl⟩ : syracuseStep 5950367 = 8925551) B8925551
theorem B10046713 : Blo 1762082 10046713 := bstep (se 2 (by rfl) ⟨3767517, by rfl⟩ : syracuseStep 10046713 = 7535035) B7535035
theorem B82578811 : Blo 1762082 82578811 := bstep (se 1 (by rfl) ⟨61934108, by rfl⟩ : syracuseStep 82578811 = 123868217) B123868217
theorem B3346103 : Blo 1762082 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B3969017 : Blo 1762082 3969017 := bstep (se 2 (by rfl) ⟨1488381, by rfl⟩ : syracuseStep 3969017 = 2976763) B2976763
theorem B16076843 : Blo 1762082 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B20361289 : Blo 1762082 20361289 := bstep (se 2 (by rfl) ⟨7635483, by rfl⟩ : syracuseStep 20361289 = 15270967) B15270967
theorem B12062945 : Blo 1762082 12062945 := bstep (se 2 (by rfl) ⟨4523604, by rfl⟩ : syracuseStep 12062945 = 9047209) B9047209
theorem B5017913 : Blo 1762082 5017913 := bstep (se 2 (by rfl) ⟨1881717, by rfl⟩ : syracuseStep 5017913 = 3763435) B3763435
theorem B4460903 : Blo 1762082 4460903 := bstep (se 1 (by rfl) ⟨3345677, by rfl⟩ : syracuseStep 4460903 = 6691355) B6691355
theorem B2863583 : Blo 1762082 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B3347561 : Blo 1762082 3347561 := bstep (se 2 (by rfl) ⟨1255335, by rfl⟩ : syracuseStep 3347561 = 2510671) B2510671
theorem B5952797 : Blo 1762082 5952797 := bstep (se 3 (by rfl) ⟨1116149, by rfl⟩ : syracuseStep 5952797 = 2232299) B2232299
theorem B10720619 : Blo 1762082 10720619 := bstep (se 1 (by rfl) ⟨8040464, by rfl⟩ : syracuseStep 10720619 = 16080929) B16080929
theorem B6034895 : Blo 1762082 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B2643563 : Blo 1762082 2643563 := bstep (se 1 (by rfl) ⟨1982672, by rfl⟩ : syracuseStep 2643563 = 3965345) B3965345
theorem B1409554169 : Blo 1762082 1409554169 := bstep (se 2 (by rfl) ⟨528582813, by rfl⟩ : syracuseStep 1409554169 = 1057165627) B1057165627
theorem B2643935 : Blo 1762082 2643935 := bstep (se 1 (by rfl) ⟨1982951, by rfl⟩ : syracuseStep 2643935 = 3965903) B3965903
theorem B2643995 : Blo 1762082 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B38639915 : Blo 1762082 38639915 := bstep (se 1 (by rfl) ⟨28979936, by rfl⟩ : syracuseStep 38639915 = 57959873) B57959873
theorem B30136859 : Blo 1762082 30136859 := bstep (se 1 (by rfl) ⟨22602644, by rfl⟩ : syracuseStep 30136859 = 45205289) B45205289
theorem B2644583 : Blo 1762082 2644583 := bstep (se 1 (by rfl) ⟨1983437, by rfl⟩ : syracuseStep 2644583 = 3966875) B3966875
theorem B1486256759 : Blo 1762082 1486256759 := bstep (se 1 (by rfl) ⟨1114692569, by rfl⟩ : syracuseStep 1486256759 = 2229385139) B2229385139
theorem B20085407 : Blo 1762082 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B2644715 : Blo 1762082 2644715 := bstep (se 1 (by rfl) ⟨1983536, by rfl⟩ : syracuseStep 2644715 = 3967073) B3967073
theorem B3767305 : Blo 1762082 3767305 := bstep (se 2 (by rfl) ⟨1412739, by rfl⟩ : syracuseStep 3767305 = 2825479) B2825479
theorem B2645087 : Blo 1762082 2645087 := bstep (se 1 (by rfl) ⟨1983815, by rfl⟩ : syracuseStep 2645087 = 3967631) B3967631
theorem B2645129 : Blo 1762082 2645129 := bstep (se 2 (by rfl) ⟨991923, by rfl⟩ : syracuseStep 2645129 = 1983847) B1983847
theorem B2645147 : Blo 1762082 2645147 := bstep (se 1 (by rfl) ⟨1983860, by rfl⟩ : syracuseStep 2645147 = 3967721) B3967721
theorem B2645183 : Blo 1762082 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B6356303 : Blo 1762082 6356303 := bstep (se 1 (by rfl) ⟨4767227, by rfl⟩ : syracuseStep 6356303 = 9534455) B9534455
theorem B38141279 : Blo 1762082 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B8592767 : Blo 1762082 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B9534955 : Blo 1762082 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B2645615 : Blo 1762082 2645615 := bstep (se 1 (by rfl) ⟨1984211, by rfl⟩ : syracuseStep 2645615 = 3968423) B3968423
theorem B2645735 : Blo 1762082 2645735 := bstep (se 1 (by rfl) ⟨1984301, by rfl⟩ : syracuseStep 2645735 = 3968603) B3968603
theorem B5947343 : Blo 1762082 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B154591193 : Blo 1762082 154591193 := bstep (se 2 (by rfl) ⟨57971697, by rfl⟩ : syracuseStep 154591193 = 115943395) B115943395
theorem B27148385 : Blo 1762082 27148385 := bstep (se 2 (by rfl) ⟨10180644, by rfl⟩ : syracuseStep 27148385 = 20361289) B20361289
theorem B2973935 : Blo 1762082 2973935 := bstep (se 1 (by rfl) ⟨2230451, by rfl⟩ : syracuseStep 2973935 = 4460903) B4460903
theorem B1909055 : Blo 1762082 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B15057359 : Blo 1762082 15057359 := bstep (se 1 (by rfl) ⟨11293019, by rfl⟩ : syracuseStep 15057359 = 22586039) B22586039
theorem B5947883 : Blo 1762082 5947883 := bstep (se 1 (by rfl) ⟨4460912, by rfl⟩ : syracuseStep 5947883 = 8921825) B8921825
theorem B4023263 : Blo 1762082 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B3965921 : Blo 1762082 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B1762375 : Blo 1762082 1762375 := bstep (se 1 (by rfl) ⟨1321781, by rfl⟩ : syracuseStep 1762375 = 2643563) B2643563
theorem B1983559 : Blo 1762082 1983559 := bstep (se 1 (by rfl) ⟨1487669, by rfl⟩ : syracuseStep 1983559 = 2975339) B2975339
theorem B3966047 : Blo 1762082 3966047 := bstep (se 1 (by rfl) ⟨2974535, by rfl⟩ : syracuseStep 3966047 = 5949071) B5949071
theorem B3966263 : Blo 1762082 3966263 := bstep (se 1 (by rfl) ⟨2974697, by rfl⟩ : syracuseStep 3966263 = 5949395) B5949395
theorem B1762623 : Blo 1762082 1762623 := bstep (se 1 (by rfl) ⟨1321967, by rfl⟩ : syracuseStep 1762623 = 2643935) B2643935
theorem B5023073 : Blo 1762082 5023073 := bstep (se 2 (by rfl) ⟨1883652, by rfl⟩ : syracuseStep 5023073 = 3767305) B3767305
theorem B1762663 : Blo 1762082 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B13387355 : Blo 1762082 13387355 := bstep (se 1 (by rfl) ⟨10040516, by rfl⟩ : syracuseStep 13387355 = 20081033) B20081033
theorem B13395617 : Blo 1762082 13395617 := bstep (se 2 (by rfl) ⟨5023356, by rfl⟩ : syracuseStep 13395617 = 10046713) B10046713
theorem B3966695 : Blo 1762082 3966695 := bstep (se 1 (by rfl) ⟨2975021, by rfl⟩ : syracuseStep 3966695 = 5950043) B5950043
theorem B1763055 : Blo 1762082 1763055 := bstep (se 1 (by rfl) ⟨1322291, by rfl⟩ : syracuseStep 1763055 = 2644583) B2644583
theorem B1763143 : Blo 1762082 1763143 := bstep (se 1 (by rfl) ⟨1322357, by rfl⟩ : syracuseStep 1763143 = 2644715) B2644715
theorem B5949287 : Blo 1762082 5949287 := bstep (se 1 (by rfl) ⟨4461965, by rfl⟩ : syracuseStep 5949287 = 8923931) B8923931
theorem B5949341 : Blo 1762082 5949341 := bstep (se 3 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 5949341 = 2231003) B2231003
theorem B3966911 : Blo 1762082 3966911 := bstep (se 1 (by rfl) ⟨2975183, by rfl⟩ : syracuseStep 3966911 = 5950367) B5950367
theorem B1763391 : Blo 1762082 1763391 := bstep (se 1 (by rfl) ⟨1322543, by rfl⟩ : syracuseStep 1763391 = 2645087) B2645087
theorem B1763419 : Blo 1762082 1763419 := bstep (se 1 (by rfl) ⟨1322564, by rfl⟩ : syracuseStep 1763419 = 2645129) B2645129
theorem B1763431 : Blo 1762082 1763431 := bstep (se 1 (by rfl) ⟨1322573, by rfl⟩ : syracuseStep 1763431 = 2645147) B2645147
theorem B1763455 : Blo 1762082 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B4237535 : Blo 1762082 4237535 := bstep (se 1 (by rfl) ⟨3178151, by rfl⟩ : syracuseStep 4237535 = 6356303) B6356303
theorem B5728511 : Blo 1762082 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B1763743 : Blo 1762082 1763743 := bstep (se 1 (by rfl) ⟨1322807, by rfl⟩ : syracuseStep 1763743 = 2645615) B2645615
theorem B2230735 : Blo 1762082 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B1763823 : Blo 1762082 1763823 := bstep (se 1 (by rfl) ⟨1322867, by rfl⟩ : syracuseStep 1763823 = 2645735) B2645735
theorem B10717895 : Blo 1762082 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B3345275 : Blo 1762082 3345275 := bstep (se 1 (by rfl) ⟨2508956, by rfl⟩ : syracuseStep 3345275 = 5017913) B5017913
theorem B5090465 : Blo 1762082 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B2231707 : Blo 1762082 2231707 := bstep (se 1 (by rfl) ⟨1673780, by rfl⟩ : syracuseStep 2231707 = 3347561) B3347561
theorem B38120867 : Blo 1762082 38120867 := bstep (se 1 (by rfl) ⟨28590650, by rfl⟩ : syracuseStep 38120867 = 57181301) B57181301
theorem B3968531 : Blo 1762082 3968531 := bstep (se 1 (by rfl) ⟨2976398, by rfl⟩ : syracuseStep 3968531 = 5952797) B5952797
theorem B7147079 : Blo 1762082 7147079 := bstep (se 1 (by rfl) ⟨5360309, by rfl⟩ : syracuseStep 7147079 = 10720619) B10720619
theorem B25759943 : Blo 1762082 25759943 := bstep (se 1 (by rfl) ⟨19319957, by rfl⟩ : syracuseStep 25759943 = 38639915) B38639915
theorem B20091239 : Blo 1762082 20091239 := bstep (se 1 (by rfl) ⟨15068429, by rfl⟩ : syracuseStep 20091239 = 30136859) B30136859
theorem B13390271 : Blo 1762082 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B110105081 : Blo 1762082 110105081 := bstep (se 2 (by rfl) ⟨41289405, by rfl⟩ : syracuseStep 110105081 = 82578811) B82578811
theorem B29389853 : Blo 1762082 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B412243181 : Blo 1762082 412243181 := bstep (se 3 (by rfl) ⟨77295596, by rfl⟩ : syracuseStep 412243181 = 154591193) B154591193
theorem B8041963 : Blo 1762082 8041963 := bstep (se 1 (by rfl) ⟨6031472, by rfl⟩ : syracuseStep 8041963 = 12062945) B12062945
theorem B22599161 : Blo 1762082 22599161 := bstep (se 2 (by rfl) ⟨8474685, by rfl⟩ : syracuseStep 22599161 = 16949371) B16949371
theorem B2643455 : Blo 1762082 2643455 := bstep (se 1 (by rfl) ⟨1982591, by rfl⟩ : syracuseStep 2643455 = 3965183) B3965183
theorem B2643881 : Blo 1762082 2643881 := bstep (se 2 (by rfl) ⟨991455, by rfl⟩ : syracuseStep 2643881 = 1982911) B1982911
theorem B4462847 : Blo 1762082 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B2382143 : Blo 1762082 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B10721767 : Blo 1762082 10721767 := bstep (se 1 (by rfl) ⟨8041325, by rfl⟩ : syracuseStep 10721767 = 16082651) B16082651
theorem B939702779 : Blo 1762082 939702779 := bstep (se 1 (by rfl) ⟨704777084, by rfl⟩ : syracuseStep 939702779 = 1409554169) B1409554169
theorem B990837839 : Blo 1762082 990837839 := bstep (se 1 (by rfl) ⟨743128379, by rfl⟩ : syracuseStep 990837839 = 1486256759) B1486256759
theorem B4463707 : Blo 1762082 4463707 := bstep (se 1 (by rfl) ⟨3347780, by rfl⟩ : syracuseStep 4463707 = 6695561) B6695561
theorem B9526367 : Blo 1762082 9526367 := bstep (se 1 (by rfl) ⟨7144775, by rfl⟩ : syracuseStep 9526367 = 14289551) B14289551
theorem B12713273 : Blo 1762082 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B11296097 : Blo 1762082 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B25427519 : Blo 1762082 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B3964895 : Blo 1762082 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B2646011 : Blo 1762082 2646011 := bstep (se 1 (by rfl) ⟨1984508, by rfl⟩ : syracuseStep 2646011 = 3969017) B3969017
theorem B1982623 : Blo 1762082 1982623 := bstep (se 1 (by rfl) ⟨1486967, by rfl⟩ : syracuseStep 1982623 = 2973935) B2973935
theorem B13394159 : Blo 1762082 13394159 := bstep (se 1 (by rfl) ⟨10045619, by rfl⟩ : syracuseStep 13394159 = 20091239) B20091239
theorem B25403645 : Blo 1762082 25403645 := bstep (se 3 (by rfl) ⟨4763183, by rfl⟩ : syracuseStep 25403645 = 9526367) B9526367
theorem B3965255 : Blo 1762082 3965255 := bstep (se 1 (by rfl) ⟨2973941, by rfl⟩ : syracuseStep 3965255 = 5947883) B5947883
theorem B13574573 : Blo 1762082 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B2974313 : Blo 1762082 2974313 := bstep (se 2 (by rfl) ⟨1115367, by rfl⟩ : syracuseStep 2974313 = 2230735) B2230735
theorem B14295689 : Blo 1762082 14295689 := bstep (se 2 (by rfl) ⟨5360883, by rfl⟩ : syracuseStep 14295689 = 10721767) B10721767
theorem B15066107 : Blo 1762082 15066107 := bstep (se 1 (by rfl) ⟨11299580, by rfl⟩ : syracuseStep 15066107 = 22599161) B22599161
theorem B1762303 : Blo 1762082 1762303 := bstep (se 1 (by rfl) ⟨1321727, by rfl⟩ : syracuseStep 1762303 = 2643455) B2643455
theorem B8930411 : Blo 1762082 8930411 := bstep (se 1 (by rfl) ⟨6697808, by rfl⟩ : syracuseStep 8930411 = 13395617) B13395617
theorem B3966191 : Blo 1762082 3966191 := bstep (se 1 (by rfl) ⟨2974643, by rfl⟩ : syracuseStep 3966191 = 5949287) B5949287
theorem B3966227 : Blo 1762082 3966227 := bstep (se 1 (by rfl) ⟨2974670, by rfl⟩ : syracuseStep 3966227 = 5949341) B5949341
theorem B1762587 : Blo 1762082 1762587 := bstep (se 1 (by rfl) ⟨1321940, by rfl⟩ : syracuseStep 1762587 = 2643881) B2643881
theorem B2975231 : Blo 1762082 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B3819007 : Blo 1762082 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B626468519 : Blo 1762082 626468519 := bstep (se 1 (by rfl) ⟨469851389, by rfl⟩ : syracuseStep 626468519 = 939702779) B939702779
theorem B7145263 : Blo 1762082 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B2975609 : Blo 1762082 2975609 := bstep (se 2 (by rfl) ⟨1115853, by rfl⟩ : syracuseStep 2975609 = 2231707) B2231707
theorem B2230183 : Blo 1762082 2230183 := bstep (se 1 (by rfl) ⟨1672637, by rfl⟩ : syracuseStep 2230183 = 3345275) B3345275
theorem B7530731 : Blo 1762082 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B25413911 : Blo 1762082 25413911 := bstep (se 1 (by rfl) ⟨19060433, by rfl⟩ : syracuseStep 25413911 = 38120867) B38120867
theorem B16951679 : Blo 1762082 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B1764007 : Blo 1762082 1764007 := bstep (se 1 (by rfl) ⟨1323005, by rfl⟩ : syracuseStep 1764007 = 2646011) B2646011
theorem B17173295 : Blo 1762082 17173295 := bstep (se 1 (by rfl) ⟨12879971, by rfl⟩ : syracuseStep 17173295 = 25759943) B25759943
theorem B72395693 : Blo 1762082 72395693 := bstep (se 3 (by rfl) ⟨13574192, by rfl⟩ : syracuseStep 72395693 = 27148385) B27148385
theorem B10038239 : Blo 1762082 10038239 := bstep (se 1 (by rfl) ⟨7528679, by rfl⟩ : syracuseStep 10038239 = 15057359) B15057359
theorem B73403387 : Blo 1762082 73403387 := bstep (se 1 (by rfl) ⟨55052540, by rfl⟩ : syracuseStep 73403387 = 110105081) B110105081
theorem B11300093 : Blo 1762082 11300093 := bstep (se 3 (by rfl) ⟨2118767, by rfl⟩ : syracuseStep 11300093 = 4237535) B4237535
theorem B2682175 : Blo 1762082 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B274828787 : Blo 1762082 274828787 := bstep (se 1 (by rfl) ⟨206121590, by rfl⟩ : syracuseStep 274828787 = 412243181) B412243181
theorem B6352381 : Blo 1762082 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B5090813 : Blo 1762082 5090813 := bstep (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) B1909055
theorem B8924903 : Blo 1762082 8924903 := bstep (se 1 (by rfl) ⟨6693677, by rfl⟩ : syracuseStep 8924903 = 13387355) B13387355
theorem B5951609 : Blo 1762082 5951609 := bstep (se 2 (by rfl) ⟨2231853, by rfl⟩ : syracuseStep 5951609 = 4463707) B4463707
theorem B660558559 : Blo 1762082 660558559 := bstep (se 1 (by rfl) ⟨495418919, by rfl⟩ : syracuseStep 660558559 = 990837839) B990837839
theorem B8475515 : Blo 1762082 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B4764719 : Blo 1762082 4764719 := bstep (se 1 (by rfl) ⟨3573539, by rfl⟩ : syracuseStep 4764719 = 7147079) B7147079
theorem B2643263 : Blo 1762082 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B8926847 : Blo 1762082 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B2643947 : Blo 1762082 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B19593235 : Blo 1762082 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B2644031 : Blo 1762082 2644031 := bstep (se 1 (by rfl) ⟨1983023, by rfl⟩ : syracuseStep 2644031 = 3966047) B3966047
theorem B2644175 : Blo 1762082 2644175 := bstep (se 1 (by rfl) ⟨1983131, by rfl⟩ : syracuseStep 2644175 = 3966263) B3966263
theorem B3348715 : Blo 1762082 3348715 := bstep (se 1 (by rfl) ⟨2511536, by rfl⟩ : syracuseStep 3348715 = 5023073) B5023073
theorem B2644463 : Blo 1762082 2644463 := bstep (se 1 (by rfl) ⟨1983347, by rfl⟩ : syracuseStep 2644463 = 3966695) B3966695
theorem B2644607 : Blo 1762082 2644607 := bstep (se 1 (by rfl) ⟨1983455, by rfl⟩ : syracuseStep 2644607 = 3966911) B3966911
theorem B2644745 : Blo 1762082 2644745 := bstep (se 2 (by rfl) ⟨991779, by rfl⟩ : syracuseStep 2644745 = 1983559) B1983559
theorem B10722617 : Blo 1762082 10722617 := bstep (se 2 (by rfl) ⟨4020981, by rfl⟩ : syracuseStep 10722617 = 8041963) B8041963
theorem B2645687 : Blo 1762082 2645687 := bstep (se 1 (by rfl) ⟨1984265, by rfl⟩ : syracuseStep 2645687 = 3968531) B3968531
theorem B104497253 : Blo 1762082 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B8929439 : Blo 1762082 8929439 := bstep (se 1 (by rfl) ⟨6697079, by rfl⟩ : syracuseStep 8929439 = 13394159) B13394159
theorem B4464953 : Blo 1762082 4464953 := bstep (se 2 (by rfl) ⟨1674357, by rfl⟩ : syracuseStep 4464953 = 3348715) B3348715
theorem B1982875 : Blo 1762082 1982875 := bstep (se 1 (by rfl) ⟨1487156, by rfl⟩ : syracuseStep 1982875 = 2974313) B2974313
theorem B10044071 : Blo 1762082 10044071 := bstep (se 1 (by rfl) ⟨7533053, by rfl⟩ : syracuseStep 10044071 = 15066107) B15066107
theorem B1762175 : Blo 1762082 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1983487 : Blo 1762082 1983487 := bstep (se 1 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 1983487 = 2975231) B2975231
theorem B417645679 : Blo 1762082 417645679 := bstep (se 1 (by rfl) ⟨313234259, by rfl⟩ : syracuseStep 417645679 = 626468519) B626468519
theorem B1983739 : Blo 1762082 1983739 := bstep (se 1 (by rfl) ⟨1487804, by rfl⟩ : syracuseStep 1983739 = 2975609) B2975609
theorem B1762631 : Blo 1762082 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B1762687 : Blo 1762082 1762687 := bstep (se 1 (by rfl) ⟨1322015, by rfl⟩ : syracuseStep 1762687 = 2644031) B2644031
theorem B1762783 : Blo 1762082 1762783 := bstep (se 1 (by rfl) ⟨1322087, by rfl⟩ : syracuseStep 1762783 = 2644175) B2644175
theorem B16942607 : Blo 1762082 16942607 := bstep (se 1 (by rfl) ⟨12706955, by rfl⟩ : syracuseStep 16942607 = 25413911) B25413911
theorem B1762975 : Blo 1762082 1762975 := bstep (se 1 (by rfl) ⟨1322231, by rfl⟩ : syracuseStep 1762975 = 2644463) B2644463
theorem B1763071 : Blo 1762082 1763071 := bstep (se 1 (by rfl) ⟨1322303, by rfl⟩ : syracuseStep 1763071 = 2644607) B2644607
theorem B1763163 : Blo 1762082 1763163 := bstep (se 1 (by rfl) ⟨1322372, by rfl⟩ : syracuseStep 1763163 = 2644745) B2644745
theorem B3393875 : Blo 1762082 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B1763791 : Blo 1762082 1763791 := bstep (se 1 (by rfl) ⟨1322843, by rfl⟩ : syracuseStep 1763791 = 2645687) B2645687
theorem B5949935 : Blo 1762082 5949935 := bstep (se 1 (by rfl) ⟨4462451, by rfl⟩ : syracuseStep 5949935 = 8924903) B8924903
theorem B20368037 : Blo 1762082 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B3967739 : Blo 1762082 3967739 := bstep (se 1 (by rfl) ⟨2975804, by rfl⟩ : syracuseStep 3967739 = 5951609) B5951609
theorem B16935763 : Blo 1762082 16935763 := bstep (se 1 (by rfl) ⟨12701822, by rfl⟩ : syracuseStep 16935763 = 25403645) B25403645
theorem B9530459 : Blo 1762082 9530459 := bstep (se 1 (by rfl) ⟨7147844, by rfl⟩ : syracuseStep 9530459 = 14295689) B14295689
theorem B5951231 : Blo 1762082 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B11301119 : Blo 1762082 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B3576233 : Blo 1762082 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B11448863 : Blo 1762082 11448863 := bstep (se 1 (by rfl) ⟨8586647, by rfl⟩ : syracuseStep 11448863 = 17173295) B17173295
theorem B48263795 : Blo 1762082 48263795 := bstep (se 1 (by rfl) ⟨36197846, by rfl⟩ : syracuseStep 48263795 = 72395693) B72395693
theorem B48935591 : Blo 1762082 48935591 := bstep (se 1 (by rfl) ⟨36701693, by rfl⟩ : syracuseStep 48935591 = 73403387) B73403387
theorem B7533395 : Blo 1762082 7533395 := bstep (se 1 (by rfl) ⟨5650046, by rfl⟩ : syracuseStep 7533395 = 11300093) B11300093
theorem B7148411 : Blo 1762082 7148411 := bstep (se 1 (by rfl) ⟨5361308, by rfl⟩ : syracuseStep 7148411 = 10722617) B10722617
theorem B183219191 : Blo 1762082 183219191 := bstep (se 1 (by rfl) ⟨137414393, by rfl⟩ : syracuseStep 183219191 = 274828787) B274828787
theorem B2643497 : Blo 1762082 2643497 := bstep (se 2 (by rfl) ⟨991311, by rfl⟩ : syracuseStep 2643497 = 1982623) B1982623
theorem B2643503 : Blo 1762082 2643503 := bstep (se 1 (by rfl) ⟨1982627, by rfl⟩ : syracuseStep 2643503 = 3965255) B3965255
theorem B9049715 : Blo 1762082 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B5650343 : Blo 1762082 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B3176479 : Blo 1762082 3176479 := bstep (se 1 (by rfl) ⟨2382359, by rfl⟩ : syracuseStep 3176479 = 4764719) B4764719
theorem B5953607 : Blo 1762082 5953607 := bstep (se 1 (by rfl) ⟨4465205, by rfl⟩ : syracuseStep 5953607 = 8930411) B8930411
theorem B2644127 : Blo 1762082 2644127 := bstep (se 1 (by rfl) ⟨1983095, by rfl⟩ : syracuseStep 2644127 = 3966191) B3966191
theorem B2644151 : Blo 1762082 2644151 := bstep (se 1 (by rfl) ⟨1983113, by rfl⟩ : syracuseStep 2644151 = 3966227) B3966227
theorem B880744745 : Blo 1762082 880744745 := bstep (se 2 (by rfl) ⟨330279279, by rfl⟩ : syracuseStep 880744745 = 660558559) B660558559
theorem B5020487 : Blo 1762082 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B6692159 : Blo 1762082 6692159 := bstep (se 1 (by rfl) ⟨5019119, by rfl⟩ : syracuseStep 6692159 = 10038239) B10038239
theorem B8469841 : Blo 1762082 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B9527017 : Blo 1762082 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B2973577 : Blo 1762082 2973577 := bstep (se 2 (by rfl) ⟨1115091, by rfl⟩ : syracuseStep 2973577 = 2230183) B2230183
theorem B69664835 : Blo 1762082 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B16941221 : Blo 1762082 16941221 := bstep (se 4 (by rfl) ⟨1588239, by rfl⟩ : syracuseStep 16941221 = 3176479) B3176479
theorem B2384155 : Blo 1762082 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B5022263 : Blo 1762082 5022263 := bstep (se 1 (by rfl) ⟨3766697, by rfl⟩ : syracuseStep 5022263 = 7533395) B7533395
theorem B1762331 : Blo 1762082 1762331 := bstep (se 1 (by rfl) ⟨1321748, by rfl⟩ : syracuseStep 1762331 = 2643497) B2643497
theorem B1762335 : Blo 1762082 1762335 := bstep (se 1 (by rfl) ⟨1321751, by rfl⟩ : syracuseStep 1762335 = 2643503) B2643503
theorem B1762751 : Blo 1762082 1762751 := bstep (se 1 (by rfl) ⟨1322063, by rfl⟩ : syracuseStep 1762751 = 2644127) B2644127
theorem B1762767 : Blo 1762082 1762767 := bstep (se 1 (by rfl) ⟨1322075, by rfl⟩ : syracuseStep 1762767 = 2644151) B2644151
theorem B556860905 : Blo 1762082 556860905 := bstep (se 2 (by rfl) ⟨208822839, by rfl⟩ : syracuseStep 556860905 = 417645679) B417645679
theorem B587163163 : Blo 1762082 587163163 := bstep (se 1 (by rfl) ⟨440372372, by rfl⟩ : syracuseStep 587163163 = 880744745) B880744745
theorem B2262583 : Blo 1762082 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B3966623 : Blo 1762082 3966623 := bstep (se 1 (by rfl) ⟨2974967, by rfl⟩ : syracuseStep 3966623 = 5949935) B5949935
theorem B3967487 : Blo 1762082 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B2976635 : Blo 1762082 2976635 := bstep (se 1 (by rfl) ⟨2232476, by rfl⟩ : syracuseStep 2976635 = 4464953) B4464953
theorem B6696047 : Blo 1762082 6696047 := bstep (se 1 (by rfl) ⟨5022035, by rfl⟩ : syracuseStep 6696047 = 10044071) B10044071
theorem B32623727 : Blo 1762082 32623727 := bstep (se 1 (by rfl) ⟨24467795, by rfl⟩ : syracuseStep 32623727 = 48935591) B48935591
theorem B122146127 : Blo 1762082 122146127 := bstep (se 1 (by rfl) ⟨91609595, by rfl⟩ : syracuseStep 122146127 = 183219191) B183219191
theorem B6033143 : Blo 1762082 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B22581017 : Blo 1762082 22581017 := bstep (se 2 (by rfl) ⟨8467881, by rfl⟩ : syracuseStep 22581017 = 16935763) B16935763
theorem B3969071 : Blo 1762082 3969071 := bstep (se 1 (by rfl) ⟨2976803, by rfl⟩ : syracuseStep 3969071 = 5953607) B5953607
theorem B11293121 : Blo 1762082 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B13578691 : Blo 1762082 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B3346991 : Blo 1762082 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B6353639 : Blo 1762082 6353639 := bstep (se 1 (by rfl) ⟨4765229, by rfl⟩ : syracuseStep 6353639 = 9530459) B9530459
theorem B4461439 : Blo 1762082 4461439 := bstep (se 1 (by rfl) ⟨3346079, by rfl⟩ : syracuseStep 4461439 = 6692159) B6692159
theorem B12702689 : Blo 1762082 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B5952959 : Blo 1762082 5952959 := bstep (se 1 (by rfl) ⟨4464719, by rfl⟩ : syracuseStep 5952959 = 8929439) B8929439
theorem B7534079 : Blo 1762082 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B7632575 : Blo 1762082 7632575 := bstep (se 1 (by rfl) ⟨5724431, by rfl⟩ : syracuseStep 7632575 = 11448863) B11448863
theorem B32175863 : Blo 1762082 32175863 := bstep (se 1 (by rfl) ⟨24131897, by rfl⟩ : syracuseStep 32175863 = 48263795) B48263795
theorem B2643833 : Blo 1762082 2643833 := bstep (se 2 (by rfl) ⟨991437, by rfl⟩ : syracuseStep 2643833 = 1982875) B1982875
theorem B4765607 : Blo 1762082 4765607 := bstep (se 1 (by rfl) ⟨3574205, by rfl⟩ : syracuseStep 4765607 = 7148411) B7148411
theorem B11295071 : Blo 1762082 11295071 := bstep (se 1 (by rfl) ⟨8471303, by rfl⟩ : syracuseStep 11295071 = 16942607) B16942607
theorem B3766895 : Blo 1762082 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B2644649 : Blo 1762082 2644649 := bstep (se 2 (by rfl) ⟨991743, by rfl⟩ : syracuseStep 2644649 = 1983487) B1983487
theorem B2644985 : Blo 1762082 2644985 := bstep (se 2 (by rfl) ⟨991869, by rfl⟩ : syracuseStep 2644985 = 1983739) B1983739
theorem B2645159 : Blo 1762082 2645159 := bstep (se 1 (by rfl) ⟨1983869, by rfl⟩ : syracuseStep 2645159 = 3967739) B3967739
theorem B3964769 : Blo 1762082 3964769 := bstep (se 2 (by rfl) ⟨1486788, by rfl⟩ : syracuseStep 3964769 = 2973577) B2973577
theorem B2646047 : Blo 1762082 2646047 := bstep (se 1 (by rfl) ⟨1984535, by rfl⟩ : syracuseStep 2646047 = 3969071) B3969071
theorem B3178873 : Blo 1762082 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B4235759 : Blo 1762082 4235759 := bstep (se 1 (by rfl) ⟨3176819, by rfl⟩ : syracuseStep 4235759 = 6353639) B6353639
theorem B18104921 : Blo 1762082 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B5022719 : Blo 1762082 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B5088383 : Blo 1762082 5088383 := bstep (se 1 (by rfl) ⟨3816287, by rfl⟩ : syracuseStep 5088383 = 7632575) B7632575
theorem B5948585 : Blo 1762082 5948585 := bstep (se 2 (by rfl) ⟨2230719, by rfl⟩ : syracuseStep 5948585 = 4461439) B4461439
theorem B30114989 : Blo 1762082 30114989 := bstep (se 3 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 30114989 = 11293121) B11293121
theorem B1762555 : Blo 1762082 1762555 := bstep (se 1 (by rfl) ⟨1321916, by rfl⟩ : syracuseStep 1762555 = 2643833) B2643833
theorem B7530047 : Blo 1762082 7530047 := bstep (se 1 (by rfl) ⟨5647535, by rfl⟩ : syracuseStep 7530047 = 11295071) B11295071
theorem B1763099 : Blo 1762082 1763099 := bstep (se 1 (by rfl) ⟨1322324, by rfl⟩ : syracuseStep 1763099 = 2644649) B2644649
theorem B1984423 : Blo 1762082 1984423 := bstep (se 1 (by rfl) ⟨1488317, by rfl⟩ : syracuseStep 1984423 = 2976635) B2976635
theorem B1763323 : Blo 1762082 1763323 := bstep (se 1 (by rfl) ⟨1322492, by rfl⟩ : syracuseStep 1763323 = 2644985) B2644985
theorem B3016777 : Blo 1762082 3016777 := bstep (se 2 (by rfl) ⟨1131291, by rfl⟩ : syracuseStep 3016777 = 2262583) B2262583
theorem B1763439 : Blo 1762082 1763439 := bstep (se 1 (by rfl) ⟨1322579, by rfl⟩ : syracuseStep 1763439 = 2645159) B2645159
theorem B81430751 : Blo 1762082 81430751 := bstep (se 1 (by rfl) ⟨61073063, by rfl⟩ : syracuseStep 81430751 = 122146127) B122146127
theorem B46443223 : Blo 1762082 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B2231327 : Blo 1762082 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B3968639 : Blo 1762082 3968639 := bstep (se 1 (by rfl) ⟨2976479, by rfl⟩ : syracuseStep 3968639 = 5952959) B5952959
theorem B371240603 : Blo 1762082 371240603 := bstep (se 1 (by rfl) ⟨278430452, by rfl⟩ : syracuseStep 371240603 = 556860905) B556860905
theorem B21450575 : Blo 1762082 21450575 := bstep (se 1 (by rfl) ⟨16087931, by rfl⟩ : syracuseStep 21450575 = 32175863) B32175863
theorem B2511263 : Blo 1762082 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B15054011 : Blo 1762082 15054011 := bstep (se 1 (by rfl) ⟨11290508, by rfl⟩ : syracuseStep 15054011 = 22581017) B22581017
theorem B2643179 : Blo 1762082 2643179 := bstep (se 1 (by rfl) ⟨1982384, by rfl⟩ : syracuseStep 2643179 = 3964769) B3964769
theorem B11294147 : Blo 1762082 11294147 := bstep (se 1 (by rfl) ⟨8470610, by rfl⟩ : syracuseStep 11294147 = 16941221) B16941221
theorem B86996605 : Blo 1762082 86996605 := bstep (se 3 (by rfl) ⟨16311863, by rfl⟩ : syracuseStep 86996605 = 32623727) B32623727
theorem B8468459 : Blo 1762082 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B2644415 : Blo 1762082 2644415 := bstep (se 1 (by rfl) ⟨1983311, by rfl⟩ : syracuseStep 2644415 = 3966623) B3966623
theorem B3177071 : Blo 1762082 3177071 := bstep (se 1 (by rfl) ⟨2382803, by rfl⟩ : syracuseStep 3177071 = 4765607) B4765607
theorem B13392701 : Blo 1762082 13392701 := bstep (se 3 (by rfl) ⟨2511131, by rfl⟩ : syracuseStep 13392701 = 5022263) B5022263
theorem B2644991 : Blo 1762082 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B782884217 : Blo 1762082 782884217 := bstep (se 2 (by rfl) ⟨293581581, by rfl⟩ : syracuseStep 782884217 = 587163163) B587163163
theorem B4464031 : Blo 1762082 4464031 := bstep (se 1 (by rfl) ⟨3348023, by rfl⟩ : syracuseStep 4464031 = 6696047) B6696047
theorem B4022095 : Blo 1762082 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B4022369 : Blo 1762082 4022369 := bstep (se 2 (by rfl) ⟨1508388, by rfl⟩ : syracuseStep 4022369 = 3016777) B3016777
theorem B3392255 : Blo 1762082 3392255 := bstep (se 1 (by rfl) ⟨2544191, by rfl⟩ : syracuseStep 3392255 = 5088383) B5088383
theorem B3965723 : Blo 1762082 3965723 := bstep (se 1 (by rfl) ⟨2974292, by rfl⟩ : syracuseStep 3965723 = 5948585) B5948585
theorem B10036007 : Blo 1762082 10036007 := bstep (se 1 (by rfl) ⟨7527005, by rfl⟩ : syracuseStep 10036007 = 15054011) B15054011
theorem B1762119 : Blo 1762082 1762119 := bstep (se 1 (by rfl) ⟨1321589, by rfl⟩ : syracuseStep 1762119 = 2643179) B2643179
theorem B61924297 : Blo 1762082 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B7529431 : Blo 1762082 7529431 := bstep (se 1 (by rfl) ⟨5647073, by rfl⟩ : syracuseStep 7529431 = 11294147) B11294147
theorem B5645639 : Blo 1762082 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B1762943 : Blo 1762082 1762943 := bstep (se 1 (by rfl) ⟨1322207, by rfl⟩ : syracuseStep 1762943 = 2644415) B2644415
theorem B1763327 : Blo 1762082 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B521922811 : Blo 1762082 521922811 := bstep (se 1 (by rfl) ⟨391442108, by rfl⟩ : syracuseStep 521922811 = 782884217) B782884217
theorem B1764031 : Blo 1762082 1764031 := bstep (se 1 (by rfl) ⟨1323023, by rfl⟩ : syracuseStep 1764031 = 2646047) B2646047
theorem B5950205 : Blo 1762082 5950205 := bstep (se 3 (by rfl) ⟨1115663, by rfl⟩ : syracuseStep 5950205 = 2231327) B2231327
theorem B12069947 : Blo 1762082 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B4238497 : Blo 1762082 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B6696701 : Blo 1762082 6696701 := bstep (se 3 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 6696701 = 2511263) B2511263
theorem B2118047 : Blo 1762082 2118047 := bstep (se 1 (by rfl) ⟨1588535, by rfl⟩ : syracuseStep 2118047 = 3177071) B3177071
theorem B5952041 : Blo 1762082 5952041 := bstep (se 2 (by rfl) ⟨2232015, by rfl⟩ : syracuseStep 5952041 = 4464031) B4464031
theorem B115995473 : Blo 1762082 115995473 := bstep (se 2 (by rfl) ⟨43498302, by rfl⟩ : syracuseStep 115995473 = 86996605) B86996605
theorem B247493735 : Blo 1762082 247493735 := bstep (se 1 (by rfl) ⟨185620301, by rfl⟩ : syracuseStep 247493735 = 371240603) B371240603
theorem B5362793 : Blo 1762082 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B14300383 : Blo 1762082 14300383 := bstep (se 1 (by rfl) ⟨10725287, by rfl⟩ : syracuseStep 14300383 = 21450575) B21450575
theorem B2823839 : Blo 1762082 2823839 := bstep (se 1 (by rfl) ⟨2117879, by rfl⟩ : syracuseStep 2823839 = 4235759) B4235759
theorem B3348479 : Blo 1762082 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B20076659 : Blo 1762082 20076659 := bstep (se 1 (by rfl) ⟨15057494, by rfl⟩ : syracuseStep 20076659 = 30114989) B30114989
theorem B5020031 : Blo 1762082 5020031 := bstep (se 1 (by rfl) ⟨3765023, by rfl⟩ : syracuseStep 5020031 = 7530047) B7530047
theorem B54287167 : Blo 1762082 54287167 := bstep (se 1 (by rfl) ⟨40715375, by rfl⟩ : syracuseStep 54287167 = 81430751) B81430751
theorem B8928467 : Blo 1762082 8928467 := bstep (se 1 (by rfl) ⟨6696350, by rfl⟩ : syracuseStep 8928467 = 13392701) B13392701
theorem B2645759 : Blo 1762082 2645759 := bstep (se 1 (by rfl) ⟨1984319, by rfl⟩ : syracuseStep 2645759 = 3968639) B3968639
theorem B2645897 : Blo 1762082 2645897 := bstep (se 2 (by rfl) ⟨992211, by rfl⟩ : syracuseStep 2645897 = 1984423) B1984423
theorem B8929277 : Blo 1762082 8929277 := bstep (se 3 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 8929277 = 3348479) B3348479
theorem B164995823 : Blo 1762082 164995823 := bstep (se 1 (by rfl) ⟨123746867, by rfl⟩ : syracuseStep 164995823 = 247493735) B247493735
theorem B3966803 : Blo 1762082 3966803 := bstep (se 1 (by rfl) ⟨2975102, by rfl⟩ : syracuseStep 3966803 = 5950205) B5950205
theorem B9046013 : Blo 1762082 9046013 := bstep (se 3 (by rfl) ⟨1696127, by rfl⟩ : syracuseStep 9046013 = 3392255) B3392255
theorem B8046631 : Blo 1762082 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B1763839 : Blo 1762082 1763839 := bstep (se 1 (by rfl) ⟨1322879, by rfl⟩ : syracuseStep 1763839 = 2645759) B2645759
theorem B1763931 : Blo 1762082 1763931 := bstep (se 1 (by rfl) ⟨1322948, by rfl⟩ : syracuseStep 1763931 = 2645897) B2645897
theorem B2681579 : Blo 1762082 2681579 := bstep (se 1 (by rfl) ⟨2011184, by rfl⟩ : syracuseStep 2681579 = 4022369) B4022369
theorem B695897081 : Blo 1762082 695897081 := bstep (se 2 (by rfl) ⟨260961405, by rfl⟩ : syracuseStep 695897081 = 521922811) B521922811
theorem B3968027 : Blo 1762082 3968027 := bstep (se 1 (by rfl) ⟨2976020, by rfl⟩ : syracuseStep 3968027 = 5952041) B5952041
theorem B3575195 : Blo 1762082 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B3763759 : Blo 1762082 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B5648125 : Blo 1762082 5648125 := bstep (se 3 (by rfl) ⟨1059023, by rfl⟩ : syracuseStep 5648125 = 2118047) B2118047
theorem B10039241 : Blo 1762082 10039241 := bstep (se 2 (by rfl) ⟨3764715, by rfl⟩ : syracuseStep 10039241 = 7529431) B7529431
theorem B3346687 : Blo 1762082 3346687 := bstep (se 1 (by rfl) ⟨2510015, by rfl⟩ : syracuseStep 3346687 = 5020031) B5020031
theorem B19067177 : Blo 1762082 19067177 := bstep (se 2 (by rfl) ⟨7150191, by rfl⟩ : syracuseStep 19067177 = 14300383) B14300383
theorem B5952311 : Blo 1762082 5952311 := bstep (se 1 (by rfl) ⟨4464233, by rfl⟩ : syracuseStep 5952311 = 8928467) B8928467
theorem B2643815 : Blo 1762082 2643815 := bstep (se 1 (by rfl) ⟨1982861, by rfl⟩ : syracuseStep 2643815 = 3965723) B3965723
theorem B6690671 : Blo 1762082 6690671 := bstep (se 1 (by rfl) ⟨5018003, by rfl⟩ : syracuseStep 6690671 = 10036007) B10036007
theorem B77330315 : Blo 1762082 77330315 := bstep (se 1 (by rfl) ⟨57997736, by rfl⟩ : syracuseStep 77330315 = 115995473) B115995473
theorem B72382889 : Blo 1762082 72382889 := bstep (se 2 (by rfl) ⟨27143583, by rfl⟩ : syracuseStep 72382889 = 54287167) B54287167
theorem B1882559 : Blo 1762082 1882559 := bstep (se 1 (by rfl) ⟨1411919, by rfl⟩ : syracuseStep 1882559 = 2823839) B2823839
theorem B82565729 : Blo 1762082 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B13384439 : Blo 1762082 13384439 := bstep (se 1 (by rfl) ⟨10038329, by rfl⟩ : syracuseStep 13384439 = 20076659) B20076659
theorem B5651329 : Blo 1762082 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B4464467 : Blo 1762082 4464467 := bstep (se 1 (by rfl) ⟨3348350, by rfl⟩ : syracuseStep 4464467 = 6696701) B6696701
theorem B1762543 : Blo 1762082 1762543 := bstep (se 1 (by rfl) ⟨1321907, by rfl⟩ : syracuseStep 1762543 = 2643815) B2643815
theorem B51553543 : Blo 1762082 51553543 := bstep (se 1 (by rfl) ⟨38665157, by rfl⟩ : syracuseStep 51553543 = 77330315) B77330315
theorem B55043819 : Blo 1762082 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B1787719 : Blo 1762082 1787719 := bstep (se 1 (by rfl) ⟨1340789, by rfl⟩ : syracuseStep 1787719 = 2681579) B2681579
theorem B8922959 : Blo 1762082 8922959 := bstep (se 1 (by rfl) ⟨6692219, by rfl⟩ : syracuseStep 8922959 = 13384439) B13384439
theorem B463931387 : Blo 1762082 463931387 := bstep (se 1 (by rfl) ⟨347948540, by rfl⟩ : syracuseStep 463931387 = 695897081) B695897081
theorem B7530833 : Blo 1762082 7530833 := bstep (se 2 (by rfl) ⟨2824062, by rfl⟩ : syracuseStep 7530833 = 5648125) B5648125
theorem B2976311 : Blo 1762082 2976311 := bstep (se 1 (by rfl) ⟨2232233, by rfl⟩ : syracuseStep 2976311 = 4464467) B4464467
theorem B3968207 : Blo 1762082 3968207 := bstep (se 1 (by rfl) ⟨2976155, by rfl⟩ : syracuseStep 3968207 = 5952311) B5952311
theorem B4460447 : Blo 1762082 4460447 := bstep (se 1 (by rfl) ⟨3345335, by rfl⟩ : syracuseStep 4460447 = 6690671) B6690671
theorem B48255259 : Blo 1762082 48255259 := bstep (se 1 (by rfl) ⟨36191444, by rfl⟩ : syracuseStep 48255259 = 72382889) B72382889
theorem B439988861 : Blo 1762082 439988861 := bstep (se 3 (by rfl) ⟨82497911, by rfl⟩ : syracuseStep 439988861 = 164995823) B164995823
theorem B5018345 : Blo 1762082 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B24122701 : Blo 1762082 24122701 := bstep (se 3 (by rfl) ⟨4523006, by rfl⟩ : syracuseStep 24122701 = 9046013) B9046013
theorem B5952851 : Blo 1762082 5952851 := bstep (se 1 (by rfl) ⟨4464638, by rfl⟩ : syracuseStep 5952851 = 8929277) B8929277
theorem B42915365 : Blo 1762082 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B4462249 : Blo 1762082 4462249 := bstep (se 2 (by rfl) ⟨1673343, by rfl⟩ : syracuseStep 4462249 = 3346687) B3346687
theorem B50845805 : Blo 1762082 50845805 := bstep (se 3 (by rfl) ⟨9533588, by rfl⟩ : syracuseStep 50845805 = 19067177) B19067177
theorem B5020157 : Blo 1762082 5020157 := bstep (se 3 (by rfl) ⟨941279, by rfl⟩ : syracuseStep 5020157 = 1882559) B1882559
theorem B7535105 : Blo 1762082 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B2644535 : Blo 1762082 2644535 := bstep (se 1 (by rfl) ⟨1983401, by rfl⟩ : syracuseStep 2644535 = 3966803) B3966803
theorem B2645351 : Blo 1762082 2645351 := bstep (se 1 (by rfl) ⟨1984013, by rfl⟩ : syracuseStep 2645351 = 3968027) B3968027
theorem B2383463 : Blo 1762082 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B6692827 : Blo 1762082 6692827 := bstep (se 1 (by rfl) ⟨5019620, by rfl⟩ : syracuseStep 6692827 = 10039241) B10039241
theorem B64340345 : Blo 1762082 64340345 := bstep (se 2 (by rfl) ⟨24127629, by rfl⟩ : syracuseStep 64340345 = 48255259) B48255259
theorem B5948639 : Blo 1762082 5948639 := bstep (se 1 (by rfl) ⟨4461479, by rfl⟩ : syracuseStep 5948639 = 8922959) B8922959
theorem B5023403 : Blo 1762082 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B1763023 : Blo 1762082 1763023 := bstep (se 1 (by rfl) ⟨1322267, by rfl⟩ : syracuseStep 1763023 = 2644535) B2644535
theorem B1984207 : Blo 1762082 1984207 := bstep (se 1 (by rfl) ⟨1488155, by rfl⟩ : syracuseStep 1984207 = 2976311) B2976311
theorem B32163601 : Blo 1762082 32163601 := bstep (se 2 (by rfl) ⟨12061350, by rfl⟩ : syracuseStep 32163601 = 24122701) B24122701
theorem B5949665 : Blo 1762082 5949665 := bstep (se 2 (by rfl) ⟨2231124, by rfl⟩ : syracuseStep 5949665 = 4462249) B4462249
theorem B1763567 : Blo 1762082 1763567 := bstep (se 1 (by rfl) ⟨1322675, by rfl⟩ : syracuseStep 1763567 = 2645351) B2645351
theorem B8923769 : Blo 1762082 8923769 := bstep (se 2 (by rfl) ⟨3346413, by rfl⟩ : syracuseStep 8923769 = 6692827) B6692827
theorem B293325907 : Blo 1762082 293325907 := bstep (se 1 (by rfl) ⟨219994430, by rfl⟩ : syracuseStep 293325907 = 439988861) B439988861
theorem B3345563 : Blo 1762082 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B3968567 : Blo 1762082 3968567 := bstep (se 1 (by rfl) ⟨2976425, by rfl⟩ : syracuseStep 3968567 = 5952851) B5952851
theorem B28610243 : Blo 1762082 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B36695879 : Blo 1762082 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B3346771 : Blo 1762082 3346771 := bstep (se 1 (by rfl) ⟨2510078, by rfl⟩ : syracuseStep 3346771 = 5020157) B5020157
theorem B309287591 : Blo 1762082 309287591 := bstep (se 1 (by rfl) ⟨231965693, by rfl⟩ : syracuseStep 309287591 = 463931387) B463931387
theorem B33897203 : Blo 1762082 33897203 := bstep (se 1 (by rfl) ⟨25422902, by rfl⟩ : syracuseStep 33897203 = 50845805) B50845805
theorem B5020555 : Blo 1762082 5020555 := bstep (se 1 (by rfl) ⟨3765416, by rfl⟩ : syracuseStep 5020555 = 7530833) B7530833
theorem B6355901 : Blo 1762082 6355901 := bstep (se 3 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 6355901 = 2383463) B2383463
theorem B68738057 : Blo 1762082 68738057 := bstep (se 2 (by rfl) ⟨25776771, by rfl⟩ : syracuseStep 68738057 = 51553543) B51553543
theorem B2645471 : Blo 1762082 2645471 := bstep (se 1 (by rfl) ⟨1984103, by rfl⟩ : syracuseStep 2645471 = 3968207) B3968207
theorem B2383625 : Blo 1762082 2383625 := bstep (se 2 (by rfl) ⟨893859, by rfl⟩ : syracuseStep 2383625 = 1787719) B1787719
theorem B2973631 : Blo 1762082 2973631 := bstep (se 1 (by rfl) ⟨2230223, by rfl⟩ : syracuseStep 2973631 = 4460447) B4460447
theorem B42893563 : Blo 1762082 42893563 := bstep (se 1 (by rfl) ⟨32170172, by rfl⟩ : syracuseStep 42893563 = 64340345) B64340345
theorem B8921501 : Blo 1762082 8921501 := bstep (se 3 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 8921501 = 3345563) B3345563
theorem B3965759 : Blo 1762082 3965759 := bstep (se 1 (by rfl) ⟨2974319, by rfl⟩ : syracuseStep 3965759 = 5948639) B5948639
theorem B6694073 : Blo 1762082 6694073 := bstep (se 2 (by rfl) ⟨2510277, by rfl⟩ : syracuseStep 6694073 = 5020555) B5020555
theorem B3966443 : Blo 1762082 3966443 := bstep (se 1 (by rfl) ⟨2974832, by rfl⟩ : syracuseStep 3966443 = 5949665) B5949665
theorem B5949179 : Blo 1762082 5949179 := bstep (se 1 (by rfl) ⟨4461884, by rfl⟩ : syracuseStep 5949179 = 8923769) B8923769
theorem B4237267 : Blo 1762082 4237267 := bstep (se 1 (by rfl) ⟨3177950, by rfl⟩ : syracuseStep 4237267 = 6355901) B6355901
theorem B1763647 : Blo 1762082 1763647 := bstep (se 1 (by rfl) ⟨1322735, by rfl⟩ : syracuseStep 1763647 = 2645471) B2645471
theorem B19073495 : Blo 1762082 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B24463919 : Blo 1762082 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B22598135 : Blo 1762082 22598135 := bstep (se 1 (by rfl) ⟨16948601, by rfl⟩ : syracuseStep 22598135 = 33897203) B33897203
theorem B4462361 : Blo 1762082 4462361 := bstep (se 2 (by rfl) ⟨1673385, by rfl⟩ : syracuseStep 4462361 = 3346771) B3346771
theorem B3348935 : Blo 1762082 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B391101209 : Blo 1762082 391101209 := bstep (se 2 (by rfl) ⟨146662953, by rfl⟩ : syracuseStep 391101209 = 293325907) B293325907
theorem B206191727 : Blo 1762082 206191727 := bstep (se 1 (by rfl) ⟨154643795, by rfl⟩ : syracuseStep 206191727 = 309287591) B309287591
theorem B45825371 : Blo 1762082 45825371 := bstep (se 1 (by rfl) ⟨34369028, by rfl⟩ : syracuseStep 45825371 = 68738057) B68738057
theorem B6356333 : Blo 1762082 6356333 := bstep (se 3 (by rfl) ⟨1191812, by rfl⟩ : syracuseStep 6356333 = 2383625) B2383625
theorem B2645609 : Blo 1762082 2645609 := bstep (se 2 (by rfl) ⟨992103, by rfl⟩ : syracuseStep 2645609 = 1984207) B1984207
theorem B42884801 : Blo 1762082 42884801 := bstep (se 2 (by rfl) ⟨16081800, by rfl⟩ : syracuseStep 42884801 = 32163601) B32163601
theorem B2645711 : Blo 1762082 2645711 := bstep (se 1 (by rfl) ⟨1984283, by rfl⟩ : syracuseStep 2645711 = 3968567) B3968567
theorem B3964841 : Blo 1762082 3964841 := bstep (se 2 (by rfl) ⟨1486815, by rfl⟩ : syracuseStep 3964841 = 2973631) B2973631
theorem B5947667 : Blo 1762082 5947667 := bstep (se 1 (by rfl) ⟨4460750, by rfl⟩ : syracuseStep 5947667 = 8921501) B8921501
theorem B15065423 : Blo 1762082 15065423 := bstep (se 1 (by rfl) ⟨11299067, by rfl⟩ : syracuseStep 15065423 = 22598135) B22598135
theorem B16950221 : Blo 1762082 16950221 := bstep (se 3 (by rfl) ⟨3178166, by rfl⟩ : syracuseStep 16950221 = 6356333) B6356333
theorem B3966119 : Blo 1762082 3966119 := bstep (se 1 (by rfl) ⟨2974589, by rfl⟩ : syracuseStep 3966119 = 5949179) B5949179
theorem B2974907 : Blo 1762082 2974907 := bstep (se 1 (by rfl) ⟨2231180, by rfl⟩ : syracuseStep 2974907 = 4462361) B4462361
theorem B12715663 : Blo 1762082 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B30550247 : Blo 1762082 30550247 := bstep (se 1 (by rfl) ⟨22912685, by rfl⟩ : syracuseStep 30550247 = 45825371) B45825371
theorem B1763739 : Blo 1762082 1763739 := bstep (se 1 (by rfl) ⟨1322804, by rfl⟩ : syracuseStep 1763739 = 2645609) B2645609
theorem B1763807 : Blo 1762082 1763807 := bstep (se 1 (by rfl) ⟨1322855, by rfl⟩ : syracuseStep 1763807 = 2645711) B2645711
theorem B57191417 : Blo 1762082 57191417 := bstep (se 2 (by rfl) ⟨21446781, by rfl⟩ : syracuseStep 57191417 = 42893563) B42893563
theorem B2232623 : Blo 1762082 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B5649689 : Blo 1762082 5649689 := bstep (se 2 (by rfl) ⟨2118633, by rfl⟩ : syracuseStep 5649689 = 4237267) B4237267
theorem B2643227 : Blo 1762082 2643227 := bstep (se 1 (by rfl) ⟨1982420, by rfl⟩ : syracuseStep 2643227 = 3964841) B3964841
theorem B2643839 : Blo 1762082 2643839 := bstep (se 1 (by rfl) ⟨1982879, by rfl⟩ : syracuseStep 2643839 = 3965759) B3965759
theorem B4462715 : Blo 1762082 4462715 := bstep (se 1 (by rfl) ⟨3347036, by rfl⟩ : syracuseStep 4462715 = 6694073) B6694073
theorem B2644295 : Blo 1762082 2644295 := bstep (se 1 (by rfl) ⟨1983221, by rfl⟩ : syracuseStep 2644295 = 3966443) B3966443
theorem B16309279 : Blo 1762082 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B260734139 : Blo 1762082 260734139 := bstep (se 1 (by rfl) ⟨195550604, by rfl⟩ : syracuseStep 260734139 = 391101209) B391101209
theorem B137461151 : Blo 1762082 137461151 := bstep (se 1 (by rfl) ⟨103095863, by rfl⟩ : syracuseStep 137461151 = 206191727) B206191727
theorem B28589867 : Blo 1762082 28589867 := bstep (se 1 (by rfl) ⟨21442400, by rfl⟩ : syracuseStep 28589867 = 42884801) B42884801
theorem B3965111 : Blo 1762082 3965111 := bstep (se 1 (by rfl) ⟨2973833, by rfl⟩ : syracuseStep 3965111 = 5947667) B5947667
theorem B10043615 : Blo 1762082 10043615 := bstep (se 1 (by rfl) ⟨7532711, by rfl⟩ : syracuseStep 10043615 = 15065423) B15065423
theorem B1983271 : Blo 1762082 1983271 := bstep (se 1 (by rfl) ⟨1487453, by rfl⟩ : syracuseStep 1983271 = 2974907) B2974907
theorem B1762151 : Blo 1762082 1762151 := bstep (se 1 (by rfl) ⟨1321613, by rfl⟩ : syracuseStep 1762151 = 2643227) B2643227
theorem B1762559 : Blo 1762082 1762559 := bstep (se 1 (by rfl) ⟨1321919, by rfl⟩ : syracuseStep 1762559 = 2643839) B2643839
theorem B2975143 : Blo 1762082 2975143 := bstep (se 1 (by rfl) ⟨2231357, by rfl⟩ : syracuseStep 2975143 = 4462715) B4462715
theorem B20366831 : Blo 1762082 20366831 := bstep (se 1 (by rfl) ⟨15275123, by rfl⟩ : syracuseStep 20366831 = 30550247) B30550247
theorem B1762863 : Blo 1762082 1762863 := bstep (se 1 (by rfl) ⟨1322147, by rfl⟩ : syracuseStep 1762863 = 2644295) B2644295
theorem B38127611 : Blo 1762082 38127611 := bstep (se 1 (by rfl) ⟨28595708, by rfl⟩ : syracuseStep 38127611 = 57191417) B57191417
theorem B11300147 : Blo 1762082 11300147 := bstep (se 1 (by rfl) ⟨8475110, by rfl⟩ : syracuseStep 11300147 = 16950221) B16950221
theorem B21745705 : Blo 1762082 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B173822759 : Blo 1762082 173822759 := bstep (se 1 (by rfl) ⟨130367069, by rfl⟩ : syracuseStep 173822759 = 260734139) B260734139
theorem B16954217 : Blo 1762082 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B91640767 : Blo 1762082 91640767 := bstep (se 1 (by rfl) ⟨68730575, by rfl⟩ : syracuseStep 91640767 = 137461151) B137461151
theorem B19059911 : Blo 1762082 19059911 := bstep (se 1 (by rfl) ⟨14294933, by rfl⟩ : syracuseStep 19059911 = 28589867) B28589867
theorem B2644079 : Blo 1762082 2644079 := bstep (se 1 (by rfl) ⟨1983059, by rfl⟩ : syracuseStep 2644079 = 3966119) B3966119
theorem B5953661 : Blo 1762082 5953661 := bstep (se 3 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 5953661 = 2232623) B2232623
theorem B3766459 : Blo 1762082 3766459 := bstep (se 1 (by rfl) ⟨2824844, by rfl⟩ : syracuseStep 3766459 = 5649689) B5649689
theorem B5021945 : Blo 1762082 5021945 := bstep (se 2 (by rfl) ⟨1883229, by rfl⟩ : syracuseStep 5021945 = 3766459) B3766459
theorem B12706607 : Blo 1762082 12706607 := bstep (se 1 (by rfl) ⟨9529955, by rfl⟩ : syracuseStep 12706607 = 19059911) B19059911
theorem B1762719 : Blo 1762082 1762719 := bstep (se 1 (by rfl) ⟨1322039, by rfl⟩ : syracuseStep 1762719 = 2644079) B2644079
theorem B3966857 : Blo 1762082 3966857 := bstep (se 2 (by rfl) ⟨1487571, by rfl⟩ : syracuseStep 3966857 = 2975143) B2975143
theorem B28994273 : Blo 1762082 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B6695743 : Blo 1762082 6695743 := bstep (se 1 (by rfl) ⟨5021807, by rfl⟩ : syracuseStep 6695743 = 10043615) B10043615
theorem B13577887 : Blo 1762082 13577887 := bstep (se 1 (by rfl) ⟨10183415, by rfl⟩ : syracuseStep 13577887 = 20366831) B20366831
theorem B122187689 : Blo 1762082 122187689 := bstep (se 2 (by rfl) ⟨45820383, by rfl⟩ : syracuseStep 122187689 = 91640767) B91640767
theorem B3969107 : Blo 1762082 3969107 := bstep (se 1 (by rfl) ⟨2976830, by rfl⟩ : syracuseStep 3969107 = 5953661) B5953661
theorem B7533431 : Blo 1762082 7533431 := bstep (se 1 (by rfl) ⟨5650073, by rfl⟩ : syracuseStep 7533431 = 11300147) B11300147
theorem B2643407 : Blo 1762082 2643407 := bstep (se 1 (by rfl) ⟨1982555, by rfl⟩ : syracuseStep 2643407 = 3965111) B3965111
theorem B115881839 : Blo 1762082 115881839 := bstep (se 1 (by rfl) ⟨86911379, by rfl⟩ : syracuseStep 115881839 = 173822759) B173822759
theorem B11302811 : Blo 1762082 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B2644361 : Blo 1762082 2644361 := bstep (se 2 (by rfl) ⟨991635, by rfl⟩ : syracuseStep 2644361 = 1983271) B1983271
theorem B25418407 : Blo 1762082 25418407 := bstep (se 1 (by rfl) ⟨19063805, by rfl⟩ : syracuseStep 25418407 = 38127611) B38127611
theorem B2646071 : Blo 1762082 2646071 := bstep (se 1 (by rfl) ⟨1984553, by rfl⟩ : syracuseStep 2646071 = 3969107) B3969107
theorem B8471071 : Blo 1762082 8471071 := bstep (se 1 (by rfl) ⟨6353303, by rfl⟩ : syracuseStep 8471071 = 12706607) B12706607
theorem B5022287 : Blo 1762082 5022287 := bstep (se 1 (by rfl) ⟨3766715, by rfl⟩ : syracuseStep 5022287 = 7533431) B7533431
theorem B33891209 : Blo 1762082 33891209 := bstep (se 2 (by rfl) ⟨12709203, by rfl⟩ : syracuseStep 33891209 = 25418407) B25418407
theorem B1762271 : Blo 1762082 1762271 := bstep (se 1 (by rfl) ⟨1321703, by rfl⟩ : syracuseStep 1762271 = 2643407) B2643407
theorem B1762907 : Blo 1762082 1762907 := bstep (se 1 (by rfl) ⟨1322180, by rfl⟩ : syracuseStep 1762907 = 2644361) B2644361
theorem B77254559 : Blo 1762082 77254559 := bstep (se 1 (by rfl) ⟨57940919, by rfl⟩ : syracuseStep 77254559 = 115881839) B115881839
theorem B19329515 : Blo 1762082 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B81458459 : Blo 1762082 81458459 := bstep (se 1 (by rfl) ⟨61093844, by rfl⟩ : syracuseStep 81458459 = 122187689) B122187689
theorem B3347963 : Blo 1762082 3347963 := bstep (se 1 (by rfl) ⟨2510972, by rfl⟩ : syracuseStep 3347963 = 5021945) B5021945
theorem B72415397 : Blo 1762082 72415397 := bstep (se 4 (by rfl) ⟨6788943, by rfl⟩ : syracuseStep 72415397 = 13577887) B13577887
theorem B8927657 : Blo 1762082 8927657 := bstep (se 2 (by rfl) ⟨3347871, by rfl⟩ : syracuseStep 8927657 = 6695743) B6695743
theorem B2644571 : Blo 1762082 2644571 := bstep (se 1 (by rfl) ⟨1983428, by rfl⟩ : syracuseStep 2644571 = 3966857) B3966857
theorem B7535207 : Blo 1762082 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B45179045 : Blo 1762082 45179045 := bstep (se 4 (by rfl) ⟨4235535, by rfl⟩ : syracuseStep 45179045 = 8471071) B8471071
theorem B12886343 : Blo 1762082 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B22594139 : Blo 1762082 22594139 := bstep (se 1 (by rfl) ⟨16945604, by rfl⟩ : syracuseStep 22594139 = 33891209) B33891209
theorem B54305639 : Blo 1762082 54305639 := bstep (se 1 (by rfl) ⟨40729229, by rfl⟩ : syracuseStep 54305639 = 81458459) B81458459
theorem B48276931 : Blo 1762082 48276931 := bstep (se 1 (by rfl) ⟨36207698, by rfl⟩ : syracuseStep 48276931 = 72415397) B72415397
theorem B1763047 : Blo 1762082 1763047 := bstep (se 1 (by rfl) ⟨1322285, by rfl⟩ : syracuseStep 1763047 = 2644571) B2644571
theorem B5023471 : Blo 1762082 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B1764047 : Blo 1762082 1764047 := bstep (se 1 (by rfl) ⟨1323035, by rfl⟩ : syracuseStep 1764047 = 2646071) B2646071
theorem B2231975 : Blo 1762082 2231975 := bstep (se 1 (by rfl) ⟨1673981, by rfl⟩ : syracuseStep 2231975 = 3347963) B3347963
theorem B5951771 : Blo 1762082 5951771 := bstep (se 1 (by rfl) ⟨4463828, by rfl⟩ : syracuseStep 5951771 = 8927657) B8927657
theorem B3348191 : Blo 1762082 3348191 := bstep (se 1 (by rfl) ⟨2511143, by rfl⟩ : syracuseStep 3348191 = 5022287) B5022287
theorem B51503039 : Blo 1762082 51503039 := bstep (se 1 (by rfl) ⟨38627279, by rfl⟩ : syracuseStep 51503039 = 77254559) B77254559
theorem B34335359 : Blo 1762082 34335359 := bstep (se 1 (by rfl) ⟨25751519, by rfl⟩ : syracuseStep 34335359 = 51503039) B51503039
theorem B3967847 : Blo 1762082 3967847 := bstep (se 1 (by rfl) ⟨2975885, by rfl⟩ : syracuseStep 3967847 = 5951771) B5951771
theorem B36203759 : Blo 1762082 36203759 := bstep (se 1 (by rfl) ⟨27152819, by rfl⟩ : syracuseStep 36203759 = 54305639) B54305639
theorem B2232127 : Blo 1762082 2232127 := bstep (se 1 (by rfl) ⟨1674095, by rfl⟩ : syracuseStep 2232127 = 3348191) B3348191
theorem B5951933 : Blo 1762082 5951933 := bstep (se 3 (by rfl) ⟨1115987, by rfl⟩ : syracuseStep 5951933 = 2231975) B2231975
theorem B64369241 : Blo 1762082 64369241 := bstep (se 2 (by rfl) ⟨24138465, by rfl⟩ : syracuseStep 64369241 = 48276931) B48276931
theorem B6697961 : Blo 1762082 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B30119363 : Blo 1762082 30119363 := bstep (se 1 (by rfl) ⟨22589522, by rfl⟩ : syracuseStep 30119363 = 45179045) B45179045
theorem B8590895 : Blo 1762082 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B15062759 : Blo 1762082 15062759 := bstep (se 1 (by rfl) ⟨11297069, by rfl⟩ : syracuseStep 15062759 = 22594139) B22594139
theorem B4465307 : Blo 1762082 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B20079575 : Blo 1762082 20079575 := bstep (se 1 (by rfl) ⟨15059681, by rfl⟩ : syracuseStep 20079575 = 30119363) B30119363
theorem B5727263 : Blo 1762082 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B22890239 : Blo 1762082 22890239 := bstep (se 1 (by rfl) ⟨17167679, by rfl⟩ : syracuseStep 22890239 = 34335359) B34335359
theorem B24135839 : Blo 1762082 24135839 := bstep (se 1 (by rfl) ⟨18101879, by rfl⟩ : syracuseStep 24135839 = 36203759) B36203759
theorem B2976169 : Blo 1762082 2976169 := bstep (se 2 (by rfl) ⟨1116063, by rfl⟩ : syracuseStep 2976169 = 2232127) B2232127
theorem B3967955 : Blo 1762082 3967955 := bstep (se 1 (by rfl) ⟨2975966, by rfl⟩ : syracuseStep 3967955 = 5951933) B5951933
theorem B42912827 : Blo 1762082 42912827 := bstep (se 1 (by rfl) ⟨32184620, by rfl⟩ : syracuseStep 42912827 = 64369241) B64369241
theorem B10041839 : Blo 1762082 10041839 := bstep (se 1 (by rfl) ⟨7531379, by rfl⟩ : syracuseStep 10041839 = 15062759) B15062759
theorem B2645231 : Blo 1762082 2645231 := bstep (se 1 (by rfl) ⟨1983923, by rfl⟩ : syracuseStep 2645231 = 3967847) B3967847
theorem B13386383 : Blo 1762082 13386383 := bstep (se 1 (by rfl) ⟨10039787, by rfl⟩ : syracuseStep 13386383 = 20079575) B20079575
theorem B16090559 : Blo 1762082 16090559 := bstep (se 1 (by rfl) ⟨12067919, by rfl⟩ : syracuseStep 16090559 = 24135839) B24135839
theorem B6694559 : Blo 1762082 6694559 := bstep (se 1 (by rfl) ⟨5020919, by rfl⟩ : syracuseStep 6694559 = 10041839) B10041839
theorem B28608551 : Blo 1762082 28608551 := bstep (se 1 (by rfl) ⟨21456413, by rfl⟩ : syracuseStep 28608551 = 42912827) B42912827
theorem B1763487 : Blo 1762082 1763487 := bstep (se 1 (by rfl) ⟨1322615, by rfl⟩ : syracuseStep 1763487 = 2645231) B2645231
theorem B15272701 : Blo 1762082 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B2976871 : Blo 1762082 2976871 := bstep (se 1 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 2976871 = 4465307) B4465307
theorem B3968225 : Blo 1762082 3968225 := bstep (se 2 (by rfl) ⟨1488084, by rfl⟩ : syracuseStep 3968225 = 2976169) B2976169
theorem B15260159 : Blo 1762082 15260159 := bstep (se 1 (by rfl) ⟨11445119, by rfl⟩ : syracuseStep 15260159 = 22890239) B22890239
theorem B2645303 : Blo 1762082 2645303 := bstep (se 1 (by rfl) ⟨1983977, by rfl⟩ : syracuseStep 2645303 = 3967955) B3967955
theorem B81454405 : Blo 1762082 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B19072367 : Blo 1762082 19072367 := bstep (se 1 (by rfl) ⟨14304275, by rfl⟩ : syracuseStep 19072367 = 28608551) B28608551
theorem B1763535 : Blo 1762082 1763535 := bstep (se 1 (by rfl) ⟨1322651, by rfl⟩ : syracuseStep 1763535 = 2645303) B2645303
theorem B8924255 : Blo 1762082 8924255 := bstep (se 1 (by rfl) ⟨6693191, by rfl⟩ : syracuseStep 8924255 = 13386383) B13386383
theorem B10727039 : Blo 1762082 10727039 := bstep (se 1 (by rfl) ⟨8045279, by rfl⟩ : syracuseStep 10727039 = 16090559) B16090559
theorem B40693757 : Blo 1762082 40693757 := bstep (se 3 (by rfl) ⟨7630079, by rfl⟩ : syracuseStep 40693757 = 15260159) B15260159
theorem B3969161 : Blo 1762082 3969161 := bstep (se 2 (by rfl) ⟨1488435, by rfl⟩ : syracuseStep 3969161 = 2976871) B2976871
theorem B4463039 : Blo 1762082 4463039 := bstep (se 1 (by rfl) ⟨3347279, by rfl⟩ : syracuseStep 4463039 = 6694559) B6694559
theorem B2645483 : Blo 1762082 2645483 := bstep (se 1 (by rfl) ⟨1984112, by rfl⟩ : syracuseStep 2645483 = 3968225) B3968225
theorem B2646107 : Blo 1762082 2646107 := bstep (se 1 (by rfl) ⟨1984580, by rfl⟩ : syracuseStep 2646107 = 3969161) B3969161
theorem B12714911 : Blo 1762082 12714911 := bstep (se 1 (by rfl) ⟨9536183, by rfl⟩ : syracuseStep 12714911 = 19072367) B19072367
theorem B2975359 : Blo 1762082 2975359 := bstep (se 1 (by rfl) ⟨2231519, by rfl⟩ : syracuseStep 2975359 = 4463039) B4463039
theorem B5949503 : Blo 1762082 5949503 := bstep (se 1 (by rfl) ⟨4462127, by rfl⟩ : syracuseStep 5949503 = 8924255) B8924255
theorem B1763655 : Blo 1762082 1763655 := bstep (se 1 (by rfl) ⟨1322741, by rfl⟩ : syracuseStep 1763655 = 2645483) B2645483
theorem B108605873 : Blo 1762082 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B108516685 : Blo 1762082 108516685 := bstep (se 3 (by rfl) ⟨20346878, by rfl⟩ : syracuseStep 108516685 = 40693757) B40693757
theorem B28605437 : Blo 1762082 28605437 := bstep (se 3 (by rfl) ⟨5363519, by rfl⟩ : syracuseStep 28605437 = 10727039) B10727039
theorem B3966335 : Blo 1762082 3966335 := bstep (se 1 (by rfl) ⟨2974751, by rfl⟩ : syracuseStep 3966335 = 5949503) B5949503
theorem B144688913 : Blo 1762082 144688913 := bstep (se 2 (by rfl) ⟨54258342, by rfl⟩ : syracuseStep 144688913 = 108516685) B108516685
theorem B3967145 : Blo 1762082 3967145 := bstep (se 2 (by rfl) ⟨1487679, by rfl⟩ : syracuseStep 3967145 = 2975359) B2975359
theorem B1764071 : Blo 1762082 1764071 := bstep (se 1 (by rfl) ⟨1323053, by rfl⟩ : syracuseStep 1764071 = 2646107) B2646107
theorem B72403915 : Blo 1762082 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B8476607 : Blo 1762082 8476607 := bstep (se 1 (by rfl) ⟨6357455, by rfl⟩ : syracuseStep 8476607 = 12714911) B12714911
theorem B19070291 : Blo 1762082 19070291 := bstep (se 1 (by rfl) ⟨14302718, by rfl⟩ : syracuseStep 19070291 = 28605437) B28605437
theorem B22604285 : Blo 1762082 22604285 := bstep (se 3 (by rfl) ⟨4238303, by rfl⟩ : syracuseStep 22604285 = 8476607) B8476607
theorem B96538553 : Blo 1762082 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B2644223 : Blo 1762082 2644223 := bstep (se 1 (by rfl) ⟨1983167, by rfl⟩ : syracuseStep 2644223 = 3966335) B3966335
theorem B96459275 : Blo 1762082 96459275 := bstep (se 1 (by rfl) ⟨72344456, by rfl⟩ : syracuseStep 96459275 = 144688913) B144688913
theorem B2644763 : Blo 1762082 2644763 := bstep (se 1 (by rfl) ⟨1983572, by rfl⟩ : syracuseStep 2644763 = 3967145) B3967145
theorem B12713527 : Blo 1762082 12713527 := bstep (se 1 (by rfl) ⟨9535145, by rfl⟩ : syracuseStep 12713527 = 19070291) B19070291
theorem B1762815 : Blo 1762082 1762815 := bstep (se 1 (by rfl) ⟨1322111, by rfl⟩ : syracuseStep 1762815 = 2644223) B2644223
theorem B1763175 : Blo 1762082 1763175 := bstep (se 1 (by rfl) ⟨1322381, by rfl⟩ : syracuseStep 1763175 = 2644763) B2644763
theorem B16951369 : Blo 1762082 16951369 := bstep (se 2 (by rfl) ⟨6356763, by rfl⟩ : syracuseStep 16951369 = 12713527) B12713527
theorem B64359035 : Blo 1762082 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B15069523 : Blo 1762082 15069523 := bstep (se 1 (by rfl) ⟨11302142, by rfl⟩ : syracuseStep 15069523 = 22604285) B22604285
theorem B64306183 : Blo 1762082 64306183 := bstep (se 1 (by rfl) ⟨48229637, by rfl⟩ : syracuseStep 64306183 = 96459275) B96459275
theorem B22601825 : Blo 1762082 22601825 := bstep (se 2 (by rfl) ⟨8475684, by rfl⟩ : syracuseStep 22601825 = 16951369) B16951369
theorem B85741577 : Blo 1762082 85741577 := bstep (se 2 (by rfl) ⟨32153091, by rfl⟩ : syracuseStep 85741577 = 64306183) B64306183
theorem B42906023 : Blo 1762082 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B20092697 : Blo 1762082 20092697 := bstep (se 2 (by rfl) ⟨7534761, by rfl⟩ : syracuseStep 20092697 = 15069523) B15069523
theorem B13395131 : Blo 1762082 13395131 := bstep (se 1 (by rfl) ⟨10046348, by rfl⟩ : syracuseStep 13395131 = 20092697) B20092697
theorem B15067883 : Blo 1762082 15067883 := bstep (se 1 (by rfl) ⟨11300912, by rfl⟩ : syracuseStep 15067883 = 22601825) B22601825
theorem B57161051 : Blo 1762082 57161051 := bstep (se 1 (by rfl) ⟨42870788, by rfl⟩ : syracuseStep 57161051 = 85741577) B85741577
theorem B28604015 : Blo 1762082 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B8930087 : Blo 1762082 8930087 := bstep (se 1 (by rfl) ⟨6697565, by rfl⟩ : syracuseStep 8930087 = 13395131) B13395131
theorem B10045255 : Blo 1762082 10045255 := bstep (se 1 (by rfl) ⟨7533941, by rfl⟩ : syracuseStep 10045255 = 15067883) B15067883
theorem B38107367 : Blo 1762082 38107367 := bstep (se 1 (by rfl) ⟨28580525, by rfl⟩ : syracuseStep 38107367 = 57161051) B57161051
theorem B19069343 : Blo 1762082 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B25404911 : Blo 1762082 25404911 := bstep (se 1 (by rfl) ⟨19053683, by rfl⟩ : syracuseStep 25404911 = 38107367) B38107367
theorem B5953391 : Blo 1762082 5953391 := bstep (se 1 (by rfl) ⟨4465043, by rfl⟩ : syracuseStep 5953391 = 8930087) B8930087
theorem B12712895 : Blo 1762082 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B13393673 : Blo 1762082 13393673 := bstep (se 2 (by rfl) ⟨5022627, by rfl⟩ : syracuseStep 13393673 = 10045255) B10045255
theorem B16936607 : Blo 1762082 16936607 := bstep (se 1 (by rfl) ⟨12702455, by rfl⟩ : syracuseStep 16936607 = 25404911) B25404911
theorem B3968927 : Blo 1762082 3968927 := bstep (se 1 (by rfl) ⟨2976695, by rfl⟩ : syracuseStep 3968927 = 5953391) B5953391
theorem B8475263 : Blo 1762082 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B8929115 : Blo 1762082 8929115 := bstep (se 1 (by rfl) ⟨6696836, by rfl⟩ : syracuseStep 8929115 = 13393673) B13393673
theorem B11291071 : Blo 1762082 11291071 := bstep (se 1 (by rfl) ⟨8468303, by rfl⟩ : syracuseStep 11291071 = 16936607) B16936607
theorem B5952743 : Blo 1762082 5952743 := bstep (se 1 (by rfl) ⟨4464557, by rfl⟩ : syracuseStep 5952743 = 8929115) B8929115
theorem B5650175 : Blo 1762082 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B2645951 : Blo 1762082 2645951 := bstep (se 1 (by rfl) ⟨1984463, by rfl⟩ : syracuseStep 2645951 = 3968927) B3968927
theorem B15067133 : Blo 1762082 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B1763967 : Blo 1762082 1763967 := bstep (se 1 (by rfl) ⟨1322975, by rfl⟩ : syracuseStep 1763967 = 2645951) B2645951
theorem B3968495 : Blo 1762082 3968495 := bstep (se 1 (by rfl) ⟨2976371, by rfl⟩ : syracuseStep 3968495 = 5952743) B5952743
theorem B15054761 : Blo 1762082 15054761 := bstep (se 2 (by rfl) ⟨5645535, by rfl⟩ : syracuseStep 15054761 = 11291071) B11291071
theorem B10036507 : Blo 1762082 10036507 := bstep (se 1 (by rfl) ⟨7527380, by rfl⟩ : syracuseStep 10036507 = 15054761) B15054761
theorem B10044755 : Blo 1762082 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B2645663 : Blo 1762082 2645663 := bstep (se 1 (by rfl) ⟨1984247, by rfl⟩ : syracuseStep 2645663 = 3968495) B3968495
theorem B1763775 : Blo 1762082 1763775 := bstep (se 1 (by rfl) ⟨1322831, by rfl⟩ : syracuseStep 1763775 = 2645663) B2645663
theorem B6696503 : Blo 1762082 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B13382009 : Blo 1762082 13382009 := bstep (se 2 (by rfl) ⟨5018253, by rfl⟩ : syracuseStep 13382009 = 10036507) B10036507
theorem B8921339 : Blo 1762082 8921339 := bstep (se 1 (by rfl) ⟨6691004, by rfl⟩ : syracuseStep 8921339 = 13382009) B13382009
theorem B4464335 : Blo 1762082 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B5947559 : Blo 1762082 5947559 := bstep (se 1 (by rfl) ⟨4460669, by rfl⟩ : syracuseStep 5947559 = 8921339) B8921339
theorem B2976223 : Blo 1762082 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B3965039 : Blo 1762082 3965039 := bstep (se 1 (by rfl) ⟨2973779, by rfl⟩ : syracuseStep 3965039 = 5947559) B5947559
theorem B3968297 : Blo 1762082 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B2643359 : Blo 1762082 2643359 := bstep (se 1 (by rfl) ⟨1982519, by rfl⟩ : syracuseStep 2643359 = 3965039) B3965039
theorem B2645531 : Blo 1762082 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B1762239 : Blo 1762082 1762239 := bstep (se 1 (by rfl) ⟨1321679, by rfl⟩ : syracuseStep 1762239 = 2643359) B2643359
theorem B1763687 : Blo 1762082 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531

theorem C0 (j : ℕ) (h1 : 440520 ≤ j) (h2 : j ≤ 441019) : Blo 1762082 (4 * j + 3) := by
  interval_cases j
  · exact B1762083
  · exact B1762087
  · exact B1762091
  · exact B1762095
  · exact B1762099
  · exact B1762103
  · exact B1762107
  · exact B1762111
  · exact B1762115
  · exact B1762119
  · exact B1762123
  · exact B1762127
  · exact B1762131
  · exact B1762135
  · exact B1762139
  · exact B1762143
  · exact B1762147
  · exact B1762151
  · exact B1762155
  · exact B1762159
  · exact B1762163
  · exact B1762167
  · exact B1762171
  · exact B1762175
  · exact B1762179
  · exact B1762183
  · exact B1762187
  · exact B1762191
  · exact B1762195
  · exact B1762199
  · exact B1762203
  · exact B1762207
  · exact B1762211
  · exact B1762215
  · exact B1762219
  · exact B1762223
  · exact B1762227
  · exact B1762231
  · exact B1762235
  · exact B1762239
  · exact B1762243
  · exact B1762247
  · exact B1762251
  · exact B1762255
  · exact B1762259
  · exact B1762263
  · exact B1762267
  · exact B1762271
  · exact B1762275
  · exact B1762279
  · exact B1762283
  · exact B1762287
  · exact B1762291
  · exact B1762295
  · exact B1762299
  · exact B1762303
  · exact B1762307
  · exact B1762311
  · exact B1762315
  · exact B1762319
  · exact B1762323
  · exact B1762327
  · exact B1762331
  · exact B1762335
  · exact B1762339
  · exact B1762343
  · exact B1762347
  · exact B1762351
  · exact B1762355
  · exact B1762359
  · exact B1762363
  · exact B1762367
  · exact B1762371
  · exact B1762375
  · exact B1762379
  · exact B1762383
  · exact B1762387
  · exact B1762391
  · exact B1762395
  · exact B1762399
  · exact B1762403
  · exact B1762407
  · exact B1762411
  · exact B1762415
  · exact B1762419
  · exact B1762423
  · exact B1762427
  · exact B1762431
  · exact B1762435
  · exact B1762439
  · exact B1762443
  · exact B1762447
  · exact B1762451
  · exact B1762455
  · exact B1762459
  · exact B1762463
  · exact B1762467
  · exact B1762471
  · exact B1762475
  · exact B1762479
  · exact B1762483
  · exact B1762487
  · exact B1762491
  · exact B1762495
  · exact B1762499
  · exact B1762503
  · exact B1762507
  · exact B1762511
  · exact B1762515
  · exact B1762519
  · exact B1762523
  · exact B1762527
  · exact B1762531
  · exact B1762535
  · exact B1762539
  · exact B1762543
  · exact B1762547
  · exact B1762551
  · exact B1762555
  · exact B1762559
  · exact B1762563
  · exact B1762567
  · exact B1762571
  · exact B1762575
  · exact B1762579
  · exact B1762583
  · exact B1762587
  · exact B1762591
  · exact B1762595
  · exact B1762599
  · exact B1762603
  · exact B1762607
  · exact B1762611
  · exact B1762615
  · exact B1762619
  · exact B1762623
  · exact B1762627
  · exact B1762631
  · exact B1762635
  · exact B1762639
  · exact B1762643
  · exact B1762647
  · exact B1762651
  · exact B1762655
  · exact B1762659
  · exact B1762663
  · exact B1762667
  · exact B1762671
  · exact B1762675
  · exact B1762679
  · exact B1762683
  · exact B1762687
  · exact B1762691
  · exact B1762695
  · exact B1762699
  · exact B1762703
  · exact B1762707
  · exact B1762711
  · exact B1762715
  · exact B1762719
  · exact B1762723
  · exact B1762727
  · exact B1762731
  · exact B1762735
  · exact B1762739
  · exact B1762743
  · exact B1762747
  · exact B1762751
  · exact B1762755
  · exact B1762759
  · exact B1762763
  · exact B1762767
  · exact B1762771
  · exact B1762775
  · exact B1762779
  · exact B1762783
  · exact B1762787
  · exact B1762791
  · exact B1762795
  · exact B1762799
  · exact B1762803
  · exact B1762807
  · exact B1762811
  · exact B1762815
  · exact B1762819
  · exact B1762823
  · exact B1762827
  · exact B1762831
  · exact B1762835
  · exact B1762839
  · exact B1762843
  · exact B1762847
  · exact B1762851
  · exact B1762855
  · exact B1762859
  · exact B1762863
  · exact B1762867
  · exact B1762871
  · exact B1762875
  · exact B1762879
  · exact B1762883
  · exact B1762887
  · exact B1762891
  · exact B1762895
  · exact B1762899
  · exact B1762903
  · exact B1762907
  · exact B1762911
  · exact B1762915
  · exact B1762919
  · exact B1762923
  · exact B1762927
  · exact B1762931
  · exact B1762935
  · exact B1762939
  · exact B1762943
  · exact B1762947
  · exact B1762951
  · exact B1762955
  · exact B1762959
  · exact B1762963
  · exact B1762967
  · exact B1762971
  · exact B1762975
  · exact B1762979
  · exact B1762983
  · exact B1762987
  · exact B1762991
  · exact B1762995
  · exact B1762999
  · exact B1763003
  · exact B1763007
  · exact B1763011
  · exact B1763015
  · exact B1763019
  · exact B1763023
  · exact B1763027
  · exact B1763031
  · exact B1763035
  · exact B1763039
  · exact B1763043
  · exact B1763047
  · exact B1763051
  · exact B1763055
  · exact B1763059
  · exact B1763063
  · exact B1763067
  · exact B1763071
  · exact B1763075
  · exact B1763079
  · exact B1763083
  · exact B1763087
  · exact B1763091
  · exact B1763095
  · exact B1763099
  · exact B1763103
  · exact B1763107
  · exact B1763111
  · exact B1763115
  · exact B1763119
  · exact B1763123
  · exact B1763127
  · exact B1763131
  · exact B1763135
  · exact B1763139
  · exact B1763143
  · exact B1763147
  · exact B1763151
  · exact B1763155
  · exact B1763159
  · exact B1763163
  · exact B1763167
  · exact B1763171
  · exact B1763175
  · exact B1763179
  · exact B1763183
  · exact B1763187
  · exact B1763191
  · exact B1763195
  · exact B1763199
  · exact B1763203
  · exact B1763207
  · exact B1763211
  · exact B1763215
  · exact B1763219
  · exact B1763223
  · exact B1763227
  · exact B1763231
  · exact B1763235
  · exact B1763239
  · exact B1763243
  · exact B1763247
  · exact B1763251
  · exact B1763255
  · exact B1763259
  · exact B1763263
  · exact B1763267
  · exact B1763271
  · exact B1763275
  · exact B1763279
  · exact B1763283
  · exact B1763287
  · exact B1763291
  · exact B1763295
  · exact B1763299
  · exact B1763303
  · exact B1763307
  · exact B1763311
  · exact B1763315
  · exact B1763319
  · exact B1763323
  · exact B1763327
  · exact B1763331
  · exact B1763335
  · exact B1763339
  · exact B1763343
  · exact B1763347
  · exact B1763351
  · exact B1763355
  · exact B1763359
  · exact B1763363
  · exact B1763367
  · exact B1763371
  · exact B1763375
  · exact B1763379
  · exact B1763383
  · exact B1763387
  · exact B1763391
  · exact B1763395
  · exact B1763399
  · exact B1763403
  · exact B1763407
  · exact B1763411
  · exact B1763415
  · exact B1763419
  · exact B1763423
  · exact B1763427
  · exact B1763431
  · exact B1763435
  · exact B1763439
  · exact B1763443
  · exact B1763447
  · exact B1763451
  · exact B1763455
  · exact B1763459
  · exact B1763463
  · exact B1763467
  · exact B1763471
  · exact B1763475
  · exact B1763479
  · exact B1763483
  · exact B1763487
  · exact B1763491
  · exact B1763495
  · exact B1763499
  · exact B1763503
  · exact B1763507
  · exact B1763511
  · exact B1763515
  · exact B1763519
  · exact B1763523
  · exact B1763527
  · exact B1763531
  · exact B1763535
  · exact B1763539
  · exact B1763543
  · exact B1763547
  · exact B1763551
  · exact B1763555
  · exact B1763559
  · exact B1763563
  · exact B1763567
  · exact B1763571
  · exact B1763575
  · exact B1763579
  · exact B1763583
  · exact B1763587
  · exact B1763591
  · exact B1763595
  · exact B1763599
  · exact B1763603
  · exact B1763607
  · exact B1763611
  · exact B1763615
  · exact B1763619
  · exact B1763623
  · exact B1763627
  · exact B1763631
  · exact B1763635
  · exact B1763639
  · exact B1763643
  · exact B1763647
  · exact B1763651
  · exact B1763655
  · exact B1763659
  · exact B1763663
  · exact B1763667
  · exact B1763671
  · exact B1763675
  · exact B1763679
  · exact B1763683
  · exact B1763687
  · exact B1763691
  · exact B1763695
  · exact B1763699
  · exact B1763703
  · exact B1763707
  · exact B1763711
  · exact B1763715
  · exact B1763719
  · exact B1763723
  · exact B1763727
  · exact B1763731
  · exact B1763735
  · exact B1763739
  · exact B1763743
  · exact B1763747
  · exact B1763751
  · exact B1763755
  · exact B1763759
  · exact B1763763
  · exact B1763767
  · exact B1763771
  · exact B1763775
  · exact B1763779
  · exact B1763783
  · exact B1763787
  · exact B1763791
  · exact B1763795
  · exact B1763799
  · exact B1763803
  · exact B1763807
  · exact B1763811
  · exact B1763815
  · exact B1763819
  · exact B1763823
  · exact B1763827
  · exact B1763831
  · exact B1763835
  · exact B1763839
  · exact B1763843
  · exact B1763847
  · exact B1763851
  · exact B1763855
  · exact B1763859
  · exact B1763863
  · exact B1763867
  · exact B1763871
  · exact B1763875
  · exact B1763879
  · exact B1763883
  · exact B1763887
  · exact B1763891
  · exact B1763895
  · exact B1763899
  · exact B1763903
  · exact B1763907
  · exact B1763911
  · exact B1763915
  · exact B1763919
  · exact B1763923
  · exact B1763927
  · exact B1763931
  · exact B1763935
  · exact B1763939
  · exact B1763943
  · exact B1763947
  · exact B1763951
  · exact B1763955
  · exact B1763959
  · exact B1763963
  · exact B1763967
  · exact B1763971
  · exact B1763975
  · exact B1763979
  · exact B1763983
  · exact B1763987
  · exact B1763991
  · exact B1763995
  · exact B1763999
  · exact B1764003
  · exact B1764007
  · exact B1764011
  · exact B1764015
  · exact B1764019
  · exact B1764023
  · exact B1764027
  · exact B1764031
  · exact B1764035
  · exact B1764039
  · exact B1764043
  · exact B1764047
  · exact B1764051
  · exact B1764055
  · exact B1764059
  · exact B1764063
  · exact B1764067
  · exact B1764071
  · exact B1764075
  · exact B1764079

theorem solution (m : ℕ) (hlo : 1762082 ≤ m) (hhi : m ≤ 1764082) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 440520 ≤ j := by omega
    have hj2 : j ≤ 441019 := by omega
    have hb : Blo 1762082 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
