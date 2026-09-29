-- Prove2me | solution 1 for syracuse_descends_range_1466553_1468553
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:43.145126+00:00
-- url     : https://prove2.me/submissions/1a6dcb9b-ad8a-4314-9f6c-908395b00524

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


theorem B3301397 : Blo 1466553 3301397 := bbase (se 6 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 3301397 = 154753) (by norm_num)
theorem B5947445 : Blo 1466553 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B2785357 : Blo 1466553 2785357 := bbase (se 3 (by rfl) ⟨522254, by rfl⟩ : syracuseStep 2785357 = 1044509) (by norm_num)
theorem B3301469 : Blo 1466553 3301469 := bbase (se 3 (by rfl) ⟨619025, by rfl⟩ : syracuseStep 3301469 = 1238051) (by norm_num)
theorem B2089109 : Blo 1466553 2089109 := bbase (se 6 (by rfl) ⟨48963, by rfl⟩ : syracuseStep 2089109 = 97927) (by norm_num)
theorem B2351261 : Blo 1466553 2351261 := bbase (se 3 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 2351261 = 881723) (by norm_num)
theorem B3301541 : Blo 1466553 3301541 := bbase (se 4 (by rfl) ⟨309519, by rfl⟩ : syracuseStep 3301541 = 619039) (by norm_num)
theorem B2089189 : Blo 1466553 2089189 := bbase (se 4 (by rfl) ⟨195861, by rfl⟩ : syracuseStep 2089189 = 391723) (by norm_num)
theorem B3301613 : Blo 1466553 3301613 := bbase (se 3 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 3301613 = 1238105) (by norm_num)
theorem B14106869 : Blo 1466553 14106869 := bbase (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) (by norm_num)
theorem B3391741 : Blo 1466553 3391741 := bbase (se 3 (by rfl) ⟨635951, by rfl⟩ : syracuseStep 3391741 = 1271903) (by norm_num)
theorem B3301685 : Blo 1466553 3301685 := bbase (se 5 (by rfl) ⟨154766, by rfl⟩ : syracuseStep 3301685 = 309533) (by norm_num)
theorem B7430453 : Blo 1466553 7430453 := bbase (se 5 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 7430453 = 696605) (by norm_num)
theorem B2089309 : Blo 1466553 2089309 := bbase (se 3 (by rfl) ⟨391745, by rfl⟩ : syracuseStep 2089309 = 783491) (by norm_num)
theorem B2785661 : Blo 1466553 2785661 := bbase (se 3 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 2785661 = 1044623) (by norm_num)
theorem B3301757 : Blo 1466553 3301757 := bbase (se 3 (by rfl) ⟨619079, by rfl⟩ : syracuseStep 3301757 = 1238159) (by norm_num)
theorem B2089405 : Blo 1466553 2089405 := bbase (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) (by norm_num)
theorem B2351549 : Blo 1466553 2351549 := bbase (se 3 (by rfl) ⟨440915, by rfl⟩ : syracuseStep 2351549 = 881831) (by norm_num)
theorem B3301829 : Blo 1466553 3301829 := bbase (se 4 (by rfl) ⟨309546, by rfl⟩ : syracuseStep 3301829 = 619093) (by norm_num)
theorem B3301901 : Blo 1466553 3301901 := bbase (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) (by norm_num)
theorem B5571125 : Blo 1466553 5571125 := bbase (se 5 (by rfl) ⟨261146, by rfl⟩ : syracuseStep 5571125 = 522293) (by norm_num)
theorem B3301973 : Blo 1466553 3301973 := bbase (se 8 (by rfl) ⟨19347, by rfl⟩ : syracuseStep 3301973 = 38695) (by norm_num)
theorem B1761917 : Blo 1466553 1761917 := bbase (se 3 (by rfl) ⟨330359, by rfl⟩ : syracuseStep 1761917 = 660719) (by norm_num)
theorem B3302045 : Blo 1466553 3302045 := bbase (se 3 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 3302045 = 1238267) (by norm_num)
theorem B3302117 : Blo 1466553 3302117 := bbase (se 4 (by rfl) ⟨309573, by rfl⟩ : syracuseStep 3302117 = 619147) (by norm_num)
theorem B7144213 : Blo 1466553 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B2614037 : Blo 1466553 2614037 := bbase (se 6 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 2614037 = 122533) (by norm_num)
theorem B3302189 : Blo 1466553 3302189 := bbase (se 3 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 3302189 = 1238321) (by norm_num)
theorem B2974517 : Blo 1466553 2974517 := bbase (se 5 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 2974517 = 278861) (by norm_num)
theorem B2474813 : Blo 1466553 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B5571413 : Blo 1466553 5571413 := bbase (se 9 (by rfl) ⟨16322, by rfl⟩ : syracuseStep 5571413 = 32645) (by norm_num)
theorem B7938901 : Blo 1466553 7938901 := bbase (se 9 (by rfl) ⟨23258, by rfl⟩ : syracuseStep 7938901 = 46517) (by norm_num)
theorem B2351965 : Blo 1466553 2351965 := bbase (se 3 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 2351965 = 881987) (by norm_num)
theorem B3302261 : Blo 1466553 3302261 := bbase (se 5 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 3302261 = 309587) (by norm_num)
theorem B7938965 : Blo 1466553 7938965 := bbase (se 6 (by rfl) ⟨186069, by rfl⟩ : syracuseStep 7938965 = 372139) (by norm_num)
theorem B2089901 : Blo 1466553 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B2474941 : Blo 1466553 2474941 := bbase (se 3 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 2474941 = 928103) (by norm_num)
theorem B3302333 : Blo 1466553 3302333 := bbase (se 3 (by rfl) ⟨619187, by rfl⟩ : syracuseStep 3302333 = 1238375) (by norm_num)
theorem B5161925 : Blo 1466553 5161925 := bbase (se 4 (by rfl) ⟨483930, by rfl⟩ : syracuseStep 5161925 = 967861) (by norm_num)
theorem B3302405 : Blo 1466553 3302405 := bbase (se 4 (by rfl) ⟨309600, by rfl⟩ : syracuseStep 3302405 = 619201) (by norm_num)
theorem B2475029 : Blo 1466553 2475029 := bbase (se 6 (by rfl) ⟨58008, by rfl⟩ : syracuseStep 2475029 = 116017) (by norm_num)
theorem B7939093 : Blo 1466553 7939093 := bbase (se 6 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 7939093 = 372145) (by norm_num)
theorem B6693941 : Blo 1466553 6693941 := bbase (se 5 (by rfl) ⟨313778, by rfl⟩ : syracuseStep 6693941 = 627557) (by norm_num)
theorem B3302477 : Blo 1466553 3302477 := bbase (se 3 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 3302477 = 1238429) (by norm_num)
theorem B2786413 : Blo 1466553 2786413 := bbase (se 3 (by rfl) ⟨522452, by rfl⟩ : syracuseStep 2786413 = 1044905) (by norm_num)
theorem B2475157 : Blo 1466553 2475157 := bbase (se 6 (by rfl) ⟨58011, by rfl⟩ : syracuseStep 2475157 = 116023) (by norm_num)
theorem B3302549 : Blo 1466553 3302549 := bbase (se 6 (by rfl) ⟨77403, by rfl⟩ : syracuseStep 3302549 = 154807) (by norm_num)
theorem B3302621 : Blo 1466553 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B2475245 : Blo 1466553 2475245 := bbase (se 3 (by rfl) ⟨464108, by rfl⟩ : syracuseStep 2475245 = 928217) (by norm_num)
theorem B2786557 : Blo 1466553 2786557 := bbase (se 3 (by rfl) ⟨522479, by rfl⟩ : syracuseStep 2786557 = 1044959) (by norm_num)
theorem B4179221 : Blo 1466553 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B3302693 : Blo 1466553 3302693 := bbase (se 4 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 3302693 = 619255) (by norm_num)
theorem B3712301 : Blo 1466553 3712301 := bbase (se 3 (by rfl) ⟨696056, by rfl⟩ : syracuseStep 3712301 = 1392113) (by norm_num)
theorem B3015997 : Blo 1466553 3015997 := bbase (se 3 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 3015997 = 1130999) (by norm_num)
theorem B56411477 : Blo 1466553 56411477 := bbase (se 12 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 56411477 = 41317) (by norm_num)
theorem B2475373 : Blo 1466553 2475373 := bbase (se 3 (by rfl) ⟨464132, by rfl⟩ : syracuseStep 2475373 = 928265) (by norm_num)
theorem B3302765 : Blo 1466553 3302765 := bbase (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) (by norm_num)
theorem B1566097 : Blo 1466553 1566097 := bbase (se 2 (by rfl) ⟨587286, by rfl⟩ : syracuseStep 1566097 = 1174573) (by norm_num)
theorem B1762705 : Blo 1466553 1762705 := bbase (se 2 (by rfl) ⟨661014, by rfl⟩ : syracuseStep 1762705 = 1322029) (by norm_num)
theorem B1697177 : Blo 1466553 1697177 := bbase (se 2 (by rfl) ⟨636441, by rfl⟩ : syracuseStep 1697177 = 1272883) (by norm_num)
theorem B2786717 : Blo 1466553 2786717 := bbase (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) (by norm_num)
theorem B3302837 : Blo 1466553 3302837 := bbase (se 5 (by rfl) ⟨154820, by rfl⟩ : syracuseStep 3302837 = 309641) (by norm_num)
theorem B2475461 : Blo 1466553 2475461 := bbase (se 4 (by rfl) ⟨232074, by rfl⟩ : syracuseStep 2475461 = 464149) (by norm_num)
theorem B2090453 : Blo 1466553 2090453 := bbase (se 7 (by rfl) ⟨24497, by rfl⟩ : syracuseStep 2090453 = 48995) (by norm_num)
theorem B3712493 : Blo 1466553 3712493 := bbase (se 3 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 3712493 = 1392185) (by norm_num)
theorem B3302909 : Blo 1466553 3302909 := bbase (se 3 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 3302909 = 1238591) (by norm_num)
theorem B6268421 : Blo 1466553 6268421 := bbase (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) (by norm_num)
theorem B1566217 : Blo 1466553 1566217 := bbase (se 2 (by rfl) ⟨587331, by rfl⟩ : syracuseStep 1566217 = 1174663) (by norm_num)
theorem B2786861 : Blo 1466553 2786861 := bbase (se 3 (by rfl) ⟨522536, by rfl⟩ : syracuseStep 2786861 = 1045073) (by norm_num)
theorem B2475589 : Blo 1466553 2475589 := bbase (se 4 (by rfl) ⟨232086, by rfl⟩ : syracuseStep 2475589 = 464173) (by norm_num)
theorem B3302981 : Blo 1466553 3302981 := bbase (se 4 (by rfl) ⟨309654, by rfl⟩ : syracuseStep 3302981 = 619309) (by norm_num)
theorem B7431749 : Blo 1466553 7431749 := bbase (se 4 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 7431749 = 1393453) (by norm_num)
theorem B3303053 : Blo 1466553 3303053 := bbase (se 3 (by rfl) ⟨619322, by rfl⟩ : syracuseStep 3303053 = 1238645) (by norm_num)
theorem B8922773 : Blo 1466553 8922773 := bbase (se 6 (by rfl) ⟨209127, by rfl⟩ : syracuseStep 8922773 = 418255) (by norm_num)
theorem B2475677 : Blo 1466553 2475677 := bbase (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) (by norm_num)
theorem B3303125 : Blo 1466553 3303125 := bbase (se 7 (by rfl) ⟨38708, by rfl⟩ : syracuseStep 3303125 = 77417) (by norm_num)
theorem B4703957 : Blo 1466553 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B6268661 : Blo 1466553 6268661 := bbase (se 5 (by rfl) ⟨293843, by rfl⟩ : syracuseStep 6268661 = 587687) (by norm_num)
theorem B1566469 : Blo 1466553 1566469 := bbase (se 4 (by rfl) ⟨146856, by rfl⟩ : syracuseStep 1566469 = 293713) (by norm_num)
theorem B1836805 : Blo 1466553 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B1566473 : Blo 1466553 1566473 := bbase (se 2 (by rfl) ⟨587427, by rfl⟩ : syracuseStep 1566473 = 1174855) (by norm_num)
theorem B2475805 : Blo 1466553 2475805 := bbase (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) (by norm_num)
theorem B3303197 : Blo 1466553 3303197 := bbase (se 3 (by rfl) ⟨619349, by rfl⟩ : syracuseStep 3303197 = 1238699) (by norm_num)
theorem B3712837 : Blo 1466553 3712837 := bbase (se 4 (by rfl) ⟨348078, by rfl⟩ : syracuseStep 3712837 = 696157) (by norm_num)
theorem B1673029 : Blo 1466553 1673029 := bbase (se 4 (by rfl) ⟨156846, by rfl⟩ : syracuseStep 1673029 = 313693) (by norm_num)
theorem B2787149 : Blo 1466553 2787149 := bbase (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) (by norm_num)
theorem B3303269 : Blo 1466553 3303269 := bbase (se 4 (by rfl) ⟨309681, by rfl⟩ : syracuseStep 3303269 = 619363) (by norm_num)
theorem B2475893 : Blo 1466553 2475893 := bbase (se 5 (by rfl) ⟨116057, by rfl⟩ : syracuseStep 2475893 = 232115) (by norm_num)
theorem B2860933 : Blo 1466553 2860933 := bbase (se 4 (by rfl) ⟨268212, by rfl⟩ : syracuseStep 2860933 = 536425) (by norm_num)
theorem B4949909 : Blo 1466553 4949909 := bbase (se 6 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 4949909 = 232027) (by norm_num)
theorem B3303341 : Blo 1466553 3303341 := bbase (se 3 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 3303341 = 1238753) (by norm_num)
theorem B3712949 : Blo 1466553 3712949 := bbase (se 5 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 3712949 = 348089) (by norm_num)
theorem B2787301 : Blo 1466553 2787301 := bbase (se 4 (by rfl) ⟨261309, by rfl⟩ : syracuseStep 2787301 = 522619) (by norm_num)
theorem B2476021 : Blo 1466553 2476021 := bbase (se 5 (by rfl) ⟨116063, by rfl⟩ : syracuseStep 2476021 = 232127) (by norm_num)
theorem B5572597 : Blo 1466553 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B3303413 : Blo 1466553 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B3303485 : Blo 1466553 3303485 := bbase (se 3 (by rfl) ⟨619403, by rfl⟩ : syracuseStep 3303485 = 1238807) (by norm_num)
theorem B2476109 : Blo 1466553 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B12544085 : Blo 1466553 12544085 := bbase (se 8 (by rfl) ⟨73500, by rfl⟩ : syracuseStep 12544085 = 147001) (by norm_num)
theorem B1763417 : Blo 1466553 1763417 := bbase (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) (by norm_num)
theorem B3713141 : Blo 1466553 3713141 := bbase (se 5 (by rfl) ⟨174053, by rfl⟩ : syracuseStep 3713141 = 348107) (by norm_num)
theorem B3303557 : Blo 1466553 3303557 := bbase (se 4 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 3303557 = 619417) (by norm_num)
theorem B8472757 : Blo 1466553 8472757 := bbase (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) (by norm_num)
theorem B2476237 : Blo 1466553 2476237 := bbase (se 3 (by rfl) ⟨464294, by rfl⟩ : syracuseStep 2476237 = 928589) (by norm_num)
theorem B3303629 : Blo 1466553 3303629 := bbase (se 3 (by rfl) ⟨619430, by rfl⟩ : syracuseStep 3303629 = 1238861) (by norm_num)
theorem B3303701 : Blo 1466553 3303701 := bbase (se 6 (by rfl) ⟨77430, by rfl⟩ : syracuseStep 3303701 = 154861) (by norm_num)
theorem B2787605 : Blo 1466553 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2509093 : Blo 1466553 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B2476325 : Blo 1466553 2476325 := bbase (se 4 (by rfl) ⟨232155, by rfl⟩ : syracuseStep 2476325 = 464311) (by norm_num)
theorem B5572901 : Blo 1466553 5572901 := bbase (se 4 (by rfl) ⟨522459, by rfl⟩ : syracuseStep 5572901 = 1044919) (by norm_num)
theorem B1567037 : Blo 1466553 1567037 := bbase (se 3 (by rfl) ⟨293819, by rfl⟩ : syracuseStep 1567037 = 587639) (by norm_num)
theorem B4950341 : Blo 1466553 4950341 := bbase (se 4 (by rfl) ⟨464094, by rfl⟩ : syracuseStep 4950341 = 928189) (by norm_num)
theorem B3303773 : Blo 1466553 3303773 := bbase (se 3 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 3303773 = 1238915) (by norm_num)
theorem B2476453 : Blo 1466553 2476453 := bbase (se 4 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 2476453 = 464335) (by norm_num)
theorem B3303845 : Blo 1466553 3303845 := bbase (se 4 (by rfl) ⟨309735, by rfl⟩ : syracuseStep 3303845 = 619471) (by norm_num)
theorem B1763753 : Blo 1466553 1763753 := bbase (se 2 (by rfl) ⟨661407, by rfl⟩ : syracuseStep 1763753 = 1322815) (by norm_num)
theorem B4180405 : Blo 1466553 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B3713485 : Blo 1466553 3713485 := bbase (se 3 (by rfl) ⟨696278, by rfl⟩ : syracuseStep 3713485 = 1392557) (by norm_num)
theorem B3303917 : Blo 1466553 3303917 := bbase (se 3 (by rfl) ⟨619484, by rfl⟩ : syracuseStep 3303917 = 1238969) (by norm_num)
theorem B1567225 : Blo 1466553 1567225 := bbase (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) (by norm_num)
theorem B2476541 : Blo 1466553 2476541 := bbase (se 3 (by rfl) ⟨464351, by rfl⟩ : syracuseStep 2476541 = 928703) (by norm_num)
theorem B1763869 : Blo 1466553 1763869 := bbase (se 3 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 1763869 = 661451) (by norm_num)
theorem B1763893 : Blo 1466553 1763893 := bbase (se 5 (by rfl) ⟨82682, by rfl⟩ : syracuseStep 1763893 = 165365) (by norm_num)
theorem B3303989 : Blo 1466553 3303989 := bbase (se 5 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 3303989 = 309749) (by norm_num)
theorem B3713597 : Blo 1466553 3713597 := bbase (se 3 (by rfl) ⟨696299, by rfl⟩ : syracuseStep 3713597 = 1392599) (by norm_num)
theorem B4180565 : Blo 1466553 4180565 := bbase (se 8 (by rfl) ⟨24495, by rfl⟩ : syracuseStep 4180565 = 48991) (by norm_num)
theorem B2476669 : Blo 1466553 2476669 := bbase (se 3 (by rfl) ⟨464375, by rfl⟩ : syracuseStep 2476669 = 928751) (by norm_num)
theorem B3304061 : Blo 1466553 3304061 := bbase (se 3 (by rfl) ⟨619511, by rfl⟩ : syracuseStep 3304061 = 1239023) (by norm_num)
theorem B3525277 : Blo 1466553 3525277 := bbase (se 3 (by rfl) ⟨660989, by rfl⟩ : syracuseStep 3525277 = 1321979) (by norm_num)
theorem B3304133 : Blo 1466553 3304133 := bbase (se 4 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 3304133 = 619525) (by norm_num)
theorem B2476757 : Blo 1466553 2476757 := bbase (se 7 (by rfl) ⟨29024, by rfl⟩ : syracuseStep 2476757 = 58049) (by norm_num)
theorem B4950773 : Blo 1466553 4950773 := bbase (se 5 (by rfl) ⟨232067, by rfl⟩ : syracuseStep 4950773 = 464135) (by norm_num)
theorem B3713789 : Blo 1466553 3713789 := bbase (se 3 (by rfl) ⟨696335, by rfl⟩ : syracuseStep 3713789 = 1392671) (by norm_num)
theorem B3304205 : Blo 1466553 3304205 := bbase (se 3 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 3304205 = 1239077) (by norm_num)
theorem B3132229 : Blo 1466553 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B4180805 : Blo 1466553 4180805 := bbase (se 4 (by rfl) ⟨391950, by rfl⟩ : syracuseStep 4180805 = 783901) (by norm_num)
theorem B2476885 : Blo 1466553 2476885 := bbase (se 9 (by rfl) ⟨7256, by rfl⟩ : syracuseStep 2476885 = 14513) (by norm_num)
theorem B7433045 : Blo 1466553 7433045 := bbase (se 9 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 7433045 = 43553) (by norm_num)
theorem B3345293 : Blo 1466553 3345293 := bbase (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) (by norm_num)
theorem B2476973 : Blo 1466553 2476973 := bbase (se 3 (by rfl) ⟨464432, by rfl⟩ : syracuseStep 2476973 = 928865) (by norm_num)
theorem B6351797 : Blo 1466553 6351797 := bbase (se 5 (by rfl) ⟨297740, by rfl⟩ : syracuseStep 6351797 = 595481) (by norm_num)
theorem B7056341 : Blo 1466553 7056341 := bbase (se 7 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 7056341 = 165383) (by norm_num)
theorem B3574757 : Blo 1466553 3574757 := bbase (se 4 (by rfl) ⟨335133, by rfl⟩ : syracuseStep 3574757 = 670267) (by norm_num)
theorem B4180997 : Blo 1466553 4180997 := bbase (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) (by norm_num)
theorem B2477101 : Blo 1466553 2477101 := bbase (se 3 (by rfl) ⟨464456, by rfl⟩ : syracuseStep 2477101 = 928913) (by norm_num)
theorem B3714133 : Blo 1466553 3714133 := bbase (se 8 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 3714133 = 43525) (by norm_num)
theorem B1674361 : Blo 1466553 1674361 := bbase (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) (by norm_num)
theorem B2477189 : Blo 1466553 2477189 := bbase (se 4 (by rfl) ⟨232236, by rfl⟩ : syracuseStep 2477189 = 464473) (by norm_num)
theorem B4951205 : Blo 1466553 4951205 := bbase (se 4 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 4951205 = 928351) (by norm_num)
theorem B3714245 : Blo 1466553 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B1649893 : Blo 1466553 1649893 := bbase (se 4 (by rfl) ⟨154677, by rfl⟩ : syracuseStep 1649893 = 309355) (by norm_num)
theorem B7425269 : Blo 1466553 7425269 := bbase (se 5 (by rfl) ⟨348059, by rfl⟩ : syracuseStep 7425269 = 696119) (by norm_num)
theorem B3525893 : Blo 1466553 3525893 := bbase (se 4 (by rfl) ⟨330552, by rfl⟩ : syracuseStep 3525893 = 661105) (by norm_num)
theorem B2477317 : Blo 1466553 2477317 := bbase (se 4 (by rfl) ⟨232248, by rfl⟩ : syracuseStep 2477317 = 464497) (by norm_num)
theorem B1649929 : Blo 1466553 1649929 := bbase (se 2 (by rfl) ⟨618723, by rfl⟩ : syracuseStep 1649929 = 1237447) (by norm_num)
theorem B1649965 : Blo 1466553 1649965 := bbase (se 3 (by rfl) ⟨309368, by rfl⟩ : syracuseStep 1649965 = 618737) (by norm_num)
theorem B1568045 : Blo 1466553 1568045 := bbase (se 3 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 1568045 = 588017) (by norm_num)
theorem B1650001 : Blo 1466553 1650001 := bbase (se 2 (by rfl) ⟨618750, by rfl⟩ : syracuseStep 1650001 = 1237501) (by norm_num)
theorem B2477405 : Blo 1466553 2477405 := bbase (se 3 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 2477405 = 929027) (by norm_num)
theorem B1650037 : Blo 1466553 1650037 := bbase (se 5 (by rfl) ⟨77345, by rfl⟩ : syracuseStep 1650037 = 154691) (by norm_num)
theorem B3714437 : Blo 1466553 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B1650073 : Blo 1466553 1650073 := bbase (se 2 (by rfl) ⟨618777, by rfl⟩ : syracuseStep 1650073 = 1237555) (by norm_num)
theorem B1650109 : Blo 1466553 1650109 := bbase (se 3 (by rfl) ⟨309395, by rfl⟩ : syracuseStep 1650109 = 618791) (by norm_num)
theorem B2477533 : Blo 1466553 2477533 := bbase (se 3 (by rfl) ⟨464537, by rfl⟩ : syracuseStep 2477533 = 929075) (by norm_num)
theorem B1650145 : Blo 1466553 1650145 := bbase (se 2 (by rfl) ⟨618804, by rfl⟩ : syracuseStep 1650145 = 1237609) (by norm_num)
theorem B1650181 : Blo 1466553 1650181 := bbase (se 4 (by rfl) ⟨154704, by rfl⟩ : syracuseStep 1650181 = 309409) (by norm_num)
theorem B1650217 : Blo 1466553 1650217 := bbase (se 2 (by rfl) ⟨618831, by rfl⟩ : syracuseStep 1650217 = 1237663) (by norm_num)
theorem B2477621 : Blo 1466553 2477621 := bbase (se 5 (by rfl) ⟨116138, by rfl⟩ : syracuseStep 2477621 = 232277) (by norm_num)
theorem B1650253 : Blo 1466553 1650253 := bbase (se 3 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 1650253 = 618845) (by norm_num)
theorem B3264077 : Blo 1466553 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B4951637 : Blo 1466553 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B1650289 : Blo 1466553 1650289 := bbase (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) (by norm_num)
theorem B16707221 : Blo 1466553 16707221 := bbase (se 6 (by rfl) ⟨391575, by rfl⟩ : syracuseStep 16707221 = 783151) (by norm_num)
theorem B1650325 : Blo 1466553 1650325 := bbase (se 6 (by rfl) ⟨38679, by rfl⟩ : syracuseStep 1650325 = 77359) (by norm_num)
theorem B3526325 : Blo 1466553 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B2477749 : Blo 1466553 2477749 := bbase (se 5 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 2477749 = 232289) (by norm_num)
theorem B1650361 : Blo 1466553 1650361 := bbase (se 2 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 1650361 = 1237771) (by norm_num)
theorem B3133117 : Blo 1466553 3133117 := bbase (se 3 (by rfl) ⟨587459, by rfl⟩ : syracuseStep 3133117 = 1174919) (by norm_num)
theorem B1650397 : Blo 1466553 1650397 := bbase (se 3 (by rfl) ⟨309449, by rfl⟩ : syracuseStep 1650397 = 618899) (by norm_num)
theorem B3714781 : Blo 1466553 3714781 := bbase (se 3 (by rfl) ⟨696521, by rfl⟩ : syracuseStep 3714781 = 1393043) (by norm_num)
theorem B1650433 : Blo 1466553 1650433 := bbase (se 2 (by rfl) ⟨618912, by rfl⟩ : syracuseStep 1650433 = 1237825) (by norm_num)
theorem B2477837 : Blo 1466553 2477837 := bbase (se 3 (by rfl) ⟨464594, by rfl⟩ : syracuseStep 2477837 = 929189) (by norm_num)
theorem B1650469 : Blo 1466553 1650469 := bbase (se 4 (by rfl) ⟨154731, by rfl⟩ : syracuseStep 1650469 = 309463) (by norm_num)
theorem B3133237 : Blo 1466553 3133237 := bbase (se 5 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 3133237 = 293741) (by norm_num)
theorem B1650505 : Blo 1466553 1650505 := bbase (se 2 (by rfl) ⟨618939, by rfl⟩ : syracuseStep 1650505 = 1237879) (by norm_num)
theorem B3714893 : Blo 1466553 3714893 := bbase (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) (by norm_num)
theorem B1650541 : Blo 1466553 1650541 := bbase (se 3 (by rfl) ⟨309476, by rfl⟩ : syracuseStep 1650541 = 618953) (by norm_num)
theorem B6352757 : Blo 1466553 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B2477965 : Blo 1466553 2477965 := bbase (se 3 (by rfl) ⟨464618, by rfl⟩ : syracuseStep 2477965 = 929237) (by norm_num)
theorem B1650577 : Blo 1466553 1650577 := bbase (se 2 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 1650577 = 1237933) (by norm_num)
theorem B1650613 : Blo 1466553 1650613 := bbase (se 5 (by rfl) ⟨77372, by rfl⟩ : syracuseStep 1650613 = 154745) (by norm_num)
theorem B1486793 : Blo 1466553 1486793 := bbase (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) (by norm_num)
theorem B1650649 : Blo 1466553 1650649 := bbase (se 2 (by rfl) ⟨618993, by rfl⟩ : syracuseStep 1650649 = 1237987) (by norm_num)
theorem B6270949 : Blo 1466553 6270949 := bbase (se 4 (by rfl) ⟨587901, by rfl⟩ : syracuseStep 6270949 = 1175803) (by norm_num)
theorem B2478053 : Blo 1466553 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B1650685 : Blo 1466553 1650685 := bbase (se 3 (by rfl) ⟨309503, by rfl⟩ : syracuseStep 1650685 = 619007) (by norm_num)
theorem B4952069 : Blo 1466553 4952069 := bbase (se 4 (by rfl) ⟨464256, by rfl⟩ : syracuseStep 4952069 = 928513) (by norm_num)
theorem B3715085 : Blo 1466553 3715085 := bbase (se 3 (by rfl) ⟨696578, by rfl⟩ : syracuseStep 3715085 = 1393157) (by norm_num)
theorem B1650721 : Blo 1466553 1650721 := bbase (se 2 (by rfl) ⟨619020, by rfl⟩ : syracuseStep 1650721 = 1238041) (by norm_num)
theorem B3133493 : Blo 1466553 3133493 := bbase (se 5 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 3133493 = 293765) (by norm_num)
theorem B2715709 : Blo 1466553 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B1650757 : Blo 1466553 1650757 := bbase (se 4 (by rfl) ⟨154758, by rfl⟩ : syracuseStep 1650757 = 309517) (by norm_num)
theorem B2822221 : Blo 1466553 2822221 := bbase (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) (by norm_num)
theorem B7434341 : Blo 1466553 7434341 := bbase (se 4 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 7434341 = 1393939) (by norm_num)
theorem B2478181 : Blo 1466553 2478181 := bbase (se 4 (by rfl) ⟨232329, by rfl⟩ : syracuseStep 2478181 = 464659) (by norm_num)
theorem B1650793 : Blo 1466553 1650793 := bbase (se 2 (by rfl) ⟨619047, by rfl⟩ : syracuseStep 1650793 = 1238095) (by norm_num)
theorem B7245941 : Blo 1466553 7245941 := bbase (se 5 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 7245941 = 679307) (by norm_num)
theorem B3764357 : Blo 1466553 3764357 := bbase (se 4 (by rfl) ⟨352908, by rfl⟩ : syracuseStep 3764357 = 705817) (by norm_num)
theorem B1650829 : Blo 1466553 1650829 := bbase (se 3 (by rfl) ⟨309530, by rfl⟩ : syracuseStep 1650829 = 619061) (by norm_num)
theorem B1650865 : Blo 1466553 1650865 := bbase (se 2 (by rfl) ⟨619074, by rfl⟩ : syracuseStep 1650865 = 1238149) (by norm_num)
theorem B1650901 : Blo 1466553 1650901 := bbase (se 7 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 1650901 = 38693) (by norm_num)
theorem B1650937 : Blo 1466553 1650937 := bbase (se 2 (by rfl) ⟨619101, by rfl⟩ : syracuseStep 1650937 = 1238203) (by norm_num)
theorem B1650973 : Blo 1466553 1650973 := bbase (se 3 (by rfl) ⟨309557, by rfl⟩ : syracuseStep 1650973 = 619115) (by norm_num)
theorem B2199845 : Blo 1466553 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B2199869 : Blo 1466553 2199869 := bbase (se 3 (by rfl) ⟨412475, by rfl⟩ : syracuseStep 2199869 = 824951) (by norm_num)
theorem B1651009 : Blo 1466553 1651009 := bbase (se 2 (by rfl) ⟨619128, by rfl⟩ : syracuseStep 1651009 = 1238257) (by norm_num)
theorem B2199893 : Blo 1466553 2199893 := bbase (se 10 (by rfl) ⟨3222, by rfl⟩ : syracuseStep 2199893 = 6445) (by norm_num)
theorem B1651045 : Blo 1466553 1651045 := bbase (se 4 (by rfl) ⟨154785, by rfl⟩ : syracuseStep 1651045 = 309571) (by norm_num)
theorem B3715429 : Blo 1466553 3715429 := bbase (se 4 (by rfl) ⟨348321, by rfl⟩ : syracuseStep 3715429 = 696643) (by norm_num)
theorem B5575013 : Blo 1466553 5575013 := bbase (se 4 (by rfl) ⟨522657, by rfl⟩ : syracuseStep 5575013 = 1045315) (by norm_num)
theorem B2199917 : Blo 1466553 2199917 := bbase (se 3 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 2199917 = 824969) (by norm_num)
theorem B2199941 : Blo 1466553 2199941 := bbase (se 4 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 2199941 = 412489) (by norm_num)
theorem B1651081 : Blo 1466553 1651081 := bbase (se 2 (by rfl) ⟨619155, by rfl⟩ : syracuseStep 1651081 = 1238311) (by norm_num)
theorem B2199965 : Blo 1466553 2199965 := bbase (se 3 (by rfl) ⟨412493, by rfl⟩ : syracuseStep 2199965 = 824987) (by norm_num)
theorem B1651117 : Blo 1466553 1651117 := bbase (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) (by norm_num)
theorem B2199989 : Blo 1466553 2199989 := bbase (se 5 (by rfl) ⟨103124, by rfl⟩ : syracuseStep 2199989 = 206249) (by norm_num)
theorem B4952501 : Blo 1466553 4952501 := bbase (se 5 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 4952501 = 464297) (by norm_num)
theorem B2200013 : Blo 1466553 2200013 := bbase (se 3 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 2200013 = 825005) (by norm_num)
theorem B1651153 : Blo 1466553 1651153 := bbase (se 2 (by rfl) ⟨619182, by rfl⟩ : syracuseStep 1651153 = 1238365) (by norm_num)
theorem B3715541 : Blo 1466553 3715541 := bbase (se 7 (by rfl) ⟨43541, by rfl⟩ : syracuseStep 3715541 = 87083) (by norm_num)
theorem B2200037 : Blo 1466553 2200037 := bbase (se 4 (by rfl) ⟨206253, by rfl⟩ : syracuseStep 2200037 = 412507) (by norm_num)
theorem B1651189 : Blo 1466553 1651189 := bbase (se 5 (by rfl) ⟨77399, by rfl⟩ : syracuseStep 1651189 = 154799) (by norm_num)
theorem B2200061 : Blo 1466553 2200061 := bbase (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) (by norm_num)
theorem B7426565 : Blo 1466553 7426565 := bbase (se 4 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 7426565 = 1392481) (by norm_num)
theorem B2200085 : Blo 1466553 2200085 := bbase (se 6 (by rfl) ⟨51564, by rfl⟩ : syracuseStep 2200085 = 103129) (by norm_num)
theorem B1651225 : Blo 1466553 1651225 := bbase (se 2 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 1651225 = 1238419) (by norm_num)
theorem B2200109 : Blo 1466553 2200109 := bbase (se 3 (by rfl) ⟨412520, by rfl⟩ : syracuseStep 2200109 = 825041) (by norm_num)
theorem B1651261 : Blo 1466553 1651261 := bbase (se 3 (by rfl) ⟨309611, by rfl⟩ : syracuseStep 1651261 = 619223) (by norm_num)
theorem B2200133 : Blo 1466553 2200133 := bbase (se 4 (by rfl) ⟨206262, by rfl⟩ : syracuseStep 2200133 = 412525) (by norm_num)
theorem B2200157 : Blo 1466553 2200157 := bbase (se 3 (by rfl) ⟨412529, by rfl⟩ : syracuseStep 2200157 = 825059) (by norm_num)
theorem B1651297 : Blo 1466553 1651297 := bbase (se 2 (by rfl) ⟨619236, by rfl⟩ : syracuseStep 1651297 = 1238473) (by norm_num)
theorem B5018213 : Blo 1466553 5018213 := bbase (se 4 (by rfl) ⟨470457, by rfl⟩ : syracuseStep 5018213 = 940915) (by norm_num)
theorem B3347045 : Blo 1466553 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B2200181 : Blo 1466553 2200181 := bbase (se 5 (by rfl) ⟨103133, by rfl⟩ : syracuseStep 2200181 = 206267) (by norm_num)
theorem B1856125 : Blo 1466553 1856125 := bbase (se 3 (by rfl) ⟨348023, by rfl⟩ : syracuseStep 1856125 = 696047) (by norm_num)
theorem B1651333 : Blo 1466553 1651333 := bbase (se 4 (by rfl) ⟨154812, by rfl⟩ : syracuseStep 1651333 = 309625) (by norm_num)
theorem B5575301 : Blo 1466553 5575301 := bbase (se 4 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 5575301 = 1045369) (by norm_num)
theorem B2200205 : Blo 1466553 2200205 := bbase (se 3 (by rfl) ⟨412538, by rfl⟩ : syracuseStep 2200205 = 825077) (by norm_num)
theorem B3715733 : Blo 1466553 3715733 := bbase (se 6 (by rfl) ⟨87087, by rfl⟩ : syracuseStep 3715733 = 174175) (by norm_num)
theorem B5952149 : Blo 1466553 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B2200229 : Blo 1466553 2200229 := bbase (se 4 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 2200229 = 412543) (by norm_num)
theorem B1651369 : Blo 1466553 1651369 := bbase (se 2 (by rfl) ⟨619263, by rfl⟩ : syracuseStep 1651369 = 1238527) (by norm_num)
theorem B2200253 : Blo 1466553 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B3764933 : Blo 1466553 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B1651405 : Blo 1466553 1651405 := bbase (se 3 (by rfl) ⟨309638, by rfl⟩ : syracuseStep 1651405 = 619277) (by norm_num)
theorem B2200277 : Blo 1466553 2200277 := bbase (se 7 (by rfl) ⟨25784, by rfl⟩ : syracuseStep 2200277 = 51569) (by norm_num)
theorem B2200301 : Blo 1466553 2200301 := bbase (se 3 (by rfl) ⟨412556, by rfl⟩ : syracuseStep 2200301 = 825113) (by norm_num)
theorem B1651441 : Blo 1466553 1651441 := bbase (se 2 (by rfl) ⟨619290, by rfl⟩ : syracuseStep 1651441 = 1238581) (by norm_num)
theorem B2200325 : Blo 1466553 2200325 := bbase (se 4 (by rfl) ⟨206280, by rfl⟩ : syracuseStep 2200325 = 412561) (by norm_num)
theorem B1651477 : Blo 1466553 1651477 := bbase (se 6 (by rfl) ⟨38706, by rfl⟩ : syracuseStep 1651477 = 77413) (by norm_num)
theorem B2200349 : Blo 1466553 2200349 := bbase (se 3 (by rfl) ⟨412565, by rfl⟩ : syracuseStep 2200349 = 825131) (by norm_num)
theorem B1856297 : Blo 1466553 1856297 := bbase (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) (by norm_num)
theorem B2200373 : Blo 1466553 2200373 := bbase (se 5 (by rfl) ⟨103142, by rfl⟩ : syracuseStep 2200373 = 206285) (by norm_num)
theorem B1651513 : Blo 1466553 1651513 := bbase (se 2 (by rfl) ⟨619317, by rfl⟩ : syracuseStep 1651513 = 1238635) (by norm_num)
theorem B2200397 : Blo 1466553 2200397 := bbase (se 3 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 2200397 = 825149) (by norm_num)
theorem B3765085 : Blo 1466553 3765085 := bbase (se 3 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 3765085 = 1411907) (by norm_num)
theorem B1651549 : Blo 1466553 1651549 := bbase (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) (by norm_num)
theorem B1856353 : Blo 1466553 1856353 := bbase (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) (by norm_num)
theorem B2200421 : Blo 1466553 2200421 := bbase (se 4 (by rfl) ⟨206289, by rfl⟩ : syracuseStep 2200421 = 412579) (by norm_num)
theorem B4952933 : Blo 1466553 4952933 := bbase (se 4 (by rfl) ⟨464337, by rfl⟩ : syracuseStep 4952933 = 928675) (by norm_num)
theorem B3527525 : Blo 1466553 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B1487737 : Blo 1466553 1487737 := bbase (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) (by norm_num)
theorem B2200445 : Blo 1466553 2200445 := bbase (se 3 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 2200445 = 825167) (by norm_num)
theorem B1651585 : Blo 1466553 1651585 := bbase (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) (by norm_num)
theorem B2200469 : Blo 1466553 2200469 := bbase (se 6 (by rfl) ⟨51573, by rfl⟩ : syracuseStep 2200469 = 103147) (by norm_num)
theorem B1651621 : Blo 1466553 1651621 := bbase (se 4 (by rfl) ⟨154839, by rfl⟩ : syracuseStep 1651621 = 309679) (by norm_num)
theorem B2200493 : Blo 1466553 2200493 := bbase (se 3 (by rfl) ⟨412592, by rfl⟩ : syracuseStep 2200493 = 825185) (by norm_num)
theorem B3134381 : Blo 1466553 3134381 := bbase (se 3 (by rfl) ⟨587696, by rfl⟩ : syracuseStep 3134381 = 1175393) (by norm_num)
theorem B1856449 : Blo 1466553 1856449 := bbase (se 2 (by rfl) ⟨696168, by rfl⟩ : syracuseStep 1856449 = 1392337) (by norm_num)
theorem B2200517 : Blo 1466553 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B1651657 : Blo 1466553 1651657 := bbase (se 2 (by rfl) ⟨619371, by rfl⟩ : syracuseStep 1651657 = 1238743) (by norm_num)
theorem B2200541 : Blo 1466553 2200541 := bbase (se 3 (by rfl) ⟨412601, by rfl⟩ : syracuseStep 2200541 = 825203) (by norm_num)
theorem B3716077 : Blo 1466553 3716077 := bbase (se 3 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 3716077 = 1393529) (by norm_num)
theorem B1651693 : Blo 1466553 1651693 := bbase (se 3 (by rfl) ⟨309692, by rfl⟩ : syracuseStep 1651693 = 619385) (by norm_num)
theorem B2200565 : Blo 1466553 2200565 := bbase (se 5 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 2200565 = 206303) (by norm_num)
theorem B2200589 : Blo 1466553 2200589 := bbase (se 3 (by rfl) ⟨412610, by rfl⟩ : syracuseStep 2200589 = 825221) (by norm_num)
theorem B1651729 : Blo 1466553 1651729 := bbase (se 2 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 1651729 = 1238797) (by norm_num)
theorem B2200613 : Blo 1466553 2200613 := bbase (se 4 (by rfl) ⟨206307, by rfl⟩ : syracuseStep 2200613 = 412615) (by norm_num)
theorem B1651765 : Blo 1466553 1651765 := bbase (se 5 (by rfl) ⟨77426, by rfl⟩ : syracuseStep 1651765 = 154853) (by norm_num)
theorem B2200637 : Blo 1466553 2200637 := bbase (se 3 (by rfl) ⟨412619, by rfl⟩ : syracuseStep 2200637 = 825239) (by norm_num)
theorem B2200661 : Blo 1466553 2200661 := bbase (se 8 (by rfl) ⟨12894, by rfl⟩ : syracuseStep 2200661 = 25789) (by norm_num)
theorem B1651801 : Blo 1466553 1651801 := bbase (se 2 (by rfl) ⟨619425, by rfl⟩ : syracuseStep 1651801 = 1238851) (by norm_num)
theorem B3716189 : Blo 1466553 3716189 := bbase (se 3 (by rfl) ⟨696785, by rfl⟩ : syracuseStep 3716189 = 1393571) (by norm_num)
theorem B7050341 : Blo 1466553 7050341 := bbase (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) (by norm_num)
theorem B1856621 : Blo 1466553 1856621 := bbase (se 3 (by rfl) ⟨348116, by rfl⟩ : syracuseStep 1856621 = 696233) (by norm_num)
theorem B2200685 : Blo 1466553 2200685 := bbase (se 3 (by rfl) ⟨412628, by rfl⟩ : syracuseStep 2200685 = 825257) (by norm_num)
theorem B1651837 : Blo 1466553 1651837 := bbase (se 3 (by rfl) ⟨309719, by rfl⟩ : syracuseStep 1651837 = 619439) (by norm_num)
theorem B2200709 : Blo 1466553 2200709 := bbase (se 4 (by rfl) ⟨206316, by rfl⟩ : syracuseStep 2200709 = 412633) (by norm_num)
theorem B2200733 : Blo 1466553 2200733 := bbase (se 3 (by rfl) ⟨412637, by rfl⟩ : syracuseStep 2200733 = 825275) (by norm_num)
theorem B3134621 : Blo 1466553 3134621 := bbase (se 3 (by rfl) ⟨587741, by rfl⟩ : syracuseStep 3134621 = 1175483) (by norm_num)
theorem B1651873 : Blo 1466553 1651873 := bbase (se 2 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 1651873 = 1238905) (by norm_num)
theorem B1856677 : Blo 1466553 1856677 := bbase (se 4 (by rfl) ⟨174063, by rfl⟩ : syracuseStep 1856677 = 348127) (by norm_num)
theorem B2200757 : Blo 1466553 2200757 := bbase (se 5 (by rfl) ⟨103160, by rfl⟩ : syracuseStep 2200757 = 206321) (by norm_num)
theorem B1651909 : Blo 1466553 1651909 := bbase (se 4 (by rfl) ⟨154866, by rfl⟩ : syracuseStep 1651909 = 309733) (by norm_num)
theorem B2200781 : Blo 1466553 2200781 := bbase (se 3 (by rfl) ⟨412646, by rfl⟩ : syracuseStep 2200781 = 825293) (by norm_num)
theorem B2200805 : Blo 1466553 2200805 := bbase (se 4 (by rfl) ⟨206325, by rfl⟩ : syracuseStep 2200805 = 412651) (by norm_num)
theorem B1651945 : Blo 1466553 1651945 := bbase (se 2 (by rfl) ⟨619479, by rfl⟩ : syracuseStep 1651945 = 1238959) (by norm_num)
theorem B2200829 : Blo 1466553 2200829 := bbase (se 3 (by rfl) ⟨412655, by rfl⟩ : syracuseStep 2200829 = 825311) (by norm_num)
theorem B1856773 : Blo 1466553 1856773 := bbase (se 4 (by rfl) ⟨174072, by rfl⟩ : syracuseStep 1856773 = 348145) (by norm_num)
theorem B1651981 : Blo 1466553 1651981 := bbase (se 3 (by rfl) ⟨309746, by rfl⟩ : syracuseStep 1651981 = 619493) (by norm_num)
theorem B2200853 : Blo 1466553 2200853 := bbase (se 6 (by rfl) ⟨51582, by rfl⟩ : syracuseStep 2200853 = 103165) (by norm_num)
theorem B4953365 : Blo 1466553 4953365 := bbase (se 6 (by rfl) ⟨116094, by rfl⟩ : syracuseStep 4953365 = 232189) (by norm_num)
theorem B3716381 : Blo 1466553 3716381 := bbase (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) (by norm_num)
theorem B2200877 : Blo 1466553 2200877 := bbase (se 3 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 2200877 = 825329) (by norm_num)
theorem B12711221 : Blo 1466553 12711221 := bbase (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) (by norm_num)
theorem B1652017 : Blo 1466553 1652017 := bbase (se 2 (by rfl) ⟨619506, by rfl⟩ : syracuseStep 1652017 = 1239013) (by norm_num)
theorem B3347773 : Blo 1466553 3347773 := bbase (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) (by norm_num)
theorem B2200901 : Blo 1466553 2200901 := bbase (se 4 (by rfl) ⟨206334, by rfl⟩ : syracuseStep 2200901 = 412669) (by norm_num)
theorem B1652053 : Blo 1466553 1652053 := bbase (se 13 (by rfl) ⟨302, by rfl⟩ : syracuseStep 1652053 = 605) (by norm_num)
theorem B2200925 : Blo 1466553 2200925 := bbase (se 3 (by rfl) ⟨412673, by rfl⟩ : syracuseStep 2200925 = 825347) (by norm_num)
theorem B2200949 : Blo 1466553 2200949 := bbase (se 5 (by rfl) ⟨103169, by rfl⟩ : syracuseStep 2200949 = 206339) (by norm_num)
theorem B1652089 : Blo 1466553 1652089 := bbase (se 2 (by rfl) ⟨619533, by rfl⟩ : syracuseStep 1652089 = 1239067) (by norm_num)
theorem B3765629 : Blo 1466553 3765629 := bbase (se 3 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 3765629 = 1412111) (by norm_num)
theorem B2200973 : Blo 1466553 2200973 := bbase (se 3 (by rfl) ⟨412682, by rfl⟩ : syracuseStep 2200973 = 825365) (by norm_num)
theorem B2200997 : Blo 1466553 2200997 := bbase (se 4 (by rfl) ⟨206343, by rfl⟩ : syracuseStep 2200997 = 412687) (by norm_num)
theorem B1881517 : Blo 1466553 1881517 := bbase (se 3 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 1881517 = 705569) (by norm_num)
theorem B1856945 : Blo 1466553 1856945 := bbase (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) (by norm_num)
theorem B1488305 : Blo 1466553 1488305 := bbase (se 2 (by rfl) ⟨558114, by rfl⟩ : syracuseStep 1488305 = 1116229) (by norm_num)
theorem B6272437 : Blo 1466553 6272437 := bbase (se 5 (by rfl) ⟨294020, by rfl⟩ : syracuseStep 6272437 = 588041) (by norm_num)
theorem B2201021 : Blo 1466553 2201021 := bbase (se 3 (by rfl) ⟨412691, by rfl⟩ : syracuseStep 2201021 = 825383) (by norm_num)
theorem B6272453 : Blo 1466553 6272453 := bbase (se 4 (by rfl) ⟨588042, by rfl⟩ : syracuseStep 6272453 = 1176085) (by norm_num)
theorem B2201045 : Blo 1466553 2201045 := bbase (se 7 (by rfl) ⟨25793, by rfl⟩ : syracuseStep 2201045 = 51587) (by norm_num)
theorem B1857001 : Blo 1466553 1857001 := bbase (se 2 (by rfl) ⟨696375, by rfl⟩ : syracuseStep 1857001 = 1392751) (by norm_num)
theorem B2201069 : Blo 1466553 2201069 := bbase (se 3 (by rfl) ⟨412700, by rfl⟩ : syracuseStep 2201069 = 825401) (by norm_num)
theorem B2201093 : Blo 1466553 2201093 := bbase (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) (by norm_num)
theorem B13391381 : Blo 1466553 13391381 := bbase (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) (by norm_num)
theorem B2201117 : Blo 1466553 2201117 := bbase (se 3 (by rfl) ⟨412709, by rfl⟩ : syracuseStep 2201117 = 825419) (by norm_num)
theorem B2201141 : Blo 1466553 2201141 := bbase (se 5 (by rfl) ⟨103178, by rfl⟩ : syracuseStep 2201141 = 206357) (by norm_num)
theorem B1857097 : Blo 1466553 1857097 := bbase (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) (by norm_num)
theorem B2643533 : Blo 1466553 2643533 := bbase (se 3 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 2643533 = 991325) (by norm_num)
theorem B2201165 : Blo 1466553 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B2201189 : Blo 1466553 2201189 := bbase (se 4 (by rfl) ⟨206361, by rfl⟩ : syracuseStep 2201189 = 412723) (by norm_num)
theorem B3716725 : Blo 1466553 3716725 := bbase (se 5 (by rfl) ⟨174221, by rfl⟩ : syracuseStep 3716725 = 348443) (by norm_num)
theorem B2201213 : Blo 1466553 2201213 := bbase (se 3 (by rfl) ⟨412727, by rfl⟩ : syracuseStep 2201213 = 825455) (by norm_num)
theorem B2201237 : Blo 1466553 2201237 := bbase (se 6 (by rfl) ⟨51591, by rfl⟩ : syracuseStep 2201237 = 103183) (by norm_num)
theorem B3135125 : Blo 1466553 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B3135133 : Blo 1466553 3135133 := bbase (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) (by norm_num)
theorem B2201261 : Blo 1466553 2201261 := bbase (se 3 (by rfl) ⟨412736, by rfl⟩ : syracuseStep 2201261 = 825473) (by norm_num)
theorem B4699829 : Blo 1466553 4699829 := bbase (se 5 (by rfl) ⟨220304, by rfl⟩ : syracuseStep 4699829 = 440609) (by norm_num)
theorem B2201285 : Blo 1466553 2201285 := bbase (se 4 (by rfl) ⟨206370, by rfl⟩ : syracuseStep 2201285 = 412741) (by norm_num)
theorem B4953797 : Blo 1466553 4953797 := bbase (se 4 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 4953797 = 928837) (by norm_num)
theorem B2201309 : Blo 1466553 2201309 := bbase (se 3 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 2201309 = 825491) (by norm_num)
theorem B3716837 : Blo 1466553 3716837 := bbase (se 4 (by rfl) ⟨348453, by rfl⟩ : syracuseStep 3716837 = 696907) (by norm_num)
theorem B1857269 : Blo 1466553 1857269 := bbase (se 5 (by rfl) ⟨87059, by rfl⟩ : syracuseStep 1857269 = 174119) (by norm_num)
theorem B2201333 : Blo 1466553 2201333 := bbase (se 5 (by rfl) ⟨103187, by rfl⟩ : syracuseStep 2201333 = 206375) (by norm_num)
theorem B2201357 : Blo 1466553 2201357 := bbase (se 3 (by rfl) ⟨412754, by rfl⟩ : syracuseStep 2201357 = 825509) (by norm_num)
theorem B7427861 : Blo 1466553 7427861 := bbase (se 6 (by rfl) ⟨174090, by rfl⟩ : syracuseStep 7427861 = 348181) (by norm_num)
theorem B2201381 : Blo 1466553 2201381 := bbase (se 4 (by rfl) ⟨206379, by rfl⟩ : syracuseStep 2201381 = 412759) (by norm_num)
theorem B1857325 : Blo 1466553 1857325 := bbase (se 3 (by rfl) ⟨348248, by rfl⟩ : syracuseStep 1857325 = 696497) (by norm_num)
theorem B2201405 : Blo 1466553 2201405 := bbase (se 3 (by rfl) ⟨412763, by rfl⟩ : syracuseStep 2201405 = 825527) (by norm_num)
theorem B2201429 : Blo 1466553 2201429 := bbase (se 9 (by rfl) ⟨6449, by rfl⟩ : syracuseStep 2201429 = 12899) (by norm_num)
theorem B2201453 : Blo 1466553 2201453 := bbase (se 3 (by rfl) ⟨412772, by rfl⟩ : syracuseStep 2201453 = 825545) (by norm_num)
theorem B2201477 : Blo 1466553 2201477 := bbase (se 4 (by rfl) ⟨206388, by rfl⟩ : syracuseStep 2201477 = 412777) (by norm_num)
theorem B1857421 : Blo 1466553 1857421 := bbase (se 3 (by rfl) ⟨348266, by rfl⟩ : syracuseStep 1857421 = 696533) (by norm_num)
theorem B2201501 : Blo 1466553 2201501 := bbase (se 3 (by rfl) ⟨412781, by rfl⟩ : syracuseStep 2201501 = 825563) (by norm_num)
theorem B3717029 : Blo 1466553 3717029 := bbase (se 4 (by rfl) ⟨348471, by rfl⟩ : syracuseStep 3717029 = 696943) (by norm_num)
theorem B2201525 : Blo 1466553 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B2201549 : Blo 1466553 2201549 := bbase (se 3 (by rfl) ⟨412790, by rfl⟩ : syracuseStep 2201549 = 825581) (by norm_num)
theorem B2578405 : Blo 1466553 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B2201573 : Blo 1466553 2201573 := bbase (se 4 (by rfl) ⟨206397, by rfl⟩ : syracuseStep 2201573 = 412795) (by norm_num)
theorem B2201597 : Blo 1466553 2201597 := bbase (se 3 (by rfl) ⟨412799, by rfl⟩ : syracuseStep 2201597 = 825599) (by norm_num)
theorem B2201621 : Blo 1466553 2201621 := bbase (se 6 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 2201621 = 103201) (by norm_num)
theorem B2201645 : Blo 1466553 2201645 := bbase (se 3 (by rfl) ⟨412808, by rfl⟩ : syracuseStep 2201645 = 825617) (by norm_num)
theorem B1857593 : Blo 1466553 1857593 := bbase (se 2 (by rfl) ⟨696597, by rfl⟩ : syracuseStep 1857593 = 1393195) (by norm_num)
theorem B2201669 : Blo 1466553 2201669 := bbase (se 4 (by rfl) ⟨206406, by rfl⟩ : syracuseStep 2201669 = 412813) (by norm_num)
theorem B2201693 : Blo 1466553 2201693 := bbase (se 3 (by rfl) ⟨412817, by rfl⟩ : syracuseStep 2201693 = 825635) (by norm_num)
theorem B1857649 : Blo 1466553 1857649 := bbase (se 2 (by rfl) ⟨696618, by rfl⟩ : syracuseStep 1857649 = 1393237) (by norm_num)
theorem B2201717 : Blo 1466553 2201717 := bbase (se 5 (by rfl) ⟨103205, by rfl⟩ : syracuseStep 2201717 = 206411) (by norm_num)
theorem B4954229 : Blo 1466553 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B11147381 : Blo 1466553 11147381 := bbase (se 5 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 11147381 = 1045067) (by norm_num)
theorem B2201741 : Blo 1466553 2201741 := bbase (se 3 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 2201741 = 825653) (by norm_num)
theorem B1882261 : Blo 1466553 1882261 := bbase (se 6 (by rfl) ⟨44115, by rfl⟩ : syracuseStep 1882261 = 88231) (by norm_num)
theorem B2201765 : Blo 1466553 2201765 := bbase (se 4 (by rfl) ⟨206415, by rfl⟩ : syracuseStep 2201765 = 412831) (by norm_num)
theorem B2201789 : Blo 1466553 2201789 := bbase (se 3 (by rfl) ⟨412835, by rfl⟩ : syracuseStep 2201789 = 825671) (by norm_num)
theorem B5568709 : Blo 1466553 5568709 := bbase (se 4 (by rfl) ⟨522066, by rfl⟩ : syracuseStep 5568709 = 1044133) (by norm_num)
theorem B1857745 : Blo 1466553 1857745 := bbase (se 2 (by rfl) ⟨696654, by rfl⟩ : syracuseStep 1857745 = 1393309) (by norm_num)
theorem B9402581 : Blo 1466553 9402581 := bbase (se 7 (by rfl) ⟨110186, by rfl⟩ : syracuseStep 9402581 = 220373) (by norm_num)
theorem B2201813 : Blo 1466553 2201813 := bbase (se 7 (by rfl) ⟨25802, by rfl⟩ : syracuseStep 2201813 = 51605) (by norm_num)
theorem B2201837 : Blo 1466553 2201837 := bbase (se 3 (by rfl) ⟨412844, by rfl⟩ : syracuseStep 2201837 = 825689) (by norm_num)
theorem B2201861 : Blo 1466553 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B2201885 : Blo 1466553 2201885 := bbase (se 3 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 2201885 = 825707) (by norm_num)
theorem B2201909 : Blo 1466553 2201909 := bbase (se 5 (by rfl) ⟨103214, by rfl⟩ : syracuseStep 2201909 = 206429) (by norm_num)
theorem B2201933 : Blo 1466553 2201933 := bbase (se 3 (by rfl) ⟨412862, by rfl⟩ : syracuseStep 2201933 = 825725) (by norm_num)
theorem B2201957 : Blo 1466553 2201957 := bbase (se 4 (by rfl) ⟨206433, by rfl⟩ : syracuseStep 2201957 = 412867) (by norm_num)
theorem B2546029 : Blo 1466553 2546029 := bbase (se 3 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 2546029 = 954761) (by norm_num)
theorem B1857917 : Blo 1466553 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B2201981 : Blo 1466553 2201981 := bbase (se 3 (by rfl) ⟨412871, by rfl⟩ : syracuseStep 2201981 = 825743) (by norm_num)
theorem B2202005 : Blo 1466553 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B2202029 : Blo 1466553 2202029 := bbase (se 3 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 2202029 = 825761) (by norm_num)
theorem B1857973 : Blo 1466553 1857973 := bbase (se 5 (by rfl) ⟨87092, by rfl⟩ : syracuseStep 1857973 = 174185) (by norm_num)
theorem B2202053 : Blo 1466553 2202053 := bbase (se 4 (by rfl) ⟨206442, by rfl⟩ : syracuseStep 2202053 = 412885) (by norm_num)
theorem B2202077 : Blo 1466553 2202077 := bbase (se 3 (by rfl) ⟨412889, by rfl⟩ : syracuseStep 2202077 = 825779) (by norm_num)
theorem B3299813 : Blo 1466553 3299813 := bbase (se 4 (by rfl) ⟨309357, by rfl⟩ : syracuseStep 3299813 = 618715) (by norm_num)
theorem B4176373 : Blo 1466553 4176373 := bbase (se 5 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 4176373 = 391535) (by norm_num)
theorem B5569013 : Blo 1466553 5569013 := bbase (se 5 (by rfl) ⟨261047, by rfl⟩ : syracuseStep 5569013 = 522095) (by norm_num)
theorem B2202101 : Blo 1466553 2202101 := bbase (se 5 (by rfl) ⟨103223, by rfl⟩ : syracuseStep 2202101 = 206447) (by norm_num)
theorem B2202125 : Blo 1466553 2202125 := bbase (se 3 (by rfl) ⟨412898, by rfl⟩ : syracuseStep 2202125 = 825797) (by norm_num)
theorem B11139605 : Blo 1466553 11139605 := bbase (se 6 (by rfl) ⟨261084, by rfl⟩ : syracuseStep 11139605 = 522169) (by norm_num)
theorem B1858069 : Blo 1466553 1858069 := bbase (se 6 (by rfl) ⟨43548, by rfl⟩ : syracuseStep 1858069 = 87097) (by norm_num)
theorem B4954661 : Blo 1466553 4954661 := bbase (se 4 (by rfl) ⟨464499, by rfl⟩ : syracuseStep 4954661 = 928999) (by norm_num)
theorem B2202149 : Blo 1466553 2202149 := bbase (se 4 (by rfl) ⟨206451, by rfl⟩ : syracuseStep 2202149 = 412903) (by norm_num)
theorem B3299885 : Blo 1466553 3299885 := bbase (se 3 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 3299885 = 1237457) (by norm_num)
theorem B11893301 : Blo 1466553 11893301 := bbase (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) (by norm_num)
theorem B2202173 : Blo 1466553 2202173 := bbase (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) (by norm_num)
theorem B2202197 : Blo 1466553 2202197 := bbase (se 8 (by rfl) ⟨12903, by rfl⟩ : syracuseStep 2202197 = 25807) (by norm_num)
theorem B2202221 : Blo 1466553 2202221 := bbase (se 3 (by rfl) ⟨412916, by rfl⟩ : syracuseStep 2202221 = 825833) (by norm_num)
theorem B3299957 : Blo 1466553 3299957 := bbase (se 5 (by rfl) ⟨154685, by rfl⟩ : syracuseStep 3299957 = 309371) (by norm_num)
theorem B4463237 : Blo 1466553 4463237 := bbase (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) (by norm_num)
theorem B2202245 : Blo 1466553 2202245 := bbase (se 4 (by rfl) ⟨206460, by rfl⟩ : syracuseStep 2202245 = 412921) (by norm_num)
theorem B2202269 : Blo 1466553 2202269 := bbase (se 3 (by rfl) ⟨412925, by rfl⟩ : syracuseStep 2202269 = 825851) (by norm_num)
theorem B2202293 : Blo 1466553 2202293 := bbase (se 5 (by rfl) ⟨103232, by rfl⟩ : syracuseStep 2202293 = 206465) (by norm_num)
theorem B3300029 : Blo 1466553 3300029 := bbase (se 3 (by rfl) ⟨618755, by rfl⟩ : syracuseStep 3300029 = 1237511) (by norm_num)
theorem B3349181 : Blo 1466553 3349181 := bbase (se 3 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 3349181 = 1255943) (by norm_num)
theorem B1858241 : Blo 1466553 1858241 := bbase (se 2 (by rfl) ⟨696840, by rfl⟩ : syracuseStep 1858241 = 1393681) (by norm_num)
theorem B2202317 : Blo 1466553 2202317 := bbase (se 3 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 2202317 = 825869) (by norm_num)
theorem B4463333 : Blo 1466553 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B2202341 : Blo 1466553 2202341 := bbase (se 4 (by rfl) ⟨206469, by rfl⟩ : syracuseStep 2202341 = 412939) (by norm_num)
theorem B1858297 : Blo 1466553 1858297 := bbase (se 2 (by rfl) ⟨696861, by rfl⟩ : syracuseStep 1858297 = 1393723) (by norm_num)
theorem B2202365 : Blo 1466553 2202365 := bbase (se 3 (by rfl) ⟨412943, by rfl⟩ : syracuseStep 2202365 = 825887) (by norm_num)
theorem B3300101 : Blo 1466553 3300101 := bbase (se 4 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 3300101 = 618769) (by norm_num)
theorem B5290757 : Blo 1466553 5290757 := bbase (se 4 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 5290757 = 992017) (by norm_num)
theorem B3136261 : Blo 1466553 3136261 := bbase (se 4 (by rfl) ⟨294024, by rfl⟩ : syracuseStep 3136261 = 588049) (by norm_num)
theorem B2202389 : Blo 1466553 2202389 := bbase (se 6 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 2202389 = 103237) (by norm_num)
theorem B2202413 : Blo 1466553 2202413 := bbase (se 3 (by rfl) ⟨412952, by rfl⟩ : syracuseStep 2202413 = 825905) (by norm_num)
theorem B15276853 : Blo 1466553 15276853 := bbase (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) (by norm_num)
theorem B2202437 : Blo 1466553 2202437 := bbase (se 4 (by rfl) ⟨206478, by rfl⟩ : syracuseStep 2202437 = 412957) (by norm_num)
theorem B3300173 : Blo 1466553 3300173 := bbase (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) (by norm_num)
theorem B1858393 : Blo 1466553 1858393 := bbase (se 2 (by rfl) ⟨696897, by rfl⟩ : syracuseStep 1858393 = 1393795) (by norm_num)
theorem B2202461 : Blo 1466553 2202461 := bbase (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) (by norm_num)
theorem B2202485 : Blo 1466553 2202485 := bbase (se 5 (by rfl) ⟨103241, by rfl⟩ : syracuseStep 2202485 = 206483) (by norm_num)
theorem B2202509 : Blo 1466553 2202509 := bbase (se 3 (by rfl) ⟨412970, by rfl⟩ : syracuseStep 2202509 = 825941) (by norm_num)
theorem B3300245 : Blo 1466553 3300245 := bbase (se 6 (by rfl) ⟨77349, by rfl⟩ : syracuseStep 3300245 = 154699) (by norm_num)
theorem B2202533 : Blo 1466553 2202533 := bbase (se 4 (by rfl) ⟨206487, by rfl⟩ : syracuseStep 2202533 = 412975) (by norm_num)
theorem B2202557 : Blo 1466553 2202557 := bbase (se 3 (by rfl) ⟨412979, by rfl⟩ : syracuseStep 2202557 = 825959) (by norm_num)
theorem B1883081 : Blo 1466553 1883081 := bbase (se 2 (by rfl) ⟨706155, by rfl⟩ : syracuseStep 1883081 = 1412311) (by norm_num)
theorem B4955093 : Blo 1466553 4955093 := bbase (se 7 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 4955093 = 116135) (by norm_num)
theorem B2202581 : Blo 1466553 2202581 := bbase (se 7 (by rfl) ⟨25811, by rfl⟩ : syracuseStep 2202581 = 51623) (by norm_num)
theorem B3300317 : Blo 1466553 3300317 := bbase (se 3 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 3300317 = 1237619) (by norm_num)
theorem B7527397 : Blo 1466553 7527397 := bbase (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) (by norm_num)
theorem B2202605 : Blo 1466553 2202605 := bbase (se 3 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 2202605 = 825977) (by norm_num)
theorem B8362997 : Blo 1466553 8362997 := bbase (se 5 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 8362997 = 784031) (by norm_num)
theorem B2202629 : Blo 1466553 2202629 := bbase (se 4 (by rfl) ⟨206496, by rfl⟩ : syracuseStep 2202629 = 412993) (by norm_num)
theorem B1858565 : Blo 1466553 1858565 := bbase (se 4 (by rfl) ⟨174240, by rfl⟩ : syracuseStep 1858565 = 348481) (by norm_num)
theorem B2202653 : Blo 1466553 2202653 := bbase (se 3 (by rfl) ⟨412997, by rfl⟩ : syracuseStep 2202653 = 825995) (by norm_num)
theorem B3300389 : Blo 1466553 3300389 := bbase (se 4 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 3300389 = 618823) (by norm_num)
theorem B7429157 : Blo 1466553 7429157 := bbase (se 4 (by rfl) ⟨696483, by rfl⟩ : syracuseStep 7429157 = 1392967) (by norm_num)
theorem B2202677 : Blo 1466553 2202677 := bbase (se 5 (by rfl) ⟨103250, by rfl⟩ : syracuseStep 2202677 = 206501) (by norm_num)
theorem B1858621 : Blo 1466553 1858621 := bbase (se 3 (by rfl) ⟨348491, by rfl⟩ : syracuseStep 1858621 = 696983) (by norm_num)
theorem B4701253 : Blo 1466553 4701253 := bbase (se 4 (by rfl) ⟨440742, by rfl⟩ : syracuseStep 4701253 = 881485) (by norm_num)
theorem B2825293 : Blo 1466553 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B2202701 : Blo 1466553 2202701 := bbase (se 3 (by rfl) ⟨413006, by rfl⟩ : syracuseStep 2202701 = 826013) (by norm_num)
theorem B28220501 : Blo 1466553 28220501 := bbase (se 8 (by rfl) ⟨165354, by rfl⟩ : syracuseStep 28220501 = 330709) (by norm_num)
theorem B1883225 : Blo 1466553 1883225 := bbase (se 2 (by rfl) ⟨706209, by rfl⟩ : syracuseStep 1883225 = 1412419) (by norm_num)
theorem B2202725 : Blo 1466553 2202725 := bbase (se 4 (by rfl) ⟨206505, by rfl⟩ : syracuseStep 2202725 = 413011) (by norm_num)
theorem B3300461 : Blo 1466553 3300461 := bbase (se 3 (by rfl) ⟨618836, by rfl⟩ : syracuseStep 3300461 = 1237673) (by norm_num)
theorem B8354933 : Blo 1466553 8354933 := bbase (se 5 (by rfl) ⟨391637, by rfl⟩ : syracuseStep 8354933 = 783275) (by norm_num)
theorem B2202749 : Blo 1466553 2202749 := bbase (se 3 (by rfl) ⟨413015, by rfl⟩ : syracuseStep 2202749 = 826031) (by norm_num)
theorem B2202773 : Blo 1466553 2202773 := bbase (se 6 (by rfl) ⟨51627, by rfl⟩ : syracuseStep 2202773 = 103255) (by norm_num)
theorem B5291173 : Blo 1466553 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B2202797 : Blo 1466553 2202797 := bbase (se 3 (by rfl) ⟨413024, by rfl⟩ : syracuseStep 2202797 = 826049) (by norm_num)
theorem B3300533 : Blo 1466553 3300533 := bbase (se 5 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 3300533 = 309425) (by norm_num)
theorem B2202821 : Blo 1466553 2202821 := bbase (se 4 (by rfl) ⟨206514, by rfl⟩ : syracuseStep 2202821 = 413029) (by norm_num)
theorem B2784469 : Blo 1466553 2784469 := bbase (se 7 (by rfl) ⟨32630, by rfl⟩ : syracuseStep 2784469 = 65261) (by norm_num)
theorem B1883369 : Blo 1466553 1883369 := bbase (se 2 (by rfl) ⟨706263, by rfl⟩ : syracuseStep 1883369 = 1412527) (by norm_num)
theorem B2350325 : Blo 1466553 2350325 := bbase (se 5 (by rfl) ⟨110171, by rfl⟩ : syracuseStep 2350325 = 220343) (by norm_num)
theorem B3300605 : Blo 1466553 3300605 := bbase (se 3 (by rfl) ⟨618863, by rfl⟩ : syracuseStep 3300605 = 1237727) (by norm_num)
theorem B3300677 : Blo 1466553 3300677 := bbase (se 4 (by rfl) ⟨309438, by rfl⟩ : syracuseStep 3300677 = 618877) (by norm_num)
theorem B25058645 : Blo 1466553 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B2784613 : Blo 1466553 2784613 := bbase (se 4 (by rfl) ⟨261057, by rfl⟩ : syracuseStep 2784613 = 522115) (by norm_num)
theorem B4234613 : Blo 1466553 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B2350453 : Blo 1466553 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B4955525 : Blo 1466553 4955525 := bbase (se 4 (by rfl) ⟨464580, by rfl⟩ : syracuseStep 4955525 = 929161) (by norm_num)
theorem B3300749 : Blo 1466553 3300749 := bbase (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) (by norm_num)
theorem B3300821 : Blo 1466553 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B2784773 : Blo 1466553 2784773 := bbase (se 4 (by rfl) ⟨261072, by rfl⟩ : syracuseStep 2784773 = 522145) (by norm_num)
theorem B4701701 : Blo 1466553 4701701 := bbase (se 4 (by rfl) ⟨440784, by rfl⟩ : syracuseStep 4701701 = 881569) (by norm_num)
theorem B3300893 : Blo 1466553 3300893 := bbase (se 3 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 3300893 = 1237835) (by norm_num)
theorem B2088517 : Blo 1466553 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B3300965 : Blo 1466553 3300965 := bbase (se 4 (by rfl) ⟨309465, by rfl⟩ : syracuseStep 3300965 = 618931) (by norm_num)
theorem B2784917 : Blo 1466553 2784917 := bbase (se 6 (by rfl) ⟨65271, by rfl⟩ : syracuseStep 2784917 = 130543) (by norm_num)
theorem B3301037 : Blo 1466553 3301037 := bbase (se 3 (by rfl) ⟨618944, by rfl⟩ : syracuseStep 3301037 = 1237889) (by norm_num)
theorem B5086901 : Blo 1466553 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B3301109 : Blo 1466553 3301109 := bbase (se 5 (by rfl) ⟨154739, by rfl⟩ : syracuseStep 3301109 = 309479) (by norm_num)
theorem B17841941 : Blo 1466553 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B6266645 : Blo 1466553 6266645 := bbase (se 6 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 6266645 = 293749) (by norm_num)
theorem B4955957 : Blo 1466553 4955957 := bbase (se 5 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 4955957 = 464621) (by norm_num)
theorem B3301181 : Blo 1466553 3301181 := bbase (se 3 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 3301181 = 1237943) (by norm_num)
theorem B3301253 : Blo 1466553 3301253 := bbase (se 4 (by rfl) ⟨309492, by rfl⟩ : syracuseStep 3301253 = 618985) (by norm_num)
theorem B2785205 : Blo 1466553 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B3301325 : Blo 1466553 3301325 := bbase (se 3 (by rfl) ⟨618998, by rfl⟩ : syracuseStep 3301325 = 1237997) (by norm_num)
theorem B3301379 : Blo 1466553 3301379 := bstep (se 1 (by rfl) ⟨2476034, by rfl⟩ : syracuseStep 3301379 = 4952069) B4952069
theorem B11149325 : Blo 1466553 11149325 := bstep (se 3 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 11149325 = 4180997) B4180997
theorem B4956173 : Blo 1466553 4956173 := bstep (se 3 (by rfl) ⟨929282, by rfl⟩ : syracuseStep 4956173 = 1858565) B1858565
theorem B3964963 : Blo 1466553 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B2088995 : Blo 1466553 2088995 := bstep (se 1 (by rfl) ⟨1566746, by rfl⟩ : syracuseStep 2088995 = 3133493) B3133493
theorem B4956227 : Blo 1466553 4956227 := bstep (se 1 (by rfl) ⟨3717170, by rfl⟩ : syracuseStep 4956227 = 7434341) B7434341
theorem B3620945 : Blo 1466553 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B9404579 : Blo 1466553 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B1466563 : Blo 1466553 1466563 := bstep (se 1 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 1466563 = 2199845) B2199845
theorem B1466579 : Blo 1466553 1466579 := bstep (se 1 (by rfl) ⟨1099934, by rfl⟩ : syracuseStep 1466579 = 2199869) B2199869
theorem B1466595 : Blo 1466553 1466595 := bstep (se 1 (by rfl) ⟨1099946, by rfl⟩ : syracuseStep 1466595 = 2199893) B2199893
theorem B4702445 : Blo 1466553 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B5021933 : Blo 1466553 5021933 := bstep (se 3 (by rfl) ⟨941612, by rfl⟩ : syracuseStep 5021933 = 1883225) B1883225
theorem B11297009 : Blo 1466553 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B1466611 : Blo 1466553 1466611 := bstep (se 1 (by rfl) ⟨1099958, by rfl⟩ : syracuseStep 1466611 = 2199917) B2199917
theorem B1466627 : Blo 1466553 1466627 := bstep (se 1 (by rfl) ⟨1099970, by rfl⟩ : syracuseStep 1466627 = 2199941) B2199941
theorem B18800909 : Blo 1466553 18800909 := bstep (se 3 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 18800909 = 7050341) B7050341
theorem B3301649 : Blo 1466553 3301649 := bstep (se 2 (by rfl) ⟨1238118, by rfl⟩ : syracuseStep 3301649 = 2476237) B2476237
theorem B1466643 : Blo 1466553 1466643 := bstep (se 1 (by rfl) ⟨1099982, by rfl⟩ : syracuseStep 1466643 = 2199965) B2199965
theorem B1466659 : Blo 1466553 1466659 := bstep (se 1 (by rfl) ⟨1099994, by rfl⟩ : syracuseStep 1466659 = 2199989) B2199989
theorem B3301667 : Blo 1466553 3301667 := bstep (se 1 (by rfl) ⟨2476250, by rfl⟩ : syracuseStep 3301667 = 4952501) B4952501
theorem B2785585 : Blo 1466553 2785585 := bstep (se 2 (by rfl) ⟨1044594, by rfl⟩ : syracuseStep 2785585 = 2089189) B2089189
theorem B1466675 : Blo 1466553 1466675 := bstep (se 1 (by rfl) ⟨1100006, by rfl⟩ : syracuseStep 1466675 = 2200013) B2200013
theorem B1466691 : Blo 1466553 1466691 := bstep (se 1 (by rfl) ⟨1100018, by rfl⟩ : syracuseStep 1466691 = 2200037) B2200037
theorem B4522321 : Blo 1466553 4522321 := bstep (se 2 (by rfl) ⟨1695870, by rfl⟩ : syracuseStep 4522321 = 3391741) B3391741
theorem B1466707 : Blo 1466553 1466707 := bstep (se 1 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 1466707 = 2200061) B2200061
theorem B1466723 : Blo 1466553 1466723 := bstep (se 1 (by rfl) ⟨1100042, by rfl⟩ : syracuseStep 1466723 = 2200085) B2200085
theorem B1466739 : Blo 1466553 1466739 := bstep (se 1 (by rfl) ⟨1100054, by rfl⟩ : syracuseStep 1466739 = 2200109) B2200109
theorem B1466755 : Blo 1466553 1466755 := bstep (se 1 (by rfl) ⟨1100066, by rfl⟩ : syracuseStep 1466755 = 2200133) B2200133
theorem B5570957 : Blo 1466553 5570957 := bstep (se 3 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 5570957 = 2089109) B2089109
theorem B1466771 : Blo 1466553 1466771 := bstep (se 1 (by rfl) ⟨1100078, by rfl⟩ : syracuseStep 1466771 = 2200157) B2200157
theorem B1466787 : Blo 1466553 1466787 := bstep (se 1 (by rfl) ⟨1100090, by rfl⟩ : syracuseStep 1466787 = 2200181) B2200181
theorem B1466803 : Blo 1466553 1466803 := bstep (se 1 (by rfl) ⟨1100102, by rfl⟩ : syracuseStep 1466803 = 2200205) B2200205
theorem B1466819 : Blo 1466553 1466819 := bstep (se 1 (by rfl) ⟨1100114, by rfl⟩ : syracuseStep 1466819 = 2200229) B2200229
theorem B2785745 : Blo 1466553 2785745 := bstep (se 2 (by rfl) ⟨1044654, by rfl⟩ : syracuseStep 2785745 = 2089309) B2089309
theorem B1466835 : Blo 1466553 1466835 := bstep (se 1 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 1466835 = 2200253) B2200253
theorem B1466851 : Blo 1466553 1466851 := bstep (se 1 (by rfl) ⟨1100138, by rfl⟩ : syracuseStep 1466851 = 2200277) B2200277
theorem B1466867 : Blo 1466553 1466867 := bstep (se 1 (by rfl) ⟨1100150, by rfl⟩ : syracuseStep 1466867 = 2200301) B2200301
theorem B1466883 : Blo 1466553 1466883 := bstep (se 1 (by rfl) ⟨1100162, by rfl⟩ : syracuseStep 1466883 = 2200325) B2200325
theorem B1466899 : Blo 1466553 1466899 := bstep (se 1 (by rfl) ⟨1100174, by rfl⟩ : syracuseStep 1466899 = 2200349) B2200349
theorem B1466915 : Blo 1466553 1466915 := bstep (se 1 (by rfl) ⟨1100186, by rfl⟩ : syracuseStep 1466915 = 2200373) B2200373
theorem B1983011 : Blo 1466553 1983011 := bstep (se 1 (by rfl) ⟨1487258, by rfl⟩ : syracuseStep 1983011 = 2974517) B2974517
theorem B3301937 : Blo 1466553 3301937 := bstep (se 2 (by rfl) ⟨1238226, by rfl⟩ : syracuseStep 3301937 = 2476453) B2476453
theorem B1466931 : Blo 1466553 1466931 := bstep (se 1 (by rfl) ⟨1100198, by rfl⟩ : syracuseStep 1466931 = 2200397) B2200397
theorem B1466947 : Blo 1466553 1466947 := bstep (se 1 (by rfl) ⟨1100210, by rfl⟩ : syracuseStep 1466947 = 2200421) B2200421
theorem B3301955 : Blo 1466553 3301955 := bstep (se 1 (by rfl) ⟨2476466, by rfl⟩ : syracuseStep 3301955 = 4952933) B4952933
theorem B2351683 : Blo 1466553 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B1466963 : Blo 1466553 1466963 := bstep (se 1 (by rfl) ⟨1100222, by rfl⟩ : syracuseStep 1466963 = 2200445) B2200445
theorem B1466979 : Blo 1466553 1466979 := bstep (se 1 (by rfl) ⟨1100234, by rfl⟩ : syracuseStep 1466979 = 2200469) B2200469
theorem B5292643 : Blo 1466553 5292643 := bstep (se 1 (by rfl) ⟨3969482, by rfl⟩ : syracuseStep 5292643 = 7938965) B7938965
theorem B5022317 : Blo 1466553 5022317 := bstep (se 3 (by rfl) ⟨941684, by rfl⟩ : syracuseStep 5022317 = 1883369) B1883369
theorem B1466995 : Blo 1466553 1466995 := bstep (se 1 (by rfl) ⟨1100246, by rfl⟩ : syracuseStep 1466995 = 2200493) B2200493
theorem B1467011 : Blo 1466553 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B3441283 : Blo 1466553 3441283 := bstep (se 1 (by rfl) ⟨2580962, by rfl⟩ : syracuseStep 3441283 = 5161925) B5161925
theorem B8929925 : Blo 1466553 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B1467027 : Blo 1466553 1467027 := bstep (se 1 (by rfl) ⟨1100270, by rfl⟩ : syracuseStep 1467027 = 2200541) B2200541
theorem B2089633 : Blo 1466553 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B1467043 : Blo 1466553 1467043 := bstep (se 1 (by rfl) ⟨1100282, by rfl⟩ : syracuseStep 1467043 = 2200565) B2200565
theorem B1467059 : Blo 1466553 1467059 := bstep (se 1 (by rfl) ⟨1100294, by rfl⟩ : syracuseStep 1467059 = 2200589) B2200589
theorem B1467075 : Blo 1466553 1467075 := bstep (se 1 (by rfl) ⟨1100306, by rfl⟩ : syracuseStep 1467075 = 2200613) B2200613
theorem B2351825 : Blo 1466553 2351825 := bstep (se 2 (by rfl) ⟨881934, by rfl⟩ : syracuseStep 2351825 = 1763869) B1763869
theorem B1467091 : Blo 1466553 1467091 := bstep (se 1 (by rfl) ⟨1100318, by rfl⟩ : syracuseStep 1467091 = 2200637) B2200637
theorem B1467107 : Blo 1466553 1467107 := bstep (se 1 (by rfl) ⟨1100330, by rfl⟩ : syracuseStep 1467107 = 2200661) B2200661
theorem B2351857 : Blo 1466553 2351857 := bstep (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) B1763893
theorem B1467123 : Blo 1466553 1467123 := bstep (se 1 (by rfl) ⟨1100342, by rfl⟩ : syracuseStep 1467123 = 2200685) B2200685
theorem B1467139 : Blo 1466553 1467139 := bstep (se 1 (by rfl) ⟨1100354, by rfl⟩ : syracuseStep 1467139 = 2200709) B2200709
theorem B1467155 : Blo 1466553 1467155 := bstep (se 1 (by rfl) ⟨1100366, by rfl⟩ : syracuseStep 1467155 = 2200733) B2200733
theorem B2089747 : Blo 1466553 2089747 := bstep (se 1 (by rfl) ⟨1567310, by rfl⟩ : syracuseStep 2089747 = 3134621) B3134621
theorem B1467171 : Blo 1466553 1467171 := bstep (se 1 (by rfl) ⟨1100378, by rfl⟩ : syracuseStep 1467171 = 2200757) B2200757
theorem B1467187 : Blo 1466553 1467187 := bstep (se 1 (by rfl) ⟨1100390, by rfl⟩ : syracuseStep 1467187 = 2200781) B2200781
theorem B1467203 : Blo 1466553 1467203 := bstep (se 1 (by rfl) ⟨1100402, by rfl⟩ : syracuseStep 1467203 = 2200805) B2200805
theorem B4178765 : Blo 1466553 4178765 := bstep (se 3 (by rfl) ⟨783518, by rfl⟩ : syracuseStep 4178765 = 1567037) B1567037
theorem B2474833 : Blo 1466553 2474833 := bstep (se 2 (by rfl) ⟨928062, by rfl⟩ : syracuseStep 2474833 = 1856125) B1856125
theorem B3302225 : Blo 1466553 3302225 := bstep (se 2 (by rfl) ⟨1238334, by rfl⟩ : syracuseStep 3302225 = 2476669) B2476669
theorem B1467219 : Blo 1466553 1467219 := bstep (se 1 (by rfl) ⟨1100414, by rfl⟩ : syracuseStep 1467219 = 2200829) B2200829
theorem B1467235 : Blo 1466553 1467235 := bstep (se 1 (by rfl) ⟨1100426, by rfl⟩ : syracuseStep 1467235 = 2200853) B2200853
theorem B2786147 : Blo 1466553 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B3302243 : Blo 1466553 3302243 := bstep (se 1 (by rfl) ⟨2476682, by rfl⟩ : syracuseStep 3302243 = 4953365) B4953365
theorem B2474867 : Blo 1466553 2474867 := bstep (se 1 (by rfl) ⟨1856150, by rfl⟩ : syracuseStep 2474867 = 3712301) B3712301
theorem B1467251 : Blo 1466553 1467251 := bstep (se 1 (by rfl) ⟨1100438, by rfl⟩ : syracuseStep 1467251 = 2200877) B2200877
theorem B1467267 : Blo 1466553 1467267 := bstep (se 1 (by rfl) ⟨1100450, by rfl⟩ : syracuseStep 1467267 = 2200901) B2200901
theorem B1467283 : Blo 1466553 1467283 := bstep (se 1 (by rfl) ⟨1100462, by rfl⟩ : syracuseStep 1467283 = 2200925) B2200925
theorem B1467299 : Blo 1466553 1467299 := bstep (se 1 (by rfl) ⟨1100474, by rfl⟩ : syracuseStep 1467299 = 2200949) B2200949
theorem B1467315 : Blo 1466553 1467315 := bstep (se 1 (by rfl) ⟨1100486, by rfl⟩ : syracuseStep 1467315 = 2200973) B2200973
theorem B1467331 : Blo 1466553 1467331 := bstep (se 1 (by rfl) ⟨1100498, by rfl⟩ : syracuseStep 1467331 = 2200997) B2200997
theorem B1467347 : Blo 1466553 1467347 := bstep (se 1 (by rfl) ⟨1100510, by rfl⟩ : syracuseStep 1467347 = 2201021) B2201021
theorem B1467363 : Blo 1466553 1467363 := bstep (se 1 (by rfl) ⟨1100522, by rfl⟩ : syracuseStep 1467363 = 2201045) B2201045
theorem B2474995 : Blo 1466553 2474995 := bstep (se 1 (by rfl) ⟨1856246, by rfl⟩ : syracuseStep 2474995 = 3712493) B3712493
theorem B1467379 : Blo 1466553 1467379 := bstep (se 1 (by rfl) ⟨1100534, by rfl⟩ : syracuseStep 1467379 = 2201069) B2201069
theorem B1467395 : Blo 1466553 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B4178947 : Blo 1466553 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B1467411 : Blo 1466553 1467411 := bstep (se 1 (by rfl) ⟨1100558, by rfl⟩ : syracuseStep 1467411 = 2201117) B2201117
theorem B1467427 : Blo 1466553 1467427 := bstep (se 1 (by rfl) ⟨1100570, by rfl⟩ : syracuseStep 1467427 = 2201141) B2201141
theorem B1762355 : Blo 1466553 1762355 := bstep (se 1 (by rfl) ⟨1321766, by rfl⟩ : syracuseStep 1762355 = 2643533) B2643533
theorem B1467443 : Blo 1466553 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B1467459 : Blo 1466553 1467459 := bstep (se 1 (by rfl) ⟨1100594, by rfl⟩ : syracuseStep 1467459 = 2201189) B2201189
theorem B1467475 : Blo 1466553 1467475 := bstep (se 1 (by rfl) ⟨1100606, by rfl⟩ : syracuseStep 1467475 = 2201213) B2201213
theorem B5948515 : Blo 1466553 5948515 := bstep (se 1 (by rfl) ⟨4461386, by rfl⟩ : syracuseStep 5948515 = 8922773) B8922773
theorem B1467491 : Blo 1466553 1467491 := bstep (se 1 (by rfl) ⟨1100618, by rfl⟩ : syracuseStep 1467491 = 2201237) B2201237
theorem B4703341 : Blo 1466553 4703341 := bstep (se 3 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 4703341 = 1763753) B1763753
theorem B3302513 : Blo 1466553 3302513 := bstep (se 2 (by rfl) ⟨1238442, by rfl⟩ : syracuseStep 3302513 = 2476885) B2476885
theorem B10585201 : Blo 1466553 10585201 := bstep (se 2 (by rfl) ⟨3969450, by rfl⟩ : syracuseStep 10585201 = 7938901) B7938901
theorem B1467507 : Blo 1466553 1467507 := bstep (se 1 (by rfl) ⟨1100630, by rfl⟩ : syracuseStep 1467507 = 2201261) B2201261
theorem B2475137 : Blo 1466553 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B1467523 : Blo 1466553 1467523 := bstep (se 1 (by rfl) ⟨1100642, by rfl⟩ : syracuseStep 1467523 = 2201285) B2201285
theorem B3302531 : Blo 1466553 3302531 := bstep (se 1 (by rfl) ⟨2476898, by rfl⟩ : syracuseStep 3302531 = 4953797) B4953797
theorem B1467539 : Blo 1466553 1467539 := bstep (se 1 (by rfl) ⟨1100654, by rfl⟩ : syracuseStep 1467539 = 2201309) B2201309
theorem B1467555 : Blo 1466553 1467555 := bstep (se 1 (by rfl) ⟨1100666, by rfl⟩ : syracuseStep 1467555 = 2201333) B2201333
theorem B4179107 : Blo 1466553 4179107 := bstep (se 1 (by rfl) ⟨3134330, by rfl⟩ : syracuseStep 4179107 = 6268661) B6268661
theorem B1467571 : Blo 1466553 1467571 := bstep (se 1 (by rfl) ⟨1100678, by rfl⟩ : syracuseStep 1467571 = 2201357) B2201357
theorem B1467587 : Blo 1466553 1467587 := bstep (se 1 (by rfl) ⟨1100690, by rfl⟩ : syracuseStep 1467587 = 2201381) B2201381
theorem B1467603 : Blo 1466553 1467603 := bstep (se 1 (by rfl) ⟨1100702, by rfl⟩ : syracuseStep 1467603 = 2201405) B2201405
theorem B1467619 : Blo 1466553 1467619 := bstep (se 1 (by rfl) ⟨1100714, by rfl⟩ : syracuseStep 1467619 = 2201429) B2201429
theorem B1467635 : Blo 1466553 1467635 := bstep (se 1 (by rfl) ⟨1100726, by rfl⟩ : syracuseStep 1467635 = 2201453) B2201453
theorem B2475265 : Blo 1466553 2475265 := bstep (se 2 (by rfl) ⟨928224, by rfl⟩ : syracuseStep 2475265 = 1856449) B1856449
theorem B1467651 : Blo 1466553 1467651 := bstep (se 1 (by rfl) ⟨1100738, by rfl⟩ : syracuseStep 1467651 = 2201477) B2201477
theorem B1467667 : Blo 1466553 1467667 := bstep (se 1 (by rfl) ⟨1100750, by rfl⟩ : syracuseStep 1467667 = 2201501) B2201501
theorem B2475299 : Blo 1466553 2475299 := bstep (se 1 (by rfl) ⟨1856474, by rfl⟩ : syracuseStep 2475299 = 3712949) B3712949
theorem B1467683 : Blo 1466553 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B10036529 : Blo 1466553 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B1467699 : Blo 1466553 1467699 := bstep (se 1 (by rfl) ⟨1100774, by rfl⟩ : syracuseStep 1467699 = 2201549) B2201549
theorem B18793781 : Blo 1466553 18793781 := bstep (se 5 (by rfl) ⟨880958, by rfl⟩ : syracuseStep 18793781 = 1761917) B1761917
theorem B1467715 : Blo 1466553 1467715 := bstep (se 1 (by rfl) ⟨1100786, by rfl⟩ : syracuseStep 1467715 = 2201573) B2201573
theorem B1467731 : Blo 1466553 1467731 := bstep (se 1 (by rfl) ⟨1100798, by rfl⟩ : syracuseStep 1467731 = 2201597) B2201597
theorem B1467747 : Blo 1466553 1467747 := bstep (se 1 (by rfl) ⟨1100810, by rfl⟩ : syracuseStep 1467747 = 2201621) B2201621
theorem B10585457 : Blo 1466553 10585457 := bstep (se 2 (by rfl) ⟨3969546, by rfl⟩ : syracuseStep 10585457 = 7939093) B7939093
theorem B1467763 : Blo 1466553 1467763 := bstep (se 1 (by rfl) ⟨1100822, by rfl⟩ : syracuseStep 1467763 = 2201645) B2201645
theorem B1467779 : Blo 1466553 1467779 := bstep (se 1 (by rfl) ⟨1100834, by rfl⟩ : syracuseStep 1467779 = 2201669) B2201669
theorem B1467795 : Blo 1466553 1467795 := bstep (se 1 (by rfl) ⟨1100846, by rfl⟩ : syracuseStep 1467795 = 2201693) B2201693
theorem B3302801 : Blo 1466553 3302801 := bstep (se 2 (by rfl) ⟨1238550, by rfl⟩ : syracuseStep 3302801 = 2477101) B2477101
theorem B2475427 : Blo 1466553 2475427 := bstep (se 1 (by rfl) ⟨1856570, by rfl⟩ : syracuseStep 2475427 = 3713141) B3713141
theorem B1467811 : Blo 1466553 1467811 := bstep (se 1 (by rfl) ⟨1100858, by rfl⟩ : syracuseStep 1467811 = 2201717) B2201717
theorem B3302819 : Blo 1466553 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B7431587 : Blo 1466553 7431587 := bstep (se 1 (by rfl) ⟨5573690, by rfl⟩ : syracuseStep 7431587 = 11147381) B11147381
theorem B6268337 : Blo 1466553 6268337 := bstep (se 2 (by rfl) ⟨2350626, by rfl⟩ : syracuseStep 6268337 = 4701253) B4701253
theorem B1467827 : Blo 1466553 1467827 := bstep (se 1 (by rfl) ⟨1100870, by rfl⟩ : syracuseStep 1467827 = 2201741) B2201741
theorem B1467843 : Blo 1466553 1467843 := bstep (se 1 (by rfl) ⟨1100882, by rfl⟩ : syracuseStep 1467843 = 2201765) B2201765
theorem B1467859 : Blo 1466553 1467859 := bstep (se 1 (by rfl) ⟨1100894, by rfl⟩ : syracuseStep 1467859 = 2201789) B2201789
theorem B6268387 : Blo 1466553 6268387 := bstep (se 1 (by rfl) ⟨4701290, by rfl⟩ : syracuseStep 6268387 = 9402581) B9402581
theorem B1467875 : Blo 1466553 1467875 := bstep (se 1 (by rfl) ⟨1100906, by rfl⟩ : syracuseStep 1467875 = 2201813) B2201813
theorem B1467891 : Blo 1466553 1467891 := bstep (se 1 (by rfl) ⟨1100918, by rfl⟩ : syracuseStep 1467891 = 2201837) B2201837
theorem B1467907 : Blo 1466553 1467907 := bstep (se 1 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 1467907 = 2201861) B2201861
theorem B1467923 : Blo 1466553 1467923 := bstep (se 1 (by rfl) ⟨1100942, by rfl⟩ : syracuseStep 1467923 = 2201885) B2201885
theorem B1467939 : Blo 1466553 1467939 := bstep (se 1 (by rfl) ⟨1100954, by rfl⟩ : syracuseStep 1467939 = 2201909) B2201909
theorem B2475569 : Blo 1466553 2475569 := bstep (se 2 (by rfl) ⟨928338, by rfl⟩ : syracuseStep 2475569 = 1856677) B1856677
theorem B7054897 : Blo 1466553 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B1467955 : Blo 1466553 1467955 := bstep (se 1 (by rfl) ⟨1100966, by rfl⟩ : syracuseStep 1467955 = 2201933) B2201933
theorem B1467971 : Blo 1466553 1467971 := bstep (se 1 (by rfl) ⟨1100978, by rfl⟩ : syracuseStep 1467971 = 2201957) B2201957
theorem B1467987 : Blo 1466553 1467987 := bstep (se 1 (by rfl) ⟨1100990, by rfl⟩ : syracuseStep 1467987 = 2201981) B2201981
theorem B1468003 : Blo 1466553 1468003 := bstep (se 1 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 1468003 = 2202005) B2202005
theorem B3712625 : Blo 1466553 3712625 := bstep (se 2 (by rfl) ⟨1392234, by rfl⟩ : syracuseStep 3712625 = 2784469) B2784469
theorem B1468019 : Blo 1466553 1468019 := bstep (se 1 (by rfl) ⟨1101014, by rfl⟩ : syracuseStep 1468019 = 2202029) B2202029
theorem B1468035 : Blo 1466553 1468035 := bstep (se 1 (by rfl) ⟨1101026, by rfl⟩ : syracuseStep 1468035 = 2202053) B2202053
theorem B1468051 : Blo 1466553 1468051 := bstep (se 1 (by rfl) ⟨1101038, by rfl⟩ : syracuseStep 1468051 = 2202077) B2202077
theorem B3712675 : Blo 1466553 3712675 := bstep (se 1 (by rfl) ⟨2784506, by rfl⟩ : syracuseStep 3712675 = 5569013) B5569013
theorem B1468067 : Blo 1466553 1468067 := bstep (se 1 (by rfl) ⟨1101050, by rfl⟩ : syracuseStep 1468067 = 2202101) B2202101
theorem B2475697 : Blo 1466553 2475697 := bstep (se 2 (by rfl) ⟨928386, by rfl⟩ : syracuseStep 2475697 = 1856773) B1856773
theorem B3303089 : Blo 1466553 3303089 := bstep (se 2 (by rfl) ⟨1238658, by rfl⟩ : syracuseStep 3303089 = 2477317) B2477317
theorem B1468083 : Blo 1466553 1468083 := bstep (se 1 (by rfl) ⟨1101062, by rfl⟩ : syracuseStep 1468083 = 2202125) B2202125
theorem B3303107 : Blo 1466553 3303107 := bstep (se 1 (by rfl) ⟨2477330, by rfl⟩ : syracuseStep 3303107 = 4954661) B4954661
theorem B1468099 : Blo 1466553 1468099 := bstep (se 1 (by rfl) ⟨1101074, by rfl⟩ : syracuseStep 1468099 = 2202149) B2202149
theorem B2475731 : Blo 1466553 2475731 := bstep (se 1 (by rfl) ⟨1856798, by rfl⟩ : syracuseStep 2475731 = 3713597) B3713597
theorem B1468115 : Blo 1466553 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B2787043 : Blo 1466553 2787043 := bstep (se 1 (by rfl) ⟨2090282, by rfl⟩ : syracuseStep 2787043 = 4180565) B4180565
theorem B1468131 : Blo 1466553 1468131 := bstep (se 1 (by rfl) ⟨1101098, by rfl⟩ : syracuseStep 1468131 = 2202197) B2202197
theorem B1468147 : Blo 1466553 1468147 := bstep (se 1 (by rfl) ⟨1101110, by rfl⟩ : syracuseStep 1468147 = 2202221) B2202221
theorem B2975491 : Blo 1466553 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1468163 : Blo 1466553 1468163 := bstep (se 1 (by rfl) ⟨1101122, by rfl⟩ : syracuseStep 1468163 = 2202245) B2202245
theorem B1468179 : Blo 1466553 1468179 := bstep (se 1 (by rfl) ⟨1101134, by rfl⟩ : syracuseStep 1468179 = 2202269) B2202269
theorem B1468195 : Blo 1466553 1468195 := bstep (se 1 (by rfl) ⟨1101146, by rfl⟩ : syracuseStep 1468195 = 2202293) B2202293
theorem B3712817 : Blo 1466553 3712817 := bstep (se 2 (by rfl) ⟨1392306, by rfl⟩ : syracuseStep 3712817 = 2784613) B2784613
theorem B1468211 : Blo 1466553 1468211 := bstep (se 1 (by rfl) ⟨1101158, by rfl⟩ : syracuseStep 1468211 = 2202317) B2202317
theorem B2975555 : Blo 1466553 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B1468227 : Blo 1466553 1468227 := bstep (se 1 (by rfl) ⟨1101170, by rfl⟩ : syracuseStep 1468227 = 2202341) B2202341
theorem B2475859 : Blo 1466553 2475859 := bstep (se 1 (by rfl) ⟨1856894, by rfl⟩ : syracuseStep 2475859 = 3713789) B3713789
theorem B1468243 : Blo 1466553 1468243 := bstep (se 1 (by rfl) ⟨1101182, by rfl⟩ : syracuseStep 1468243 = 2202365) B2202365
theorem B1468259 : Blo 1466553 1468259 := bstep (se 1 (by rfl) ⟨1101194, by rfl⟩ : syracuseStep 1468259 = 2202389) B2202389
theorem B1468275 : Blo 1466553 1468275 := bstep (se 1 (by rfl) ⟨1101206, by rfl⟩ : syracuseStep 1468275 = 2202413) B2202413
theorem B2787203 : Blo 1466553 2787203 := bstep (se 1 (by rfl) ⟨2090402, by rfl⟩ : syracuseStep 2787203 = 4180805) B4180805
theorem B1468291 : Blo 1466553 1468291 := bstep (se 1 (by rfl) ⟨1101218, by rfl⟩ : syracuseStep 1468291 = 2202437) B2202437
theorem B2508689 : Blo 1466553 2508689 := bstep (se 2 (by rfl) ⟨940758, by rfl⟩ : syracuseStep 2508689 = 1881517) B1881517
theorem B1468307 : Blo 1466553 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B1468323 : Blo 1466553 1468323 := bstep (se 1 (by rfl) ⟨1101242, by rfl⟩ : syracuseStep 1468323 = 2202485) B2202485
theorem B2230195 : Blo 1466553 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B1468339 : Blo 1466553 1468339 := bstep (se 1 (by rfl) ⟨1101254, by rfl⟩ : syracuseStep 1468339 = 2202509) B2202509
theorem B1468355 : Blo 1466553 1468355 := bstep (se 1 (by rfl) ⟨1101266, by rfl⟩ : syracuseStep 1468355 = 2202533) B2202533
theorem B3303377 : Blo 1466553 3303377 := bstep (se 2 (by rfl) ⟨1238766, by rfl⟩ : syracuseStep 3303377 = 2477533) B2477533
theorem B1468371 : Blo 1466553 1468371 := bstep (se 1 (by rfl) ⟨1101278, by rfl⟩ : syracuseStep 1468371 = 2202557) B2202557
theorem B2476001 : Blo 1466553 2476001 := bstep (se 2 (by rfl) ⟨928500, by rfl⟩ : syracuseStep 2476001 = 1857001) B1857001
theorem B3303395 : Blo 1466553 3303395 := bstep (se 1 (by rfl) ⟨2477546, by rfl⟩ : syracuseStep 3303395 = 4955093) B4955093
theorem B1468387 : Blo 1466553 1468387 := bstep (se 1 (by rfl) ⟨1101290, by rfl⟩ : syracuseStep 1468387 = 2202581) B2202581
theorem B4704227 : Blo 1466553 4704227 := bstep (se 1 (by rfl) ⟨3528170, by rfl⟩ : syracuseStep 4704227 = 7056341) B7056341
theorem B1468403 : Blo 1466553 1468403 := bstep (se 1 (by rfl) ⟨1101302, by rfl⟩ : syracuseStep 1468403 = 2202605) B2202605
theorem B1468419 : Blo 1466553 1468419 := bstep (se 1 (by rfl) ⟨1101314, by rfl⟩ : syracuseStep 1468419 = 2202629) B2202629
theorem B1468435 : Blo 1466553 1468435 := bstep (se 1 (by rfl) ⟨1101326, by rfl⟩ : syracuseStep 1468435 = 2202653) B2202653
theorem B1468451 : Blo 1466553 1468451 := bstep (se 1 (by rfl) ⟨1101338, by rfl⟩ : syracuseStep 1468451 = 2202677) B2202677
theorem B1468467 : Blo 1466553 1468467 := bstep (se 1 (by rfl) ⟨1101350, by rfl⟩ : syracuseStep 1468467 = 2202701) B2202701
theorem B1468483 : Blo 1466553 1468483 := bstep (se 1 (by rfl) ⟨1101362, by rfl⟩ : syracuseStep 1468483 = 2202725) B2202725
theorem B1468499 : Blo 1466553 1468499 := bstep (se 1 (by rfl) ⟨1101374, by rfl⟩ : syracuseStep 1468499 = 2202749) B2202749
theorem B2476129 : Blo 1466553 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B1468515 : Blo 1466553 1468515 := bstep (se 1 (by rfl) ⟨1101386, by rfl⟩ : syracuseStep 1468515 = 2202773) B2202773
theorem B4950125 : Blo 1466553 4950125 := bstep (se 3 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 4950125 = 1856297) B1856297
theorem B1468531 : Blo 1466553 1468531 := bstep (se 1 (by rfl) ⟨1101398, by rfl⟩ : syracuseStep 1468531 = 2202797) B2202797
theorem B2476163 : Blo 1466553 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B1468547 : Blo 1466553 1468547 := bstep (se 1 (by rfl) ⟨1101410, by rfl⟩ : syracuseStep 1468547 = 2202821) B2202821
theorem B4950179 : Blo 1466553 4950179 := bstep (se 1 (by rfl) ⟨3712634, by rfl⟩ : syracuseStep 4950179 = 7425269) B7425269
theorem B1566883 : Blo 1466553 1566883 := bstep (se 1 (by rfl) ⟨1175162, by rfl⟩ : syracuseStep 1566883 = 2350325) B2350325
theorem B7432397 : Blo 1466553 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B4180177 : Blo 1466553 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B16705763 : Blo 1466553 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B3303665 : Blo 1466553 3303665 := bstep (se 2 (by rfl) ⟨1238874, by rfl⟩ : syracuseStep 3303665 = 2477749) B2477749
theorem B2476291 : Blo 1466553 2476291 := bstep (se 1 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 2476291 = 3714437) B3714437
theorem B3303683 : Blo 1466553 3303683 := bstep (se 1 (by rfl) ⟨2477762, by rfl⟩ : syracuseStep 3303683 = 4955525) B4955525
theorem B11143493 : Blo 1466553 11143493 := bstep (se 4 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 11143493 = 2089405) B2089405
theorem B2476433 : Blo 1466553 2476433 := bstep (se 2 (by rfl) ⟨928662, by rfl⟩ : syracuseStep 2476433 = 1857325) B1857325
theorem B4950449 : Blo 1466553 4950449 := bstep (se 2 (by rfl) ⟨1856418, by rfl⟩ : syracuseStep 4950449 = 3712837) B3712837
theorem B2230705 : Blo 1466553 2230705 := bstep (se 2 (by rfl) ⟨836514, by rfl⟩ : syracuseStep 2230705 = 1673029) B1673029
theorem B8358349 : Blo 1466553 8358349 := bstep (se 3 (by rfl) ⟨1567190, by rfl⟩ : syracuseStep 8358349 = 3134381) B3134381
theorem B5573069 : Blo 1466553 5573069 := bstep (se 3 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 5573069 = 2089901) B2089901
theorem B2476561 : Blo 1466553 2476561 := bstep (se 2 (by rfl) ⟨928710, by rfl⟩ : syracuseStep 2476561 = 1857421) B1857421
theorem B3303953 : Blo 1466553 3303953 := bstep (se 2 (by rfl) ⟨1238982, by rfl⟩ : syracuseStep 3303953 = 2477965) B2477965
theorem B3303971 : Blo 1466553 3303971 := bstep (se 1 (by rfl) ⟨2477978, by rfl⟩ : syracuseStep 3303971 = 4955957) B4955957
theorem B2476595 : Blo 1466553 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B2476723 : Blo 1466553 2476723 := bstep (se 1 (by rfl) ⟨1857542, by rfl⟩ : syracuseStep 2476723 = 3715085) B3715085
theorem B2509571 : Blo 1466553 2509571 := bstep (se 1 (by rfl) ⟨1882178, by rfl⟩ : syracuseStep 2509571 = 3764357) B3764357
theorem B3713809 : Blo 1466553 3713809 := bstep (se 2 (by rfl) ⟨1392678, by rfl⟩ : syracuseStep 3713809 = 2785357) B2785357
theorem B1567507 : Blo 1466553 1567507 := bstep (se 1 (by rfl) ⟨1175630, by rfl⟩ : syracuseStep 1567507 = 2351261) B2351261
theorem B3304241 : Blo 1466553 3304241 := bstep (se 2 (by rfl) ⟨1239090, by rfl⟩ : syracuseStep 3304241 = 2478181) B2478181
theorem B2476865 : Blo 1466553 2476865 := bstep (se 2 (by rfl) ⟨928824, by rfl⟩ : syracuseStep 2476865 = 1857649) B1857649
theorem B7424945 : Blo 1466553 7424945 := bstep (se 2 (by rfl) ⟨2784354, by rfl⟩ : syracuseStep 7424945 = 5568709) B5568709
theorem B2476993 : Blo 1466553 2476993 := bstep (se 2 (by rfl) ⟨928872, by rfl⟩ : syracuseStep 2476993 = 1857745) B1857745
theorem B4950989 : Blo 1466553 4950989 := bstep (se 3 (by rfl) ⟨928310, by rfl⟩ : syracuseStep 4950989 = 1856621) B1856621
theorem B2477027 : Blo 1466553 2477027 := bstep (se 1 (by rfl) ⟨1857770, by rfl⟩ : syracuseStep 2477027 = 3715541) B3715541
theorem B4951043 : Blo 1466553 4951043 := bstep (se 1 (by rfl) ⟨3713282, by rfl⟩ : syracuseStep 4951043 = 7426565) B7426565
theorem B3714083 : Blo 1466553 3714083 := bstep (se 1 (by rfl) ⟨2785562, by rfl⟩ : syracuseStep 3714083 = 5571125) B5571125
theorem B3345457 : Blo 1466553 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B3345475 : Blo 1466553 3345475 := bstep (se 1 (by rfl) ⟨2509106, by rfl⟩ : syracuseStep 3345475 = 5018213) B5018213
theorem B2231363 : Blo 1466553 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B15051845 : Blo 1466553 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B2477155 : Blo 1466553 2477155 := bstep (se 1 (by rfl) ⟨1857866, by rfl⟩ : syracuseStep 2477155 = 3715733) B3715733
theorem B3968099 : Blo 1466553 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2509955 : Blo 1466553 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B3394705 : Blo 1466553 3394705 := bstep (se 2 (by rfl) ⟨1273014, by rfl⟩ : syracuseStep 3394705 = 2546029) B2546029
theorem B1649875 : Blo 1466553 1649875 := bstep (se 1 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 1649875 = 2474813) B2474813
theorem B3714275 : Blo 1466553 3714275 := bstep (se 1 (by rfl) ⟨2785706, by rfl⟩ : syracuseStep 3714275 = 5571413) B5571413
theorem B5573873 : Blo 1466553 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B2477297 : Blo 1466553 2477297 := bstep (se 2 (by rfl) ⟨928986, by rfl⟩ : syracuseStep 2477297 = 1857973) B1857973
theorem B4951313 : Blo 1466553 4951313 := bstep (se 2 (by rfl) ⟨1856742, by rfl⟩ : syracuseStep 4951313 = 3713485) B3713485
theorem B1650019 : Blo 1466553 1650019 := bstep (se 1 (by rfl) ⟨1237514, by rfl⟩ : syracuseStep 1650019 = 2475029) B2475029
theorem B2477425 : Blo 1466553 2477425 := bstep (se 2 (by rfl) ⟨929034, by rfl⟩ : syracuseStep 2477425 = 1858069) B1858069
theorem B2477459 : Blo 1466553 2477459 := bstep (se 1 (by rfl) ⟨1858094, by rfl⟩ : syracuseStep 2477459 = 3716189) B3716189
theorem B10038725 : Blo 1466553 10038725 := bstep (se 4 (by rfl) ⟨941130, by rfl⟩ : syracuseStep 10038725 = 1882261) B1882261
theorem B4181453 : Blo 1466553 4181453 := bstep (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) B1568045
theorem B1650163 : Blo 1466553 1650163 := bstep (se 1 (by rfl) ⟨1237622, by rfl⟩ : syracuseStep 1650163 = 2475245) B2475245
theorem B2477587 : Blo 1466553 2477587 := bstep (se 1 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 2477587 = 3716381) B3716381
theorem B8474147 : Blo 1466553 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B1650307 : Blo 1466553 1650307 := bstep (se 1 (by rfl) ⟨1237730, by rfl⟩ : syracuseStep 1650307 = 2475461) B2475461
theorem B4181635 : Blo 1466553 4181635 := bstep (se 1 (by rfl) ⟨3136226, by rfl⟩ : syracuseStep 4181635 = 6272453) B6272453
theorem B11292301 : Blo 1466553 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B2477729 : Blo 1466553 2477729 := bstep (se 2 (by rfl) ⟨929148, by rfl⟩ : syracuseStep 2477729 = 1858297) B1858297
theorem B4181681 : Blo 1466553 4181681 := bstep (se 2 (by rfl) ⟨1568130, by rfl⟩ : syracuseStep 4181681 = 3136261) B3136261
theorem B4525805 : Blo 1466553 4525805 := bstep (se 3 (by rfl) ⟨848588, by rfl⟩ : syracuseStep 4525805 = 1697177) B1697177
theorem B1650451 : Blo 1466553 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B2477857 : Blo 1466553 2477857 := bstep (se 2 (by rfl) ⟨929196, by rfl⟩ : syracuseStep 2477857 = 1858393) B1858393
theorem B4951853 : Blo 1466553 4951853 := bstep (se 3 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 4951853 = 1856945) B1856945
theorem B3968813 : Blo 1466553 3968813 := bstep (se 3 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 3968813 = 1488305) B1488305
theorem B2477891 : Blo 1466553 2477891 := bstep (se 1 (by rfl) ⟨1858418, by rfl⟩ : syracuseStep 2477891 = 3716837) B3716837
theorem B6270797 : Blo 1466553 6270797 := bstep (se 3 (by rfl) ⟨1175774, by rfl⟩ : syracuseStep 6270797 = 2351549) B2351549
theorem B4951907 : Blo 1466553 4951907 := bstep (se 1 (by rfl) ⟨3713930, by rfl⟩ : syracuseStep 4951907 = 7427861) B7427861
theorem B5574541 : Blo 1466553 5574541 := bstep (se 3 (by rfl) ⟨1045226, by rfl⟩ : syracuseStep 5574541 = 2090453) B2090453
theorem B1650595 : Blo 1466553 1650595 := bstep (se 1 (by rfl) ⟨1237946, by rfl⟩ : syracuseStep 1650595 = 2475893) B2475893
theorem B2478019 : Blo 1466553 2478019 := bstep (se 1 (by rfl) ⟨1858514, by rfl⟩ : syracuseStep 2478019 = 3717029) B3717029
theorem B1650739 : Blo 1466553 1650739 := bstep (se 1 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 1650739 = 2476109) B2476109
theorem B2478161 : Blo 1466553 2478161 := bstep (se 2 (by rfl) ⟨929310, by rfl⟩ : syracuseStep 2478161 = 1858621) B1858621
theorem B4952177 : Blo 1466553 4952177 := bstep (se 2 (by rfl) ⟨1857066, by rfl⟩ : syracuseStep 4952177 = 3714133) B3714133
theorem B3715217 : Blo 1466553 3715217 := bstep (se 2 (by rfl) ⟨1393206, by rfl⟩ : syracuseStep 3715217 = 2786413) B2786413
theorem B1650883 : Blo 1466553 1650883 := bstep (se 1 (by rfl) ⟨1238162, by rfl⟩ : syracuseStep 1650883 = 2476325) B2476325
theorem B3715267 : Blo 1466553 3715267 := bstep (se 1 (by rfl) ⟨2786450, by rfl⟩ : syracuseStep 3715267 = 5572901) B5572901
theorem B8704205 : Blo 1466553 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B2199857 : Blo 1466553 2199857 := bstep (se 2 (by rfl) ⟨824946, by rfl⟩ : syracuseStep 2199857 = 1649893) B1649893
theorem B2199875 : Blo 1466553 2199875 := bstep (se 1 (by rfl) ⟨1649906, by rfl⟩ : syracuseStep 2199875 = 3299813) B3299813
theorem B16085317 : Blo 1466553 16085317 := bstep (se 4 (by rfl) ⟨1507998, by rfl⟩ : syracuseStep 16085317 = 3015997) B3015997
theorem B17854789 : Blo 1466553 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B3715409 : Blo 1466553 3715409 := bstep (se 2 (by rfl) ⟨1393278, by rfl⟩ : syracuseStep 3715409 = 2786557) B2786557
theorem B1651027 : Blo 1466553 1651027 := bstep (se 1 (by rfl) ⟨1238270, by rfl⟩ : syracuseStep 1651027 = 2476541) B2476541
theorem B2199905 : Blo 1466553 2199905 := bstep (se 2 (by rfl) ⟨824964, by rfl⟩ : syracuseStep 2199905 = 1649929) B1649929
theorem B7426403 : Blo 1466553 7426403 := bstep (se 1 (by rfl) ⟨5569802, by rfl⟩ : syracuseStep 7426403 = 11139605) B11139605
theorem B2199923 : Blo 1466553 2199923 := bstep (se 1 (by rfl) ⟨1649942, by rfl⟩ : syracuseStep 2199923 = 3299885) B3299885
theorem B8360333 : Blo 1466553 8360333 := bstep (se 3 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 8360333 = 3135125) B3135125
theorem B2199953 : Blo 1466553 2199953 := bstep (se 2 (by rfl) ⟨824982, by rfl⟩ : syracuseStep 2199953 = 1649965) B1649965
theorem B2199971 : Blo 1466553 2199971 := bstep (se 1 (by rfl) ⟨1649978, by rfl⟩ : syracuseStep 2199971 = 3299957) B3299957
theorem B2200001 : Blo 1466553 2200001 := bstep (se 2 (by rfl) ⟨825000, by rfl⟩ : syracuseStep 2200001 = 1650001) B1650001
theorem B2200019 : Blo 1466553 2200019 := bstep (se 1 (by rfl) ⟨1650014, by rfl⟩ : syracuseStep 2200019 = 3300029) B3300029
theorem B2232787 : Blo 1466553 2232787 := bstep (se 1 (by rfl) ⟨1674590, by rfl⟩ : syracuseStep 2232787 = 3349181) B3349181
theorem B1651171 : Blo 1466553 1651171 := bstep (se 1 (by rfl) ⟨1238378, by rfl⟩ : syracuseStep 1651171 = 2476757) B2476757
theorem B2200049 : Blo 1466553 2200049 := bstep (se 2 (by rfl) ⟨825018, by rfl⟩ : syracuseStep 2200049 = 1650037) B1650037
theorem B3133937 : Blo 1466553 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B2200067 : Blo 1466553 2200067 := bstep (se 1 (by rfl) ⟨1650050, by rfl⟩ : syracuseStep 2200067 = 3300101) B3300101
theorem B3527171 : Blo 1466553 3527171 := bstep (se 1 (by rfl) ⟨2645378, by rfl⟩ : syracuseStep 3527171 = 5290757) B5290757
theorem B2200097 : Blo 1466553 2200097 := bstep (se 2 (by rfl) ⟨825036, by rfl⟩ : syracuseStep 2200097 = 1650073) B1650073
theorem B2200115 : Blo 1466553 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B2200145 : Blo 1466553 2200145 := bstep (se 2 (by rfl) ⟨825054, by rfl⟩ : syracuseStep 2200145 = 1650109) B1650109
theorem B2200163 : Blo 1466553 2200163 := bstep (se 1 (by rfl) ⟨1650122, by rfl⟩ : syracuseStep 2200163 = 3300245) B3300245
theorem B1651315 : Blo 1466553 1651315 := bstep (se 1 (by rfl) ⟨1238486, by rfl⟩ : syracuseStep 1651315 = 2476973) B2476973
theorem B2200193 : Blo 1466553 2200193 := bstep (se 2 (by rfl) ⟨825072, by rfl⟩ : syracuseStep 2200193 = 1650145) B1650145
theorem B7934597 : Blo 1466553 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B4952717 : Blo 1466553 4952717 := bstep (se 3 (by rfl) ⟨928634, by rfl⟩ : syracuseStep 4952717 = 1857269) B1857269
theorem B2200211 : Blo 1466553 2200211 := bstep (se 1 (by rfl) ⟨1650158, by rfl⟩ : syracuseStep 2200211 = 3300317) B3300317
theorem B5575331 : Blo 1466553 5575331 := bstep (se 1 (by rfl) ⟨4181498, by rfl⟩ : syracuseStep 5575331 = 8362997) B8362997
theorem B2200241 : Blo 1466553 2200241 := bstep (se 2 (by rfl) ⟨825090, by rfl⟩ : syracuseStep 2200241 = 1650181) B1650181
theorem B2200259 : Blo 1466553 2200259 := bstep (se 1 (by rfl) ⟨1650194, by rfl⟩ : syracuseStep 2200259 = 3300389) B3300389
theorem B4952771 : Blo 1466553 4952771 := bstep (se 1 (by rfl) ⟨3714578, by rfl⟩ : syracuseStep 4952771 = 7429157) B7429157
theorem B2200289 : Blo 1466553 2200289 := bstep (se 2 (by rfl) ⟨825108, by rfl⟩ : syracuseStep 2200289 = 1650217) B1650217
theorem B18813667 : Blo 1466553 18813667 := bstep (se 1 (by rfl) ⟨14110250, by rfl⟩ : syracuseStep 18813667 = 28220501) B28220501
theorem B2200307 : Blo 1466553 2200307 := bstep (se 1 (by rfl) ⟨1650230, by rfl⟩ : syracuseStep 2200307 = 3300461) B3300461
theorem B1651459 : Blo 1466553 1651459 := bstep (se 1 (by rfl) ⟨1238594, by rfl⟩ : syracuseStep 1651459 = 2477189) B2477189
theorem B8352517 : Blo 1466553 8352517 := bstep (se 4 (by rfl) ⟨783048, by rfl⟩ : syracuseStep 8352517 = 1566097) B1566097
theorem B9401093 : Blo 1466553 9401093 := bstep (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) B1762705
theorem B2200337 : Blo 1466553 2200337 := bstep (se 2 (by rfl) ⟨825126, by rfl⟩ : syracuseStep 2200337 = 1650253) B1650253
theorem B2200355 : Blo 1466553 2200355 := bstep (se 1 (by rfl) ⟨1650266, by rfl⟩ : syracuseStep 2200355 = 3300533) B3300533
theorem B2200385 : Blo 1466553 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B2200403 : Blo 1466553 2200403 := bstep (se 1 (by rfl) ⟨1650302, by rfl⟩ : syracuseStep 2200403 = 3300605) B3300605
theorem B2200433 : Blo 1466553 2200433 := bstep (se 2 (by rfl) ⟨825162, by rfl⟩ : syracuseStep 2200433 = 1650325) B1650325
theorem B2200451 : Blo 1466553 2200451 := bstep (se 1 (by rfl) ⟨1650338, by rfl⟩ : syracuseStep 2200451 = 3300677) B3300677
theorem B1651603 : Blo 1466553 1651603 := bstep (se 1 (by rfl) ⟨1238702, by rfl⟩ : syracuseStep 1651603 = 2477405) B2477405
theorem B2200481 : Blo 1466553 2200481 := bstep (se 2 (by rfl) ⟨825180, by rfl⟩ : syracuseStep 2200481 = 1650361) B1650361
theorem B2200499 : Blo 1466553 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B2200529 : Blo 1466553 2200529 := bstep (se 2 (by rfl) ⟨825198, by rfl⟩ : syracuseStep 2200529 = 1650397) B1650397
theorem B4953041 : Blo 1466553 4953041 := bstep (se 2 (by rfl) ⟨1857390, by rfl⟩ : syracuseStep 4953041 = 3714781) B3714781
theorem B2200547 : Blo 1466553 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B2200577 : Blo 1466553 2200577 := bstep (se 2 (by rfl) ⟨825216, by rfl⟩ : syracuseStep 2200577 = 1650433) B1650433
theorem B1856515 : Blo 1466553 1856515 := bstep (se 1 (by rfl) ⟨1392386, by rfl⟩ : syracuseStep 1856515 = 2784773) B2784773
theorem B3134467 : Blo 1466553 3134467 := bstep (se 1 (by rfl) ⟨2350850, by rfl⟩ : syracuseStep 3134467 = 4701701) B4701701
theorem B2200595 : Blo 1466553 2200595 := bstep (se 1 (by rfl) ⟨1650446, by rfl⟩ : syracuseStep 2200595 = 3300893) B3300893
theorem B1651747 : Blo 1466553 1651747 := bstep (se 1 (by rfl) ⟨1238810, by rfl⟩ : syracuseStep 1651747 = 2477621) B2477621
theorem B2200625 : Blo 1466553 2200625 := bstep (se 2 (by rfl) ⟨825234, by rfl⟩ : syracuseStep 2200625 = 1650469) B1650469
theorem B2200643 : Blo 1466553 2200643 := bstep (se 1 (by rfl) ⟨1650482, by rfl⟩ : syracuseStep 2200643 = 3300965) B3300965
theorem B11138147 : Blo 1466553 11138147 := bstep (se 1 (by rfl) ⟨8353610, by rfl⟩ : syracuseStep 11138147 = 16707221) B16707221
theorem B1856611 : Blo 1466553 1856611 := bstep (se 1 (by rfl) ⟨1392458, by rfl⟩ : syracuseStep 1856611 = 2784917) B2784917
theorem B2200673 : Blo 1466553 2200673 := bstep (se 2 (by rfl) ⟨825252, by rfl⟩ : syracuseStep 2200673 = 1650505) B1650505
theorem B2200691 : Blo 1466553 2200691 := bstep (se 1 (by rfl) ⟨1650518, by rfl⟩ : syracuseStep 2200691 = 3301037) B3301037
theorem B7427213 : Blo 1466553 7427213 := bstep (se 3 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 7427213 = 2785205) B2785205
theorem B2200721 : Blo 1466553 2200721 := bstep (se 2 (by rfl) ⟨825270, by rfl⟩ : syracuseStep 2200721 = 1650541) B1650541
theorem B2200739 : Blo 1466553 2200739 := bstep (se 1 (by rfl) ⟨1650554, by rfl⟩ : syracuseStep 2200739 = 3301109) B3301109
theorem B3814577 : Blo 1466553 3814577 := bstep (se 2 (by rfl) ⟨1430466, by rfl⟩ : syracuseStep 3814577 = 2860933) B2860933
theorem B1651891 : Blo 1466553 1651891 := bstep (se 1 (by rfl) ⟨1238918, by rfl⟩ : syracuseStep 1651891 = 2477837) B2477837
theorem B2200769 : Blo 1466553 2200769 := bstep (se 2 (by rfl) ⟨825288, by rfl⟩ : syracuseStep 2200769 = 1650577) B1650577
theorem B2200787 : Blo 1466553 2200787 := bstep (se 1 (by rfl) ⟨1650590, by rfl⟩ : syracuseStep 2200787 = 3301181) B3301181
theorem B2200817 : Blo 1466553 2200817 := bstep (se 2 (by rfl) ⟨825306, by rfl⟩ : syracuseStep 2200817 = 1650613) B1650613
theorem B2200835 : Blo 1466553 2200835 := bstep (se 1 (by rfl) ⟨1650626, by rfl⟩ : syracuseStep 2200835 = 3301253) B3301253
theorem B9532685 : Blo 1466553 9532685 := bstep (se 3 (by rfl) ⟨1787378, by rfl⟩ : syracuseStep 9532685 = 3574757) B3574757
theorem B2200865 : Blo 1466553 2200865 := bstep (se 2 (by rfl) ⟨825324, by rfl⟩ : syracuseStep 2200865 = 1650649) B1650649
theorem B3437873 : Blo 1466553 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B8361265 : Blo 1466553 8361265 := bstep (se 2 (by rfl) ⟨3135474, by rfl⟩ : syracuseStep 8361265 = 6270949) B6270949
theorem B2200883 : Blo 1466553 2200883 := bstep (se 1 (by rfl) ⟨1650662, by rfl⟩ : syracuseStep 2200883 = 3301325) B3301325
theorem B3716401 : Blo 1466553 3716401 := bstep (se 2 (by rfl) ⟨1393650, by rfl⟩ : syracuseStep 3716401 = 2787301) B2787301
theorem B1652035 : Blo 1466553 1652035 := bstep (se 1 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 1652035 = 2478053) B2478053
theorem B2200913 : Blo 1466553 2200913 := bstep (se 2 (by rfl) ⟨825342, by rfl⟩ : syracuseStep 2200913 = 1650685) B1650685
theorem B2200931 : Blo 1466553 2200931 := bstep (se 1 (by rfl) ⟨1650698, by rfl⟩ : syracuseStep 2200931 = 3301397) B3301397
theorem B2200961 : Blo 1466553 2200961 := bstep (se 2 (by rfl) ⟨825360, by rfl⟩ : syracuseStep 2200961 = 1650721) B1650721
theorem B2200979 : Blo 1466553 2200979 := bstep (se 1 (by rfl) ⟨1650734, by rfl⟩ : syracuseStep 2200979 = 3301469) B3301469
theorem B2201009 : Blo 1466553 2201009 := bstep (se 2 (by rfl) ⟨825378, by rfl⟩ : syracuseStep 2201009 = 1650757) B1650757
theorem B2201027 : Blo 1466553 2201027 := bstep (se 1 (by rfl) ⟨1650770, by rfl⟩ : syracuseStep 2201027 = 3301541) B3301541
theorem B2201057 : Blo 1466553 2201057 := bstep (se 2 (by rfl) ⟨825396, by rfl⟩ : syracuseStep 2201057 = 1650793) B1650793
theorem B4953581 : Blo 1466553 4953581 := bstep (se 3 (by rfl) ⟨928796, by rfl⟩ : syracuseStep 4953581 = 1857593) B1857593
theorem B2201075 : Blo 1466553 2201075 := bstep (se 1 (by rfl) ⟨1650806, by rfl⟩ : syracuseStep 2201075 = 3301613) B3301613
theorem B2201105 : Blo 1466553 2201105 := bstep (se 2 (by rfl) ⟨825414, by rfl⟩ : syracuseStep 2201105 = 1650829) B1650829
theorem B2201123 : Blo 1466553 2201123 := bstep (se 1 (by rfl) ⟨1650842, by rfl⟩ : syracuseStep 2201123 = 3301685) B3301685
theorem B4953635 : Blo 1466553 4953635 := bstep (se 1 (by rfl) ⟨3715226, by rfl⟩ : syracuseStep 4953635 = 7430453) B7430453
theorem B2201153 : Blo 1466553 2201153 := bstep (se 2 (by rfl) ⟨825432, by rfl⟩ : syracuseStep 2201153 = 1650865) B1650865
theorem B3716675 : Blo 1466553 3716675 := bstep (se 1 (by rfl) ⟨2787506, by rfl⟩ : syracuseStep 3716675 = 5575013) B5575013
theorem B1857107 : Blo 1466553 1857107 := bstep (se 1 (by rfl) ⟨1392830, by rfl⟩ : syracuseStep 1857107 = 2785661) B2785661
theorem B2201171 : Blo 1466553 2201171 := bstep (se 1 (by rfl) ⟨1650878, by rfl⟩ : syracuseStep 2201171 = 3301757) B3301757
theorem B2201201 : Blo 1466553 2201201 := bstep (se 2 (by rfl) ⟨825450, by rfl⟩ : syracuseStep 2201201 = 1650901) B1650901
theorem B2201219 : Blo 1466553 2201219 := bstep (se 1 (by rfl) ⟨1650914, by rfl⟩ : syracuseStep 2201219 = 3301829) B3301829
theorem B2201249 : Blo 1466553 2201249 := bstep (se 2 (by rfl) ⟨825468, by rfl⟩ : syracuseStep 2201249 = 1650937) B1650937
theorem B2201267 : Blo 1466553 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B2201297 : Blo 1466553 2201297 := bstep (se 2 (by rfl) ⟨825486, by rfl⟩ : syracuseStep 2201297 = 1650973) B1650973
theorem B2201315 : Blo 1466553 2201315 := bstep (se 1 (by rfl) ⟨1650986, by rfl⟩ : syracuseStep 2201315 = 3301973) B3301973
theorem B2201345 : Blo 1466553 2201345 := bstep (se 2 (by rfl) ⟨825504, by rfl⟩ : syracuseStep 2201345 = 1651009) B1651009
theorem B3716867 : Blo 1466553 3716867 := bstep (se 1 (by rfl) ⟨2787650, by rfl⟩ : syracuseStep 3716867 = 5575301) B5575301
theorem B2201363 : Blo 1466553 2201363 := bstep (se 1 (by rfl) ⟨1651022, by rfl⟩ : syracuseStep 2201363 = 3302045) B3302045
theorem B2201393 : Blo 1466553 2201393 := bstep (se 2 (by rfl) ⟨825522, by rfl⟩ : syracuseStep 2201393 = 1651045) B1651045
theorem B4953905 : Blo 1466553 4953905 := bstep (se 2 (by rfl) ⟨1857714, by rfl⟩ : syracuseStep 4953905 = 3715429) B3715429
theorem B2201411 : Blo 1466553 2201411 := bstep (se 1 (by rfl) ⟨1651058, by rfl⟩ : syracuseStep 2201411 = 3302117) B3302117
theorem B2201441 : Blo 1466553 2201441 := bstep (se 2 (by rfl) ⟨825540, by rfl⟩ : syracuseStep 2201441 = 1651081) B1651081
theorem B2201459 : Blo 1466553 2201459 := bstep (se 1 (by rfl) ⟨1651094, by rfl⟩ : syracuseStep 2201459 = 3302189) B3302189
theorem B2201489 : Blo 1466553 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B2201507 : Blo 1466553 2201507 := bstep (se 1 (by rfl) ⟨1651130, by rfl⟩ : syracuseStep 2201507 = 3302261) B3302261
theorem B2201537 : Blo 1466553 2201537 := bstep (se 2 (by rfl) ⟨825576, by rfl⟩ : syracuseStep 2201537 = 1651153) B1651153
theorem B2201555 : Blo 1466553 2201555 := bstep (se 1 (by rfl) ⟨1651166, by rfl⟩ : syracuseStep 2201555 = 3302333) B3302333
theorem B5568497 : Blo 1466553 5568497 := bstep (se 2 (by rfl) ⟨2088186, by rfl⟩ : syracuseStep 5568497 = 4176373) B4176373
theorem B2201585 : Blo 1466553 2201585 := bstep (se 2 (by rfl) ⟨825594, by rfl⟩ : syracuseStep 2201585 = 1651189) B1651189
theorem B2201603 : Blo 1466553 2201603 := bstep (se 1 (by rfl) ⟨1651202, by rfl⟩ : syracuseStep 2201603 = 3302405) B3302405
theorem B2201633 : Blo 1466553 2201633 := bstep (se 2 (by rfl) ⟨825612, by rfl⟩ : syracuseStep 2201633 = 1651225) B1651225
theorem B4462627 : Blo 1466553 4462627 := bstep (se 1 (by rfl) ⟨3346970, by rfl⟩ : syracuseStep 4462627 = 6693941) B6693941
theorem B2201651 : Blo 1466553 2201651 := bstep (se 1 (by rfl) ⟨1651238, by rfl⟩ : syracuseStep 2201651 = 3302477) B3302477
theorem B2201681 : Blo 1466553 2201681 := bstep (se 2 (by rfl) ⟨825630, by rfl⟩ : syracuseStep 2201681 = 1651261) B1651261
theorem B2201699 : Blo 1466553 2201699 := bstep (se 1 (by rfl) ⟨1651274, by rfl⟩ : syracuseStep 2201699 = 3302549) B3302549
theorem B2201729 : Blo 1466553 2201729 := bstep (se 2 (by rfl) ⟨825648, by rfl⟩ : syracuseStep 2201729 = 1651297) B1651297
theorem B2201747 : Blo 1466553 2201747 := bstep (se 1 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 2201747 = 3302621) B3302621
theorem B2201777 : Blo 1466553 2201777 := bstep (se 2 (by rfl) ⟨825666, by rfl⟩ : syracuseStep 2201777 = 1651333) B1651333
theorem B2201795 : Blo 1466553 2201795 := bstep (se 1 (by rfl) ⟨1651346, by rfl⟩ : syracuseStep 2201795 = 3302693) B3302693
theorem B4700369 : Blo 1466553 4700369 := bstep (se 2 (by rfl) ⟨1762638, by rfl⟩ : syracuseStep 4700369 = 3525277) B3525277
theorem B2201825 : Blo 1466553 2201825 := bstep (se 2 (by rfl) ⟨825684, by rfl⟩ : syracuseStep 2201825 = 1651369) B1651369
theorem B37607651 : Blo 1466553 37607651 := bstep (se 1 (by rfl) ⟨28205738, by rfl⟩ : syracuseStep 37607651 = 56411477) B56411477
theorem B2201843 : Blo 1466553 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B2201873 : Blo 1466553 2201873 := bstep (se 2 (by rfl) ⟨825702, by rfl⟩ : syracuseStep 2201873 = 1651405) B1651405
theorem B1857811 : Blo 1466553 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B2201891 : Blo 1466553 2201891 := bstep (se 1 (by rfl) ⟨1651418, by rfl⟩ : syracuseStep 2201891 = 3302837) B3302837
theorem B2201921 : Blo 1466553 2201921 := bstep (se 2 (by rfl) ⟨825720, by rfl⟩ : syracuseStep 2201921 = 1651441) B1651441
theorem B10041677 : Blo 1466553 10041677 := bstep (se 3 (by rfl) ⟨1882814, by rfl⟩ : syracuseStep 10041677 = 3765629) B3765629
theorem B4954445 : Blo 1466553 4954445 := bstep (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) B1857917
theorem B2201939 : Blo 1466553 2201939 := bstep (se 1 (by rfl) ⟨1651454, by rfl⟩ : syracuseStep 2201939 = 3302909) B3302909
theorem B8927587 : Blo 1466553 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B9525617 : Blo 1466553 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B2201969 : Blo 1466553 2201969 := bstep (se 2 (by rfl) ⟨825738, by rfl⟩ : syracuseStep 2201969 = 1651477) B1651477
theorem B1857907 : Blo 1466553 1857907 := bstep (se 1 (by rfl) ⟨1393430, by rfl⟩ : syracuseStep 1857907 = 2786861) B2786861
theorem B2201987 : Blo 1466553 2201987 := bstep (se 1 (by rfl) ⟨1651490, by rfl⟩ : syracuseStep 2201987 = 3302981) B3302981
theorem B4954499 : Blo 1466553 4954499 := bstep (se 1 (by rfl) ⟨3715874, by rfl⟩ : syracuseStep 4954499 = 7431749) B7431749
theorem B2202017 : Blo 1466553 2202017 := bstep (se 2 (by rfl) ⟨825756, by rfl⟩ : syracuseStep 2202017 = 1651513) B1651513
theorem B4176305 : Blo 1466553 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B2202035 : Blo 1466553 2202035 := bstep (se 1 (by rfl) ⟨1651526, by rfl⟩ : syracuseStep 2202035 = 3303053) B3303053
theorem B2202065 : Blo 1466553 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B3135953 : Blo 1466553 3135953 := bstep (se 2 (by rfl) ⟨1175982, by rfl⟩ : syracuseStep 3135953 = 2351965) B2351965
theorem B2202083 : Blo 1466553 2202083 := bstep (se 1 (by rfl) ⟨1651562, by rfl⟩ : syracuseStep 2202083 = 3303125) B3303125
theorem B3135971 : Blo 1466553 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B2202113 : Blo 1466553 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B2202131 : Blo 1466553 2202131 := bstep (se 1 (by rfl) ⟨1651598, by rfl⟩ : syracuseStep 2202131 = 3303197) B3303197
theorem B2202161 : Blo 1466553 2202161 := bstep (se 2 (by rfl) ⟨825810, by rfl⟩ : syracuseStep 2202161 = 1651621) B1651621
theorem B77290037 : Blo 1466553 77290037 := bstep (se 5 (by rfl) ⟨3622970, by rfl⟩ : syracuseStep 77290037 = 7245941) B7245941
theorem B2202179 : Blo 1466553 2202179 := bstep (se 1 (by rfl) ⟨1651634, by rfl⟩ : syracuseStep 2202179 = 3303269) B3303269
theorem B3299921 : Blo 1466553 3299921 := bstep (se 2 (by rfl) ⟨1237470, by rfl⟩ : syracuseStep 3299921 = 2474941) B2474941
theorem B2202209 : Blo 1466553 2202209 := bstep (se 2 (by rfl) ⟨825828, by rfl⟩ : syracuseStep 2202209 = 1651657) B1651657
theorem B3299939 : Blo 1466553 3299939 := bstep (se 1 (by rfl) ⟨2474954, by rfl⟩ : syracuseStep 3299939 = 4949909) B4949909
theorem B2202227 : Blo 1466553 2202227 := bstep (se 1 (by rfl) ⟨1651670, by rfl⟩ : syracuseStep 2202227 = 3303341) B3303341
theorem B4954769 : Blo 1466553 4954769 := bstep (se 2 (by rfl) ⟨1858038, by rfl⟩ : syracuseStep 4954769 = 3716077) B3716077
theorem B2202257 : Blo 1466553 2202257 := bstep (se 2 (by rfl) ⟨825846, by rfl⟩ : syracuseStep 2202257 = 1651693) B1651693
theorem B2202275 : Blo 1466553 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B2202305 : Blo 1466553 2202305 := bstep (se 2 (by rfl) ⟨825864, by rfl⟩ : syracuseStep 2202305 = 1651729) B1651729
theorem B8354501 : Blo 1466553 8354501 := bstep (se 4 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 8354501 = 1566469) B1566469
theorem B2202323 : Blo 1466553 2202323 := bstep (se 1 (by rfl) ⟨1651742, by rfl⟩ : syracuseStep 2202323 = 3303485) B3303485
theorem B8362723 : Blo 1466553 8362723 := bstep (se 1 (by rfl) ⟨6272042, by rfl⟩ : syracuseStep 8362723 = 12544085) B12544085
theorem B2202353 : Blo 1466553 2202353 := bstep (se 2 (by rfl) ⟨825882, by rfl⟩ : syracuseStep 2202353 = 1651765) B1651765
theorem B2202371 : Blo 1466553 2202371 := bstep (se 1 (by rfl) ⟨1651778, by rfl⟩ : syracuseStep 2202371 = 3303557) B3303557
theorem B3767057 : Blo 1466553 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2202401 : Blo 1466553 2202401 := bstep (se 2 (by rfl) ⟨825900, by rfl⟩ : syracuseStep 2202401 = 1651801) B1651801
theorem B2202419 : Blo 1466553 2202419 := bstep (se 1 (by rfl) ⟨1651814, by rfl⟩ : syracuseStep 2202419 = 3303629) B3303629
theorem B2202449 : Blo 1466553 2202449 := bstep (se 2 (by rfl) ⟨825918, by rfl⟩ : syracuseStep 2202449 = 1651837) B1651837
theorem B2202467 : Blo 1466553 2202467 := bstep (se 1 (by rfl) ⟨1651850, by rfl⟩ : syracuseStep 2202467 = 3303701) B3303701
theorem B1858403 : Blo 1466553 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B3300209 : Blo 1466553 3300209 := bstep (se 2 (by rfl) ⟨1237578, by rfl⟩ : syracuseStep 3300209 = 2475157) B2475157
theorem B2202497 : Blo 1466553 2202497 := bstep (se 2 (by rfl) ⟨825936, by rfl⟩ : syracuseStep 2202497 = 1651873) B1651873
theorem B3300227 : Blo 1466553 3300227 := bstep (se 1 (by rfl) ⟨2475170, by rfl⟩ : syracuseStep 3300227 = 4950341) B4950341
theorem B2202515 : Blo 1466553 2202515 := bstep (se 1 (by rfl) ⟨1651886, by rfl⟩ : syracuseStep 2202515 = 3303773) B3303773
theorem B2202545 : Blo 1466553 2202545 := bstep (se 2 (by rfl) ⟨825954, by rfl⟩ : syracuseStep 2202545 = 1651909) B1651909
theorem B2202563 : Blo 1466553 2202563 := bstep (se 1 (by rfl) ⟨1651922, by rfl⟩ : syracuseStep 2202563 = 3303845) B3303845
theorem B81476549 : Blo 1466553 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B2202593 : Blo 1466553 2202593 := bstep (se 2 (by rfl) ⟨825972, by rfl⟩ : syracuseStep 2202593 = 1651945) B1651945
theorem B2202611 : Blo 1466553 2202611 := bstep (se 1 (by rfl) ⟨1651958, by rfl⟩ : syracuseStep 2202611 = 3303917) B3303917
theorem B2202641 : Blo 1466553 2202641 := bstep (se 2 (by rfl) ⟨825990, by rfl⟩ : syracuseStep 2202641 = 1651981) B1651981
theorem B7928867 : Blo 1466553 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B2202659 : Blo 1466553 2202659 := bstep (se 1 (by rfl) ⟨1651994, by rfl⟩ : syracuseStep 2202659 = 3303989) B3303989
theorem B2202689 : Blo 1466553 2202689 := bstep (se 2 (by rfl) ⟨826008, by rfl⟩ : syracuseStep 2202689 = 1652017) B1652017
theorem B2202707 : Blo 1466553 2202707 := bstep (se 1 (by rfl) ⟨1652030, by rfl⟩ : syracuseStep 2202707 = 3304061) B3304061
theorem B2202737 : Blo 1466553 2202737 := bstep (se 2 (by rfl) ⟨826026, by rfl⟩ : syracuseStep 2202737 = 1652053) B1652053
theorem B2202755 : Blo 1466553 2202755 := bstep (se 1 (by rfl) ⟨1652066, by rfl⟩ : syracuseStep 2202755 = 3304133) B3304133
theorem B13565069 : Blo 1466553 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B12532877 : Blo 1466553 12532877 := bstep (se 3 (by rfl) ⟨2349914, by rfl⟩ : syracuseStep 12532877 = 4699829) B4699829
theorem B3300497 : Blo 1466553 3300497 := bstep (se 2 (by rfl) ⟨1237686, by rfl⟩ : syracuseStep 3300497 = 2475373) B2475373
theorem B2202785 : Blo 1466553 2202785 := bstep (se 2 (by rfl) ⟨826044, by rfl⟩ : syracuseStep 2202785 = 1652089) B1652089
theorem B3300515 : Blo 1466553 3300515 := bstep (se 1 (by rfl) ⟨2475386, by rfl⟩ : syracuseStep 3300515 = 4950773) B4950773
theorem B4955309 : Blo 1466553 4955309 := bstep (se 3 (by rfl) ⟨929120, by rfl⟩ : syracuseStep 4955309 = 1858241) B1858241
theorem B2202803 : Blo 1466553 2202803 := bstep (se 1 (by rfl) ⟨1652102, by rfl⟩ : syracuseStep 2202803 = 3304205) B3304205
theorem B4955363 : Blo 1466553 4955363 := bstep (se 1 (by rfl) ⟨3716522, by rfl⟩ : syracuseStep 4955363 = 7433045) B7433045
theorem B8363249 : Blo 1466553 8363249 := bstep (se 2 (by rfl) ⟨3136218, by rfl⟩ : syracuseStep 8363249 = 6272437) B6272437
theorem B80321813 : Blo 1466553 80321813 := bstep (se 6 (by rfl) ⟨1882542, by rfl⟩ : syracuseStep 80321813 = 3765085) B3765085
theorem B4234531 : Blo 1466553 4234531 := bstep (se 1 (by rfl) ⟨3175898, by rfl⟩ : syracuseStep 4234531 = 6351797) B6351797
theorem B2088289 : Blo 1466553 2088289 := bstep (se 2 (by rfl) ⟨783108, by rfl⟩ : syracuseStep 2088289 = 1566217) B1566217
theorem B4177261 : Blo 1466553 4177261 := bstep (se 3 (by rfl) ⟨783236, by rfl⟩ : syracuseStep 4177261 = 1566473) B1566473
theorem B6970765 : Blo 1466553 6970765 := bstep (se 3 (by rfl) ⟨1307018, by rfl⟩ : syracuseStep 6970765 = 2614037) B2614037
theorem B5569955 : Blo 1466553 5569955 := bstep (se 1 (by rfl) ⟨4177466, by rfl⟩ : syracuseStep 5569955 = 8354933) B8354933
theorem B2784689 : Blo 1466553 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B3300785 : Blo 1466553 3300785 := bstep (se 2 (by rfl) ⟨1237794, by rfl⟩ : syracuseStep 3300785 = 2475589) B2475589
theorem B3300803 : Blo 1466553 3300803 := bstep (se 1 (by rfl) ⟨2475602, by rfl⟩ : syracuseStep 3300803 = 4951205) B4951205
theorem B4955633 : Blo 1466553 4955633 := bstep (se 2 (by rfl) ⟨1858362, by rfl⟩ : syracuseStep 4955633 = 3716725) B3716725
theorem B2350595 : Blo 1466553 2350595 := bstep (se 1 (by rfl) ⟨1762946, by rfl⟩ : syracuseStep 2350595 = 3525893) B3525893
theorem B4177489 : Blo 1466553 4177489 := bstep (se 2 (by rfl) ⟨1566558, by rfl⟩ : syracuseStep 4177489 = 3133117) B3133117
theorem B2449073 : Blo 1466553 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B3301073 : Blo 1466553 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B3301091 : Blo 1466553 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B4177649 : Blo 1466553 4177649 := bstep (se 2 (by rfl) ⟨1566618, by rfl⟩ : syracuseStep 4177649 = 3133237) B3133237
theorem B2350883 : Blo 1466553 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B11894627 : Blo 1466553 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B4177763 : Blo 1466553 4177763 := bstep (se 1 (by rfl) ⟨3133322, by rfl⟩ : syracuseStep 4177763 = 6266645) B6266645
theorem B3964781 : Blo 1466553 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B5021549 : Blo 1466553 5021549 := bstep (se 3 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 5021549 = 1883081) B1883081
theorem B4235171 : Blo 1466553 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B3301361 : Blo 1466553 3301361 := bstep (se 2 (by rfl) ⟨1238010, by rfl⟩ : syracuseStep 3301361 = 2476021) B2476021
theorem B7430129 : Blo 1466553 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B3301451 : Blo 1466553 3301451 := bstep (se 1 (by rfl) ⟨2476088, by rfl⟩ : syracuseStep 3301451 = 4952177) B4952177
theorem B5570653 : Blo 1466553 5570653 := bstep (se 3 (by rfl) ⟨1044497, by rfl⟩ : syracuseStep 5570653 = 2088995) B2088995
theorem B3301505 : Blo 1466553 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B12533939 : Blo 1466553 12533939 := bstep (se 1 (by rfl) ⟨9400454, by rfl⟩ : syracuseStep 12533939 = 18800909) B18800909
theorem B1466571 : Blo 1466553 1466571 := bstep (se 1 (by rfl) ⟨1099928, by rfl⟩ : syracuseStep 1466571 = 2199857) B2199857
theorem B1466583 : Blo 1466553 1466583 := bstep (se 1 (by rfl) ⟨1099937, by rfl⟩ : syracuseStep 1466583 = 2199875) B2199875
theorem B1466603 : Blo 1466553 1466603 := bstep (se 1 (by rfl) ⟨1099952, by rfl⟩ : syracuseStep 1466603 = 2199905) B2199905
theorem B1466615 : Blo 1466553 1466615 := bstep (se 1 (by rfl) ⟨1099961, by rfl⟩ : syracuseStep 1466615 = 2199923) B2199923
theorem B1466635 : Blo 1466553 1466635 := bstep (se 1 (by rfl) ⟨1099976, by rfl⟩ : syracuseStep 1466635 = 2199953) B2199953
theorem B1466647 : Blo 1466553 1466647 := bstep (se 1 (by rfl) ⟨1099985, by rfl⟩ : syracuseStep 1466647 = 2199971) B2199971
theorem B1466667 : Blo 1466553 1466667 := bstep (se 1 (by rfl) ⟨1100000, by rfl⟩ : syracuseStep 1466667 = 2200001) B2200001
theorem B1466679 : Blo 1466553 1466679 := bstep (se 1 (by rfl) ⟨1100009, by rfl⟩ : syracuseStep 1466679 = 2200019) B2200019
theorem B1466699 : Blo 1466553 1466699 := bstep (se 1 (by rfl) ⟨1100024, by rfl⟩ : syracuseStep 1466699 = 2200049) B2200049
theorem B1466711 : Blo 1466553 1466711 := bstep (se 1 (by rfl) ⟨1100033, by rfl⟩ : syracuseStep 1466711 = 2200067) B2200067
theorem B2351447 : Blo 1466553 2351447 := bstep (se 1 (by rfl) ⟨1763585, by rfl⟩ : syracuseStep 2351447 = 3527171) B3527171
theorem B3301721 : Blo 1466553 3301721 := bstep (se 2 (by rfl) ⟨1238145, by rfl⟩ : syracuseStep 3301721 = 2476291) B2476291
theorem B12542309 : Blo 1466553 12542309 := bstep (se 4 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 12542309 = 2351683) B2351683
theorem B1466731 : Blo 1466553 1466731 := bstep (se 1 (by rfl) ⟨1100048, by rfl⟩ : syracuseStep 1466731 = 2200097) B2200097
theorem B21152117 : Blo 1466553 21152117 := bstep (se 5 (by rfl) ⟨991505, by rfl⟩ : syracuseStep 21152117 = 1983011) B1983011
theorem B1466743 : Blo 1466553 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B1466763 : Blo 1466553 1466763 := bstep (se 1 (by rfl) ⟨1100072, by rfl⟩ : syracuseStep 1466763 = 2200145) B2200145
theorem B1466775 : Blo 1466553 1466775 := bstep (se 1 (by rfl) ⟨1100081, by rfl⟩ : syracuseStep 1466775 = 2200163) B2200163
theorem B1466795 : Blo 1466553 1466795 := bstep (se 1 (by rfl) ⟨1100096, by rfl⟩ : syracuseStep 1466795 = 2200193) B2200193
theorem B21447089 : Blo 1466553 21447089 := bstep (se 2 (by rfl) ⟨8042658, by rfl⟩ : syracuseStep 21447089 = 16085317) B16085317
theorem B23806385 : Blo 1466553 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B3301811 : Blo 1466553 3301811 := bstep (se 1 (by rfl) ⟨2476358, by rfl⟩ : syracuseStep 3301811 = 4952717) B4952717
theorem B1466807 : Blo 1466553 1466807 := bstep (se 1 (by rfl) ⟨1100105, by rfl⟩ : syracuseStep 1466807 = 2200211) B2200211
theorem B6029761 : Blo 1466553 6029761 := bstep (se 2 (by rfl) ⟨2261160, by rfl⟩ : syracuseStep 6029761 = 4522321) B4522321
theorem B1466827 : Blo 1466553 1466827 := bstep (se 1 (by rfl) ⟨1100120, by rfl⟩ : syracuseStep 1466827 = 2200241) B2200241
theorem B1466839 : Blo 1466553 1466839 := bstep (se 1 (by rfl) ⟨1100129, by rfl⟩ : syracuseStep 1466839 = 2200259) B2200259
theorem B3301847 : Blo 1466553 3301847 := bstep (se 1 (by rfl) ⟨2476385, by rfl⟩ : syracuseStep 3301847 = 4952771) B4952771
theorem B11903449 : Blo 1466553 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B1466859 : Blo 1466553 1466859 := bstep (se 1 (by rfl) ⟨1100144, by rfl⟩ : syracuseStep 1466859 = 2200289) B2200289
theorem B1466871 : Blo 1466553 1466871 := bstep (se 1 (by rfl) ⟨1100153, by rfl⟩ : syracuseStep 1466871 = 2200307) B2200307
theorem B6267395 : Blo 1466553 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B1466891 : Blo 1466553 1466891 := bstep (se 1 (by rfl) ⟨1100168, by rfl⟩ : syracuseStep 1466891 = 2200337) B2200337
theorem B1466903 : Blo 1466553 1466903 := bstep (se 1 (by rfl) ⟨1100177, by rfl⟩ : syracuseStep 1466903 = 2200355) B2200355
theorem B1466923 : Blo 1466553 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B2785843 : Blo 1466553 2785843 := bstep (se 1 (by rfl) ⟨2089382, by rfl⟩ : syracuseStep 2785843 = 4178765) B4178765
theorem B1466935 : Blo 1466553 1466935 := bstep (se 1 (by rfl) ⟨1100201, by rfl⟩ : syracuseStep 1466935 = 2200403) B2200403
theorem B1466955 : Blo 1466553 1466955 := bstep (se 1 (by rfl) ⟨1100216, by rfl⟩ : syracuseStep 1466955 = 2200433) B2200433
theorem B1466967 : Blo 1466553 1466967 := bstep (se 1 (by rfl) ⟨1100225, by rfl⟩ : syracuseStep 1466967 = 2200451) B2200451
theorem B1466987 : Blo 1466553 1466987 := bstep (se 1 (by rfl) ⟨1100240, by rfl⟩ : syracuseStep 1466987 = 2200481) B2200481
theorem B1466999 : Blo 1466553 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1467019 : Blo 1466553 1467019 := bstep (se 1 (by rfl) ⟨1100264, by rfl⟩ : syracuseStep 1467019 = 2200529) B2200529
theorem B3302027 : Blo 1466553 3302027 := bstep (se 1 (by rfl) ⟨2476520, by rfl⟩ : syracuseStep 3302027 = 4953041) B4953041
theorem B1467031 : Blo 1466553 1467031 := bstep (se 1 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 1467031 = 2200547) B2200547
theorem B1467051 : Blo 1466553 1467051 := bstep (se 1 (by rfl) ⟨1100288, by rfl⟩ : syracuseStep 1467051 = 2200577) B2200577
theorem B1467063 : Blo 1466553 1467063 := bstep (se 1 (by rfl) ⟨1100297, by rfl⟩ : syracuseStep 1467063 = 2200595) B2200595
theorem B3302081 : Blo 1466553 3302081 := bstep (se 2 (by rfl) ⟨1238280, by rfl⟩ : syracuseStep 3302081 = 2476561) B2476561
theorem B1467083 : Blo 1466553 1467083 := bstep (se 1 (by rfl) ⟨1100312, by rfl⟩ : syracuseStep 1467083 = 2200625) B2200625
theorem B25420493 : Blo 1466553 25420493 := bstep (se 3 (by rfl) ⟨4766342, by rfl⟩ : syracuseStep 25420493 = 9532685) B9532685
theorem B1467095 : Blo 1466553 1467095 := bstep (se 1 (by rfl) ⟨1100321, by rfl⟩ : syracuseStep 1467095 = 2200643) B2200643
theorem B1467115 : Blo 1466553 1467115 := bstep (se 1 (by rfl) ⟨1100336, by rfl⟩ : syracuseStep 1467115 = 2200673) B2200673
theorem B1467127 : Blo 1466553 1467127 := bstep (se 1 (by rfl) ⟨1100345, by rfl⟩ : syracuseStep 1467127 = 2200691) B2200691
theorem B1467147 : Blo 1466553 1467147 := bstep (se 1 (by rfl) ⟨1100360, by rfl⟩ : syracuseStep 1467147 = 2200721) B2200721
theorem B1467159 : Blo 1466553 1467159 := bstep (se 1 (by rfl) ⟨1100369, by rfl⟩ : syracuseStep 1467159 = 2200739) B2200739
theorem B2786071 : Blo 1466553 2786071 := bstep (se 1 (by rfl) ⟨2089553, by rfl⟩ : syracuseStep 2786071 = 4179107) B4179107
theorem B1467179 : Blo 1466553 1467179 := bstep (se 1 (by rfl) ⟨1100384, by rfl⟩ : syracuseStep 1467179 = 2200769) B2200769
theorem B1467191 : Blo 1466553 1467191 := bstep (se 1 (by rfl) ⟨1100393, by rfl⟩ : syracuseStep 1467191 = 2200787) B2200787
theorem B1467211 : Blo 1466553 1467211 := bstep (se 1 (by rfl) ⟨1100408, by rfl⟩ : syracuseStep 1467211 = 2200817) B2200817
theorem B1467223 : Blo 1466553 1467223 := bstep (se 1 (by rfl) ⟨1100417, by rfl⟩ : syracuseStep 1467223 = 2200835) B2200835
theorem B8356709 : Blo 1466553 8356709 := bstep (se 4 (by rfl) ⟨783441, by rfl⟩ : syracuseStep 8356709 = 1566883) B1566883
theorem B1467243 : Blo 1466553 1467243 := bstep (se 1 (by rfl) ⟨1100432, by rfl⟩ : syracuseStep 1467243 = 2200865) B2200865
theorem B1467255 : Blo 1466553 1467255 := bstep (se 1 (by rfl) ⟨1100441, by rfl⟩ : syracuseStep 1467255 = 2200883) B2200883
theorem B2786177 : Blo 1466553 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B1467275 : Blo 1466553 1467275 := bstep (se 1 (by rfl) ⟨1100456, by rfl⟩ : syracuseStep 1467275 = 2200913) B2200913
theorem B1467287 : Blo 1466553 1467287 := bstep (se 1 (by rfl) ⟨1100465, by rfl⟩ : syracuseStep 1467287 = 2200931) B2200931
theorem B3302297 : Blo 1466553 3302297 := bstep (se 2 (by rfl) ⟨1238361, by rfl⟩ : syracuseStep 3302297 = 2476723) B2476723
theorem B1467307 : Blo 1466553 1467307 := bstep (se 1 (by rfl) ⟨1100480, by rfl⟩ : syracuseStep 1467307 = 2200961) B2200961
theorem B1467319 : Blo 1466553 1467319 := bstep (se 1 (by rfl) ⟨1100489, by rfl⟩ : syracuseStep 1467319 = 2200979) B2200979
theorem B1467339 : Blo 1466553 1467339 := bstep (se 1 (by rfl) ⟨1100504, by rfl⟩ : syracuseStep 1467339 = 2201009) B2201009
theorem B4178891 : Blo 1466553 4178891 := bstep (se 1 (by rfl) ⟨3134168, by rfl⟩ : syracuseStep 4178891 = 6268337) B6268337
theorem B1467351 : Blo 1466553 1467351 := bstep (se 1 (by rfl) ⟨1100513, by rfl⟩ : syracuseStep 1467351 = 2201027) B2201027
theorem B25084889 : Blo 1466553 25084889 := bstep (se 2 (by rfl) ⟨9406833, by rfl⟩ : syracuseStep 25084889 = 18813667) B18813667
theorem B11150297 : Blo 1466553 11150297 := bstep (se 2 (by rfl) ⟨4181361, by rfl⟩ : syracuseStep 11150297 = 8362723) B8362723
theorem B1467371 : Blo 1466553 1467371 := bstep (se 1 (by rfl) ⟨1100528, by rfl⟩ : syracuseStep 1467371 = 2201057) B2201057
theorem B3302387 : Blo 1466553 3302387 := bstep (se 1 (by rfl) ⟨2476790, by rfl⟩ : syracuseStep 3302387 = 4953581) B4953581
theorem B1467383 : Blo 1466553 1467383 := bstep (se 1 (by rfl) ⟨1100537, by rfl⟩ : syracuseStep 1467383 = 2201075) B2201075
theorem B1467403 : Blo 1466553 1467403 := bstep (se 1 (by rfl) ⟨1100552, by rfl⟩ : syracuseStep 1467403 = 2201105) B2201105
theorem B1467415 : Blo 1466553 1467415 := bstep (se 1 (by rfl) ⟨1100561, by rfl⟩ : syracuseStep 1467415 = 2201123) B2201123
theorem B3302423 : Blo 1466553 3302423 := bstep (se 1 (by rfl) ⟨2476817, by rfl⟩ : syracuseStep 3302423 = 4953635) B4953635
theorem B2786329 : Blo 1466553 2786329 := bstep (se 2 (by rfl) ⟨1044873, by rfl⟩ : syracuseStep 2786329 = 2089747) B2089747
theorem B2090009 : Blo 1466553 2090009 := bstep (se 2 (by rfl) ⟨783753, by rfl⟩ : syracuseStep 2090009 = 1567507) B1567507
theorem B1467435 : Blo 1466553 1467435 := bstep (se 1 (by rfl) ⟨1100576, by rfl⟩ : syracuseStep 1467435 = 2201153) B2201153
theorem B1467447 : Blo 1466553 1467447 := bstep (se 1 (by rfl) ⟨1100585, by rfl⟩ : syracuseStep 1467447 = 2201171) B2201171
theorem B2475083 : Blo 1466553 2475083 := bstep (se 1 (by rfl) ⟨1856312, by rfl⟩ : syracuseStep 2475083 = 3712625) B3712625
theorem B1467467 : Blo 1466553 1467467 := bstep (se 1 (by rfl) ⟨1100600, by rfl⟩ : syracuseStep 1467467 = 2201201) B2201201
theorem B1467479 : Blo 1466553 1467479 := bstep (se 1 (by rfl) ⟨1100609, by rfl⟩ : syracuseStep 1467479 = 2201219) B2201219
theorem B1467499 : Blo 1466553 1467499 := bstep (se 1 (by rfl) ⟨1100624, by rfl⟩ : syracuseStep 1467499 = 2201249) B2201249
theorem B1467511 : Blo 1466553 1467511 := bstep (se 1 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 1467511 = 2201267) B2201267
theorem B1467531 : Blo 1466553 1467531 := bstep (se 1 (by rfl) ⟨1100648, by rfl⟩ : syracuseStep 1467531 = 2201297) B2201297
theorem B1467543 : Blo 1466553 1467543 := bstep (se 1 (by rfl) ⟨1100657, by rfl⟩ : syracuseStep 1467543 = 2201315) B2201315
theorem B1467563 : Blo 1466553 1467563 := bstep (se 1 (by rfl) ⟨1100672, by rfl⟩ : syracuseStep 1467563 = 2201345) B2201345
theorem B1467575 : Blo 1466553 1467575 := bstep (se 1 (by rfl) ⟨1100681, by rfl⟩ : syracuseStep 1467575 = 2201363) B2201363
theorem B2475211 : Blo 1466553 2475211 := bstep (se 1 (by rfl) ⟨1856408, by rfl⟩ : syracuseStep 2475211 = 3712817) B3712817
theorem B1467595 : Blo 1466553 1467595 := bstep (se 1 (by rfl) ⟨1100696, by rfl⟩ : syracuseStep 1467595 = 2201393) B2201393
theorem B3302603 : Blo 1466553 3302603 := bstep (se 1 (by rfl) ⟨2476952, by rfl⟩ : syracuseStep 3302603 = 4953905) B4953905
theorem B1467607 : Blo 1466553 1467607 := bstep (se 1 (by rfl) ⟨1100705, by rfl⟩ : syracuseStep 1467607 = 2201411) B2201411
theorem B1467627 : Blo 1466553 1467627 := bstep (se 1 (by rfl) ⟨1100720, by rfl⟩ : syracuseStep 1467627 = 2201441) B2201441
theorem B1467639 : Blo 1466553 1467639 := bstep (se 1 (by rfl) ⟨1100729, by rfl⟩ : syracuseStep 1467639 = 2201459) B2201459
theorem B3302657 : Blo 1466553 3302657 := bstep (se 2 (by rfl) ⟨1238496, by rfl⟩ : syracuseStep 3302657 = 2476993) B2476993
theorem B1467659 : Blo 1466553 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B1467671 : Blo 1466553 1467671 := bstep (se 1 (by rfl) ⟨1100753, by rfl⟩ : syracuseStep 1467671 = 2201507) B2201507
theorem B1467691 : Blo 1466553 1467691 := bstep (se 1 (by rfl) ⟨1100768, by rfl⟩ : syracuseStep 1467691 = 2201537) B2201537
theorem B8357165 : Blo 1466553 8357165 := bstep (se 3 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 8357165 = 3133937) B3133937
theorem B1467703 : Blo 1466553 1467703 := bstep (se 1 (by rfl) ⟨1100777, by rfl⟩ : syracuseStep 1467703 = 2201555) B2201555
theorem B3712331 : Blo 1466553 3712331 := bstep (se 1 (by rfl) ⟨2784248, by rfl⟩ : syracuseStep 3712331 = 5568497) B5568497
theorem B1467723 : Blo 1466553 1467723 := bstep (se 1 (by rfl) ⟨1100792, by rfl⟩ : syracuseStep 1467723 = 2201585) B2201585
theorem B1467735 : Blo 1466553 1467735 := bstep (se 1 (by rfl) ⟨1100801, by rfl⟩ : syracuseStep 1467735 = 2201603) B2201603
theorem B2475353 : Blo 1466553 2475353 := bstep (se 2 (by rfl) ⟨928257, by rfl⟩ : syracuseStep 2475353 = 1856515) B1856515
theorem B5571929 : Blo 1466553 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B4179289 : Blo 1466553 4179289 := bstep (se 2 (by rfl) ⟨1567233, by rfl⟩ : syracuseStep 4179289 = 3134467) B3134467
theorem B1467755 : Blo 1466553 1467755 := bstep (se 1 (by rfl) ⟨1100816, by rfl⟩ : syracuseStep 1467755 = 2201633) B2201633
theorem B1467767 : Blo 1466553 1467767 := bstep (se 1 (by rfl) ⟨1100825, by rfl⟩ : syracuseStep 1467767 = 2201651) B2201651
theorem B1467787 : Blo 1466553 1467787 := bstep (se 1 (by rfl) ⟨1100840, by rfl⟩ : syracuseStep 1467787 = 2201681) B2201681
theorem B1467799 : Blo 1466553 1467799 := bstep (se 1 (by rfl) ⟨1100849, by rfl⟩ : syracuseStep 1467799 = 2201699) B2201699
theorem B1467819 : Blo 1466553 1467819 := bstep (se 1 (by rfl) ⟨1100864, by rfl⟩ : syracuseStep 1467819 = 2201729) B2201729
theorem B1467831 : Blo 1466553 1467831 := bstep (se 1 (by rfl) ⟨1100873, by rfl⟩ : syracuseStep 1467831 = 2201747) B2201747
theorem B1467851 : Blo 1466553 1467851 := bstep (se 1 (by rfl) ⟨1100888, by rfl⟩ : syracuseStep 1467851 = 2201777) B2201777
theorem B1467863 : Blo 1466553 1467863 := bstep (se 1 (by rfl) ⟨1100897, by rfl⟩ : syracuseStep 1467863 = 2201795) B2201795
theorem B2475481 : Blo 1466553 2475481 := bstep (se 2 (by rfl) ⟨928305, by rfl⟩ : syracuseStep 2475481 = 1856611) B1856611
theorem B7931353 : Blo 1466553 7931353 := bstep (se 2 (by rfl) ⟨2974257, by rfl⟩ : syracuseStep 7931353 = 5948515) B5948515
theorem B3302873 : Blo 1466553 3302873 := bstep (se 2 (by rfl) ⟨1238577, by rfl⟩ : syracuseStep 3302873 = 2477155) B2477155
theorem B1467883 : Blo 1466553 1467883 := bstep (se 1 (by rfl) ⟨1100912, by rfl⟩ : syracuseStep 1467883 = 2201825) B2201825
theorem B1467895 : Blo 1466553 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B1467915 : Blo 1466553 1467915 := bstep (se 1 (by rfl) ⟨1100936, by rfl⟩ : syracuseStep 1467915 = 2201873) B2201873
theorem B1467927 : Blo 1466553 1467927 := bstep (se 1 (by rfl) ⟨1100945, by rfl⟩ : syracuseStep 1467927 = 2201891) B2201891
theorem B1467947 : Blo 1466553 1467947 := bstep (se 1 (by rfl) ⟨1100960, by rfl⟩ : syracuseStep 1467947 = 2201921) B2201921
theorem B6694451 : Blo 1466553 6694451 := bstep (se 1 (by rfl) ⟨5020838, by rfl⟩ : syracuseStep 6694451 = 10041677) B10041677
theorem B3302963 : Blo 1466553 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B1467959 : Blo 1466553 1467959 := bstep (se 1 (by rfl) ⟨1100969, by rfl⟩ : syracuseStep 1467959 = 2201939) B2201939
theorem B6350411 : Blo 1466553 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B1467979 : Blo 1466553 1467979 := bstep (se 1 (by rfl) ⟨1100984, by rfl⟩ : syracuseStep 1467979 = 2201969) B2201969
theorem B1467991 : Blo 1466553 1467991 := bstep (se 1 (by rfl) ⟨1100993, by rfl⟩ : syracuseStep 1467991 = 2201987) B2201987
theorem B3302999 : Blo 1466553 3302999 := bstep (se 1 (by rfl) ⟨2477249, by rfl⟩ : syracuseStep 3302999 = 4954499) B4954499
theorem B1468011 : Blo 1466553 1468011 := bstep (se 1 (by rfl) ⟨1101008, by rfl⟩ : syracuseStep 1468011 = 2202017) B2202017
theorem B1468023 : Blo 1466553 1468023 := bstep (se 1 (by rfl) ⟨1101017, by rfl⟩ : syracuseStep 1468023 = 2202035) B2202035
theorem B1468043 : Blo 1466553 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B1468055 : Blo 1466553 1468055 := bstep (se 1 (by rfl) ⟨1101041, by rfl⟩ : syracuseStep 1468055 = 2202083) B2202083
theorem B2090647 : Blo 1466553 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1468075 : Blo 1466553 1468075 := bstep (se 1 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 1468075 = 2202113) B2202113
theorem B1468087 : Blo 1466553 1468087 := bstep (se 1 (by rfl) ⟨1101065, by rfl⟩ : syracuseStep 1468087 = 2202131) B2202131
theorem B1468107 : Blo 1466553 1468107 := bstep (se 1 (by rfl) ⟨1101080, by rfl⟩ : syracuseStep 1468107 = 2202161) B2202161
theorem B1468119 : Blo 1466553 1468119 := bstep (se 1 (by rfl) ⟨1101089, by rfl⟩ : syracuseStep 1468119 = 2202179) B2202179
theorem B5646041 : Blo 1466553 5646041 := bstep (se 2 (by rfl) ⟨2117265, by rfl⟩ : syracuseStep 5646041 = 4234531) B4234531
theorem B1468139 : Blo 1466553 1468139 := bstep (se 1 (by rfl) ⟨1101104, by rfl⟩ : syracuseStep 1468139 = 2202209) B2202209
theorem B1468151 : Blo 1466553 1468151 := bstep (se 1 (by rfl) ⟨1101113, by rfl⟩ : syracuseStep 1468151 = 2202227) B2202227
theorem B3303179 : Blo 1466553 3303179 := bstep (se 1 (by rfl) ⟨2477384, by rfl⟩ : syracuseStep 3303179 = 4954769) B4954769
theorem B1468171 : Blo 1466553 1468171 := bstep (se 1 (by rfl) ⟨1101128, by rfl⟩ : syracuseStep 1468171 = 2202257) B2202257
theorem B1468183 : Blo 1466553 1468183 := bstep (se 1 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 1468183 = 2202275) B2202275
theorem B1468203 : Blo 1466553 1468203 := bstep (se 1 (by rfl) ⟨1101152, by rfl⟩ : syracuseStep 1468203 = 2202305) B2202305
theorem B6530861 : Blo 1466553 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B1468215 : Blo 1466553 1468215 := bstep (se 1 (by rfl) ⟨1101161, by rfl⟩ : syracuseStep 1468215 = 2202323) B2202323
theorem B3303233 : Blo 1466553 3303233 := bstep (se 2 (by rfl) ⟨1238712, by rfl⟩ : syracuseStep 3303233 = 2477425) B2477425
theorem B1468235 : Blo 1466553 1468235 := bstep (se 1 (by rfl) ⟨1101176, by rfl⟩ : syracuseStep 1468235 = 2202353) B2202353
theorem B1673047 : Blo 1466553 1673047 := bstep (se 1 (by rfl) ⟨1254785, by rfl⟩ : syracuseStep 1673047 = 2509571) B2509571
theorem B1468247 : Blo 1466553 1468247 := bstep (se 1 (by rfl) ⟨1101185, by rfl⟩ : syracuseStep 1468247 = 2202371) B2202371
theorem B1468267 : Blo 1466553 1468267 := bstep (se 1 (by rfl) ⟨1101200, by rfl⟩ : syracuseStep 1468267 = 2202401) B2202401
theorem B1468279 : Blo 1466553 1468279 := bstep (se 1 (by rfl) ⟨1101209, by rfl⟩ : syracuseStep 1468279 = 2202419) B2202419
theorem B1468299 : Blo 1466553 1468299 := bstep (se 1 (by rfl) ⟨1101224, by rfl⟩ : syracuseStep 1468299 = 2202449) B2202449
theorem B1468311 : Blo 1466553 1468311 := bstep (se 1 (by rfl) ⟨1101233, by rfl⟩ : syracuseStep 1468311 = 2202467) B2202467
theorem B1468331 : Blo 1466553 1468331 := bstep (se 1 (by rfl) ⟨1101248, by rfl⟩ : syracuseStep 1468331 = 2202497) B2202497
theorem B1468343 : Blo 1466553 1468343 := bstep (se 1 (by rfl) ⟨1101257, by rfl⟩ : syracuseStep 1468343 = 2202515) B2202515
theorem B4949963 : Blo 1466553 4949963 := bstep (se 1 (by rfl) ⟨3712472, by rfl⟩ : syracuseStep 4949963 = 7424945) B7424945
theorem B1468363 : Blo 1466553 1468363 := bstep (se 1 (by rfl) ⟨1101272, by rfl⟩ : syracuseStep 1468363 = 2202545) B2202545
theorem B12068813 : Blo 1466553 12068813 := bstep (se 3 (by rfl) ⟨2262902, by rfl⟩ : syracuseStep 12068813 = 4525805) B4525805
theorem B1468375 : Blo 1466553 1468375 := bstep (se 1 (by rfl) ⟨1101281, by rfl⟩ : syracuseStep 1468375 = 2202563) B2202563
theorem B8357849 : Blo 1466553 8357849 := bstep (se 2 (by rfl) ⟨3134193, by rfl⟩ : syracuseStep 8357849 = 6268387) B6268387
theorem B1468395 : Blo 1466553 1468395 := bstep (se 1 (by rfl) ⟨1101296, by rfl⟩ : syracuseStep 1468395 = 2202593) B2202593
theorem B1468407 : Blo 1466553 1468407 := bstep (se 1 (by rfl) ⟨1101305, by rfl⟩ : syracuseStep 1468407 = 2202611) B2202611
theorem B1468427 : Blo 1466553 1468427 := bstep (se 1 (by rfl) ⟨1101320, by rfl⟩ : syracuseStep 1468427 = 2202641) B2202641
theorem B5285911 : Blo 1466553 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B2476055 : Blo 1466553 2476055 := bstep (se 1 (by rfl) ⟨1857041, by rfl⟩ : syracuseStep 2476055 = 3714083) B3714083
theorem B3303449 : Blo 1466553 3303449 := bstep (se 2 (by rfl) ⟨1238793, by rfl⟩ : syracuseStep 3303449 = 2477587) B2477587
theorem B1468439 : Blo 1466553 1468439 := bstep (se 1 (by rfl) ⟨1101329, by rfl⟩ : syracuseStep 1468439 = 2202659) B2202659
theorem B1468459 : Blo 1466553 1468459 := bstep (se 1 (by rfl) ⟨1101344, by rfl⟩ : syracuseStep 1468459 = 2202689) B2202689
theorem B1468471 : Blo 1466553 1468471 := bstep (se 1 (by rfl) ⟨1101353, by rfl⟩ : syracuseStep 1468471 = 2202707) B2202707
theorem B9406529 : Blo 1466553 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B1468491 : Blo 1466553 1468491 := bstep (se 1 (by rfl) ⟨1101368, by rfl⟩ : syracuseStep 1468491 = 2202737) B2202737
theorem B1673303 : Blo 1466553 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1468503 : Blo 1466553 1468503 := bstep (se 1 (by rfl) ⟨1101377, by rfl⟩ : syracuseStep 1468503 = 2202755) B2202755
theorem B6269021 : Blo 1466553 6269021 := bstep (se 3 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 6269021 = 2350883) B2350883
theorem B1468523 : Blo 1466553 1468523 := bstep (se 1 (by rfl) ⟨1101392, by rfl⟩ : syracuseStep 1468523 = 2202785) B2202785
theorem B3303539 : Blo 1466553 3303539 := bstep (se 1 (by rfl) ⟨2477654, by rfl⟩ : syracuseStep 3303539 = 4955309) B4955309
theorem B1468535 : Blo 1466553 1468535 := bstep (se 1 (by rfl) ⟨1101401, by rfl⟩ : syracuseStep 1468535 = 2202803) B2202803
theorem B2476183 : Blo 1466553 2476183 := bstep (se 1 (by rfl) ⟨1857137, by rfl⟩ : syracuseStep 2476183 = 3714275) B3714275
theorem B3303575 : Blo 1466553 3303575 := bstep (se 1 (by rfl) ⟨2477681, by rfl⟩ : syracuseStep 3303575 = 4955363) B4955363
theorem B4950233 : Blo 1466553 4950233 := bstep (se 2 (by rfl) ⟨1856337, by rfl⟩ : syracuseStep 4950233 = 3712675) B3712675
theorem B11897093 : Blo 1466553 11897093 := bstep (se 4 (by rfl) ⟨1115352, by rfl⟩ : syracuseStep 11897093 = 2230705) B2230705
theorem B3713303 : Blo 1466553 3713303 := bstep (se 1 (by rfl) ⟨2784977, by rfl⟩ : syracuseStep 3713303 = 5569955) B5569955
theorem B2787635 : Blo 1466553 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B3303755 : Blo 1466553 3303755 := bstep (se 1 (by rfl) ⟨2477816, by rfl⟩ : syracuseStep 3303755 = 4955633) B4955633
theorem B1567063 : Blo 1466553 1567063 := bstep (se 1 (by rfl) ⟨1175297, by rfl⟩ : syracuseStep 1567063 = 2350595) B2350595
theorem B3967321 : Blo 1466553 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B3303809 : Blo 1466553 3303809 := bstep (se 2 (by rfl) ⟨1238928, by rfl⟩ : syracuseStep 3303809 = 2477857) B2477857
theorem B2787787 : Blo 1466553 2787787 := bstep (se 1 (by rfl) ⟨2090840, by rfl⟩ : syracuseStep 2787787 = 4181681) B4181681
theorem B7432721 : Blo 1466553 7432721 := bstep (se 2 (by rfl) ⟨2787270, by rfl⟩ : syracuseStep 7432721 = 5574541) B5574541
theorem B4180531 : Blo 1466553 4180531 := bstep (se 1 (by rfl) ⟨3135398, by rfl⟩ : syracuseStep 4180531 = 6270797) B6270797
theorem B3304025 : Blo 1466553 3304025 := bstep (se 2 (by rfl) ⟨1239009, by rfl⟩ : syracuseStep 3304025 = 2478019) B2478019
theorem B7432883 : Blo 1466553 7432883 := bstep (se 1 (by rfl) ⟨5574662, by rfl⟩ : syracuseStep 7432883 = 11149325) B11149325
theorem B3304115 : Blo 1466553 3304115 := bstep (se 1 (by rfl) ⟨2478086, by rfl⟩ : syracuseStep 3304115 = 4956173) B4956173
theorem B3304151 : Blo 1466553 3304151 := bstep (se 1 (by rfl) ⟨2478113, by rfl⟩ : syracuseStep 3304151 = 4956227) B4956227
theorem B5286617 : Blo 1466553 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B5950169 : Blo 1466553 5950169 := bstep (se 2 (by rfl) ⟨2231313, by rfl⟩ : syracuseStep 5950169 = 4462627) B4462627
theorem B2476811 : Blo 1466553 2476811 := bstep (se 1 (by rfl) ⟨1857608, by rfl⟩ : syracuseStep 2476811 = 3715217) B3715217
theorem B6269719 : Blo 1466553 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B5802803 : Blo 1466553 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B2476939 : Blo 1466553 2476939 := bstep (se 1 (by rfl) ⟨1857704, by rfl⟩ : syracuseStep 2476939 = 3715409) B3715409
theorem B4950935 : Blo 1466553 4950935 := bstep (se 1 (by rfl) ⟨3713201, by rfl⟩ : syracuseStep 4950935 = 7426403) B7426403
theorem B3713971 : Blo 1466553 3713971 := bstep (se 1 (by rfl) ⟨2785478, by rfl⟩ : syracuseStep 3713971 = 5570957) B5570957
theorem B5573555 : Blo 1466553 5573555 := bstep (se 1 (by rfl) ⟨4180166, by rfl⟩ : syracuseStep 5573555 = 8360333) B8360333
theorem B5573569 : Blo 1466553 5573569 := bstep (se 2 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 5573569 = 4180177) B4180177
theorem B2477081 : Blo 1466553 2477081 := bstep (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) B1857811
theorem B3714113 : Blo 1466553 3714113 := bstep (se 2 (by rfl) ⟨1392792, by rfl⟩ : syracuseStep 3714113 = 2785585) B2785585
theorem B1567883 : Blo 1466553 1567883 := bstep (se 1 (by rfl) ⟨1175912, by rfl⟩ : syracuseStep 1567883 = 2351825) B2351825
theorem B2477209 : Blo 1466553 2477209 := bstep (se 2 (by rfl) ⟨928953, by rfl⟩ : syracuseStep 2477209 = 1857907) B1857907
theorem B1649911 : Blo 1466553 1649911 := bstep (se 1 (by rfl) ⟨1237433, by rfl⟩ : syracuseStep 1649911 = 2474867) B2474867
theorem B11144465 : Blo 1466553 11144465 := bstep (se 2 (by rfl) ⟨4179174, by rfl⟩ : syracuseStep 11144465 = 8358349) B8358349
theorem B2977049 : Blo 1466553 2977049 := bstep (se 2 (by rfl) ⟨1116393, by rfl⟩ : syracuseStep 2977049 = 2232787) B2232787
theorem B30125357 : Blo 1466553 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B18353509 : Blo 1466553 18353509 := bstep (se 4 (by rfl) ⟨1720641, by rfl⟩ : syracuseStep 18353509 = 3441283) B3441283
theorem B7425431 : Blo 1466553 7425431 := bstep (se 1 (by rfl) ⟨5569073, by rfl⟩ : syracuseStep 7425431 = 11138147) B11138147
theorem B1650091 : Blo 1466553 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B4951475 : Blo 1466553 4951475 := bstep (se 1 (by rfl) ⟨3713606, by rfl⟩ : syracuseStep 4951475 = 7427213) B7427213
theorem B2543051 : Blo 1466553 2543051 := bstep (se 1 (by rfl) ⟨1907288, by rfl⟩ : syracuseStep 2543051 = 3814577) B3814577
theorem B7056857 : Blo 1466553 7056857 := bstep (se 2 (by rfl) ⟨2646321, by rfl⟩ : syracuseStep 7056857 = 5292643) B5292643
theorem B1650199 : Blo 1466553 1650199 := bstep (se 1 (by rfl) ⟨1237649, by rfl⟩ : syracuseStep 1650199 = 2475299) B2475299
theorem B12529187 : Blo 1466553 12529187 := bstep (se 1 (by rfl) ⟨9396890, by rfl⟩ : syracuseStep 12529187 = 18793781) B18793781
theorem B7056971 : Blo 1466553 7056971 := bstep (se 1 (by rfl) ⟨5292728, by rfl⟩ : syracuseStep 7056971 = 10585457) B10585457
theorem B11136689 : Blo 1466553 11136689 := bstep (se 2 (by rfl) ⟨4176258, by rfl⟩ : syracuseStep 11136689 = 8352517) B8352517
theorem B4951745 : Blo 1466553 4951745 := bstep (se 2 (by rfl) ⟨1856904, by rfl⟩ : syracuseStep 4951745 = 3713809) B3713809
theorem B1650379 : Blo 1466553 1650379 := bstep (se 1 (by rfl) ⟨1237784, by rfl⟩ : syracuseStep 1650379 = 2475569) B2475569
theorem B2477783 : Blo 1466553 2477783 := bstep (se 1 (by rfl) ⟨1858337, by rfl⟩ : syracuseStep 2477783 = 3716675) B3716675
theorem B1650487 : Blo 1466553 1650487 := bstep (se 1 (by rfl) ⟨1237865, by rfl⟩ : syracuseStep 1650487 = 2475731) B2475731
theorem B2477911 : Blo 1466553 2477911 := bstep (se 1 (by rfl) ⟨1858433, by rfl⟩ : syracuseStep 2477911 = 3716867) B3716867
theorem B1650667 : Blo 1466553 1650667 := bstep (se 1 (by rfl) ⟨1238000, by rfl⟩ : syracuseStep 1650667 = 2476001) B2476001
theorem B4460609 : Blo 1466553 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B1650775 : Blo 1466553 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B4460633 : Blo 1466553 4460633 := bstep (se 2 (by rfl) ⟨1672737, by rfl⟩ : syracuseStep 4460633 = 3345475) B3345475
theorem B3133579 : Blo 1466553 3133579 := bstep (se 1 (by rfl) ⟨2350184, by rfl⟩ : syracuseStep 3133579 = 4700369) B4700369
theorem B6271121 : Blo 1466553 6271121 := bstep (se 2 (by rfl) ⟨2351670, by rfl⟩ : syracuseStep 6271121 = 4703341) B4703341
theorem B11137175 : Blo 1466553 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B25071767 : Blo 1466553 25071767 := bstep (se 1 (by rfl) ⟨18803825, by rfl⟩ : syracuseStep 25071767 = 37607651) B37607651
theorem B4526273 : Blo 1466553 4526273 := bstep (se 2 (by rfl) ⟨1697352, by rfl⟩ : syracuseStep 4526273 = 3394705) B3394705
theorem B4952285 : Blo 1466553 4952285 := bstep (se 3 (by rfl) ⟨928553, by rfl⟩ : syracuseStep 4952285 = 1857107) B1857107
theorem B1650955 : Blo 1466553 1650955 := bstep (se 1 (by rfl) ⟨1238216, by rfl⟩ : syracuseStep 1650955 = 2476433) B2476433
theorem B2199833 : Blo 1466553 2199833 := bstep (se 2 (by rfl) ⟨824937, by rfl⟩ : syracuseStep 2199833 = 1649875) B1649875
theorem B3715379 : Blo 1466553 3715379 := bstep (se 1 (by rfl) ⟨2786534, by rfl⟩ : syracuseStep 3715379 = 5573069) B5573069
theorem B1651063 : Blo 1466553 1651063 := bstep (se 1 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 1651063 = 2476595) B2476595
theorem B2199947 : Blo 1466553 2199947 := bstep (se 1 (by rfl) ⟨1649960, by rfl⟩ : syracuseStep 2199947 = 3299921) B3299921
theorem B2199959 : Blo 1466553 2199959 := bstep (se 1 (by rfl) ⟨1649969, by rfl⟩ : syracuseStep 2199959 = 3299939) B3299939
theorem B2200025 : Blo 1466553 2200025 := bstep (se 2 (by rfl) ⟨825009, by rfl⟩ : syracuseStep 2200025 = 1650019) B1650019
theorem B2511371 : Blo 1466553 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B9294353 : Blo 1466553 9294353 := bstep (se 2 (by rfl) ⟨3485382, by rfl⟩ : syracuseStep 9294353 = 6970765) B6970765
theorem B1651243 : Blo 1466553 1651243 := bstep (se 1 (by rfl) ⟨1238432, by rfl⟩ : syracuseStep 1651243 = 2476865) B2476865
theorem B2200139 : Blo 1466553 2200139 := bstep (se 1 (by rfl) ⟨1650104, by rfl⟩ : syracuseStep 2200139 = 3300209) B3300209
theorem B2200151 : Blo 1466553 2200151 := bstep (se 1 (by rfl) ⟨1650113, by rfl⟩ : syracuseStep 2200151 = 3300227) B3300227
theorem B54317699 : Blo 1466553 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B1651351 : Blo 1466553 1651351 := bstep (se 1 (by rfl) ⟨1238513, by rfl⟩ : syracuseStep 1651351 = 2477027) B2477027
theorem B2200217 : Blo 1466553 2200217 := bstep (se 2 (by rfl) ⟨825081, by rfl⟩ : syracuseStep 2200217 = 1650163) B1650163
theorem B1487575 : Blo 1466553 1487575 := bstep (se 1 (by rfl) ⟨1115681, by rfl⟩ : syracuseStep 1487575 = 2231363) B2231363
theorem B2200331 : Blo 1466553 2200331 := bstep (se 1 (by rfl) ⟨1650248, by rfl⟩ : syracuseStep 2200331 = 3300497) B3300497
theorem B2200343 : Blo 1466553 2200343 := bstep (se 1 (by rfl) ⟨1650257, by rfl⟩ : syracuseStep 2200343 = 3300515) B3300515
theorem B3715915 : Blo 1466553 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B1651531 : Blo 1466553 1651531 := bstep (se 1 (by rfl) ⟨1238648, by rfl⟩ : syracuseStep 1651531 = 2477297) B2477297
theorem B5575499 : Blo 1466553 5575499 := bstep (se 1 (by rfl) ⟨4181624, by rfl⟩ : syracuseStep 5575499 = 8363249) B8363249
theorem B2200409 : Blo 1466553 2200409 := bstep (se 2 (by rfl) ⟨825153, by rfl⟩ : syracuseStep 2200409 = 1650307) B1650307
theorem B5575513 : Blo 1466553 5575513 := bstep (se 2 (by rfl) ⟨2090817, by rfl⟩ : syracuseStep 5575513 = 4181635) B4181635
theorem B7934813 : Blo 1466553 7934813 := bstep (se 3 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 7934813 = 2975555) B2975555
theorem B53547875 : Blo 1466553 53547875 := bstep (se 1 (by rfl) ⟨40160906, by rfl⟩ : syracuseStep 53547875 = 80321813) B80321813
theorem B1651639 : Blo 1466553 1651639 := bstep (se 1 (by rfl) ⟨1238729, by rfl⟩ : syracuseStep 1651639 = 2477459) B2477459
theorem B1856459 : Blo 1466553 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B2200523 : Blo 1466553 2200523 := bstep (se 1 (by rfl) ⟨1650392, by rfl⟩ : syracuseStep 2200523 = 3300785) B3300785
theorem B2200535 : Blo 1466553 2200535 := bstep (se 1 (by rfl) ⟨1650401, by rfl⟩ : syracuseStep 2200535 = 3300803) B3300803
theorem B3716057 : Blo 1466553 3716057 := bstep (se 2 (by rfl) ⟨1393521, by rfl⟩ : syracuseStep 3716057 = 2787043) B2787043
theorem B5649431 : Blo 1466553 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B2200601 : Blo 1466553 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B6689837 : Blo 1466553 6689837 := bstep (se 3 (by rfl) ⟨1254344, by rfl⟩ : syracuseStep 6689837 = 2508689) B2508689
theorem B11293789 : Blo 1466553 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B1651819 : Blo 1466553 1651819 := bstep (se 1 (by rfl) ⟨1238864, by rfl⟩ : syracuseStep 1651819 = 2477729) B2477729
theorem B2200715 : Blo 1466553 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B2200727 : Blo 1466553 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B1651927 : Blo 1466553 1651927 := bstep (se 1 (by rfl) ⟨1238945, by rfl⟩ : syracuseStep 1651927 = 2477891) B2477891
theorem B2200793 : Blo 1466553 2200793 := bstep (se 2 (by rfl) ⟨825297, by rfl⟩ : syracuseStep 2200793 = 1650595) B1650595
theorem B2643187 : Blo 1466553 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B3347699 : Blo 1466553 3347699 := bstep (se 1 (by rfl) ⟨2510774, by rfl⟩ : syracuseStep 3347699 = 5021549) B5021549
theorem B2200907 : Blo 1466553 2200907 := bstep (se 1 (by rfl) ⟨1650680, by rfl⟩ : syracuseStep 2200907 = 3301361) B3301361
theorem B4953419 : Blo 1466553 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B2200919 : Blo 1466553 2200919 := bstep (se 1 (by rfl) ⟨1650689, by rfl⟩ : syracuseStep 2200919 = 3301379) B3301379
theorem B1652107 : Blo 1466553 1652107 := bstep (se 1 (by rfl) ⟨1239080, by rfl⟩ : syracuseStep 1652107 = 2478161) B2478161
theorem B2200985 : Blo 1466553 2200985 := bstep (se 2 (by rfl) ⟨825369, by rfl⟩ : syracuseStep 2200985 = 1650739) B1650739
theorem B4699613 : Blo 1466553 4699613 := bstep (se 3 (by rfl) ⟨881177, by rfl⟩ : syracuseStep 4699613 = 1762355) B1762355
theorem B3134963 : Blo 1466553 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B2201099 : Blo 1466553 2201099 := bstep (se 1 (by rfl) ⟨1650824, by rfl⟩ : syracuseStep 2201099 = 3301649) B3301649
theorem B40138253 : Blo 1466553 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B2201111 : Blo 1466553 2201111 := bstep (se 1 (by rfl) ⟨1650833, by rfl⟩ : syracuseStep 2201111 = 3301667) B3301667
theorem B9655853 : Blo 1466553 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2201177 : Blo 1466553 2201177 := bstep (se 2 (by rfl) ⟨825441, by rfl⟩ : syracuseStep 2201177 = 1650883) B1650883
theorem B4953689 : Blo 1466553 4953689 := bstep (se 2 (by rfl) ⟨1857633, by rfl⟩ : syracuseStep 4953689 = 3715267) B3715267
theorem B1857163 : Blo 1466553 1857163 := bstep (se 1 (by rfl) ⟨1392872, by rfl⟩ : syracuseStep 1857163 = 2785745) B2785745
theorem B2201291 : Blo 1466553 2201291 := bstep (se 1 (by rfl) ⟨1650968, by rfl⟩ : syracuseStep 2201291 = 3301937) B3301937
theorem B2201303 : Blo 1466553 2201303 := bstep (se 1 (by rfl) ⟨1650977, by rfl⟩ : syracuseStep 2201303 = 3301955) B3301955
theorem B3348211 : Blo 1466553 3348211 := bstep (se 1 (by rfl) ⟨2511158, by rfl⟩ : syracuseStep 3348211 = 5022317) B5022317
theorem B5289731 : Blo 1466553 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B5953283 : Blo 1466553 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B3716887 : Blo 1466553 3716887 := bstep (se 1 (by rfl) ⟨2787665, by rfl⟩ : syracuseStep 3716887 = 5575331) B5575331
theorem B2201369 : Blo 1466553 2201369 := bstep (se 2 (by rfl) ⟨825513, by rfl⟩ : syracuseStep 2201369 = 1651027) B1651027
theorem B2201483 : Blo 1466553 2201483 := bstep (se 1 (by rfl) ⟨1651112, by rfl⟩ : syracuseStep 2201483 = 3302225) B3302225
theorem B1857431 : Blo 1466553 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B2201495 : Blo 1466553 2201495 := bstep (se 1 (by rfl) ⟨1651121, by rfl⟩ : syracuseStep 2201495 = 3302243) B3302243
theorem B13391821 : Blo 1466553 13391821 := bstep (se 3 (by rfl) ⟨2510966, by rfl⟩ : syracuseStep 13391821 = 5021933) B5021933
theorem B2201561 : Blo 1466553 2201561 := bstep (se 2 (by rfl) ⟨825585, by rfl⟩ : syracuseStep 2201561 = 1651171) B1651171
theorem B60225605 : Blo 1466553 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B2201675 : Blo 1466553 2201675 := bstep (se 1 (by rfl) ⟨1651256, by rfl⟩ : syracuseStep 2201675 = 3302513) B3302513
theorem B2201687 : Blo 1466553 2201687 := bstep (se 1 (by rfl) ⟨1651265, by rfl⟩ : syracuseStep 2201687 = 3302531) B3302531
theorem B2201753 : Blo 1466553 2201753 := bstep (se 2 (by rfl) ⟨825657, by rfl⟩ : syracuseStep 2201753 = 1651315) B1651315
theorem B6691019 : Blo 1466553 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B2291915 : Blo 1466553 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B2201867 : Blo 1466553 2201867 := bstep (se 1 (by rfl) ⟨1651400, by rfl⟩ : syracuseStep 2201867 = 3302801) B3302801
theorem B2201879 : Blo 1466553 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B4954391 : Blo 1466553 4954391 := bstep (se 1 (by rfl) ⟨3715793, by rfl⟩ : syracuseStep 4954391 = 7431587) B7431587
theorem B3135809 : Blo 1466553 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B2201945 : Blo 1466553 2201945 := bstep (se 2 (by rfl) ⟨825729, by rfl⟩ : syracuseStep 2201945 = 1651459) B1651459
theorem B3299777 : Blo 1466553 3299777 := bstep (se 2 (by rfl) ⟨1237416, by rfl⟩ : syracuseStep 3299777 = 2474833) B2474833
theorem B2202059 : Blo 1466553 2202059 := bstep (se 1 (by rfl) ⟨1651544, by rfl⟩ : syracuseStep 2202059 = 3303089) B3303089
theorem B2202071 : Blo 1466553 2202071 := bstep (se 1 (by rfl) ⟨1651553, by rfl⟩ : syracuseStep 2202071 = 3303107) B3303107
theorem B2202137 : Blo 1466553 2202137 := bstep (se 2 (by rfl) ⟨825801, by rfl⟩ : syracuseStep 2202137 = 1651603) B1651603
theorem B8362541 : Blo 1466553 8362541 := bstep (se 3 (by rfl) ⟨1567976, by rfl⟩ : syracuseStep 8362541 = 3135953) B3135953
theorem B1858135 : Blo 1466553 1858135 := bstep (se 1 (by rfl) ⟨1393601, by rfl⟩ : syracuseStep 1858135 = 2787203) B2787203
theorem B2202251 : Blo 1466553 2202251 := bstep (se 1 (by rfl) ⟨1651688, by rfl⟩ : syracuseStep 2202251 = 3303377) B3303377
theorem B2202263 : Blo 1466553 2202263 := bstep (se 1 (by rfl) ⟨1651697, by rfl⟩ : syracuseStep 2202263 = 3303395) B3303395
theorem B3136151 : Blo 1466553 3136151 := bstep (se 1 (by rfl) ⟨2352113, by rfl⟩ : syracuseStep 3136151 = 4704227) B4704227
theorem B3299993 : Blo 1466553 3299993 := bstep (se 2 (by rfl) ⟨1237497, by rfl⟩ : syracuseStep 3299993 = 2474995) B2474995
theorem B2202329 : Blo 1466553 2202329 := bstep (se 2 (by rfl) ⟨825873, by rfl⟩ : syracuseStep 2202329 = 1651747) B1651747
theorem B3300083 : Blo 1466553 3300083 := bstep (se 1 (by rfl) ⟨2475062, by rfl⟩ : syracuseStep 3300083 = 4950125) B4950125
theorem B3300119 : Blo 1466553 3300119 := bstep (se 1 (by rfl) ⟨2475089, by rfl⟩ : syracuseStep 3300119 = 4950179) B4950179
theorem B4954931 : Blo 1466553 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B14113601 : Blo 1466553 14113601 := bstep (se 2 (by rfl) ⟨5292600, by rfl⟩ : syracuseStep 14113601 = 10585201) B10585201
theorem B2202443 : Blo 1466553 2202443 := bstep (se 1 (by rfl) ⟨1651832, by rfl⟩ : syracuseStep 2202443 = 3303665) B3303665
theorem B2202455 : Blo 1466553 2202455 := bstep (se 1 (by rfl) ⟨1651841, by rfl⟩ : syracuseStep 2202455 = 3303683) B3303683
theorem B7428995 : Blo 1466553 7428995 := bstep (se 1 (by rfl) ⟨5571746, by rfl⟩ : syracuseStep 7428995 = 11143493) B11143493
theorem B2202521 : Blo 1466553 2202521 := bstep (se 2 (by rfl) ⟨825945, by rfl⟩ : syracuseStep 2202521 = 1651891) B1651891
theorem B2784203 : Blo 1466553 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B3300299 : Blo 1466553 3300299 := bstep (se 1 (by rfl) ⟨2475224, by rfl⟩ : syracuseStep 3300299 = 4950449) B4950449
theorem B3300353 : Blo 1466553 3300353 := bstep (se 2 (by rfl) ⟨1237632, by rfl⟩ : syracuseStep 3300353 = 2475265) B2475265
theorem B2202635 : Blo 1466553 2202635 := bstep (se 1 (by rfl) ⟨1651976, by rfl⟩ : syracuseStep 2202635 = 3303953) B3303953
theorem B2202647 : Blo 1466553 2202647 := bstep (se 1 (by rfl) ⟨1651985, by rfl⟩ : syracuseStep 2202647 = 3303971) B3303971
theorem B51526691 : Blo 1466553 51526691 := bstep (se 1 (by rfl) ⟨38645018, by rfl⟩ : syracuseStep 51526691 = 77290037) B77290037
theorem B11148353 : Blo 1466553 11148353 := bstep (se 2 (by rfl) ⟨4180632, by rfl⟩ : syracuseStep 11148353 = 8361265) B8361265
theorem B4955201 : Blo 1466553 4955201 := bstep (se 2 (by rfl) ⟨1858200, by rfl⟩ : syracuseStep 4955201 = 3716401) B3716401
theorem B2202713 : Blo 1466553 2202713 := bstep (se 2 (by rfl) ⟨826017, by rfl⟩ : syracuseStep 2202713 = 1652035) B1652035
theorem B2784385 : Blo 1466553 2784385 := bstep (se 2 (by rfl) ⟨1044144, by rfl⟩ : syracuseStep 2784385 = 2088289) B2088289
theorem B5569667 : Blo 1466553 5569667 := bstep (se 1 (by rfl) ⟨4177250, by rfl⟩ : syracuseStep 5569667 = 8354501) B8354501
theorem B5569681 : Blo 1466553 5569681 := bstep (se 2 (by rfl) ⟨2088630, by rfl⟩ : syracuseStep 5569681 = 4177261) B4177261
theorem B2202827 : Blo 1466553 2202827 := bstep (se 1 (by rfl) ⟨1652120, by rfl⟩ : syracuseStep 2202827 = 3304241) B3304241
theorem B3300569 : Blo 1466553 3300569 := bstep (se 2 (by rfl) ⟨1237713, by rfl⟩ : syracuseStep 3300569 = 2475427) B2475427
theorem B3300659 : Blo 1466553 3300659 := bstep (se 1 (by rfl) ⟨2475494, by rfl⟩ : syracuseStep 3300659 = 4950989) B4950989
theorem B3300695 : Blo 1466553 3300695 := bstep (se 1 (by rfl) ⟨2475521, by rfl⟩ : syracuseStep 3300695 = 4951043) B4951043
theorem B2645399 : Blo 1466553 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B9043379 : Blo 1466553 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B8355251 : Blo 1466553 8355251 := bstep (se 1 (by rfl) ⟨6266438, by rfl⟩ : syracuseStep 8355251 = 12532877) B12532877
theorem B5569985 : Blo 1466553 5569985 := bstep (se 2 (by rfl) ⟨2088744, by rfl⟩ : syracuseStep 5569985 = 4177489) B4177489
theorem B3300875 : Blo 1466553 3300875 := bstep (se 1 (by rfl) ⟨2475656, by rfl⟩ : syracuseStep 3300875 = 4951313) B4951313
theorem B3300929 : Blo 1466553 3300929 := bstep (se 2 (by rfl) ⟨1237848, by rfl⟩ : syracuseStep 3300929 = 2475697) B2475697
theorem B4955741 : Blo 1466553 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B6692483 : Blo 1466553 6692483 := bstep (se 1 (by rfl) ⟨5019362, by rfl⟩ : syracuseStep 6692483 = 10038725) B10038725
theorem B3301145 : Blo 1466553 3301145 := bstep (se 2 (by rfl) ⟨1237929, by rfl⟩ : syracuseStep 3301145 = 2475859) B2475859
theorem B2785099 : Blo 1466553 2785099 := bstep (se 1 (by rfl) ⟨2088824, by rfl⟩ : syracuseStep 2785099 = 4177649) B4177649
theorem B3301235 : Blo 1466553 3301235 := bstep (se 1 (by rfl) ⟨2475926, by rfl⟩ : syracuseStep 3301235 = 4951853) B4951853
theorem B2645875 : Blo 1466553 2645875 := bstep (se 1 (by rfl) ⟨1984406, by rfl⟩ : syracuseStep 2645875 = 3968813) B3968813
theorem B7929751 : Blo 1466553 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B2785175 : Blo 1466553 2785175 := bstep (se 1 (by rfl) ⟨2088881, by rfl⟩ : syracuseStep 2785175 = 4177763) B4177763
theorem B2973593 : Blo 1466553 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B3301271 : Blo 1466553 3301271 := bstep (se 1 (by rfl) ⟨2475953, by rfl⟩ : syracuseStep 3301271 = 4951907) B4951907
theorem B2973755 : Blo 1466553 2973755 := bstep (se 1 (by rfl) ⟨2230316, by rfl⟩ : syracuseStep 2973755 = 4460633) B4460633
theorem B15065149 : Blo 1466553 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B8355959 : Blo 1466553 8355959 := bstep (se 1 (by rfl) ⟨6266969, by rfl⟩ : syracuseStep 8355959 = 12533939) B12533939
theorem B3301523 : Blo 1466553 3301523 := bstep (se 1 (by rfl) ⟨2476142, by rfl⟩ : syracuseStep 3301523 = 4952285) B4952285
theorem B11894957 : Blo 1466553 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B4178105 : Blo 1466553 4178105 := bstep (se 2 (by rfl) ⟨1566789, by rfl⟩ : syracuseStep 4178105 = 3133579) B3133579
theorem B1466555 : Blo 1466553 1466555 := bstep (se 1 (by rfl) ⟨1099916, by rfl⟩ : syracuseStep 1466555 = 2199833) B2199833
theorem B3301577 : Blo 1466553 3301577 := bstep (se 2 (by rfl) ⟨1238091, by rfl⟩ : syracuseStep 3301577 = 2476183) B2476183
theorem B1466631 : Blo 1466553 1466631 := bstep (se 1 (by rfl) ⟨1099973, by rfl⟩ : syracuseStep 1466631 = 2199947) B2199947
theorem B1466639 : Blo 1466553 1466639 := bstep (se 1 (by rfl) ⟨1099979, by rfl⟩ : syracuseStep 1466639 = 2199959) B2199959
theorem B1466683 : Blo 1466553 1466683 := bstep (se 1 (by rfl) ⟨1100012, by rfl⟩ : syracuseStep 1466683 = 2200025) B2200025
theorem B1466759 : Blo 1466553 1466759 := bstep (se 1 (by rfl) ⟨1100069, by rfl⟩ : syracuseStep 1466759 = 2200139) B2200139
theorem B1466767 : Blo 1466553 1466767 := bstep (se 1 (by rfl) ⟨1100075, by rfl⟩ : syracuseStep 1466767 = 2200151) B2200151
theorem B1466811 : Blo 1466553 1466811 := bstep (se 1 (by rfl) ⟨1100108, by rfl⟩ : syracuseStep 1466811 = 2200217) B2200217
theorem B2089417 : Blo 1466553 2089417 := bstep (se 2 (by rfl) ⟨783531, by rfl⟩ : syracuseStep 2089417 = 1567063) B1567063
theorem B1466887 : Blo 1466553 1466887 := bstep (se 1 (by rfl) ⟨1100165, by rfl⟩ : syracuseStep 1466887 = 2200331) B2200331
theorem B1466895 : Blo 1466553 1466895 := bstep (se 1 (by rfl) ⟨1100171, by rfl⟩ : syracuseStep 1466895 = 2200343) B2200343
theorem B17842717 : Blo 1466553 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B6111773 : Blo 1466553 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B1466939 : Blo 1466553 1466939 := bstep (se 1 (by rfl) ⟨1100204, by rfl⟩ : syracuseStep 1466939 = 2200409) B2200409
theorem B5571139 : Blo 1466553 5571139 := bstep (se 1 (by rfl) ⟨4178354, by rfl⟩ : syracuseStep 5571139 = 8356709) B8356709
theorem B1467015 : Blo 1466553 1467015 := bstep (se 1 (by rfl) ⟨1100261, by rfl⟩ : syracuseStep 1467015 = 2200523) B2200523
theorem B2785927 : Blo 1466553 2785927 := bstep (se 1 (by rfl) ⟨2089445, by rfl⟩ : syracuseStep 2785927 = 4178891) B4178891
theorem B1467023 : Blo 1466553 1467023 := bstep (se 1 (by rfl) ⟨1100267, by rfl⟩ : syracuseStep 1467023 = 2200535) B2200535
theorem B1467067 : Blo 1466553 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B1467143 : Blo 1466553 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B1467151 : Blo 1466553 1467151 := bstep (se 1 (by rfl) ⟨1100363, by rfl⟩ : syracuseStep 1467151 = 2200727) B2200727
theorem B1467195 : Blo 1466553 1467195 := bstep (se 1 (by rfl) ⟨1100396, by rfl⟩ : syracuseStep 1467195 = 2200793) B2200793
theorem B5571443 : Blo 1466553 5571443 := bstep (se 1 (by rfl) ⟨4178582, by rfl⟩ : syracuseStep 5571443 = 8357165) B8357165
theorem B2474887 : Blo 1466553 2474887 := bstep (se 1 (by rfl) ⟨1856165, by rfl⟩ : syracuseStep 2474887 = 3712331) B3712331
theorem B1467271 : Blo 1466553 1467271 := bstep (se 1 (by rfl) ⟨1100453, by rfl⟩ : syracuseStep 1467271 = 2200907) B2200907
theorem B3302279 : Blo 1466553 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B1467279 : Blo 1466553 1467279 := bstep (se 1 (by rfl) ⟨1100459, by rfl⟩ : syracuseStep 1467279 = 2200919) B2200919
theorem B1467323 : Blo 1466553 1467323 := bstep (se 1 (by rfl) ⟨1100492, by rfl⟩ : syracuseStep 1467323 = 2200985) B2200985
theorem B1983433 : Blo 1466553 1983433 := bstep (se 2 (by rfl) ⟨743787, by rfl⟩ : syracuseStep 1983433 = 1487575) B1487575
theorem B2089975 : Blo 1466553 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B1467399 : Blo 1466553 1467399 := bstep (se 1 (by rfl) ⟨1100549, by rfl⟩ : syracuseStep 1467399 = 2201099) B2201099
theorem B1467407 : Blo 1466553 1467407 := bstep (se 1 (by rfl) ⟨1100555, by rfl⟩ : syracuseStep 1467407 = 2201111) B2201111
theorem B1467451 : Blo 1466553 1467451 := bstep (se 1 (by rfl) ⟨1100588, by rfl⟩ : syracuseStep 1467451 = 2201177) B2201177
theorem B3302459 : Blo 1466553 3302459 := bstep (se 1 (by rfl) ⟨2476844, by rfl⟩ : syracuseStep 3302459 = 4953689) B4953689
theorem B7054397 : Blo 1466553 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B1467527 : Blo 1466553 1467527 := bstep (se 1 (by rfl) ⟨1100645, by rfl⟩ : syracuseStep 1467527 = 2201291) B2201291
theorem B1467535 : Blo 1466553 1467535 := bstep (se 1 (by rfl) ⟨1100651, by rfl⟩ : syracuseStep 1467535 = 2201303) B2201303
theorem B1467579 : Blo 1466553 1467579 := bstep (se 1 (by rfl) ⟨1100684, by rfl⟩ : syracuseStep 1467579 = 2201369) B2201369
theorem B3302585 : Blo 1466553 3302585 := bstep (se 2 (by rfl) ⟨1238469, by rfl⟩ : syracuseStep 3302585 = 2476939) B2476939
theorem B7431425 : Blo 1466553 7431425 := bstep (se 2 (by rfl) ⟨2786784, by rfl⟩ : syracuseStep 7431425 = 5573569) B5573569
theorem B1467655 : Blo 1466553 1467655 := bstep (se 1 (by rfl) ⟨1100741, by rfl⟩ : syracuseStep 1467655 = 2201483) B2201483
theorem B1467663 : Blo 1466553 1467663 := bstep (se 1 (by rfl) ⟨1100747, by rfl⟩ : syracuseStep 1467663 = 2201495) B2201495
theorem B8045875 : Blo 1466553 8045875 := bstep (se 1 (by rfl) ⟨6034406, by rfl⟩ : syracuseStep 8045875 = 12068813) B12068813
theorem B5571899 : Blo 1466553 5571899 := bstep (se 1 (by rfl) ⟨4178924, by rfl⟩ : syracuseStep 5571899 = 8357849) B8357849
theorem B1467707 : Blo 1466553 1467707 := bstep (se 1 (by rfl) ⟨1100780, by rfl⟩ : syracuseStep 1467707 = 2201561) B2201561
theorem B16713053 : Blo 1466553 16713053 := bstep (se 3 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 16713053 = 6267395) B6267395
theorem B40150403 : Blo 1466553 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B1467783 : Blo 1466553 1467783 := bstep (se 1 (by rfl) ⟨1100837, by rfl⟩ : syracuseStep 1467783 = 2201675) B2201675
theorem B1467791 : Blo 1466553 1467791 := bstep (se 1 (by rfl) ⟨1100843, by rfl⟩ : syracuseStep 1467791 = 2201687) B2201687
theorem B4179347 : Blo 1466553 4179347 := bstep (se 1 (by rfl) ⟨3134510, by rfl⟩ : syracuseStep 4179347 = 6269021) B6269021
theorem B1467835 : Blo 1466553 1467835 := bstep (se 1 (by rfl) ⟨1100876, by rfl⟩ : syracuseStep 1467835 = 2201753) B2201753
theorem B25748941 : Blo 1466553 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B15058385 : Blo 1466553 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B3712513 : Blo 1466553 3712513 := bstep (se 2 (by rfl) ⟨1392192, by rfl⟩ : syracuseStep 3712513 = 2784385) B2784385
theorem B7931395 : Blo 1466553 7931395 := bstep (se 1 (by rfl) ⟨5948546, by rfl⟩ : syracuseStep 7931395 = 11897093) B11897093
theorem B1467911 : Blo 1466553 1467911 := bstep (se 1 (by rfl) ⟨1100933, by rfl⟩ : syracuseStep 1467911 = 2201867) B2201867
theorem B2475535 : Blo 1466553 2475535 := bstep (se 1 (by rfl) ⟨1856651, by rfl⟩ : syracuseStep 2475535 = 3713303) B3713303
theorem B1467919 : Blo 1466553 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B3302927 : Blo 1466553 3302927 := bstep (se 1 (by rfl) ⟨2477195, by rfl⟩ : syracuseStep 3302927 = 4954391) B4954391
theorem B16934429 : Blo 1466553 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B3302945 : Blo 1466553 3302945 := bstep (se 2 (by rfl) ⟨1238604, by rfl⟩ : syracuseStep 3302945 = 2477209) B2477209
theorem B2090539 : Blo 1466553 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B1467963 : Blo 1466553 1467963 := bstep (se 1 (by rfl) ⟨1100972, by rfl⟩ : syracuseStep 1467963 = 2201945) B2201945
theorem B1468039 : Blo 1466553 1468039 := bstep (se 1 (by rfl) ⟨1101029, by rfl⟩ : syracuseStep 1468039 = 2202059) B2202059
theorem B1468047 : Blo 1466553 1468047 := bstep (se 1 (by rfl) ⟨1101035, by rfl⟩ : syracuseStep 1468047 = 2202071) B2202071
theorem B3524249 : Blo 1466553 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B1468091 : Blo 1466553 1468091 := bstep (se 1 (by rfl) ⟨1101068, by rfl⟩ : syracuseStep 1468091 = 2202137) B2202137
theorem B1468167 : Blo 1466553 1468167 := bstep (se 1 (by rfl) ⟨1101125, by rfl⟩ : syracuseStep 1468167 = 2202251) B2202251
theorem B1468175 : Blo 1466553 1468175 := bstep (se 1 (by rfl) ⟨1101131, by rfl⟩ : syracuseStep 1468175 = 2202263) B2202263
theorem B2090767 : Blo 1466553 2090767 := bstep (se 1 (by rfl) ⟨1568075, by rfl⟩ : syracuseStep 2090767 = 3136151) B3136151
theorem B5572385 : Blo 1466553 5572385 := bstep (se 2 (by rfl) ⟨2089644, by rfl⟩ : syracuseStep 5572385 = 4179289) B4179289
theorem B3524411 : Blo 1466553 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B3966779 : Blo 1466553 3966779 := bstep (se 1 (by rfl) ⟨2975084, by rfl⟩ : syracuseStep 3966779 = 5950169) B5950169
theorem B1468219 : Blo 1466553 1468219 := bstep (se 1 (by rfl) ⟨1101164, by rfl⟩ : syracuseStep 1468219 = 2202329) B2202329
theorem B3868535 : Blo 1466553 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B3303287 : Blo 1466553 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B1468295 : Blo 1466553 1468295 := bstep (se 1 (by rfl) ⟨1101221, by rfl⟩ : syracuseStep 1468295 = 2202443) B2202443
theorem B1468303 : Blo 1466553 1468303 := bstep (se 1 (by rfl) ⟨1101227, by rfl⟩ : syracuseStep 1468303 = 2202455) B2202455
theorem B1468347 : Blo 1466553 1468347 := bstep (se 1 (by rfl) ⟨1101260, by rfl⟩ : syracuseStep 1468347 = 2202521) B2202521
theorem B1468423 : Blo 1466553 1468423 := bstep (se 1 (by rfl) ⟨1101317, by rfl⟩ : syracuseStep 1468423 = 2202635) B2202635
theorem B1468431 : Blo 1466553 1468431 := bstep (se 1 (by rfl) ⟨1101323, by rfl⟩ : syracuseStep 1468431 = 2202647) B2202647
theorem B34351127 : Blo 1466553 34351127 := bstep (se 1 (by rfl) ⟨25763345, by rfl⟩ : syracuseStep 34351127 = 51526691) B51526691
theorem B2476075 : Blo 1466553 2476075 := bstep (se 1 (by rfl) ⟨1857056, by rfl⟩ : syracuseStep 2476075 = 3714113) B3714113
theorem B7432235 : Blo 1466553 7432235 := bstep (se 1 (by rfl) ⟨5574176, by rfl⟩ : syracuseStep 7432235 = 11148353) B11148353
theorem B3303467 : Blo 1466553 3303467 := bstep (se 1 (by rfl) ⟨2477600, by rfl⟩ : syracuseStep 3303467 = 4955201) B4955201
theorem B1468475 : Blo 1466553 1468475 := bstep (se 1 (by rfl) ⟨1101356, by rfl⟩ : syracuseStep 1468475 = 2202713) B2202713
theorem B3713111 : Blo 1466553 3713111 := bstep (se 1 (by rfl) ⟨2784833, by rfl⟩ : syracuseStep 3713111 = 5569667) B5569667
theorem B1468551 : Blo 1466553 1468551 := bstep (se 1 (by rfl) ⟨1101413, by rfl⟩ : syracuseStep 1468551 = 2202827) B2202827
theorem B2476217 : Blo 1466553 2476217 := bstep (se 2 (by rfl) ⟨928581, by rfl⟩ : syracuseStep 2476217 = 1857163) B1857163
theorem B1984699 : Blo 1466553 1984699 := bstep (se 1 (by rfl) ⟨1488524, by rfl⟩ : syracuseStep 1984699 = 2977049) B2977049
theorem B2787529 : Blo 1466553 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B4950287 : Blo 1466553 4950287 := bstep (se 1 (by rfl) ⟨3712715, by rfl⟩ : syracuseStep 4950287 = 7425431) B7425431
theorem B3713323 : Blo 1466553 3713323 := bstep (se 1 (by rfl) ⟨2784992, by rfl⟩ : syracuseStep 3713323 = 5569985) B5569985
theorem B4704571 : Blo 1466553 4704571 := bstep (se 1 (by rfl) ⟨3528428, by rfl⟩ : syracuseStep 4704571 = 7056857) B7056857
theorem B4704647 : Blo 1466553 4704647 := bstep (se 1 (by rfl) ⟨3528485, by rfl⟩ : syracuseStep 4704647 = 7056971) B7056971
theorem B3303827 : Blo 1466553 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B3713465 : Blo 1466553 3713465 := bstep (se 2 (by rfl) ⟨1392549, by rfl⟩ : syracuseStep 3713465 = 2785099) B2785099
theorem B2230729 : Blo 1466553 2230729 := bstep (se 2 (by rfl) ⟨836523, by rfl⟩ : syracuseStep 2230729 = 1673047) B1673047
theorem B3303881 : Blo 1466553 3303881 := bstep (se 2 (by rfl) ⟨1238955, by rfl⟩ : syracuseStep 3303881 = 2477911) B2477911
theorem B7424459 : Blo 1466553 7424459 := bstep (se 1 (by rfl) ⟨5568344, by rfl⟩ : syracuseStep 7424459 = 11136689) B11136689
theorem B4950557 : Blo 1466553 4950557 := bstep (se 3 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 4950557 = 1856459) B1856459
theorem B7047881 : Blo 1466553 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B5573357 : Blo 1466553 5573357 := bstep (se 3 (by rfl) ⟨1045004, by rfl⟩ : syracuseStep 5573357 = 2090009) B2090009
theorem B4180747 : Blo 1466553 4180747 := bstep (se 1 (by rfl) ⟨3135560, by rfl⟩ : syracuseStep 4180747 = 6271121) B6271121
theorem B7424783 : Blo 1466553 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B16714511 : Blo 1466553 16714511 := bstep (se 1 (by rfl) ⟨12535883, by rfl⟩ : syracuseStep 16714511 = 25071767) B25071767
theorem B3017515 : Blo 1466553 3017515 := bstep (se 1 (by rfl) ⟨2263136, by rfl⟩ : syracuseStep 3017515 = 4526273) B4526273
theorem B2476919 : Blo 1466553 2476919 := bstep (se 1 (by rfl) ⟨1857689, by rfl⟩ : syracuseStep 2476919 = 3715379) B3715379
theorem B1567631 : Blo 1466553 1567631 := bstep (se 1 (by rfl) ⟨1175723, by rfl⟩ : syracuseStep 1567631 = 2351447) B2351447
theorem B14101411 : Blo 1466553 14101411 := bstep (se 1 (by rfl) ⟨10576058, by rfl⟩ : syracuseStep 14101411 = 21152117) B21152117
theorem B14298059 : Blo 1466553 14298059 := bstep (se 1 (by rfl) ⟨10723544, by rfl⟩ : syracuseStep 14298059 = 21447089) B21447089
theorem B15870923 : Blo 1466553 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B1674247 : Blo 1466553 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B6196235 : Blo 1466553 6196235 := bstep (se 1 (by rfl) ⟨4647176, by rfl⟩ : syracuseStep 6196235 = 9294353) B9294353
theorem B4181021 : Blo 1466553 4181021 := bstep (se 3 (by rfl) ⟨783941, by rfl⟩ : syracuseStep 4181021 = 1567883) B1567883
theorem B36211799 : Blo 1466553 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B8039681 : Blo 1466553 8039681 := bstep (se 2 (by rfl) ⟨3014880, by rfl⟩ : syracuseStep 8039681 = 6029761) B6029761
theorem B15871265 : Blo 1466553 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B2477371 : Blo 1466553 2477371 := bstep (se 1 (by rfl) ⟨1858028, by rfl⟩ : syracuseStep 2477371 = 3716057) B3716057
theorem B16723259 : Blo 1466553 16723259 := bstep (se 1 (by rfl) ⟨12542444, by rfl⟩ : syracuseStep 16723259 = 25084889) B25084889
theorem B7433531 : Blo 1466553 7433531 := bstep (se 1 (by rfl) ⟨5575148, by rfl⟩ : syracuseStep 7433531 = 11150297) B11150297
theorem B1650055 : Blo 1466553 1650055 := bstep (se 1 (by rfl) ⟨1237541, by rfl⟩ : syracuseStep 1650055 = 2475083) B2475083
theorem B3714457 : Blo 1466553 3714457 := bstep (se 2 (by rfl) ⟨1392921, by rfl⟩ : syracuseStep 3714457 = 2785843) B2785843
theorem B5574041 : Blo 1466553 5574041 := bstep (se 2 (by rfl) ⟨2090265, by rfl⟩ : syracuseStep 5574041 = 4180531) B4180531
theorem B2477513 : Blo 1466553 2477513 := bstep (se 2 (by rfl) ⟨929067, by rfl⟩ : syracuseStep 2477513 = 1858135) B1858135
theorem B7433693 : Blo 1466553 7433693 := bstep (se 3 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 7433693 = 2787635) B2787635
theorem B1650235 : Blo 1466553 1650235 := bstep (se 1 (by rfl) ⟨1237676, by rfl⟩ : syracuseStep 1650235 = 2475353) B2475353
theorem B3714619 : Blo 1466553 3714619 := bstep (se 1 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 3714619 = 5571929) B5571929
theorem B3133075 : Blo 1466553 3133075 := bstep (se 1 (by rfl) ⟨2349806, by rfl⟩ : syracuseStep 3133075 = 4699613) B4699613
theorem B26758835 : Blo 1466553 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B3714761 : Blo 1466553 3714761 := bstep (se 2 (by rfl) ⟨1393035, by rfl⟩ : syracuseStep 3714761 = 2786071) B2786071
theorem B8359625 : Blo 1466553 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B7434017 : Blo 1466553 7434017 := bstep (se 2 (by rfl) ⟨2787756, by rfl⟩ : syracuseStep 7434017 = 5575513) B5575513
theorem B3764027 : Blo 1466553 3764027 := bstep (se 1 (by rfl) ⟨2823020, by rfl⟩ : syracuseStep 3764027 = 5646041) B5646041
theorem B3526487 : Blo 1466553 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B3968855 : Blo 1466553 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B4353907 : Blo 1466553 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B4951961 : Blo 1466553 4951961 := bstep (se 2 (by rfl) ⟨1856985, by rfl⟩ : syracuseStep 4951961 = 3713971) B3713971
theorem B1650703 : Blo 1466553 1650703 := bstep (se 1 (by rfl) ⟨1238027, by rfl⟩ : syracuseStep 1650703 = 2476055) B2476055
theorem B3715105 : Blo 1466553 3715105 := bstep (se 2 (by rfl) ⟨1393164, by rfl⟩ : syracuseStep 3715105 = 2786329) B2786329
theorem B6271019 : Blo 1466553 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B7426241 : Blo 1466553 7426241 := bstep (se 2 (by rfl) ⟨2784840, by rfl⟩ : syracuseStep 7426241 = 5569681) B5569681
theorem B2199851 : Blo 1466553 2199851 := bstep (se 1 (by rfl) ⟨1649888, by rfl⟩ : syracuseStep 2199851 = 3299777) B3299777
theorem B2199881 : Blo 1466553 2199881 := bstep (se 2 (by rfl) ⟨824955, by rfl⟩ : syracuseStep 2199881 = 1649911) B1649911
theorem B5575027 : Blo 1466553 5575027 := bstep (se 1 (by rfl) ⟨4181270, by rfl⟩ : syracuseStep 5575027 = 8362541) B8362541
theorem B2199995 : Blo 1466553 2199995 := bstep (se 1 (by rfl) ⟨1649996, by rfl⟩ : syracuseStep 2199995 = 3299993) B3299993
theorem B2200055 : Blo 1466553 2200055 := bstep (se 1 (by rfl) ⟨1650041, by rfl⟩ : syracuseStep 2200055 = 3300083) B3300083
theorem B1651207 : Blo 1466553 1651207 := bstep (se 1 (by rfl) ⟨1238405, by rfl⟩ : syracuseStep 1651207 = 2476811) B2476811
theorem B2200079 : Blo 1466553 2200079 := bstep (se 1 (by rfl) ⟨1650059, by rfl⟩ : syracuseStep 2200079 = 3300119) B3300119
theorem B9409067 : Blo 1466553 9409067 := bstep (se 1 (by rfl) ⟨7056800, by rfl⟩ : syracuseStep 9409067 = 14113601) B14113601
theorem B2200121 : Blo 1466553 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B4952663 : Blo 1466553 4952663 := bstep (se 1 (by rfl) ⟨3714497, by rfl⟩ : syracuseStep 4952663 = 7428995) B7428995
theorem B3715703 : Blo 1466553 3715703 := bstep (se 1 (by rfl) ⟨2786777, by rfl⟩ : syracuseStep 3715703 = 5573555) B5573555
theorem B1856135 : Blo 1466553 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B2200199 : Blo 1466553 2200199 := bstep (se 1 (by rfl) ⟨1650149, by rfl⟩ : syracuseStep 2200199 = 3300299) B3300299
theorem B2200235 : Blo 1466553 2200235 := bstep (se 1 (by rfl) ⟨1650176, by rfl⟩ : syracuseStep 2200235 = 3300353) B3300353
theorem B1651387 : Blo 1466553 1651387 := bstep (se 1 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 1651387 = 2477081) B2477081
theorem B2200265 : Blo 1466553 2200265 := bstep (se 2 (by rfl) ⟨825099, by rfl⟩ : syracuseStep 2200265 = 1650199) B1650199
theorem B2200379 : Blo 1466553 2200379 := bstep (se 1 (by rfl) ⟨1650284, by rfl⟩ : syracuseStep 2200379 = 3300569) B3300569
theorem B20083571 : Blo 1466553 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B2200439 : Blo 1466553 2200439 := bstep (se 1 (by rfl) ⟨1650329, by rfl⟩ : syracuseStep 2200439 = 3300659) B3300659
theorem B2200463 : Blo 1466553 2200463 := bstep (se 1 (by rfl) ⟨1650347, by rfl⟩ : syracuseStep 2200463 = 3300695) B3300695
theorem B2200505 : Blo 1466553 2200505 := bstep (se 2 (by rfl) ⟨825189, by rfl⟩ : syracuseStep 2200505 = 1650379) B1650379
theorem B2200583 : Blo 1466553 2200583 := bstep (se 1 (by rfl) ⟨1650437, by rfl⟩ : syracuseStep 2200583 = 3300875) B3300875
theorem B8352791 : Blo 1466553 8352791 := bstep (se 1 (by rfl) ⟨6264593, by rfl⟩ : syracuseStep 8352791 = 12529187) B12529187
theorem B2200619 : Blo 1466553 2200619 := bstep (se 1 (by rfl) ⟨1650464, by rfl⟩ : syracuseStep 2200619 = 3300929) B3300929
theorem B4953149 : Blo 1466553 4953149 := bstep (se 3 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 4953149 = 1857431) B1857431
theorem B71423045 : Blo 1466553 71423045 := bstep (se 4 (by rfl) ⟨6695910, by rfl⟩ : syracuseStep 71423045 = 13391821) B13391821
theorem B2200649 : Blo 1466553 2200649 := bstep (se 2 (by rfl) ⟨825243, by rfl⟩ : syracuseStep 2200649 = 1650487) B1650487
theorem B4461655 : Blo 1466553 4461655 := bstep (se 1 (by rfl) ⟨3346241, by rfl⟩ : syracuseStep 4461655 = 6692483) B6692483
theorem B1651855 : Blo 1466553 1651855 := bstep (se 1 (by rfl) ⟨1238891, by rfl⟩ : syracuseStep 1651855 = 2477783) B2477783
theorem B3527833 : Blo 1466553 3527833 := bstep (se 2 (by rfl) ⟨1322937, by rfl⟩ : syracuseStep 3527833 = 2645875) B2645875
theorem B2200763 : Blo 1466553 2200763 := bstep (se 1 (by rfl) ⟨1650572, by rfl⟩ : syracuseStep 2200763 = 3301145) B3301145
theorem B10573001 : Blo 1466553 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B2200823 : Blo 1466553 2200823 := bstep (se 1 (by rfl) ⟨1650617, by rfl⟩ : syracuseStep 2200823 = 3301235) B3301235
theorem B1856783 : Blo 1466553 1856783 := bstep (se 1 (by rfl) ⟨1392587, by rfl⟩ : syracuseStep 1856783 = 2785175) B2785175
theorem B2200847 : Blo 1466553 2200847 := bstep (se 1 (by rfl) ⟨1650635, by rfl⟩ : syracuseStep 2200847 = 3301271) B3301271
theorem B2200889 : Blo 1466553 2200889 := bstep (se 2 (by rfl) ⟨825333, by rfl⟩ : syracuseStep 2200889 = 1650667) B1650667
theorem B2200967 : Blo 1466553 2200967 := bstep (se 1 (by rfl) ⟨1650725, by rfl⟩ : syracuseStep 2200967 = 3301451) B3301451
theorem B2201003 : Blo 1466553 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B2201033 : Blo 1466553 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B17839565 : Blo 1466553 17839565 := bstep (se 3 (by rfl) ⟨3344918, by rfl⟩ : syracuseStep 17839565 = 6689837) B6689837
theorem B7427537 : Blo 1466553 7427537 := bstep (se 2 (by rfl) ⟨2785326, by rfl⟩ : syracuseStep 7427537 = 5570653) B5570653
theorem B2201147 : Blo 1466553 2201147 := bstep (se 1 (by rfl) ⟨1650860, by rfl⟩ : syracuseStep 2201147 = 3301721) B3301721
theorem B4462141 : Blo 1466553 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B8361539 : Blo 1466553 8361539 := bstep (se 1 (by rfl) ⟨6271154, by rfl⟩ : syracuseStep 8361539 = 12542309) B12542309
theorem B2201207 : Blo 1466553 2201207 := bstep (se 1 (by rfl) ⟨1650905, by rfl⟩ : syracuseStep 2201207 = 3301811) B3301811
theorem B2201231 : Blo 1466553 2201231 := bstep (se 1 (by rfl) ⟨1650923, by rfl⟩ : syracuseStep 2201231 = 3301847) B3301847
theorem B2201273 : Blo 1466553 2201273 := bstep (se 2 (by rfl) ⟨825477, by rfl⟩ : syracuseStep 2201273 = 1650955) B1650955
theorem B2201351 : Blo 1466553 2201351 := bstep (se 1 (by rfl) ⟨1651013, by rfl⟩ : syracuseStep 2201351 = 3302027) B3302027
theorem B5289761 : Blo 1466553 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B2201387 : Blo 1466553 2201387 := bstep (se 1 (by rfl) ⟨1651040, by rfl⟩ : syracuseStep 2201387 = 3302081) B3302081
theorem B16946995 : Blo 1466553 16946995 := bstep (se 1 (by rfl) ⟨12710246, by rfl⟩ : syracuseStep 16946995 = 25420493) B25420493
theorem B2201417 : Blo 1466553 2201417 := bstep (se 2 (by rfl) ⟨825531, by rfl⟩ : syracuseStep 2201417 = 1651063) B1651063
theorem B3716999 : Blo 1466553 3716999 := bstep (se 1 (by rfl) ⟨2787749, by rfl⟩ : syracuseStep 3716999 = 5575499) B5575499
theorem B5289875 : Blo 1466553 5289875 := bstep (se 1 (by rfl) ⟨3967406, by rfl⟩ : syracuseStep 5289875 = 7934813) B7934813
theorem B35698583 : Blo 1466553 35698583 := bstep (se 1 (by rfl) ⟨26773937, by rfl⟩ : syracuseStep 35698583 = 53547875) B53547875
theorem B3717049 : Blo 1466553 3717049 := bstep (se 2 (by rfl) ⟨1393893, by rfl⟩ : syracuseStep 3717049 = 2787787) B2787787
theorem B2201531 : Blo 1466553 2201531 := bstep (se 1 (by rfl) ⟨1651148, by rfl⟩ : syracuseStep 2201531 = 3302297) B3302297
theorem B2201591 : Blo 1466553 2201591 := bstep (se 1 (by rfl) ⟨1651193, by rfl⟩ : syracuseStep 2201591 = 3302387) B3302387
theorem B2201615 : Blo 1466553 2201615 := bstep (se 1 (by rfl) ⟨1651211, by rfl⟩ : syracuseStep 2201615 = 3302423) B3302423
theorem B2201657 : Blo 1466553 2201657 := bstep (se 2 (by rfl) ⟨825621, by rfl⟩ : syracuseStep 2201657 = 1651243) B1651243
theorem B2201735 : Blo 1466553 2201735 := bstep (se 1 (by rfl) ⟨1651301, by rfl⟩ : syracuseStep 2201735 = 3302603) B3302603
theorem B2201771 : Blo 1466553 2201771 := bstep (se 1 (by rfl) ⟨1651328, by rfl⟩ : syracuseStep 2201771 = 3302657) B3302657
theorem B2201801 : Blo 1466553 2201801 := bstep (se 2 (by rfl) ⟨825675, by rfl⟩ : syracuseStep 2201801 = 1651351) B1651351
theorem B2201915 : Blo 1466553 2201915 := bstep (se 1 (by rfl) ⟨1651436, by rfl⟩ : syracuseStep 2201915 = 3302873) B3302873
theorem B4462967 : Blo 1466553 4462967 := bstep (se 1 (by rfl) ⟨3347225, by rfl⟩ : syracuseStep 4462967 = 6694451) B6694451
theorem B2201975 : Blo 1466553 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B2201999 : Blo 1466553 2201999 := bstep (se 1 (by rfl) ⟨1651499, by rfl⟩ : syracuseStep 2201999 = 3302999) B3302999
theorem B4954553 : Blo 1466553 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B2202041 : Blo 1466553 2202041 := bstep (se 2 (by rfl) ⟨825765, by rfl⟩ : syracuseStep 2202041 = 1651531) B1651531
theorem B2202119 : Blo 1466553 2202119 := bstep (se 1 (by rfl) ⟨1651589, by rfl⟩ : syracuseStep 2202119 = 3303179) B3303179
theorem B2202155 : Blo 1466553 2202155 := bstep (se 1 (by rfl) ⟨1651616, by rfl⟩ : syracuseStep 2202155 = 3303233) B3303233
theorem B2202185 : Blo 1466553 2202185 := bstep (se 2 (by rfl) ⟨825819, by rfl⟩ : syracuseStep 2202185 = 1651639) B1651639
theorem B3299975 : Blo 1466553 3299975 := bstep (se 1 (by rfl) ⟨2474981, by rfl⟩ : syracuseStep 3299975 = 4949963) B4949963
theorem B2202299 : Blo 1466553 2202299 := bstep (se 1 (by rfl) ⟨1651724, by rfl⟩ : syracuseStep 2202299 = 3303449) B3303449
theorem B2202359 : Blo 1466553 2202359 := bstep (se 1 (by rfl) ⟨1651769, by rfl⟩ : syracuseStep 2202359 = 3303539) B3303539
theorem B2202383 : Blo 1466553 2202383 := bstep (se 1 (by rfl) ⟨1651787, by rfl⟩ : syracuseStep 2202383 = 3303575) B3303575
theorem B2202425 : Blo 1466553 2202425 := bstep (se 2 (by rfl) ⟨825909, by rfl⟩ : syracuseStep 2202425 = 1651819) B1651819
theorem B3300155 : Blo 1466553 3300155 := bstep (se 1 (by rfl) ⟨2475116, by rfl⟩ : syracuseStep 3300155 = 4950233) B4950233
theorem B2202503 : Blo 1466553 2202503 := bstep (se 1 (by rfl) ⟨1651877, by rfl⟩ : syracuseStep 2202503 = 3303755) B3303755
theorem B2202539 : Blo 1466553 2202539 := bstep (se 1 (by rfl) ⟨1651904, by rfl⟩ : syracuseStep 2202539 = 3303809) B3303809
theorem B3300281 : Blo 1466553 3300281 := bstep (se 2 (by rfl) ⟨1237605, by rfl⟩ : syracuseStep 3300281 = 2475211) B2475211
theorem B2202569 : Blo 1466553 2202569 := bstep (se 2 (by rfl) ⟨825963, by rfl⟩ : syracuseStep 2202569 = 1651927) B1651927
theorem B4955147 : Blo 1466553 4955147 := bstep (se 1 (by rfl) ⟨3716360, by rfl⟩ : syracuseStep 4955147 = 7432721) B7432721
theorem B2202683 : Blo 1466553 2202683 := bstep (se 1 (by rfl) ⟨1652012, by rfl⟩ : syracuseStep 2202683 = 3304025) B3304025
theorem B4955255 : Blo 1466553 4955255 := bstep (se 1 (by rfl) ⟨3716441, by rfl⟩ : syracuseStep 4955255 = 7432883) B7432883
theorem B2202743 : Blo 1466553 2202743 := bstep (se 1 (by rfl) ⟨1652057, by rfl⟩ : syracuseStep 2202743 = 3304115) B3304115
theorem B2202767 : Blo 1466553 2202767 := bstep (se 1 (by rfl) ⟨1652075, by rfl⟩ : syracuseStep 2202767 = 3304151) B3304151
theorem B2202809 : Blo 1466553 2202809 := bstep (se 2 (by rfl) ⟨826053, by rfl⟩ : syracuseStep 2202809 = 1652107) B1652107
theorem B97885381 : Blo 1466553 97885381 := bstep (se 4 (by rfl) ⟨9176754, by rfl⟩ : syracuseStep 97885381 = 18353509) B18353509
theorem B3300623 : Blo 1466553 3300623 := bstep (se 1 (by rfl) ⟨2475467, by rfl⟩ : syracuseStep 3300623 = 4950935) B4950935
theorem B3300641 : Blo 1466553 3300641 := bstep (se 2 (by rfl) ⟨1237740, by rfl⟩ : syracuseStep 3300641 = 2475481) B2475481
theorem B10575137 : Blo 1466553 10575137 := bstep (se 2 (by rfl) ⟨3965676, by rfl⟩ : syracuseStep 10575137 = 7931353) B7931353
theorem B7429643 : Blo 1466553 7429643 := bstep (se 1 (by rfl) ⟨5572232, by rfl⟩ : syracuseStep 7429643 = 11144465) B11144465
theorem B6028919 : Blo 1466553 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B5570167 : Blo 1466553 5570167 := bstep (se 1 (by rfl) ⟨4177625, by rfl⟩ : syracuseStep 5570167 = 8355251) B8355251
theorem B3300983 : Blo 1466553 3300983 := bstep (se 1 (by rfl) ⟨2475737, by rfl⟩ : syracuseStep 3300983 = 4951475) B4951475
theorem B1695367 : Blo 1466553 1695367 := bstep (se 1 (by rfl) ⟨1271525, by rfl⟩ : syracuseStep 1695367 = 2543051) B2543051
theorem B4464281 : Blo 1466553 4464281 := bstep (se 2 (by rfl) ⟨1674105, by rfl⟩ : syracuseStep 4464281 = 3348211) B3348211
theorem B7429805 : Blo 1466553 7429805 := bstep (se 3 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 7429805 = 2786177) B2786177
theorem B4955849 : Blo 1466553 4955849 := bstep (se 2 (by rfl) ⟨1858443, by rfl⟩ : syracuseStep 4955849 = 3716887) B3716887
theorem B3301163 : Blo 1466553 3301163 := bstep (se 1 (by rfl) ⟨2475872, by rfl⟩ : syracuseStep 3301163 = 4951745) B4951745
theorem B35708789 : Blo 1466553 35708789 := bstep (se 5 (by rfl) ⟨1673849, by rfl⟩ : syracuseStep 35708789 = 3347699) B3347699
theorem B1982395 : Blo 1466553 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B16523293 : Blo 1466553 16523293 := bstep (se 3 (by rfl) ⟨3098117, by rfl⟩ : syracuseStep 16523293 = 6196235) B6196235
theorem B1982503 : Blo 1466553 1982503 := bstep (se 1 (by rfl) ⟨1486877, by rfl⟩ : syracuseStep 1982503 = 2973755) B2973755
theorem B3301433 : Blo 1466553 3301433 := bstep (se 2 (by rfl) ⟨1238037, by rfl⟩ : syracuseStep 3301433 = 2476075) B2476075
theorem B5570639 : Blo 1466553 5570639 := bstep (se 1 (by rfl) ⟨4177979, by rfl⟩ : syracuseStep 5570639 = 8355959) B8355959
theorem B20086865 : Blo 1466553 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B7929971 : Blo 1466553 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B2785403 : Blo 1466553 2785403 := bstep (se 1 (by rfl) ⟨2089052, by rfl⟩ : syracuseStep 2785403 = 4178105) B4178105
theorem B1466567 : Blo 1466553 1466567 := bstep (se 1 (by rfl) ⟨1099925, by rfl⟩ : syracuseStep 1466567 = 2199851) B2199851
theorem B1466587 : Blo 1466553 1466587 := bstep (se 1 (by rfl) ⟨1099940, by rfl⟩ : syracuseStep 1466587 = 2199881) B2199881
theorem B2646265 : Blo 1466553 2646265 := bstep (se 2 (by rfl) ⟨992349, by rfl⟩ : syracuseStep 2646265 = 1984699) B1984699
theorem B1466663 : Blo 1466553 1466663 := bstep (se 1 (by rfl) ⟨1099997, by rfl⟩ : syracuseStep 1466663 = 2199995) B2199995
theorem B1466703 : Blo 1466553 1466703 := bstep (se 1 (by rfl) ⟨1100027, by rfl⟩ : syracuseStep 1466703 = 2200055) B2200055
theorem B1466719 : Blo 1466553 1466719 := bstep (se 1 (by rfl) ⟨1100039, by rfl⟩ : syracuseStep 1466719 = 2200079) B2200079
theorem B1466747 : Blo 1466553 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B3301775 : Blo 1466553 3301775 := bstep (se 1 (by rfl) ⟨2476331, by rfl⟩ : syracuseStep 3301775 = 4952663) B4952663
theorem B1466799 : Blo 1466553 1466799 := bstep (se 1 (by rfl) ⟨1100099, by rfl⟩ : syracuseStep 1466799 = 2200199) B2200199
theorem B1466823 : Blo 1466553 1466823 := bstep (se 1 (by rfl) ⟨1100117, by rfl⟩ : syracuseStep 1466823 = 2200235) B2200235
theorem B1466843 : Blo 1466553 1466843 := bstep (se 1 (by rfl) ⟨1100132, by rfl⟩ : syracuseStep 1466843 = 2200265) B2200265
theorem B1466919 : Blo 1466553 1466919 := bstep (se 1 (by rfl) ⟨1100189, by rfl⟩ : syracuseStep 1466919 = 2200379) B2200379
theorem B1466959 : Blo 1466553 1466959 := bstep (se 1 (by rfl) ⟨1100219, by rfl⟩ : syracuseStep 1466959 = 2200439) B2200439
theorem B1466975 : Blo 1466553 1466975 := bstep (se 1 (by rfl) ⟨1100231, by rfl⟩ : syracuseStep 1466975 = 2200463) B2200463
theorem B2785889 : Blo 1466553 2785889 := bstep (se 2 (by rfl) ⟨1044708, by rfl⟩ : syracuseStep 2785889 = 2089417) B2089417
theorem B1467003 : Blo 1466553 1467003 := bstep (se 1 (by rfl) ⟨1100252, by rfl⟩ : syracuseStep 1467003 = 2200505) B2200505
theorem B1467055 : Blo 1466553 1467055 := bstep (se 1 (by rfl) ⟨1100291, by rfl⟩ : syracuseStep 1467055 = 2200583) B2200583
theorem B1467079 : Blo 1466553 1467079 := bstep (se 1 (by rfl) ⟨1100309, by rfl⟩ : syracuseStep 1467079 = 2200619) B2200619
theorem B23790289 : Blo 1466553 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B3302099 : Blo 1466553 3302099 := bstep (se 1 (by rfl) ⟨2476574, by rfl⟩ : syracuseStep 3302099 = 4953149) B4953149
theorem B4702931 : Blo 1466553 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B1467099 : Blo 1466553 1467099 := bstep (se 1 (by rfl) ⟨1100324, by rfl⟩ : syracuseStep 1467099 = 2200649) B2200649
theorem B1467175 : Blo 1466553 1467175 := bstep (se 1 (by rfl) ⟨1100381, by rfl⟩ : syracuseStep 1467175 = 2200763) B2200763
theorem B1467215 : Blo 1466553 1467215 := bstep (se 1 (by rfl) ⟨1100411, by rfl⟩ : syracuseStep 1467215 = 2200823) B2200823
theorem B1467231 : Blo 1466553 1467231 := bstep (se 1 (by rfl) ⟨1100423, by rfl⟩ : syracuseStep 1467231 = 2200847) B2200847
theorem B1467259 : Blo 1466553 1467259 := bstep (se 1 (by rfl) ⟨1100444, by rfl⟩ : syracuseStep 1467259 = 2200889) B2200889
theorem B11142035 : Blo 1466553 11142035 := bstep (se 1 (by rfl) ⟨8356526, by rfl⟩ : syracuseStep 11142035 = 16713053) B16713053
theorem B1467311 : Blo 1466553 1467311 := bstep (se 1 (by rfl) ⟨1100483, by rfl⟩ : syracuseStep 1467311 = 2200967) B2200967
theorem B2786231 : Blo 1466553 2786231 := bstep (se 1 (by rfl) ⟨2089673, by rfl⟩ : syracuseStep 2786231 = 4179347) B4179347
theorem B1467335 : Blo 1466553 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B1467355 : Blo 1466553 1467355 := bstep (se 1 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 1467355 = 2201033) B2201033
theorem B11289619 : Blo 1466553 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B1467431 : Blo 1466553 1467431 := bstep (se 1 (by rfl) ⟨1100573, by rfl⟩ : syracuseStep 1467431 = 2201147) B2201147
theorem B4023353 : Blo 1466553 4023353 := bstep (se 2 (by rfl) ⟨1508757, by rfl⟩ : syracuseStep 4023353 = 3017515) B3017515
theorem B1467471 : Blo 1466553 1467471 := bstep (se 1 (by rfl) ⟨1100603, by rfl⟩ : syracuseStep 1467471 = 2201207) B2201207
theorem B1467487 : Blo 1466553 1467487 := bstep (se 1 (by rfl) ⟨1100615, by rfl⟩ : syracuseStep 1467487 = 2201231) B2201231
theorem B1467515 : Blo 1466553 1467515 := bstep (se 1 (by rfl) ⟨1100636, by rfl⟩ : syracuseStep 1467515 = 2201273) B2201273
theorem B1467567 : Blo 1466553 1467567 := bstep (se 1 (by rfl) ⟨1100675, by rfl⟩ : syracuseStep 1467567 = 2201351) B2201351
theorem B1467591 : Blo 1466553 1467591 := bstep (se 1 (by rfl) ⟨1100693, by rfl⟩ : syracuseStep 1467591 = 2201387) B2201387
theorem B18801881 : Blo 1466553 18801881 := bstep (se 2 (by rfl) ⟨7050705, by rfl⟩ : syracuseStep 18801881 = 14101411) B14101411
theorem B1467611 : Blo 1466553 1467611 := bstep (se 1 (by rfl) ⟨1100708, by rfl⟩ : syracuseStep 1467611 = 2201417) B2201417
theorem B23799055 : Blo 1466553 23799055 := bstep (se 1 (by rfl) ⟨17849291, by rfl⟩ : syracuseStep 23799055 = 35698583) B35698583
theorem B1467687 : Blo 1466553 1467687 := bstep (se 1 (by rfl) ⟨1100765, by rfl⟩ : syracuseStep 1467687 = 2201531) B2201531
theorem B2786633 : Blo 1466553 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B1467727 : Blo 1466553 1467727 := bstep (se 1 (by rfl) ⟨1100795, by rfl⟩ : syracuseStep 1467727 = 2201591) B2201591
theorem B1467743 : Blo 1466553 1467743 := bstep (se 1 (by rfl) ⟨1100807, by rfl⟩ : syracuseStep 1467743 = 2201615) B2201615
theorem B1467771 : Blo 1466553 1467771 := bstep (se 1 (by rfl) ⟨1100828, by rfl⟩ : syracuseStep 1467771 = 2201657) B2201657
theorem B2475407 : Blo 1466553 2475407 := bstep (se 1 (by rfl) ⟨1856555, by rfl⟩ : syracuseStep 2475407 = 3713111) B3713111
theorem B1467823 : Blo 1466553 1467823 := bstep (se 1 (by rfl) ⟨1100867, by rfl⟩ : syracuseStep 1467823 = 2201735) B2201735
theorem B1467847 : Blo 1466553 1467847 := bstep (se 1 (by rfl) ⟨1100885, by rfl⟩ : syracuseStep 1467847 = 2201771) B2201771
theorem B5948873 : Blo 1466553 5948873 := bstep (se 2 (by rfl) ⟨2230827, by rfl⟩ : syracuseStep 5948873 = 4461655) B4461655
theorem B1467867 : Blo 1466553 1467867 := bstep (se 1 (by rfl) ⟨1100900, by rfl⟩ : syracuseStep 1467867 = 2201801) B2201801
theorem B4703777 : Blo 1466553 4703777 := bstep (se 2 (by rfl) ⟨1763916, by rfl⟩ : syracuseStep 4703777 = 3527833) B3527833
theorem B1467943 : Blo 1466553 1467943 := bstep (se 1 (by rfl) ⟨1100957, by rfl⟩ : syracuseStep 1467943 = 2201915) B2201915
theorem B2975311 : Blo 1466553 2975311 := bstep (se 1 (by rfl) ⟨2231483, by rfl⟩ : syracuseStep 2975311 = 4462967) B4462967
theorem B1467983 : Blo 1466553 1467983 := bstep (se 1 (by rfl) ⟨1100987, by rfl⟩ : syracuseStep 1467983 = 2201975) B2201975
theorem B1467999 : Blo 1466553 1467999 := bstep (se 1 (by rfl) ⟨1100999, by rfl⟩ : syracuseStep 1467999 = 2201999) B2201999
theorem B42911333 : Blo 1466553 42911333 := bstep (se 4 (by rfl) ⟨4022937, by rfl⟩ : syracuseStep 42911333 = 8045875) B8045875
theorem B2475643 : Blo 1466553 2475643 := bstep (se 1 (by rfl) ⟨1856732, by rfl⟩ : syracuseStep 2475643 = 3713465) B3713465
theorem B3303035 : Blo 1466553 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B1468027 : Blo 1466553 1468027 := bstep (se 1 (by rfl) ⟨1101020, by rfl⟩ : syracuseStep 1468027 = 2202041) B2202041
theorem B4949639 : Blo 1466553 4949639 := bstep (se 1 (by rfl) ⟨3712229, by rfl⟩ : syracuseStep 4949639 = 7424459) B7424459
theorem B1468079 : Blo 1466553 1468079 := bstep (se 1 (by rfl) ⟨1101059, by rfl⟩ : syracuseStep 1468079 = 2202119) B2202119
theorem B4949693 : Blo 1466553 4949693 := bstep (se 3 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 4949693 = 1856135) B1856135
theorem B1468103 : Blo 1466553 1468103 := bstep (se 1 (by rfl) ⟨1101077, by rfl⟩ : syracuseStep 1468103 = 2202155) B2202155
theorem B1468123 : Blo 1466553 1468123 := bstep (se 1 (by rfl) ⟨1101092, by rfl⟩ : syracuseStep 1468123 = 2202185) B2202185
theorem B3303161 : Blo 1466553 3303161 := bstep (se 2 (by rfl) ⟨1238685, by rfl⟩ : syracuseStep 3303161 = 2477371) B2477371
theorem B1468199 : Blo 1466553 1468199 := bstep (se 1 (by rfl) ⟨1101149, by rfl⟩ : syracuseStep 1468199 = 2202299) B2202299
theorem B1468239 : Blo 1466553 1468239 := bstep (se 1 (by rfl) ⟨1101179, by rfl⟩ : syracuseStep 1468239 = 2202359) B2202359
theorem B4949855 : Blo 1466553 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B11143007 : Blo 1466553 11143007 := bstep (se 1 (by rfl) ⟨8357255, by rfl⟩ : syracuseStep 11143007 = 16714511) B16714511
theorem B1468255 : Blo 1466553 1468255 := bstep (se 1 (by rfl) ⟨1101191, by rfl⟩ : syracuseStep 1468255 = 2202383) B2202383
theorem B1468283 : Blo 1466553 1468283 := bstep (se 1 (by rfl) ⟨1101212, by rfl⟩ : syracuseStep 1468283 = 2202425) B2202425
theorem B1468335 : Blo 1466553 1468335 := bstep (se 1 (by rfl) ⟨1101251, by rfl⟩ : syracuseStep 1468335 = 2202503) B2202503
theorem B1468359 : Blo 1466553 1468359 := bstep (se 1 (by rfl) ⟨1101269, by rfl⟩ : syracuseStep 1468359 = 2202539) B2202539
theorem B1468379 : Blo 1466553 1468379 := bstep (se 1 (by rfl) ⟨1101284, by rfl⟩ : syracuseStep 1468379 = 2202569) B2202569
theorem B4950017 : Blo 1466553 4950017 := bstep (se 2 (by rfl) ⟨1856256, by rfl⟩ : syracuseStep 4950017 = 3712513) B3712513
theorem B3303431 : Blo 1466553 3303431 := bstep (se 1 (by rfl) ⟨2477573, by rfl⟩ : syracuseStep 3303431 = 4955147) B4955147
theorem B2787347 : Blo 1466553 2787347 := bstep (se 1 (by rfl) ⟨2090510, by rfl⟩ : syracuseStep 2787347 = 4181021) B4181021
theorem B1468455 : Blo 1466553 1468455 := bstep (se 1 (by rfl) ⟨1101341, by rfl⟩ : syracuseStep 1468455 = 2202683) B2202683
theorem B2787385 : Blo 1466553 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B3303503 : Blo 1466553 3303503 := bstep (se 1 (by rfl) ⟨2477627, by rfl⟩ : syracuseStep 3303503 = 4955255) B4955255
theorem B1468495 : Blo 1466553 1468495 := bstep (se 1 (by rfl) ⟨1101371, by rfl⟩ : syracuseStep 1468495 = 2202743) B2202743
theorem B5949521 : Blo 1466553 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1468511 : Blo 1466553 1468511 := bstep (se 1 (by rfl) ⟨1101383, by rfl⟩ : syracuseStep 1468511 = 2202767) B2202767
theorem B1468539 : Blo 1466553 1468539 := bstep (se 1 (by rfl) ⟨1101404, by rfl⟩ : syracuseStep 1468539 = 2202809) B2202809
theorem B9398429 : Blo 1466553 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B10037405 : Blo 1466553 10037405 := bstep (se 3 (by rfl) ⟨1882013, by rfl⟩ : syracuseStep 10037405 = 3764027) B3764027
theorem B5359787 : Blo 1466553 5359787 := bstep (se 1 (by rfl) ⟨4019840, by rfl⟩ : syracuseStep 5359787 = 8039681) B8039681
theorem B2787689 : Blo 1466553 2787689 := bstep (se 2 (by rfl) ⟨1045383, by rfl⟩ : syracuseStep 2787689 = 2090767) B2090767
theorem B4180349 : Blo 1466553 4180349 := bstep (se 3 (by rfl) ⟨783815, by rfl⟩ : syracuseStep 4180349 = 1567631) B1567631
theorem B11897221 : Blo 1466553 11897221 := bstep (se 4 (by rfl) ⟨1115364, by rfl⟩ : syracuseStep 11897221 = 2230729) B2230729
theorem B22595993 : Blo 1466553 22595993 := bstep (se 2 (by rfl) ⟨8473497, by rfl⟩ : syracuseStep 22595993 = 16946995) B16946995
theorem B2976187 : Blo 1466553 2976187 := bstep (se 1 (by rfl) ⟨2232140, by rfl⟩ : syracuseStep 2976187 = 4464281) B4464281
theorem B2476507 : Blo 1466553 2476507 := bstep (se 1 (by rfl) ⟨1857380, by rfl⟩ : syracuseStep 2476507 = 3714761) B3714761
theorem B5573083 : Blo 1466553 5573083 := bstep (se 1 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 5573083 = 8359625) B8359625
theorem B3303899 : Blo 1466553 3303899 := bstep (se 1 (by rfl) ⟨2477924, by rfl⟩ : syracuseStep 3303899 = 4955849) B4955849
theorem B38128157 : Blo 1466553 38128157 := bstep (se 3 (by rfl) ⟨7149029, by rfl⟩ : syracuseStep 38128157 = 14298059) B14298059
theorem B4180679 : Blo 1466553 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B4950827 : Blo 1466553 4950827 := bstep (se 1 (by rfl) ⟨3713120, by rfl⟩ : syracuseStep 4950827 = 7426241) B7426241
theorem B4074515 : Blo 1466553 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B4951097 : Blo 1466553 4951097 := bstep (se 2 (by rfl) ⟨1856661, by rfl⟩ : syracuseStep 4951097 = 3713323) B3713323
theorem B2477135 : Blo 1466553 2477135 := bstep (se 1 (by rfl) ⟨1857851, by rfl⟩ : syracuseStep 2477135 = 3715703) B3715703
theorem B7433369 : Blo 1466553 7433369 := bstep (se 2 (by rfl) ⟨2787513, by rfl⟩ : syracuseStep 7433369 = 5575027) B5575027
theorem B3714295 : Blo 1466553 3714295 := bstep (se 1 (by rfl) ⟨2785721, by rfl⟩ : syracuseStep 3714295 = 5571443) B5571443
theorem B13389047 : Blo 1466553 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B4951421 : Blo 1466553 4951421 := bstep (se 3 (by rfl) ⟨928391, by rfl⟩ : syracuseStep 4951421 = 1856783) B1856783
theorem B47615363 : Blo 1466553 47615363 := bstep (se 1 (by rfl) ⟨35711522, by rfl⟩ : syracuseStep 47615363 = 71423045) B71423045
theorem B7048667 : Blo 1466553 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B3714569 : Blo 1466553 3714569 := bstep (se 2 (by rfl) ⟨1392963, by rfl⟩ : syracuseStep 3714569 = 2785927) B2785927
theorem B3714599 : Blo 1466553 3714599 := bstep (se 1 (by rfl) ⟨2785949, by rfl⟩ : syracuseStep 3714599 = 5571899) B5571899
theorem B26766935 : Blo 1466553 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B4951691 : Blo 1466553 4951691 := bstep (se 1 (by rfl) ⟨3713768, by rfl⟩ : syracuseStep 4951691 = 7427537) B7427537
theorem B10038923 : Blo 1466553 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B5574329 : Blo 1466553 5574329 := bstep (se 2 (by rfl) ⟨2090373, by rfl⟩ : syracuseStep 5574329 = 4180747) B4180747
theorem B12545725 : Blo 1466553 12545725 := bstep (se 3 (by rfl) ⟨2352323, by rfl⟩ : syracuseStep 12545725 = 4704647) B4704647
theorem B5574359 : Blo 1466553 5574359 := bstep (se 1 (by rfl) ⟨4180769, by rfl⟩ : syracuseStep 5574359 = 8361539) B8361539
theorem B3714923 : Blo 1466553 3714923 := bstep (se 1 (by rfl) ⟨2786192, by rfl⟩ : syracuseStep 3714923 = 5572385) B5572385
theorem B3526507 : Blo 1466553 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B2477999 : Blo 1466553 2477999 := bstep (se 1 (by rfl) ⟨1858499, by rfl⟩ : syracuseStep 2477999 = 3716999) B3716999
theorem B3526583 : Blo 1466553 3526583 := bstep (se 1 (by rfl) ⟨2644937, by rfl⟩ : syracuseStep 3526583 = 5289875) B5289875
theorem B2232329 : Blo 1466553 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B22900751 : Blo 1466553 22900751 := bstep (se 1 (by rfl) ⟨17175563, by rfl⟩ : syracuseStep 22900751 = 34351127) B34351127
theorem B1650811 : Blo 1466553 1650811 := bstep (se 1 (by rfl) ⟨1238108, by rfl⟩ : syracuseStep 1650811 = 2476217) B2476217
theorem B2199983 : Blo 1466553 2199983 := bstep (se 1 (by rfl) ⟨1649987, by rfl⟩ : syracuseStep 2199983 = 3299975) B3299975
theorem B4698587 : Blo 1466553 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B3715571 : Blo 1466553 3715571 := bstep (se 1 (by rfl) ⟨2786678, by rfl⟩ : syracuseStep 3715571 = 5573357) B5573357
theorem B2200073 : Blo 1466553 2200073 := bstep (se 2 (by rfl) ⟨825027, by rfl⟩ : syracuseStep 2200073 = 1650055) B1650055
theorem B4952609 : Blo 1466553 4952609 := bstep (se 2 (by rfl) ⟨1857228, by rfl⟩ : syracuseStep 4952609 = 3714457) B3714457
theorem B2200103 : Blo 1466553 2200103 := bstep (se 1 (by rfl) ⟨1650077, by rfl⟩ : syracuseStep 2200103 = 3300155) B3300155
theorem B1651279 : Blo 1466553 1651279 := bstep (se 1 (by rfl) ⟨1238459, by rfl⟩ : syracuseStep 1651279 = 2476919) B2476919
theorem B2200187 : Blo 1466553 2200187 := bstep (se 1 (by rfl) ⟨1650140, by rfl⟩ : syracuseStep 2200187 = 3300281) B3300281
theorem B10580615 : Blo 1466553 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B2200313 : Blo 1466553 2200313 := bstep (se 2 (by rfl) ⟨825117, by rfl⟩ : syracuseStep 2200313 = 1650235) B1650235
theorem B4952825 : Blo 1466553 4952825 := bstep (se 2 (by rfl) ⟨1857309, by rfl⟩ : syracuseStep 4952825 = 3714619) B3714619
theorem B7426889 : Blo 1466553 7426889 := bstep (se 2 (by rfl) ⟨2785083, by rfl⟩ : syracuseStep 7426889 = 5570167) B5570167
theorem B2200415 : Blo 1466553 2200415 := bstep (se 1 (by rfl) ⟨1650311, by rfl⟩ : syracuseStep 2200415 = 3300623) B3300623
theorem B2200427 : Blo 1466553 2200427 := bstep (se 1 (by rfl) ⟨1650320, by rfl⟩ : syracuseStep 2200427 = 3300641) B3300641
theorem B7050091 : Blo 1466553 7050091 := bstep (se 1 (by rfl) ⟨5287568, by rfl⟩ : syracuseStep 7050091 = 10575137) B10575137
theorem B10580843 : Blo 1466553 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B3716027 : Blo 1466553 3716027 := bstep (se 1 (by rfl) ⟨2787020, by rfl⟩ : syracuseStep 3716027 = 5574041) B5574041
theorem B1651675 : Blo 1466553 1651675 := bstep (se 1 (by rfl) ⟨1238756, by rfl⟩ : syracuseStep 1651675 = 2477513) B2477513
theorem B4953095 : Blo 1466553 4953095 := bstep (se 1 (by rfl) ⟨3714821, by rfl⟩ : syracuseStep 4953095 = 7429643) B7429643
theorem B4019279 : Blo 1466553 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B2200655 : Blo 1466553 2200655 := bstep (se 1 (by rfl) ⟨1650491, by rfl⟩ : syracuseStep 2200655 = 3300983) B3300983
theorem B4953203 : Blo 1466553 4953203 := bstep (se 1 (by rfl) ⟨3714902, by rfl⟩ : syracuseStep 4953203 = 7429805) B7429805
theorem B17839223 : Blo 1466553 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B5805209 : Blo 1466553 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B2200775 : Blo 1466553 2200775 := bstep (se 1 (by rfl) ⟨1650581, by rfl⟩ : syracuseStep 2200775 = 3301163) B3301163
theorem B2643193 : Blo 1466553 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B2200937 : Blo 1466553 2200937 := bstep (se 2 (by rfl) ⟨825351, by rfl⟩ : syracuseStep 2200937 = 1650703) B1650703
theorem B4953473 : Blo 1466553 4953473 := bstep (se 2 (by rfl) ⟨1857552, by rfl⟩ : syracuseStep 4953473 = 3715105) B3715105
theorem B2201015 : Blo 1466553 2201015 := bstep (se 1 (by rfl) ⟨1650761, by rfl⟩ : syracuseStep 2201015 = 3301523) B3301523
theorem B2201051 : Blo 1466553 2201051 := bstep (se 1 (by rfl) ⟨1650788, by rfl⟩ : syracuseStep 2201051 = 3301577) B3301577
theorem B3716705 : Blo 1466553 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B6272711 : Blo 1466553 6272711 := bstep (se 1 (by rfl) ⟨4704533, by rfl⟩ : syracuseStep 6272711 = 9409067) B9409067
theorem B6272761 : Blo 1466553 6272761 := bstep (se 2 (by rfl) ⟨2352285, by rfl⟩ : syracuseStep 6272761 = 4704571) B4704571
theorem B2201519 : Blo 1466553 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B2201609 : Blo 1466553 2201609 := bstep (se 2 (by rfl) ⟨825603, by rfl⟩ : syracuseStep 2201609 = 1651207) B1651207
theorem B5568527 : Blo 1466553 5568527 := bstep (se 1 (by rfl) ⟨4176395, by rfl⟩ : syracuseStep 5568527 = 8352791) B8352791
theorem B2201639 : Blo 1466553 2201639 := bstep (se 1 (by rfl) ⟨1651229, by rfl⟩ : syracuseStep 2201639 = 3302459) B3302459
theorem B7428185 : Blo 1466553 7428185 := bstep (se 2 (by rfl) ⟨2785569, by rfl⟩ : syracuseStep 7428185 = 5571139) B5571139
theorem B2201723 : Blo 1466553 2201723 := bstep (se 1 (by rfl) ⟨1651292, by rfl⟩ : syracuseStep 2201723 = 3302585) B3302585
theorem B4954283 : Blo 1466553 4954283 := bstep (se 1 (by rfl) ⟨3715712, by rfl⟩ : syracuseStep 4954283 = 7431425) B7431425
theorem B2201849 : Blo 1466553 2201849 := bstep (se 2 (by rfl) ⟨825693, by rfl⟩ : syracuseStep 2201849 = 1651387) B1651387
theorem B11893043 : Blo 1466553 11893043 := bstep (se 1 (by rfl) ⟨8919782, by rfl⟩ : syracuseStep 11893043 = 17839565) B17839565
theorem B2201951 : Blo 1466553 2201951 := bstep (se 1 (by rfl) ⟨1651463, by rfl⟩ : syracuseStep 2201951 = 3302927) B3302927
theorem B2201963 : Blo 1466553 2201963 := bstep (se 1 (by rfl) ⟨1651472, by rfl⟩ : syracuseStep 2201963 = 3302945) B3302945
theorem B2349499 : Blo 1466553 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B3299849 : Blo 1466553 3299849 := bstep (se 2 (by rfl) ⟨1237443, by rfl⟩ : syracuseStep 3299849 = 2474887) B2474887
theorem B2644519 : Blo 1466553 2644519 := bstep (se 1 (by rfl) ⟨1983389, by rfl⟩ : syracuseStep 2644519 = 3966779) B3966779
theorem B2579023 : Blo 1466553 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B2202191 : Blo 1466553 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B2644577 : Blo 1466553 2644577 := bstep (se 2 (by rfl) ⟨991716, by rfl⟩ : syracuseStep 2644577 = 1983433) B1983433
theorem B4954823 : Blo 1466553 4954823 := bstep (se 1 (by rfl) ⟨3716117, by rfl⟩ : syracuseStep 4954823 = 7432235) B7432235
theorem B2202311 : Blo 1466553 2202311 := bstep (se 1 (by rfl) ⟨1651733, by rfl⟩ : syracuseStep 2202311 = 3303467) B3303467
theorem B3300191 : Blo 1466553 3300191 := bstep (se 1 (by rfl) ⟨2475143, by rfl⟩ : syracuseStep 3300191 = 4950287) B4950287
theorem B2202473 : Blo 1466553 2202473 := bstep (se 2 (by rfl) ⟨825927, by rfl⟩ : syracuseStep 2202473 = 1651855) B1651855
theorem B130513841 : Blo 1466553 130513841 := bstep (se 2 (by rfl) ⟨48942690, by rfl⟩ : syracuseStep 130513841 = 97885381) B97885381
theorem B2202551 : Blo 1466553 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B2202587 : Blo 1466553 2202587 := bstep (se 1 (by rfl) ⟨1651940, by rfl⟩ : syracuseStep 2202587 = 3303881) B3303881
theorem B3300371 : Blo 1466553 3300371 := bstep (se 1 (by rfl) ⟨2475278, by rfl⟩ : syracuseStep 3300371 = 4950557) B4950557
theorem B34331921 : Blo 1466553 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B10575193 : Blo 1466553 10575193 := bstep (se 2 (by rfl) ⟨3965697, by rfl⟩ : syracuseStep 10575193 = 7931395) B7931395
theorem B3300713 : Blo 1466553 3300713 := bstep (se 2 (by rfl) ⟨1237767, by rfl⟩ : syracuseStep 3300713 = 2475535) B2475535
theorem B24141199 : Blo 1466553 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B2260489 : Blo 1466553 2260489 := bstep (se 2 (by rfl) ⟨847683, by rfl⟩ : syracuseStep 2260489 = 1695367) B1695367
theorem B4177433 : Blo 1466553 4177433 := bstep (se 2 (by rfl) ⟨1566537, by rfl⟩ : syracuseStep 4177433 = 3133075) B3133075
theorem B11148839 : Blo 1466553 11148839 := bstep (se 1 (by rfl) ⟨8361629, by rfl⟩ : syracuseStep 11148839 = 16723259) B16723259
theorem B4955687 : Blo 1466553 4955687 := bstep (se 1 (by rfl) ⟨3716765, by rfl⟩ : syracuseStep 4955687 = 7433531) B7433531
theorem B95223437 : Blo 1466553 95223437 := bstep (se 3 (by rfl) ⟨17854394, by rfl⟩ : syracuseStep 95223437 = 35708789) B35708789
theorem B4955795 : Blo 1466553 4955795 := bstep (se 1 (by rfl) ⟨3716846, by rfl⟩ : syracuseStep 4955795 = 7433693) B7433693
theorem B4956011 : Blo 1466553 4956011 := bstep (se 1 (by rfl) ⟨3717008, by rfl⟩ : syracuseStep 4956011 = 7434017) B7434017
theorem B2350991 : Blo 1466553 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B2645903 : Blo 1466553 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B4956065 : Blo 1466553 4956065 := bstep (se 2 (by rfl) ⟨1858524, by rfl⟩ : syracuseStep 4956065 = 3717049) B3717049
theorem B3301307 : Blo 1466553 3301307 := bstep (se 1 (by rfl) ⟨2475980, by rfl⟩ : syracuseStep 3301307 = 4951961) B4951961
theorem B1466655 : Blo 1466553 1466655 := bstep (se 1 (by rfl) ⟨1099991, by rfl⟩ : syracuseStep 1466655 = 2199983) B2199983
theorem B1466715 : Blo 1466553 1466715 := bstep (se 1 (by rfl) ⟨1100036, by rfl⟩ : syracuseStep 1466715 = 2200073) B2200073
theorem B3301739 : Blo 1466553 3301739 := bstep (se 1 (by rfl) ⟨2476304, by rfl⟩ : syracuseStep 3301739 = 4952609) B4952609
theorem B1466735 : Blo 1466553 1466735 := bstep (se 1 (by rfl) ⟨1100051, by rfl⟩ : syracuseStep 1466735 = 2200103) B2200103
theorem B15868325 : Blo 1466553 15868325 := bstep (se 4 (by rfl) ⟨1487655, by rfl⟩ : syracuseStep 15868325 = 2975311) B2975311
theorem B1466791 : Blo 1466553 1466791 := bstep (se 1 (by rfl) ⟨1100093, by rfl⟩ : syracuseStep 1466791 = 2200187) B2200187
theorem B7053743 : Blo 1466553 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B1466875 : Blo 1466553 1466875 := bstep (se 1 (by rfl) ⟨1100156, by rfl⟩ : syracuseStep 1466875 = 2200313) B2200313
theorem B3301883 : Blo 1466553 3301883 := bstep (se 1 (by rfl) ⟨2476412, by rfl⟩ : syracuseStep 3301883 = 4952825) B4952825
theorem B1466943 : Blo 1466553 1466943 := bstep (se 1 (by rfl) ⟨1100207, by rfl⟩ : syracuseStep 1466943 = 2200415) B2200415
theorem B1466951 : Blo 1466553 1466951 := bstep (se 1 (by rfl) ⟨1100213, by rfl⟩ : syracuseStep 1466951 = 2200427) B2200427
theorem B7053895 : Blo 1466553 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B3302009 : Blo 1466553 3302009 := bstep (se 2 (by rfl) ⟨1238253, by rfl⟩ : syracuseStep 3302009 = 2476507) B2476507
theorem B7430777 : Blo 1466553 7430777 := bstep (se 2 (by rfl) ⟨2786541, by rfl⟩ : syracuseStep 7430777 = 5573083) B5573083
theorem B3302063 : Blo 1466553 3302063 := bstep (se 1 (by rfl) ⟨2476547, by rfl⟩ : syracuseStep 3302063 = 4953095) B4953095
theorem B1467103 : Blo 1466553 1467103 := bstep (se 1 (by rfl) ⟨1100327, by rfl⟩ : syracuseStep 1467103 = 2200655) B2200655
theorem B3302135 : Blo 1466553 3302135 := bstep (se 1 (by rfl) ⟨2476601, by rfl⟩ : syracuseStep 3302135 = 4953203) B4953203
theorem B1467183 : Blo 1466553 1467183 := bstep (se 1 (by rfl) ⟨1100387, by rfl⟩ : syracuseStep 1467183 = 2200775) B2200775
theorem B12534587 : Blo 1466553 12534587 := bstep (se 1 (by rfl) ⟨9400940, by rfl⟩ : syracuseStep 12534587 = 18801881) B18801881
theorem B1467291 : Blo 1466553 1467291 := bstep (se 1 (by rfl) ⟨1100468, by rfl⟩ : syracuseStep 1467291 = 2200937) B2200937
theorem B3302315 : Blo 1466553 3302315 := bstep (se 1 (by rfl) ⟨2476736, by rfl⟩ : syracuseStep 3302315 = 4953473) B4953473
theorem B31720385 : Blo 1466553 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B1467343 : Blo 1466553 1467343 := bstep (se 1 (by rfl) ⟨1100507, by rfl⟩ : syracuseStep 1467343 = 2201015) B2201015
theorem B3965915 : Blo 1466553 3965915 := bstep (se 1 (by rfl) ⟨2974436, by rfl⟩ : syracuseStep 3965915 = 5948873) B5948873
theorem B1467367 : Blo 1466553 1467367 := bstep (se 1 (by rfl) ⟨1100525, by rfl⟩ : syracuseStep 1467367 = 2201051) B2201051
theorem B28607555 : Blo 1466553 28607555 := bstep (se 1 (by rfl) ⟨21455666, by rfl⟩ : syracuseStep 28607555 = 42911333) B42911333
theorem B1467679 : Blo 1466553 1467679 := bstep (se 1 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 1467679 = 2201519) B2201519
theorem B1467739 : Blo 1466553 1467739 := bstep (se 1 (by rfl) ⟨1100804, by rfl⟩ : syracuseStep 1467739 = 2201609) B2201609
theorem B3712351 : Blo 1466553 3712351 := bstep (se 1 (by rfl) ⟨2784263, by rfl⟩ : syracuseStep 3712351 = 5568527) B5568527
theorem B1467759 : Blo 1466553 1467759 := bstep (se 1 (by rfl) ⟨1100819, by rfl⟩ : syracuseStep 1467759 = 2201639) B2201639
theorem B3966347 : Blo 1466553 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B1467815 : Blo 1466553 1467815 := bstep (se 1 (by rfl) ⟨1100861, by rfl⟩ : syracuseStep 1467815 = 2201723) B2201723
theorem B3573191 : Blo 1466553 3573191 := bstep (se 1 (by rfl) ⟨2679893, by rfl⟩ : syracuseStep 3573191 = 5359787) B5359787
theorem B3302855 : Blo 1466553 3302855 := bstep (se 1 (by rfl) ⟨2477141, by rfl⟩ : syracuseStep 3302855 = 4954283) B4954283
theorem B1467899 : Blo 1466553 1467899 := bstep (se 1 (by rfl) ⟨1100924, by rfl⟩ : syracuseStep 1467899 = 2201849) B2201849
theorem B1467967 : Blo 1466553 1467967 := bstep (se 1 (by rfl) ⟨1100975, by rfl⟩ : syracuseStep 1467967 = 2201951) B2201951
theorem B1467975 : Blo 1466553 1467975 := bstep (se 1 (by rfl) ⟨1100981, by rfl⟩ : syracuseStep 1467975 = 2201963) B2201963
theorem B2786899 : Blo 1466553 2786899 := bstep (se 1 (by rfl) ⟨2090174, by rfl⟩ : syracuseStep 2786899 = 4180349) B4180349
theorem B3524257 : Blo 1466553 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B1468127 : Blo 1466553 1468127 := bstep (se 1 (by rfl) ⟨1101095, by rfl⟩ : syracuseStep 1468127 = 2202191) B2202191
theorem B1763051 : Blo 1466553 1763051 := bstep (se 1 (by rfl) ⟨1322288, by rfl⟩ : syracuseStep 1763051 = 2644577) B2644577
theorem B14100257 : Blo 1466553 14100257 := bstep (se 2 (by rfl) ⟨5287596, by rfl⟩ : syracuseStep 14100257 = 10575193) B10575193
theorem B3303215 : Blo 1466553 3303215 := bstep (se 1 (by rfl) ⟨2477411, by rfl⟩ : syracuseStep 3303215 = 4954823) B4954823
theorem B2787119 : Blo 1466553 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B1468207 : Blo 1466553 1468207 := bstep (se 1 (by rfl) ⟨1101155, by rfl⟩ : syracuseStep 1468207 = 2202311) B2202311
theorem B32188265 : Blo 1466553 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1468315 : Blo 1466553 1468315 := bstep (se 1 (by rfl) ⟨1101236, by rfl⟩ : syracuseStep 1468315 = 2202473) B2202473
theorem B87009227 : Blo 1466553 87009227 := bstep (se 1 (by rfl) ⟨65256920, by rfl⟩ : syracuseStep 87009227 = 130513841) B130513841
theorem B1468367 : Blo 1466553 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B1468391 : Blo 1466553 1468391 := bstep (se 1 (by rfl) ⟨1101293, by rfl⟩ : syracuseStep 1468391 = 2202587) B2202587
theorem B2476379 : Blo 1466553 2476379 := bstep (se 1 (by rfl) ⟨1857284, by rfl⟩ : syracuseStep 2476379 = 3714569) B3714569
theorem B2476399 : Blo 1466553 2476399 := bstep (se 1 (by rfl) ⟨1857299, by rfl⟩ : syracuseStep 2476399 = 3714599) B3714599
theorem B7432559 : Blo 1466553 7432559 := bstep (se 1 (by rfl) ⟨5574419, by rfl⟩ : syracuseStep 7432559 = 11148839) B11148839
theorem B3303791 : Blo 1466553 3303791 := bstep (se 1 (by rfl) ⟨2477843, by rfl⟩ : syracuseStep 3303791 = 4955687) B4955687
theorem B6269309 : Blo 1466553 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B7055741 : Blo 1466553 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B17844623 : Blo 1466553 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B63482291 : Blo 1466553 63482291 := bstep (se 1 (by rfl) ⟨47611718, by rfl⟩ : syracuseStep 63482291 = 95223437) B95223437
theorem B3303863 : Blo 1466553 3303863 := bstep (se 1 (by rfl) ⟨2477897, by rfl⟩ : syracuseStep 3303863 = 4955795) B4955795
theorem B2476615 : Blo 1466553 2476615 := bstep (se 1 (by rfl) ⟨1857461, by rfl⟩ : syracuseStep 2476615 = 3714923) B3714923
theorem B3304007 : Blo 1466553 3304007 := bstep (se 1 (by rfl) ⟨2478005, by rfl⟩ : syracuseStep 3304007 = 4956011) B4956011
theorem B3304043 : Blo 1466553 3304043 := bstep (se 1 (by rfl) ⟨2478032, by rfl⟩ : syracuseStep 3304043 = 4956065) B4956065
theorem B22031057 : Blo 1466553 22031057 := bstep (se 2 (by rfl) ⟨8261646, by rfl⟩ : syracuseStep 22031057 = 16523293) B16523293
theorem B3713759 : Blo 1466553 3713759 := bstep (se 1 (by rfl) ⟨2785319, by rfl⟩ : syracuseStep 3713759 = 5570639) B5570639
theorem B5286647 : Blo 1466553 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B10718077 : Blo 1466553 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B2477047 : Blo 1466553 2477047 := bstep (se 1 (by rfl) ⟨1857785, by rfl⟩ : syracuseStep 2477047 = 3715571) B3715571
theorem B26766413 : Blo 1466553 26766413 := bstep (se 3 (by rfl) ⟨5018702, by rfl⟩ : syracuseStep 26766413 = 10037405) B10037405
theorem B15862961 : Blo 1466553 15862961 := bstep (se 2 (by rfl) ⟨5948610, by rfl⟩ : syracuseStep 15862961 = 11897221) B11897221
theorem B4951259 : Blo 1466553 4951259 := bstep (se 1 (by rfl) ⟨3713444, by rfl⟩ : syracuseStep 4951259 = 7426889) B7426889
theorem B3132665 : Blo 1466553 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B3968249 : Blo 1466553 3968249 := bstep (se 2 (by rfl) ⟨1488093, by rfl⟩ : syracuseStep 3968249 = 2976187) B2976187
theorem B2477351 : Blo 1466553 2477351 := bstep (se 1 (by rfl) ⟨1858013, by rfl⟩ : syracuseStep 2477351 = 3716027) B3716027
theorem B3526025 : Blo 1466553 3526025 := bstep (se 2 (by rfl) ⟨1322259, by rfl⟩ : syracuseStep 3526025 = 2644519) B2644519
theorem B1650271 : Blo 1466553 1650271 := bstep (se 1 (by rfl) ⟨1237703, by rfl⟩ : syracuseStep 1650271 = 2475407) B2475407
theorem B2477803 : Blo 1466553 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B4181807 : Blo 1466553 4181807 := bstep (se 1 (by rfl) ⟨3136355, by rfl⟩ : syracuseStep 4181807 = 6272711) B6272711
theorem B9400121 : Blo 1466553 9400121 := bstep (se 2 (by rfl) ⟨3525045, by rfl⟩ : syracuseStep 9400121 = 7050091) B7050091
theorem B12529565 : Blo 1466553 12529565 := bstep (se 3 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 12529565 = 4698587) B4698587
theorem B18796445 : Blo 1466553 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B15052825 : Blo 1466553 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B4952123 : Blo 1466553 4952123 := bstep (se 1 (by rfl) ⟨3714092, by rfl⟩ : syracuseStep 4952123 = 7428185) B7428185
theorem B4952393 : Blo 1466553 4952393 := bstep (se 2 (by rfl) ⟨1857147, by rfl⟩ : syracuseStep 4952393 = 3714295) B3714295
theorem B2199899 : Blo 1466553 2199899 := bstep (se 1 (by rfl) ⟨1649924, by rfl⟩ : syracuseStep 2199899 = 3299849) B3299849
theorem B31732073 : Blo 1466553 31732073 := bstep (se 2 (by rfl) ⟨11899527, by rfl⟩ : syracuseStep 31732073 = 23799055) B23799055
theorem B2200127 : Blo 1466553 2200127 := bstep (se 1 (by rfl) ⟨1650095, by rfl⟩ : syracuseStep 2200127 = 3300191) B3300191
theorem B2200247 : Blo 1466553 2200247 := bstep (se 1 (by rfl) ⟨1650185, by rfl⟩ : syracuseStep 2200247 = 3300371) B3300371
theorem B2716343 : Blo 1466553 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B1651423 : Blo 1466553 1651423 := bstep (se 1 (by rfl) ⟨1238567, by rfl⟩ : syracuseStep 1651423 = 2477135) B2477135
theorem B8926031 : Blo 1466553 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B2200475 : Blo 1466553 2200475 := bstep (se 1 (by rfl) ⟨1650356, by rfl⟩ : syracuseStep 2200475 = 3300713) B3300713
theorem B3716219 : Blo 1466553 3716219 := bstep (se 1 (by rfl) ⟨2787164, by rfl⟩ : syracuseStep 3716219 = 5574329) B5574329
theorem B3716239 : Blo 1466553 3716239 := bstep (se 1 (by rfl) ⟨2787179, by rfl⟩ : syracuseStep 3716239 = 5574359) B5574359
theorem B1651999 : Blo 1466553 1651999 := bstep (se 1 (by rfl) ⟨1238999, by rfl⟩ : syracuseStep 1651999 = 2477999) B2477999
theorem B2200871 : Blo 1466553 2200871 := bstep (se 1 (by rfl) ⟨1650653, by rfl⟩ : syracuseStep 2200871 = 3301307) B3301307
theorem B15267167 : Blo 1466553 15267167 := bstep (se 1 (by rfl) ⟨11450375, by rfl⟩ : syracuseStep 15267167 = 22900751) B22900751
theorem B2200955 : Blo 1466553 2200955 := bstep (se 1 (by rfl) ⟨1650716, by rfl⟩ : syracuseStep 2200955 = 3301433) B3301433
theorem B2643337 : Blo 1466553 2643337 := bstep (se 2 (by rfl) ⟨991251, by rfl⟩ : syracuseStep 2643337 = 1982503) B1982503
theorem B13391243 : Blo 1466553 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B3716513 : Blo 1466553 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B1856935 : Blo 1466553 1856935 := bstep (se 1 (by rfl) ⟨1392701, by rfl⟩ : syracuseStep 1856935 = 2785403) B2785403
theorem B23811509 : Blo 1466553 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B10728941 : Blo 1466553 10728941 := bstep (se 3 (by rfl) ⟨2011676, by rfl⟩ : syracuseStep 10728941 = 4023353) B4023353
theorem B2201081 : Blo 1466553 2201081 := bstep (se 2 (by rfl) ⟨825405, by rfl⟩ : syracuseStep 2201081 = 1650811) B1650811
theorem B2201183 : Blo 1466553 2201183 := bstep (se 1 (by rfl) ⟨1650887, by rfl⟩ : syracuseStep 2201183 = 3301775) B3301775
theorem B3528353 : Blo 1466553 3528353 := bstep (se 2 (by rfl) ⟨1323132, by rfl⟩ : syracuseStep 3528353 = 2646265) B2646265
theorem B1857259 : Blo 1466553 1857259 := bstep (se 1 (by rfl) ⟨1392944, by rfl⟩ : syracuseStep 1857259 = 2785889) B2785889
theorem B15480557 : Blo 1466553 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B2201399 : Blo 1466553 2201399 := bstep (se 1 (by rfl) ⟨1651049, by rfl⟩ : syracuseStep 2201399 = 3302099) B3302099
theorem B3135287 : Blo 1466553 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B7428023 : Blo 1466553 7428023 := bstep (se 1 (by rfl) ⟨5571017, by rfl⟩ : syracuseStep 7428023 = 11142035) B11142035
theorem B1857487 : Blo 1466553 1857487 := bstep (se 1 (by rfl) ⟨1393115, by rfl⟩ : syracuseStep 1857487 = 2786231) B2786231
theorem B11892815 : Blo 1466553 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B3438697 : Blo 1466553 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B2201705 : Blo 1466553 2201705 := bstep (se 2 (by rfl) ⟨825639, by rfl⟩ : syracuseStep 2201705 = 1651279) B1651279
theorem B1857755 : Blo 1466553 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B3135851 : Blo 1466553 3135851 := bstep (se 1 (by rfl) ⟨2351888, by rfl⟩ : syracuseStep 3135851 = 4703777) B4703777
theorem B2202023 : Blo 1466553 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B3299759 : Blo 1466553 3299759 := bstep (se 1 (by rfl) ⟨2474819, by rfl⟩ : syracuseStep 3299759 = 4949639) B4949639
theorem B3299795 : Blo 1466553 3299795 := bstep (se 1 (by rfl) ⟨2474846, by rfl⟩ : syracuseStep 3299795 = 4949693) B4949693
theorem B2202107 : Blo 1466553 2202107 := bstep (se 1 (by rfl) ⟨1651580, by rfl⟩ : syracuseStep 2202107 = 3303161) B3303161
theorem B3299903 : Blo 1466553 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B7428671 : Blo 1466553 7428671 := bstep (se 1 (by rfl) ⟨5571503, by rfl⟩ : syracuseStep 7428671 = 11143007) B11143007
theorem B2202233 : Blo 1466553 2202233 := bstep (se 2 (by rfl) ⟨825837, by rfl⟩ : syracuseStep 2202233 = 1651675) B1651675
theorem B3300011 : Blo 1466553 3300011 := bstep (se 1 (by rfl) ⟨2475008, by rfl⟩ : syracuseStep 3300011 = 4950017) B4950017
theorem B2202287 : Blo 1466553 2202287 := bstep (se 1 (by rfl) ⟨1651715, by rfl⟩ : syracuseStep 2202287 = 3303431) B3303431
theorem B1858231 : Blo 1466553 1858231 := bstep (se 1 (by rfl) ⟨1393673, by rfl⟩ : syracuseStep 1858231 = 2787347) B2787347
theorem B2202335 : Blo 1466553 2202335 := bstep (se 1 (by rfl) ⟨1651751, by rfl⟩ : syracuseStep 2202335 = 3303503) B3303503
theorem B6265619 : Blo 1466553 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B7928695 : Blo 1466553 7928695 := bstep (se 1 (by rfl) ⟨5946521, by rfl⟩ : syracuseStep 7928695 = 11893043) B11893043
theorem B1858459 : Blo 1466553 1858459 := bstep (se 1 (by rfl) ⟨1393844, by rfl⟩ : syracuseStep 1858459 = 2787689) B2787689
theorem B15063995 : Blo 1466553 15063995 := bstep (se 1 (by rfl) ⟨11297996, by rfl⟩ : syracuseStep 15063995 = 22595993) B22595993
theorem B2202599 : Blo 1466553 2202599 := bstep (se 1 (by rfl) ⟨1651949, by rfl⟩ : syracuseStep 2202599 = 3303899) B3303899
theorem B25418771 : Blo 1466553 25418771 := bstep (se 1 (by rfl) ⟨19064078, by rfl⟩ : syracuseStep 25418771 = 38128157) B38128157
theorem B3300551 : Blo 1466553 3300551 := bstep (se 1 (by rfl) ⟨2475413, by rfl⟩ : syracuseStep 3300551 = 4950827) B4950827
theorem B3013985 : Blo 1466553 3013985 := bstep (se 2 (by rfl) ⟨1130244, by rfl⟩ : syracuseStep 3013985 = 2260489) B2260489
theorem B3300731 : Blo 1466553 3300731 := bstep (se 1 (by rfl) ⟨2475548, by rfl⟩ : syracuseStep 3300731 = 4951097) B4951097
theorem B4955579 : Blo 1466553 4955579 := bstep (se 1 (by rfl) ⟨3716684, by rfl⟩ : syracuseStep 4955579 = 7433369) B7433369
theorem B3300857 : Blo 1466553 3300857 := bstep (se 2 (by rfl) ⟨1237821, by rfl⟩ : syracuseStep 3300857 = 2475643) B2475643
theorem B22887947 : Blo 1466553 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B16727633 : Blo 1466553 16727633 := bstep (se 2 (by rfl) ⟨6272862, by rfl⟩ : syracuseStep 16727633 = 12545725) B12545725
theorem B3300947 : Blo 1466553 3300947 := bstep (se 1 (by rfl) ⟨2475710, by rfl⟩ : syracuseStep 3300947 = 4951421) B4951421
theorem B31743575 : Blo 1466553 31743575 := bstep (se 1 (by rfl) ⟨23807681, by rfl⟩ : syracuseStep 31743575 = 47615363) B47615363
theorem B8363681 : Blo 1466553 8363681 := bstep (se 2 (by rfl) ⟨3136380, by rfl⟩ : syracuseStep 8363681 = 6272761) B6272761
theorem B2784955 : Blo 1466553 2784955 := bstep (se 1 (by rfl) ⟨2088716, by rfl⟩ : syracuseStep 2784955 = 4177433) B4177433
theorem B3301127 : Blo 1466553 3301127 := bstep (se 1 (by rfl) ⟨2475845, by rfl⟩ : syracuseStep 3301127 = 4951691) B4951691
theorem B6692615 : Blo 1466553 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B4702009 : Blo 1466553 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B9404221 : Blo 1466553 9404221 := bstep (se 3 (by rfl) ⟨1763291, by rfl⟩ : syracuseStep 9404221 = 3526583) B3526583
theorem B20070433 : Blo 1466553 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B3301415 : Blo 1466553 3301415 := bstep (se 1 (by rfl) ⟨2476061, by rfl⟩ : syracuseStep 3301415 = 4952123) B4952123
theorem B3301595 : Blo 1466553 3301595 := bstep (se 1 (by rfl) ⟨2476196, by rfl⟩ : syracuseStep 3301595 = 4952393) B4952393
theorem B1466599 : Blo 1466553 1466599 := bstep (se 1 (by rfl) ⟨1099949, by rfl⟩ : syracuseStep 1466599 = 2199899) B2199899
theorem B4702495 : Blo 1466553 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B1466751 : Blo 1466553 1466751 := bstep (se 1 (by rfl) ⟨1100063, by rfl⟩ : syracuseStep 1466751 = 2200127) B2200127
theorem B1466831 : Blo 1466553 1466831 := bstep (se 1 (by rfl) ⟨1100123, by rfl⟩ : syracuseStep 1466831 = 2200247) B2200247
theorem B1810895 : Blo 1466553 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B3301865 : Blo 1466553 3301865 := bstep (se 2 (by rfl) ⟨1238199, by rfl⟩ : syracuseStep 3301865 = 2476399) B2476399
theorem B8356391 : Blo 1466553 8356391 := bstep (se 1 (by rfl) ⟨6267293, by rfl⟩ : syracuseStep 8356391 = 12534587) B12534587
theorem B1466983 : Blo 1466553 1466983 := bstep (se 1 (by rfl) ⟨1100237, by rfl⟩ : syracuseStep 1466983 = 2200475) B2200475
theorem B19071703 : Blo 1466553 19071703 := bstep (se 1 (by rfl) ⟨14303777, by rfl⟩ : syracuseStep 19071703 = 28607555) B28607555
theorem B3302153 : Blo 1466553 3302153 := bstep (se 2 (by rfl) ⟨1238307, by rfl⟩ : syracuseStep 3302153 = 2476615) B2476615
theorem B1467247 : Blo 1466553 1467247 := bstep (se 1 (by rfl) ⟨1100435, by rfl⟩ : syracuseStep 1467247 = 2200871) B2200871
theorem B1467303 : Blo 1466553 1467303 := bstep (se 1 (by rfl) ⟨1100477, by rfl⟩ : syracuseStep 1467303 = 2200955) B2200955
theorem B1467387 : Blo 1466553 1467387 := bstep (se 1 (by rfl) ⟨1100540, by rfl⟩ : syracuseStep 1467387 = 2201081) B2201081
theorem B10576925 : Blo 1466553 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B1467455 : Blo 1466553 1467455 := bstep (se 1 (by rfl) ⟨1100591, by rfl⟩ : syracuseStep 1467455 = 2201183) B2201183
theorem B2352235 : Blo 1466553 2352235 := bstep (se 1 (by rfl) ⟨1764176, by rfl⟩ : syracuseStep 2352235 = 3528353) B3528353
theorem B63497357 : Blo 1466553 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B9528509 : Blo 1466553 9528509 := bstep (se 3 (by rfl) ⟨1786595, by rfl⟩ : syracuseStep 9528509 = 3573191) B3573191
theorem B1467599 : Blo 1466553 1467599 := bstep (se 1 (by rfl) ⟨1100699, by rfl⟩ : syracuseStep 1467599 = 2201399) B2201399
theorem B3302729 : Blo 1466553 3302729 := bstep (se 2 (by rfl) ⟨1238523, by rfl⟩ : syracuseStep 3302729 = 2477047) B2477047
theorem B1467803 : Blo 1466553 1467803 := bstep (se 1 (by rfl) ⟨1100852, by rfl⟩ : syracuseStep 1467803 = 2201705) B2201705
theorem B2090567 : Blo 1466553 2090567 := bstep (se 1 (by rfl) ⟨1567925, by rfl⟩ : syracuseStep 2090567 = 3135851) B3135851
theorem B4179539 : Blo 1466553 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B4703827 : Blo 1466553 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B11896415 : Blo 1466553 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B1468015 : Blo 1466553 1468015 := bstep (se 1 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 1468015 = 2202023) B2202023
theorem B42321527 : Blo 1466553 42321527 := bstep (se 1 (by rfl) ⟨31741145, by rfl⟩ : syracuseStep 42321527 = 63482291) B63482291
theorem B1468071 : Blo 1466553 1468071 := bstep (se 1 (by rfl) ⟨1101053, by rfl⟩ : syracuseStep 1468071 = 2202107) B2202107
theorem B1468155 : Blo 1466553 1468155 := bstep (se 1 (by rfl) ⟨1101116, by rfl⟩ : syracuseStep 1468155 = 2202233) B2202233
theorem B1468191 : Blo 1466553 1468191 := bstep (se 1 (by rfl) ⟨1101143, by rfl⟩ : syracuseStep 1468191 = 2202287) B2202287
theorem B4949801 : Blo 1466553 4949801 := bstep (se 2 (by rfl) ⟨1856175, by rfl⟩ : syracuseStep 4949801 = 3712351) B3712351
theorem B2475839 : Blo 1466553 2475839 := bstep (se 1 (by rfl) ⟨1856879, by rfl⟩ : syracuseStep 2475839 = 3713759) B3713759
theorem B1468223 : Blo 1466553 1468223 := bstep (se 1 (by rfl) ⟨1101167, by rfl⟩ : syracuseStep 1468223 = 2202335) B2202335
theorem B3524431 : Blo 1466553 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B2475913 : Blo 1466553 2475913 := bstep (se 2 (by rfl) ⟨928467, by rfl⟩ : syracuseStep 2475913 = 1856935) B1856935
theorem B1468399 : Blo 1466553 1468399 := bstep (se 1 (by rfl) ⟨1101299, by rfl⟩ : syracuseStep 1468399 = 2202599) B2202599
theorem B17844275 : Blo 1466553 17844275 := bstep (se 1 (by rfl) ⟨13383206, by rfl⟩ : syracuseStep 17844275 = 26766413) B26766413
theorem B2009323 : Blo 1466553 2009323 := bstep (se 1 (by rfl) ⟨1506992, by rfl⟩ : syracuseStep 2009323 = 3013985) B3013985
theorem B3713273 : Blo 1466553 3713273 := bstep (se 2 (by rfl) ⟨1392477, by rfl⟩ : syracuseStep 3713273 = 2784955) B2784955
theorem B3303719 : Blo 1466553 3303719 := bstep (se 1 (by rfl) ⟨2477789, by rfl⟩ : syracuseStep 3303719 = 4955579) B4955579
theorem B2476345 : Blo 1466553 2476345 := bstep (se 2 (by rfl) ⟨928629, by rfl⟩ : syracuseStep 2476345 = 1857259) B1857259
theorem B3303737 : Blo 1466553 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B11151755 : Blo 1466553 11151755 := bstep (se 1 (by rfl) ⟨8363816, by rfl⟩ : syracuseStep 11151755 = 16727633) B16727633
theorem B21162383 : Blo 1466553 21162383 := bstep (se 1 (by rfl) ⟨15871787, by rfl⟩ : syracuseStep 21162383 = 31743575) B31743575
theorem B6269345 : Blo 1466553 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B2787871 : Blo 1466553 2787871 := bstep (se 1 (by rfl) ⟨2090903, by rfl⟩ : syracuseStep 2787871 = 4181807) B4181807
theorem B2476649 : Blo 1466553 2476649 := bstep (se 2 (by rfl) ⟨928743, by rfl⟩ : syracuseStep 2476649 = 1857487) B1857487
theorem B21154715 : Blo 1466553 21154715 := bstep (se 1 (by rfl) ⟨15866036, by rfl⟩ : syracuseStep 21154715 = 31732073) B31732073
theorem B37620773 : Blo 1466553 37620773 := bstep (se 4 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 37620773 = 7053895) B7053895
theorem B5950687 : Blo 1466553 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B21146923 : Blo 1466553 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B2477479 : Blo 1466553 2477479 := bstep (se 1 (by rfl) ⟨1858109, by rfl⟩ : syracuseStep 2477479 = 3716219) B3716219
theorem B10178111 : Blo 1466553 10178111 := bstep (se 1 (by rfl) ⟨7633583, by rfl⟩ : syracuseStep 10178111 = 15267167) B15267167
theorem B2477641 : Blo 1466553 2477641 := bstep (se 2 (by rfl) ⟨929115, by rfl⟩ : syracuseStep 2477641 = 1858231) B1858231
theorem B2477675 : Blo 1466553 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B42315533 : Blo 1466553 42315533 := bstep (se 3 (by rfl) ⟨7934162, by rfl⟩ : syracuseStep 42315533 = 15868325) B15868325
theorem B10571593 : Blo 1466553 10571593 := bstep (se 2 (by rfl) ⟨3964347, by rfl⟩ : syracuseStep 10571593 = 7928695) B7928695
theorem B14290769 : Blo 1466553 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B9400171 : Blo 1466553 9400171 := bstep (se 1 (by rfl) ⟨7050128, by rfl⟩ : syracuseStep 9400171 = 14100257) B14100257
theorem B2477945 : Blo 1466553 2477945 := bstep (se 2 (by rfl) ⟨929229, by rfl⟩ : syracuseStep 2477945 = 1858459) B1858459
theorem B21458843 : Blo 1466553 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B4952015 : Blo 1466553 4952015 := bstep (se 1 (by rfl) ⟨3714011, by rfl⟩ : syracuseStep 4952015 = 7428023) B7428023
theorem B1650919 : Blo 1466553 1650919 := bstep (se 1 (by rfl) ⟨1238189, by rfl⟩ : syracuseStep 1650919 = 2476379) B2476379
theorem B2199839 : Blo 1466553 2199839 := bstep (se 1 (by rfl) ⟨1649879, by rfl⟩ : syracuseStep 2199839 = 3299759) B3299759
theorem B2199863 : Blo 1466553 2199863 := bstep (se 1 (by rfl) ⟨1649897, by rfl⟩ : syracuseStep 2199863 = 3299795) B3299795
theorem B2199935 : Blo 1466553 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B4952447 : Blo 1466553 4952447 := bstep (se 1 (by rfl) ⟨3714335, by rfl⟩ : syracuseStep 4952447 = 7428671) B7428671
theorem B2200007 : Blo 1466553 2200007 := bstep (se 1 (by rfl) ⟨1650005, by rfl⟩ : syracuseStep 2200007 = 3300011) B3300011
theorem B16945847 : Blo 1466553 16945847 := bstep (se 1 (by rfl) ⟨12709385, by rfl⟩ : syracuseStep 16945847 = 25418771) B25418771
theorem B3715865 : Blo 1466553 3715865 := bstep (se 2 (by rfl) ⟨1393449, by rfl⟩ : syracuseStep 3715865 = 2786899) B2786899
theorem B2200361 : Blo 1466553 2200361 := bstep (se 2 (by rfl) ⟨825135, by rfl⟩ : syracuseStep 2200361 = 1650271) B1650271
theorem B2200367 : Blo 1466553 2200367 := bstep (se 1 (by rfl) ⟨1650275, by rfl⟩ : syracuseStep 2200367 = 3300551) B3300551
theorem B8360765 : Blo 1466553 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B1651567 : Blo 1466553 1651567 := bstep (se 1 (by rfl) ⟨1238675, by rfl⟩ : syracuseStep 1651567 = 2477351) B2477351
theorem B4699009 : Blo 1466553 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B2200487 : Blo 1466553 2200487 := bstep (se 1 (by rfl) ⟨1650365, by rfl⟩ : syracuseStep 2200487 = 3300731) B3300731
theorem B2200571 : Blo 1466553 2200571 := bstep (se 1 (by rfl) ⟨1650428, by rfl⟩ : syracuseStep 2200571 = 3300857) B3300857
theorem B15258631 : Blo 1466553 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B2200631 : Blo 1466553 2200631 := bstep (se 1 (by rfl) ⟨1650473, by rfl⟩ : syracuseStep 2200631 = 3300947) B3300947
theorem B12538961 : Blo 1466553 12538961 := bstep (se 2 (by rfl) ⟨4702110, by rfl⟩ : syracuseStep 12538961 = 9404221) B9404221
theorem B5575787 : Blo 1466553 5575787 := bstep (se 1 (by rfl) ⟨4181840, by rfl⟩ : syracuseStep 5575787 = 8363681) B8363681
theorem B18805877 : Blo 1466553 18805877 := bstep (se 5 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 18805877 = 1763051) B1763051
theorem B2200751 : Blo 1466553 2200751 := bstep (se 1 (by rfl) ⟨1650563, by rfl⟩ : syracuseStep 2200751 = 3301127) B3301127
theorem B4461743 : Blo 1466553 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B8353043 : Blo 1466553 8353043 := bstep (se 1 (by rfl) ⟨6264782, by rfl⟩ : syracuseStep 8353043 = 12529565) B12529565
theorem B12530963 : Blo 1466553 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B4584929 : Blo 1466553 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B2201159 : Blo 1466553 2201159 := bstep (se 1 (by rfl) ⟨1650869, by rfl⟩ : syracuseStep 2201159 = 3301739) B3301739
theorem B2201255 : Blo 1466553 2201255 := bstep (se 1 (by rfl) ⟨1650941, by rfl⟩ : syracuseStep 2201255 = 3301883) B3301883
theorem B2201339 : Blo 1466553 2201339 := bstep (se 1 (by rfl) ⟨1651004, by rfl⟩ : syracuseStep 2201339 = 3302009) B3302009
theorem B4953851 : Blo 1466553 4953851 := bstep (se 1 (by rfl) ⟨3715388, by rfl⟩ : syracuseStep 4953851 = 7430777) B7430777
theorem B2201375 : Blo 1466553 2201375 := bstep (se 1 (by rfl) ⟨1651031, by rfl⟩ : syracuseStep 2201375 = 3302063) B3302063
theorem B2201423 : Blo 1466553 2201423 := bstep (se 1 (by rfl) ⟨1651067, by rfl⟩ : syracuseStep 2201423 = 3302135) B3302135
theorem B4954013 : Blo 1466553 4954013 := bstep (se 3 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 4954013 = 1857755) B1857755
theorem B2201543 : Blo 1466553 2201543 := bstep (se 1 (by rfl) ⟨1651157, by rfl⟩ : syracuseStep 2201543 = 3302315) B3302315
theorem B2643943 : Blo 1466553 2643943 := bstep (se 1 (by rfl) ⟨1982957, by rfl⟩ : syracuseStep 2643943 = 3965915) B3965915
theorem B10581997 : Blo 1466553 10581997 := bstep (se 3 (by rfl) ⟨1984124, by rfl⟩ : syracuseStep 10581997 = 3968249) B3968249
theorem B8927495 : Blo 1466553 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B2201897 : Blo 1466553 2201897 := bstep (se 2 (by rfl) ⟨825711, by rfl⟩ : syracuseStep 2201897 = 1651423) B1651423
theorem B2201903 : Blo 1466553 2201903 := bstep (se 1 (by rfl) ⟨1651427, by rfl⟩ : syracuseStep 2201903 = 3302855) B3302855
theorem B9402733 : Blo 1466553 9402733 := bstep (se 3 (by rfl) ⟨1763012, by rfl⟩ : syracuseStep 9402733 = 3526025) B3526025
theorem B10320371 : Blo 1466553 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B2202143 : Blo 1466553 2202143 := bstep (se 1 (by rfl) ⟨1651607, by rfl⟩ : syracuseStep 2202143 = 3303215) B3303215
theorem B1858079 : Blo 1466553 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B58006151 : Blo 1466553 58006151 := bstep (se 1 (by rfl) ⟨43504613, by rfl⟩ : syracuseStep 58006151 = 87009227) B87009227
theorem B7928543 : Blo 1466553 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B4954985 : Blo 1466553 4954985 := bstep (se 2 (by rfl) ⟨1858119, by rfl⟩ : syracuseStep 4954985 = 3716239) B3716239
theorem B4955039 : Blo 1466553 4955039 := bstep (se 1 (by rfl) ⟨3716279, by rfl⟩ : syracuseStep 4955039 = 7432559) B7432559
theorem B2202527 : Blo 1466553 2202527 := bstep (se 1 (by rfl) ⟨1651895, by rfl⟩ : syracuseStep 2202527 = 3303791) B3303791
theorem B2202575 : Blo 1466553 2202575 := bstep (se 1 (by rfl) ⟨1651931, by rfl⟩ : syracuseStep 2202575 = 3303863) B3303863
theorem B2202665 : Blo 1466553 2202665 := bstep (se 2 (by rfl) ⟨825999, by rfl⟩ : syracuseStep 2202665 = 1651999) B1651999
theorem B2202671 : Blo 1466553 2202671 := bstep (se 1 (by rfl) ⟨1652003, by rfl⟩ : syracuseStep 2202671 = 3304007) B3304007
theorem B2202695 : Blo 1466553 2202695 := bstep (se 1 (by rfl) ⟨1652021, by rfl⟩ : syracuseStep 2202695 = 3304043) B3304043
theorem B14687371 : Blo 1466553 14687371 := bstep (se 1 (by rfl) ⟨11015528, by rfl⟩ : syracuseStep 14687371 = 22031057) B22031057
theorem B4177079 : Blo 1466553 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B10042663 : Blo 1466553 10042663 := bstep (se 1 (by rfl) ⟨7531997, by rfl⟩ : syracuseStep 10042663 = 15063995) B15063995
theorem B14097797 : Blo 1466553 14097797 := bstep (se 4 (by rfl) ⟨1321668, by rfl⟩ : syracuseStep 14097797 = 2643337) B2643337
theorem B10575307 : Blo 1466553 10575307 := bstep (se 1 (by rfl) ⟨7931480, by rfl⟩ : syracuseStep 10575307 = 15862961) B15862961
theorem B3300839 : Blo 1466553 3300839 := bstep (se 1 (by rfl) ⟨2475629, by rfl⟩ : syracuseStep 3300839 = 4951259) B4951259
theorem B2088443 : Blo 1466553 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B114442037 : Blo 1466553 114442037 := bstep (se 5 (by rfl) ⟨5364470, by rfl⟩ : syracuseStep 114442037 = 10728941) B10728941
theorem B6266747 : Blo 1466553 6266747 := bstep (se 1 (by rfl) ⟨4700060, by rfl⟩ : syracuseStep 6266747 = 9400121) B9400121
theorem B1466559 : Blo 1466553 1466559 := bstep (se 1 (by rfl) ⟨1099919, by rfl⟩ : syracuseStep 1466559 = 2199839) B2199839
theorem B1466575 : Blo 1466553 1466575 := bstep (se 1 (by rfl) ⟨1099931, by rfl⟩ : syracuseStep 1466575 = 2199863) B2199863
theorem B1466623 : Blo 1466553 1466623 := bstep (se 1 (by rfl) ⟨1099967, by rfl⟩ : syracuseStep 1466623 = 2199935) B2199935
theorem B3301631 : Blo 1466553 3301631 := bstep (se 1 (by rfl) ⟨2476223, by rfl⟩ : syracuseStep 3301631 = 4952447) B4952447
theorem B1466671 : Blo 1466553 1466671 := bstep (se 1 (by rfl) ⟨1100003, by rfl⟩ : syracuseStep 1466671 = 2200007) B2200007
theorem B2679097 : Blo 1466553 2679097 := bstep (se 2 (by rfl) ⟨1004661, by rfl⟩ : syracuseStep 2679097 = 2009323) B2009323
theorem B5570927 : Blo 1466553 5570927 := bstep (se 1 (by rfl) ⟨4178195, by rfl⟩ : syracuseStep 5570927 = 8356391) B8356391
theorem B3301793 : Blo 1466553 3301793 := bstep (se 2 (by rfl) ⟨1238172, by rfl⟩ : syracuseStep 3301793 = 2476345) B2476345
theorem B11297231 : Blo 1466553 11297231 := bstep (se 1 (by rfl) ⟨8472923, by rfl⟩ : syracuseStep 11297231 = 16945847) B16945847
theorem B1466907 : Blo 1466553 1466907 := bstep (se 1 (by rfl) ⟨1100180, by rfl⟩ : syracuseStep 1466907 = 2200361) B2200361
theorem B1466911 : Blo 1466553 1466911 := bstep (se 1 (by rfl) ⟨1100183, by rfl⟩ : syracuseStep 1466911 = 2200367) B2200367
theorem B1466991 : Blo 1466553 1466991 := bstep (se 1 (by rfl) ⟨1100243, by rfl⟩ : syracuseStep 1466991 = 2200487) B2200487
theorem B1467047 : Blo 1466553 1467047 := bstep (se 1 (by rfl) ⟨1100285, by rfl⟩ : syracuseStep 1467047 = 2200571) B2200571
theorem B1467087 : Blo 1466553 1467087 := bstep (se 1 (by rfl) ⟨1100315, by rfl⟩ : syracuseStep 1467087 = 2200631) B2200631
theorem B78332645 : Blo 1466553 78332645 := bstep (se 4 (by rfl) ⟨7343685, by rfl⟩ : syracuseStep 78332645 = 14687371) B14687371
theorem B1467167 : Blo 1466553 1467167 := bstep (se 1 (by rfl) ⟨1100375, by rfl⟩ : syracuseStep 1467167 = 2200751) B2200751
theorem B2974495 : Blo 1466553 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B1467439 : Blo 1466553 1467439 := bstep (se 1 (by rfl) ⟨1100579, by rfl⟩ : syracuseStep 1467439 = 2201159) B2201159
theorem B7930943 : Blo 1466553 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B28214351 : Blo 1466553 28214351 := bstep (se 1 (by rfl) ⟨21160763, by rfl⟩ : syracuseStep 28214351 = 42321527) B42321527
theorem B1467503 : Blo 1466553 1467503 := bstep (se 1 (by rfl) ⟨1100627, by rfl⟩ : syracuseStep 1467503 = 2201255) B2201255
theorem B1467559 : Blo 1466553 1467559 := bstep (se 1 (by rfl) ⟨1100669, by rfl⟩ : syracuseStep 1467559 = 2201339) B2201339
theorem B3302567 : Blo 1466553 3302567 := bstep (se 1 (by rfl) ⟨2476925, by rfl⟩ : syracuseStep 3302567 = 4953851) B4953851
theorem B1467583 : Blo 1466553 1467583 := bstep (se 1 (by rfl) ⟨1100687, by rfl⟩ : syracuseStep 1467583 = 2201375) B2201375
theorem B1467615 : Blo 1466553 1467615 := bstep (se 1 (by rfl) ⟨1100711, by rfl⟩ : syracuseStep 1467615 = 2201423) B2201423
theorem B3302675 : Blo 1466553 3302675 := bstep (se 1 (by rfl) ⟨2477006, by rfl⟩ : syracuseStep 3302675 = 4954013) B4954013
theorem B1467695 : Blo 1466553 1467695 := bstep (se 1 (by rfl) ⟨1100771, by rfl⟩ : syracuseStep 1467695 = 2201543) B2201543
theorem B11896183 : Blo 1466553 11896183 := bstep (se 1 (by rfl) ⟨8922137, by rfl⟩ : syracuseStep 11896183 = 17844275) B17844275
theorem B2475515 : Blo 1466553 2475515 := bstep (se 1 (by rfl) ⟨1856636, by rfl⟩ : syracuseStep 2475515 = 3713273) B3713273
theorem B1467931 : Blo 1466553 1467931 := bstep (se 1 (by rfl) ⟨1100948, by rfl⟩ : syracuseStep 1467931 = 2201897) B2201897
theorem B1467935 : Blo 1466553 1467935 := bstep (se 1 (by rfl) ⟨1100951, by rfl⟩ : syracuseStep 1467935 = 2201903) B2201903
theorem B14108255 : Blo 1466553 14108255 := bstep (se 1 (by rfl) ⟨10581191, by rfl⟩ : syracuseStep 14108255 = 21162383) B21162383
theorem B4179563 : Blo 1466553 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B1468095 : Blo 1466553 1468095 := bstep (se 1 (by rfl) ⟨1101071, by rfl⟩ : syracuseStep 1468095 = 2202143) B2202143
theorem B5285695 : Blo 1466553 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B3303305 : Blo 1466553 3303305 := bstep (se 2 (by rfl) ⟨1238739, by rfl⟩ : syracuseStep 3303305 = 2477479) B2477479
theorem B3303323 : Blo 1466553 3303323 := bstep (se 1 (by rfl) ⟨2477492, by rfl⟩ : syracuseStep 3303323 = 4954985) B4954985
theorem B14100409 : Blo 1466553 14100409 := bstep (se 2 (by rfl) ⟨5287653, by rfl⟩ : syracuseStep 14100409 = 10575307) B10575307
theorem B3303359 : Blo 1466553 3303359 := bstep (se 1 (by rfl) ⟨2477519, by rfl⟩ : syracuseStep 3303359 = 4955039) B4955039
theorem B1468351 : Blo 1466553 1468351 := bstep (se 1 (by rfl) ⟨1101263, by rfl⟩ : syracuseStep 1468351 = 2202527) B2202527
theorem B1468383 : Blo 1466553 1468383 := bstep (se 1 (by rfl) ⟨1101287, by rfl⟩ : syracuseStep 1468383 = 2202575) B2202575
theorem B1468443 : Blo 1466553 1468443 := bstep (se 1 (by rfl) ⟨1101332, by rfl⟩ : syracuseStep 1468443 = 2202665) B2202665
theorem B1468447 : Blo 1466553 1468447 := bstep (se 1 (by rfl) ⟨1101335, by rfl⟩ : syracuseStep 1468447 = 2202671) B2202671
theorem B1468463 : Blo 1466553 1468463 := bstep (se 1 (by rfl) ⟨1101347, by rfl⟩ : syracuseStep 1468463 = 2202695) B2202695
theorem B3303521 : Blo 1466553 3303521 := bstep (se 2 (by rfl) ⟨1238820, by rfl⟩ : syracuseStep 3303521 = 2477641) B2477641
theorem B9398531 : Blo 1466553 9398531 := bstep (se 1 (by rfl) ⟨7048898, by rfl⟩ : syracuseStep 9398531 = 14097797) B14097797
theorem B6785407 : Blo 1466553 6785407 := bstep (se 1 (by rfl) ⟨5089055, by rfl⟩ : syracuseStep 6785407 = 10178111) B10178111
theorem B76294691 : Blo 1466553 76294691 := bstep (se 1 (by rfl) ⟨57221018, by rfl⟩ : syracuseStep 76294691 = 114442037) B114442037
theorem B14305895 : Blo 1466553 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B3525257 : Blo 1466553 3525257 := bstep (se 2 (by rfl) ⟨1321971, by rfl⟩ : syracuseStep 3525257 = 2643943) B2643943
theorem B14109329 : Blo 1466553 14109329 := bstep (se 2 (by rfl) ⟨5290998, by rfl⟩ : syracuseStep 14109329 = 10581997) B10581997
theorem B6269993 : Blo 1466553 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B12536977 : Blo 1466553 12536977 := bstep (se 2 (by rfl) ⟨4701366, by rfl⟩ : syracuseStep 12536977 = 9402733) B9402733
theorem B2477243 : Blo 1466553 2477243 := bstep (se 1 (by rfl) ⟨1857932, by rfl⟩ : syracuseStep 2477243 = 3715865) B3715865
theorem B5573843 : Blo 1466553 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B8359307 : Blo 1466553 8359307 := bstep (se 1 (by rfl) ⟨6269480, by rfl⟩ : syracuseStep 8359307 = 12538961) B12538961
theorem B12537251 : Blo 1466553 12537251 := bstep (se 1 (by rfl) ⟨9402938, by rfl⟩ : syracuseStep 12537251 = 18805877) B18805877
theorem B42331571 : Blo 1466553 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B6352339 : Blo 1466553 6352339 := bstep (se 1 (by rfl) ⟨4764254, by rfl⟩ : syracuseStep 6352339 = 9528509) B9528509
theorem B101715749 : Blo 1466553 101715749 := bstep (se 4 (by rfl) ⟨9535851, by rfl⟩ : syracuseStep 101715749 = 19071703) B19071703
theorem B4829053 : Blo 1466553 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B1650559 : Blo 1466553 1650559 := bstep (se 1 (by rfl) ⟨1237919, by rfl⟩ : syracuseStep 1650559 = 2475839) B2475839
theorem B20344841 : Blo 1466553 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B5951663 : Blo 1466553 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B5574845 : Blo 1466553 5574845 := bstep (se 3 (by rfl) ⟨1045283, by rfl⟩ : syracuseStep 5574845 = 2090567) B2090567
theorem B11145437 : Blo 1466553 11145437 := bstep (se 3 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 11145437 = 4179539) B4179539
theorem B7434503 : Blo 1466553 7434503 := bstep (se 1 (by rfl) ⟨5575877, by rfl⟩ : syracuseStep 7434503 = 11151755) B11151755
theorem B7934249 : Blo 1466553 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B13390217 : Blo 1466553 13390217 := bstep (se 2 (by rfl) ⟨5021331, by rfl⟩ : syracuseStep 13390217 = 10042663) B10042663
theorem B1651099 : Blo 1466553 1651099 := bstep (se 1 (by rfl) ⟨1238324, by rfl⟩ : syracuseStep 1651099 = 2476649) B2476649
theorem B38670767 : Blo 1466553 38670767 := bstep (se 1 (by rfl) ⟨29003075, by rfl⟩ : syracuseStep 38670767 = 58006151) B58006151
theorem B14103143 : Blo 1466553 14103143 := bstep (se 1 (by rfl) ⟨10577357, by rfl⟩ : syracuseStep 14103143 = 21154715) B21154715
theorem B25080515 : Blo 1466553 25080515 := bstep (se 1 (by rfl) ⟨18810386, by rfl⟩ : syracuseStep 25080515 = 37620773) B37620773
theorem B6271769 : Blo 1466553 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B2200559 : Blo 1466553 2200559 := bstep (se 1 (by rfl) ⟨1650419, by rfl⟩ : syracuseStep 2200559 = 3300839) B3300839
theorem B1651783 : Blo 1466553 1651783 := bstep (se 1 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 1651783 = 2477675) B2477675
theorem B14095457 : Blo 1466553 14095457 := bstep (se 2 (by rfl) ⟨5285796, by rfl⟩ : syracuseStep 14095457 = 10571593) B10571593
theorem B4699241 : Blo 1466553 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B28210355 : Blo 1466553 28210355 := bstep (se 1 (by rfl) ⟨21157766, by rfl⟩ : syracuseStep 28210355 = 42315533) B42315533
theorem B1651963 : Blo 1466553 1651963 := bstep (se 1 (by rfl) ⟨1238972, by rfl⟩ : syracuseStep 1651963 = 2477945) B2477945
theorem B2200943 : Blo 1466553 2200943 := bstep (se 1 (by rfl) ⟨1650707, by rfl⟩ : syracuseStep 2200943 = 3301415) B3301415
theorem B26760577 : Blo 1466553 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B2201063 : Blo 1466553 2201063 := bstep (se 1 (by rfl) ⟨1650797, by rfl⟩ : syracuseStep 2201063 = 3301595) B3301595
theorem B2201225 : Blo 1466553 2201225 := bstep (se 2 (by rfl) ⟨825459, by rfl⟩ : syracuseStep 2201225 = 1650919) B1650919
theorem B2201243 : Blo 1466553 2201243 := bstep (se 1 (by rfl) ⟨1650932, by rfl⟩ : syracuseStep 2201243 = 3301865) B3301865
theorem B2201435 : Blo 1466553 2201435 := bstep (se 1 (by rfl) ⟨1651076, by rfl⟩ : syracuseStep 2201435 = 3302153) B3302153
theorem B7051283 : Blo 1466553 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B3717161 : Blo 1466553 3717161 := bstep (se 2 (by rfl) ⟨1393935, by rfl⟩ : syracuseStep 3717161 = 2787871) B2787871
theorem B3717191 : Blo 1466553 3717191 := bstep (se 1 (by rfl) ⟨2787893, by rfl⟩ : syracuseStep 3717191 = 5575787) B5575787
theorem B5568695 : Blo 1466553 5568695 := bstep (se 1 (by rfl) ⟨4176521, by rfl⟩ : syracuseStep 5568695 = 8353043) B8353043
theorem B8353975 : Blo 1466553 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B2201819 : Blo 1466553 2201819 := bstep (se 1 (by rfl) ⟨1651364, by rfl⟩ : syracuseStep 2201819 = 3302729) B3302729
theorem B2202089 : Blo 1466553 2202089 := bstep (se 2 (by rfl) ⟨825783, by rfl⟩ : syracuseStep 2202089 = 1651567) B1651567
theorem B6265345 : Blo 1466553 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B3299867 : Blo 1466553 3299867 := bstep (se 1 (by rfl) ⟨2474900, by rfl⟩ : syracuseStep 3299867 = 4949801) B4949801
theorem B5569181 : Blo 1466553 5569181 := bstep (se 3 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 5569181 = 2088443) B2088443
theorem B4954877 : Blo 1466553 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B3136313 : Blo 1466553 3136313 := bstep (se 2 (by rfl) ⟨1176117, by rfl⟩ : syracuseStep 3136313 = 2352235) B2352235
theorem B2202479 : Blo 1466553 2202479 := bstep (se 1 (by rfl) ⟨1651859, by rfl⟩ : syracuseStep 2202479 = 3303719) B3303719
theorem B2202491 : Blo 1466553 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B6880247 : Blo 1466553 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B28195897 : Blo 1466553 28195897 := bstep (se 2 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 28195897 = 21146923) B21146923
theorem B2784719 : Blo 1466553 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B38108717 : Blo 1466553 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B48905909 : Blo 1466553 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B12533561 : Blo 1466553 12533561 := bstep (se 2 (by rfl) ⟨4700085, by rfl⟩ : syracuseStep 12533561 = 9400171) B9400171
theorem B3301217 : Blo 1466553 3301217 := bstep (se 2 (by rfl) ⟨1237956, by rfl⟩ : syracuseStep 3301217 = 2475913) B2475913
theorem B4177831 : Blo 1466553 4177831 := bstep (se 1 (by rfl) ⟨3133373, by rfl⟩ : syracuseStep 4177831 = 6266747) B6266747
theorem B3301343 : Blo 1466553 3301343 := bstep (se 1 (by rfl) ⟨2476007, by rfl⟩ : syracuseStep 3301343 = 4952015) B4952015
theorem B7430291 : Blo 1466553 7430291 := bstep (se 1 (by rfl) ⟨5572718, by rfl⟩ : syracuseStep 7430291 = 11145437) B11145437
theorem B4956335 : Blo 1466553 4956335 := bstep (se 1 (by rfl) ⟨3717251, by rfl⟩ : syracuseStep 4956335 = 7434503) B7434503
theorem B25780511 : Blo 1466553 25780511 := bstep (se 1 (by rfl) ⟨19335383, by rfl⟩ : syracuseStep 25780511 = 38670767) B38670767
theorem B813810037 : Blo 1466553 813810037 := bstep (se 5 (by rfl) ⟨38147345, by rfl⟩ : syracuseStep 813810037 = 76294691) B76294691
theorem B3572129 : Blo 1466553 3572129 := bstep (se 2 (by rfl) ⟨1339548, by rfl⟩ : syracuseStep 3572129 = 2679097) B2679097
theorem B16720343 : Blo 1466553 16720343 := bstep (se 1 (by rfl) ⟨12540257, by rfl⟩ : syracuseStep 16720343 = 25080515) B25080515
theorem B1467039 : Blo 1466553 1467039 := bstep (se 1 (by rfl) ⟨1100279, by rfl⟩ : syracuseStep 1467039 = 2200559) B2200559
theorem B18809567 : Blo 1466553 18809567 := bstep (se 1 (by rfl) ⟨14107175, by rfl⟩ : syracuseStep 18809567 = 28214351) B28214351
theorem B9396971 : Blo 1466553 9396971 := bstep (se 1 (by rfl) ⟨7047728, by rfl⟩ : syracuseStep 9396971 = 14095457) B14095457
theorem B1467295 : Blo 1466553 1467295 := bstep (se 1 (by rfl) ⟨1100471, by rfl⟩ : syracuseStep 1467295 = 2200943) B2200943
theorem B1467375 : Blo 1466553 1467375 := bstep (se 1 (by rfl) ⟨1100531, by rfl⟩ : syracuseStep 1467375 = 2201063) B2201063
theorem B3965993 : Blo 1466553 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B9405503 : Blo 1466553 9405503 := bstep (se 1 (by rfl) ⟨7054127, by rfl⟩ : syracuseStep 9405503 = 14108255) B14108255
theorem B2786375 : Blo 1466553 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B1467483 : Blo 1466553 1467483 := bstep (se 1 (by rfl) ⟨1100612, by rfl⟩ : syracuseStep 1467483 = 2201225) B2201225
theorem B1467495 : Blo 1466553 1467495 := bstep (se 1 (by rfl) ⟨1100621, by rfl⟩ : syracuseStep 1467495 = 2201243) B2201243
theorem B1467623 : Blo 1466553 1467623 := bstep (se 1 (by rfl) ⟨1100717, by rfl⟩ : syracuseStep 1467623 = 2201435) B2201435
theorem B37594529 : Blo 1466553 37594529 := bstep (se 2 (by rfl) ⟨14097948, by rfl⟩ : syracuseStep 37594529 = 28195897) B28195897
theorem B3712463 : Blo 1466553 3712463 := bstep (se 1 (by rfl) ⟨2784347, by rfl⟩ : syracuseStep 3712463 = 5568695) B5568695
theorem B1467879 : Blo 1466553 1467879 := bstep (se 1 (by rfl) ⟨1100909, by rfl⟩ : syracuseStep 1467879 = 2201819) B2201819
theorem B1468059 : Blo 1466553 1468059 := bstep (se 1 (by rfl) ⟨1101044, by rfl⟩ : syracuseStep 1468059 = 2202089) B2202089
theorem B9537263 : Blo 1466553 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B9406219 : Blo 1466553 9406219 := bstep (se 1 (by rfl) ⟨7054664, by rfl⟩ : syracuseStep 9406219 = 14109329) B14109329
theorem B3712787 : Blo 1466553 3712787 := bstep (se 1 (by rfl) ⟨2784590, by rfl⟩ : syracuseStep 3712787 = 5569181) B5569181
theorem B15861577 : Blo 1466553 15861577 := bstep (se 2 (by rfl) ⟨5948091, by rfl⟩ : syracuseStep 15861577 = 11896183) B11896183
theorem B3303251 : Blo 1466553 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B2090875 : Blo 1466553 2090875 := bstep (se 1 (by rfl) ⟨1568156, by rfl⟩ : syracuseStep 2090875 = 3136313) B3136313
theorem B1468319 : Blo 1466553 1468319 := bstep (se 1 (by rfl) ⟨1101239, by rfl⟩ : syracuseStep 1468319 = 2202479) B2202479
theorem B1468327 : Blo 1466553 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B4179995 : Blo 1466553 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B5572871 : Blo 1466553 5572871 := bstep (se 1 (by rfl) ⟨4179653, by rfl⟩ : syracuseStep 5572871 = 8359307) B8359307
theorem B8358167 : Blo 1466553 8358167 := bstep (se 1 (by rfl) ⟨6268625, by rfl⟩ : syracuseStep 8358167 = 12537251) B12537251
theorem B25405811 : Blo 1466553 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B7047593 : Blo 1466553 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B3967775 : Blo 1466553 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B3713951 : Blo 1466553 3713951 := bstep (se 1 (by rfl) ⟨2785463, by rfl⟩ : syracuseStep 3713951 = 5570927) B5570927
theorem B7531487 : Blo 1466553 7531487 := bstep (se 1 (by rfl) ⟨5648615, by rfl⟩ : syracuseStep 7531487 = 11297231) B11297231
theorem B9047209 : Blo 1466553 9047209 := bstep (se 2 (by rfl) ⟨3392703, by rfl⟩ : syracuseStep 9047209 = 6785407) B6785407
theorem B5287295 : Blo 1466553 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B3132827 : Blo 1466553 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B1650343 : Blo 1466553 1650343 := bstep (se 1 (by rfl) ⟨1237757, by rfl⟩ : syracuseStep 1650343 = 2475515) B2475515
theorem B7425917 : Blo 1466553 7425917 := bstep (se 3 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 7425917 = 2784719) B2784719
theorem B2478107 : Blo 1466553 2478107 := bstep (se 1 (by rfl) ⟨1858580, by rfl⟩ : syracuseStep 2478107 = 3717161) B3717161
theorem B2478127 : Blo 1466553 2478127 := bstep (se 1 (by rfl) ⟨1858595, by rfl⟩ : syracuseStep 2478127 = 3717191) B3717191
theorem B16715969 : Blo 1466553 16715969 := bstep (se 2 (by rfl) ⟨6268488, by rfl⟩ : syracuseStep 16715969 = 12536977) B12536977
theorem B2199911 : Blo 1466553 2199911 := bstep (se 1 (by rfl) ⟨1649933, by rfl⟩ : syracuseStep 2199911 = 3299867) B3299867
theorem B35680769 : Blo 1466553 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B16724717 : Blo 1466553 16724717 := bstep (se 3 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 16724717 = 6271769) B6271769
theorem B1651495 : Blo 1466553 1651495 := bstep (se 1 (by rfl) ⟨1238621, by rfl⟩ : syracuseStep 1651495 = 2477243) B2477243
theorem B3715895 : Blo 1466553 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B2200745 : Blo 1466553 2200745 := bstep (se 2 (by rfl) ⟨825279, by rfl⟩ : syracuseStep 2200745 = 1650559) B1650559
theorem B67810499 : Blo 1466553 67810499 := bstep (se 1 (by rfl) ⟨50857874, by rfl⟩ : syracuseStep 67810499 = 101715749) B101715749
theorem B2200811 : Blo 1466553 2200811 := bstep (se 1 (by rfl) ⟨1650608, by rfl⟩ : syracuseStep 2200811 = 3301217) B3301217
theorem B2200895 : Blo 1466553 2200895 := bstep (se 1 (by rfl) ⟨1650671, by rfl⟩ : syracuseStep 2200895 = 3301343) B3301343
theorem B13563227 : Blo 1466553 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B3716563 : Blo 1466553 3716563 := bstep (se 1 (by rfl) ⟨2787422, by rfl⟩ : syracuseStep 3716563 = 5574845) B5574845
theorem B2201087 : Blo 1466553 2201087 := bstep (se 1 (by rfl) ⟨1650815, by rfl⟩ : syracuseStep 2201087 = 3301631) B3301631
theorem B5289499 : Blo 1466553 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B11138633 : Blo 1466553 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B8926811 : Blo 1466553 8926811 := bstep (se 1 (by rfl) ⟨6695108, by rfl⟩ : syracuseStep 8926811 = 13390217) B13390217
theorem B2201195 : Blo 1466553 2201195 := bstep (se 1 (by rfl) ⟨1650896, by rfl⟩ : syracuseStep 2201195 = 3301793) B3301793
theorem B9402095 : Blo 1466553 9402095 := bstep (se 1 (by rfl) ⟨7051571, by rfl⟩ : syracuseStep 9402095 = 14103143) B14103143
theorem B52221763 : Blo 1466553 52221763 := bstep (se 1 (by rfl) ⟨39166322, by rfl⟩ : syracuseStep 52221763 = 78332645) B78332645
theorem B2201465 : Blo 1466553 2201465 := bstep (se 2 (by rfl) ⟨825549, by rfl⟩ : syracuseStep 2201465 = 1651099) B1651099
theorem B8353793 : Blo 1466553 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B2201711 : Blo 1466553 2201711 := bstep (se 1 (by rfl) ⟨1651283, by rfl⟩ : syracuseStep 2201711 = 3302567) B3302567
theorem B18806903 : Blo 1466553 18806903 := bstep (se 1 (by rfl) ⟨14105177, by rfl⟩ : syracuseStep 18806903 = 28210355) B28210355
theorem B2201783 : Blo 1466553 2201783 := bstep (se 1 (by rfl) ⟨1651337, by rfl⟩ : syracuseStep 2201783 = 3302675) B3302675
theorem B2202203 : Blo 1466553 2202203 := bstep (se 1 (by rfl) ⟨1651652, by rfl⟩ : syracuseStep 2202203 = 3303305) B3303305
theorem B2202215 : Blo 1466553 2202215 := bstep (se 1 (by rfl) ⟨1651661, by rfl⟩ : syracuseStep 2202215 = 3303323) B3303323
theorem B2202239 : Blo 1466553 2202239 := bstep (se 1 (by rfl) ⟨1651679, by rfl⟩ : syracuseStep 2202239 = 3303359) B3303359
theorem B4700855 : Blo 1466553 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B2202347 : Blo 1466553 2202347 := bstep (se 1 (by rfl) ⟨1651760, by rfl⟩ : syracuseStep 2202347 = 3303521) B3303521
theorem B2202377 : Blo 1466553 2202377 := bstep (se 2 (by rfl) ⟨825891, by rfl⟩ : syracuseStep 2202377 = 1651783) B1651783
theorem B6265687 : Blo 1466553 6265687 := bstep (se 1 (by rfl) ⟨4699265, by rfl⟩ : syracuseStep 6265687 = 9398531) B9398531
theorem B2202617 : Blo 1466553 2202617 := bstep (se 2 (by rfl) ⟨825981, by rfl⟩ : syracuseStep 2202617 = 1651963) B1651963
theorem B2350171 : Blo 1466553 2350171 := bstep (se 1 (by rfl) ⟨1762628, by rfl⟩ : syracuseStep 2350171 = 3525257) B3525257
theorem B8469785 : Blo 1466553 8469785 := bstep (se 2 (by rfl) ⟨3176169, by rfl⟩ : syracuseStep 8469785 = 6352339) B6352339
theorem B4586831 : Blo 1466553 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B28221047 : Blo 1466553 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B32603939 : Blo 1466553 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B6438737 : Blo 1466553 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B8355707 : Blo 1466553 8355707 := bstep (se 1 (by rfl) ⟨6266780, by rfl⟩ : syracuseStep 8355707 = 12533561) B12533561
theorem B5570441 : Blo 1466553 5570441 := bstep (se 2 (by rfl) ⟨2088915, by rfl⟩ : syracuseStep 5570441 = 4177831) B4177831
theorem B18800545 : Blo 1466553 18800545 := bstep (se 2 (by rfl) ⟨7050204, by rfl⟩ : syracuseStep 18800545 = 14100409) B14100409
theorem B17187007 : Blo 1466553 17187007 := bstep (se 1 (by rfl) ⟨12890255, by rfl⟩ : syracuseStep 17187007 = 25780511) B25780511
theorem B1466607 : Blo 1466553 1466607 := bstep (se 1 (by rfl) ⟨1099955, by rfl⟩ : syracuseStep 1466607 = 2199911) B2199911
theorem B1085080049 : Blo 1466553 1085080049 := bstep (se 2 (by rfl) ⟨406905018, by rfl⟩ : syracuseStep 1085080049 = 813810037) B813810037
theorem B11149811 : Blo 1466553 11149811 := bstep (se 1 (by rfl) ⟨8362358, by rfl⟩ : syracuseStep 11149811 = 16724717) B16724717
theorem B1467163 : Blo 1466553 1467163 := bstep (se 1 (by rfl) ⟨1100372, by rfl⟩ : syracuseStep 1467163 = 2200745) B2200745
theorem B1467207 : Blo 1466553 1467207 := bstep (se 1 (by rfl) ⟨1100405, by rfl⟩ : syracuseStep 1467207 = 2200811) B2200811
theorem B1467263 : Blo 1466553 1467263 := bstep (se 1 (by rfl) ⟨1100447, by rfl⟩ : syracuseStep 1467263 = 2200895) B2200895
theorem B2474975 : Blo 1466553 2474975 := bstep (se 1 (by rfl) ⟨1856231, by rfl⟩ : syracuseStep 2474975 = 3712463) B3712463
theorem B14099453 : Blo 1466553 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B1467391 : Blo 1466553 1467391 := bstep (se 1 (by rfl) ⟨1100543, by rfl⟩ : syracuseStep 1467391 = 2201087) B2201087
theorem B1467463 : Blo 1466553 1467463 := bstep (se 1 (by rfl) ⟨1100597, by rfl⟩ : syracuseStep 1467463 = 2201195) B2201195
theorem B6268063 : Blo 1466553 6268063 := bstep (se 1 (by rfl) ⟨4701047, by rfl⟩ : syracuseStep 6268063 = 9402095) B9402095
theorem B6358175 : Blo 1466553 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B2475191 : Blo 1466553 2475191 := bstep (se 1 (by rfl) ⟨1856393, by rfl⟩ : syracuseStep 2475191 = 3712787) B3712787
theorem B1467643 : Blo 1466553 1467643 := bstep (se 1 (by rfl) ⟨1100732, by rfl⟩ : syracuseStep 1467643 = 2201465) B2201465
theorem B2786663 : Blo 1466553 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B1467807 : Blo 1466553 1467807 := bstep (se 1 (by rfl) ⟨1100855, by rfl⟩ : syracuseStep 1467807 = 2201711) B2201711
theorem B1467855 : Blo 1466553 1467855 := bstep (se 1 (by rfl) ⟨1100891, by rfl⟩ : syracuseStep 1467855 = 2201783) B2201783
theorem B5572111 : Blo 1466553 5572111 := bstep (se 1 (by rfl) ⟨4179083, by rfl⟩ : syracuseStep 5572111 = 8358167) B8358167
theorem B1468135 : Blo 1466553 1468135 := bstep (se 1 (by rfl) ⟨1101101, by rfl⟩ : syracuseStep 1468135 = 2202203) B2202203
theorem B1468143 : Blo 1466553 1468143 := bstep (se 1 (by rfl) ⟨1101107, by rfl⟩ : syracuseStep 1468143 = 2202215) B2202215
theorem B1468159 : Blo 1466553 1468159 := bstep (se 1 (by rfl) ⟨1101119, by rfl⟩ : syracuseStep 1468159 = 2202239) B2202239
theorem B1468231 : Blo 1466553 1468231 := bstep (se 1 (by rfl) ⟨1101173, by rfl⟩ : syracuseStep 1468231 = 2202347) B2202347
theorem B1468251 : Blo 1466553 1468251 := bstep (se 1 (by rfl) ⟨1101188, by rfl⟩ : syracuseStep 1468251 = 2202377) B2202377
theorem B2475967 : Blo 1466553 2475967 := bstep (se 1 (by rfl) ⟨1856975, by rfl⟩ : syracuseStep 2475967 = 3713951) B3713951
theorem B1468411 : Blo 1466553 1468411 := bstep (se 1 (by rfl) ⟨1101308, by rfl⟩ : syracuseStep 1468411 = 2202617) B2202617
theorem B5646523 : Blo 1466553 5646523 := bstep (se 1 (by rfl) ⟨4234892, by rfl⟩ : syracuseStep 5646523 = 8469785) B8469785
theorem B3057887 : Blo 1466553 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B2787833 : Blo 1466553 2787833 := bstep (se 2 (by rfl) ⟨1045437, by rfl⟩ : syracuseStep 2787833 = 2090875) B2090875
theorem B21735959 : Blo 1466553 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B4950611 : Blo 1466553 4950611 := bstep (se 1 (by rfl) ⟨3712958, by rfl⟩ : syracuseStep 4950611 = 7425917) B7425917
theorem B3713627 : Blo 1466553 3713627 := bstep (se 1 (by rfl) ⟨2785220, by rfl⟩ : syracuseStep 3713627 = 5570441) B5570441
theorem B3304169 : Blo 1466553 3304169 := bstep (se 2 (by rfl) ⟨1239063, by rfl⟩ : syracuseStep 3304169 = 2478127) B2478127
theorem B3304223 : Blo 1466553 3304223 := bstep (se 1 (by rfl) ⟨2478167, by rfl⟩ : syracuseStep 3304223 = 4956335) B4956335
theorem B11143979 : Blo 1466553 11143979 := bstep (se 1 (by rfl) ⟨8357984, by rfl⟩ : syracuseStep 11143979 = 16715969) B16715969
theorem B2477263 : Blo 1466553 2477263 := bstep (se 1 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 2477263 = 3715895) B3715895
theorem B6270335 : Blo 1466553 6270335 := bstep (se 1 (by rfl) ⟨4702751, by rfl⟩ : syracuseStep 6270335 = 9405503) B9405503
theorem B45206999 : Blo 1466553 45206999 := bstep (se 1 (by rfl) ⟨33905249, by rfl⟩ : syracuseStep 45206999 = 67810499) B67810499
theorem B25063019 : Blo 1466553 25063019 := bstep (se 1 (by rfl) ⟨18797264, by rfl⟩ : syracuseStep 25063019 = 37594529) B37594529
theorem B7425755 : Blo 1466553 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B5951207 : Blo 1466553 5951207 := bstep (se 1 (by rfl) ⟨4463405, by rfl⟩ : syracuseStep 5951207 = 8926811) B8926811
theorem B12537935 : Blo 1466553 12537935 := bstep (se 1 (by rfl) ⟨9403451, by rfl⟩ : syracuseStep 12537935 = 18806903) B18806903
theorem B3133561 : Blo 1466553 3133561 := bstep (se 2 (by rfl) ⟨1175085, by rfl⟩ : syracuseStep 3133561 = 2350171) B2350171
theorem B3715247 : Blo 1466553 3715247 := bstep (se 1 (by rfl) ⟨2786435, by rfl⟩ : syracuseStep 3715247 = 5572871) B5572871
theorem B12062945 : Blo 1466553 12062945 := bstep (se 2 (by rfl) ⟨4523604, by rfl⟩ : syracuseStep 12062945 = 9047209) B9047209
theorem B16937207 : Blo 1466553 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B4698395 : Blo 1466553 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B278516069 : Blo 1466553 278516069 := bstep (se 4 (by rfl) ⟨26110881, by rfl⟩ : syracuseStep 278516069 = 52221763) B52221763
theorem B3133903 : Blo 1466553 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B2200457 : Blo 1466553 2200457 := bstep (se 2 (by rfl) ⟨825171, by rfl⟩ : syracuseStep 2200457 = 1650343) B1650343
theorem B18814031 : Blo 1466553 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B21148769 : Blo 1466553 21148769 := bstep (se 2 (by rfl) ⟨7930788, by rfl⟩ : syracuseStep 21148769 = 15861577) B15861577
theorem B1652071 : Blo 1466553 1652071 := bstep (se 1 (by rfl) ⟨1239053, by rfl⟩ : syracuseStep 1652071 = 2478107) B2478107
theorem B4953527 : Blo 1466553 4953527 := bstep (se 1 (by rfl) ⟨3715145, by rfl⟩ : syracuseStep 4953527 = 7430291) B7430291
theorem B2381419 : Blo 1466553 2381419 := bstep (se 1 (by rfl) ⟨1786064, by rfl⟩ : syracuseStep 2381419 = 3572129) B3572129
theorem B11146895 : Blo 1466553 11146895 := bstep (se 1 (by rfl) ⟨8360171, by rfl⟩ : syracuseStep 11146895 = 16720343) B16720343
theorem B23787179 : Blo 1466553 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B12539711 : Blo 1466553 12539711 := bstep (se 1 (by rfl) ⟨9404783, by rfl⟩ : syracuseStep 12539711 = 18809567) B18809567
theorem B6264647 : Blo 1466553 6264647 := bstep (se 1 (by rfl) ⟨4698485, by rfl⟩ : syracuseStep 6264647 = 9396971) B9396971
theorem B2643995 : Blo 1466553 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B1857583 : Blo 1466553 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B9042151 : Blo 1466553 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B2201993 : Blo 1466553 2201993 := bstep (se 2 (by rfl) ⟨825747, by rfl⟩ : syracuseStep 2201993 = 1651495) B1651495
theorem B8354249 : Blo 1466553 8354249 := bstep (se 2 (by rfl) ⟨3132843, by rfl⟩ : syracuseStep 8354249 = 6265687) B6265687
theorem B2202167 : Blo 1466553 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B5569195 : Blo 1466553 5569195 := bstep (se 1 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 5569195 = 8353793) B8353793
theorem B2645183 : Blo 1466553 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B4955417 : Blo 1466553 4955417 := bstep (se 2 (by rfl) ⟨1858281, by rfl⟩ : syracuseStep 4955417 = 3716563) B3716563
theorem B5020991 : Blo 1466553 5020991 := bstep (se 1 (by rfl) ⟨3765743, by rfl⟩ : syracuseStep 5020991 = 7531487) B7531487
theorem B7052665 : Blo 1466553 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B17169965 : Blo 1466553 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B2088551 : Blo 1466553 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B12541625 : Blo 1466553 12541625 := bstep (se 2 (by rfl) ⟨4703109, by rfl⟩ : syracuseStep 12541625 = 9406219) B9406219
theorem B25067393 : Blo 1466553 25067393 := bstep (se 2 (by rfl) ⟨9400272, by rfl⟩ : syracuseStep 25067393 = 18800545) B18800545
theorem B5570471 : Blo 1466553 5570471 := bstep (se 1 (by rfl) ⟨4177853, by rfl⟩ : syracuseStep 5570471 = 8355707) B8355707
theorem B4178081 : Blo 1466553 4178081 := bstep (se 2 (by rfl) ⟨1566780, by rfl⟩ : syracuseStep 4178081 = 3133561) B3133561
theorem B7528697 : Blo 1466553 7528697 := bstep (se 2 (by rfl) ⟨2823261, by rfl⟩ : syracuseStep 7528697 = 5646523) B5646523
theorem B723386699 : Blo 1466553 723386699 := bstep (se 1 (by rfl) ⟨542540024, by rfl⟩ : syracuseStep 723386699 = 1085080049) B1085080049
theorem B1466971 : Blo 1466553 1466971 := bstep (se 1 (by rfl) ⟨1100228, by rfl⟩ : syracuseStep 1466971 = 2200457) B2200457
theorem B4178537 : Blo 1466553 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B12542687 : Blo 1466553 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B14099179 : Blo 1466553 14099179 := bstep (se 1 (by rfl) ⟨10574384, by rfl⟩ : syracuseStep 14099179 = 21148769) B21148769
theorem B7431101 : Blo 1466553 7431101 := bstep (se 3 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 7431101 = 2786663) B2786663
theorem B3302351 : Blo 1466553 3302351 := bstep (se 1 (by rfl) ⟨2476763, by rfl⟩ : syracuseStep 3302351 = 4953527) B4953527
theorem B7431263 : Blo 1466553 7431263 := bstep (se 1 (by rfl) ⟨5573447, by rfl⟩ : syracuseStep 7431263 = 11146895) B11146895
theorem B1762663 : Blo 1466553 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B8357417 : Blo 1466553 8357417 := bstep (se 2 (by rfl) ⟨3134031, by rfl⟩ : syracuseStep 8357417 = 6268063) B6268063
theorem B1467995 : Blo 1466553 1467995 := bstep (se 1 (by rfl) ⟨1100996, by rfl⟩ : syracuseStep 1467995 = 2201993) B2201993
theorem B3303017 : Blo 1466553 3303017 := bstep (se 2 (by rfl) ⟨1238631, by rfl⟩ : syracuseStep 3303017 = 2477263) B2477263
theorem B1468111 : Blo 1466553 1468111 := bstep (se 1 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 1468111 = 2202167) B2202167
theorem B2475751 : Blo 1466553 2475751 := bstep (se 1 (by rfl) ⟨1856813, by rfl⟩ : syracuseStep 2475751 = 3713627) B3713627
theorem B1763455 : Blo 1466553 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B3303611 : Blo 1466553 3303611 := bstep (se 1 (by rfl) ⟨2477708, by rfl⟩ : syracuseStep 3303611 = 4955417) B4955417
theorem B4180223 : Blo 1466553 4180223 := bstep (se 1 (by rfl) ⟨3135167, by rfl⟩ : syracuseStep 4180223 = 6270335) B6270335
theorem B11446643 : Blo 1466553 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B4950503 : Blo 1466553 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B3967471 : Blo 1466553 3967471 := bstep (se 1 (by rfl) ⟨2975603, by rfl⟩ : syracuseStep 3967471 = 5951207) B5951207
theorem B3713647 : Blo 1466553 3713647 := bstep (se 1 (by rfl) ⟨2785235, by rfl⟩ : syracuseStep 3713647 = 5570471) B5570471
theorem B8358623 : Blo 1466553 8358623 := bstep (se 1 (by rfl) ⟨6268967, by rfl⟩ : syracuseStep 8358623 = 12537935) B12537935
theorem B2476777 : Blo 1466553 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B2476831 : Blo 1466553 2476831 := bstep (se 1 (by rfl) ⟨1857623, by rfl⟩ : syracuseStep 2476831 = 3715247) B3715247
theorem B11291471 : Blo 1466553 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B3132263 : Blo 1466553 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B22916009 : Blo 1466553 22916009 := bstep (se 2 (by rfl) ⟨8593503, by rfl⟩ : syracuseStep 22916009 = 17187007) B17187007
theorem B7433207 : Blo 1466553 7433207 := bstep (se 1 (by rfl) ⟨5574905, by rfl⟩ : syracuseStep 7433207 = 11149811) B11149811
theorem B12700901 : Blo 1466553 12700901 := bstep (se 4 (by rfl) ⟨1190709, by rfl⟩ : syracuseStep 12700901 = 2381419) B2381419
theorem B1649983 : Blo 1466553 1649983 := bstep (se 1 (by rfl) ⟨1237487, by rfl⟩ : syracuseStep 1649983 = 2474975) B2474975
theorem B9399635 : Blo 1466553 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B4238783 : Blo 1466553 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B1650127 : Blo 1466553 1650127 := bstep (se 1 (by rfl) ⟨1237595, by rfl⟩ : syracuseStep 1650127 = 2475191) B2475191
theorem B7425593 : Blo 1466553 7425593 := bstep (se 2 (by rfl) ⟨2784597, by rfl⟩ : syracuseStep 7425593 = 5569195) B5569195
theorem B8359807 : Blo 1466553 8359807 := bstep (se 1 (by rfl) ⟨6269855, by rfl⟩ : syracuseStep 8359807 = 12539711) B12539711
theorem B57962557 : Blo 1466553 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B3347327 : Blo 1466553 3347327 := bstep (se 1 (by rfl) ⟨2510495, by rfl⟩ : syracuseStep 3347327 = 5020991) B5020991
theorem B16708679 : Blo 1466553 16708679 := bstep (se 1 (by rfl) ⟨12531509, by rfl⟩ : syracuseStep 16708679 = 25063019) B25063019
theorem B8361083 : Blo 1466553 8361083 := bstep (se 1 (by rfl) ⟨6270812, by rfl⟩ : syracuseStep 8361083 = 12541625) B12541625
theorem B8041963 : Blo 1466553 8041963 := bstep (se 1 (by rfl) ⟨6031472, by rfl⟩ : syracuseStep 8041963 = 12062945) B12062945
theorem B185677379 : Blo 1466553 185677379 := bstep (se 1 (by rfl) ⟨139258034, by rfl⟩ : syracuseStep 185677379 = 278516069) B278516069
theorem B12056201 : Blo 1466553 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B15858119 : Blo 1466553 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B4176431 : Blo 1466553 4176431 := bstep (se 1 (by rfl) ⟨3132323, by rfl⟩ : syracuseStep 4176431 = 6264647) B6264647
theorem B2038591 : Blo 1466553 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B5569469 : Blo 1466553 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B5569499 : Blo 1466553 5569499 := bstep (se 1 (by rfl) ⟨4177124, by rfl⟩ : syracuseStep 5569499 = 8354249) B8354249
theorem B1858555 : Blo 1466553 1858555 := bstep (se 1 (by rfl) ⟨1393916, by rfl⟩ : syracuseStep 1858555 = 2787833) B2787833
theorem B3300407 : Blo 1466553 3300407 := bstep (se 1 (by rfl) ⟨2475305, by rfl⟩ : syracuseStep 3300407 = 4950611) B4950611
theorem B2202761 : Blo 1466553 2202761 := bstep (se 2 (by rfl) ⟨826035, by rfl⟩ : syracuseStep 2202761 = 1652071) B1652071
theorem B2202779 : Blo 1466553 2202779 := bstep (se 1 (by rfl) ⟨1652084, by rfl⟩ : syracuseStep 2202779 = 3304169) B3304169
theorem B9403553 : Blo 1466553 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B2202815 : Blo 1466553 2202815 := bstep (se 1 (by rfl) ⟨1652111, by rfl⟩ : syracuseStep 2202815 = 3304223) B3304223
theorem B7429319 : Blo 1466553 7429319 := bstep (se 1 (by rfl) ⟨5571989, by rfl⟩ : syracuseStep 7429319 = 11143979) B11143979
theorem B7429481 : Blo 1466553 7429481 := bstep (se 2 (by rfl) ⟨2786055, by rfl⟩ : syracuseStep 7429481 = 5572111) B5572111
theorem B30137999 : Blo 1466553 30137999 := bstep (se 1 (by rfl) ⟨22603499, by rfl⟩ : syracuseStep 30137999 = 45206999) B45206999
theorem B3301289 : Blo 1466553 3301289 := bstep (se 2 (by rfl) ⟨1237983, by rfl⟩ : syracuseStep 3301289 = 2475967) B2475967
theorem B16711595 : Blo 1466553 16711595 := bstep (se 1 (by rfl) ⟨12533696, by rfl⟩ : syracuseStep 16711595 = 25067393) B25067393
theorem B77283409 : Blo 1466553 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B2351273 : Blo 1466553 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B2785691 : Blo 1466553 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B11141549 : Blo 1466553 11141549 := bstep (se 3 (by rfl) ⟨2089040, by rfl⟩ : syracuseStep 11141549 = 4178081) B4178081
theorem B25076141 : Blo 1466553 25076141 := bstep (se 3 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 25076141 = 9403553) B9403553
theorem B30524381 : Blo 1466553 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B3302369 : Blo 1466553 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B5571611 : Blo 1466553 5571611 := bstep (se 1 (by rfl) ⟨4178708, by rfl⟩ : syracuseStep 5571611 = 8357417) B8357417
theorem B3302441 : Blo 1466553 3302441 := bstep (se 2 (by rfl) ⟨1238415, by rfl⟩ : syracuseStep 3302441 = 2476831) B2476831
theorem B8037467 : Blo 1466553 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B2786815 : Blo 1466553 2786815 := bstep (se 1 (by rfl) ⟨2090111, by rfl⟩ : syracuseStep 2786815 = 4180223) B4180223
theorem B10872485 : Blo 1466553 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B5572415 : Blo 1466553 5572415 := bstep (se 1 (by rfl) ⟨4179311, by rfl⟩ : syracuseStep 5572415 = 8358623) B8358623
theorem B3712979 : Blo 1466553 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B3712999 : Blo 1466553 3712999 := bstep (se 1 (by rfl) ⟨2784749, by rfl⟩ : syracuseStep 3712999 = 5569499) B5569499
theorem B1468507 : Blo 1466553 1468507 := bstep (se 1 (by rfl) ⟨1101380, by rfl⟩ : syracuseStep 1468507 = 2202761) B2202761
theorem B1468519 : Blo 1466553 1468519 := bstep (se 1 (by rfl) ⟨1101389, by rfl⟩ : syracuseStep 1468519 = 2202779) B2202779
theorem B1468543 : Blo 1466553 1468543 := bstep (se 1 (by rfl) ⟨1101407, by rfl⟩ : syracuseStep 1468543 = 2202815) B2202815
theorem B4950395 : Blo 1466553 4950395 := bstep (se 1 (by rfl) ⟨3712796, by rfl⟩ : syracuseStep 4950395 = 7425593) B7425593
theorem B482257799 : Blo 1466553 482257799 := bstep (se 1 (by rfl) ⟨361693349, by rfl⟩ : syracuseStep 482257799 = 723386699) B723386699
theorem B2231551 : Blo 1466553 2231551 := bstep (se 1 (by rfl) ⟨1673663, by rfl⟩ : syracuseStep 2231551 = 3347327) B3347327
theorem B5574055 : Blo 1466553 5574055 := bstep (se 1 (by rfl) ⟨4180541, by rfl⟩ : syracuseStep 5574055 = 8361083) B8361083
theorem B4951529 : Blo 1466553 4951529 := bstep (se 2 (by rfl) ⟨1856823, by rfl⟩ : syracuseStep 4951529 = 3713647) B3713647
theorem B123784919 : Blo 1466553 123784919 := bstep (se 1 (by rfl) ⟨92838689, by rfl⟩ : syracuseStep 123784919 = 185677379) B185677379
theorem B2478073 : Blo 1466553 2478073 := bstep (se 2 (by rfl) ⟨929277, by rfl⟩ : syracuseStep 2478073 = 1858555) B1858555
theorem B10572079 : Blo 1466553 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B80367997 : Blo 1466553 80367997 := bstep (se 3 (by rfl) ⟨15068999, by rfl⟩ : syracuseStep 80367997 = 30137999) B30137999
theorem B2199977 : Blo 1466553 2199977 := bstep (se 2 (by rfl) ⟨824991, by rfl⟩ : syracuseStep 2199977 = 1649983) B1649983
theorem B2200169 : Blo 1466553 2200169 := bstep (se 2 (by rfl) ⟨825063, by rfl⟩ : syracuseStep 2200169 = 1650127) B1650127
theorem B2200271 : Blo 1466553 2200271 := bstep (se 1 (by rfl) ⟨1650203, by rfl⟩ : syracuseStep 2200271 = 3300407) B3300407
theorem B4952879 : Blo 1466553 4952879 := bstep (se 1 (by rfl) ⟨3714659, by rfl⟩ : syracuseStep 4952879 = 7429319) B7429319
theorem B8467267 : Blo 1466553 8467267 := bstep (se 1 (by rfl) ⟨6350450, by rfl⟩ : syracuseStep 8467267 = 12700901) B12700901
theorem B4952987 : Blo 1466553 4952987 := bstep (se 1 (by rfl) ⟨3714740, by rfl⟩ : syracuseStep 4952987 = 7429481) B7429481
theorem B11146409 : Blo 1466553 11146409 := bstep (se 2 (by rfl) ⟨4179903, by rfl⟩ : syracuseStep 11146409 = 8359807) B8359807
theorem B2200859 : Blo 1466553 2200859 := bstep (se 1 (by rfl) ⟨1650644, by rfl⟩ : syracuseStep 2200859 = 3301289) B3301289
theorem B5019131 : Blo 1466553 5019131 := bstep (se 1 (by rfl) ⟨3764348, by rfl⟩ : syracuseStep 5019131 = 7528697) B7528697
theorem B8361791 : Blo 1466553 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B4954067 : Blo 1466553 4954067 := bstep (se 1 (by rfl) ⟨3715550, by rfl⟩ : syracuseStep 4954067 = 7431101) B7431101
theorem B2201567 : Blo 1466553 2201567 := bstep (se 1 (by rfl) ⟨1651175, by rfl⟩ : syracuseStep 2201567 = 3302351) B3302351
theorem B5289961 : Blo 1466553 5289961 := bstep (se 2 (by rfl) ⟨1983735, by rfl⟩ : syracuseStep 5289961 = 3967471) B3967471
theorem B11139119 : Blo 1466553 11139119 := bstep (se 1 (by rfl) ⟨8354339, by rfl⟩ : syracuseStep 11139119 = 16708679) B16708679
theorem B4954175 : Blo 1466553 4954175 := bstep (se 1 (by rfl) ⟨3715631, by rfl⟩ : syracuseStep 4954175 = 7431263) B7431263
theorem B18798905 : Blo 1466553 18798905 := bstep (se 2 (by rfl) ⟨7049589, by rfl⟩ : syracuseStep 18798905 = 14099179) B14099179
theorem B2202011 : Blo 1466553 2202011 := bstep (se 1 (by rfl) ⟨1651508, by rfl⟩ : syracuseStep 2202011 = 3303017) B3303017
theorem B2202407 : Blo 1466553 2202407 := bstep (se 1 (by rfl) ⟨1651805, by rfl⟩ : syracuseStep 2202407 = 3303611) B3303611
theorem B3300335 : Blo 1466553 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2784287 : Blo 1466553 2784287 := bstep (se 1 (by rfl) ⟨2088215, by rfl⟩ : syracuseStep 2784287 = 4176431) B4176431
theorem B2350217 : Blo 1466553 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B7527647 : Blo 1466553 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B2088175 : Blo 1466553 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B15277339 : Blo 1466553 15277339 := bstep (se 1 (by rfl) ⟨11458004, by rfl⟩ : syracuseStep 15277339 = 22916009) B22916009
theorem B10722617 : Blo 1466553 10722617 := bstep (se 2 (by rfl) ⟨4020981, by rfl⟩ : syracuseStep 10722617 = 8041963) B8041963
theorem B4955471 : Blo 1466553 4955471 := bstep (se 1 (by rfl) ⟨3716603, by rfl⟩ : syracuseStep 4955471 = 7433207) B7433207
theorem B6266423 : Blo 1466553 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B2825855 : Blo 1466553 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B3301001 : Blo 1466553 3301001 := bstep (se 2 (by rfl) ⟨1237875, by rfl⟩ : syracuseStep 3301001 = 2475751) B2475751
theorem B11141063 : Blo 1466553 11141063 := bstep (se 1 (by rfl) ⟨8355797, by rfl⟩ : syracuseStep 11141063 = 16711595) B16711595
theorem B1466651 : Blo 1466553 1466651 := bstep (se 1 (by rfl) ⟨1099988, by rfl⟩ : syracuseStep 1466651 = 2199977) B2199977
theorem B1466779 : Blo 1466553 1466779 := bstep (se 1 (by rfl) ⟨1100084, by rfl⟩ : syracuseStep 1466779 = 2200169) B2200169
theorem B1466847 : Blo 1466553 1466847 := bstep (se 1 (by rfl) ⟨1100135, by rfl⟩ : syracuseStep 1466847 = 2200271) B2200271
theorem B3301919 : Blo 1466553 3301919 := bstep (se 1 (by rfl) ⟨2476439, by rfl⟩ : syracuseStep 3301919 = 4952879) B4952879
theorem B3301991 : Blo 1466553 3301991 := bstep (se 1 (by rfl) ⟨2476493, by rfl⟩ : syracuseStep 3301991 = 4952987) B4952987
theorem B20349587 : Blo 1466553 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B5358311 : Blo 1466553 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B7430939 : Blo 1466553 7430939 := bstep (se 1 (by rfl) ⟨5573204, by rfl⟩ : syracuseStep 7430939 = 11146409) B11146409
theorem B1467239 : Blo 1466553 1467239 := bstep (se 1 (by rfl) ⟨1100429, by rfl⟩ : syracuseStep 1467239 = 2200859) B2200859
theorem B11289689 : Blo 1466553 11289689 := bstep (se 2 (by rfl) ⟨4233633, by rfl⟩ : syracuseStep 11289689 = 8467267) B8467267
theorem B2475319 : Blo 1466553 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B3302711 : Blo 1466553 3302711 := bstep (se 1 (by rfl) ⟨2477033, by rfl⟩ : syracuseStep 3302711 = 4954067) B4954067
theorem B1467711 : Blo 1466553 1467711 := bstep (se 1 (by rfl) ⟨1100783, by rfl⟩ : syracuseStep 1467711 = 2201567) B2201567
theorem B3302783 : Blo 1466553 3302783 := bstep (se 1 (by rfl) ⟨2477087, by rfl⟩ : syracuseStep 3302783 = 4954175) B4954175
theorem B1468007 : Blo 1466553 1468007 := bstep (se 1 (by rfl) ⟨1101005, by rfl⟩ : syracuseStep 1468007 = 2202011) B2202011
theorem B2975401 : Blo 1466553 2975401 := bstep (se 2 (by rfl) ⟨1115775, by rfl⟩ : syracuseStep 2975401 = 2231551) B2231551
theorem B1468271 : Blo 1466553 1468271 := bstep (se 1 (by rfl) ⟨1101203, by rfl⟩ : syracuseStep 1468271 = 2202407) B2202407
theorem B7432073 : Blo 1466553 7432073 := bstep (se 2 (by rfl) ⟨2787027, by rfl⟩ : syracuseStep 7432073 = 5574055) B5574055
theorem B321505199 : Blo 1466553 321505199 := bstep (se 1 (by rfl) ⟨241128899, by rfl⟩ : syracuseStep 321505199 = 482257799) B482257799
theorem B1566811 : Blo 1466553 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B3303647 : Blo 1466553 3303647 := bstep (se 1 (by rfl) ⟨2477735, by rfl⟩ : syracuseStep 3303647 = 4955471) B4955471
theorem B4950665 : Blo 1466553 4950665 := bstep (se 2 (by rfl) ⟨1856499, by rfl⟩ : syracuseStep 4950665 = 3712999) B3712999
theorem B3304097 : Blo 1466553 3304097 := bstep (se 2 (by rfl) ⟨1239036, by rfl⟩ : syracuseStep 3304097 = 2478073) B2478073
theorem B6270061 : Blo 1466553 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B3714407 : Blo 1466553 3714407 := bstep (se 1 (by rfl) ⟨2785805, by rfl⟩ : syracuseStep 3714407 = 5571611) B5571611
theorem B3714943 : Blo 1466553 3714943 := bstep (se 1 (by rfl) ⟨2786207, by rfl⟩ : syracuseStep 3714943 = 5572415) B5572415
theorem B5574527 : Blo 1466553 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B7426079 : Blo 1466553 7426079 := bstep (se 1 (by rfl) ⟨5569559, by rfl⟩ : syracuseStep 7426079 = 11139119) B11139119
theorem B20369785 : Blo 1466553 20369785 := bstep (se 2 (by rfl) ⟨7638669, by rfl⟩ : syracuseStep 20369785 = 15277339) B15277339
theorem B2200223 : Blo 1466553 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B3715753 : Blo 1466553 3715753 := bstep (se 2 (by rfl) ⟨1393407, by rfl⟩ : syracuseStep 3715753 = 2786815) B2786815
theorem B1856191 : Blo 1466553 1856191 := bstep (se 1 (by rfl) ⟨1392143, by rfl⟩ : syracuseStep 1856191 = 2784287) B2784287
theorem B5018431 : Blo 1466553 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B7148411 : Blo 1466553 7148411 := bstep (se 1 (by rfl) ⟨5361308, by rfl⟩ : syracuseStep 7148411 = 10722617) B10722617
theorem B2200667 : Blo 1466553 2200667 := bstep (se 1 (by rfl) ⟨1650500, by rfl⟩ : syracuseStep 2200667 = 3301001) B3301001
theorem B82523279 : Blo 1466553 82523279 := bstep (se 1 (by rfl) ⟨61892459, by rfl⟩ : syracuseStep 82523279 = 123784919) B123784919
theorem B7427375 : Blo 1466553 7427375 := bstep (se 1 (by rfl) ⟨5570531, by rfl⟩ : syracuseStep 7427375 = 11141063) B11141063
theorem B103044545 : Blo 1466553 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B7427699 : Blo 1466553 7427699 := bstep (se 1 (by rfl) ⟨5570774, by rfl⟩ : syracuseStep 7427699 = 11141549) B11141549
theorem B16717427 : Blo 1466553 16717427 := bstep (se 1 (by rfl) ⟨12538070, by rfl⟩ : syracuseStep 16717427 = 25076141) B25076141
theorem B14096105 : Blo 1466553 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B107157329 : Blo 1466553 107157329 := bstep (se 2 (by rfl) ⟨40183998, by rfl⟩ : syracuseStep 107157329 = 80367997) B80367997
theorem B2201579 : Blo 1466553 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B2201627 : Blo 1466553 2201627 := bstep (se 1 (by rfl) ⟨1651220, by rfl⟩ : syracuseStep 2201627 = 3302441) B3302441
theorem B7428509 : Blo 1466553 7428509 := bstep (se 3 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 7428509 = 2785691) B2785691
theorem B7248323 : Blo 1466553 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B13384349 : Blo 1466553 13384349 := bstep (se 3 (by rfl) ⟨2509565, by rfl⟩ : syracuseStep 13384349 = 5019131) B5019131
theorem B12532603 : Blo 1466553 12532603 := bstep (se 1 (by rfl) ⟨9399452, by rfl⟩ : syracuseStep 12532603 = 18798905) B18798905
theorem B3300263 : Blo 1466553 3300263 := bstep (se 1 (by rfl) ⟨2475197, by rfl⟩ : syracuseStep 3300263 = 4950395) B4950395
theorem B2784233 : Blo 1466553 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B3301019 : Blo 1466553 3301019 := bstep (se 1 (by rfl) ⟨2475764, by rfl⟩ : syracuseStep 3301019 = 4951529) B4951529
theorem B4177615 : Blo 1466553 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B1883903 : Blo 1466553 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B7053281 : Blo 1466553 7053281 := bstep (se 2 (by rfl) ⟨2644980, by rfl⟩ : syracuseStep 7053281 = 5289961) B5289961
theorem B2089081 : Blo 1466553 2089081 := bstep (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) B1566811
theorem B1466815 : Blo 1466553 1466815 := bstep (se 1 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 1466815 = 2200223) B2200223
theorem B3572207 : Blo 1466553 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B1467111 : Blo 1466553 1467111 := bstep (se 1 (by rfl) ⟨1100333, by rfl⟩ : syracuseStep 1467111 = 2200667) B2200667
theorem B2474921 : Blo 1466553 2474921 := bstep (se 2 (by rfl) ⟨928095, by rfl⟩ : syracuseStep 2474921 = 1856191) B1856191
theorem B9397403 : Blo 1466553 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B214336799 : Blo 1466553 214336799 := bstep (se 1 (by rfl) ⟨160752599, by rfl⟩ : syracuseStep 214336799 = 321505199) B321505199
theorem B1467719 : Blo 1466553 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B1467751 : Blo 1466553 1467751 := bstep (se 1 (by rfl) ⟨1100813, by rfl⟩ : syracuseStep 1467751 = 2201627) B2201627
theorem B54265565 : Blo 1466553 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B8922899 : Blo 1466553 8922899 := bstep (se 1 (by rfl) ⟨6692174, by rfl⟩ : syracuseStep 8922899 = 13384349) B13384349
theorem B5023741 : Blo 1466553 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B3967201 : Blo 1466553 3967201 := bstep (se 2 (by rfl) ⟨1487700, by rfl⟩ : syracuseStep 3967201 = 2975401) B2975401
theorem B2476271 : Blo 1466553 2476271 := bstep (se 1 (by rfl) ⟨1857203, by rfl⟩ : syracuseStep 2476271 = 3714407) B3714407
theorem B7424621 : Blo 1466553 7424621 := bstep (se 3 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 7424621 = 2784233) B2784233
theorem B4950719 : Blo 1466553 4950719 := bstep (se 1 (by rfl) ⟨3713039, by rfl⟩ : syracuseStep 4950719 = 7426079) B7426079
theorem B27159713 : Blo 1466553 27159713 := bstep (se 2 (by rfl) ⟨10184892, by rfl⟩ : syracuseStep 27159713 = 20369785) B20369785
theorem B4951583 : Blo 1466553 4951583 := bstep (se 1 (by rfl) ⟨3713687, by rfl⟩ : syracuseStep 4951583 = 7427375) B7427375
theorem B4951799 : Blo 1466553 4951799 := bstep (se 1 (by rfl) ⟨3713849, by rfl⟩ : syracuseStep 4951799 = 7427699) B7427699
theorem B11144951 : Blo 1466553 11144951 := bstep (se 1 (by rfl) ⟨8358713, by rfl⟩ : syracuseStep 11144951 = 16717427) B16717427
theorem B19328861 : Blo 1466553 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B71438219 : Blo 1466553 71438219 := bstep (se 1 (by rfl) ⟨53578664, by rfl⟩ : syracuseStep 71438219 = 107157329) B107157329
theorem B8360081 : Blo 1466553 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B4952339 : Blo 1466553 4952339 := bstep (se 1 (by rfl) ⟨3714254, by rfl⟩ : syracuseStep 4952339 = 7428509) B7428509
theorem B2200175 : Blo 1466553 2200175 := bstep (se 1 (by rfl) ⟨1650131, by rfl⟩ : syracuseStep 2200175 = 3300263) B3300263
theorem B2200679 : Blo 1466553 2200679 := bstep (se 1 (by rfl) ⟨1650509, by rfl⟩ : syracuseStep 2200679 = 3301019) B3301019
theorem B4953257 : Blo 1466553 4953257 := bstep (se 2 (by rfl) ⟨1857471, by rfl⟩ : syracuseStep 4953257 = 3714943) B3714943
theorem B3716351 : Blo 1466553 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B2201279 : Blo 1466553 2201279 := bstep (se 1 (by rfl) ⟨1650959, by rfl⟩ : syracuseStep 2201279 = 3301919) B3301919
theorem B2201327 : Blo 1466553 2201327 := bstep (se 1 (by rfl) ⟨1650995, by rfl⟩ : syracuseStep 2201327 = 3301991) B3301991
theorem B4953959 : Blo 1466553 4953959 := bstep (se 1 (by rfl) ⟨3715469, by rfl⟩ : syracuseStep 4953959 = 7430939) B7430939
theorem B4765607 : Blo 1466553 4765607 := bstep (se 1 (by rfl) ⟨3574205, by rfl⟩ : syracuseStep 4765607 = 7148411) B7148411
theorem B7526459 : Blo 1466553 7526459 := bstep (se 1 (by rfl) ⟨5644844, by rfl⟩ : syracuseStep 7526459 = 11289689) B11289689
theorem B55015519 : Blo 1466553 55015519 := bstep (se 1 (by rfl) ⟨41261639, by rfl⟩ : syracuseStep 55015519 = 82523279) B82523279
theorem B2201807 : Blo 1466553 2201807 := bstep (se 1 (by rfl) ⟨1651355, by rfl⟩ : syracuseStep 2201807 = 3302711) B3302711
theorem B4954337 : Blo 1466553 4954337 := bstep (se 2 (by rfl) ⟨1857876, by rfl⟩ : syracuseStep 4954337 = 3715753) B3715753
theorem B2201855 : Blo 1466553 2201855 := bstep (se 1 (by rfl) ⟨1651391, by rfl⟩ : syracuseStep 2201855 = 3302783) B3302783
theorem B68696363 : Blo 1466553 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B6691241 : Blo 1466553 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B16710137 : Blo 1466553 16710137 := bstep (se 2 (by rfl) ⟨6266301, by rfl⟩ : syracuseStep 16710137 = 12532603) B12532603
theorem B4954715 : Blo 1466553 4954715 := bstep (se 1 (by rfl) ⟨3716036, by rfl⟩ : syracuseStep 4954715 = 7432073) B7432073
theorem B2202431 : Blo 1466553 2202431 := bstep (se 1 (by rfl) ⟨1651823, by rfl⟩ : syracuseStep 2202431 = 3303647) B3303647
theorem B3300425 : Blo 1466553 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B3300443 : Blo 1466553 3300443 := bstep (se 1 (by rfl) ⟨2475332, by rfl⟩ : syracuseStep 3300443 = 4950665) B4950665
theorem B2202731 : Blo 1466553 2202731 := bstep (se 1 (by rfl) ⟨1652048, by rfl⟩ : syracuseStep 2202731 = 3304097) B3304097
theorem B5570153 : Blo 1466553 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B4702187 : Blo 1466553 4702187 := bstep (se 1 (by rfl) ⟨3526640, by rfl⟩ : syracuseStep 4702187 = 7053281) B7053281
theorem B2785441 : Blo 1466553 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B3301559 : Blo 1466553 3301559 := bstep (se 1 (by rfl) ⟨2476169, by rfl⟩ : syracuseStep 3301559 = 4952339) B4952339
theorem B1466783 : Blo 1466553 1466783 := bstep (se 1 (by rfl) ⟨1100087, by rfl⟩ : syracuseStep 1466783 = 2200175) B2200175
theorem B1467119 : Blo 1466553 1467119 := bstep (se 1 (by rfl) ⟨1100339, by rfl⟩ : syracuseStep 1467119 = 2200679) B2200679
theorem B3302171 : Blo 1466553 3302171 := bstep (se 1 (by rfl) ⟨2476628, by rfl⟩ : syracuseStep 3302171 = 4953257) B4953257
theorem B1467519 : Blo 1466553 1467519 := bstep (se 1 (by rfl) ⟨1100639, by rfl⟩ : syracuseStep 1467519 = 2201279) B2201279
theorem B36177043 : Blo 1466553 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B1467551 : Blo 1466553 1467551 := bstep (se 1 (by rfl) ⟨1100663, by rfl⟩ : syracuseStep 1467551 = 2201327) B2201327
theorem B5948599 : Blo 1466553 5948599 := bstep (se 1 (by rfl) ⟨4461449, by rfl⟩ : syracuseStep 5948599 = 8922899) B8922899
theorem B3302639 : Blo 1466553 3302639 := bstep (se 1 (by rfl) ⟨2476979, by rfl⟩ : syracuseStep 3302639 = 4953959) B4953959
theorem B1467871 : Blo 1466553 1467871 := bstep (se 1 (by rfl) ⟨1100903, by rfl⟩ : syracuseStep 1467871 = 2201807) B2201807
theorem B3302891 : Blo 1466553 3302891 := bstep (se 1 (by rfl) ⟨2477168, by rfl⟩ : syracuseStep 3302891 = 4954337) B4954337
theorem B1467903 : Blo 1466553 1467903 := bstep (se 1 (by rfl) ⟨1100927, by rfl⟩ : syracuseStep 1467903 = 2201855) B2201855
theorem B3303143 : Blo 1466553 3303143 := bstep (se 1 (by rfl) ⟨2477357, by rfl⟩ : syracuseStep 3303143 = 4954715) B4954715
theorem B4949747 : Blo 1466553 4949747 := bstep (se 1 (by rfl) ⟨3712310, by rfl⟩ : syracuseStep 4949747 = 7424621) B7424621
theorem B1468287 : Blo 1466553 1468287 := bstep (se 1 (by rfl) ⟨1101215, by rfl⟩ : syracuseStep 1468287 = 2202431) B2202431
theorem B1468487 : Blo 1466553 1468487 := bstep (se 1 (by rfl) ⟨1101365, by rfl⟩ : syracuseStep 1468487 = 2202731) B2202731
theorem B18106475 : Blo 1466553 18106475 := bstep (se 1 (by rfl) ⟨13579856, by rfl⟩ : syracuseStep 18106475 = 27159713) B27159713
theorem B3713435 : Blo 1466553 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B5573387 : Blo 1466553 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B73354025 : Blo 1466553 73354025 := bstep (se 2 (by rfl) ⟨27507759, by rfl⟩ : syracuseStep 73354025 = 55015519) B55015519
theorem B1649947 : Blo 1466553 1649947 := bstep (se 1 (by rfl) ⟨1237460, by rfl⟩ : syracuseStep 1649947 = 2474921) B2474921
theorem B2477567 : Blo 1466553 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B5017639 : Blo 1466553 5017639 := bstep (se 1 (by rfl) ⟨3763229, by rfl⟩ : syracuseStep 5017639 = 7526459) B7526459
theorem B1650847 : Blo 1466553 1650847 := bstep (se 1 (by rfl) ⟨1238135, by rfl⟩ : syracuseStep 1650847 = 2476271) B2476271
theorem B45797575 : Blo 1466553 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B4460827 : Blo 1466553 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B2200283 : Blo 1466553 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B2200295 : Blo 1466553 2200295 := bstep (se 1 (by rfl) ⟨1650221, by rfl⟩ : syracuseStep 2200295 = 3300443) B3300443
theorem B47625479 : Blo 1466553 47625479 := bstep (se 1 (by rfl) ⟨35719109, by rfl⟩ : syracuseStep 47625479 = 71438219) B71438219
theorem B3134791 : Blo 1466553 3134791 := bstep (se 1 (by rfl) ⟨2351093, by rfl⟩ : syracuseStep 3134791 = 4702187) B4702187
theorem B6698321 : Blo 1466553 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B2381471 : Blo 1466553 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B6264935 : Blo 1466553 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B142891199 : Blo 1466553 142891199 := bstep (se 1 (by rfl) ⟨107168399, by rfl⟩ : syracuseStep 142891199 = 214336799) B214336799
theorem B21158405 : Blo 1466553 21158405 := bstep (se 4 (by rfl) ⟨1983600, by rfl⟩ : syracuseStep 21158405 = 3967201) B3967201
theorem B3177071 : Blo 1466553 3177071 := bstep (se 1 (by rfl) ⟨2382803, by rfl⟩ : syracuseStep 3177071 = 4765607) B4765607
theorem B11140091 : Blo 1466553 11140091 := bstep (se 1 (by rfl) ⟨8355068, by rfl⟩ : syracuseStep 11140091 = 16710137) B16710137
theorem B3300479 : Blo 1466553 3300479 := bstep (se 1 (by rfl) ⟨2475359, by rfl⟩ : syracuseStep 3300479 = 4950719) B4950719
theorem B3301055 : Blo 1466553 3301055 := bstep (se 1 (by rfl) ⟨2475791, by rfl⟩ : syracuseStep 3301055 = 4951583) B4951583
theorem B3301199 : Blo 1466553 3301199 := bstep (se 1 (by rfl) ⟨2475899, by rfl⟩ : syracuseStep 3301199 = 4951799) B4951799
theorem B7429967 : Blo 1466553 7429967 := bstep (se 1 (by rfl) ⟨5572475, by rfl⟩ : syracuseStep 7429967 = 11144951) B11144951
theorem B12885907 : Blo 1466553 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B61063433 : Blo 1466553 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B48283933 : Blo 1466553 48283933 := bstep (se 3 (by rfl) ⟨9053237, by rfl⟩ : syracuseStep 48283933 = 18106475) B18106475
theorem B5947769 : Blo 1466553 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B1466855 : Blo 1466553 1466855 := bstep (se 1 (by rfl) ⟨1100141, by rfl⟩ : syracuseStep 1466855 = 2200283) B2200283
theorem B1466863 : Blo 1466553 1466863 := bstep (se 1 (by rfl) ⟨1100147, by rfl⟩ : syracuseStep 1466863 = 2200295) B2200295
theorem B4465547 : Blo 1466553 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B48236057 : Blo 1466553 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B7931465 : Blo 1466553 7931465 := bstep (se 2 (by rfl) ⟨2974299, by rfl⟩ : syracuseStep 7931465 = 5948599) B5948599
theorem B2475623 : Blo 1466553 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B195610733 : Blo 1466553 195610733 := bstep (se 3 (by rfl) ⟨36677012, by rfl⟩ : syracuseStep 195610733 = 73354025) B73354025
theorem B17181209 : Blo 1466553 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B3713921 : Blo 1466553 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B95260799 : Blo 1466553 95260799 := bstep (se 1 (by rfl) ⟨71445599, by rfl⟩ : syracuseStep 95260799 = 142891199) B142891199
theorem B2199929 : Blo 1466553 2199929 := bstep (se 2 (by rfl) ⟨824973, by rfl⟩ : syracuseStep 2199929 = 1649947) B1649947
theorem B2118047 : Blo 1466553 2118047 := bstep (se 1 (by rfl) ⟨1588535, by rfl⟩ : syracuseStep 2118047 = 3177071) B3177071
theorem B3715591 : Blo 1466553 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B7426727 : Blo 1466553 7426727 := bstep (se 1 (by rfl) ⟨5570045, by rfl⟩ : syracuseStep 7426727 = 11140091) B11140091
theorem B2200319 : Blo 1466553 2200319 := bstep (se 1 (by rfl) ⟨1650239, by rfl⟩ : syracuseStep 2200319 = 3300479) B3300479
theorem B1651711 : Blo 1466553 1651711 := bstep (se 1 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 1651711 = 2477567) B2477567
theorem B2200703 : Blo 1466553 2200703 := bstep (se 1 (by rfl) ⟨1650527, by rfl⟩ : syracuseStep 2200703 = 3301055) B3301055
theorem B2200799 : Blo 1466553 2200799 := bstep (se 1 (by rfl) ⟨1650599, by rfl⟩ : syracuseStep 2200799 = 3301199) B3301199
theorem B4953311 : Blo 1466553 4953311 := bstep (se 1 (by rfl) ⟨3714983, by rfl⟩ : syracuseStep 4953311 = 7429967) B7429967
theorem B6690185 : Blo 1466553 6690185 := bstep (se 2 (by rfl) ⟨2508819, by rfl⟩ : syracuseStep 6690185 = 5017639) B5017639
theorem B2201039 : Blo 1466553 2201039 := bstep (se 1 (by rfl) ⟨1650779, by rfl⟩ : syracuseStep 2201039 = 3301559) B3301559
theorem B2201129 : Blo 1466553 2201129 := bstep (se 2 (by rfl) ⟨825423, by rfl⟩ : syracuseStep 2201129 = 1650847) B1650847
theorem B2201447 : Blo 1466553 2201447 := bstep (se 1 (by rfl) ⟨1651085, by rfl⟩ : syracuseStep 2201447 = 3302171) B3302171
theorem B2201759 : Blo 1466553 2201759 := bstep (se 1 (by rfl) ⟨1651319, by rfl⟩ : syracuseStep 2201759 = 3302639) B3302639
theorem B31750319 : Blo 1466553 31750319 := bstep (se 1 (by rfl) ⟨23812739, by rfl⟩ : syracuseStep 31750319 = 47625479) B47625479
theorem B2201927 : Blo 1466553 2201927 := bstep (se 1 (by rfl) ⟨1651445, by rfl⟩ : syracuseStep 2201927 = 3302891) B3302891
theorem B1587647 : Blo 1466553 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B2202095 : Blo 1466553 2202095 := bstep (se 1 (by rfl) ⟨1651571, by rfl⟩ : syracuseStep 2202095 = 3303143) B3303143
theorem B3299831 : Blo 1466553 3299831 := bstep (se 1 (by rfl) ⟨2474873, by rfl⟩ : syracuseStep 3299831 = 4949747) B4949747
theorem B4176623 : Blo 1466553 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B14105603 : Blo 1466553 14105603 := bstep (se 1 (by rfl) ⟨10579202, by rfl⟩ : syracuseStep 14105603 = 21158405) B21158405
theorem B16718885 : Blo 1466553 16718885 := bstep (se 4 (by rfl) ⟨1567395, by rfl⟩ : syracuseStep 16718885 = 3134791) B3134791
theorem B1466619 : Blo 1466553 1466619 := bstep (se 1 (by rfl) ⟨1099964, by rfl⟩ : syracuseStep 1466619 = 2199929) B2199929
theorem B1466879 : Blo 1466553 1466879 := bstep (se 1 (by rfl) ⟨1100159, by rfl⟩ : syracuseStep 1466879 = 2200319) B2200319
theorem B1467135 : Blo 1466553 1467135 := bstep (se 1 (by rfl) ⟨1100351, by rfl⟩ : syracuseStep 1467135 = 2200703) B2200703
theorem B1467199 : Blo 1466553 1467199 := bstep (se 1 (by rfl) ⟨1100399, by rfl⟩ : syracuseStep 1467199 = 2200799) B2200799
theorem B3302207 : Blo 1466553 3302207 := bstep (se 1 (by rfl) ⟨2476655, by rfl⟩ : syracuseStep 3302207 = 4953311) B4953311
theorem B1467359 : Blo 1466553 1467359 := bstep (se 1 (by rfl) ⟨1100519, by rfl⟩ : syracuseStep 1467359 = 2201039) B2201039
theorem B15860717 : Blo 1466553 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B1467419 : Blo 1466553 1467419 := bstep (se 1 (by rfl) ⟨1100564, by rfl⟩ : syracuseStep 1467419 = 2201129) B2201129
theorem B1467631 : Blo 1466553 1467631 := bstep (se 1 (by rfl) ⟨1100723, by rfl⟩ : syracuseStep 1467631 = 2201447) B2201447
theorem B1467839 : Blo 1466553 1467839 := bstep (se 1 (by rfl) ⟨1100879, by rfl⟩ : syracuseStep 1467839 = 2201759) B2201759
theorem B1467951 : Blo 1466553 1467951 := bstep (se 1 (by rfl) ⟨1100963, by rfl⟩ : syracuseStep 1467951 = 2201927) B2201927
theorem B1468063 : Blo 1466553 1468063 := bstep (se 1 (by rfl) ⟨1101047, by rfl⟩ : syracuseStep 1468063 = 2202095) B2202095
theorem B11454139 : Blo 1466553 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B2475947 : Blo 1466553 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B63507199 : Blo 1466553 63507199 := bstep (se 1 (by rfl) ⟨47630399, by rfl⟩ : syracuseStep 63507199 = 95260799) B95260799
theorem B40708955 : Blo 1466553 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B4951151 : Blo 1466553 4951151 := bstep (se 1 (by rfl) ⟨3713363, by rfl⟩ : syracuseStep 4951151 = 7426727) B7426727
theorem B2977031 : Blo 1466553 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B4460123 : Blo 1466553 4460123 := bstep (se 1 (by rfl) ⟨3345092, by rfl⟩ : syracuseStep 4460123 = 6690185) B6690185
theorem B32157371 : Blo 1466553 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B5287643 : Blo 1466553 5287643 := bstep (se 1 (by rfl) ⟨3965732, by rfl⟩ : syracuseStep 5287643 = 7931465) B7931465
theorem B1650415 : Blo 1466553 1650415 := bstep (se 1 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 1650415 = 2475623) B2475623
theorem B5648125 : Blo 1466553 5648125 := bstep (se 3 (by rfl) ⟨1059023, by rfl⟩ : syracuseStep 5648125 = 2118047) B2118047
theorem B2199887 : Blo 1466553 2199887 := bstep (se 1 (by rfl) ⟨1649915, by rfl⟩ : syracuseStep 2199887 = 3299831) B3299831
theorem B11137661 : Blo 1466553 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B11145923 : Blo 1466553 11145923 := bstep (se 1 (by rfl) ⟨8359442, by rfl⟩ : syracuseStep 11145923 = 16718885) B16718885
theorem B64378577 : Blo 1466553 64378577 := bstep (se 2 (by rfl) ⟨24141966, by rfl⟩ : syracuseStep 64378577 = 48283933) B48283933
theorem B4954121 : Blo 1466553 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B4233725 : Blo 1466553 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B2202281 : Blo 1466553 2202281 := bstep (se 2 (by rfl) ⟨825855, by rfl⟩ : syracuseStep 2202281 = 1651711) B1651711
theorem B130407155 : Blo 1466553 130407155 := bstep (se 1 (by rfl) ⟨97805366, by rfl⟩ : syracuseStep 130407155 = 195610733) B195610733
theorem B21166879 : Blo 1466553 21166879 := bstep (se 1 (by rfl) ⟨15875159, by rfl⟩ : syracuseStep 21166879 = 31750319) B31750319
theorem B9403735 : Blo 1466553 9403735 := bstep (se 1 (by rfl) ⟨7052801, by rfl⟩ : syracuseStep 9403735 = 14105603) B14105603
theorem B1466591 : Blo 1466553 1466591 := bstep (se 1 (by rfl) ⟨1099943, by rfl⟩ : syracuseStep 1466591 = 2199887) B2199887
theorem B7430615 : Blo 1466553 7430615 := bstep (se 1 (by rfl) ⟨5572961, by rfl⟩ : syracuseStep 7430615 = 11145923) B11145923
theorem B7938749 : Blo 1466553 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B28222505 : Blo 1466553 28222505 := bstep (se 2 (by rfl) ⟨10583439, by rfl⟩ : syracuseStep 28222505 = 21166879) B21166879
theorem B3302747 : Blo 1466553 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B1468187 : Blo 1466553 1468187 := bstep (se 1 (by rfl) ⟨1101140, by rfl⟩ : syracuseStep 1468187 = 2202281) B2202281
theorem B15272185 : Blo 1466553 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B7530833 : Blo 1466553 7530833 := bstep (se 2 (by rfl) ⟨2824062, by rfl⟩ : syracuseStep 7530833 = 5648125) B5648125
theorem B3525095 : Blo 1466553 3525095 := bstep (se 1 (by rfl) ⟨2643821, by rfl⟩ : syracuseStep 3525095 = 5287643) B5287643
theorem B7425107 : Blo 1466553 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B84676265 : Blo 1466553 84676265 := bstep (se 2 (by rfl) ⟨31753599, by rfl⟩ : syracuseStep 84676265 = 63507199) B63507199
theorem B1650631 : Blo 1466553 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B2822483 : Blo 1466553 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B12538313 : Blo 1466553 12538313 := bstep (se 2 (by rfl) ⟨4701867, by rfl⟩ : syracuseStep 12538313 = 9403735) B9403735
theorem B86938103 : Blo 1466553 86938103 := bstep (se 1 (by rfl) ⟨65203577, by rfl⟩ : syracuseStep 86938103 = 130407155) B130407155
theorem B171676205 : Blo 1466553 171676205 := bstep (se 3 (by rfl) ⟨32189288, by rfl⟩ : syracuseStep 171676205 = 64378577) B64378577
theorem B2200553 : Blo 1466553 2200553 := bstep (se 2 (by rfl) ⟨825207, by rfl⟩ : syracuseStep 2200553 = 1650415) B1650415
theorem B2201471 : Blo 1466553 2201471 := bstep (se 1 (by rfl) ⟨1651103, by rfl⟩ : syracuseStep 2201471 = 3302207) B3302207
theorem B10573811 : Blo 1466553 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B85752989 : Blo 1466553 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B27139303 : Blo 1466553 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B3300767 : Blo 1466553 3300767 := bstep (se 1 (by rfl) ⟨2475575, by rfl⟩ : syracuseStep 3300767 = 4951151) B4951151
theorem B2973415 : Blo 1466553 2973415 := bstep (se 1 (by rfl) ⟨2230061, by rfl⟩ : syracuseStep 2973415 = 4460123) B4460123
theorem B57958735 : Blo 1466553 57958735 := bstep (se 1 (by rfl) ⟨43469051, by rfl⟩ : syracuseStep 57958735 = 86938103) B86938103
theorem B114450803 : Blo 1466553 114450803 := bstep (se 1 (by rfl) ⟨85838102, by rfl⟩ : syracuseStep 114450803 = 171676205) B171676205
theorem B5292499 : Blo 1466553 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B1467035 : Blo 1466553 1467035 := bstep (se 1 (by rfl) ⟨1100276, by rfl⟩ : syracuseStep 1467035 = 2200553) B2200553
theorem B1467647 : Blo 1466553 1467647 := bstep (se 1 (by rfl) ⟨1100735, by rfl⟩ : syracuseStep 1467647 = 2201471) B2201471
theorem B36185737 : Blo 1466553 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B4950071 : Blo 1466553 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B8358875 : Blo 1466553 8358875 := bstep (se 1 (by rfl) ⟨6269156, by rfl⟩ : syracuseStep 8358875 = 12538313) B12538313
theorem B7049207 : Blo 1466553 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B57168659 : Blo 1466553 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B2200511 : Blo 1466553 2200511 := bstep (se 1 (by rfl) ⟨1650383, by rfl⟩ : syracuseStep 2200511 = 3300767) B3300767
theorem B2200841 : Blo 1466553 2200841 := bstep (se 2 (by rfl) ⟨825315, by rfl⟩ : syracuseStep 2200841 = 1650631) B1650631
theorem B4953743 : Blo 1466553 4953743 := bstep (se 1 (by rfl) ⟨3715307, by rfl⟩ : syracuseStep 4953743 = 7430615) B7430615
theorem B20362913 : Blo 1466553 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B18815003 : Blo 1466553 18815003 := bstep (se 1 (by rfl) ⟨14111252, by rfl⟩ : syracuseStep 18815003 = 28222505) B28222505
theorem B7526621 : Blo 1466553 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B2201831 : Blo 1466553 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B5020555 : Blo 1466553 5020555 := bstep (se 1 (by rfl) ⟨3765416, by rfl⟩ : syracuseStep 5020555 = 7530833) B7530833
theorem B2350063 : Blo 1466553 2350063 := bstep (se 1 (by rfl) ⟨1762547, by rfl⟩ : syracuseStep 2350063 = 3525095) B3525095
theorem B3964553 : Blo 1466553 3964553 := bstep (se 2 (by rfl) ⟨1486707, by rfl⟩ : syracuseStep 3964553 = 2973415) B2973415
theorem B56450843 : Blo 1466553 56450843 := bstep (se 1 (by rfl) ⟨42338132, by rfl⟩ : syracuseStep 56450843 = 84676265) B84676265
theorem B76300535 : Blo 1466553 76300535 := bstep (se 1 (by rfl) ⟨57225401, by rfl⟩ : syracuseStep 76300535 = 114450803) B114450803
theorem B20070989 : Blo 1466553 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B1467007 : Blo 1466553 1467007 := bstep (se 1 (by rfl) ⟨1100255, by rfl⟩ : syracuseStep 1467007 = 2200511) B2200511
theorem B1467227 : Blo 1466553 1467227 := bstep (se 1 (by rfl) ⟨1100420, by rfl⟩ : syracuseStep 1467227 = 2200841) B2200841
theorem B3302495 : Blo 1466553 3302495 := bstep (se 1 (by rfl) ⟨2476871, by rfl⟩ : syracuseStep 3302495 = 4953743) B4953743
theorem B13575275 : Blo 1466553 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B6694073 : Blo 1466553 6694073 := bstep (se 2 (by rfl) ⟨2510277, by rfl⟩ : syracuseStep 6694073 = 5020555) B5020555
theorem B12543335 : Blo 1466553 12543335 := bstep (se 1 (by rfl) ⟨9407501, by rfl⟩ : syracuseStep 12543335 = 18815003) B18815003
theorem B1467887 : Blo 1466553 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B5572583 : Blo 1466553 5572583 := bstep (se 1 (by rfl) ⟨4179437, by rfl⟩ : syracuseStep 5572583 = 8358875) B8358875
theorem B77278313 : Blo 1466553 77278313 := bstep (se 2 (by rfl) ⟨28979367, by rfl⟩ : syracuseStep 77278313 = 57958735) B57958735
theorem B38112439 : Blo 1466553 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B7056665 : Blo 1466553 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B3133417 : Blo 1466553 3133417 := bstep (se 2 (by rfl) ⟨1175031, by rfl⟩ : syracuseStep 3133417 = 2350063) B2350063
theorem B48247649 : Blo 1466553 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B2643035 : Blo 1466553 2643035 := bstep (se 1 (by rfl) ⟨1982276, by rfl⟩ : syracuseStep 2643035 = 3964553) B3964553
theorem B4699471 : Blo 1466553 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B3300047 : Blo 1466553 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B37633895 : Blo 1466553 37633895 := bstep (se 1 (by rfl) ⟨28225421, by rfl⟩ : syracuseStep 37633895 = 56450843) B56450843
theorem B50816585 : Blo 1466553 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B4704443 : Blo 1466553 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B50867023 : Blo 1466553 50867023 := bstep (se 1 (by rfl) ⟨38150267, by rfl⟩ : syracuseStep 50867023 = 76300535) B76300535
theorem B7048093 : Blo 1466553 7048093 := bstep (se 3 (by rfl) ⟨1321517, by rfl⟩ : syracuseStep 7048093 = 2643035) B2643035
theorem B13380659 : Blo 1466553 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B32165099 : Blo 1466553 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B3715055 : Blo 1466553 3715055 := bstep (se 1 (by rfl) ⟨2786291, by rfl⟩ : syracuseStep 3715055 = 5572583) B5572583
theorem B2200031 : Blo 1466553 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B25089263 : Blo 1466553 25089263 := bstep (se 1 (by rfl) ⟨18816947, by rfl⟩ : syracuseStep 25089263 = 37633895) B37633895
theorem B2201663 : Blo 1466553 2201663 := bstep (se 1 (by rfl) ⟨1651247, by rfl⟩ : syracuseStep 2201663 = 3302495) B3302495
theorem B9050183 : Blo 1466553 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B4462715 : Blo 1466553 4462715 := bstep (se 1 (by rfl) ⟨3347036, by rfl⟩ : syracuseStep 4462715 = 6694073) B6694073
theorem B8362223 : Blo 1466553 8362223 := bstep (se 1 (by rfl) ⟨6271667, by rfl⟩ : syracuseStep 8362223 = 12543335) B12543335
theorem B6265961 : Blo 1466553 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B51518875 : Blo 1466553 51518875 := bstep (se 1 (by rfl) ⟨38639156, by rfl⟩ : syracuseStep 51518875 = 77278313) B77278313
theorem B4177889 : Blo 1466553 4177889 := bstep (se 2 (by rfl) ⟨1566708, by rfl⟩ : syracuseStep 4177889 = 3133417) B3133417
theorem B1466687 : Blo 1466553 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B67822697 : Blo 1466553 67822697 := bstep (se 2 (by rfl) ⟨25433511, by rfl⟩ : syracuseStep 67822697 = 50867023) B50867023
theorem B9397457 : Blo 1466553 9397457 := bstep (se 2 (by rfl) ⟨3524046, by rfl⟩ : syracuseStep 9397457 = 7048093) B7048093
theorem B1467775 : Blo 1466553 1467775 := bstep (se 1 (by rfl) ⟨1100831, by rfl⟩ : syracuseStep 1467775 = 2201663) B2201663
theorem B2975143 : Blo 1466553 2975143 := bstep (se 1 (by rfl) ⟨2231357, by rfl⟩ : syracuseStep 2975143 = 4462715) B4462715
theorem B68691833 : Blo 1466553 68691833 := bstep (se 2 (by rfl) ⟨25759437, by rfl⟩ : syracuseStep 68691833 = 51518875) B51518875
theorem B2476703 : Blo 1466553 2476703 := bstep (se 1 (by rfl) ⟨1857527, by rfl⟩ : syracuseStep 2476703 = 3715055) B3715055
theorem B6033455 : Blo 1466553 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B5574815 : Blo 1466553 5574815 := bstep (se 1 (by rfl) ⟨4181111, by rfl⟩ : syracuseStep 5574815 = 8362223) B8362223
theorem B21443399 : Blo 1466553 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B16726175 : Blo 1466553 16726175 := bstep (se 1 (by rfl) ⟨12544631, by rfl⟩ : syracuseStep 16726175 = 25089263) B25089263
theorem B3136295 : Blo 1466553 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B135510893 : Blo 1466553 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B8920439 : Blo 1466553 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B4177307 : Blo 1466553 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B2785259 : Blo 1466553 2785259 := bstep (se 1 (by rfl) ⟨2088944, by rfl⟩ : syracuseStep 2785259 = 4177889) B4177889
theorem B4022303 : Blo 1466553 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B14295599 : Blo 1466553 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B45794555 : Blo 1466553 45794555 := bstep (se 1 (by rfl) ⟨34345916, by rfl⟩ : syracuseStep 45794555 = 68691833) B68691833
theorem B11150783 : Blo 1466553 11150783 := bstep (se 1 (by rfl) ⟨8363087, by rfl⟩ : syracuseStep 11150783 = 16726175) B16726175
theorem B2090863 : Blo 1466553 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B3966857 : Blo 1466553 3966857 := bstep (se 2 (by rfl) ⟨1487571, by rfl⟩ : syracuseStep 3966857 = 2975143) B2975143
theorem B1651135 : Blo 1466553 1651135 := bstep (se 1 (by rfl) ⟨1238351, by rfl⟩ : syracuseStep 1651135 = 2476703) B2476703
theorem B1856839 : Blo 1466553 1856839 := bstep (se 1 (by rfl) ⟨1392629, by rfl⟩ : syracuseStep 1856839 = 2785259) B2785259
theorem B3716543 : Blo 1466553 3716543 := bstep (se 1 (by rfl) ⟨2787407, by rfl⟩ : syracuseStep 3716543 = 5574815) B5574815
theorem B180860525 : Blo 1466553 180860525 := bstep (se 3 (by rfl) ⟨33911348, by rfl⟩ : syracuseStep 180860525 = 67822697) B67822697
theorem B6264971 : Blo 1466553 6264971 := bstep (se 1 (by rfl) ⟨4698728, by rfl⟩ : syracuseStep 6264971 = 9397457) B9397457
theorem B90340595 : Blo 1466553 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B5946959 : Blo 1466553 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B2784871 : Blo 1466553 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B2475785 : Blo 1466553 2475785 := bstep (se 2 (by rfl) ⟨928419, by rfl⟩ : syracuseStep 2475785 = 1856839) B1856839
theorem B11151269 : Blo 1466553 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B3713161 : Blo 1466553 3713161 := bstep (se 2 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 3713161 = 2784871) B2784871
theorem B42904565 : Blo 1466553 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B9530399 : Blo 1466553 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B2477695 : Blo 1466553 2477695 := bstep (se 1 (by rfl) ⟨1858271, by rfl⟩ : syracuseStep 2477695 = 3716543) B3716543
theorem B7433855 : Blo 1466553 7433855 := bstep (se 1 (by rfl) ⟨5575391, by rfl⟩ : syracuseStep 7433855 = 11150783) B11150783
theorem B120573683 : Blo 1466553 120573683 := bstep (se 1 (by rfl) ⟨90430262, by rfl⟩ : syracuseStep 120573683 = 180860525) B180860525
theorem B2201513 : Blo 1466553 2201513 := bstep (se 2 (by rfl) ⟨825567, by rfl⟩ : syracuseStep 2201513 = 1651135) B1651135
theorem B30529703 : Blo 1466553 30529703 := bstep (se 1 (by rfl) ⟨22897277, by rfl⟩ : syracuseStep 30529703 = 45794555) B45794555
theorem B2644571 : Blo 1466553 2644571 := bstep (se 1 (by rfl) ⟨1983428, by rfl⟩ : syracuseStep 2644571 = 3966857) B3966857
theorem B4176647 : Blo 1466553 4176647 := bstep (se 1 (by rfl) ⟨3132485, by rfl⟩ : syracuseStep 4176647 = 6264971) B6264971
theorem B60227063 : Blo 1466553 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B3964639 : Blo 1466553 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B81412541 : Blo 1466553 81412541 := bstep (se 3 (by rfl) ⟨15264851, by rfl⟩ : syracuseStep 81412541 = 30529703) B30529703
theorem B1467675 : Blo 1466553 1467675 := bstep (se 1 (by rfl) ⟨1100756, by rfl⟩ : syracuseStep 1467675 = 2201513) B2201513
theorem B1763047 : Blo 1466553 1763047 := bstep (se 1 (by rfl) ⟨1322285, by rfl⟩ : syracuseStep 1763047 = 2644571) B2644571
theorem B3303593 : Blo 1466553 3303593 := bstep (se 2 (by rfl) ⟨1238847, by rfl⟩ : syracuseStep 3303593 = 2477695) B2477695
theorem B5286185 : Blo 1466553 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B40151375 : Blo 1466553 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B80382455 : Blo 1466553 80382455 := bstep (se 1 (by rfl) ⟨60286841, by rfl⟩ : syracuseStep 80382455 = 120573683) B120573683
theorem B25414397 : Blo 1466553 25414397 := bstep (se 3 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 25414397 = 9530399) B9530399
theorem B4950881 : Blo 1466553 4950881 := bstep (se 2 (by rfl) ⟨1856580, by rfl⟩ : syracuseStep 4950881 = 3713161) B3713161
theorem B1650523 : Blo 1466553 1650523 := bstep (se 1 (by rfl) ⟨1237892, by rfl⟩ : syracuseStep 1650523 = 2475785) B2475785
theorem B7434179 : Blo 1466553 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B28603043 : Blo 1466553 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B2784431 : Blo 1466553 2784431 := bstep (se 1 (by rfl) ⟨2088323, by rfl⟩ : syracuseStep 2784431 = 4176647) B4176647
theorem B4955903 : Blo 1466553 4955903 := bstep (se 1 (by rfl) ⟨3716927, by rfl⟩ : syracuseStep 4955903 = 7433855) B7433855
theorem B3524123 : Blo 1466553 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B16942931 : Blo 1466553 16942931 := bstep (se 1 (by rfl) ⟨12707198, by rfl⟩ : syracuseStep 16942931 = 25414397) B25414397
theorem B3303935 : Blo 1466553 3303935 := bstep (se 1 (by rfl) ⟨2477951, by rfl⟩ : syracuseStep 3303935 = 4955903) B4955903
theorem B54275027 : Blo 1466553 54275027 := bstep (se 1 (by rfl) ⟨40706270, by rfl⟩ : syracuseStep 54275027 = 81412541) B81412541
theorem B26767583 : Blo 1466553 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B53588303 : Blo 1466553 53588303 := bstep (se 1 (by rfl) ⟨40191227, by rfl⟩ : syracuseStep 53588303 = 80382455) B80382455
theorem B1856287 : Blo 1466553 1856287 := bstep (se 1 (by rfl) ⟨1392215, by rfl⟩ : syracuseStep 1856287 = 2784431) B2784431
theorem B2200697 : Blo 1466553 2200697 := bstep (se 2 (by rfl) ⟨825261, by rfl⟩ : syracuseStep 2200697 = 1650523) B1650523
theorem B19068695 : Blo 1466553 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B2202395 : Blo 1466553 2202395 := bstep (se 1 (by rfl) ⟨1651796, by rfl⟩ : syracuseStep 2202395 = 3303593) B3303593
theorem B3300587 : Blo 1466553 3300587 := bstep (se 1 (by rfl) ⟨2475440, by rfl⟩ : syracuseStep 3300587 = 4950881) B4950881
theorem B2350729 : Blo 1466553 2350729 := bstep (se 2 (by rfl) ⟨881523, by rfl⟩ : syracuseStep 2350729 = 1763047) B1763047
theorem B4956119 : Blo 1466553 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B35725535 : Blo 1466553 35725535 := bstep (se 1 (by rfl) ⟨26794151, by rfl⟩ : syracuseStep 35725535 = 53588303) B53588303
theorem B1467131 : Blo 1466553 1467131 := bstep (se 1 (by rfl) ⟨1100348, by rfl⟩ : syracuseStep 1467131 = 2200697) B2200697
theorem B2475049 : Blo 1466553 2475049 := bstep (se 2 (by rfl) ⟨928143, by rfl⟩ : syracuseStep 2475049 = 1856287) B1856287
theorem B1468263 : Blo 1466553 1468263 := bstep (se 1 (by rfl) ⟨1101197, by rfl⟩ : syracuseStep 1468263 = 2202395) B2202395
theorem B3304079 : Blo 1466553 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B17845055 : Blo 1466553 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B2200391 : Blo 1466553 2200391 := bstep (se 1 (by rfl) ⟨1650293, by rfl⟩ : syracuseStep 2200391 = 3300587) B3300587
theorem B3134305 : Blo 1466553 3134305 := bstep (se 2 (by rfl) ⟨1175364, by rfl⟩ : syracuseStep 3134305 = 2350729) B2350729
theorem B144733405 : Blo 1466553 144733405 := bstep (se 3 (by rfl) ⟨27137513, by rfl⟩ : syracuseStep 144733405 = 54275027) B54275027
theorem B2349415 : Blo 1466553 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B12712463 : Blo 1466553 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B11295287 : Blo 1466553 11295287 := bstep (se 1 (by rfl) ⟨8471465, by rfl⟩ : syracuseStep 11295287 = 16942931) B16942931
theorem B2202623 : Blo 1466553 2202623 := bstep (se 1 (by rfl) ⟨1651967, by rfl⟩ : syracuseStep 2202623 = 3303935) B3303935
theorem B1466927 : Blo 1466553 1466927 := bstep (se 1 (by rfl) ⟨1100195, by rfl⟩ : syracuseStep 1466927 = 2200391) B2200391
theorem B4179073 : Blo 1466553 4179073 := bstep (se 2 (by rfl) ⟨1567152, by rfl⟩ : syracuseStep 4179073 = 3134305) B3134305
theorem B7530191 : Blo 1466553 7530191 := bstep (se 1 (by rfl) ⟨5647643, by rfl⟩ : syracuseStep 7530191 = 11295287) B11295287
theorem B11896703 : Blo 1466553 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B1468415 : Blo 1466553 1468415 := bstep (se 1 (by rfl) ⟨1101311, by rfl⟩ : syracuseStep 1468415 = 2202623) B2202623
theorem B23817023 : Blo 1466553 23817023 := bstep (se 1 (by rfl) ⟨17862767, by rfl⟩ : syracuseStep 23817023 = 35725535) B35725535
theorem B8474975 : Blo 1466553 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B12530213 : Blo 1466553 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B3300065 : Blo 1466553 3300065 := bstep (se 2 (by rfl) ⟨1237524, by rfl⟩ : syracuseStep 3300065 = 2475049) B2475049
theorem B192977873 : Blo 1466553 192977873 := bstep (se 2 (by rfl) ⟨72366702, by rfl⟩ : syracuseStep 192977873 = 144733405) B144733405
theorem B2202719 : Blo 1466553 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B7931135 : Blo 1466553 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B5572097 : Blo 1466553 5572097 := bstep (se 2 (by rfl) ⟨2089536, by rfl⟩ : syracuseStep 5572097 = 4179073) B4179073
theorem B15878015 : Blo 1466553 15878015 := bstep (se 1 (by rfl) ⟨11908511, by rfl⟩ : syracuseStep 15878015 = 23817023) B23817023
theorem B1468479 : Blo 1466553 1468479 := bstep (se 1 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 1468479 = 2202719) B2202719
theorem B2200043 : Blo 1466553 2200043 := bstep (se 1 (by rfl) ⟨1650032, by rfl⟩ : syracuseStep 2200043 = 3300065) B3300065
theorem B128651915 : Blo 1466553 128651915 := bstep (se 1 (by rfl) ⟨96488936, by rfl⟩ : syracuseStep 128651915 = 192977873) B192977873
theorem B5649983 : Blo 1466553 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B8353475 : Blo 1466553 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B5020127 : Blo 1466553 5020127 := bstep (se 1 (by rfl) ⟨3765095, by rfl⟩ : syracuseStep 5020127 = 7530191) B7530191
theorem B1466695 : Blo 1466553 1466695 := bstep (se 1 (by rfl) ⟨1100021, by rfl⟩ : syracuseStep 1466695 = 2200043) B2200043
theorem B10585343 : Blo 1466553 10585343 := bstep (se 1 (by rfl) ⟨7939007, by rfl⟩ : syracuseStep 10585343 = 15878015) B15878015
theorem B3714731 : Blo 1466553 3714731 := bstep (se 1 (by rfl) ⟨2786048, by rfl⟩ : syracuseStep 3714731 = 5572097) B5572097
theorem B3346751 : Blo 1466553 3346751 := bstep (se 1 (by rfl) ⟨2510063, by rfl⟩ : syracuseStep 3346751 = 5020127) B5020127
theorem B21149693 : Blo 1466553 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B3766655 : Blo 1466553 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B5568983 : Blo 1466553 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B343071773 : Blo 1466553 343071773 := bstep (se 3 (by rfl) ⟨64325957, by rfl⟩ : syracuseStep 343071773 = 128651915) B128651915
theorem B14099795 : Blo 1466553 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B3712655 : Blo 1466553 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B228714515 : Blo 1466553 228714515 := bstep (se 1 (by rfl) ⟨171535886, by rfl⟩ : syracuseStep 228714515 = 343071773) B343071773
theorem B2476487 : Blo 1466553 2476487 := bstep (se 1 (by rfl) ⟨1857365, by rfl⟩ : syracuseStep 2476487 = 3714731) B3714731
theorem B8924669 : Blo 1466553 8924669 := bstep (se 3 (by rfl) ⟨1673375, by rfl⟩ : syracuseStep 8924669 = 3346751) B3346751
theorem B7056895 : Blo 1466553 7056895 := bstep (se 1 (by rfl) ⟨5292671, by rfl⟩ : syracuseStep 7056895 = 10585343) B10585343
theorem B2511103 : Blo 1466553 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B2475103 : Blo 1466553 2475103 := bstep (se 1 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 2475103 = 3712655) B3712655
theorem B5949779 : Blo 1466553 5949779 := bstep (se 1 (by rfl) ⟨4462334, by rfl⟩ : syracuseStep 5949779 = 8924669) B8924669
theorem B9399863 : Blo 1466553 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B1650991 : Blo 1466553 1650991 := bstep (se 1 (by rfl) ⟨1238243, by rfl⟩ : syracuseStep 1650991 = 2476487) B2476487
theorem B9409193 : Blo 1466553 9409193 := bstep (se 2 (by rfl) ⟨3528447, by rfl⟩ : syracuseStep 9409193 = 7056895) B7056895
theorem B3348137 : Blo 1466553 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B152476343 : Blo 1466553 152476343 := bstep (se 1 (by rfl) ⟨114357257, by rfl⟩ : syracuseStep 152476343 = 228714515) B228714515
theorem B101650895 : Blo 1466553 101650895 := bstep (se 1 (by rfl) ⟨76238171, by rfl⟩ : syracuseStep 101650895 = 152476343) B152476343
theorem B2201321 : Blo 1466553 2201321 := bstep (se 2 (by rfl) ⟨825495, by rfl⟩ : syracuseStep 2201321 = 1650991) B1650991
theorem B6272795 : Blo 1466553 6272795 := bstep (se 1 (by rfl) ⟨4704596, by rfl⟩ : syracuseStep 6272795 = 9409193) B9409193
theorem B15866077 : Blo 1466553 15866077 := bstep (se 3 (by rfl) ⟨2974889, by rfl⟩ : syracuseStep 15866077 = 5949779) B5949779
theorem B3300137 : Blo 1466553 3300137 := bstep (se 2 (by rfl) ⟨1237551, by rfl⟩ : syracuseStep 3300137 = 2475103) B2475103
theorem B8928365 : Blo 1466553 8928365 := bstep (se 3 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 8928365 = 3348137) B3348137
theorem B6266575 : Blo 1466553 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B1467547 : Blo 1466553 1467547 := bstep (se 1 (by rfl) ⟨1100660, by rfl⟩ : syracuseStep 1467547 = 2201321) B2201321
theorem B23808973 : Blo 1466553 23808973 := bstep (se 3 (by rfl) ⟨4464182, by rfl⟩ : syracuseStep 23808973 = 8928365) B8928365
theorem B21154769 : Blo 1466553 21154769 := bstep (se 2 (by rfl) ⟨7933038, by rfl⟩ : syracuseStep 21154769 = 15866077) B15866077
theorem B67767263 : Blo 1466553 67767263 := bstep (se 1 (by rfl) ⟨50825447, by rfl⟩ : syracuseStep 67767263 = 101650895) B101650895
theorem B4181863 : Blo 1466553 4181863 := bstep (se 1 (by rfl) ⟨3136397, by rfl⟩ : syracuseStep 4181863 = 6272795) B6272795
theorem B2200091 : Blo 1466553 2200091 := bstep (se 1 (by rfl) ⟨1650068, by rfl⟩ : syracuseStep 2200091 = 3300137) B3300137
theorem B8355433 : Blo 1466553 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B1466727 : Blo 1466553 1466727 := bstep (se 1 (by rfl) ⟨1100045, by rfl⟩ : syracuseStep 1466727 = 2200091) B2200091
theorem B31745297 : Blo 1466553 31745297 := bstep (se 2 (by rfl) ⟨11904486, by rfl⟩ : syracuseStep 31745297 = 23808973) B23808973
theorem B14103179 : Blo 1466553 14103179 := bstep (se 1 (by rfl) ⟨10577384, by rfl⟩ : syracuseStep 14103179 = 21154769) B21154769
theorem B5575817 : Blo 1466553 5575817 := bstep (se 2 (by rfl) ⟨2090931, by rfl⟩ : syracuseStep 5575817 = 4181863) B4181863
theorem B45178175 : Blo 1466553 45178175 := bstep (se 1 (by rfl) ⟨33883631, by rfl⟩ : syracuseStep 45178175 = 67767263) B67767263
theorem B11140577 : Blo 1466553 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B120475133 : Blo 1466553 120475133 := bstep (se 3 (by rfl) ⟨22589087, by rfl⟩ : syracuseStep 120475133 = 45178175) B45178175
theorem B21163531 : Blo 1466553 21163531 := bstep (se 1 (by rfl) ⟨15872648, by rfl⟩ : syracuseStep 21163531 = 31745297) B31745297
theorem B7427051 : Blo 1466553 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B9402119 : Blo 1466553 9402119 := bstep (se 1 (by rfl) ⟨7051589, by rfl⟩ : syracuseStep 9402119 = 14103179) B14103179
theorem B3717211 : Blo 1466553 3717211 := bstep (se 1 (by rfl) ⟨2787908, by rfl⟩ : syracuseStep 3717211 = 5575817) B5575817
theorem B4956281 : Blo 1466553 4956281 := bstep (se 2 (by rfl) ⟨1858605, by rfl⟩ : syracuseStep 4956281 = 3717211) B3717211
theorem B6268079 : Blo 1466553 6268079 := bstep (se 1 (by rfl) ⟨4701059, by rfl⟩ : syracuseStep 6268079 = 9402119) B9402119
theorem B80316755 : Blo 1466553 80316755 := bstep (se 1 (by rfl) ⟨60237566, by rfl⟩ : syracuseStep 80316755 = 120475133) B120475133
theorem B4951367 : Blo 1466553 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B28218041 : Blo 1466553 28218041 := bstep (se 2 (by rfl) ⟨10581765, by rfl⟩ : syracuseStep 28218041 = 21163531) B21163531
theorem B4178719 : Blo 1466553 4178719 := bstep (se 1 (by rfl) ⟨3134039, by rfl⟩ : syracuseStep 4178719 = 6268079) B6268079
theorem B53544503 : Blo 1466553 53544503 := bstep (se 1 (by rfl) ⟨40158377, by rfl⟩ : syracuseStep 53544503 = 80316755) B80316755
theorem B3304187 : Blo 1466553 3304187 := bstep (se 1 (by rfl) ⟨2478140, by rfl⟩ : syracuseStep 3304187 = 4956281) B4956281
theorem B18812027 : Blo 1466553 18812027 := bstep (se 1 (by rfl) ⟨14109020, by rfl⟩ : syracuseStep 18812027 = 28218041) B28218041
theorem B3300911 : Blo 1466553 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B5571625 : Blo 1466553 5571625 := bstep (se 2 (by rfl) ⟨2089359, by rfl⟩ : syracuseStep 5571625 = 4178719) B4178719
theorem B35696335 : Blo 1466553 35696335 := bstep (se 1 (by rfl) ⟨26772251, by rfl⟩ : syracuseStep 35696335 = 53544503) B53544503
theorem B2200607 : Blo 1466553 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B2202791 : Blo 1466553 2202791 := bstep (se 1 (by rfl) ⟨1652093, by rfl⟩ : syracuseStep 2202791 = 3304187) B3304187
theorem B12541351 : Blo 1466553 12541351 := bstep (se 1 (by rfl) ⟨9406013, by rfl⟩ : syracuseStep 12541351 = 18812027) B18812027
theorem B1467071 : Blo 1466553 1467071 := bstep (se 1 (by rfl) ⟨1100303, by rfl⟩ : syracuseStep 1467071 = 2200607) B2200607
theorem B16721801 : Blo 1466553 16721801 := bstep (se 2 (by rfl) ⟨6270675, by rfl⟩ : syracuseStep 16721801 = 12541351) B12541351
theorem B1468527 : Blo 1466553 1468527 := bstep (se 1 (by rfl) ⟨1101395, by rfl⟩ : syracuseStep 1468527 = 2202791) B2202791
theorem B7428833 : Blo 1466553 7428833 := bstep (se 2 (by rfl) ⟨2785812, by rfl⟩ : syracuseStep 7428833 = 5571625) B5571625
theorem B47595113 : Blo 1466553 47595113 := bstep (se 2 (by rfl) ⟨17848167, by rfl⟩ : syracuseStep 47595113 = 35696335) B35696335
theorem B31730075 : Blo 1466553 31730075 := bstep (se 1 (by rfl) ⟨23797556, by rfl⟩ : syracuseStep 31730075 = 47595113) B47595113
theorem B4952555 : Blo 1466553 4952555 := bstep (se 1 (by rfl) ⟨3714416, by rfl⟩ : syracuseStep 4952555 = 7428833) B7428833
theorem B11147867 : Blo 1466553 11147867 := bstep (se 1 (by rfl) ⟨8360900, by rfl⟩ : syracuseStep 11147867 = 16721801) B16721801
theorem B3301703 : Blo 1466553 3301703 := bstep (se 1 (by rfl) ⟨2476277, by rfl⟩ : syracuseStep 3301703 = 4952555) B4952555
theorem B21153383 : Blo 1466553 21153383 := bstep (se 1 (by rfl) ⟨15865037, by rfl⟩ : syracuseStep 21153383 = 31730075) B31730075
theorem B7431911 : Blo 1466553 7431911 := bstep (se 1 (by rfl) ⟨5573933, by rfl⟩ : syracuseStep 7431911 = 11147867) B11147867
theorem B14102255 : Blo 1466553 14102255 := bstep (se 1 (by rfl) ⟨10576691, by rfl⟩ : syracuseStep 14102255 = 21153383) B21153383
theorem B2201135 : Blo 1466553 2201135 := bstep (se 1 (by rfl) ⟨1650851, by rfl⟩ : syracuseStep 2201135 = 3301703) B3301703
theorem B4954607 : Blo 1466553 4954607 := bstep (se 1 (by rfl) ⟨3715955, by rfl⟩ : syracuseStep 4954607 = 7431911) B7431911
theorem B1467423 : Blo 1466553 1467423 := bstep (se 1 (by rfl) ⟨1100567, by rfl⟩ : syracuseStep 1467423 = 2201135) B2201135
theorem B3303071 : Blo 1466553 3303071 := bstep (se 1 (by rfl) ⟨2477303, by rfl⟩ : syracuseStep 3303071 = 4954607) B4954607
theorem B9401503 : Blo 1466553 9401503 := bstep (se 1 (by rfl) ⟨7051127, by rfl⟩ : syracuseStep 9401503 = 14102255) B14102255
theorem B12535337 : Blo 1466553 12535337 := bstep (se 2 (by rfl) ⟨4700751, by rfl⟩ : syracuseStep 12535337 = 9401503) B9401503
theorem B2202047 : Blo 1466553 2202047 := bstep (se 1 (by rfl) ⟨1651535, by rfl⟩ : syracuseStep 2202047 = 3303071) B3303071
theorem B8356891 : Blo 1466553 8356891 := bstep (se 1 (by rfl) ⟨6267668, by rfl⟩ : syracuseStep 8356891 = 12535337) B12535337
theorem B1468031 : Blo 1466553 1468031 := bstep (se 1 (by rfl) ⟨1101023, by rfl⟩ : syracuseStep 1468031 = 2202047) B2202047
theorem B11142521 : Blo 1466553 11142521 := bstep (se 2 (by rfl) ⟨4178445, by rfl⟩ : syracuseStep 11142521 = 8356891) B8356891
theorem B7428347 : Blo 1466553 7428347 := bstep (se 1 (by rfl) ⟨5571260, by rfl⟩ : syracuseStep 7428347 = 11142521) B11142521
theorem B4952231 : Blo 1466553 4952231 := bstep (se 1 (by rfl) ⟨3714173, by rfl⟩ : syracuseStep 4952231 = 7428347) B7428347
theorem B3301487 : Blo 1466553 3301487 := bstep (se 1 (by rfl) ⟨2476115, by rfl⟩ : syracuseStep 3301487 = 4952231) B4952231
theorem B2200991 : Blo 1466553 2200991 := bstep (se 1 (by rfl) ⟨1650743, by rfl⟩ : syracuseStep 2200991 = 3301487) B3301487
theorem B1467327 : Blo 1466553 1467327 := bstep (se 1 (by rfl) ⟨1100495, by rfl⟩ : syracuseStep 1467327 = 2200991) B2200991

theorem C0 (j : ℕ) (h1 : 366638 ≤ j) (h2 : j ≤ 367137) : Blo 1466553 (4 * j + 3) := by
  interval_cases j
  · exact B1466555
  · exact B1466559
  · exact B1466563
  · exact B1466567
  · exact B1466571
  · exact B1466575
  · exact B1466579
  · exact B1466583
  · exact B1466587
  · exact B1466591
  · exact B1466595
  · exact B1466599
  · exact B1466603
  · exact B1466607
  · exact B1466611
  · exact B1466615
  · exact B1466619
  · exact B1466623
  · exact B1466627
  · exact B1466631
  · exact B1466635
  · exact B1466639
  · exact B1466643
  · exact B1466647
  · exact B1466651
  · exact B1466655
  · exact B1466659
  · exact B1466663
  · exact B1466667
  · exact B1466671
  · exact B1466675
  · exact B1466679
  · exact B1466683
  · exact B1466687
  · exact B1466691
  · exact B1466695
  · exact B1466699
  · exact B1466703
  · exact B1466707
  · exact B1466711
  · exact B1466715
  · exact B1466719
  · exact B1466723
  · exact B1466727
  · exact B1466731
  · exact B1466735
  · exact B1466739
  · exact B1466743
  · exact B1466747
  · exact B1466751
  · exact B1466755
  · exact B1466759
  · exact B1466763
  · exact B1466767
  · exact B1466771
  · exact B1466775
  · exact B1466779
  · exact B1466783
  · exact B1466787
  · exact B1466791
  · exact B1466795
  · exact B1466799
  · exact B1466803
  · exact B1466807
  · exact B1466811
  · exact B1466815
  · exact B1466819
  · exact B1466823
  · exact B1466827
  · exact B1466831
  · exact B1466835
  · exact B1466839
  · exact B1466843
  · exact B1466847
  · exact B1466851
  · exact B1466855
  · exact B1466859
  · exact B1466863
  · exact B1466867
  · exact B1466871
  · exact B1466875
  · exact B1466879
  · exact B1466883
  · exact B1466887
  · exact B1466891
  · exact B1466895
  · exact B1466899
  · exact B1466903
  · exact B1466907
  · exact B1466911
  · exact B1466915
  · exact B1466919
  · exact B1466923
  · exact B1466927
  · exact B1466931
  · exact B1466935
  · exact B1466939
  · exact B1466943
  · exact B1466947
  · exact B1466951
  · exact B1466955
  · exact B1466959
  · exact B1466963
  · exact B1466967
  · exact B1466971
  · exact B1466975
  · exact B1466979
  · exact B1466983
  · exact B1466987
  · exact B1466991
  · exact B1466995
  · exact B1466999
  · exact B1467003
  · exact B1467007
  · exact B1467011
  · exact B1467015
  · exact B1467019
  · exact B1467023
  · exact B1467027
  · exact B1467031
  · exact B1467035
  · exact B1467039
  · exact B1467043
  · exact B1467047
  · exact B1467051
  · exact B1467055
  · exact B1467059
  · exact B1467063
  · exact B1467067
  · exact B1467071
  · exact B1467075
  · exact B1467079
  · exact B1467083
  · exact B1467087
  · exact B1467091
  · exact B1467095
  · exact B1467099
  · exact B1467103
  · exact B1467107
  · exact B1467111
  · exact B1467115
  · exact B1467119
  · exact B1467123
  · exact B1467127
  · exact B1467131
  · exact B1467135
  · exact B1467139
  · exact B1467143
  · exact B1467147
  · exact B1467151
  · exact B1467155
  · exact B1467159
  · exact B1467163
  · exact B1467167
  · exact B1467171
  · exact B1467175
  · exact B1467179
  · exact B1467183
  · exact B1467187
  · exact B1467191
  · exact B1467195
  · exact B1467199
  · exact B1467203
  · exact B1467207
  · exact B1467211
  · exact B1467215
  · exact B1467219
  · exact B1467223
  · exact B1467227
  · exact B1467231
  · exact B1467235
  · exact B1467239
  · exact B1467243
  · exact B1467247
  · exact B1467251
  · exact B1467255
  · exact B1467259
  · exact B1467263
  · exact B1467267
  · exact B1467271
  · exact B1467275
  · exact B1467279
  · exact B1467283
  · exact B1467287
  · exact B1467291
  · exact B1467295
  · exact B1467299
  · exact B1467303
  · exact B1467307
  · exact B1467311
  · exact B1467315
  · exact B1467319
  · exact B1467323
  · exact B1467327
  · exact B1467331
  · exact B1467335
  · exact B1467339
  · exact B1467343
  · exact B1467347
  · exact B1467351
  · exact B1467355
  · exact B1467359
  · exact B1467363
  · exact B1467367
  · exact B1467371
  · exact B1467375
  · exact B1467379
  · exact B1467383
  · exact B1467387
  · exact B1467391
  · exact B1467395
  · exact B1467399
  · exact B1467403
  · exact B1467407
  · exact B1467411
  · exact B1467415
  · exact B1467419
  · exact B1467423
  · exact B1467427
  · exact B1467431
  · exact B1467435
  · exact B1467439
  · exact B1467443
  · exact B1467447
  · exact B1467451
  · exact B1467455
  · exact B1467459
  · exact B1467463
  · exact B1467467
  · exact B1467471
  · exact B1467475
  · exact B1467479
  · exact B1467483
  · exact B1467487
  · exact B1467491
  · exact B1467495
  · exact B1467499
  · exact B1467503
  · exact B1467507
  · exact B1467511
  · exact B1467515
  · exact B1467519
  · exact B1467523
  · exact B1467527
  · exact B1467531
  · exact B1467535
  · exact B1467539
  · exact B1467543
  · exact B1467547
  · exact B1467551
  · exact B1467555
  · exact B1467559
  · exact B1467563
  · exact B1467567
  · exact B1467571
  · exact B1467575
  · exact B1467579
  · exact B1467583
  · exact B1467587
  · exact B1467591
  · exact B1467595
  · exact B1467599
  · exact B1467603
  · exact B1467607
  · exact B1467611
  · exact B1467615
  · exact B1467619
  · exact B1467623
  · exact B1467627
  · exact B1467631
  · exact B1467635
  · exact B1467639
  · exact B1467643
  · exact B1467647
  · exact B1467651
  · exact B1467655
  · exact B1467659
  · exact B1467663
  · exact B1467667
  · exact B1467671
  · exact B1467675
  · exact B1467679
  · exact B1467683
  · exact B1467687
  · exact B1467691
  · exact B1467695
  · exact B1467699
  · exact B1467703
  · exact B1467707
  · exact B1467711
  · exact B1467715
  · exact B1467719
  · exact B1467723
  · exact B1467727
  · exact B1467731
  · exact B1467735
  · exact B1467739
  · exact B1467743
  · exact B1467747
  · exact B1467751
  · exact B1467755
  · exact B1467759
  · exact B1467763
  · exact B1467767
  · exact B1467771
  · exact B1467775
  · exact B1467779
  · exact B1467783
  · exact B1467787
  · exact B1467791
  · exact B1467795
  · exact B1467799
  · exact B1467803
  · exact B1467807
  · exact B1467811
  · exact B1467815
  · exact B1467819
  · exact B1467823
  · exact B1467827
  · exact B1467831
  · exact B1467835
  · exact B1467839
  · exact B1467843
  · exact B1467847
  · exact B1467851
  · exact B1467855
  · exact B1467859
  · exact B1467863
  · exact B1467867
  · exact B1467871
  · exact B1467875
  · exact B1467879
  · exact B1467883
  · exact B1467887
  · exact B1467891
  · exact B1467895
  · exact B1467899
  · exact B1467903
  · exact B1467907
  · exact B1467911
  · exact B1467915
  · exact B1467919
  · exact B1467923
  · exact B1467927
  · exact B1467931
  · exact B1467935
  · exact B1467939
  · exact B1467943
  · exact B1467947
  · exact B1467951
  · exact B1467955
  · exact B1467959
  · exact B1467963
  · exact B1467967
  · exact B1467971
  · exact B1467975
  · exact B1467979
  · exact B1467983
  · exact B1467987
  · exact B1467991
  · exact B1467995
  · exact B1467999
  · exact B1468003
  · exact B1468007
  · exact B1468011
  · exact B1468015
  · exact B1468019
  · exact B1468023
  · exact B1468027
  · exact B1468031
  · exact B1468035
  · exact B1468039
  · exact B1468043
  · exact B1468047
  · exact B1468051
  · exact B1468055
  · exact B1468059
  · exact B1468063
  · exact B1468067
  · exact B1468071
  · exact B1468075
  · exact B1468079
  · exact B1468083
  · exact B1468087
  · exact B1468091
  · exact B1468095
  · exact B1468099
  · exact B1468103
  · exact B1468107
  · exact B1468111
  · exact B1468115
  · exact B1468119
  · exact B1468123
  · exact B1468127
  · exact B1468131
  · exact B1468135
  · exact B1468139
  · exact B1468143
  · exact B1468147
  · exact B1468151
  · exact B1468155
  · exact B1468159
  · exact B1468163
  · exact B1468167
  · exact B1468171
  · exact B1468175
  · exact B1468179
  · exact B1468183
  · exact B1468187
  · exact B1468191
  · exact B1468195
  · exact B1468199
  · exact B1468203
  · exact B1468207
  · exact B1468211
  · exact B1468215
  · exact B1468219
  · exact B1468223
  · exact B1468227
  · exact B1468231
  · exact B1468235
  · exact B1468239
  · exact B1468243
  · exact B1468247
  · exact B1468251
  · exact B1468255
  · exact B1468259
  · exact B1468263
  · exact B1468267
  · exact B1468271
  · exact B1468275
  · exact B1468279
  · exact B1468283
  · exact B1468287
  · exact B1468291
  · exact B1468295
  · exact B1468299
  · exact B1468303
  · exact B1468307
  · exact B1468311
  · exact B1468315
  · exact B1468319
  · exact B1468323
  · exact B1468327
  · exact B1468331
  · exact B1468335
  · exact B1468339
  · exact B1468343
  · exact B1468347
  · exact B1468351
  · exact B1468355
  · exact B1468359
  · exact B1468363
  · exact B1468367
  · exact B1468371
  · exact B1468375
  · exact B1468379
  · exact B1468383
  · exact B1468387
  · exact B1468391
  · exact B1468395
  · exact B1468399
  · exact B1468403
  · exact B1468407
  · exact B1468411
  · exact B1468415
  · exact B1468419
  · exact B1468423
  · exact B1468427
  · exact B1468431
  · exact B1468435
  · exact B1468439
  · exact B1468443
  · exact B1468447
  · exact B1468451
  · exact B1468455
  · exact B1468459
  · exact B1468463
  · exact B1468467
  · exact B1468471
  · exact B1468475
  · exact B1468479
  · exact B1468483
  · exact B1468487
  · exact B1468491
  · exact B1468495
  · exact B1468499
  · exact B1468503
  · exact B1468507
  · exact B1468511
  · exact B1468515
  · exact B1468519
  · exact B1468523
  · exact B1468527
  · exact B1468531
  · exact B1468535
  · exact B1468539
  · exact B1468543
  · exact B1468547
  · exact B1468551

theorem solution (m : ℕ) (hlo : 1466553 ≤ m) (hhi : m ≤ 1468553) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 366638 ≤ j := by omega
    have hj2 : j ≤ 367137 := by omega
    have hb : Blo 1466553 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
