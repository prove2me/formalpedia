-- Prove2me | solution 1 for syracuse_descends_range_766334_770334
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:21.580555+00:00
-- url     : https://prove2.me/submissions/d91509bb-5d38-4e2d-9530-d5283241b6d1

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


theorem B1802549 : Blo 766334 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B819553 : Blo 766334 819553 := bbase (se 2 (by rfl) ⟨307332, by rfl⟩ : syracuseStep 819553 = 614665) (by norm_num)
theorem B2589029 : Blo 766334 2589029 := bbase (se 4 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 2589029 = 485443) (by norm_num)
theorem B3277205 : Blo 766334 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B819677 : Blo 766334 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B4915829 : Blo 766334 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B1475245 : Blo 766334 1475245 := bbase (se 3 (by rfl) ⟨276608, by rfl⟩ : syracuseStep 1475245 = 553217) (by norm_num)
theorem B3277493 : Blo 766334 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2458325 : Blo 766334 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B819929 : Blo 766334 819929 := bbase (se 2 (by rfl) ⟨307473, by rfl⟩ : syracuseStep 819929 = 614947) (by norm_num)
theorem B2917093 : Blo 766334 2917093 := bbase (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) (by norm_num)
theorem B1311493 : Blo 766334 1311493 := bbase (se 4 (by rfl) ⟨122952, by rfl⟩ : syracuseStep 1311493 = 245905) (by norm_num)
theorem B2589461 : Blo 766334 2589461 := bbase (se 6 (by rfl) ⟨60690, by rfl⟩ : syracuseStep 2589461 = 121381) (by norm_num)
theorem B2917397 : Blo 766334 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B3376181 : Blo 766334 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B820373 : Blo 766334 820373 := bbase (se 6 (by rfl) ⟨19227, by rfl⟩ : syracuseStep 820373 = 38455) (by norm_num)
theorem B2589893 : Blo 766334 2589893 := bbase (se 4 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 2589893 = 485605) (by norm_num)
theorem B820621 : Blo 766334 820621 := bbase (se 3 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 820621 = 307733) (by norm_num)
theorem B3278245 : Blo 766334 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B3737029 : Blo 766334 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B1639901 : Blo 766334 1639901 := bbase (se 3 (by rfl) ⟨307481, by rfl⟩ : syracuseStep 1639901 = 614963) (by norm_num)
theorem B984565 : Blo 766334 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B1640045 : Blo 766334 1640045 := bbase (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) (by norm_num)
theorem B2590325 : Blo 766334 2590325 := bbase (se 5 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 2590325 = 242843) (by norm_num)
theorem B1312453 : Blo 766334 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B821065 : Blo 766334 821065 := bbase (se 2 (by rfl) ⟨307899, by rfl⟩ : syracuseStep 821065 = 615799) (by norm_num)
theorem B821125 : Blo 766334 821125 := bbase (se 4 (by rfl) ⟨76980, by rfl⟩ : syracuseStep 821125 = 153961) (by norm_num)
theorem B8521685 : Blo 766334 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B1640405 : Blo 766334 1640405 := bbase (se 7 (by rfl) ⟨19223, by rfl⟩ : syracuseStep 1640405 = 38447) (by norm_num)
theorem B2590757 : Blo 766334 2590757 := bbase (se 4 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 2590757 = 485767) (by norm_num)
theorem B3278981 : Blo 766334 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B821441 : Blo 766334 821441 := bbase (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) (by norm_num)
theorem B2623861 : Blo 766334 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B788945 : Blo 766334 788945 := bbase (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) (by norm_num)
theorem B2591189 : Blo 766334 2591189 := bbase (se 7 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 2591189 = 60731) (by norm_num)
theorem B1149509 : Blo 766334 1149509 := bbase (se 4 (by rfl) ⟨107766, by rfl⟩ : syracuseStep 1149509 = 215533) (by norm_num)
theorem B1149533 : Blo 766334 1149533 := bbase (se 3 (by rfl) ⟨215537, by rfl⟩ : syracuseStep 1149533 = 431075) (by norm_num)
theorem B1149557 : Blo 766334 1149557 := bbase (se 5 (by rfl) ⟨53885, by rfl⟩ : syracuseStep 1149557 = 107771) (by norm_num)
theorem B821885 : Blo 766334 821885 := bbase (se 3 (by rfl) ⟨154103, by rfl⟩ : syracuseStep 821885 = 308207) (by norm_num)
theorem B1149581 : Blo 766334 1149581 := bbase (se 3 (by rfl) ⟨215546, by rfl⟩ : syracuseStep 1149581 = 431093) (by norm_num)
theorem B1149605 : Blo 766334 1149605 := bbase (se 4 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 1149605 = 215551) (by norm_num)
theorem B821945 : Blo 766334 821945 := bbase (se 2 (by rfl) ⟨308229, by rfl⟩ : syracuseStep 821945 = 616459) (by norm_num)
theorem B1149629 : Blo 766334 1149629 := bbase (se 3 (by rfl) ⟨215555, by rfl⟩ : syracuseStep 1149629 = 431111) (by norm_num)
theorem B1149653 : Blo 766334 1149653 := bbase (se 7 (by rfl) ⟨13472, by rfl⟩ : syracuseStep 1149653 = 26945) (by norm_num)
theorem B1149677 : Blo 766334 1149677 := bbase (se 3 (by rfl) ⟨215564, by rfl⟩ : syracuseStep 1149677 = 431129) (by norm_num)
theorem B985837 : Blo 766334 985837 := bbase (se 3 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 985837 = 369689) (by norm_num)
theorem B1149701 : Blo 766334 1149701 := bbase (se 4 (by rfl) ⟨107784, by rfl⟩ : syracuseStep 1149701 = 215569) (by norm_num)
theorem B1149725 : Blo 766334 1149725 := bbase (se 3 (by rfl) ⟨215573, by rfl⟩ : syracuseStep 1149725 = 431147) (by norm_num)
theorem B1149749 : Blo 766334 1149749 := bbase (se 5 (by rfl) ⟨53894, by rfl⟩ : syracuseStep 1149749 = 107789) (by norm_num)
theorem B822073 : Blo 766334 822073 := bbase (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) (by norm_num)
theorem B1149773 : Blo 766334 1149773 := bbase (se 3 (by rfl) ⟨215582, by rfl⟩ : syracuseStep 1149773 = 431165) (by norm_num)
theorem B1641293 : Blo 766334 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B1149797 : Blo 766334 1149797 := bbase (se 4 (by rfl) ⟨107793, by rfl⟩ : syracuseStep 1149797 = 215587) (by norm_num)
theorem B1149821 : Blo 766334 1149821 := bbase (se 3 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 1149821 = 431183) (by norm_num)
theorem B2591621 : Blo 766334 2591621 := bbase (se 4 (by rfl) ⟨242964, by rfl⟩ : syracuseStep 2591621 = 485929) (by norm_num)
theorem B1149845 : Blo 766334 1149845 := bbase (se 6 (by rfl) ⟨26949, by rfl⟩ : syracuseStep 1149845 = 53899) (by norm_num)
theorem B3115925 : Blo 766334 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B2460581 : Blo 766334 2460581 := bbase (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) (by norm_num)
theorem B1149869 : Blo 766334 1149869 := bbase (se 3 (by rfl) ⟨215600, by rfl⟩ : syracuseStep 1149869 = 431201) (by norm_num)
theorem B1149893 : Blo 766334 1149893 := bbase (se 4 (by rfl) ⟨107802, by rfl⟩ : syracuseStep 1149893 = 215605) (by norm_num)
theorem B1149917 : Blo 766334 1149917 := bbase (se 3 (by rfl) ⟨215609, by rfl⟩ : syracuseStep 1149917 = 431219) (by norm_num)
theorem B1149941 : Blo 766334 1149941 := bbase (se 5 (by rfl) ⟨53903, by rfl⟩ : syracuseStep 1149941 = 107807) (by norm_num)
theorem B1149965 : Blo 766334 1149965 := bbase (se 3 (by rfl) ⟨215618, by rfl⟩ : syracuseStep 1149965 = 431237) (by norm_num)
theorem B1575965 : Blo 766334 1575965 := bbase (se 3 (by rfl) ⟨295493, by rfl⟩ : syracuseStep 1575965 = 590987) (by norm_num)
theorem B1149989 : Blo 766334 1149989 := bbase (se 4 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 1149989 = 215623) (by norm_num)
theorem B2460709 : Blo 766334 2460709 := bbase (se 4 (by rfl) ⟨230691, by rfl⟩ : syracuseStep 2460709 = 461383) (by norm_num)
theorem B1150013 : Blo 766334 1150013 := bbase (se 3 (by rfl) ⟨215627, by rfl⟩ : syracuseStep 1150013 = 431255) (by norm_num)
theorem B1641541 : Blo 766334 1641541 := bbase (se 4 (by rfl) ⟨153894, by rfl⟩ : syracuseStep 1641541 = 307789) (by norm_num)
theorem B1150037 : Blo 766334 1150037 := bbase (se 8 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 1150037 = 13477) (by norm_num)
theorem B2919509 : Blo 766334 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1150061 : Blo 766334 1150061 := bbase (se 3 (by rfl) ⟨215636, by rfl⟩ : syracuseStep 1150061 = 431273) (by norm_num)
theorem B1150085 : Blo 766334 1150085 := bbase (se 4 (by rfl) ⟨107820, by rfl⟩ : syracuseStep 1150085 = 215641) (by norm_num)
theorem B1150109 : Blo 766334 1150109 := bbase (se 3 (by rfl) ⟨215645, by rfl⟩ : syracuseStep 1150109 = 431291) (by norm_num)
theorem B1150133 : Blo 766334 1150133 := bbase (se 5 (by rfl) ⟨53912, by rfl⟩ : syracuseStep 1150133 = 107825) (by norm_num)
theorem B1150157 : Blo 766334 1150157 := bbase (se 3 (by rfl) ⟨215654, by rfl⟩ : syracuseStep 1150157 = 431309) (by norm_num)
theorem B1150181 : Blo 766334 1150181 := bbase (se 4 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 1150181 = 215659) (by norm_num)
theorem B822517 : Blo 766334 822517 := bbase (se 5 (by rfl) ⟨38555, by rfl⟩ : syracuseStep 822517 = 77111) (by norm_num)
theorem B1150205 : Blo 766334 1150205 := bbase (se 3 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 1150205 = 431327) (by norm_num)
theorem B1150229 : Blo 766334 1150229 := bbase (se 6 (by rfl) ⟨26958, by rfl⟩ : syracuseStep 1150229 = 53917) (by norm_num)
theorem B1150253 : Blo 766334 1150253 := bbase (se 3 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 1150253 = 431345) (by norm_num)
theorem B2592053 : Blo 766334 2592053 := bbase (se 5 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 2592053 = 243005) (by norm_num)
theorem B1150277 : Blo 766334 1150277 := bbase (se 4 (by rfl) ⟨107838, by rfl⟩ : syracuseStep 1150277 = 215677) (by norm_num)
theorem B1150301 : Blo 766334 1150301 := bbase (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) (by norm_num)
theorem B1150325 : Blo 766334 1150325 := bbase (se 5 (by rfl) ⟨53921, by rfl⟩ : syracuseStep 1150325 = 107843) (by norm_num)
theorem B2919797 : Blo 766334 2919797 := bbase (se 5 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 2919797 = 273731) (by norm_num)
theorem B1150349 : Blo 766334 1150349 := bbase (se 3 (by rfl) ⟨215690, by rfl⟩ : syracuseStep 1150349 = 431381) (by norm_num)
theorem B1150373 : Blo 766334 1150373 := bbase (se 4 (by rfl) ⟨107847, by rfl⟩ : syracuseStep 1150373 = 215695) (by norm_num)
theorem B1150397 : Blo 766334 1150397 := bbase (se 3 (by rfl) ⟨215699, by rfl⟩ : syracuseStep 1150397 = 431399) (by norm_num)
theorem B1150421 : Blo 766334 1150421 := bbase (se 7 (by rfl) ⟨13481, by rfl⟩ : syracuseStep 1150421 = 26963) (by norm_num)
theorem B23662037 : Blo 766334 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B1150445 : Blo 766334 1150445 := bbase (se 3 (by rfl) ⟨215708, by rfl⟩ : syracuseStep 1150445 = 431417) (by norm_num)
theorem B1150469 : Blo 766334 1150469 := bbase (se 4 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 1150469 = 215713) (by norm_num)
theorem B4918805 : Blo 766334 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1150493 : Blo 766334 1150493 := bbase (se 3 (by rfl) ⟨215717, by rfl⟩ : syracuseStep 1150493 = 431435) (by norm_num)
theorem B1576493 : Blo 766334 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B921137 : Blo 766334 921137 := bbase (se 2 (by rfl) ⟨345426, by rfl⟩ : syracuseStep 921137 = 690853) (by norm_num)
theorem B1150517 : Blo 766334 1150517 := bbase (se 5 (by rfl) ⟨53930, by rfl⟩ : syracuseStep 1150517 = 107861) (by norm_num)
theorem B1642045 : Blo 766334 1642045 := bbase (se 3 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 1642045 = 615767) (by norm_num)
theorem B1150541 : Blo 766334 1150541 := bbase (se 3 (by rfl) ⟨215726, by rfl⟩ : syracuseStep 1150541 = 431453) (by norm_num)
theorem B5836373 : Blo 766334 5836373 := bbase (se 8 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 5836373 = 68395) (by norm_num)
theorem B1150565 : Blo 766334 1150565 := bbase (se 4 (by rfl) ⟨107865, by rfl⟩ : syracuseStep 1150565 = 215731) (by norm_num)
theorem B1150589 : Blo 766334 1150589 := bbase (se 3 (by rfl) ⟨215735, by rfl⟩ : syracuseStep 1150589 = 431471) (by norm_num)
theorem B1150613 : Blo 766334 1150613 := bbase (se 6 (by rfl) ⟨26967, by rfl⟩ : syracuseStep 1150613 = 53935) (by norm_num)
theorem B1150637 : Blo 766334 1150637 := bbase (se 3 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 1150637 = 431489) (by norm_num)
theorem B1150661 : Blo 766334 1150661 := bbase (se 4 (by rfl) ⟨107874, by rfl⟩ : syracuseStep 1150661 = 215749) (by norm_num)
theorem B1150685 : Blo 766334 1150685 := bbase (se 3 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 1150685 = 431507) (by norm_num)
theorem B2592485 : Blo 766334 2592485 := bbase (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) (by norm_num)
theorem B1150709 : Blo 766334 1150709 := bbase (se 5 (by rfl) ⟨53939, by rfl⟩ : syracuseStep 1150709 = 107879) (by norm_num)
theorem B1150733 : Blo 766334 1150733 := bbase (se 3 (by rfl) ⟨215762, by rfl⟩ : syracuseStep 1150733 = 431525) (by norm_num)
theorem B1150757 : Blo 766334 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1150781 : Blo 766334 1150781 := bbase (se 3 (by rfl) ⟨215771, by rfl⟩ : syracuseStep 1150781 = 431543) (by norm_num)
theorem B986941 : Blo 766334 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1150805 : Blo 766334 1150805 := bbase (se 9 (by rfl) ⟨3371, by rfl⟩ : syracuseStep 1150805 = 6743) (by norm_num)
theorem B1150829 : Blo 766334 1150829 := bbase (se 3 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 1150829 = 431561) (by norm_num)
theorem B6655861 : Blo 766334 6655861 := bbase (se 5 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 6655861 = 623987) (by norm_num)
theorem B921469 : Blo 766334 921469 := bbase (se 3 (by rfl) ⟨172775, by rfl⟩ : syracuseStep 921469 = 345551) (by norm_num)
theorem B1150853 : Blo 766334 1150853 := bbase (se 4 (by rfl) ⟨107892, by rfl⟩ : syracuseStep 1150853 = 215785) (by norm_num)
theorem B1150877 : Blo 766334 1150877 := bbase (se 3 (by rfl) ⟨215789, by rfl⟩ : syracuseStep 1150877 = 431579) (by norm_num)
theorem B1150901 : Blo 766334 1150901 := bbase (se 5 (by rfl) ⟨53948, by rfl⟩ : syracuseStep 1150901 = 107897) (by norm_num)
theorem B6655925 : Blo 766334 6655925 := bbase (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) (by norm_num)
theorem B1150925 : Blo 766334 1150925 := bbase (se 3 (by rfl) ⟨215798, by rfl⟩ : syracuseStep 1150925 = 431597) (by norm_num)
theorem B790481 : Blo 766334 790481 := bbase (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) (by norm_num)
theorem B1150949 : Blo 766334 1150949 := bbase (se 4 (by rfl) ⟨107901, by rfl⟩ : syracuseStep 1150949 = 215803) (by norm_num)
theorem B1150973 : Blo 766334 1150973 := bbase (se 3 (by rfl) ⟨215807, by rfl⟩ : syracuseStep 1150973 = 431615) (by norm_num)
theorem B921613 : Blo 766334 921613 := bbase (se 3 (by rfl) ⟨172802, by rfl⟩ : syracuseStep 921613 = 345605) (by norm_num)
theorem B1150997 : Blo 766334 1150997 := bbase (se 6 (by rfl) ⟨26976, by rfl⟩ : syracuseStep 1150997 = 53953) (by norm_num)
theorem B1151021 : Blo 766334 1151021 := bbase (se 3 (by rfl) ⟨215816, by rfl⟩ : syracuseStep 1151021 = 431633) (by norm_num)
theorem B1151045 : Blo 766334 1151045 := bbase (se 4 (by rfl) ⟨107910, by rfl⟩ : syracuseStep 1151045 = 215821) (by norm_num)
theorem B1151069 : Blo 766334 1151069 := bbase (se 3 (by rfl) ⟨215825, by rfl⟩ : syracuseStep 1151069 = 431651) (by norm_num)
theorem B1151093 : Blo 766334 1151093 := bbase (se 5 (by rfl) ⟨53957, by rfl⟩ : syracuseStep 1151093 = 107915) (by norm_num)
theorem B1151117 : Blo 766334 1151117 := bbase (se 3 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 1151117 = 431669) (by norm_num)
theorem B2592917 : Blo 766334 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B1151141 : Blo 766334 1151141 := bbase (se 4 (by rfl) ⟨107919, by rfl⟩ : syracuseStep 1151141 = 215839) (by norm_num)
theorem B1151165 : Blo 766334 1151165 := bbase (se 3 (by rfl) ⟨215843, by rfl⟩ : syracuseStep 1151165 = 431687) (by norm_num)
theorem B1151189 : Blo 766334 1151189 := bbase (se 7 (by rfl) ⟨13490, by rfl⟩ : syracuseStep 1151189 = 26981) (by norm_num)
theorem B1151213 : Blo 766334 1151213 := bbase (se 3 (by rfl) ⟨215852, by rfl⟩ : syracuseStep 1151213 = 431705) (by norm_num)
theorem B1151237 : Blo 766334 1151237 := bbase (se 4 (by rfl) ⟨107928, by rfl⟩ : syracuseStep 1151237 = 215857) (by norm_num)
theorem B1151261 : Blo 766334 1151261 := bbase (se 3 (by rfl) ⟨215861, by rfl⟩ : syracuseStep 1151261 = 431723) (by norm_num)
theorem B1151285 : Blo 766334 1151285 := bbase (se 5 (by rfl) ⟨53966, by rfl⟩ : syracuseStep 1151285 = 107933) (by norm_num)
theorem B1151309 : Blo 766334 1151309 := bbase (se 3 (by rfl) ⟨215870, by rfl⟩ : syracuseStep 1151309 = 431741) (by norm_num)
theorem B1151333 : Blo 766334 1151333 := bbase (se 4 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 1151333 = 215875) (by norm_num)
theorem B1151357 : Blo 766334 1151357 := bbase (se 3 (by rfl) ⟨215879, by rfl⟩ : syracuseStep 1151357 = 431759) (by norm_num)
theorem B1151381 : Blo 766334 1151381 := bbase (se 6 (by rfl) ⟨26985, by rfl⟩ : syracuseStep 1151381 = 53971) (by norm_num)
theorem B1151405 : Blo 766334 1151405 := bbase (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) (by norm_num)
theorem B1642933 : Blo 766334 1642933 := bbase (se 5 (by rfl) ⟨77012, by rfl⟩ : syracuseStep 1642933 = 154025) (by norm_num)
theorem B1151429 : Blo 766334 1151429 := bbase (se 4 (by rfl) ⟨107946, by rfl⟩ : syracuseStep 1151429 = 215893) (by norm_num)
theorem B1151453 : Blo 766334 1151453 := bbase (se 3 (by rfl) ⟨215897, by rfl⟩ : syracuseStep 1151453 = 431795) (by norm_num)
theorem B1151477 : Blo 766334 1151477 := bbase (se 5 (by rfl) ⟨53975, by rfl⟩ : syracuseStep 1151477 = 107951) (by norm_num)
theorem B1151501 : Blo 766334 1151501 := bbase (se 3 (by rfl) ⟨215906, by rfl⟩ : syracuseStep 1151501 = 431813) (by norm_num)
theorem B2920981 : Blo 766334 2920981 := bbase (se 6 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 2920981 = 136921) (by norm_num)
theorem B1151525 : Blo 766334 1151525 := bbase (se 4 (by rfl) ⟨107955, by rfl⟩ : syracuseStep 1151525 = 215911) (by norm_num)
theorem B1151549 : Blo 766334 1151549 := bbase (se 3 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 1151549 = 431831) (by norm_num)
theorem B2593349 : Blo 766334 2593349 := bbase (se 4 (by rfl) ⟨243126, by rfl⟩ : syracuseStep 2593349 = 486253) (by norm_num)
theorem B1151573 : Blo 766334 1151573 := bbase (se 8 (by rfl) ⟨6747, by rfl⟩ : syracuseStep 1151573 = 13495) (by norm_num)
theorem B1151597 : Blo 766334 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B1151621 : Blo 766334 1151621 := bbase (se 4 (by rfl) ⟨107964, by rfl⟩ : syracuseStep 1151621 = 215929) (by norm_num)
theorem B1151645 : Blo 766334 1151645 := bbase (se 3 (by rfl) ⟨215933, by rfl⟩ : syracuseStep 1151645 = 431867) (by norm_num)
theorem B1151669 : Blo 766334 1151669 := bbase (se 5 (by rfl) ⟨53984, by rfl⟩ : syracuseStep 1151669 = 107969) (by norm_num)
theorem B1151693 : Blo 766334 1151693 := bbase (se 3 (by rfl) ⟨215942, by rfl⟩ : syracuseStep 1151693 = 431885) (by norm_num)
theorem B1151717 : Blo 766334 1151717 := bbase (se 4 (by rfl) ⟨107973, by rfl⟩ : syracuseStep 1151717 = 215947) (by norm_num)
theorem B1151741 : Blo 766334 1151741 := bbase (se 3 (by rfl) ⟨215951, by rfl⟩ : syracuseStep 1151741 = 431903) (by norm_num)
theorem B1151765 : Blo 766334 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B1151789 : Blo 766334 1151789 := bbase (se 3 (by rfl) ⟨215960, by rfl⟩ : syracuseStep 1151789 = 431921) (by norm_num)
theorem B889661 : Blo 766334 889661 := bbase (se 3 (by rfl) ⟨166811, by rfl⟩ : syracuseStep 889661 = 333623) (by norm_num)
theorem B1151813 : Blo 766334 1151813 := bbase (se 4 (by rfl) ⟨107982, by rfl⟩ : syracuseStep 1151813 = 215965) (by norm_num)
theorem B2921285 : Blo 766334 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B1151837 : Blo 766334 1151837 := bbase (se 3 (by rfl) ⟨215969, by rfl⟩ : syracuseStep 1151837 = 431939) (by norm_num)
theorem B1151861 : Blo 766334 1151861 := bbase (se 5 (by rfl) ⟨53993, by rfl⟩ : syracuseStep 1151861 = 107987) (by norm_num)
theorem B1151885 : Blo 766334 1151885 := bbase (se 3 (by rfl) ⟨215978, by rfl⟩ : syracuseStep 1151885 = 431957) (by norm_num)
theorem B1151909 : Blo 766334 1151909 := bbase (se 4 (by rfl) ⟨107991, by rfl⟩ : syracuseStep 1151909 = 215983) (by norm_num)
theorem B1643429 : Blo 766334 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B1151933 : Blo 766334 1151933 := bbase (se 3 (by rfl) ⟨215987, by rfl⟩ : syracuseStep 1151933 = 431975) (by norm_num)
theorem B6558677 : Blo 766334 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B1151957 : Blo 766334 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B1151981 : Blo 766334 1151981 := bbase (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) (by norm_num)
theorem B2593781 : Blo 766334 2593781 := bbase (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) (by norm_num)
theorem B1152005 : Blo 766334 1152005 := bbase (se 4 (by rfl) ⟨108000, by rfl⟩ : syracuseStep 1152005 = 216001) (by norm_num)
theorem B922637 : Blo 766334 922637 := bbase (se 3 (by rfl) ⟨172994, by rfl⟩ : syracuseStep 922637 = 345989) (by norm_num)
theorem B1152029 : Blo 766334 1152029 := bbase (se 3 (by rfl) ⟨216005, by rfl⟩ : syracuseStep 1152029 = 432011) (by norm_num)
theorem B1152053 : Blo 766334 1152053 := bbase (se 5 (by rfl) ⟨54002, by rfl⟩ : syracuseStep 1152053 = 108005) (by norm_num)
theorem B1152077 : Blo 766334 1152077 := bbase (se 3 (by rfl) ⟨216014, by rfl⟩ : syracuseStep 1152077 = 432029) (by norm_num)
theorem B1152101 : Blo 766334 1152101 := bbase (se 4 (by rfl) ⟨108009, by rfl⟩ : syracuseStep 1152101 = 216019) (by norm_num)
theorem B1152125 : Blo 766334 1152125 := bbase (se 3 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 1152125 = 432047) (by norm_num)
theorem B3413125 : Blo 766334 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B1152149 : Blo 766334 1152149 := bbase (se 6 (by rfl) ⟨27003, by rfl⟩ : syracuseStep 1152149 = 54007) (by norm_num)
theorem B1152173 : Blo 766334 1152173 := bbase (se 3 (by rfl) ⟨216032, by rfl⟩ : syracuseStep 1152173 = 432065) (by norm_num)
theorem B1152197 : Blo 766334 1152197 := bbase (se 4 (by rfl) ⟨108018, by rfl⟩ : syracuseStep 1152197 = 216037) (by norm_num)
theorem B1152221 : Blo 766334 1152221 := bbase (se 3 (by rfl) ⟨216041, by rfl⟩ : syracuseStep 1152221 = 432083) (by norm_num)
theorem B1152245 : Blo 766334 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B1152269 : Blo 766334 1152269 := bbase (se 3 (by rfl) ⟨216050, by rfl⟩ : syracuseStep 1152269 = 432101) (by norm_num)
theorem B1152293 : Blo 766334 1152293 := bbase (se 4 (by rfl) ⟨108027, by rfl⟩ : syracuseStep 1152293 = 216055) (by norm_num)
theorem B1152317 : Blo 766334 1152317 := bbase (se 3 (by rfl) ⟨216059, by rfl⟩ : syracuseStep 1152317 = 432119) (by norm_num)
theorem B1152341 : Blo 766334 1152341 := bbase (se 14 (by rfl) ⟨105, by rfl⟩ : syracuseStep 1152341 = 211) (by norm_num)
theorem B3282277 : Blo 766334 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B1152365 : Blo 766334 1152365 := bbase (se 3 (by rfl) ⟨216068, by rfl⟩ : syracuseStep 1152365 = 432137) (by norm_num)
theorem B1152389 : Blo 766334 1152389 := bbase (se 4 (by rfl) ⟨108036, by rfl⟩ : syracuseStep 1152389 = 216073) (by norm_num)
theorem B1152413 : Blo 766334 1152413 := bbase (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) (by norm_num)
theorem B2594213 : Blo 766334 2594213 := bbase (se 4 (by rfl) ⟨243207, by rfl⟩ : syracuseStep 2594213 = 486415) (by norm_num)
theorem B1152437 : Blo 766334 1152437 := bbase (se 5 (by rfl) ⟨54020, by rfl⟩ : syracuseStep 1152437 = 108041) (by norm_num)
theorem B1152461 : Blo 766334 1152461 := bbase (se 3 (by rfl) ⟨216086, by rfl⟩ : syracuseStep 1152461 = 432173) (by norm_num)
theorem B1152485 : Blo 766334 1152485 := bbase (se 4 (by rfl) ⟨108045, by rfl⟩ : syracuseStep 1152485 = 216091) (by norm_num)
theorem B1152509 : Blo 766334 1152509 := bbase (se 3 (by rfl) ⟨216095, by rfl⟩ : syracuseStep 1152509 = 432191) (by norm_num)
theorem B1152533 : Blo 766334 1152533 := bbase (se 6 (by rfl) ⟨27012, by rfl⟩ : syracuseStep 1152533 = 54025) (by norm_num)
theorem B1152557 : Blo 766334 1152557 := bbase (se 3 (by rfl) ⟨216104, by rfl⟩ : syracuseStep 1152557 = 432209) (by norm_num)
theorem B1152581 : Blo 766334 1152581 := bbase (se 4 (by rfl) ⟨108054, by rfl⟩ : syracuseStep 1152581 = 216109) (by norm_num)
theorem B1152605 : Blo 766334 1152605 := bbase (se 3 (by rfl) ⟨216113, by rfl⟩ : syracuseStep 1152605 = 432227) (by norm_num)
theorem B1152629 : Blo 766334 1152629 := bbase (se 5 (by rfl) ⟨54029, by rfl⟩ : syracuseStep 1152629 = 108059) (by norm_num)
theorem B1152653 : Blo 766334 1152653 := bbase (se 3 (by rfl) ⟨216122, by rfl⟩ : syracuseStep 1152653 = 432245) (by norm_num)
theorem B1152677 : Blo 766334 1152677 := bbase (se 4 (by rfl) ⟨108063, by rfl⟩ : syracuseStep 1152677 = 216127) (by norm_num)
theorem B1152701 : Blo 766334 1152701 := bbase (se 3 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 1152701 = 432263) (by norm_num)
theorem B1152725 : Blo 766334 1152725 := bbase (se 7 (by rfl) ⟨13508, by rfl⟩ : syracuseStep 1152725 = 27017) (by norm_num)
theorem B1152749 : Blo 766334 1152749 := bbase (se 3 (by rfl) ⟨216140, by rfl⟩ : syracuseStep 1152749 = 432281) (by norm_num)
theorem B1152773 : Blo 766334 1152773 := bbase (se 4 (by rfl) ⟨108072, by rfl⟩ : syracuseStep 1152773 = 216145) (by norm_num)
theorem B1152797 : Blo 766334 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B1644317 : Blo 766334 1644317 := bbase (se 3 (by rfl) ⟨308309, by rfl⟩ : syracuseStep 1644317 = 616619) (by norm_num)
theorem B1152821 : Blo 766334 1152821 := bbase (se 5 (by rfl) ⟨54038, by rfl⟩ : syracuseStep 1152821 = 108077) (by norm_num)
theorem B1152845 : Blo 766334 1152845 := bbase (se 3 (by rfl) ⟨216158, by rfl⟩ : syracuseStep 1152845 = 432317) (by norm_num)
theorem B2594645 : Blo 766334 2594645 := bbase (se 9 (by rfl) ⟨7601, by rfl⟩ : syracuseStep 2594645 = 15203) (by norm_num)
theorem B1152869 : Blo 766334 1152869 := bbase (se 4 (by rfl) ⟨108081, by rfl⟩ : syracuseStep 1152869 = 216163) (by norm_num)
theorem B2463605 : Blo 766334 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1152893 : Blo 766334 1152893 := bbase (se 3 (by rfl) ⟨216167, by rfl⟩ : syracuseStep 1152893 = 432335) (by norm_num)
theorem B1152917 : Blo 766334 1152917 := bbase (se 6 (by rfl) ⟨27021, by rfl⟩ : syracuseStep 1152917 = 54043) (by norm_num)
theorem B1644437 : Blo 766334 1644437 := bbase (se 6 (by rfl) ⟨38541, by rfl⟩ : syracuseStep 1644437 = 77083) (by norm_num)
theorem B1152941 : Blo 766334 1152941 := bbase (se 3 (by rfl) ⟨216176, by rfl⟩ : syracuseStep 1152941 = 432353) (by norm_num)
theorem B1152965 : Blo 766334 1152965 := bbase (se 4 (by rfl) ⟨108090, by rfl⟩ : syracuseStep 1152965 = 216181) (by norm_num)
theorem B13277141 : Blo 766334 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1152989 : Blo 766334 1152989 := bbase (se 3 (by rfl) ⟨216185, by rfl⟩ : syracuseStep 1152989 = 432371) (by norm_num)
theorem B1153013 : Blo 766334 1153013 := bbase (se 5 (by rfl) ⟨54047, by rfl⟩ : syracuseStep 1153013 = 108095) (by norm_num)
theorem B1153037 : Blo 766334 1153037 := bbase (se 3 (by rfl) ⟨216194, by rfl⟩ : syracuseStep 1153037 = 432389) (by norm_num)
theorem B1153061 : Blo 766334 1153061 := bbase (se 4 (by rfl) ⟨108099, by rfl⟩ : syracuseStep 1153061 = 216199) (by norm_num)
theorem B1153085 : Blo 766334 1153085 := bbase (se 3 (by rfl) ⟨216203, by rfl⟩ : syracuseStep 1153085 = 432407) (by norm_num)
theorem B1153109 : Blo 766334 1153109 := bbase (se 8 (by rfl) ⟨6756, by rfl⟩ : syracuseStep 1153109 = 13513) (by norm_num)
theorem B1153133 : Blo 766334 1153133 := bbase (se 3 (by rfl) ⟨216212, by rfl⟩ : syracuseStep 1153133 = 432425) (by norm_num)
theorem B1153157 : Blo 766334 1153157 := bbase (se 4 (by rfl) ⟨108108, by rfl⟩ : syracuseStep 1153157 = 216217) (by norm_num)
theorem B1153181 : Blo 766334 1153181 := bbase (se 3 (by rfl) ⟨216221, by rfl⟩ : syracuseStep 1153181 = 432443) (by norm_num)
theorem B2627749 : Blo 766334 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B1153205 : Blo 766334 1153205 := bbase (se 5 (by rfl) ⟨54056, by rfl⟩ : syracuseStep 1153205 = 108113) (by norm_num)
theorem B923833 : Blo 766334 923833 := bbase (se 2 (by rfl) ⟨346437, by rfl⟩ : syracuseStep 923833 = 692875) (by norm_num)
theorem B1153229 : Blo 766334 1153229 := bbase (se 3 (by rfl) ⟨216230, by rfl⟩ : syracuseStep 1153229 = 432461) (by norm_num)
theorem B1317077 : Blo 766334 1317077 := bbase (se 7 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 1317077 = 30869) (by norm_num)
theorem B1153253 : Blo 766334 1153253 := bbase (se 4 (by rfl) ⟨108117, by rfl⟩ : syracuseStep 1153253 = 216235) (by norm_num)
theorem B1153277 : Blo 766334 1153277 := bbase (se 3 (by rfl) ⟨216239, by rfl⟩ : syracuseStep 1153277 = 432479) (by norm_num)
theorem B923905 : Blo 766334 923905 := bbase (se 2 (by rfl) ⟨346464, by rfl⟩ : syracuseStep 923905 = 692929) (by norm_num)
theorem B2595077 : Blo 766334 2595077 := bbase (se 4 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 2595077 = 486577) (by norm_num)
theorem B1153301 : Blo 766334 1153301 := bbase (se 6 (by rfl) ⟨27030, by rfl⟩ : syracuseStep 1153301 = 54061) (by norm_num)
theorem B1841437 : Blo 766334 1841437 := bbase (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) (by norm_num)
theorem B1153325 : Blo 766334 1153325 := bbase (se 3 (by rfl) ⟨216248, by rfl⟩ : syracuseStep 1153325 = 432497) (by norm_num)
theorem B1153349 : Blo 766334 1153349 := bbase (se 4 (by rfl) ⟨108126, by rfl⟩ : syracuseStep 1153349 = 216253) (by norm_num)
theorem B1153373 : Blo 766334 1153373 := bbase (se 3 (by rfl) ⟨216257, by rfl⟩ : syracuseStep 1153373 = 432515) (by norm_num)
theorem B1382765 : Blo 766334 1382765 := bbase (se 3 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 1382765 = 518537) (by norm_num)
theorem B1153397 : Blo 766334 1153397 := bbase (se 5 (by rfl) ⟨54065, by rfl⟩ : syracuseStep 1153397 = 108131) (by norm_num)
theorem B1153421 : Blo 766334 1153421 := bbase (se 3 (by rfl) ⟨216266, by rfl⟩ : syracuseStep 1153421 = 432533) (by norm_num)
theorem B1317269 : Blo 766334 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B1153445 : Blo 766334 1153445 := bbase (se 4 (by rfl) ⟨108135, by rfl⟩ : syracuseStep 1153445 = 216271) (by norm_num)
theorem B7018933 : Blo 766334 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B1153469 : Blo 766334 1153469 := bbase (se 3 (by rfl) ⟨216275, by rfl⟩ : syracuseStep 1153469 = 432551) (by norm_num)
theorem B1939909 : Blo 766334 1939909 := bbase (se 4 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 1939909 = 363733) (by norm_num)
theorem B1153493 : Blo 766334 1153493 := bbase (se 7 (by rfl) ⟨13517, by rfl⟩ : syracuseStep 1153493 = 27035) (by norm_num)
theorem B1153517 : Blo 766334 1153517 := bbase (se 3 (by rfl) ⟨216284, by rfl⟩ : syracuseStep 1153517 = 432569) (by norm_num)
theorem B1841669 : Blo 766334 1841669 := bbase (se 4 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 1841669 = 345313) (by norm_num)
theorem B1153541 : Blo 766334 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B1645069 : Blo 766334 1645069 := bbase (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) (by norm_num)
theorem B1153565 : Blo 766334 1153565 := bbase (se 3 (by rfl) ⟨216293, by rfl⟩ : syracuseStep 1153565 = 432587) (by norm_num)
theorem B1940021 : Blo 766334 1940021 := bbase (se 5 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 1940021 = 181877) (by norm_num)
theorem B1153589 : Blo 766334 1153589 := bbase (se 5 (by rfl) ⟨54074, by rfl⟩ : syracuseStep 1153589 = 108149) (by norm_num)
theorem B1153613 : Blo 766334 1153613 := bbase (se 3 (by rfl) ⟨216302, by rfl⟩ : syracuseStep 1153613 = 432605) (by norm_num)
theorem B1153637 : Blo 766334 1153637 := bbase (se 4 (by rfl) ⟨108153, by rfl⟩ : syracuseStep 1153637 = 216307) (by norm_num)
theorem B1153661 : Blo 766334 1153661 := bbase (se 3 (by rfl) ⟨216311, by rfl⟩ : syracuseStep 1153661 = 432623) (by norm_num)
theorem B1153685 : Blo 766334 1153685 := bbase (se 6 (by rfl) ⟨27039, by rfl⟩ : syracuseStep 1153685 = 54079) (by norm_num)
theorem B1153709 : Blo 766334 1153709 := bbase (se 3 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 1153709 = 432641) (by norm_num)
theorem B2595509 : Blo 766334 2595509 := bbase (se 5 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 2595509 = 243329) (by norm_num)
theorem B1841861 : Blo 766334 1841861 := bbase (se 4 (by rfl) ⟨172674, by rfl⟩ : syracuseStep 1841861 = 345349) (by norm_num)
theorem B1153733 : Blo 766334 1153733 := bbase (se 4 (by rfl) ⟨108162, by rfl⟩ : syracuseStep 1153733 = 216325) (by norm_num)
theorem B1153757 : Blo 766334 1153757 := bbase (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) (by norm_num)
theorem B1940213 : Blo 766334 1940213 := bbase (se 5 (by rfl) ⟨90947, by rfl⟩ : syracuseStep 1940213 = 181895) (by norm_num)
theorem B1153781 : Blo 766334 1153781 := bbase (se 5 (by rfl) ⟨54083, by rfl⟩ : syracuseStep 1153781 = 108167) (by norm_num)
theorem B1153805 : Blo 766334 1153805 := bbase (se 3 (by rfl) ⟨216338, by rfl⟩ : syracuseStep 1153805 = 432677) (by norm_num)
theorem B1153829 : Blo 766334 1153829 := bbase (se 4 (by rfl) ⟨108171, by rfl⟩ : syracuseStep 1153829 = 216343) (by norm_num)
theorem B1153853 : Blo 766334 1153853 := bbase (se 3 (by rfl) ⟨216347, by rfl⟩ : syracuseStep 1153853 = 432695) (by norm_num)
theorem B1153877 : Blo 766334 1153877 := bbase (se 9 (by rfl) ⟨3380, by rfl⟩ : syracuseStep 1153877 = 6761) (by norm_num)
theorem B1383269 : Blo 766334 1383269 := bbase (se 4 (by rfl) ⟨129681, by rfl⟩ : syracuseStep 1383269 = 259363) (by norm_num)
theorem B1153901 : Blo 766334 1153901 := bbase (se 3 (by rfl) ⟨216356, by rfl⟩ : syracuseStep 1153901 = 432713) (by norm_num)
theorem B1153925 : Blo 766334 1153925 := bbase (se 4 (by rfl) ⟨108180, by rfl⟩ : syracuseStep 1153925 = 216361) (by norm_num)
theorem B2923397 : Blo 766334 2923397 := bbase (se 4 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 2923397 = 548137) (by norm_num)
theorem B1153949 : Blo 766334 1153949 := bbase (se 3 (by rfl) ⟨216365, by rfl⟩ : syracuseStep 1153949 = 432731) (by norm_num)
theorem B1153973 : Blo 766334 1153973 := bbase (se 5 (by rfl) ⟨54092, by rfl⟩ : syracuseStep 1153973 = 108185) (by norm_num)
theorem B1153997 : Blo 766334 1153997 := bbase (se 3 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 1153997 = 432749) (by norm_num)
theorem B1842149 : Blo 766334 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B1154021 : Blo 766334 1154021 := bbase (se 4 (by rfl) ⟨108189, by rfl⟩ : syracuseStep 1154021 = 216379) (by norm_num)
theorem B1154045 : Blo 766334 1154045 := bbase (se 3 (by rfl) ⟨216383, by rfl⟩ : syracuseStep 1154045 = 432767) (by norm_num)
theorem B1154069 : Blo 766334 1154069 := bbase (se 6 (by rfl) ⟨27048, by rfl⟩ : syracuseStep 1154069 = 54097) (by norm_num)
theorem B1154093 : Blo 766334 1154093 := bbase (se 3 (by rfl) ⟨216392, by rfl⟩ : syracuseStep 1154093 = 432785) (by norm_num)
theorem B1154117 : Blo 766334 1154117 := bbase (se 4 (by rfl) ⟨108198, by rfl⟩ : syracuseStep 1154117 = 216397) (by norm_num)
theorem B1940557 : Blo 766334 1940557 := bbase (se 3 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 1940557 = 727709) (by norm_num)
theorem B1154141 : Blo 766334 1154141 := bbase (se 3 (by rfl) ⟨216401, by rfl⟩ : syracuseStep 1154141 = 432803) (by norm_num)
theorem B2595941 : Blo 766334 2595941 := bbase (se 4 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 2595941 = 486739) (by norm_num)
theorem B1154165 : Blo 766334 1154165 := bbase (se 5 (by rfl) ⟨54101, by rfl⟩ : syracuseStep 1154165 = 108203) (by norm_num)
theorem B1875077 : Blo 766334 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B1154189 : Blo 766334 1154189 := bbase (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) (by norm_num)
theorem B1154213 : Blo 766334 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B2923685 : Blo 766334 2923685 := bbase (se 4 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 2923685 = 548191) (by norm_num)
theorem B1154237 : Blo 766334 1154237 := bbase (se 3 (by rfl) ⟨216419, by rfl⟩ : syracuseStep 1154237 = 432839) (by norm_num)
theorem B1940669 : Blo 766334 1940669 := bbase (se 3 (by rfl) ⟨363875, by rfl⟩ : syracuseStep 1940669 = 727751) (by norm_num)
theorem B1154261 : Blo 766334 1154261 := bbase (se 7 (by rfl) ⟨13526, by rfl⟩ : syracuseStep 1154261 = 27053) (by norm_num)
theorem B924905 : Blo 766334 924905 := bbase (se 2 (by rfl) ⟨346839, by rfl⟩ : syracuseStep 924905 = 693679) (by norm_num)
theorem B1154285 : Blo 766334 1154285 := bbase (se 3 (by rfl) ⟨216428, by rfl⟩ : syracuseStep 1154285 = 432857) (by norm_num)
theorem B1154309 : Blo 766334 1154309 := bbase (se 4 (by rfl) ⟨108216, by rfl⟩ : syracuseStep 1154309 = 216433) (by norm_num)
theorem B1154333 : Blo 766334 1154333 := bbase (se 3 (by rfl) ⟨216437, by rfl⟩ : syracuseStep 1154333 = 432875) (by norm_num)
theorem B1154357 : Blo 766334 1154357 := bbase (se 5 (by rfl) ⟨54110, by rfl⟩ : syracuseStep 1154357 = 108221) (by norm_num)
theorem B1154381 : Blo 766334 1154381 := bbase (se 3 (by rfl) ⟨216446, by rfl⟩ : syracuseStep 1154381 = 432893) (by norm_num)
theorem B1154405 : Blo 766334 1154405 := bbase (se 4 (by rfl) ⟨108225, by rfl⟩ : syracuseStep 1154405 = 216451) (by norm_num)
theorem B1940861 : Blo 766334 1940861 := bbase (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) (by norm_num)
theorem B1154429 : Blo 766334 1154429 := bbase (se 3 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 1154429 = 432911) (by norm_num)
theorem B1154453 : Blo 766334 1154453 := bbase (se 6 (by rfl) ⟨27057, by rfl⟩ : syracuseStep 1154453 = 54115) (by norm_num)
theorem B2956709 : Blo 766334 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B1154477 : Blo 766334 1154477 := bbase (se 3 (by rfl) ⟨216464, by rfl⟩ : syracuseStep 1154477 = 432929) (by norm_num)
theorem B3120565 : Blo 766334 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B1154501 : Blo 766334 1154501 := bbase (se 4 (by rfl) ⟨108234, by rfl⟩ : syracuseStep 1154501 = 216469) (by norm_num)
theorem B1154525 : Blo 766334 1154525 := bbase (se 3 (by rfl) ⟨216473, by rfl⟩ : syracuseStep 1154525 = 432947) (by norm_num)
theorem B2334197 : Blo 766334 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1154549 : Blo 766334 1154549 := bbase (se 5 (by rfl) ⟨54119, by rfl⟩ : syracuseStep 1154549 = 108239) (by norm_num)
theorem B1154573 : Blo 766334 1154573 := bbase (se 3 (by rfl) ⟨216482, by rfl⟩ : syracuseStep 1154573 = 432965) (by norm_num)
theorem B4365845 : Blo 766334 4365845 := bbase (se 6 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 4365845 = 204649) (by norm_num)
theorem B2596373 : Blo 766334 2596373 := bbase (se 6 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 2596373 = 121705) (by norm_num)
theorem B1154597 : Blo 766334 1154597 := bbase (se 4 (by rfl) ⟨108243, by rfl⟩ : syracuseStep 1154597 = 216487) (by norm_num)
theorem B1154621 : Blo 766334 1154621 := bbase (se 3 (by rfl) ⟨216491, by rfl⟩ : syracuseStep 1154621 = 432983) (by norm_num)
theorem B1384013 : Blo 766334 1384013 := bbase (se 3 (by rfl) ⟨259502, by rfl⟩ : syracuseStep 1384013 = 519005) (by norm_num)
theorem B1154645 : Blo 766334 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B1154669 : Blo 766334 1154669 := bbase (se 3 (by rfl) ⟨216500, by rfl⟩ : syracuseStep 1154669 = 433001) (by norm_num)
theorem B1154693 : Blo 766334 1154693 := bbase (se 4 (by rfl) ⟨108252, by rfl⟩ : syracuseStep 1154693 = 216505) (by norm_num)
theorem B1154717 : Blo 766334 1154717 := bbase (se 3 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 1154717 = 433019) (by norm_num)
theorem B1154741 : Blo 766334 1154741 := bbase (se 5 (by rfl) ⟨54128, by rfl⟩ : syracuseStep 1154741 = 108257) (by norm_num)
theorem B1154765 : Blo 766334 1154765 := bbase (se 3 (by rfl) ⟨216518, by rfl⟩ : syracuseStep 1154765 = 433037) (by norm_num)
theorem B1941205 : Blo 766334 1941205 := bbase (se 7 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 1941205 = 45497) (by norm_num)
theorem B1154789 : Blo 766334 1154789 := bbase (se 4 (by rfl) ⟨108261, by rfl⟩ : syracuseStep 1154789 = 216523) (by norm_num)
theorem B2072309 : Blo 766334 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B1154813 : Blo 766334 1154813 := bbase (se 3 (by rfl) ⟨216527, by rfl⟩ : syracuseStep 1154813 = 433055) (by norm_num)
theorem B1154837 : Blo 766334 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B1154861 : Blo 766334 1154861 := bbase (se 3 (by rfl) ⟨216536, by rfl⟩ : syracuseStep 1154861 = 433073) (by norm_num)
theorem B1941317 : Blo 766334 1941317 := bbase (se 4 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 1941317 = 363997) (by norm_num)
theorem B1154885 : Blo 766334 1154885 := bbase (se 4 (by rfl) ⟨108270, by rfl⟩ : syracuseStep 1154885 = 216541) (by norm_num)
theorem B4726613 : Blo 766334 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B1154909 : Blo 766334 1154909 := bbase (se 3 (by rfl) ⟨216545, by rfl⟩ : syracuseStep 1154909 = 433091) (by norm_num)
theorem B1154933 : Blo 766334 1154933 := bbase (se 5 (by rfl) ⟨54137, by rfl⟩ : syracuseStep 1154933 = 108275) (by norm_num)
theorem B1154957 : Blo 766334 1154957 := bbase (se 3 (by rfl) ⟨216554, by rfl⟩ : syracuseStep 1154957 = 433109) (by norm_num)
theorem B1154981 : Blo 766334 1154981 := bbase (se 4 (by rfl) ⟨108279, by rfl⟩ : syracuseStep 1154981 = 216559) (by norm_num)
theorem B1155005 : Blo 766334 1155005 := bbase (se 3 (by rfl) ⟨216563, by rfl⟩ : syracuseStep 1155005 = 433127) (by norm_num)
theorem B2596805 : Blo 766334 2596805 := bbase (se 4 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 2596805 = 486901) (by norm_num)
theorem B1155029 : Blo 766334 1155029 := bbase (se 7 (by rfl) ⟨13535, by rfl⟩ : syracuseStep 1155029 = 27071) (by norm_num)
theorem B1155053 : Blo 766334 1155053 := bbase (se 3 (by rfl) ⟨216572, by rfl⟩ : syracuseStep 1155053 = 433145) (by norm_num)
theorem B1941509 : Blo 766334 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B2465797 : Blo 766334 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B1155077 : Blo 766334 1155077 := bbase (se 4 (by rfl) ⟨108288, by rfl⟩ : syracuseStep 1155077 = 216577) (by norm_num)
theorem B1155101 : Blo 766334 1155101 := bbase (se 3 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 1155101 = 433163) (by norm_num)
theorem B1155125 : Blo 766334 1155125 := bbase (se 5 (by rfl) ⟨54146, by rfl⟩ : syracuseStep 1155125 = 108293) (by norm_num)
theorem B1351757 : Blo 766334 1351757 := bbase (se 3 (by rfl) ⟨253454, by rfl⟩ : syracuseStep 1351757 = 506909) (by norm_num)
theorem B1155149 : Blo 766334 1155149 := bbase (se 3 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 1155149 = 433181) (by norm_num)
theorem B1155173 : Blo 766334 1155173 := bbase (se 4 (by rfl) ⟨108297, by rfl⟩ : syracuseStep 1155173 = 216595) (by norm_num)
theorem B1155197 : Blo 766334 1155197 := bbase (se 3 (by rfl) ⟨216599, by rfl⟩ : syracuseStep 1155197 = 433199) (by norm_num)
theorem B1155221 : Blo 766334 1155221 := bbase (se 6 (by rfl) ⟨27075, by rfl⟩ : syracuseStep 1155221 = 54151) (by norm_num)
theorem B2498725 : Blo 766334 2498725 := bbase (se 4 (by rfl) ⟨234255, by rfl⟩ : syracuseStep 2498725 = 468511) (by norm_num)
theorem B1155245 : Blo 766334 1155245 := bbase (se 3 (by rfl) ⟨216608, by rfl⟩ : syracuseStep 1155245 = 433217) (by norm_num)
theorem B1155269 : Blo 766334 1155269 := bbase (se 4 (by rfl) ⟨108306, by rfl⟩ : syracuseStep 1155269 = 216613) (by norm_num)
theorem B1155293 : Blo 766334 1155293 := bbase (se 3 (by rfl) ⟨216617, by rfl⟩ : syracuseStep 1155293 = 433235) (by norm_num)
theorem B1155317 : Blo 766334 1155317 := bbase (se 5 (by rfl) ⟨54155, by rfl⟩ : syracuseStep 1155317 = 108311) (by norm_num)
theorem B1155341 : Blo 766334 1155341 := bbase (se 3 (by rfl) ⟨216626, by rfl⟩ : syracuseStep 1155341 = 433253) (by norm_num)
theorem B3285269 : Blo 766334 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B1155365 : Blo 766334 1155365 := bbase (se 4 (by rfl) ⟨108315, by rfl⟩ : syracuseStep 1155365 = 216631) (by norm_num)
theorem B1155389 : Blo 766334 1155389 := bbase (se 3 (by rfl) ⟨216635, by rfl⟩ : syracuseStep 1155389 = 433271) (by norm_num)
theorem B1155413 : Blo 766334 1155413 := bbase (se 10 (by rfl) ⟨1692, by rfl⟩ : syracuseStep 1155413 = 3385) (by norm_num)
theorem B1941853 : Blo 766334 1941853 := bbase (se 3 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 1941853 = 728195) (by norm_num)
theorem B1155437 : Blo 766334 1155437 := bbase (se 3 (by rfl) ⟨216644, by rfl⟩ : syracuseStep 1155437 = 433289) (by norm_num)
theorem B2597237 : Blo 766334 2597237 := bbase (se 5 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 2597237 = 243491) (by norm_num)
theorem B1155461 : Blo 766334 1155461 := bbase (se 4 (by rfl) ⟨108324, by rfl⟩ : syracuseStep 1155461 = 216649) (by norm_num)
theorem B1155485 : Blo 766334 1155485 := bbase (se 3 (by rfl) ⟨216653, by rfl⟩ : syracuseStep 1155485 = 433307) (by norm_num)
theorem B1941965 : Blo 766334 1941965 := bbase (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) (by norm_num)
theorem B1942157 : Blo 766334 1942157 := bbase (se 3 (by rfl) ⟨364154, by rfl⟩ : syracuseStep 1942157 = 728309) (by norm_num)
theorem B2597669 : Blo 766334 2597669 := bbase (se 4 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 2597669 = 487063) (by norm_num)
theorem B2466629 : Blo 766334 2466629 := bbase (se 4 (by rfl) ⟨231246, by rfl⟩ : syracuseStep 2466629 = 462493) (by norm_num)
theorem B1942501 : Blo 766334 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B1385461 : Blo 766334 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B1385533 : Blo 766334 1385533 := bbase (se 3 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 1385533 = 519575) (by norm_num)
theorem B1942613 : Blo 766334 1942613 := bbase (se 8 (by rfl) ⟨11382, by rfl⟩ : syracuseStep 1942613 = 22765) (by norm_num)
theorem B2598101 : Blo 766334 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B3286277 : Blo 766334 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B1942805 : Blo 766334 1942805 := bbase (se 6 (by rfl) ⟨45534, by rfl⟩ : syracuseStep 1942805 = 91069) (by norm_num)
theorem B4433173 : Blo 766334 4433173 := bbase (se 6 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 4433173 = 207805) (by norm_num)
theorem B1975853 : Blo 766334 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B1386037 : Blo 766334 1386037 := bbase (se 5 (by rfl) ⟨64970, by rfl⟩ : syracuseStep 1386037 = 129941) (by norm_num)
theorem B1975861 : Blo 766334 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B1943149 : Blo 766334 1943149 := bbase (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) (by norm_num)
theorem B2598533 : Blo 766334 2598533 := bbase (se 4 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 2598533 = 487225) (by norm_num)
theorem B1091245 : Blo 766334 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B1943261 : Blo 766334 1943261 := bbase (se 3 (by rfl) ⟨364361, by rfl⟩ : syracuseStep 1943261 = 728723) (by norm_num)
theorem B1943453 : Blo 766334 1943453 := bbase (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) (by norm_num)
theorem B862141 : Blo 766334 862141 := bbase (se 3 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 862141 = 323303) (by norm_num)
theorem B862177 : Blo 766334 862177 := bbase (se 2 (by rfl) ⟨323316, by rfl⟩ : syracuseStep 862177 = 646633) (by norm_num)
theorem B862213 : Blo 766334 862213 := bbase (se 4 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 862213 = 161665) (by norm_num)
theorem B862249 : Blo 766334 862249 := bbase (se 2 (by rfl) ⟨323343, by rfl⟩ : syracuseStep 862249 = 646687) (by norm_num)
theorem B2598965 : Blo 766334 2598965 := bbase (se 5 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 2598965 = 243653) (by norm_num)
theorem B862285 : Blo 766334 862285 := bbase (se 3 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 862285 = 323357) (by norm_num)
theorem B829549 : Blo 766334 829549 := bbase (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) (by norm_num)
theorem B862321 : Blo 766334 862321 := bbase (se 2 (by rfl) ⟨323370, by rfl⟩ : syracuseStep 862321 = 646741) (by norm_num)
theorem B862357 : Blo 766334 862357 := bbase (se 6 (by rfl) ⟨20211, by rfl⟩ : syracuseStep 862357 = 40423) (by norm_num)
theorem B862393 : Blo 766334 862393 := bbase (se 2 (by rfl) ⟨323397, by rfl⟩ : syracuseStep 862393 = 646795) (by norm_num)
theorem B1386701 : Blo 766334 1386701 := bbase (se 3 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 1386701 = 520013) (by norm_num)
theorem B862429 : Blo 766334 862429 := bbase (se 3 (by rfl) ⟨161705, by rfl⟩ : syracuseStep 862429 = 323411) (by norm_num)
theorem B1943797 : Blo 766334 1943797 := bbase (se 5 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 1943797 = 182231) (by norm_num)
theorem B1091837 : Blo 766334 1091837 := bbase (se 3 (by rfl) ⟨204719, by rfl⟩ : syracuseStep 1091837 = 409439) (by norm_num)
theorem B862465 : Blo 766334 862465 := bbase (se 2 (by rfl) ⟨323424, by rfl⟩ : syracuseStep 862465 = 646849) (by norm_num)
theorem B862501 : Blo 766334 862501 := bbase (se 4 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 862501 = 161719) (by norm_num)
theorem B862537 : Blo 766334 862537 := bbase (se 2 (by rfl) ⟨323451, by rfl⟩ : syracuseStep 862537 = 646903) (by norm_num)
theorem B1091917 : Blo 766334 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B1845589 : Blo 766334 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B1943909 : Blo 766334 1943909 := bbase (se 4 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 1943909 = 364483) (by norm_num)
theorem B862573 : Blo 766334 862573 := bbase (se 3 (by rfl) ⟨161732, by rfl⟩ : syracuseStep 862573 = 323465) (by norm_num)
theorem B862609 : Blo 766334 862609 := bbase (se 2 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 862609 = 646957) (by norm_num)
theorem B862645 : Blo 766334 862645 := bbase (se 5 (by rfl) ⟨40436, by rfl⟩ : syracuseStep 862645 = 80873) (by norm_num)
theorem B1092037 : Blo 766334 1092037 := bbase (se 4 (by rfl) ⟨102378, by rfl⟩ : syracuseStep 1092037 = 204757) (by norm_num)
theorem B862681 : Blo 766334 862681 := bbase (se 2 (by rfl) ⟨323505, by rfl⟩ : syracuseStep 862681 = 647011) (by norm_num)
theorem B2599397 : Blo 766334 2599397 := bbase (se 4 (by rfl) ⟨243693, by rfl⟩ : syracuseStep 2599397 = 487387) (by norm_num)
theorem B862717 : Blo 766334 862717 := bbase (se 3 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 862717 = 323519) (by norm_num)
theorem B862753 : Blo 766334 862753 := bbase (se 2 (by rfl) ⟨323532, by rfl⟩ : syracuseStep 862753 = 647065) (by norm_num)
theorem B1092133 : Blo 766334 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B1944101 : Blo 766334 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B3156533 : Blo 766334 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B1845821 : Blo 766334 1845821 := bbase (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) (by norm_num)
theorem B862789 : Blo 766334 862789 := bbase (se 4 (by rfl) ⟨80886, by rfl⟩ : syracuseStep 862789 = 161773) (by norm_num)
theorem B862825 : Blo 766334 862825 := bbase (se 2 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 862825 = 647119) (by norm_num)
theorem B862861 : Blo 766334 862861 := bbase (se 3 (by rfl) ⟨161786, by rfl⟩ : syracuseStep 862861 = 323573) (by norm_num)
theorem B862897 : Blo 766334 862897 := bbase (se 2 (by rfl) ⟨323586, by rfl⟩ : syracuseStep 862897 = 647173) (by norm_num)
theorem B1845965 : Blo 766334 1845965 := bbase (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) (by norm_num)
theorem B862933 : Blo 766334 862933 := bbase (se 7 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 862933 = 20225) (by norm_num)
theorem B862969 : Blo 766334 862969 := bbase (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) (by norm_num)
theorem B863005 : Blo 766334 863005 := bbase (se 3 (by rfl) ⟨161813, by rfl⟩ : syracuseStep 863005 = 323627) (by norm_num)
theorem B863041 : Blo 766334 863041 := bbase (se 2 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 863041 = 647281) (by norm_num)
theorem B863077 : Blo 766334 863077 := bbase (se 4 (by rfl) ⟨80913, by rfl⟩ : syracuseStep 863077 = 161827) (by norm_num)
theorem B1944445 : Blo 766334 1944445 := bbase (se 3 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 1944445 = 729167) (by norm_num)
theorem B863113 : Blo 766334 863113 := bbase (se 2 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 863113 = 647335) (by norm_num)
theorem B2599829 : Blo 766334 2599829 := bbase (se 6 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 2599829 = 121867) (by norm_num)
theorem B863149 : Blo 766334 863149 := bbase (se 3 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 863149 = 323681) (by norm_num)
theorem B1846205 : Blo 766334 1846205 := bbase (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) (by norm_num)
theorem B863185 : Blo 766334 863185 := bbase (se 2 (by rfl) ⟨323694, by rfl⟩ : syracuseStep 863185 = 647389) (by norm_num)
theorem B1944557 : Blo 766334 1944557 := bbase (se 3 (by rfl) ⟨364604, by rfl⟩ : syracuseStep 1944557 = 729209) (by norm_num)
theorem B863221 : Blo 766334 863221 := bbase (se 5 (by rfl) ⟨40463, by rfl⟩ : syracuseStep 863221 = 80927) (by norm_num)
theorem B3288053 : Blo 766334 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B1092629 : Blo 766334 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B863257 : Blo 766334 863257 := bbase (se 2 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 863257 = 647443) (by norm_num)
theorem B863293 : Blo 766334 863293 := bbase (se 3 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 863293 = 323735) (by norm_num)
theorem B863329 : Blo 766334 863329 := bbase (se 2 (by rfl) ⟨323748, by rfl⟩ : syracuseStep 863329 = 647497) (by norm_num)
theorem B863365 : Blo 766334 863365 := bbase (se 4 (by rfl) ⟨80940, by rfl⟩ : syracuseStep 863365 = 161881) (by norm_num)
theorem B863401 : Blo 766334 863401 := bbase (se 2 (by rfl) ⟨323775, by rfl⟩ : syracuseStep 863401 = 647551) (by norm_num)
theorem B1944749 : Blo 766334 1944749 := bbase (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) (by norm_num)
theorem B5844149 : Blo 766334 5844149 := bbase (se 5 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 5844149 = 547889) (by norm_num)
theorem B863437 : Blo 766334 863437 := bbase (se 3 (by rfl) ⟨161894, by rfl⟩ : syracuseStep 863437 = 323789) (by norm_num)
theorem B863473 : Blo 766334 863473 := bbase (se 2 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 863473 = 647605) (by norm_num)
theorem B863509 : Blo 766334 863509 := bbase (se 6 (by rfl) ⟨20238, by rfl⟩ : syracuseStep 863509 = 40477) (by norm_num)
theorem B863545 : Blo 766334 863545 := bbase (se 2 (by rfl) ⟨323829, by rfl⟩ : syracuseStep 863545 = 647659) (by norm_num)
theorem B1748285 : Blo 766334 1748285 := bbase (se 3 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 1748285 = 655607) (by norm_num)
theorem B863581 : Blo 766334 863581 := bbase (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) (by norm_num)
theorem B863617 : Blo 766334 863617 := bbase (se 2 (by rfl) ⟨323856, by rfl⟩ : syracuseStep 863617 = 647713) (by norm_num)
theorem B863653 : Blo 766334 863653 := bbase (se 4 (by rfl) ⟨80967, by rfl⟩ : syracuseStep 863653 = 161935) (by norm_num)
theorem B4926901 : Blo 766334 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B863689 : Blo 766334 863689 := bbase (se 2 (by rfl) ⟨323883, by rfl⟩ : syracuseStep 863689 = 647767) (by norm_num)
theorem B863725 : Blo 766334 863725 := bbase (se 3 (by rfl) ⟨161948, by rfl⟩ : syracuseStep 863725 = 323897) (by norm_num)
theorem B1945093 : Blo 766334 1945093 := bbase (se 4 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 1945093 = 364705) (by norm_num)
theorem B863761 : Blo 766334 863761 := bbase (se 2 (by rfl) ⟨323910, by rfl⟩ : syracuseStep 863761 = 647821) (by norm_num)
theorem B863797 : Blo 766334 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B1093181 : Blo 766334 1093181 := bbase (se 3 (by rfl) ⟨204971, by rfl⟩ : syracuseStep 1093181 = 409943) (by norm_num)
theorem B863833 : Blo 766334 863833 := bbase (se 2 (by rfl) ⟨323937, by rfl⟩ : syracuseStep 863833 = 647875) (by norm_num)
theorem B1945205 : Blo 766334 1945205 := bbase (se 5 (by rfl) ⟨91181, by rfl⟩ : syracuseStep 1945205 = 182363) (by norm_num)
theorem B863869 : Blo 766334 863869 := bbase (se 3 (by rfl) ⟨161975, by rfl⟩ : syracuseStep 863869 = 323951) (by norm_num)
theorem B863905 : Blo 766334 863905 := bbase (se 2 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 863905 = 647929) (by norm_num)
theorem B1846973 : Blo 766334 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B863941 : Blo 766334 863941 := bbase (se 4 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 863941 = 161989) (by norm_num)
theorem B3550949 : Blo 766334 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B863977 : Blo 766334 863977 := bbase (se 2 (by rfl) ⟨323991, by rfl⟩ : syracuseStep 863977 = 647983) (by norm_num)
theorem B864013 : Blo 766334 864013 := bbase (se 3 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 864013 = 324005) (by norm_num)
theorem B864049 : Blo 766334 864049 := bbase (se 2 (by rfl) ⟨324018, by rfl⟩ : syracuseStep 864049 = 648037) (by norm_num)
theorem B1945397 : Blo 766334 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B864085 : Blo 766334 864085 := bbase (se 9 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 864085 = 5063) (by norm_num)
theorem B4665205 : Blo 766334 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B864121 : Blo 766334 864121 := bbase (se 2 (by rfl) ⟨324045, by rfl⟩ : syracuseStep 864121 = 648091) (by norm_num)
theorem B2764693 : Blo 766334 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B864157 : Blo 766334 864157 := bbase (se 3 (by rfl) ⟨162029, by rfl⟩ : syracuseStep 864157 = 324059) (by norm_num)
theorem B864193 : Blo 766334 864193 := bbase (se 2 (by rfl) ⟨324072, by rfl⟩ : syracuseStep 864193 = 648145) (by norm_num)
theorem B864229 : Blo 766334 864229 := bbase (se 4 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 864229 = 162043) (by norm_num)
theorem B864265 : Blo 766334 864265 := bbase (se 2 (by rfl) ⟨324099, by rfl⟩ : syracuseStep 864265 = 648199) (by norm_num)
theorem B864301 : Blo 766334 864301 := bbase (se 3 (by rfl) ⟨162056, by rfl⟩ : syracuseStep 864301 = 324113) (by norm_num)
theorem B864337 : Blo 766334 864337 := bbase (se 2 (by rfl) ⟨324126, by rfl⟩ : syracuseStep 864337 = 648253) (by norm_num)
theorem B864373 : Blo 766334 864373 := bbase (se 5 (by rfl) ⟨40517, by rfl⟩ : syracuseStep 864373 = 81035) (by norm_num)
theorem B1945741 : Blo 766334 1945741 := bbase (se 3 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 1945741 = 729653) (by norm_num)
theorem B864409 : Blo 766334 864409 := bbase (se 2 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 864409 = 648307) (by norm_num)
theorem B864445 : Blo 766334 864445 := bbase (se 3 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 864445 = 324167) (by norm_num)
theorem B864481 : Blo 766334 864481 := bbase (se 2 (by rfl) ⟨324180, by rfl⟩ : syracuseStep 864481 = 648361) (by norm_num)
theorem B1945853 : Blo 766334 1945853 := bbase (se 3 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 1945853 = 729695) (by norm_num)
theorem B864517 : Blo 766334 864517 := bbase (se 4 (by rfl) ⟨81048, by rfl⟩ : syracuseStep 864517 = 162097) (by norm_num)
theorem B864553 : Blo 766334 864553 := bbase (se 2 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 864553 = 648415) (by norm_num)
theorem B1093933 : Blo 766334 1093933 := bbase (se 3 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 1093933 = 410225) (by norm_num)
theorem B864589 : Blo 766334 864589 := bbase (se 3 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 864589 = 324221) (by norm_num)
theorem B864625 : Blo 766334 864625 := bbase (se 2 (by rfl) ⟨324234, by rfl⟩ : syracuseStep 864625 = 648469) (by norm_num)
theorem B864661 : Blo 766334 864661 := bbase (se 6 (by rfl) ⟨20265, by rfl⟩ : syracuseStep 864661 = 40531) (by norm_num)
theorem B864697 : Blo 766334 864697 := bbase (se 2 (by rfl) ⟨324261, by rfl⟩ : syracuseStep 864697 = 648523) (by norm_num)
theorem B1946045 : Blo 766334 1946045 := bbase (se 3 (by rfl) ⟨364883, by rfl⟩ : syracuseStep 1946045 = 729767) (by norm_num)
theorem B8729045 : Blo 766334 8729045 := bbase (se 7 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 8729045 = 204587) (by norm_num)
theorem B864733 : Blo 766334 864733 := bbase (se 3 (by rfl) ⟨162137, by rfl⟩ : syracuseStep 864733 = 324275) (by norm_num)
theorem B864769 : Blo 766334 864769 := bbase (se 2 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 864769 = 648577) (by norm_num)
theorem B864805 : Blo 766334 864805 := bbase (se 4 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 864805 = 162151) (by norm_num)
theorem B864841 : Blo 766334 864841 := bbase (se 2 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 864841 = 648631) (by norm_num)
theorem B864877 : Blo 766334 864877 := bbase (se 3 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 864877 = 324329) (by norm_num)
theorem B864913 : Blo 766334 864913 := bbase (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) (by norm_num)
theorem B832177 : Blo 766334 832177 := bbase (se 2 (by rfl) ⟨312066, by rfl⟩ : syracuseStep 832177 = 624133) (by norm_num)
theorem B864949 : Blo 766334 864949 := bbase (se 5 (by rfl) ⟨40544, by rfl⟩ : syracuseStep 864949 = 81089) (by norm_num)
theorem B3683029 : Blo 766334 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B864985 : Blo 766334 864985 := bbase (se 2 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 864985 = 648739) (by norm_num)
theorem B865021 : Blo 766334 865021 := bbase (se 3 (by rfl) ⟨162191, by rfl⟩ : syracuseStep 865021 = 324383) (by norm_num)
theorem B1946389 : Blo 766334 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B865057 : Blo 766334 865057 := bbase (se 2 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 865057 = 648793) (by norm_num)
theorem B1454917 : Blo 766334 1454917 := bbase (se 4 (by rfl) ⟨136398, by rfl⟩ : syracuseStep 1454917 = 272797) (by norm_num)
theorem B865093 : Blo 766334 865093 := bbase (se 4 (by rfl) ⟨81102, by rfl⟩ : syracuseStep 865093 = 162205) (by norm_num)
theorem B6566741 : Blo 766334 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B865129 : Blo 766334 865129 := bbase (se 2 (by rfl) ⟨324423, by rfl⟩ : syracuseStep 865129 = 648847) (by norm_num)
theorem B1946501 : Blo 766334 1946501 := bbase (se 4 (by rfl) ⟨182484, by rfl⟩ : syracuseStep 1946501 = 364969) (by norm_num)
theorem B865165 : Blo 766334 865165 := bbase (se 3 (by rfl) ⟨162218, by rfl⟩ : syracuseStep 865165 = 324437) (by norm_num)
theorem B865201 : Blo 766334 865201 := bbase (se 2 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 865201 = 648901) (by norm_num)
theorem B865237 : Blo 766334 865237 := bbase (se 7 (by rfl) ⟨10139, by rfl⟩ : syracuseStep 865237 = 20279) (by norm_num)
theorem B1455077 : Blo 766334 1455077 := bbase (se 4 (by rfl) ⟨136413, by rfl⟩ : syracuseStep 1455077 = 272827) (by norm_num)
theorem B865273 : Blo 766334 865273 := bbase (se 2 (by rfl) ⟨324477, by rfl⟩ : syracuseStep 865273 = 648955) (by norm_num)
theorem B865309 : Blo 766334 865309 := bbase (se 3 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 865309 = 324491) (by norm_num)
theorem B1848349 : Blo 766334 1848349 := bbase (se 3 (by rfl) ⟨346565, by rfl⟩ : syracuseStep 1848349 = 693131) (by norm_num)
theorem B865345 : Blo 766334 865345 := bbase (se 2 (by rfl) ⟨324504, by rfl⟩ : syracuseStep 865345 = 649009) (by norm_num)
theorem B1094725 : Blo 766334 1094725 := bbase (se 4 (by rfl) ⟨102630, by rfl⟩ : syracuseStep 1094725 = 205261) (by norm_num)
theorem B1946693 : Blo 766334 1946693 := bbase (se 4 (by rfl) ⟨182502, by rfl⟩ : syracuseStep 1946693 = 365005) (by norm_num)
theorem B865381 : Blo 766334 865381 := bbase (se 4 (by rfl) ⟨81129, by rfl⟩ : syracuseStep 865381 = 162259) (by norm_num)
theorem B1455221 : Blo 766334 1455221 := bbase (se 5 (by rfl) ⟨68213, by rfl⟩ : syracuseStep 1455221 = 136427) (by norm_num)
theorem B865417 : Blo 766334 865417 := bbase (se 2 (by rfl) ⟨324531, by rfl⟩ : syracuseStep 865417 = 649063) (by norm_num)
theorem B3323045 : Blo 766334 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B865453 : Blo 766334 865453 := bbase (se 3 (by rfl) ⟨162272, by rfl⟩ : syracuseStep 865453 = 324545) (by norm_num)
theorem B865489 : Blo 766334 865489 := bbase (se 2 (by rfl) ⟨324558, by rfl⟩ : syracuseStep 865489 = 649117) (by norm_num)
theorem B865525 : Blo 766334 865525 := bbase (se 5 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 865525 = 81143) (by norm_num)
theorem B865561 : Blo 766334 865561 := bbase (se 2 (by rfl) ⟨324585, by rfl⟩ : syracuseStep 865561 = 649171) (by norm_num)
theorem B865597 : Blo 766334 865597 := bbase (se 3 (by rfl) ⟨162299, by rfl⟩ : syracuseStep 865597 = 324599) (by norm_num)
theorem B865633 : Blo 766334 865633 := bbase (se 2 (by rfl) ⟨324612, by rfl⟩ : syracuseStep 865633 = 649225) (by norm_num)
theorem B865669 : Blo 766334 865669 := bbase (se 4 (by rfl) ⟨81156, by rfl⟩ : syracuseStep 865669 = 162313) (by norm_num)
theorem B1455509 : Blo 766334 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B1095061 : Blo 766334 1095061 := bbase (se 6 (by rfl) ⟨25665, by rfl⟩ : syracuseStep 1095061 = 51331) (by norm_num)
theorem B1947037 : Blo 766334 1947037 := bbase (se 3 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 1947037 = 730139) (by norm_num)
theorem B865705 : Blo 766334 865705 := bbase (se 2 (by rfl) ⟨324639, by rfl⟩ : syracuseStep 865705 = 649279) (by norm_num)
theorem B865741 : Blo 766334 865741 := bbase (se 3 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 865741 = 324653) (by norm_num)
theorem B833009 : Blo 766334 833009 := bbase (se 2 (by rfl) ⟨312378, by rfl⟩ : syracuseStep 833009 = 624757) (by norm_num)
theorem B865777 : Blo 766334 865777 := bbase (se 2 (by rfl) ⟨324666, by rfl⟩ : syracuseStep 865777 = 649333) (by norm_num)
theorem B1947149 : Blo 766334 1947149 := bbase (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) (by norm_num)
theorem B1553941 : Blo 766334 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B865813 : Blo 766334 865813 := bbase (se 6 (by rfl) ⟨20292, by rfl⟩ : syracuseStep 865813 = 40585) (by norm_num)
theorem B1455661 : Blo 766334 1455661 := bbase (se 3 (by rfl) ⟨272936, by rfl⟩ : syracuseStep 1455661 = 545873) (by norm_num)
theorem B865849 : Blo 766334 865849 := bbase (se 2 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 865849 = 649387) (by norm_num)
theorem B865885 : Blo 766334 865885 := bbase (se 3 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 865885 = 324707) (by norm_num)
theorem B1095277 : Blo 766334 1095277 := bbase (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) (by norm_num)
theorem B865921 : Blo 766334 865921 := bbase (se 2 (by rfl) ⟨324720, by rfl⟩ : syracuseStep 865921 = 649441) (by norm_num)
theorem B865957 : Blo 766334 865957 := bbase (se 4 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 865957 = 162367) (by norm_num)
theorem B865993 : Blo 766334 865993 := bbase (se 2 (by rfl) ⟨324747, by rfl⟩ : syracuseStep 865993 = 649495) (by norm_num)
theorem B1947341 : Blo 766334 1947341 := bbase (se 3 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 1947341 = 730253) (by norm_num)
theorem B866029 : Blo 766334 866029 := bbase (se 3 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 866029 = 324761) (by norm_num)
theorem B3880709 : Blo 766334 3880709 := bbase (se 4 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 3880709 = 727633) (by norm_num)
theorem B866065 : Blo 766334 866065 := bbase (se 2 (by rfl) ⟨324774, by rfl⟩ : syracuseStep 866065 = 649549) (by norm_num)
theorem B866101 : Blo 766334 866101 := bbase (se 5 (by rfl) ⟨40598, by rfl⟩ : syracuseStep 866101 = 81197) (by norm_num)
theorem B866137 : Blo 766334 866137 := bbase (se 2 (by rfl) ⟨324801, by rfl⟩ : syracuseStep 866137 = 649603) (by norm_num)
theorem B1455965 : Blo 766334 1455965 := bbase (se 3 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 1455965 = 545987) (by norm_num)
theorem B866173 : Blo 766334 866173 := bbase (se 3 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 866173 = 324815) (by norm_num)
theorem B866209 : Blo 766334 866209 := bbase (se 2 (by rfl) ⟨324828, by rfl⟩ : syracuseStep 866209 = 649657) (by norm_num)
theorem B866245 : Blo 766334 866245 := bbase (se 4 (by rfl) ⟨81210, by rfl⟩ : syracuseStep 866245 = 162421) (by norm_num)
theorem B1095653 : Blo 766334 1095653 := bbase (se 4 (by rfl) ⟨102717, by rfl⟩ : syracuseStep 1095653 = 205435) (by norm_num)
theorem B866281 : Blo 766334 866281 := bbase (se 2 (by rfl) ⟨324855, by rfl⟩ : syracuseStep 866281 = 649711) (by norm_num)
theorem B866317 : Blo 766334 866317 := bbase (se 3 (by rfl) ⟨162434, by rfl⟩ : syracuseStep 866317 = 324869) (by norm_num)
theorem B1947685 : Blo 766334 1947685 := bbase (se 4 (by rfl) ⟨182595, by rfl⟩ : syracuseStep 1947685 = 365191) (by norm_num)
theorem B866353 : Blo 766334 866353 := bbase (se 2 (by rfl) ⟨324882, by rfl⟩ : syracuseStep 866353 = 649765) (by norm_num)
theorem B1554509 : Blo 766334 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B866389 : Blo 766334 866389 := bbase (se 8 (by rfl) ⟨5076, by rfl⟩ : syracuseStep 866389 = 10153) (by norm_num)
theorem B866425 : Blo 766334 866425 := bbase (se 2 (by rfl) ⟨324909, by rfl⟩ : syracuseStep 866425 = 649819) (by norm_num)
theorem B1947797 : Blo 766334 1947797 := bbase (se 6 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 1947797 = 91303) (by norm_num)
theorem B866461 : Blo 766334 866461 := bbase (se 3 (by rfl) ⟨162461, by rfl⟩ : syracuseStep 866461 = 324923) (by norm_num)
theorem B2078885 : Blo 766334 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B866497 : Blo 766334 866497 := bbase (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) (by norm_num)
theorem B1849549 : Blo 766334 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B866533 : Blo 766334 866533 := bbase (se 4 (by rfl) ⟨81237, by rfl⟩ : syracuseStep 866533 = 162475) (by norm_num)
theorem B866569 : Blo 766334 866569 := bbase (se 2 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 866569 = 649927) (by norm_num)
theorem B866605 : Blo 766334 866605 := bbase (se 3 (by rfl) ⟨162488, by rfl⟩ : syracuseStep 866605 = 324977) (by norm_num)
theorem B1947989 : Blo 766334 1947989 := bbase (se 10 (by rfl) ⟨2853, by rfl⟩ : syracuseStep 1947989 = 5707) (by norm_num)
theorem B1456717 : Blo 766334 1456717 := bbase (se 3 (by rfl) ⟨273134, by rfl⟩ : syracuseStep 1456717 = 546269) (by norm_num)
theorem B1555109 : Blo 766334 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1948333 : Blo 766334 1948333 := bbase (se 3 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 1948333 = 730625) (by norm_num)
theorem B1456861 : Blo 766334 1456861 := bbase (se 3 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 1456861 = 546323) (by norm_num)
theorem B1555205 : Blo 766334 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B1948445 : Blo 766334 1948445 := bbase (se 3 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 1948445 = 730667) (by norm_num)
theorem B1850165 : Blo 766334 1850165 := bbase (se 5 (by rfl) ⟨86726, by rfl⟩ : syracuseStep 1850165 = 173453) (by norm_num)
theorem B1457021 : Blo 766334 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B1751941 : Blo 766334 1751941 := bbase (se 4 (by rfl) ⟨164244, by rfl⟩ : syracuseStep 1751941 = 328489) (by norm_num)
theorem B1293205 : Blo 766334 1293205 := bbase (se 6 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 1293205 = 60619) (by norm_num)
theorem B1948637 : Blo 766334 1948637 := bbase (se 3 (by rfl) ⟨365369, by rfl⟩ : syracuseStep 1948637 = 730739) (by norm_num)
theorem B1293293 : Blo 766334 1293293 := bbase (se 3 (by rfl) ⟨242492, by rfl⟩ : syracuseStep 1293293 = 484985) (by norm_num)
theorem B1850357 : Blo 766334 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B1227773 : Blo 766334 1227773 := bbase (se 3 (by rfl) ⟨230207, by rfl⟩ : syracuseStep 1227773 = 460415) (by norm_num)
theorem B2079749 : Blo 766334 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B1457165 : Blo 766334 1457165 := bbase (se 3 (by rfl) ⟨273218, by rfl⟩ : syracuseStep 1457165 = 546437) (by norm_num)
theorem B3882005 : Blo 766334 3882005 := bbase (se 6 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 3882005 = 181969) (by norm_num)
theorem B1850453 : Blo 766334 1850453 := bbase (se 8 (by rfl) ⟨10842, by rfl⟩ : syracuseStep 1850453 = 21685) (by norm_num)
theorem B1293421 : Blo 766334 1293421 := bbase (se 3 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 1293421 = 485033) (by norm_num)
theorem B1293509 : Blo 766334 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B1227997 : Blo 766334 1227997 := bbase (se 3 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 1227997 = 460499) (by norm_num)
theorem B1228061 : Blo 766334 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1457453 : Blo 766334 1457453 := bbase (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) (by norm_num)
theorem B1948981 : Blo 766334 1948981 := bbase (se 5 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 1948981 = 182717) (by norm_num)
theorem B1293637 : Blo 766334 1293637 := bbase (se 4 (by rfl) ⟨121278, by rfl⟩ : syracuseStep 1293637 = 242557) (by norm_num)
theorem B4930901 : Blo 766334 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B4373909 : Blo 766334 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B1293725 : Blo 766334 1293725 := bbase (se 3 (by rfl) ⟨242573, by rfl⟩ : syracuseStep 1293725 = 485147) (by norm_num)
theorem B1228189 : Blo 766334 1228189 := bbase (se 3 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 1228189 = 460571) (by norm_num)
theorem B1949093 : Blo 766334 1949093 := bbase (se 4 (by rfl) ⟨182727, by rfl⟩ : syracuseStep 1949093 = 365455) (by norm_num)
theorem B2080181 : Blo 766334 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B1457605 : Blo 766334 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B1293853 : Blo 766334 1293853 := bbase (se 3 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 1293853 = 485195) (by norm_num)
theorem B1949285 : Blo 766334 1949285 := bbase (se 4 (by rfl) ⟨182745, by rfl⟩ : syracuseStep 1949285 = 365491) (by norm_num)
theorem B1293941 : Blo 766334 1293941 := bbase (se 5 (by rfl) ⟨60653, by rfl⟩ : syracuseStep 1293941 = 121307) (by norm_num)
theorem B1294069 : Blo 766334 1294069 := bbase (se 5 (by rfl) ⟨60659, by rfl⟩ : syracuseStep 1294069 = 121319) (by norm_num)
theorem B1457909 : Blo 766334 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B1294157 : Blo 766334 1294157 := bbase (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) (by norm_num)
theorem B1556309 : Blo 766334 1556309 := bbase (se 9 (by rfl) ⟨4559, by rfl⟩ : syracuseStep 1556309 = 9119) (by norm_num)
theorem B2080613 : Blo 766334 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B1949629 : Blo 766334 1949629 := bbase (se 3 (by rfl) ⟨365555, by rfl⟩ : syracuseStep 1949629 = 731111) (by norm_num)
theorem B1294285 : Blo 766334 1294285 := bbase (se 3 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 1294285 = 485357) (by norm_num)
theorem B1294373 : Blo 766334 1294373 := bbase (se 4 (by rfl) ⟨121347, by rfl⟩ : syracuseStep 1294373 = 242695) (by norm_num)
theorem B1949741 : Blo 766334 1949741 := bbase (se 3 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 1949741 = 731153) (by norm_num)
theorem B1294501 : Blo 766334 1294501 := bbase (se 4 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 1294501 = 242719) (by norm_num)
theorem B1294589 : Blo 766334 1294589 := bbase (se 3 (by rfl) ⟨242735, by rfl⟩ : syracuseStep 1294589 = 485471) (by norm_num)
theorem B3883301 : Blo 766334 3883301 := bbase (se 4 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 3883301 = 728119) (by norm_num)
theorem B2769221 : Blo 766334 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1294717 : Blo 766334 1294717 := bbase (se 3 (by rfl) ⟨242759, by rfl⟩ : syracuseStep 1294717 = 485519) (by norm_num)
theorem B1294805 : Blo 766334 1294805 := bbase (se 7 (by rfl) ⟨15173, by rfl⟩ : syracuseStep 1294805 = 30347) (by norm_num)
theorem B1458661 : Blo 766334 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B4375093 : Blo 766334 4375093 := bbase (se 5 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 4375093 = 410165) (by norm_num)
theorem B1294933 : Blo 766334 1294933 := bbase (se 8 (by rfl) ⟨7587, by rfl⟩ : syracuseStep 1294933 = 15175) (by norm_num)
theorem B1229413 : Blo 766334 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1458805 : Blo 766334 1458805 := bbase (se 5 (by rfl) ⟨68381, by rfl⟩ : syracuseStep 1458805 = 136763) (by norm_num)
theorem B1295021 : Blo 766334 1295021 := bbase (se 3 (by rfl) ⟨242816, by rfl⟩ : syracuseStep 1295021 = 485633) (by norm_num)
theorem B2769653 : Blo 766334 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1458965 : Blo 766334 1458965 := bbase (se 6 (by rfl) ⟨34194, by rfl⟩ : syracuseStep 1458965 = 68389) (by norm_num)
theorem B1295149 : Blo 766334 1295149 := bbase (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) (by norm_num)
theorem B3687221 : Blo 766334 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B1295237 : Blo 766334 1295237 := bbase (se 4 (by rfl) ⟨121428, by rfl⟩ : syracuseStep 1295237 = 242857) (by norm_num)
theorem B1459109 : Blo 766334 1459109 := bbase (se 4 (by rfl) ⟨136791, by rfl⟩ : syracuseStep 1459109 = 273583) (by norm_num)
theorem B1000369 : Blo 766334 1000369 := bbase (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) (by norm_num)
theorem B1557469 : Blo 766334 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B1295365 : Blo 766334 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B1295453 : Blo 766334 1295453 := bbase (se 3 (by rfl) ⟨242897, by rfl⟩ : syracuseStep 1295453 = 485795) (by norm_num)
theorem B1459397 : Blo 766334 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B1295581 : Blo 766334 1295581 := bbase (se 3 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 1295581 = 485843) (by norm_num)
theorem B1230085 : Blo 766334 1230085 := bbase (se 4 (by rfl) ⟨115320, by rfl⟩ : syracuseStep 1230085 = 230641) (by norm_num)
theorem B1295669 : Blo 766334 1295669 := bbase (se 5 (by rfl) ⟨60734, by rfl⟩ : syracuseStep 1295669 = 121469) (by norm_num)
theorem B2770229 : Blo 766334 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B1459549 : Blo 766334 1459549 := bbase (se 3 (by rfl) ⟨273665, by rfl⟩ : syracuseStep 1459549 = 547331) (by norm_num)
theorem B1295797 : Blo 766334 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B1295885 : Blo 766334 1295885 := bbase (se 3 (by rfl) ⟨242978, by rfl⟩ : syracuseStep 1295885 = 485957) (by norm_num)
theorem B3884597 : Blo 766334 3884597 := bbase (se 5 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 3884597 = 364181) (by norm_num)
theorem B1296013 : Blo 766334 1296013 := bbase (se 3 (by rfl) ⟨243002, by rfl⟩ : syracuseStep 1296013 = 486005) (by norm_num)
theorem B1459853 : Blo 766334 1459853 := bbase (se 3 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 1459853 = 547445) (by norm_num)
theorem B1296101 : Blo 766334 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B1296229 : Blo 766334 1296229 := bbase (se 4 (by rfl) ⟨121521, by rfl⟩ : syracuseStep 1296229 = 243043) (by norm_num)
theorem B1296317 : Blo 766334 1296317 := bbase (se 3 (by rfl) ⟨243059, by rfl⟩ : syracuseStep 1296317 = 486119) (by norm_num)
theorem B1296445 : Blo 766334 1296445 := bbase (se 3 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 1296445 = 486167) (by norm_num)
theorem B1296533 : Blo 766334 1296533 := bbase (se 6 (by rfl) ⟨30387, by rfl⟩ : syracuseStep 1296533 = 60775) (by norm_num)
theorem B1231085 : Blo 766334 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B1296661 : Blo 766334 1296661 := bbase (se 6 (by rfl) ⟨30390, by rfl⟩ : syracuseStep 1296661 = 60781) (by norm_num)
theorem B1755445 : Blo 766334 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B1296749 : Blo 766334 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B1460605 : Blo 766334 1460605 := bbase (se 3 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 1460605 = 547727) (by norm_num)
theorem B1296877 : Blo 766334 1296877 := bbase (se 3 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 1296877 = 486329) (by norm_num)
theorem B4377077 : Blo 766334 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B1460749 : Blo 766334 1460749 := bbase (se 3 (by rfl) ⟨273890, by rfl⟩ : syracuseStep 1460749 = 547781) (by norm_num)
theorem B1296965 : Blo 766334 1296965 := bbase (se 4 (by rfl) ⟨121590, by rfl⟩ : syracuseStep 1296965 = 243181) (by norm_num)
theorem B1460909 : Blo 766334 1460909 := bbase (se 3 (by rfl) ⟨273920, by rfl⟩ : syracuseStep 1460909 = 547841) (by norm_num)
theorem B1297093 : Blo 766334 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B1297181 : Blo 766334 1297181 := bbase (se 3 (by rfl) ⟨243221, by rfl⟩ : syracuseStep 1297181 = 486443) (by norm_num)
theorem B1461053 : Blo 766334 1461053 := bbase (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) (by norm_num)
theorem B3885893 : Blo 766334 3885893 := bbase (se 4 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 3885893 = 728605) (by norm_num)
theorem B1297309 : Blo 766334 1297309 := bbase (se 3 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 1297309 = 486491) (by norm_num)
theorem B1297397 : Blo 766334 1297397 := bbase (se 5 (by rfl) ⟨60815, by rfl⟩ : syracuseStep 1297397 = 121631) (by norm_num)
theorem B1461341 : Blo 766334 1461341 := bbase (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) (by norm_num)
theorem B1068133 : Blo 766334 1068133 := bbase (se 4 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 1068133 = 200275) (by norm_num)
theorem B1297525 : Blo 766334 1297525 := bbase (se 5 (by rfl) ⟨60821, by rfl⟩ : syracuseStep 1297525 = 121643) (by norm_num)
theorem B1297613 : Blo 766334 1297613 := bbase (se 3 (by rfl) ⟨243302, by rfl⟩ : syracuseStep 1297613 = 486605) (by norm_num)
theorem B1461493 : Blo 766334 1461493 := bbase (se 5 (by rfl) ⟨68507, by rfl⟩ : syracuseStep 1461493 = 137015) (by norm_num)
theorem B969985 : Blo 766334 969985 := bbase (se 2 (by rfl) ⟨363744, by rfl⟩ : syracuseStep 969985 = 727489) (by norm_num)
theorem B1297741 : Blo 766334 1297741 := bbase (se 3 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 1297741 = 486653) (by norm_num)
theorem B4148597 : Blo 766334 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B1756541 : Blo 766334 1756541 := bbase (se 3 (by rfl) ⟨329351, by rfl⟩ : syracuseStep 1756541 = 658703) (by norm_num)
theorem B1297829 : Blo 766334 1297829 := bbase (se 4 (by rfl) ⟨121671, by rfl⟩ : syracuseStep 1297829 = 243343) (by norm_num)
theorem B970157 : Blo 766334 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B1068485 : Blo 766334 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B970213 : Blo 766334 970213 := bbase (se 4 (by rfl) ⟨90957, by rfl⟩ : syracuseStep 970213 = 181915) (by norm_num)
theorem B1297957 : Blo 766334 1297957 := bbase (se 4 (by rfl) ⟨121683, by rfl⟩ : syracuseStep 1297957 = 243367) (by norm_num)
theorem B1461797 : Blo 766334 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B970309 : Blo 766334 970309 := bbase (se 4 (by rfl) ⟨90966, by rfl⟩ : syracuseStep 970309 = 181933) (by norm_num)
theorem B1330805 : Blo 766334 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B1298045 : Blo 766334 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B1166989 : Blo 766334 1166989 := bbase (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) (by norm_num)
theorem B1232597 : Blo 766334 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B970481 : Blo 766334 970481 := bbase (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) (by norm_num)
theorem B1298173 : Blo 766334 1298173 := bbase (se 3 (by rfl) ⟨243407, by rfl⟩ : syracuseStep 1298173 = 486815) (by norm_num)
theorem B3952421 : Blo 766334 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B970537 : Blo 766334 970537 := bbase (se 2 (by rfl) ⟨363951, by rfl⟩ : syracuseStep 970537 = 727903) (by norm_num)
theorem B1298261 : Blo 766334 1298261 := bbase (se 9 (by rfl) ⟨3803, by rfl⟩ : syracuseStep 1298261 = 7607) (by norm_num)
theorem B970633 : Blo 766334 970633 := bbase (se 2 (by rfl) ⟨363987, by rfl⟩ : syracuseStep 970633 = 727975) (by norm_num)
theorem B1724309 : Blo 766334 1724309 := bbase (se 6 (by rfl) ⟨40413, by rfl⟩ : syracuseStep 1724309 = 80827) (by norm_num)
theorem B1560493 : Blo 766334 1560493 := bbase (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) (by norm_num)
theorem B1167293 : Blo 766334 1167293 := bbase (se 3 (by rfl) ⟨218867, by rfl⟩ : syracuseStep 1167293 = 437735) (by norm_num)
theorem B1298389 : Blo 766334 1298389 := bbase (se 7 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 1298389 = 30431) (by norm_num)
theorem B1724381 : Blo 766334 1724381 := bbase (se 3 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 1724381 = 646643) (by norm_num)
theorem B1560589 : Blo 766334 1560589 := bbase (se 3 (by rfl) ⟨292610, by rfl⟩ : syracuseStep 1560589 = 585221) (by norm_num)
theorem B1724453 : Blo 766334 1724453 := bbase (se 4 (by rfl) ⟨161667, by rfl⟩ : syracuseStep 1724453 = 323335) (by norm_num)
theorem B1298477 : Blo 766334 1298477 := bbase (se 3 (by rfl) ⟨243464, by rfl⟩ : syracuseStep 1298477 = 486929) (by norm_num)
theorem B970805 : Blo 766334 970805 := bbase (se 5 (by rfl) ⟨45506, by rfl⟩ : syracuseStep 970805 = 91013) (by norm_num)
theorem B3952709 : Blo 766334 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B3887189 : Blo 766334 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B1724525 : Blo 766334 1724525 := bbase (se 3 (by rfl) ⟨323348, by rfl⟩ : syracuseStep 1724525 = 646697) (by norm_num)
theorem B970861 : Blo 766334 970861 := bbase (se 3 (by rfl) ⟨182036, by rfl⟩ : syracuseStep 970861 = 364073) (by norm_num)
theorem B1233053 : Blo 766334 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B1298605 : Blo 766334 1298605 := bbase (se 3 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 1298605 = 486977) (by norm_num)
theorem B1724597 : Blo 766334 1724597 := bbase (se 5 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 1724597 = 161681) (by norm_num)
theorem B970957 : Blo 766334 970957 := bbase (se 3 (by rfl) ⟨182054, by rfl⟩ : syracuseStep 970957 = 364109) (by norm_num)
theorem B1724669 : Blo 766334 1724669 := bbase (se 3 (by rfl) ⟨323375, by rfl⟩ : syracuseStep 1724669 = 646751) (by norm_num)
theorem B1298693 : Blo 766334 1298693 := bbase (se 4 (by rfl) ⟨121752, by rfl⟩ : syracuseStep 1298693 = 243505) (by norm_num)
theorem B1724741 : Blo 766334 1724741 := bbase (se 4 (by rfl) ⟨161694, by rfl⟩ : syracuseStep 1724741 = 323389) (by norm_num)
theorem B971129 : Blo 766334 971129 := bbase (se 2 (by rfl) ⟨364173, by rfl⟩ : syracuseStep 971129 = 728347) (by norm_num)
theorem B1298821 : Blo 766334 1298821 := bbase (se 4 (by rfl) ⟨121764, by rfl⟩ : syracuseStep 1298821 = 243529) (by norm_num)
theorem B1724813 : Blo 766334 1724813 := bbase (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) (by norm_num)
theorem B5820821 : Blo 766334 5820821 := bbase (se 6 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 5820821 = 272851) (by norm_num)
theorem B971185 : Blo 766334 971185 := bbase (se 2 (by rfl) ⟨364194, by rfl⟩ : syracuseStep 971185 = 728389) (by norm_num)
theorem B1724885 : Blo 766334 1724885 := bbase (se 7 (by rfl) ⟨20213, by rfl⟩ : syracuseStep 1724885 = 40427) (by norm_num)
theorem B1298909 : Blo 766334 1298909 := bbase (se 3 (by rfl) ⟨243545, by rfl⟩ : syracuseStep 1298909 = 487091) (by norm_num)
theorem B971281 : Blo 766334 971281 := bbase (se 2 (by rfl) ⟨364230, by rfl⟩ : syracuseStep 971281 = 728461) (by norm_num)
theorem B1724957 : Blo 766334 1724957 := bbase (se 3 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 1724957 = 646859) (by norm_num)
theorem B1299037 : Blo 766334 1299037 := bbase (se 3 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 1299037 = 487139) (by norm_num)
theorem B1725029 : Blo 766334 1725029 := bbase (se 4 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 1725029 = 323443) (by norm_num)
theorem B4379285 : Blo 766334 4379285 := bbase (se 6 (by rfl) ⟨102639, by rfl⟩ : syracuseStep 4379285 = 205279) (by norm_num)
theorem B1725101 : Blo 766334 1725101 := bbase (se 3 (by rfl) ⟨323456, by rfl⟩ : syracuseStep 1725101 = 646913) (by norm_num)
theorem B1299125 : Blo 766334 1299125 := bbase (se 5 (by rfl) ⟨60896, by rfl⟩ : syracuseStep 1299125 = 121793) (by norm_num)
theorem B971453 : Blo 766334 971453 := bbase (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) (by norm_num)
theorem B1725173 : Blo 766334 1725173 := bbase (se 5 (by rfl) ⟨80867, by rfl⟩ : syracuseStep 1725173 = 161735) (by norm_num)
theorem B971509 : Blo 766334 971509 := bbase (se 5 (by rfl) ⟨45539, by rfl⟩ : syracuseStep 971509 = 91079) (by norm_num)
theorem B1299253 : Blo 766334 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B1725245 : Blo 766334 1725245 := bbase (se 3 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 1725245 = 646967) (by norm_num)
theorem B971605 : Blo 766334 971605 := bbase (se 9 (by rfl) ⟨2846, by rfl⟩ : syracuseStep 971605 = 5693) (by norm_num)
theorem B1725317 : Blo 766334 1725317 := bbase (se 4 (by rfl) ⟨161748, by rfl⟩ : syracuseStep 1725317 = 323497) (by norm_num)
theorem B1299341 : Blo 766334 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B13161365 : Blo 766334 13161365 := bbase (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) (by norm_num)
theorem B1725389 : Blo 766334 1725389 := bbase (se 3 (by rfl) ⟨323510, by rfl⟩ : syracuseStep 1725389 = 647021) (by norm_num)
theorem B971777 : Blo 766334 971777 := bbase (se 2 (by rfl) ⟨364416, by rfl⟩ : syracuseStep 971777 = 728833) (by norm_num)
theorem B1299469 : Blo 766334 1299469 := bbase (se 3 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 1299469 = 487301) (by norm_num)
theorem B1725461 : Blo 766334 1725461 := bbase (se 6 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 1725461 = 80881) (by norm_num)
theorem B1561621 : Blo 766334 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B971833 : Blo 766334 971833 := bbase (se 2 (by rfl) ⟨364437, by rfl⟩ : syracuseStep 971833 = 728875) (by norm_num)
theorem B1561685 : Blo 766334 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B1725533 : Blo 766334 1725533 := bbase (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) (by norm_num)
theorem B1299557 : Blo 766334 1299557 := bbase (se 4 (by rfl) ⟨121833, by rfl⟩ : syracuseStep 1299557 = 243667) (by norm_num)
theorem B971929 : Blo 766334 971929 := bbase (se 2 (by rfl) ⟨364473, by rfl⟩ : syracuseStep 971929 = 728947) (by norm_num)
theorem B1725605 : Blo 766334 1725605 := bbase (se 4 (by rfl) ⟨161775, by rfl⟩ : syracuseStep 1725605 = 323551) (by norm_num)
theorem B1660085 : Blo 766334 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1299685 : Blo 766334 1299685 := bbase (se 4 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 1299685 = 243691) (by norm_num)
theorem B1725677 : Blo 766334 1725677 := bbase (se 3 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 1725677 = 647129) (by norm_num)
theorem B1725749 : Blo 766334 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B1299773 : Blo 766334 1299773 := bbase (se 3 (by rfl) ⟨243707, by rfl⟩ : syracuseStep 1299773 = 487415) (by norm_num)
theorem B972101 : Blo 766334 972101 := bbase (se 4 (by rfl) ⟨91134, by rfl⟩ : syracuseStep 972101 = 182269) (by norm_num)
theorem B3888485 : Blo 766334 3888485 := bbase (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) (by norm_num)
theorem B1725821 : Blo 766334 1725821 := bbase (se 3 (by rfl) ⟨323591, by rfl⟩ : syracuseStep 1725821 = 647183) (by norm_num)
theorem B972157 : Blo 766334 972157 := bbase (se 3 (by rfl) ⟨182279, by rfl⟩ : syracuseStep 972157 = 364559) (by norm_num)
theorem B1168813 : Blo 766334 1168813 := bbase (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) (by norm_num)
theorem B1299901 : Blo 766334 1299901 := bbase (se 3 (by rfl) ⟨243731, by rfl⟩ : syracuseStep 1299901 = 487463) (by norm_num)
theorem B1725893 : Blo 766334 1725893 := bbase (se 4 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 1725893 = 323605) (by norm_num)
theorem B972253 : Blo 766334 972253 := bbase (se 3 (by rfl) ⟨182297, by rfl⟩ : syracuseStep 972253 = 364595) (by norm_num)
theorem B2184677 : Blo 766334 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B1725965 : Blo 766334 1725965 := bbase (se 3 (by rfl) ⟨323618, by rfl⟩ : syracuseStep 1725965 = 647237) (by norm_num)
theorem B874037 : Blo 766334 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B3692101 : Blo 766334 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B1726037 : Blo 766334 1726037 := bbase (se 8 (by rfl) ⟨10113, by rfl⟩ : syracuseStep 1726037 = 20227) (by norm_num)
theorem B972425 : Blo 766334 972425 := bbase (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) (by norm_num)
theorem B1726109 : Blo 766334 1726109 := bbase (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) (by norm_num)
theorem B972481 : Blo 766334 972481 := bbase (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) (by norm_num)
theorem B1038037 : Blo 766334 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B1726181 : Blo 766334 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B972577 : Blo 766334 972577 := bbase (se 2 (by rfl) ⟨364716, by rfl⟩ : syracuseStep 972577 = 729433) (by norm_num)
theorem B1726253 : Blo 766334 1726253 := bbase (se 3 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 1726253 = 647345) (by norm_num)
theorem B1726325 : Blo 766334 1726325 := bbase (se 5 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 1726325 = 161843) (by norm_num)
theorem B4675445 : Blo 766334 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B1038253 : Blo 766334 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B1726397 : Blo 766334 1726397 := bbase (se 3 (by rfl) ⟨323699, by rfl⟩ : syracuseStep 1726397 = 647399) (by norm_num)
theorem B972749 : Blo 766334 972749 := bbase (se 3 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 972749 = 364781) (by norm_num)
theorem B1038317 : Blo 766334 1038317 := bbase (se 3 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 1038317 = 389369) (by norm_num)
theorem B5527541 : Blo 766334 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B1726469 : Blo 766334 1726469 := bbase (se 4 (by rfl) ⟨161856, by rfl⟩ : syracuseStep 1726469 = 323713) (by norm_num)
theorem B972805 : Blo 766334 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B1726541 : Blo 766334 1726541 := bbase (se 3 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 1726541 = 647453) (by norm_num)
theorem B874585 : Blo 766334 874585 := bbase (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) (by norm_num)
theorem B972901 : Blo 766334 972901 := bbase (se 4 (by rfl) ⟨91209, by rfl⟩ : syracuseStep 972901 = 182419) (by norm_num)
theorem B1726613 : Blo 766334 1726613 := bbase (se 6 (by rfl) ⟨40467, by rfl⟩ : syracuseStep 1726613 = 80935) (by norm_num)
theorem B874657 : Blo 766334 874657 := bbase (se 2 (by rfl) ⟨327996, by rfl⟩ : syracuseStep 874657 = 655993) (by norm_num)
theorem B1726685 : Blo 766334 1726685 := bbase (se 3 (by rfl) ⟨323753, by rfl⟩ : syracuseStep 1726685 = 647507) (by norm_num)
theorem B973073 : Blo 766334 973073 := bbase (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) (by norm_num)
theorem B1726757 : Blo 766334 1726757 := bbase (se 4 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 1726757 = 323767) (by norm_num)
theorem B973129 : Blo 766334 973129 := bbase (se 2 (by rfl) ⟨364923, by rfl⟩ : syracuseStep 973129 = 729847) (by norm_num)
theorem B1726829 : Blo 766334 1726829 := bbase (se 3 (by rfl) ⟨323780, by rfl⟩ : syracuseStep 1726829 = 647561) (by norm_num)
theorem B973225 : Blo 766334 973225 := bbase (se 2 (by rfl) ⟨364959, by rfl⟩ : syracuseStep 973225 = 729919) (by norm_num)
theorem B1726901 : Blo 766334 1726901 := bbase (se 5 (by rfl) ⟨80948, by rfl⟩ : syracuseStep 1726901 = 161897) (by norm_num)
theorem B874945 : Blo 766334 874945 := bbase (se 2 (by rfl) ⟨328104, by rfl⟩ : syracuseStep 874945 = 656209) (by norm_num)
theorem B1726973 : Blo 766334 1726973 := bbase (se 3 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 1726973 = 647615) (by norm_num)
theorem B1727045 : Blo 766334 1727045 := bbase (se 4 (by rfl) ⟨161910, by rfl⟩ : syracuseStep 1727045 = 323821) (by norm_num)
theorem B973397 : Blo 766334 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B2775637 : Blo 766334 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B3889781 : Blo 766334 3889781 := bbase (se 5 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 3889781 = 364667) (by norm_num)
theorem B2185861 : Blo 766334 2185861 := bbase (se 4 (by rfl) ⟨204924, by rfl⟩ : syracuseStep 2185861 = 409849) (by norm_num)
theorem B1727117 : Blo 766334 1727117 := bbase (se 3 (by rfl) ⟨323834, by rfl⟩ : syracuseStep 1727117 = 647669) (by norm_num)
theorem B973453 : Blo 766334 973453 := bbase (se 3 (by rfl) ⟨182522, by rfl⟩ : syracuseStep 973453 = 365045) (by norm_num)
theorem B2808485 : Blo 766334 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B1727189 : Blo 766334 1727189 := bbase (se 7 (by rfl) ⟨20240, by rfl⟩ : syracuseStep 1727189 = 40481) (by norm_num)
theorem B973549 : Blo 766334 973549 := bbase (se 3 (by rfl) ⟨182540, by rfl⟩ : syracuseStep 973549 = 365081) (by norm_num)
theorem B1727261 : Blo 766334 1727261 := bbase (se 3 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 1727261 = 647723) (by norm_num)
theorem B2186021 : Blo 766334 2186021 := bbase (se 4 (by rfl) ⟨204939, by rfl⟩ : syracuseStep 2186021 = 409879) (by norm_num)
theorem B2218805 : Blo 766334 2218805 := bbase (se 5 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 2218805 = 208013) (by norm_num)
theorem B1727333 : Blo 766334 1727333 := bbase (se 4 (by rfl) ⟨161937, by rfl⟩ : syracuseStep 1727333 = 323875) (by norm_num)
theorem B973721 : Blo 766334 973721 := bbase (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) (by norm_num)
theorem B1727405 : Blo 766334 1727405 := bbase (se 3 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 1727405 = 647777) (by norm_num)
theorem B973777 : Blo 766334 973777 := bbase (se 2 (by rfl) ⟨365166, by rfl⟩ : syracuseStep 973777 = 730333) (by norm_num)
theorem B7003093 : Blo 766334 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B1727477 : Blo 766334 1727477 := bbase (se 5 (by rfl) ⟨80975, by rfl⟩ : syracuseStep 1727477 = 161951) (by norm_num)
theorem B2186261 : Blo 766334 2186261 := bbase (se 6 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 2186261 = 102481) (by norm_num)
theorem B973873 : Blo 766334 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B1170485 : Blo 766334 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B1727549 : Blo 766334 1727549 := bbase (se 3 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 1727549 = 647831) (by norm_num)
theorem B5069909 : Blo 766334 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B1170541 : Blo 766334 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B1727621 : Blo 766334 1727621 := bbase (se 4 (by rfl) ⟨161964, by rfl⟩ : syracuseStep 1727621 = 323929) (by norm_num)
theorem B1399997 : Blo 766334 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1727693 : Blo 766334 1727693 := bbase (se 3 (by rfl) ⟨323942, by rfl⟩ : syracuseStep 1727693 = 647885) (by norm_num)
theorem B2186453 : Blo 766334 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B974045 : Blo 766334 974045 := bbase (se 3 (by rfl) ⟨182633, by rfl⟩ : syracuseStep 974045 = 365267) (by norm_num)
theorem B1727765 : Blo 766334 1727765 := bbase (se 6 (by rfl) ⟨40494, by rfl⟩ : syracuseStep 1727765 = 80989) (by norm_num)
theorem B974101 : Blo 766334 974101 := bbase (se 6 (by rfl) ⟨22830, by rfl⟩ : syracuseStep 974101 = 45661) (by norm_num)
theorem B1727837 : Blo 766334 1727837 := bbase (se 3 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 1727837 = 647939) (by norm_num)
theorem B974197 : Blo 766334 974197 := bbase (se 5 (by rfl) ⟨45665, by rfl⟩ : syracuseStep 974197 = 91331) (by norm_num)
theorem B1727909 : Blo 766334 1727909 := bbase (se 4 (by rfl) ⟨161991, by rfl⟩ : syracuseStep 1727909 = 323983) (by norm_num)
theorem B875981 : Blo 766334 875981 := bbase (se 3 (by rfl) ⟨164246, by rfl⟩ : syracuseStep 875981 = 328493) (by norm_num)
theorem B1727981 : Blo 766334 1727981 := bbase (se 3 (by rfl) ⟨323996, by rfl⟩ : syracuseStep 1727981 = 647993) (by norm_num)
theorem B974369 : Blo 766334 974369 := bbase (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) (by norm_num)
theorem B1728053 : Blo 766334 1728053 := bbase (se 5 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 1728053 = 162005) (by norm_num)
theorem B1826381 : Blo 766334 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B974425 : Blo 766334 974425 := bbase (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) (by norm_num)
theorem B1662565 : Blo 766334 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B1728125 : Blo 766334 1728125 := bbase (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) (by norm_num)
theorem B974521 : Blo 766334 974521 := bbase (se 2 (by rfl) ⟨365445, by rfl⟩ : syracuseStep 974521 = 730891) (by norm_num)
theorem B1728197 : Blo 766334 1728197 := bbase (se 4 (by rfl) ⟨162018, by rfl⟩ : syracuseStep 1728197 = 324037) (by norm_num)
theorem B1728269 : Blo 766334 1728269 := bbase (se 3 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 1728269 = 648101) (by norm_num)
theorem B1728341 : Blo 766334 1728341 := bbase (se 9 (by rfl) ⟨5063, by rfl⟩ : syracuseStep 1728341 = 10127) (by norm_num)
theorem B974693 : Blo 766334 974693 := bbase (se 4 (by rfl) ⟨91377, by rfl⟩ : syracuseStep 974693 = 182755) (by norm_num)
theorem B3891077 : Blo 766334 3891077 := bbase (se 4 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 3891077 = 729577) (by norm_num)
theorem B1728413 : Blo 766334 1728413 := bbase (se 3 (by rfl) ⟨324077, by rfl⟩ : syracuseStep 1728413 = 648155) (by norm_num)
theorem B974749 : Blo 766334 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B1728485 : Blo 766334 1728485 := bbase (se 4 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 1728485 = 324091) (by norm_num)
theorem B974845 : Blo 766334 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B1728557 : Blo 766334 1728557 := bbase (se 3 (by rfl) ⟨324104, by rfl⟩ : syracuseStep 1728557 = 648209) (by norm_num)
theorem B778333 : Blo 766334 778333 := bbase (se 3 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 778333 = 291875) (by norm_num)
theorem B876637 : Blo 766334 876637 := bbase (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) (by norm_num)
theorem B778349 : Blo 766334 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B1728629 : Blo 766334 1728629 := bbase (se 5 (by rfl) ⟨81029, by rfl⟩ : syracuseStep 1728629 = 162059) (by norm_num)
theorem B15949973 : Blo 766334 15949973 := bbase (se 6 (by rfl) ⟨373827, by rfl⟩ : syracuseStep 15949973 = 747655) (by norm_num)
theorem B876701 : Blo 766334 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B2187445 : Blo 766334 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B1728701 : Blo 766334 1728701 := bbase (se 3 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 1728701 = 648263) (by norm_num)
theorem B1728773 : Blo 766334 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B1728845 : Blo 766334 1728845 := bbase (se 3 (by rfl) ⟨324158, by rfl⟩ : syracuseStep 1728845 = 648317) (by norm_num)
theorem B1728917 : Blo 766334 1728917 := bbase (se 6 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 1728917 = 81043) (by norm_num)
theorem B876953 : Blo 766334 876953 := bbase (se 2 (by rfl) ⟨328857, by rfl⟩ : syracuseStep 876953 = 657715) (by norm_num)
theorem B1728989 : Blo 766334 1728989 := bbase (se 3 (by rfl) ⟨324185, by rfl⟩ : syracuseStep 1728989 = 648371) (by norm_num)
theorem B1729061 : Blo 766334 1729061 := bbase (se 4 (by rfl) ⟨162099, by rfl⟩ : syracuseStep 1729061 = 324199) (by norm_num)
theorem B1729133 : Blo 766334 1729133 := bbase (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) (by norm_num)
theorem B778897 : Blo 766334 778897 := bbase (se 2 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 778897 = 584173) (by norm_num)
theorem B1729205 : Blo 766334 1729205 := bbase (se 5 (by rfl) ⟨81056, by rfl⟩ : syracuseStep 1729205 = 162113) (by norm_num)
theorem B1729277 : Blo 766334 1729277 := bbase (se 3 (by rfl) ⟨324239, by rfl⟩ : syracuseStep 1729277 = 648479) (by norm_num)
theorem B1729349 : Blo 766334 1729349 := bbase (se 4 (by rfl) ⟨162126, by rfl⟩ : syracuseStep 1729349 = 324253) (by norm_num)
theorem B1729421 : Blo 766334 1729421 := bbase (se 3 (by rfl) ⟨324266, by rfl⟩ : syracuseStep 1729421 = 648533) (by norm_num)
theorem B1729493 : Blo 766334 1729493 := bbase (se 7 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 1729493 = 40535) (by norm_num)
theorem B779257 : Blo 766334 779257 := bbase (se 2 (by rfl) ⟨292221, by rfl⟩ : syracuseStep 779257 = 584443) (by norm_num)
theorem B1729565 : Blo 766334 1729565 := bbase (se 3 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 1729565 = 648587) (by norm_num)
theorem B1664077 : Blo 766334 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B1729637 : Blo 766334 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B3892373 : Blo 766334 3892373 := bbase (se 6 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 3892373 = 182455) (by norm_num)
theorem B8316053 : Blo 766334 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B1729709 : Blo 766334 1729709 := bbase (se 3 (by rfl) ⟨324320, by rfl⟩ : syracuseStep 1729709 = 648641) (by norm_num)
theorem B1729781 : Blo 766334 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B5268725 : Blo 766334 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B2188549 : Blo 766334 2188549 := bbase (se 4 (by rfl) ⟨205176, by rfl⟩ : syracuseStep 2188549 = 410353) (by norm_num)
theorem B779549 : Blo 766334 779549 := bbase (se 3 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 779549 = 292331) (by norm_num)
theorem B1729853 : Blo 766334 1729853 := bbase (se 3 (by rfl) ⟨324347, by rfl⟩ : syracuseStep 1729853 = 648695) (by norm_num)
theorem B1107277 : Blo 766334 1107277 := bbase (se 3 (by rfl) ⟨207614, by rfl⟩ : syracuseStep 1107277 = 415229) (by norm_num)
theorem B1729925 : Blo 766334 1729925 := bbase (se 4 (by rfl) ⟨162180, by rfl⟩ : syracuseStep 1729925 = 324361) (by norm_num)
theorem B1729997 : Blo 766334 1729997 := bbase (se 3 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 1729997 = 648749) (by norm_num)
theorem B1730069 : Blo 766334 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B779825 : Blo 766334 779825 := bbase (se 2 (by rfl) ⟨292434, by rfl⟩ : syracuseStep 779825 = 584869) (by norm_num)
theorem B1402429 : Blo 766334 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1730141 : Blo 766334 1730141 := bbase (se 3 (by rfl) ⟨324401, by rfl⟩ : syracuseStep 1730141 = 648803) (by norm_num)
theorem B1107589 : Blo 766334 1107589 := bbase (se 4 (by rfl) ⟨103836, by rfl⟩ : syracuseStep 1107589 = 207673) (by norm_num)
theorem B1107613 : Blo 766334 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B1730213 : Blo 766334 1730213 := bbase (se 4 (by rfl) ⟨162207, by rfl⟩ : syracuseStep 1730213 = 324415) (by norm_num)
theorem B3696293 : Blo 766334 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B14804693 : Blo 766334 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B1730285 : Blo 766334 1730285 := bbase (se 3 (by rfl) ⟨324428, by rfl⟩ : syracuseStep 1730285 = 648857) (by norm_num)
theorem B1730357 : Blo 766334 1730357 := bbase (se 5 (by rfl) ⟨81110, by rfl⟩ : syracuseStep 1730357 = 162221) (by norm_num)
theorem B1730429 : Blo 766334 1730429 := bbase (se 3 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 1730429 = 648911) (by norm_num)
theorem B1730501 : Blo 766334 1730501 := bbase (se 4 (by rfl) ⟨162234, by rfl⟩ : syracuseStep 1730501 = 324469) (by norm_num)
theorem B1730573 : Blo 766334 1730573 := bbase (se 3 (by rfl) ⟨324482, by rfl⟩ : syracuseStep 1730573 = 648965) (by norm_num)
theorem B1730645 : Blo 766334 1730645 := bbase (se 8 (by rfl) ⟨10140, by rfl⟩ : syracuseStep 1730645 = 20281) (by norm_num)
theorem B1730717 : Blo 766334 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B1730789 : Blo 766334 1730789 := bbase (se 4 (by rfl) ⟨162261, by rfl⟩ : syracuseStep 1730789 = 324523) (by norm_num)
theorem B1730861 : Blo 766334 1730861 := bbase (se 3 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 1730861 = 649073) (by norm_num)
theorem B1730933 : Blo 766334 1730933 := bbase (se 5 (by rfl) ⟨81137, by rfl⟩ : syracuseStep 1730933 = 162275) (by norm_num)
theorem B3893669 : Blo 766334 3893669 := bbase (se 4 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 3893669 = 730063) (by norm_num)
theorem B1599925 : Blo 766334 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B1731005 : Blo 766334 1731005 := bbase (se 3 (by rfl) ⟨324563, by rfl⟩ : syracuseStep 1731005 = 649127) (by norm_num)
theorem B1731077 : Blo 766334 1731077 := bbase (se 4 (by rfl) ⟨162288, by rfl⟩ : syracuseStep 1731077 = 324577) (by norm_num)
theorem B1731149 : Blo 766334 1731149 := bbase (se 3 (by rfl) ⟨324590, by rfl⟩ : syracuseStep 1731149 = 649181) (by norm_num)
theorem B1731221 : Blo 766334 1731221 := bbase (se 6 (by rfl) ⟨40575, by rfl⟩ : syracuseStep 1731221 = 81151) (by norm_num)
theorem B1731293 : Blo 766334 1731293 := bbase (se 3 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 1731293 = 649235) (by norm_num)
theorem B2190053 : Blo 766334 2190053 := bbase (se 4 (by rfl) ⟨205317, by rfl⟩ : syracuseStep 2190053 = 410635) (by norm_num)
theorem B3107621 : Blo 766334 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B1731365 : Blo 766334 1731365 := bbase (se 4 (by rfl) ⟨162315, by rfl⟩ : syracuseStep 1731365 = 324631) (by norm_num)
theorem B1731437 : Blo 766334 1731437 := bbase (se 3 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 1731437 = 649289) (by norm_num)
theorem B1731509 : Blo 766334 1731509 := bbase (se 5 (by rfl) ⟨81164, by rfl⟩ : syracuseStep 1731509 = 162329) (by norm_num)
theorem B1731581 : Blo 766334 1731581 := bbase (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) (by norm_num)
theorem B1731653 : Blo 766334 1731653 := bbase (se 4 (by rfl) ⟨162342, by rfl⟩ : syracuseStep 1731653 = 324685) (by norm_num)
theorem B1731725 : Blo 766334 1731725 := bbase (se 3 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 1731725 = 649397) (by norm_num)
theorem B1731797 : Blo 766334 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B1731869 : Blo 766334 1731869 := bbase (se 3 (by rfl) ⟨324725, by rfl⟩ : syracuseStep 1731869 = 649451) (by norm_num)
theorem B2223445 : Blo 766334 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B781669 : Blo 766334 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B1731941 : Blo 766334 1731941 := bbase (se 4 (by rfl) ⟨162369, by rfl⟩ : syracuseStep 1731941 = 324739) (by norm_num)
theorem B1732013 : Blo 766334 1732013 := bbase (se 3 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 1732013 = 649505) (by norm_num)
theorem B2911733 : Blo 766334 2911733 := bbase (se 5 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 2911733 = 272975) (by norm_num)
theorem B1732085 : Blo 766334 1732085 := bbase (se 5 (by rfl) ⟨81191, by rfl⟩ : syracuseStep 1732085 = 162383) (by norm_num)
theorem B1732157 : Blo 766334 1732157 := bbase (se 3 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 1732157 = 649559) (by norm_num)
theorem B1732229 : Blo 766334 1732229 := bbase (se 4 (by rfl) ⟨162396, by rfl⟩ : syracuseStep 1732229 = 324793) (by norm_num)
theorem B3894965 : Blo 766334 3894965 := bbase (se 5 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 3894965 = 365153) (by norm_num)
theorem B1732301 : Blo 766334 1732301 := bbase (se 3 (by rfl) ⟨324806, by rfl⟩ : syracuseStep 1732301 = 649613) (by norm_num)
theorem B2912021 : Blo 766334 2912021 := bbase (se 6 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 2912021 = 136501) (by norm_num)
theorem B1732373 : Blo 766334 1732373 := bbase (se 6 (by rfl) ⟨40602, by rfl⟩ : syracuseStep 1732373 = 81205) (by norm_num)
theorem B1732445 : Blo 766334 1732445 := bbase (se 3 (by rfl) ⟨324833, by rfl⟩ : syracuseStep 1732445 = 649667) (by norm_num)
theorem B1732517 : Blo 766334 1732517 := bbase (se 4 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 1732517 = 324847) (by norm_num)
theorem B1732589 : Blo 766334 1732589 := bbase (se 3 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 1732589 = 649721) (by norm_num)
theorem B5828597 : Blo 766334 5828597 := bbase (se 5 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 5828597 = 546431) (by norm_num)
theorem B1732661 : Blo 766334 1732661 := bbase (se 5 (by rfl) ⟨81218, by rfl⟩ : syracuseStep 1732661 = 162437) (by norm_num)
theorem B1110125 : Blo 766334 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1732733 : Blo 766334 1732733 := bbase (se 3 (by rfl) ⟨324887, by rfl⟩ : syracuseStep 1732733 = 649775) (by norm_num)
theorem B1732805 : Blo 766334 1732805 := bbase (se 4 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 1732805 = 324901) (by norm_num)
theorem B1732877 : Blo 766334 1732877 := bbase (se 3 (by rfl) ⟨324914, by rfl⟩ : syracuseStep 1732877 = 649829) (by norm_num)
theorem B2191637 : Blo 766334 2191637 := bbase (se 6 (by rfl) ⟨51366, by rfl⟩ : syracuseStep 2191637 = 102733) (by norm_num)
theorem B1667405 : Blo 766334 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B1732949 : Blo 766334 1732949 := bbase (se 10 (by rfl) ⟨2538, by rfl⟩ : syracuseStep 1732949 = 5077) (by norm_num)
theorem B1733021 : Blo 766334 1733021 := bbase (se 3 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 1733021 = 649883) (by norm_num)
theorem B1733093 : Blo 766334 1733093 := bbase (se 4 (by rfl) ⟨162477, by rfl⟩ : syracuseStep 1733093 = 324955) (by norm_num)
theorem B1733165 : Blo 766334 1733165 := bbase (se 3 (by rfl) ⟨324968, by rfl⟩ : syracuseStep 1733165 = 649937) (by norm_num)
theorem B1733237 : Blo 766334 1733237 := bbase (se 5 (by rfl) ⟨81245, by rfl⟩ : syracuseStep 1733237 = 162491) (by norm_num)
theorem B4682549 : Blo 766334 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B2913205 : Blo 766334 2913205 := bbase (se 5 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 2913205 = 273113) (by norm_num)
theorem B2192309 : Blo 766334 2192309 := bbase (se 5 (by rfl) ⟨102764, by rfl⟩ : syracuseStep 2192309 = 205529) (by norm_num)
theorem B3896261 : Blo 766334 3896261 := bbase (se 4 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 3896261 = 730549) (by norm_num)
theorem B3109877 : Blo 766334 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B7009301 : Blo 766334 7009301 := bbase (se 6 (by rfl) ⟨164280, by rfl⟩ : syracuseStep 7009301 = 328561) (by norm_num)
theorem B2913509 : Blo 766334 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B2192741 : Blo 766334 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B2586437 : Blo 766334 2586437 := bbase (se 4 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 2586437 = 484957) (by norm_num)
theorem B1406789 : Blo 766334 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B2193493 : Blo 766334 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B4159669 : Blo 766334 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B3897557 : Blo 766334 3897557 := bbase (se 7 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 3897557 = 91349) (by norm_num)
theorem B2586869 : Blo 766334 2586869 := bbase (se 5 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 2586869 = 242519) (by norm_num)
theorem B1636757 : Blo 766334 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B1603997 : Blo 766334 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B2587301 : Blo 766334 2587301 := bbase (se 4 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 2587301 = 485119) (by norm_num)
theorem B2587733 : Blo 766334 2587733 := bbase (se 8 (by rfl) ⟨15162, by rfl⟩ : syracuseStep 2587733 = 30325) (by norm_num)
theorem B1637509 : Blo 766334 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B1637653 : Blo 766334 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B2915621 : Blo 766334 2915621 := bbase (se 4 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 2915621 = 546679) (by norm_num)
theorem B3898853 : Blo 766334 3898853 := bbase (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) (by norm_num)
theorem B2588165 : Blo 766334 2588165 := bbase (se 4 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 2588165 = 485281) (by norm_num)
theorem B2915909 : Blo 766334 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B1638029 : Blo 766334 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B818857 : Blo 766334 818857 := bbase (se 2 (by rfl) ⟨307071, by rfl⟩ : syracuseStep 818857 = 614143) (by norm_num)
theorem B818929 : Blo 766334 818929 := bbase (se 2 (by rfl) ⟨307098, by rfl⟩ : syracuseStep 818929 = 614197) (by norm_num)
theorem B6225749 : Blo 766334 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B33259349 : Blo 766334 33259349 := bbase (se 9 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 33259349 = 194879) (by norm_num)
theorem B819109 : Blo 766334 819109 := bbase (se 4 (by rfl) ⟨76791, by rfl⟩ : syracuseStep 819109 = 153583) (by norm_num)
theorem B2588597 : Blo 766334 2588597 := bbase (se 5 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 2588597 = 242681) (by norm_num)
theorem B1638397 : Blo 766334 1638397 := bbase (se 3 (by rfl) ⟨307199, by rfl⟩ : syracuseStep 1638397 = 614399) (by norm_num)
theorem B2588813 : Blo 766334 2588813 := bstep (se 3 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 2588813 = 970805) B970805
theorem B2588867 : Blo 766334 2588867 := bstep (se 1 (by rfl) ⟨1941650, by rfl⟩ : syracuseStep 2588867 = 3883301) B3883301
theorem B2916593 : Blo 766334 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B33292565 : Blo 766334 33292565 := bstep (se 6 (by rfl) ⟨780294, by rfl⟩ : syracuseStep 33292565 = 1560589) B1560589
theorem B2589137 : Blo 766334 2589137 := bstep (se 2 (by rfl) ⟨970926, by rfl⟩ : syracuseStep 2589137 = 1941853) B1941853
theorem B1638883 : Blo 766334 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B2458147 : Blo 766334 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B12485173 : Blo 766334 12485173 := bstep (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) B1170485
theorem B5833457 : Blo 766334 5833457 := bstep (se 2 (by rfl) ⟨2187546, by rfl⟩ : syracuseStep 5833457 = 4375093) B4375093
theorem B1639217 : Blo 766334 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1966993 : Blo 766334 1966993 := bstep (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) B1475245
theorem B2589677 : Blo 766334 2589677 := bstep (se 3 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 2589677 = 971129) B971129
theorem B2589731 : Blo 766334 2589731 := bstep (se 1 (by rfl) ⟨1942298, by rfl⟩ : syracuseStep 2589731 = 3884597) B3884597
theorem B2590001 : Blo 766334 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B13108877 : Blo 766334 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B2918051 : Blo 766334 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B2918065 : Blo 766334 2918065 := bstep (se 2 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 2918065 = 2188549) B2188549
theorem B2590541 : Blo 766334 2590541 := bstep (se 3 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 2590541 = 971453) B971453
theorem B2590595 : Blo 766334 2590595 := bstep (se 1 (by rfl) ⟨1942946, by rfl⟩ : syracuseStep 2590595 = 3885893) B3885893
theorem B4982705 : Blo 766334 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B1640387 : Blo 766334 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B1312753 : Blo 766334 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B1050643 : Blo 766334 1050643 := bstep (se 1 (by rfl) ⟨787982, by rfl⟩ : syracuseStep 1050643 = 1575965) B1575965
theorem B1869905 : Blo 766334 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B2590865 : Blo 766334 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B1476785 : Blo 766334 1476785 := bstep (se 2 (by rfl) ⟨553794, by rfl⟩ : syracuseStep 1476785 = 1107589) B1107589
theorem B3279203 : Blo 766334 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1050995 : Blo 766334 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B887203 : Blo 766334 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B1149521 : Blo 766334 1149521 := bstep (se 2 (by rfl) ⟨431070, by rfl⟩ : syracuseStep 1149521 = 862141) B862141
theorem B1149539 : Blo 766334 1149539 := bstep (se 1 (by rfl) ⟨862154, by rfl⟩ : syracuseStep 1149539 = 1724309) B1724309
theorem B1149569 : Blo 766334 1149569 := bstep (se 2 (by rfl) ⟨431088, by rfl⟩ : syracuseStep 1149569 = 862177) B862177
theorem B1149587 : Blo 766334 1149587 := bstep (se 1 (by rfl) ⟨862190, by rfl⟩ : syracuseStep 1149587 = 1724381) B1724381
theorem B2591405 : Blo 766334 2591405 := bstep (se 3 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 2591405 = 971777) B971777
theorem B1149617 : Blo 766334 1149617 := bstep (se 2 (by rfl) ⟨431106, by rfl⟩ : syracuseStep 1149617 = 862213) B862213
theorem B1149635 : Blo 766334 1149635 := bstep (se 1 (by rfl) ⟨862226, by rfl⟩ : syracuseStep 1149635 = 1724453) B1724453
theorem B2460365 : Blo 766334 2460365 := bstep (se 3 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 2460365 = 922637) B922637
theorem B1149665 : Blo 766334 1149665 := bstep (se 2 (by rfl) ⟨431124, by rfl⟩ : syracuseStep 1149665 = 862249) B862249
theorem B2591459 : Blo 766334 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B1149683 : Blo 766334 1149683 := bstep (se 1 (by rfl) ⟨862262, by rfl⟩ : syracuseStep 1149683 = 1724525) B1724525
theorem B1149713 : Blo 766334 1149713 := bstep (se 2 (by rfl) ⟨431142, by rfl⟩ : syracuseStep 1149713 = 862285) B862285
theorem B822035 : Blo 766334 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B1149731 : Blo 766334 1149731 := bstep (se 1 (by rfl) ⟨862298, by rfl⟩ : syracuseStep 1149731 = 1724597) B1724597
theorem B1149761 : Blo 766334 1149761 := bstep (se 2 (by rfl) ⟨431160, by rfl⟩ : syracuseStep 1149761 = 862321) B862321
theorem B1149779 : Blo 766334 1149779 := bstep (se 1 (by rfl) ⟨862334, by rfl⟩ : syracuseStep 1149779 = 1724669) B1724669
theorem B1149809 : Blo 766334 1149809 := bstep (se 2 (by rfl) ⟨431178, by rfl⟩ : syracuseStep 1149809 = 862357) B862357
theorem B1149827 : Blo 766334 1149827 := bstep (se 1 (by rfl) ⟨862370, by rfl⟩ : syracuseStep 1149827 = 1724741) B1724741
theorem B4164493 : Blo 766334 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B1149857 : Blo 766334 1149857 := bstep (se 2 (by rfl) ⟨431196, by rfl⟩ : syracuseStep 1149857 = 862393) B862393
theorem B1149875 : Blo 766334 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B1149905 : Blo 766334 1149905 := bstep (se 2 (by rfl) ⟨431214, by rfl⟩ : syracuseStep 1149905 = 862429) B862429
theorem B1149923 : Blo 766334 1149923 := bstep (se 1 (by rfl) ⟨862442, by rfl⟩ : syracuseStep 1149923 = 1724885) B1724885
theorem B2591729 : Blo 766334 2591729 := bstep (se 2 (by rfl) ⟨971898, by rfl⟩ : syracuseStep 2591729 = 1943797) B1943797
theorem B1149953 : Blo 766334 1149953 := bstep (se 2 (by rfl) ⟨431232, by rfl⟩ : syracuseStep 1149953 = 862465) B862465
theorem B1149971 : Blo 766334 1149971 := bstep (se 1 (by rfl) ⟨862478, by rfl⟩ : syracuseStep 1149971 = 1724957) B1724957
theorem B1150001 : Blo 766334 1150001 := bstep (se 2 (by rfl) ⟨431250, by rfl⟩ : syracuseStep 1150001 = 862501) B862501
theorem B1150019 : Blo 766334 1150019 := bstep (se 1 (by rfl) ⟨862514, by rfl⟩ : syracuseStep 1150019 = 1725029) B1725029
theorem B1150049 : Blo 766334 1150049 := bstep (se 2 (by rfl) ⟨431268, by rfl⟩ : syracuseStep 1150049 = 862537) B862537
theorem B2919523 : Blo 766334 2919523 := bstep (se 1 (by rfl) ⟨2189642, by rfl⟩ : syracuseStep 2919523 = 4379285) B4379285
theorem B2460785 : Blo 766334 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B1150067 : Blo 766334 1150067 := bstep (se 1 (by rfl) ⟨862550, by rfl⟩ : syracuseStep 1150067 = 1725101) B1725101
theorem B1150097 : Blo 766334 1150097 := bstep (se 2 (by rfl) ⟨431286, by rfl⟩ : syracuseStep 1150097 = 862573) B862573
theorem B1150115 : Blo 766334 1150115 := bstep (se 1 (by rfl) ⟨862586, by rfl⟩ : syracuseStep 1150115 = 1725173) B1725173
theorem B1150145 : Blo 766334 1150145 := bstep (se 2 (by rfl) ⟨431304, by rfl⟩ : syracuseStep 1150145 = 862609) B862609
theorem B1150163 : Blo 766334 1150163 := bstep (se 1 (by rfl) ⟨862622, by rfl⟩ : syracuseStep 1150163 = 1725245) B1725245
theorem B1150193 : Blo 766334 1150193 := bstep (se 2 (by rfl) ⟨431322, by rfl⟩ : syracuseStep 1150193 = 862645) B862645
theorem B2133233 : Blo 766334 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B1150211 : Blo 766334 1150211 := bstep (se 1 (by rfl) ⟨862658, by rfl⟩ : syracuseStep 1150211 = 1725317) B1725317
theorem B1150241 : Blo 766334 1150241 := bstep (se 2 (by rfl) ⟨431340, by rfl⟩ : syracuseStep 1150241 = 862681) B862681
theorem B1150259 : Blo 766334 1150259 := bstep (se 1 (by rfl) ⟨862694, by rfl⟩ : syracuseStep 1150259 = 1725389) B1725389
theorem B1150289 : Blo 766334 1150289 := bstep (se 2 (by rfl) ⟨431358, by rfl⟩ : syracuseStep 1150289 = 862717) B862717
theorem B1150307 : Blo 766334 1150307 := bstep (se 1 (by rfl) ⟨862730, by rfl⟩ : syracuseStep 1150307 = 1725461) B1725461
theorem B1150337 : Blo 766334 1150337 := bstep (se 2 (by rfl) ⟨431376, by rfl⟩ : syracuseStep 1150337 = 862753) B862753
theorem B1150355 : Blo 766334 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1150385 : Blo 766334 1150385 := bstep (se 2 (by rfl) ⟨431394, by rfl⟩ : syracuseStep 1150385 = 862789) B862789
theorem B1150403 : Blo 766334 1150403 := bstep (se 1 (by rfl) ⟨862802, by rfl⟩ : syracuseStep 1150403 = 1725605) B1725605
theorem B1150433 : Blo 766334 1150433 := bstep (se 2 (by rfl) ⟨431412, by rfl⟩ : syracuseStep 1150433 = 862825) B862825
theorem B1150451 : Blo 766334 1150451 := bstep (se 1 (by rfl) ⟨862838, by rfl⟩ : syracuseStep 1150451 = 1725677) B1725677
theorem B2592269 : Blo 766334 2592269 := bstep (se 3 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 2592269 = 972101) B972101
theorem B1150481 : Blo 766334 1150481 := bstep (se 2 (by rfl) ⟨431430, by rfl⟩ : syracuseStep 1150481 = 862861) B862861
theorem B1150499 : Blo 766334 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B1150529 : Blo 766334 1150529 := bstep (se 2 (by rfl) ⟨431448, by rfl⟩ : syracuseStep 1150529 = 862897) B862897
theorem B2592323 : Blo 766334 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B1150547 : Blo 766334 1150547 := bstep (se 1 (by rfl) ⟨862910, by rfl⟩ : syracuseStep 1150547 = 1725821) B1725821
theorem B1150577 : Blo 766334 1150577 := bstep (se 2 (by rfl) ⟨431466, by rfl⟩ : syracuseStep 1150577 = 862933) B862933
theorem B1150595 : Blo 766334 1150595 := bstep (se 1 (by rfl) ⟨862946, by rfl⟩ : syracuseStep 1150595 = 1725893) B1725893
theorem B1314449 : Blo 766334 1314449 := bstep (se 2 (by rfl) ⟨492918, by rfl⟩ : syracuseStep 1314449 = 985837) B985837
theorem B1150625 : Blo 766334 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B1150643 : Blo 766334 1150643 := bstep (se 1 (by rfl) ⟨862982, by rfl⟩ : syracuseStep 1150643 = 1725965) B1725965
theorem B1150673 : Blo 766334 1150673 := bstep (se 2 (by rfl) ⟨431502, by rfl⟩ : syracuseStep 1150673 = 863005) B863005
theorem B1150691 : Blo 766334 1150691 := bstep (se 1 (by rfl) ⟨863018, by rfl⟩ : syracuseStep 1150691 = 1726037) B1726037
theorem B1150721 : Blo 766334 1150721 := bstep (se 2 (by rfl) ⟨431520, by rfl⟩ : syracuseStep 1150721 = 863041) B863041
theorem B1150739 : Blo 766334 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B1150769 : Blo 766334 1150769 := bstep (se 2 (by rfl) ⟨431538, by rfl⟩ : syracuseStep 1150769 = 863077) B863077
theorem B1150787 : Blo 766334 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B2592593 : Blo 766334 2592593 := bstep (se 2 (by rfl) ⟨972222, by rfl⟩ : syracuseStep 2592593 = 1944445) B1944445
theorem B1150817 : Blo 766334 1150817 := bstep (se 2 (by rfl) ⟨431556, by rfl⟩ : syracuseStep 1150817 = 863113) B863113
theorem B1150835 : Blo 766334 1150835 := bstep (se 1 (by rfl) ⟨863126, by rfl⟩ : syracuseStep 1150835 = 1726253) B1726253
theorem B1150865 : Blo 766334 1150865 := bstep (se 2 (by rfl) ⟨431574, by rfl⟩ : syracuseStep 1150865 = 863149) B863149
theorem B1150883 : Blo 766334 1150883 := bstep (se 1 (by rfl) ⟨863162, by rfl⟩ : syracuseStep 1150883 = 1726325) B1726325
theorem B3116963 : Blo 766334 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B1642403 : Blo 766334 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B1150913 : Blo 766334 1150913 := bstep (se 2 (by rfl) ⟨431592, by rfl⟩ : syracuseStep 1150913 = 863185) B863185
theorem B1150931 : Blo 766334 1150931 := bstep (se 1 (by rfl) ⟨863198, by rfl⟩ : syracuseStep 1150931 = 1726397) B1726397
theorem B8851427 : Blo 766334 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B1150961 : Blo 766334 1150961 := bstep (se 2 (by rfl) ⟨431610, by rfl⟩ : syracuseStep 1150961 = 863221) B863221
theorem B1150979 : Blo 766334 1150979 := bstep (se 1 (by rfl) ⟨863234, by rfl⟩ : syracuseStep 1150979 = 1726469) B1726469
theorem B1151009 : Blo 766334 1151009 := bstep (se 2 (by rfl) ⟨431628, by rfl⟩ : syracuseStep 1151009 = 863257) B863257
theorem B3280945 : Blo 766334 3280945 := bstep (se 2 (by rfl) ⟨1230354, by rfl⟩ : syracuseStep 3280945 = 2460709) B2460709
theorem B1151027 : Blo 766334 1151027 := bstep (se 1 (by rfl) ⟨863270, by rfl⟩ : syracuseStep 1151027 = 1726541) B1726541
theorem B1151057 : Blo 766334 1151057 := bstep (se 2 (by rfl) ⟨431646, by rfl⟩ : syracuseStep 1151057 = 863293) B863293
theorem B1151075 : Blo 766334 1151075 := bstep (se 1 (by rfl) ⟨863306, by rfl⟩ : syracuseStep 1151075 = 1726613) B1726613
theorem B1151105 : Blo 766334 1151105 := bstep (se 2 (by rfl) ⟨431664, by rfl⟩ : syracuseStep 1151105 = 863329) B863329
theorem B2330765 : Blo 766334 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B1151123 : Blo 766334 1151123 := bstep (se 1 (by rfl) ⟨863342, by rfl⟩ : syracuseStep 1151123 = 1726685) B1726685
theorem B1151153 : Blo 766334 1151153 := bstep (se 2 (by rfl) ⟨431682, by rfl⟩ : syracuseStep 1151153 = 863365) B863365
theorem B1151171 : Blo 766334 1151171 := bstep (se 1 (by rfl) ⟨863378, by rfl⟩ : syracuseStep 1151171 = 1726757) B1726757
theorem B1151201 : Blo 766334 1151201 := bstep (se 2 (by rfl) ⟨431700, by rfl⟩ : syracuseStep 1151201 = 863401) B863401
theorem B1151219 : Blo 766334 1151219 := bstep (se 1 (by rfl) ⟨863414, by rfl⟩ : syracuseStep 1151219 = 1726829) B1726829
theorem B1151249 : Blo 766334 1151249 := bstep (se 2 (by rfl) ⟨431718, by rfl⟩ : syracuseStep 1151249 = 863437) B863437
theorem B1151267 : Blo 766334 1151267 := bstep (se 1 (by rfl) ⟨863450, by rfl⟩ : syracuseStep 1151267 = 1726901) B1726901
theorem B1151297 : Blo 766334 1151297 := bstep (se 2 (by rfl) ⟨431736, by rfl⟩ : syracuseStep 1151297 = 863473) B863473
theorem B1151315 : Blo 766334 1151315 := bstep (se 1 (by rfl) ⟨863486, by rfl⟩ : syracuseStep 1151315 = 1726973) B1726973
theorem B2593133 : Blo 766334 2593133 := bstep (se 3 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 2593133 = 972425) B972425
theorem B1151345 : Blo 766334 1151345 := bstep (se 2 (by rfl) ⟨431754, by rfl⟩ : syracuseStep 1151345 = 863509) B863509
theorem B1151363 : Blo 766334 1151363 := bstep (se 1 (by rfl) ⟨863522, by rfl⟩ : syracuseStep 1151363 = 1727045) B1727045
theorem B1151393 : Blo 766334 1151393 := bstep (se 2 (by rfl) ⟨431772, by rfl⟩ : syracuseStep 1151393 = 863545) B863545
theorem B2593187 : Blo 766334 2593187 := bstep (se 1 (by rfl) ⟨1944890, by rfl⟩ : syracuseStep 2593187 = 3889781) B3889781
theorem B1151411 : Blo 766334 1151411 := bstep (se 1 (by rfl) ⟨863558, by rfl⟩ : syracuseStep 1151411 = 1727117) B1727117
theorem B1872323 : Blo 766334 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B1151441 : Blo 766334 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B1151459 : Blo 766334 1151459 := bstep (se 1 (by rfl) ⟨863594, by rfl⟩ : syracuseStep 1151459 = 1727189) B1727189
theorem B1151489 : Blo 766334 1151489 := bstep (se 2 (by rfl) ⟨431808, by rfl⟩ : syracuseStep 1151489 = 863617) B863617
theorem B1151507 : Blo 766334 1151507 := bstep (se 1 (by rfl) ⟨863630, by rfl⟩ : syracuseStep 1151507 = 1727261) B1727261
theorem B1479203 : Blo 766334 1479203 := bstep (se 1 (by rfl) ⟨1109402, by rfl⟩ : syracuseStep 1479203 = 2218805) B2218805
theorem B1151537 : Blo 766334 1151537 := bstep (se 2 (by rfl) ⟨431826, by rfl⟩ : syracuseStep 1151537 = 863653) B863653
theorem B1151555 : Blo 766334 1151555 := bstep (se 1 (by rfl) ⟨863666, by rfl⟩ : syracuseStep 1151555 = 1727333) B1727333
theorem B1151585 : Blo 766334 1151585 := bstep (se 2 (by rfl) ⟨431844, by rfl⟩ : syracuseStep 1151585 = 863689) B863689
theorem B1151603 : Blo 766334 1151603 := bstep (se 1 (by rfl) ⟨863702, by rfl⟩ : syracuseStep 1151603 = 1727405) B1727405
theorem B1151633 : Blo 766334 1151633 := bstep (se 2 (by rfl) ⟨431862, by rfl⟩ : syracuseStep 1151633 = 863725) B863725
theorem B1151651 : Blo 766334 1151651 := bstep (se 1 (by rfl) ⟨863738, by rfl⟩ : syracuseStep 1151651 = 1727477) B1727477
theorem B2593457 : Blo 766334 2593457 := bstep (se 2 (by rfl) ⟨972546, by rfl⟩ : syracuseStep 2593457 = 1945093) B1945093
theorem B1151681 : Blo 766334 1151681 := bstep (se 2 (by rfl) ⟨431880, by rfl⟩ : syracuseStep 1151681 = 863761) B863761
theorem B1151699 : Blo 766334 1151699 := bstep (se 1 (by rfl) ⟨863774, by rfl⟩ : syracuseStep 1151699 = 1727549) B1727549
theorem B1151729 : Blo 766334 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1151747 : Blo 766334 1151747 := bstep (se 1 (by rfl) ⟨863810, by rfl⟩ : syracuseStep 1151747 = 1727621) B1727621
theorem B1250051 : Blo 766334 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B1151777 : Blo 766334 1151777 := bstep (se 2 (by rfl) ⟨431916, by rfl⟩ : syracuseStep 1151777 = 863833) B863833
theorem B1151795 : Blo 766334 1151795 := bstep (se 1 (by rfl) ⟨863846, by rfl⟩ : syracuseStep 1151795 = 1727693) B1727693
theorem B1151825 : Blo 766334 1151825 := bstep (se 2 (by rfl) ⟨431934, by rfl⟩ : syracuseStep 1151825 = 863869) B863869
theorem B1151843 : Blo 766334 1151843 := bstep (se 1 (by rfl) ⟨863882, by rfl⟩ : syracuseStep 1151843 = 1727765) B1727765
theorem B1151873 : Blo 766334 1151873 := bstep (se 2 (by rfl) ⟨431952, by rfl⟩ : syracuseStep 1151873 = 863905) B863905
theorem B1151891 : Blo 766334 1151891 := bstep (se 1 (by rfl) ⟨863918, by rfl⟩ : syracuseStep 1151891 = 1727837) B1727837
theorem B1151921 : Blo 766334 1151921 := bstep (se 2 (by rfl) ⟨431970, by rfl⟩ : syracuseStep 1151921 = 863941) B863941
theorem B1151939 : Blo 766334 1151939 := bstep (se 1 (by rfl) ⟨863954, by rfl⟩ : syracuseStep 1151939 = 1727909) B1727909
theorem B1151969 : Blo 766334 1151969 := bstep (se 2 (by rfl) ⟨431988, by rfl⟩ : syracuseStep 1151969 = 863977) B863977
theorem B1151987 : Blo 766334 1151987 := bstep (se 1 (by rfl) ⟨863990, by rfl⟩ : syracuseStep 1151987 = 1727981) B1727981
theorem B1152017 : Blo 766334 1152017 := bstep (se 2 (by rfl) ⟨432006, by rfl⟩ : syracuseStep 1152017 = 864013) B864013
theorem B1152035 : Blo 766334 1152035 := bstep (se 1 (by rfl) ⟨864026, by rfl⟩ : syracuseStep 1152035 = 1728053) B1728053
theorem B922675 : Blo 766334 922675 := bstep (se 1 (by rfl) ⟨692006, by rfl⟩ : syracuseStep 922675 = 1384013) B1384013
theorem B1217587 : Blo 766334 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B1152065 : Blo 766334 1152065 := bstep (se 2 (by rfl) ⟨432024, by rfl⟩ : syracuseStep 1152065 = 864049) B864049
theorem B1315921 : Blo 766334 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1152083 : Blo 766334 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B1152113 : Blo 766334 1152113 := bstep (se 2 (by rfl) ⟨432042, by rfl⟩ : syracuseStep 1152113 = 864085) B864085
theorem B1152131 : Blo 766334 1152131 := bstep (se 1 (by rfl) ⟨864098, by rfl⟩ : syracuseStep 1152131 = 1728197) B1728197
theorem B1152161 : Blo 766334 1152161 := bstep (se 2 (by rfl) ⟨432060, by rfl⟩ : syracuseStep 1152161 = 864121) B864121
theorem B1152179 : Blo 766334 1152179 := bstep (se 1 (by rfl) ⟨864134, by rfl⟩ : syracuseStep 1152179 = 1728269) B1728269
theorem B2593997 : Blo 766334 2593997 := bstep (se 3 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 2593997 = 972749) B972749
theorem B1152209 : Blo 766334 1152209 := bstep (se 2 (by rfl) ⟨432078, by rfl⟩ : syracuseStep 1152209 = 864157) B864157
theorem B3151075 : Blo 766334 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B1152227 : Blo 766334 1152227 := bstep (se 1 (by rfl) ⟨864170, by rfl⟩ : syracuseStep 1152227 = 1728341) B1728341
theorem B1152257 : Blo 766334 1152257 := bstep (se 2 (by rfl) ⟨432096, by rfl⟩ : syracuseStep 1152257 = 864193) B864193
theorem B2594051 : Blo 766334 2594051 := bstep (se 1 (by rfl) ⟨1945538, by rfl⟩ : syracuseStep 2594051 = 3891077) B3891077
theorem B2921741 : Blo 766334 2921741 := bstep (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) B1095653
theorem B1152275 : Blo 766334 1152275 := bstep (se 1 (by rfl) ⟨864206, by rfl⟩ : syracuseStep 1152275 = 1728413) B1728413
theorem B1152305 : Blo 766334 1152305 := bstep (se 2 (by rfl) ⟨432114, by rfl⟩ : syracuseStep 1152305 = 864229) B864229
theorem B1152323 : Blo 766334 1152323 := bstep (se 1 (by rfl) ⟨864242, by rfl⟩ : syracuseStep 1152323 = 1728485) B1728485
theorem B1152353 : Blo 766334 1152353 := bstep (se 2 (by rfl) ⟨432132, by rfl⟩ : syracuseStep 1152353 = 864265) B864265
theorem B1152371 : Blo 766334 1152371 := bstep (se 1 (by rfl) ⟨864278, by rfl⟩ : syracuseStep 1152371 = 1728557) B1728557
theorem B1152401 : Blo 766334 1152401 := bstep (se 2 (by rfl) ⟨432150, by rfl⟩ : syracuseStep 1152401 = 864301) B864301
theorem B1152419 : Blo 766334 1152419 := bstep (se 1 (by rfl) ⟨864314, by rfl⟩ : syracuseStep 1152419 = 1728629) B1728629
theorem B1152449 : Blo 766334 1152449 := bstep (se 2 (by rfl) ⟨432168, by rfl⟩ : syracuseStep 1152449 = 864337) B864337
theorem B1152467 : Blo 766334 1152467 := bstep (se 1 (by rfl) ⟨864350, by rfl⟩ : syracuseStep 1152467 = 1728701) B1728701
theorem B1152497 : Blo 766334 1152497 := bstep (se 2 (by rfl) ⟨432186, by rfl⟩ : syracuseStep 1152497 = 864373) B864373
theorem B1152515 : Blo 766334 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B2594321 : Blo 766334 2594321 := bstep (se 2 (by rfl) ⟨972870, by rfl⟩ : syracuseStep 2594321 = 1945741) B1945741
theorem B1152545 : Blo 766334 1152545 := bstep (se 2 (by rfl) ⟨432204, by rfl⟩ : syracuseStep 1152545 = 864409) B864409
theorem B1152563 : Blo 766334 1152563 := bstep (se 1 (by rfl) ⟨864422, by rfl⟩ : syracuseStep 1152563 = 1728845) B1728845
theorem B1152593 : Blo 766334 1152593 := bstep (se 2 (by rfl) ⟨432222, by rfl⟩ : syracuseStep 1152593 = 864445) B864445
theorem B1152611 : Blo 766334 1152611 := bstep (se 1 (by rfl) ⟨864458, by rfl⟩ : syracuseStep 1152611 = 1728917) B1728917
theorem B1152641 : Blo 766334 1152641 := bstep (se 2 (by rfl) ⟨432240, by rfl⟩ : syracuseStep 1152641 = 864481) B864481
theorem B1152659 : Blo 766334 1152659 := bstep (se 1 (by rfl) ⟨864494, by rfl⟩ : syracuseStep 1152659 = 1728989) B1728989
theorem B1152689 : Blo 766334 1152689 := bstep (se 2 (by rfl) ⟨432258, by rfl⟩ : syracuseStep 1152689 = 864517) B864517
theorem B1152707 : Blo 766334 1152707 := bstep (se 1 (by rfl) ⟨864530, by rfl⟩ : syracuseStep 1152707 = 1729061) B1729061
theorem B1152737 : Blo 766334 1152737 := bstep (se 2 (by rfl) ⟨432276, by rfl⟩ : syracuseStep 1152737 = 864553) B864553
theorem B1152755 : Blo 766334 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B1152785 : Blo 766334 1152785 := bstep (se 2 (by rfl) ⟨432294, by rfl⟩ : syracuseStep 1152785 = 864589) B864589
theorem B1152803 : Blo 766334 1152803 := bstep (se 1 (by rfl) ⟨864602, by rfl⟩ : syracuseStep 1152803 = 1729205) B1729205
theorem B1152833 : Blo 766334 1152833 := bstep (se 2 (by rfl) ⟨432312, by rfl⟩ : syracuseStep 1152833 = 864625) B864625
theorem B1152851 : Blo 766334 1152851 := bstep (se 1 (by rfl) ⟨864638, by rfl⟩ : syracuseStep 1152851 = 1729277) B1729277
theorem B1152881 : Blo 766334 1152881 := bstep (se 2 (by rfl) ⟨432330, by rfl⟩ : syracuseStep 1152881 = 864661) B864661
theorem B1152899 : Blo 766334 1152899 := bstep (se 1 (by rfl) ⟨864674, by rfl⟩ : syracuseStep 1152899 = 1729349) B1729349
theorem B1644419 : Blo 766334 1644419 := bstep (se 1 (by rfl) ⟨1233314, by rfl⟩ : syracuseStep 1644419 = 2466629) B2466629
theorem B1152929 : Blo 766334 1152929 := bstep (se 2 (by rfl) ⟨432348, by rfl⟩ : syracuseStep 1152929 = 864697) B864697
theorem B1152947 : Blo 766334 1152947 := bstep (se 1 (by rfl) ⟨864710, by rfl⟩ : syracuseStep 1152947 = 1729421) B1729421
theorem B3282893 : Blo 766334 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1152977 : Blo 766334 1152977 := bstep (se 2 (by rfl) ⟨432366, by rfl⟩ : syracuseStep 1152977 = 864733) B864733
theorem B1152995 : Blo 766334 1152995 := bstep (se 1 (by rfl) ⟨864746, by rfl⟩ : syracuseStep 1152995 = 1729493) B1729493
theorem B1153025 : Blo 766334 1153025 := bstep (se 2 (by rfl) ⟨432384, by rfl⟩ : syracuseStep 1153025 = 864769) B864769
theorem B1153043 : Blo 766334 1153043 := bstep (se 1 (by rfl) ⟨864782, by rfl⟩ : syracuseStep 1153043 = 1729565) B1729565
theorem B2594861 : Blo 766334 2594861 := bstep (se 3 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 2594861 = 973073) B973073
theorem B1153073 : Blo 766334 1153073 := bstep (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) B864805
theorem B1153091 : Blo 766334 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B1153121 : Blo 766334 1153121 := bstep (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) B864841
theorem B2594915 : Blo 766334 2594915 := bstep (se 1 (by rfl) ⟨1946186, by rfl⟩ : syracuseStep 2594915 = 3892373) B3892373
theorem B5544035 : Blo 766334 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B1153139 : Blo 766334 1153139 := bstep (se 1 (by rfl) ⟨864854, by rfl⟩ : syracuseStep 1153139 = 1729709) B1729709
theorem B1153169 : Blo 766334 1153169 := bstep (se 2 (by rfl) ⟨432438, by rfl⟩ : syracuseStep 1153169 = 864877) B864877
theorem B1153187 : Blo 766334 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B3512483 : Blo 766334 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B1153217 : Blo 766334 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B1153235 : Blo 766334 1153235 := bstep (se 1 (by rfl) ⟨864926, by rfl⟩ : syracuseStep 1153235 = 1729853) B1729853
theorem B1153265 : Blo 766334 1153265 := bstep (se 2 (by rfl) ⟨432474, by rfl⟩ : syracuseStep 1153265 = 864949) B864949
theorem B1153283 : Blo 766334 1153283 := bstep (se 1 (by rfl) ⟨864962, by rfl⟩ : syracuseStep 1153283 = 1729925) B1729925
theorem B1153313 : Blo 766334 1153313 := bstep (se 2 (by rfl) ⟨432492, by rfl⟩ : syracuseStep 1153313 = 864985) B864985
theorem B1153331 : Blo 766334 1153331 := bstep (se 1 (by rfl) ⟨864998, by rfl⟩ : syracuseStep 1153331 = 1729997) B1729997
theorem B1153361 : Blo 766334 1153361 := bstep (se 2 (by rfl) ⟨432510, by rfl⟩ : syracuseStep 1153361 = 865021) B865021
theorem B1153379 : Blo 766334 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B2595185 : Blo 766334 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B1317235 : Blo 766334 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1153409 : Blo 766334 1153409 := bstep (se 2 (by rfl) ⟨432528, by rfl⟩ : syracuseStep 1153409 = 865057) B865057
theorem B3512717 : Blo 766334 3512717 := bstep (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) B1317269
theorem B1153427 : Blo 766334 1153427 := bstep (se 1 (by rfl) ⟨865070, by rfl⟩ : syracuseStep 1153427 = 1730141) B1730141
theorem B1939889 : Blo 766334 1939889 := bstep (se 2 (by rfl) ⟨727458, by rfl⟩ : syracuseStep 1939889 = 1454917) B1454917
theorem B1153457 : Blo 766334 1153457 := bstep (se 2 (by rfl) ⟨432546, by rfl⟩ : syracuseStep 1153457 = 865093) B865093
theorem B1153475 : Blo 766334 1153475 := bstep (se 1 (by rfl) ⟨865106, by rfl⟩ : syracuseStep 1153475 = 1730213) B1730213
theorem B2464195 : Blo 766334 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B1153505 : Blo 766334 1153505 := bstep (se 2 (by rfl) ⟨432564, by rfl⟩ : syracuseStep 1153505 = 865129) B865129
theorem B9869795 : Blo 766334 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B1153523 : Blo 766334 1153523 := bstep (se 1 (by rfl) ⟨865142, by rfl⟩ : syracuseStep 1153523 = 1730285) B1730285
theorem B1153553 : Blo 766334 1153553 := bstep (se 2 (by rfl) ⟨432582, by rfl⟩ : syracuseStep 1153553 = 865165) B865165
theorem B1153571 : Blo 766334 1153571 := bstep (se 1 (by rfl) ⟨865178, by rfl⟩ : syracuseStep 1153571 = 1730357) B1730357
theorem B2103853 : Blo 766334 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B1153601 : Blo 766334 1153601 := bstep (se 2 (by rfl) ⟨432600, by rfl⟩ : syracuseStep 1153601 = 865201) B865201
theorem B1153619 : Blo 766334 1153619 := bstep (se 1 (by rfl) ⟨865214, by rfl⟩ : syracuseStep 1153619 = 1730429) B1730429
theorem B1153649 : Blo 766334 1153649 := bstep (se 2 (by rfl) ⟨432618, by rfl⟩ : syracuseStep 1153649 = 865237) B865237
theorem B1153667 : Blo 766334 1153667 := bstep (se 1 (by rfl) ⟨865250, by rfl⟩ : syracuseStep 1153667 = 1730501) B1730501
theorem B1153697 : Blo 766334 1153697 := bstep (se 2 (by rfl) ⟨432636, by rfl⟩ : syracuseStep 1153697 = 865273) B865273
theorem B1153715 : Blo 766334 1153715 := bstep (se 1 (by rfl) ⟨865286, by rfl⟩ : syracuseStep 1153715 = 1730573) B1730573
theorem B6560453 : Blo 766334 6560453 := bstep (se 4 (by rfl) ⟨615042, by rfl⟩ : syracuseStep 6560453 = 1230085) B1230085
theorem B1153745 : Blo 766334 1153745 := bstep (se 2 (by rfl) ⟨432654, by rfl⟩ : syracuseStep 1153745 = 865309) B865309
theorem B2464465 : Blo 766334 2464465 := bstep (se 2 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 2464465 = 1848349) B1848349
theorem B1153763 : Blo 766334 1153763 := bstep (se 1 (by rfl) ⟨865322, by rfl⟩ : syracuseStep 1153763 = 1730645) B1730645
theorem B1153793 : Blo 766334 1153793 := bstep (se 2 (by rfl) ⟨432672, by rfl⟩ : syracuseStep 1153793 = 865345) B865345
theorem B1153811 : Blo 766334 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B1153841 : Blo 766334 1153841 := bstep (se 2 (by rfl) ⟨432690, by rfl⟩ : syracuseStep 1153841 = 865381) B865381
theorem B924467 : Blo 766334 924467 := bstep (se 1 (by rfl) ⟨693350, by rfl⟩ : syracuseStep 924467 = 1386701) B1386701
theorem B1153859 : Blo 766334 1153859 := bstep (se 1 (by rfl) ⟨865394, by rfl⟩ : syracuseStep 1153859 = 1730789) B1730789
theorem B1153889 : Blo 766334 1153889 := bstep (se 2 (by rfl) ⟨432708, by rfl⟩ : syracuseStep 1153889 = 865417) B865417
theorem B1153907 : Blo 766334 1153907 := bstep (se 1 (by rfl) ⟨865430, by rfl⟩ : syracuseStep 1153907 = 1730861) B1730861
theorem B2595725 : Blo 766334 2595725 := bstep (se 3 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 2595725 = 973397) B973397
theorem B1153937 : Blo 766334 1153937 := bstep (se 2 (by rfl) ⟨432726, by rfl⟩ : syracuseStep 1153937 = 865453) B865453
theorem B1153955 : Blo 766334 1153955 := bstep (se 1 (by rfl) ⟨865466, by rfl⟩ : syracuseStep 1153955 = 1730933) B1730933
theorem B1153985 : Blo 766334 1153985 := bstep (se 2 (by rfl) ⟨432744, by rfl⟩ : syracuseStep 1153985 = 865489) B865489
theorem B2595779 : Blo 766334 2595779 := bstep (se 1 (by rfl) ⟨1946834, by rfl⟩ : syracuseStep 2595779 = 3893669) B3893669
theorem B1154003 : Blo 766334 1154003 := bstep (se 1 (by rfl) ⟨865502, by rfl⟩ : syracuseStep 1154003 = 1731005) B1731005
theorem B1154033 : Blo 766334 1154033 := bstep (se 2 (by rfl) ⟨432762, by rfl⟩ : syracuseStep 1154033 = 865525) B865525
theorem B1154051 : Blo 766334 1154051 := bstep (se 1 (by rfl) ⟨865538, by rfl⟩ : syracuseStep 1154051 = 1731077) B1731077
theorem B1154081 : Blo 766334 1154081 := bstep (se 2 (by rfl) ⟨432780, by rfl⟩ : syracuseStep 1154081 = 865561) B865561
theorem B2104355 : Blo 766334 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B1154099 : Blo 766334 1154099 := bstep (se 1 (by rfl) ⟨865574, by rfl⟩ : syracuseStep 1154099 = 1731149) B1731149
theorem B5905477 : Blo 766334 5905477 := bstep (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) B1107277
theorem B1154129 : Blo 766334 1154129 := bstep (se 2 (by rfl) ⟨432798, by rfl⟩ : syracuseStep 1154129 = 865597) B865597
theorem B1154147 : Blo 766334 1154147 := bstep (se 1 (by rfl) ⟨865610, by rfl⟩ : syracuseStep 1154147 = 1731221) B1731221
theorem B1154177 : Blo 766334 1154177 := bstep (se 2 (by rfl) ⟨432816, by rfl⟩ : syracuseStep 1154177 = 865633) B865633
theorem B1154195 : Blo 766334 1154195 := bstep (se 1 (by rfl) ⟨865646, by rfl⟩ : syracuseStep 1154195 = 1731293) B1731293
theorem B1154225 : Blo 766334 1154225 := bstep (se 2 (by rfl) ⟨432834, by rfl⟩ : syracuseStep 1154225 = 865669) B865669
theorem B2071747 : Blo 766334 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B1154243 : Blo 766334 1154243 := bstep (se 1 (by rfl) ⟨865682, by rfl⟩ : syracuseStep 1154243 = 1731365) B1731365
theorem B4168901 : Blo 766334 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B2596049 : Blo 766334 2596049 := bstep (se 2 (by rfl) ⟨973518, by rfl⟩ : syracuseStep 2596049 = 1947037) B1947037
theorem B1154273 : Blo 766334 1154273 := bstep (se 2 (by rfl) ⟨432852, by rfl⟩ : syracuseStep 1154273 = 865705) B865705
theorem B1154291 : Blo 766334 1154291 := bstep (se 1 (by rfl) ⟨865718, by rfl⟩ : syracuseStep 1154291 = 1731437) B1731437
theorem B1154321 : Blo 766334 1154321 := bstep (se 2 (by rfl) ⟨432870, by rfl⟩ : syracuseStep 1154321 = 865741) B865741
theorem B1154339 : Blo 766334 1154339 := bstep (se 1 (by rfl) ⟨865754, by rfl⟩ : syracuseStep 1154339 = 1731509) B1731509
theorem B1154369 : Blo 766334 1154369 := bstep (se 2 (by rfl) ⟨432888, by rfl⟩ : syracuseStep 1154369 = 865777) B865777
theorem B1154387 : Blo 766334 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B2071921 : Blo 766334 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B1154417 : Blo 766334 1154417 := bstep (se 2 (by rfl) ⟨432906, by rfl⟩ : syracuseStep 1154417 = 865813) B865813
theorem B1154435 : Blo 766334 1154435 := bstep (se 1 (by rfl) ⟨865826, by rfl⟩ : syracuseStep 1154435 = 1731653) B1731653
theorem B1940881 : Blo 766334 1940881 := bstep (se 2 (by rfl) ⟨727830, by rfl⟩ : syracuseStep 1940881 = 1455661) B1455661
theorem B1154465 : Blo 766334 1154465 := bstep (se 2 (by rfl) ⟨432924, by rfl⟩ : syracuseStep 1154465 = 865849) B865849
theorem B4922801 : Blo 766334 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B1154483 : Blo 766334 1154483 := bstep (se 1 (by rfl) ⟨865862, by rfl⟩ : syracuseStep 1154483 = 1731725) B1731725
theorem B1154513 : Blo 766334 1154513 := bstep (se 2 (by rfl) ⟨432942, by rfl⟩ : syracuseStep 1154513 = 865885) B865885
theorem B1154531 : Blo 766334 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B1154561 : Blo 766334 1154561 := bstep (se 2 (by rfl) ⟨432960, by rfl⟩ : syracuseStep 1154561 = 865921) B865921
theorem B1154579 : Blo 766334 1154579 := bstep (se 1 (by rfl) ⟨865934, by rfl⟩ : syracuseStep 1154579 = 1731869) B1731869
theorem B1154609 : Blo 766334 1154609 := bstep (se 2 (by rfl) ⟨432978, by rfl⟩ : syracuseStep 1154609 = 865957) B865957
theorem B1154627 : Blo 766334 1154627 := bstep (se 1 (by rfl) ⟨865970, by rfl⟩ : syracuseStep 1154627 = 1731941) B1731941
theorem B6233669 : Blo 766334 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B1154657 : Blo 766334 1154657 := bstep (se 2 (by rfl) ⟨432996, by rfl⟩ : syracuseStep 1154657 = 865993) B865993
theorem B1384049 : Blo 766334 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B1154675 : Blo 766334 1154675 := bstep (se 1 (by rfl) ⟨866006, by rfl⟩ : syracuseStep 1154675 = 1732013) B1732013
theorem B1154705 : Blo 766334 1154705 := bstep (se 2 (by rfl) ⟨433014, by rfl⟩ : syracuseStep 1154705 = 866029) B866029
theorem B1941155 : Blo 766334 1941155 := bstep (se 1 (by rfl) ⟨1455866, by rfl⟩ : syracuseStep 1941155 = 2911733) B2911733
theorem B1154723 : Blo 766334 1154723 := bstep (se 1 (by rfl) ⟨866042, by rfl⟩ : syracuseStep 1154723 = 1732085) B1732085
theorem B1154753 : Blo 766334 1154753 := bstep (se 2 (by rfl) ⟨433032, by rfl⟩ : syracuseStep 1154753 = 866065) B866065
theorem B1154771 : Blo 766334 1154771 := bstep (se 1 (by rfl) ⟨866078, by rfl⟩ : syracuseStep 1154771 = 1732157) B1732157
theorem B2596589 : Blo 766334 2596589 := bstep (se 3 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 2596589 = 973721) B973721
theorem B1154801 : Blo 766334 1154801 := bstep (se 2 (by rfl) ⟨433050, by rfl⟩ : syracuseStep 1154801 = 866101) B866101
theorem B1154819 : Blo 766334 1154819 := bstep (se 1 (by rfl) ⟨866114, by rfl⟩ : syracuseStep 1154819 = 1732229) B1732229
theorem B1154849 : Blo 766334 1154849 := bstep (se 2 (by rfl) ⟨433068, by rfl⟩ : syracuseStep 1154849 = 866137) B866137
theorem B2596643 : Blo 766334 2596643 := bstep (se 1 (by rfl) ⟨1947482, by rfl⟩ : syracuseStep 2596643 = 3894965) B3894965
theorem B1154867 : Blo 766334 1154867 := bstep (se 1 (by rfl) ⟨866150, by rfl⟩ : syracuseStep 1154867 = 1732301) B1732301
theorem B2367299 : Blo 766334 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B1154897 : Blo 766334 1154897 := bstep (se 2 (by rfl) ⟨433086, by rfl⟩ : syracuseStep 1154897 = 866173) B866173
theorem B1941347 : Blo 766334 1941347 := bstep (se 1 (by rfl) ⟨1456010, by rfl⟩ : syracuseStep 1941347 = 2912021) B2912021
theorem B1154915 : Blo 766334 1154915 := bstep (se 1 (by rfl) ⟨866186, by rfl⟩ : syracuseStep 1154915 = 1732373) B1732373
theorem B1154945 : Blo 766334 1154945 := bstep (se 2 (by rfl) ⟨433104, by rfl⟩ : syracuseStep 1154945 = 866209) B866209
theorem B1384337 : Blo 766334 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B1154963 : Blo 766334 1154963 := bstep (se 1 (by rfl) ⟨866222, by rfl⟩ : syracuseStep 1154963 = 1732445) B1732445
theorem B1154993 : Blo 766334 1154993 := bstep (se 2 (by rfl) ⟨433122, by rfl⟩ : syracuseStep 1154993 = 866245) B866245
theorem B1155011 : Blo 766334 1155011 := bstep (se 1 (by rfl) ⟨866258, by rfl⟩ : syracuseStep 1155011 = 1732517) B1732517
theorem B1155041 : Blo 766334 1155041 := bstep (se 2 (by rfl) ⟨433140, by rfl⟩ : syracuseStep 1155041 = 866281) B866281
theorem B1155059 : Blo 766334 1155059 := bstep (se 1 (by rfl) ⟨866294, by rfl⟩ : syracuseStep 1155059 = 1732589) B1732589
theorem B1155089 : Blo 766334 1155089 := bstep (se 2 (by rfl) ⟨433158, by rfl⟩ : syracuseStep 1155089 = 866317) B866317
theorem B1155107 : Blo 766334 1155107 := bstep (se 1 (by rfl) ⟨866330, by rfl⟩ : syracuseStep 1155107 = 1732661) B1732661
theorem B2596913 : Blo 766334 2596913 := bstep (se 2 (by rfl) ⟨973842, by rfl⟩ : syracuseStep 2596913 = 1947685) B1947685
theorem B1155137 : Blo 766334 1155137 := bstep (se 2 (by rfl) ⟨433176, by rfl⟩ : syracuseStep 1155137 = 866353) B866353
theorem B1155155 : Blo 766334 1155155 := bstep (se 1 (by rfl) ⟨866366, by rfl⟩ : syracuseStep 1155155 = 1732733) B1732733
theorem B1155185 : Blo 766334 1155185 := bstep (se 2 (by rfl) ⟨433194, by rfl⟩ : syracuseStep 1155185 = 866389) B866389
theorem B2924657 : Blo 766334 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1155203 : Blo 766334 1155203 := bstep (se 1 (by rfl) ⟨866402, by rfl⟩ : syracuseStep 1155203 = 1732805) B1732805
theorem B1155233 : Blo 766334 1155233 := bstep (se 2 (by rfl) ⟨433212, by rfl⟩ : syracuseStep 1155233 = 866425) B866425
theorem B1155251 : Blo 766334 1155251 := bstep (se 1 (by rfl) ⟨866438, by rfl⟩ : syracuseStep 1155251 = 1732877) B1732877
theorem B1155281 : Blo 766334 1155281 := bstep (se 2 (by rfl) ⟨433230, by rfl⟩ : syracuseStep 1155281 = 866461) B866461
theorem B1155299 : Blo 766334 1155299 := bstep (se 1 (by rfl) ⟨866474, by rfl⟩ : syracuseStep 1155299 = 1732949) B1732949
theorem B5546225 : Blo 766334 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B1155329 : Blo 766334 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B2466065 : Blo 766334 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B1155347 : Blo 766334 1155347 := bstep (se 1 (by rfl) ⟨866510, by rfl⟩ : syracuseStep 1155347 = 1733021) B1733021
theorem B1155377 : Blo 766334 1155377 := bstep (se 2 (by rfl) ⟨433266, by rfl⟩ : syracuseStep 1155377 = 866533) B866533
theorem B1155395 : Blo 766334 1155395 := bstep (se 1 (by rfl) ⟨866546, by rfl⟩ : syracuseStep 1155395 = 1733093) B1733093
theorem B1155425 : Blo 766334 1155425 := bstep (se 2 (by rfl) ⟨433284, by rfl⟩ : syracuseStep 1155425 = 866569) B866569
theorem B1155443 : Blo 766334 1155443 := bstep (se 1 (by rfl) ⟨866582, by rfl⟩ : syracuseStep 1155443 = 1733165) B1733165
theorem B1155473 : Blo 766334 1155473 := bstep (se 2 (by rfl) ⟨433302, by rfl⟩ : syracuseStep 1155473 = 866605) B866605
theorem B1155491 : Blo 766334 1155491 := bstep (se 1 (by rfl) ⟨866618, by rfl⟩ : syracuseStep 1155491 = 1733237) B1733237
theorem B3121699 : Blo 766334 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B2597453 : Blo 766334 2597453 := bstep (se 3 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 2597453 = 974045) B974045
theorem B2466413 : Blo 766334 2466413 := bstep (se 3 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 2466413 = 924905) B924905
theorem B2597507 : Blo 766334 2597507 := bstep (se 1 (by rfl) ⟨1948130, by rfl⟩ : syracuseStep 2597507 = 3896261) B3896261
theorem B2073251 : Blo 766334 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B1942289 : Blo 766334 1942289 := bstep (se 2 (by rfl) ⟨728358, by rfl⟩ : syracuseStep 1942289 = 1456717) B1456717
theorem B1942339 : Blo 766334 1942339 := bstep (se 1 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 1942339 = 2913509) B2913509
theorem B5907269 : Blo 766334 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B307635029 : Blo 766334 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B2597777 : Blo 766334 2597777 := bstep (se 2 (by rfl) ⟨974166, by rfl⟩ : syracuseStep 2597777 = 1948333) B1948333
theorem B1942481 : Blo 766334 1942481 := bstep (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) B1456861
theorem B14754869 : Blo 766334 14754869 := bstep (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) B1383269
theorem B5547149 : Blo 766334 5547149 := bstep (se 3 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 5547149 = 2080181) B2080181
theorem B2335921 : Blo 766334 2335921 := bstep (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) B1751941
theorem B2335949 : Blo 766334 2335949 := bstep (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) B875981
theorem B4367621 : Blo 766334 4367621 := bstep (se 4 (by rfl) ⟨409464, by rfl⟩ : syracuseStep 4367621 = 818929) B818929
theorem B2598317 : Blo 766334 2598317 := bstep (se 3 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 2598317 = 974369) B974369
theorem B1385923 : Blo 766334 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B2598371 : Blo 766334 2598371 := bstep (se 1 (by rfl) ⟨1948778, by rfl⟩ : syracuseStep 2598371 = 3897557) B3897557
theorem B1091171 : Blo 766334 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B4368077 : Blo 766334 4368077 := bstep (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) B1638029
theorem B2598641 : Blo 766334 2598641 := bstep (se 2 (by rfl) ⟨974490, by rfl⟩ : syracuseStep 2598641 = 1948981) B1948981
theorem B4925261 : Blo 766334 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B3286925 : Blo 766334 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B1943473 : Blo 766334 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B862195 : Blo 766334 862195 := bstep (se 1 (by rfl) ⟨646646, by rfl⟩ : syracuseStep 862195 = 1293293) B1293293
theorem B1386499 : Blo 766334 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B862339 : Blo 766334 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B1943747 : Blo 766334 1943747 := bstep (se 1 (by rfl) ⟨1457810, by rfl⟩ : syracuseStep 1943747 = 2915621) B2915621
theorem B1091809 : Blo 766334 1091809 := bstep (se 2 (by rfl) ⟨409428, by rfl⟩ : syracuseStep 1091809 = 818857) B818857
theorem B3287267 : Blo 766334 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B5548301 : Blo 766334 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B2599181 : Blo 766334 2599181 := bstep (se 3 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 2599181 = 974693) B974693
theorem B862483 : Blo 766334 862483 := bstep (se 1 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 862483 = 1293725) B1293725
theorem B2599235 : Blo 766334 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1943939 : Blo 766334 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B862627 : Blo 766334 862627 := bstep (se 1 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 862627 = 1293941) B1293941
theorem B2107949 : Blo 766334 2107949 := bstep (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) B790481
theorem B1092145 : Blo 766334 1092145 := bstep (se 2 (by rfl) ⟨409554, by rfl⟩ : syracuseStep 1092145 = 819109) B819109
theorem B862771 : Blo 766334 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B2599505 : Blo 766334 2599505 := bstep (se 2 (by rfl) ⟨974814, by rfl⟩ : syracuseStep 2599505 = 1949629) B1949629
theorem B3287729 : Blo 766334 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B862915 : Blo 766334 862915 := bstep (se 1 (by rfl) ⟨647186, by rfl⟩ : syracuseStep 862915 = 1294373) B1294373
theorem B863059 : Blo 766334 863059 := bstep (se 1 (by rfl) ⟨647294, by rfl⟩ : syracuseStep 863059 = 1294589) B1294589
theorem B1846147 : Blo 766334 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B2075597 : Blo 766334 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B2960333 : Blo 766334 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B863203 : Blo 766334 863203 := bstep (se 1 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 863203 = 1294805) B1294805
theorem B2337869 : Blo 766334 2337869 := bstep (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) B876701
theorem B863347 : Blo 766334 863347 := bstep (se 1 (by rfl) ⟨647510, by rfl⟩ : syracuseStep 863347 = 1295021) B1295021
theorem B1092737 : Blo 766334 1092737 := bstep (se 2 (by rfl) ⟨409776, by rfl⟩ : syracuseStep 1092737 = 819553) B819553
theorem B863491 : Blo 766334 863491 := bstep (se 1 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 863491 = 1295237) B1295237
theorem B1944881 : Blo 766334 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B1944931 : Blo 766334 1944931 := bstep (se 1 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 1944931 = 2917397) B2917397
theorem B863635 : Blo 766334 863635 := bstep (se 1 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 863635 = 1295453) B1295453
theorem B1945073 : Blo 766334 1945073 := bstep (se 2 (by rfl) ⟨729402, by rfl⟩ : syracuseStep 1945073 = 1458805) B1458805
theorem B4664837 : Blo 766334 4664837 := bstep (se 4 (by rfl) ⟨437328, by rfl⟩ : syracuseStep 4664837 = 874657) B874657
theorem B863779 : Blo 766334 863779 := bstep (se 1 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 863779 = 1295669) B1295669
theorem B1846819 : Blo 766334 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B1093267 : Blo 766334 1093267 := bstep (se 1 (by rfl) ⟨819950, by rfl⟩ : syracuseStep 1093267 = 1639901) B1639901
theorem B1748657 : Blo 766334 1748657 := bstep (se 2 (by rfl) ⟨655746, by rfl⟩ : syracuseStep 1748657 = 1311493) B1311493
theorem B863923 : Blo 766334 863923 := bstep (se 1 (by rfl) ⟨647942, by rfl⟩ : syracuseStep 863923 = 1295885) B1295885
theorem B2338541 : Blo 766334 2338541 := bstep (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) B876953
theorem B864067 : Blo 766334 864067 := bstep (se 1 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 864067 = 1296101) B1296101
theorem B2076625 : Blo 766334 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B864211 : Blo 766334 864211 := bstep (se 1 (by rfl) ⟨648158, by rfl⟩ : syracuseStep 864211 = 1296317) B1296317
theorem B5681123 : Blo 766334 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B1093603 : Blo 766334 1093603 := bstep (se 1 (by rfl) ⟨820202, by rfl⟩ : syracuseStep 1093603 = 1640405) B1640405
theorem B1847281 : Blo 766334 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B4927493 : Blo 766334 4927493 := bstep (se 4 (by rfl) ⟨461952, by rfl⟩ : syracuseStep 4927493 = 923905) B923905
theorem B1847377 : Blo 766334 1847377 := bstep (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) B1385533
theorem B864355 : Blo 766334 864355 := bstep (se 1 (by rfl) ⟨648266, by rfl⟩ : syracuseStep 864355 = 1296533) B1296533
theorem B864499 : Blo 766334 864499 := bstep (se 1 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 864499 = 1296749) B1296749
theorem B766339 : Blo 766334 766339 := bstep (se 1 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 766339 = 1149509) B1149509
theorem B864643 : Blo 766334 864643 := bstep (se 1 (by rfl) ⟨648482, by rfl⟩ : syracuseStep 864643 = 1296965) B1296965
theorem B766355 : Blo 766334 766355 := bstep (se 1 (by rfl) ⟨574766, by rfl⟩ : syracuseStep 766355 = 1149533) B1149533
theorem B766371 : Blo 766334 766371 := bstep (se 1 (by rfl) ⟨574778, by rfl⟩ : syracuseStep 766371 = 1149557) B1149557
theorem B766387 : Blo 766334 766387 := bstep (se 1 (by rfl) ⟨574790, by rfl⟩ : syracuseStep 766387 = 1149581) B1149581
theorem B766403 : Blo 766334 766403 := bstep (se 1 (by rfl) ⟨574802, by rfl⟩ : syracuseStep 766403 = 1149605) B1149605
theorem B1946065 : Blo 766334 1946065 := bstep (se 2 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 1946065 = 1459549) B1459549
theorem B766419 : Blo 766334 766419 := bstep (se 1 (by rfl) ⟨574814, by rfl⟩ : syracuseStep 766419 = 1149629) B1149629
theorem B766435 : Blo 766334 766435 := bstep (se 1 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 766435 = 1149653) B1149653
theorem B766451 : Blo 766334 766451 := bstep (se 1 (by rfl) ⟨574838, by rfl⟩ : syracuseStep 766451 = 1149677) B1149677
theorem B766467 : Blo 766334 766467 := bstep (se 1 (by rfl) ⟨574850, by rfl⟩ : syracuseStep 766467 = 1149701) B1149701
theorem B1094161 : Blo 766334 1094161 := bstep (se 2 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 1094161 = 820621) B820621
theorem B766483 : Blo 766334 766483 := bstep (se 1 (by rfl) ⟨574862, by rfl⟩ : syracuseStep 766483 = 1149725) B1149725
theorem B864787 : Blo 766334 864787 := bstep (se 1 (by rfl) ⟨648590, by rfl⟩ : syracuseStep 864787 = 1297181) B1297181
theorem B766499 : Blo 766334 766499 := bstep (se 1 (by rfl) ⟨574874, by rfl⟩ : syracuseStep 766499 = 1149749) B1149749
theorem B4370993 : Blo 766334 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B766515 : Blo 766334 766515 := bstep (se 1 (by rfl) ⟨574886, by rfl⟩ : syracuseStep 766515 = 1149773) B1149773
theorem B1094195 : Blo 766334 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B766531 : Blo 766334 766531 := bstep (se 1 (by rfl) ⟨574898, by rfl⟩ : syracuseStep 766531 = 1149797) B1149797
theorem B766547 : Blo 766334 766547 := bstep (se 1 (by rfl) ⟨574910, by rfl⟩ : syracuseStep 766547 = 1149821) B1149821
theorem B766563 : Blo 766334 766563 := bstep (se 1 (by rfl) ⟨574922, by rfl⟩ : syracuseStep 766563 = 1149845) B1149845
theorem B2077283 : Blo 766334 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B766579 : Blo 766334 766579 := bstep (se 1 (by rfl) ⟨574934, by rfl⟩ : syracuseStep 766579 = 1149869) B1149869
theorem B766595 : Blo 766334 766595 := bstep (se 1 (by rfl) ⟨574946, by rfl⟩ : syracuseStep 766595 = 1149893) B1149893
theorem B7385741 : Blo 766334 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B766611 : Blo 766334 766611 := bstep (se 1 (by rfl) ⟨574958, by rfl⟩ : syracuseStep 766611 = 1149917) B1149917
theorem B766627 : Blo 766334 766627 := bstep (se 1 (by rfl) ⟨574970, by rfl⟩ : syracuseStep 766627 = 1149941) B1149941
theorem B864931 : Blo 766334 864931 := bstep (se 1 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 864931 = 1297397) B1297397
theorem B766643 : Blo 766334 766643 := bstep (se 1 (by rfl) ⟨574982, by rfl⟩ : syracuseStep 766643 = 1149965) B1149965
theorem B766659 : Blo 766334 766659 := bstep (se 1 (by rfl) ⟨574994, by rfl⟩ : syracuseStep 766659 = 1149989) B1149989
theorem B766675 : Blo 766334 766675 := bstep (se 1 (by rfl) ⟨575006, by rfl⟩ : syracuseStep 766675 = 1150013) B1150013
theorem B766691 : Blo 766334 766691 := bstep (se 1 (by rfl) ⟨575018, by rfl⟩ : syracuseStep 766691 = 1150037) B1150037
theorem B1946339 : Blo 766334 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B2634481 : Blo 766334 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B766707 : Blo 766334 766707 := bstep (se 1 (by rfl) ⟨575030, by rfl⟩ : syracuseStep 766707 = 1150061) B1150061
theorem B766723 : Blo 766334 766723 := bstep (se 1 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 766723 = 1150085) B1150085
theorem B766739 : Blo 766334 766739 := bstep (se 1 (by rfl) ⟨575054, by rfl⟩ : syracuseStep 766739 = 1150109) B1150109
theorem B766755 : Blo 766334 766755 := bstep (se 1 (by rfl) ⟨575066, by rfl⟩ : syracuseStep 766755 = 1150133) B1150133
theorem B766771 : Blo 766334 766771 := bstep (se 1 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 766771 = 1150157) B1150157
theorem B865075 : Blo 766334 865075 := bstep (se 1 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 865075 = 1297613) B1297613
theorem B766787 : Blo 766334 766787 := bstep (se 1 (by rfl) ⟨575090, by rfl⟩ : syracuseStep 766787 = 1150181) B1150181
theorem B2372429 : Blo 766334 2372429 := bstep (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) B889661
theorem B766803 : Blo 766334 766803 := bstep (se 1 (by rfl) ⟨575102, by rfl⟩ : syracuseStep 766803 = 1150205) B1150205
theorem B766819 : Blo 766334 766819 := bstep (se 1 (by rfl) ⟨575114, by rfl⟩ : syracuseStep 766819 = 1150229) B1150229
theorem B766835 : Blo 766334 766835 := bstep (se 1 (by rfl) ⟨575126, by rfl⟩ : syracuseStep 766835 = 1150253) B1150253
theorem B766851 : Blo 766334 766851 := bstep (se 1 (by rfl) ⟨575138, by rfl⟩ : syracuseStep 766851 = 1150277) B1150277
theorem B1454993 : Blo 766334 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B766867 : Blo 766334 766867 := bstep (se 1 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 766867 = 1150301) B1150301
theorem B766883 : Blo 766334 766883 := bstep (se 1 (by rfl) ⟨575162, by rfl⟩ : syracuseStep 766883 = 1150325) B1150325
theorem B1946531 : Blo 766334 1946531 := bstep (se 1 (by rfl) ⟨1459898, by rfl⟩ : syracuseStep 1946531 = 2919797) B2919797
theorem B1749937 : Blo 766334 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B766899 : Blo 766334 766899 := bstep (se 1 (by rfl) ⟨575174, by rfl⟩ : syracuseStep 766899 = 1150349) B1150349
theorem B766915 : Blo 766334 766915 := bstep (se 1 (by rfl) ⟨575186, by rfl⟩ : syracuseStep 766915 = 1150373) B1150373
theorem B865219 : Blo 766334 865219 := bstep (se 1 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 865219 = 1297829) B1297829
theorem B766931 : Blo 766334 766931 := bstep (se 1 (by rfl) ⟨575198, by rfl⟩ : syracuseStep 766931 = 1150397) B1150397
theorem B766947 : Blo 766334 766947 := bstep (se 1 (by rfl) ⟨575210, by rfl⟩ : syracuseStep 766947 = 1150421) B1150421
theorem B15774691 : Blo 766334 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B766963 : Blo 766334 766963 := bstep (se 1 (by rfl) ⟨575222, by rfl⟩ : syracuseStep 766963 = 1150445) B1150445
theorem B766979 : Blo 766334 766979 := bstep (se 1 (by rfl) ⟨575234, by rfl⟩ : syracuseStep 766979 = 1150469) B1150469
theorem B766995 : Blo 766334 766995 := bstep (se 1 (by rfl) ⟨575246, by rfl⟩ : syracuseStep 766995 = 1150493) B1150493
theorem B767011 : Blo 766334 767011 := bstep (se 1 (by rfl) ⟨575258, by rfl⟩ : syracuseStep 767011 = 1150517) B1150517
theorem B767027 : Blo 766334 767027 := bstep (se 1 (by rfl) ⟨575270, by rfl⟩ : syracuseStep 767027 = 1150541) B1150541
theorem B767043 : Blo 766334 767043 := bstep (se 1 (by rfl) ⟨575282, by rfl⟩ : syracuseStep 767043 = 1150565) B1150565
theorem B767059 : Blo 766334 767059 := bstep (se 1 (by rfl) ⟨575294, by rfl⟩ : syracuseStep 767059 = 1150589) B1150589
theorem B865363 : Blo 766334 865363 := bstep (se 1 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 865363 = 1298045) B1298045
theorem B1094753 : Blo 766334 1094753 := bstep (se 2 (by rfl) ⟨410532, by rfl⟩ : syracuseStep 1094753 = 821065) B821065
theorem B767075 : Blo 766334 767075 := bstep (se 1 (by rfl) ⟨575306, by rfl⟩ : syracuseStep 767075 = 1150613) B1150613
theorem B767091 : Blo 766334 767091 := bstep (se 1 (by rfl) ⟨575318, by rfl⟩ : syracuseStep 767091 = 1150637) B1150637
theorem B767107 : Blo 766334 767107 := bstep (se 1 (by rfl) ⟨575330, by rfl⟩ : syracuseStep 767107 = 1150661) B1150661
theorem B767123 : Blo 766334 767123 := bstep (se 1 (by rfl) ⟨575342, by rfl⟩ : syracuseStep 767123 = 1150685) B1150685
theorem B767139 : Blo 766334 767139 := bstep (se 1 (by rfl) ⟨575354, by rfl⟩ : syracuseStep 767139 = 1150709) B1150709
theorem B1094833 : Blo 766334 1094833 := bstep (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) B821125
theorem B767155 : Blo 766334 767155 := bstep (se 1 (by rfl) ⟨575366, by rfl⟩ : syracuseStep 767155 = 1150733) B1150733
theorem B767171 : Blo 766334 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B2634947 : Blo 766334 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B767187 : Blo 766334 767187 := bstep (se 1 (by rfl) ⟨575390, by rfl⟩ : syracuseStep 767187 = 1150781) B1150781
theorem B865507 : Blo 766334 865507 := bstep (se 1 (by rfl) ⟨649130, by rfl⟩ : syracuseStep 865507 = 1298261) B1298261
theorem B767203 : Blo 766334 767203 := bstep (se 1 (by rfl) ⟨575402, by rfl⟩ : syracuseStep 767203 = 1150805) B1150805
theorem B767219 : Blo 766334 767219 := bstep (se 1 (by rfl) ⟨575414, by rfl⟩ : syracuseStep 767219 = 1150829) B1150829
theorem B767235 : Blo 766334 767235 := bstep (se 1 (by rfl) ⟨575426, by rfl⟩ : syracuseStep 767235 = 1150853) B1150853
theorem B767251 : Blo 766334 767251 := bstep (se 1 (by rfl) ⟨575438, by rfl⟩ : syracuseStep 767251 = 1150877) B1150877
theorem B767267 : Blo 766334 767267 := bstep (se 1 (by rfl) ⟨575450, by rfl⟩ : syracuseStep 767267 = 1150901) B1150901
theorem B4437283 : Blo 766334 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B767283 : Blo 766334 767283 := bstep (se 1 (by rfl) ⟨575462, by rfl⟩ : syracuseStep 767283 = 1150925) B1150925
theorem B767299 : Blo 766334 767299 := bstep (se 1 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 767299 = 1150949) B1150949
theorem B767315 : Blo 766334 767315 := bstep (se 1 (by rfl) ⟨575486, by rfl⟩ : syracuseStep 767315 = 1150973) B1150973
theorem B767331 : Blo 766334 767331 := bstep (se 1 (by rfl) ⟨575498, by rfl⟩ : syracuseStep 767331 = 1150997) B1150997
theorem B767347 : Blo 766334 767347 := bstep (se 1 (by rfl) ⟨575510, by rfl⟩ : syracuseStep 767347 = 1151021) B1151021
theorem B865651 : Blo 766334 865651 := bstep (se 1 (by rfl) ⟨649238, by rfl⟩ : syracuseStep 865651 = 1298477) B1298477
theorem B767363 : Blo 766334 767363 := bstep (se 1 (by rfl) ⟨575522, by rfl⟩ : syracuseStep 767363 = 1151045) B1151045
theorem B2635139 : Blo 766334 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B18691469 : Blo 766334 18691469 := bstep (se 3 (by rfl) ⟨3504650, by rfl⟩ : syracuseStep 18691469 = 7009301) B7009301
theorem B767379 : Blo 766334 767379 := bstep (se 1 (by rfl) ⟨575534, by rfl⟩ : syracuseStep 767379 = 1151069) B1151069
theorem B767395 : Blo 766334 767395 := bstep (se 1 (by rfl) ⟨575546, by rfl⟩ : syracuseStep 767395 = 1151093) B1151093
theorem B767411 : Blo 766334 767411 := bstep (se 1 (by rfl) ⟨575558, by rfl⟩ : syracuseStep 767411 = 1151117) B1151117
theorem B767427 : Blo 766334 767427 := bstep (se 1 (by rfl) ⟨575570, by rfl⟩ : syracuseStep 767427 = 1151141) B1151141
theorem B767443 : Blo 766334 767443 := bstep (se 1 (by rfl) ⟨575582, by rfl⟩ : syracuseStep 767443 = 1151165) B1151165
theorem B767459 : Blo 766334 767459 := bstep (se 1 (by rfl) ⟨575594, by rfl⟩ : syracuseStep 767459 = 1151189) B1151189
theorem B767475 : Blo 766334 767475 := bstep (se 1 (by rfl) ⟨575606, by rfl⟩ : syracuseStep 767475 = 1151213) B1151213
theorem B767491 : Blo 766334 767491 := bstep (se 1 (by rfl) ⟨575618, by rfl⟩ : syracuseStep 767491 = 1151237) B1151237
theorem B865795 : Blo 766334 865795 := bstep (se 1 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 865795 = 1298693) B1298693
theorem B767507 : Blo 766334 767507 := bstep (se 1 (by rfl) ⟨575630, by rfl⟩ : syracuseStep 767507 = 1151261) B1151261
theorem B767523 : Blo 766334 767523 := bstep (se 1 (by rfl) ⟨575642, by rfl⟩ : syracuseStep 767523 = 1151285) B1151285
theorem B767539 : Blo 766334 767539 := bstep (se 1 (by rfl) ⟨575654, by rfl⟩ : syracuseStep 767539 = 1151309) B1151309
theorem B767555 : Blo 766334 767555 := bstep (se 1 (by rfl) ⟨575666, by rfl⟩ : syracuseStep 767555 = 1151333) B1151333
theorem B767571 : Blo 766334 767571 := bstep (se 1 (by rfl) ⟨575678, by rfl⟩ : syracuseStep 767571 = 1151357) B1151357
theorem B3880547 : Blo 766334 3880547 := bstep (se 1 (by rfl) ⟨2910410, by rfl⟩ : syracuseStep 3880547 = 5820821) B5820821
theorem B767587 : Blo 766334 767587 := bstep (se 1 (by rfl) ⟨575690, by rfl⟩ : syracuseStep 767587 = 1151381) B1151381
theorem B767603 : Blo 766334 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B767619 : Blo 766334 767619 := bstep (se 1 (by rfl) ⟨575714, by rfl⟩ : syracuseStep 767619 = 1151429) B1151429
theorem B767635 : Blo 766334 767635 := bstep (se 1 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 767635 = 1151453) B1151453
theorem B865939 : Blo 766334 865939 := bstep (se 1 (by rfl) ⟨649454, by rfl⟩ : syracuseStep 865939 = 1298909) B1298909
theorem B767651 : Blo 766334 767651 := bstep (se 1 (by rfl) ⟨575738, by rfl⟩ : syracuseStep 767651 = 1151477) B1151477
theorem B767667 : Blo 766334 767667 := bstep (se 1 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 767667 = 1151501) B1151501
theorem B767683 : Blo 766334 767683 := bstep (se 1 (by rfl) ⟨575762, by rfl⟩ : syracuseStep 767683 = 1151525) B1151525
theorem B767699 : Blo 766334 767699 := bstep (se 1 (by rfl) ⟨575774, by rfl⟩ : syracuseStep 767699 = 1151549) B1151549
theorem B767715 : Blo 766334 767715 := bstep (se 1 (by rfl) ⟨575786, by rfl⟩ : syracuseStep 767715 = 1151573) B1151573
theorem B2340593 : Blo 766334 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B767731 : Blo 766334 767731 := bstep (se 1 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 767731 = 1151597) B1151597
theorem B767747 : Blo 766334 767747 := bstep (se 1 (by rfl) ⟨575810, by rfl⟩ : syracuseStep 767747 = 1151621) B1151621
theorem B1455889 : Blo 766334 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B767763 : Blo 766334 767763 := bstep (se 1 (by rfl) ⟨575822, by rfl⟩ : syracuseStep 767763 = 1151645) B1151645
theorem B767779 : Blo 766334 767779 := bstep (se 1 (by rfl) ⟨575834, by rfl⟩ : syracuseStep 767779 = 1151669) B1151669
theorem B866083 : Blo 766334 866083 := bstep (se 1 (by rfl) ⟨649562, by rfl⟩ : syracuseStep 866083 = 1299125) B1299125
theorem B767795 : Blo 766334 767795 := bstep (se 1 (by rfl) ⟨575846, by rfl⟩ : syracuseStep 767795 = 1151693) B1151693
theorem B767811 : Blo 766334 767811 := bstep (se 1 (by rfl) ⟨575858, by rfl⟩ : syracuseStep 767811 = 1151717) B1151717
theorem B1947473 : Blo 766334 1947473 := bstep (se 2 (by rfl) ⟨730302, by rfl⟩ : syracuseStep 1947473 = 1460605) B1460605
theorem B767827 : Blo 766334 767827 := bstep (se 1 (by rfl) ⟨575870, by rfl⟩ : syracuseStep 767827 = 1151741) B1151741
theorem B767843 : Blo 766334 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B767859 : Blo 766334 767859 := bstep (se 1 (by rfl) ⟨575894, by rfl⟩ : syracuseStep 767859 = 1151789) B1151789
theorem B1947523 : Blo 766334 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B767875 : Blo 766334 767875 := bstep (se 1 (by rfl) ⟨575906, by rfl⟩ : syracuseStep 767875 = 1151813) B1151813
theorem B767891 : Blo 766334 767891 := bstep (se 1 (by rfl) ⟨575918, by rfl⟩ : syracuseStep 767891 = 1151837) B1151837
theorem B767907 : Blo 766334 767907 := bstep (se 1 (by rfl) ⟨575930, by rfl⟩ : syracuseStep 767907 = 1151861) B1151861
theorem B1456049 : Blo 766334 1456049 := bstep (se 2 (by rfl) ⟨546018, by rfl⟩ : syracuseStep 1456049 = 1092037) B1092037
theorem B767923 : Blo 766334 767923 := bstep (se 1 (by rfl) ⟨575942, by rfl⟩ : syracuseStep 767923 = 1151885) B1151885
theorem B866227 : Blo 766334 866227 := bstep (se 1 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 866227 = 1299341) B1299341
theorem B767939 : Blo 766334 767939 := bstep (se 1 (by rfl) ⟨575954, by rfl⟩ : syracuseStep 767939 = 1151909) B1151909
theorem B1095619 : Blo 766334 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B767955 : Blo 766334 767955 := bstep (se 1 (by rfl) ⟨575966, by rfl⟩ : syracuseStep 767955 = 1151933) B1151933
theorem B4372451 : Blo 766334 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B767971 : Blo 766334 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B767987 : Blo 766334 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B768003 : Blo 766334 768003 := bstep (se 1 (by rfl) ⟨576002, by rfl⟩ : syracuseStep 768003 = 1152005) B1152005
theorem B1947665 : Blo 766334 1947665 := bstep (se 2 (by rfl) ⟨730374, by rfl⟩ : syracuseStep 1947665 = 1460749) B1460749
theorem B768019 : Blo 766334 768019 := bstep (se 1 (by rfl) ⟨576014, by rfl⟩ : syracuseStep 768019 = 1152029) B1152029
theorem B768035 : Blo 766334 768035 := bstep (se 1 (by rfl) ⟨576026, by rfl⟩ : syracuseStep 768035 = 1152053) B1152053
theorem B768051 : Blo 766334 768051 := bstep (se 1 (by rfl) ⟨576038, by rfl⟩ : syracuseStep 768051 = 1152077) B1152077
theorem B768067 : Blo 766334 768067 := bstep (se 1 (by rfl) ⟨576050, by rfl⟩ : syracuseStep 768067 = 1152101) B1152101
theorem B866371 : Blo 766334 866371 := bstep (se 1 (by rfl) ⟨649778, by rfl⟩ : syracuseStep 866371 = 1299557) B1299557
theorem B2078797 : Blo 766334 2078797 := bstep (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) B779549
theorem B768083 : Blo 766334 768083 := bstep (se 1 (by rfl) ⟨576062, by rfl⟩ : syracuseStep 768083 = 1152125) B1152125
theorem B768099 : Blo 766334 768099 := bstep (se 1 (by rfl) ⟨576074, by rfl⟩ : syracuseStep 768099 = 1152149) B1152149
theorem B768115 : Blo 766334 768115 := bstep (se 1 (by rfl) ⟨576086, by rfl⟩ : syracuseStep 768115 = 1152173) B1152173
theorem B768131 : Blo 766334 768131 := bstep (se 1 (by rfl) ⟨576098, by rfl⟩ : syracuseStep 768131 = 1152197) B1152197
theorem B768147 : Blo 766334 768147 := bstep (se 1 (by rfl) ⟨576110, by rfl⟩ : syracuseStep 768147 = 1152221) B1152221
theorem B768163 : Blo 766334 768163 := bstep (se 1 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 768163 = 1152245) B1152245
theorem B768179 : Blo 766334 768179 := bstep (se 1 (by rfl) ⟨576134, by rfl⟩ : syracuseStep 768179 = 1152269) B1152269
theorem B768195 : Blo 766334 768195 := bstep (se 1 (by rfl) ⟨576146, by rfl⟩ : syracuseStep 768195 = 1152293) B1152293
theorem B768211 : Blo 766334 768211 := bstep (se 1 (by rfl) ⟨576158, by rfl⟩ : syracuseStep 768211 = 1152317) B1152317
theorem B866515 : Blo 766334 866515 := bstep (se 1 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 866515 = 1299773) B1299773
theorem B768227 : Blo 766334 768227 := bstep (se 1 (by rfl) ⟨576170, by rfl⟩ : syracuseStep 768227 = 1152341) B1152341
theorem B768243 : Blo 766334 768243 := bstep (se 1 (by rfl) ⟨576182, by rfl⟩ : syracuseStep 768243 = 1152365) B1152365
theorem B768259 : Blo 766334 768259 := bstep (se 1 (by rfl) ⟨576194, by rfl⟩ : syracuseStep 768259 = 1152389) B1152389
theorem B768275 : Blo 766334 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B768291 : Blo 766334 768291 := bstep (se 1 (by rfl) ⟨576218, by rfl⟩ : syracuseStep 768291 = 1152437) B1152437
theorem B768307 : Blo 766334 768307 := bstep (se 1 (by rfl) ⟨576230, by rfl⟩ : syracuseStep 768307 = 1152461) B1152461
theorem B1456451 : Blo 766334 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B768323 : Blo 766334 768323 := bstep (se 1 (by rfl) ⟨576242, by rfl⟩ : syracuseStep 768323 = 1152485) B1152485
theorem B768339 : Blo 766334 768339 := bstep (se 1 (by rfl) ⟨576254, by rfl⟩ : syracuseStep 768339 = 1152509) B1152509
theorem B768355 : Blo 766334 768355 := bstep (se 1 (by rfl) ⟨576266, by rfl⟩ : syracuseStep 768355 = 1152533) B1152533
theorem B768371 : Blo 766334 768371 := bstep (se 1 (by rfl) ⟨576278, by rfl⟩ : syracuseStep 768371 = 1152557) B1152557
theorem B768387 : Blo 766334 768387 := bstep (se 1 (by rfl) ⟨576290, by rfl⟩ : syracuseStep 768387 = 1152581) B1152581
theorem B3881357 : Blo 766334 3881357 := bstep (se 3 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 3881357 = 1455509) B1455509
theorem B768403 : Blo 766334 768403 := bstep (se 1 (by rfl) ⟨576302, by rfl⟩ : syracuseStep 768403 = 1152605) B1152605
theorem B1096097 : Blo 766334 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B768419 : Blo 766334 768419 := bstep (se 1 (by rfl) ⟨576314, by rfl⟩ : syracuseStep 768419 = 1152629) B1152629
theorem B768435 : Blo 766334 768435 := bstep (se 1 (by rfl) ⟨576326, by rfl⟩ : syracuseStep 768435 = 1152653) B1152653
theorem B768451 : Blo 766334 768451 := bstep (se 1 (by rfl) ⟨576338, by rfl⟩ : syracuseStep 768451 = 1152677) B1152677
theorem B768467 : Blo 766334 768467 := bstep (se 1 (by rfl) ⟨576350, by rfl⟩ : syracuseStep 768467 = 1152701) B1152701
theorem B768483 : Blo 766334 768483 := bstep (se 1 (by rfl) ⟨576362, by rfl⟩ : syracuseStep 768483 = 1152725) B1152725
theorem B768499 : Blo 766334 768499 := bstep (se 1 (by rfl) ⟨576374, by rfl⟩ : syracuseStep 768499 = 1152749) B1152749
theorem B768515 : Blo 766334 768515 := bstep (se 1 (by rfl) ⟨576386, by rfl⟩ : syracuseStep 768515 = 1152773) B1152773
theorem B768531 : Blo 766334 768531 := bstep (se 1 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 768531 = 1152797) B1152797
theorem B1096211 : Blo 766334 1096211 := bstep (se 1 (by rfl) ⟨822158, by rfl⟩ : syracuseStep 1096211 = 1644317) B1644317
theorem B768547 : Blo 766334 768547 := bstep (se 1 (by rfl) ⟨576410, by rfl⟩ : syracuseStep 768547 = 1152821) B1152821
theorem B768563 : Blo 766334 768563 := bstep (se 1 (by rfl) ⟨576422, by rfl⟩ : syracuseStep 768563 = 1152845) B1152845
theorem B768579 : Blo 766334 768579 := bstep (se 1 (by rfl) ⟨576434, by rfl⟩ : syracuseStep 768579 = 1152869) B1152869
theorem B768595 : Blo 766334 768595 := bstep (se 1 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 768595 = 1152893) B1152893
theorem B768611 : Blo 766334 768611 := bstep (se 1 (by rfl) ⟨576458, by rfl⟩ : syracuseStep 768611 = 1152917) B1152917
theorem B1096291 : Blo 766334 1096291 := bstep (se 1 (by rfl) ⟨822218, by rfl⟩ : syracuseStep 1096291 = 1644437) B1644437
theorem B768627 : Blo 766334 768627 := bstep (se 1 (by rfl) ⟨576470, by rfl⟩ : syracuseStep 768627 = 1152941) B1152941
theorem B768643 : Blo 766334 768643 := bstep (se 1 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 768643 = 1152965) B1152965
theorem B768659 : Blo 766334 768659 := bstep (se 1 (by rfl) ⟨576494, by rfl⟩ : syracuseStep 768659 = 1152989) B1152989
theorem B3685027 : Blo 766334 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B768675 : Blo 766334 768675 := bstep (se 1 (by rfl) ⟨576506, by rfl⟩ : syracuseStep 768675 = 1153013) B1153013
theorem B768691 : Blo 766334 768691 := bstep (se 1 (by rfl) ⟨576518, by rfl⟩ : syracuseStep 768691 = 1153037) B1153037
theorem B768707 : Blo 766334 768707 := bstep (se 1 (by rfl) ⟨576530, by rfl⟩ : syracuseStep 768707 = 1153061) B1153061
theorem B768723 : Blo 766334 768723 := bstep (se 1 (by rfl) ⟨576542, by rfl⟩ : syracuseStep 768723 = 1153085) B1153085
theorem B768739 : Blo 766334 768739 := bstep (se 1 (by rfl) ⟨576554, by rfl⟩ : syracuseStep 768739 = 1153109) B1153109
theorem B768755 : Blo 766334 768755 := bstep (se 1 (by rfl) ⟨576566, by rfl⟩ : syracuseStep 768755 = 1153133) B1153133
theorem B768771 : Blo 766334 768771 := bstep (se 1 (by rfl) ⟨576578, by rfl⟩ : syracuseStep 768771 = 1153157) B1153157
theorem B768787 : Blo 766334 768787 := bstep (se 1 (by rfl) ⟨576590, by rfl⟩ : syracuseStep 768787 = 1153181) B1153181
theorem B768803 : Blo 766334 768803 := bstep (se 1 (by rfl) ⟨576602, by rfl⟩ : syracuseStep 768803 = 1153205) B1153205
theorem B2079533 : Blo 766334 2079533 := bstep (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) B779825
theorem B1424177 : Blo 766334 1424177 := bstep (se 2 (by rfl) ⟨534066, by rfl⟩ : syracuseStep 1424177 = 1068133) B1068133
theorem B768819 : Blo 766334 768819 := bstep (se 1 (by rfl) ⟨576614, by rfl⟩ : syracuseStep 768819 = 1153229) B1153229
theorem B768835 : Blo 766334 768835 := bstep (se 1 (by rfl) ⟨576626, by rfl⟩ : syracuseStep 768835 = 1153253) B1153253
theorem B768851 : Blo 766334 768851 := bstep (se 1 (by rfl) ⟨576638, by rfl⟩ : syracuseStep 768851 = 1153277) B1153277
theorem B768867 : Blo 766334 768867 := bstep (se 1 (by rfl) ⟨576650, by rfl⟩ : syracuseStep 768867 = 1153301) B1153301
theorem B768883 : Blo 766334 768883 := bstep (se 1 (by rfl) ⟨576662, by rfl⟩ : syracuseStep 768883 = 1153325) B1153325
theorem B768899 : Blo 766334 768899 := bstep (se 1 (by rfl) ⟨576674, by rfl⟩ : syracuseStep 768899 = 1153349) B1153349
theorem B768915 : Blo 766334 768915 := bstep (se 1 (by rfl) ⟨576686, by rfl⟩ : syracuseStep 768915 = 1153373) B1153373
theorem B768931 : Blo 766334 768931 := bstep (se 1 (by rfl) ⟨576698, by rfl⟩ : syracuseStep 768931 = 1153397) B1153397
theorem B768947 : Blo 766334 768947 := bstep (se 1 (by rfl) ⟨576710, by rfl⟩ : syracuseStep 768947 = 1153421) B1153421
theorem B768963 : Blo 766334 768963 := bstep (se 1 (by rfl) ⟨576722, by rfl⟩ : syracuseStep 768963 = 1153445) B1153445
theorem B4373453 : Blo 766334 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B768979 : Blo 766334 768979 := bstep (se 1 (by rfl) ⟨576734, by rfl⟩ : syracuseStep 768979 = 1153469) B1153469
theorem B768995 : Blo 766334 768995 := bstep (se 1 (by rfl) ⟨576746, by rfl⟩ : syracuseStep 768995 = 1153493) B1153493
theorem B1948657 : Blo 766334 1948657 := bstep (se 2 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 1948657 = 1461493) B1461493
theorem B769011 : Blo 766334 769011 := bstep (se 1 (by rfl) ⟨576758, by rfl⟩ : syracuseStep 769011 = 1153517) B1153517
theorem B1293313 : Blo 766334 1293313 := bstep (se 2 (by rfl) ⟨484992, by rfl⟩ : syracuseStep 1293313 = 969985) B969985
theorem B1227779 : Blo 766334 1227779 := bstep (se 1 (by rfl) ⟨920834, by rfl⟩ : syracuseStep 1227779 = 1841669) B1841669
theorem B769027 : Blo 766334 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B769043 : Blo 766334 769043 := bstep (se 1 (by rfl) ⟨576782, by rfl⟩ : syracuseStep 769043 = 1153565) B1153565
theorem B1293347 : Blo 766334 1293347 := bstep (se 1 (by rfl) ⟨970010, by rfl⟩ : syracuseStep 1293347 = 1940021) B1940021
theorem B769059 : Blo 766334 769059 := bstep (se 1 (by rfl) ⟨576794, by rfl⟩ : syracuseStep 769059 = 1153589) B1153589
theorem B769075 : Blo 766334 769075 := bstep (se 1 (by rfl) ⟨576806, by rfl⟩ : syracuseStep 769075 = 1153613) B1153613
theorem B769091 : Blo 766334 769091 := bstep (se 1 (by rfl) ⟨576818, by rfl⟩ : syracuseStep 769091 = 1153637) B1153637
theorem B769107 : Blo 766334 769107 := bstep (se 1 (by rfl) ⟨576830, by rfl⟩ : syracuseStep 769107 = 1153661) B1153661
theorem B769123 : Blo 766334 769123 := bstep (se 1 (by rfl) ⟨576842, by rfl⟩ : syracuseStep 769123 = 1153685) B1153685
theorem B2964593 : Blo 766334 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B769139 : Blo 766334 769139 := bstep (se 1 (by rfl) ⟨576854, by rfl⟩ : syracuseStep 769139 = 1153709) B1153709
theorem B1227907 : Blo 766334 1227907 := bstep (se 1 (by rfl) ⟨920930, by rfl⟩ : syracuseStep 1227907 = 1841861) B1841861
theorem B769155 : Blo 766334 769155 := bstep (se 1 (by rfl) ⟨576866, by rfl⟩ : syracuseStep 769155 = 1153733) B1153733
theorem B769171 : Blo 766334 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B1293475 : Blo 766334 1293475 := bstep (se 1 (by rfl) ⟨970106, by rfl⟩ : syracuseStep 1293475 = 1940213) B1940213
theorem B769187 : Blo 766334 769187 := bstep (se 1 (by rfl) ⟨576890, by rfl⟩ : syracuseStep 769187 = 1153781) B1153781
theorem B769203 : Blo 766334 769203 := bstep (se 1 (by rfl) ⟨576902, by rfl⟩ : syracuseStep 769203 = 1153805) B1153805
theorem B1457347 : Blo 766334 1457347 := bstep (se 1 (by rfl) ⟨1093010, by rfl⟩ : syracuseStep 1457347 = 2186021) B2186021
theorem B769219 : Blo 766334 769219 := bstep (se 1 (by rfl) ⟨576914, by rfl⟩ : syracuseStep 769219 = 1153829) B1153829
theorem B769235 : Blo 766334 769235 := bstep (se 1 (by rfl) ⟨576926, by rfl⟩ : syracuseStep 769235 = 1153853) B1153853
theorem B769251 : Blo 766334 769251 := bstep (se 1 (by rfl) ⟨576938, by rfl⟩ : syracuseStep 769251 = 1153877) B1153877
theorem B6569201 : Blo 766334 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B769267 : Blo 766334 769267 := bstep (se 1 (by rfl) ⟨576950, by rfl⟩ : syracuseStep 769267 = 1153901) B1153901
theorem B769283 : Blo 766334 769283 := bstep (se 1 (by rfl) ⟨576962, by rfl⟩ : syracuseStep 769283 = 1153925) B1153925
theorem B1948931 : Blo 766334 1948931 := bstep (se 1 (by rfl) ⟨1461698, by rfl⟩ : syracuseStep 1948931 = 2923397) B2923397
theorem B769299 : Blo 766334 769299 := bstep (se 1 (by rfl) ⟨576974, by rfl⟩ : syracuseStep 769299 = 1153949) B1153949
theorem B769315 : Blo 766334 769315 := bstep (se 1 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 769315 = 1153973) B1153973
theorem B1293617 : Blo 766334 1293617 := bstep (se 2 (by rfl) ⟨485106, by rfl⟩ : syracuseStep 1293617 = 970213) B970213
theorem B769331 : Blo 766334 769331 := bstep (se 1 (by rfl) ⟨576998, by rfl⟩ : syracuseStep 769331 = 1153997) B1153997
theorem B769347 : Blo 766334 769347 := bstep (se 1 (by rfl) ⟨577010, by rfl⟩ : syracuseStep 769347 = 1154021) B1154021
theorem B769363 : Blo 766334 769363 := bstep (se 1 (by rfl) ⟨577022, by rfl⟩ : syracuseStep 769363 = 1154045) B1154045
theorem B1457507 : Blo 766334 1457507 := bstep (se 1 (by rfl) ⟨1093130, by rfl⟩ : syracuseStep 1457507 = 2186261) B2186261
theorem B769379 : Blo 766334 769379 := bstep (se 1 (by rfl) ⟨577034, by rfl⟩ : syracuseStep 769379 = 1154069) B1154069
theorem B769395 : Blo 766334 769395 := bstep (se 1 (by rfl) ⟨577046, by rfl⟩ : syracuseStep 769395 = 1154093) B1154093
theorem B769411 : Blo 766334 769411 := bstep (se 1 (by rfl) ⟨577058, by rfl⟩ : syracuseStep 769411 = 1154117) B1154117
theorem B769427 : Blo 766334 769427 := bstep (se 1 (by rfl) ⟨577070, by rfl⟩ : syracuseStep 769427 = 1154141) B1154141
theorem B769443 : Blo 766334 769443 := bstep (se 1 (by rfl) ⟨577082, by rfl⟩ : syracuseStep 769443 = 1154165) B1154165
theorem B1293745 : Blo 766334 1293745 := bstep (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) B970309
theorem B769459 : Blo 766334 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B769475 : Blo 766334 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B1949123 : Blo 766334 1949123 := bstep (se 1 (by rfl) ⟨1461842, by rfl⟩ : syracuseStep 1949123 = 2923685) B2923685
theorem B933331 : Blo 766334 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1293779 : Blo 766334 1293779 := bstep (se 1 (by rfl) ⟨970334, by rfl⟩ : syracuseStep 1293779 = 1940669) B1940669
theorem B769491 : Blo 766334 769491 := bstep (se 1 (by rfl) ⟨577118, by rfl⟩ : syracuseStep 769491 = 1154237) B1154237
theorem B769507 : Blo 766334 769507 := bstep (se 1 (by rfl) ⟨577130, by rfl⟩ : syracuseStep 769507 = 1154261) B1154261
theorem B769523 : Blo 766334 769523 := bstep (se 1 (by rfl) ⟨577142, by rfl⟩ : syracuseStep 769523 = 1154285) B1154285
theorem B769539 : Blo 766334 769539 := bstep (se 1 (by rfl) ⟨577154, by rfl⟩ : syracuseStep 769539 = 1154309) B1154309
theorem B1555985 : Blo 766334 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B769555 : Blo 766334 769555 := bstep (se 1 (by rfl) ⟨577166, by rfl⟩ : syracuseStep 769555 = 1154333) B1154333
theorem B769571 : Blo 766334 769571 := bstep (se 1 (by rfl) ⟨577178, by rfl⟩ : syracuseStep 769571 = 1154357) B1154357
theorem B769587 : Blo 766334 769587 := bstep (se 1 (by rfl) ⟨577190, by rfl⟩ : syracuseStep 769587 = 1154381) B1154381
theorem B769603 : Blo 766334 769603 := bstep (se 1 (by rfl) ⟨577202, by rfl⟩ : syracuseStep 769603 = 1154405) B1154405
theorem B1293907 : Blo 766334 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B769619 : Blo 766334 769619 := bstep (se 1 (by rfl) ⟨577214, by rfl⟩ : syracuseStep 769619 = 1154429) B1154429
theorem B769635 : Blo 766334 769635 := bstep (se 1 (by rfl) ⟨577226, by rfl⟩ : syracuseStep 769635 = 1154453) B1154453
theorem B769651 : Blo 766334 769651 := bstep (se 1 (by rfl) ⟨577238, by rfl⟩ : syracuseStep 769651 = 1154477) B1154477
theorem B769667 : Blo 766334 769667 := bstep (se 1 (by rfl) ⟨577250, by rfl⟩ : syracuseStep 769667 = 1154501) B1154501
theorem B769683 : Blo 766334 769683 := bstep (se 1 (by rfl) ⟨577262, by rfl⟩ : syracuseStep 769683 = 1154525) B1154525
theorem B1556131 : Blo 766334 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B769699 : Blo 766334 769699 := bstep (se 1 (by rfl) ⟨577274, by rfl⟩ : syracuseStep 769699 = 1154549) B1154549
theorem B769715 : Blo 766334 769715 := bstep (se 1 (by rfl) ⟨577286, by rfl⟩ : syracuseStep 769715 = 1154573) B1154573
theorem B769731 : Blo 766334 769731 := bstep (se 1 (by rfl) ⟨577298, by rfl⟩ : syracuseStep 769731 = 1154597) B1154597
theorem B769747 : Blo 766334 769747 := bstep (se 1 (by rfl) ⟨577310, by rfl⟩ : syracuseStep 769747 = 1154621) B1154621
theorem B1294049 : Blo 766334 1294049 := bstep (se 2 (by rfl) ⟨485268, by rfl⟩ : syracuseStep 1294049 = 970537) B970537
theorem B769763 : Blo 766334 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B769779 : Blo 766334 769779 := bstep (se 1 (by rfl) ⟨577334, by rfl⟩ : syracuseStep 769779 = 1154669) B1154669
theorem B769795 : Blo 766334 769795 := bstep (se 1 (by rfl) ⟨577346, by rfl⟩ : syracuseStep 769795 = 1154693) B1154693
theorem B769811 : Blo 766334 769811 := bstep (se 1 (by rfl) ⟨577358, by rfl⟩ : syracuseStep 769811 = 1154717) B1154717
theorem B769827 : Blo 766334 769827 := bstep (se 1 (by rfl) ⟨577370, by rfl⟩ : syracuseStep 769827 = 1154741) B1154741
theorem B769843 : Blo 766334 769843 := bstep (se 1 (by rfl) ⟨577382, by rfl⟩ : syracuseStep 769843 = 1154765) B1154765
theorem B769859 : Blo 766334 769859 := bstep (se 1 (by rfl) ⟨577394, by rfl⟩ : syracuseStep 769859 = 1154789) B1154789
theorem B1228625 : Blo 766334 1228625 := bstep (se 2 (by rfl) ⟨460734, by rfl⟩ : syracuseStep 1228625 = 921469) B921469
theorem B769875 : Blo 766334 769875 := bstep (se 1 (by rfl) ⟨577406, by rfl⟩ : syracuseStep 769875 = 1154813) B1154813
theorem B1294177 : Blo 766334 1294177 := bstep (se 2 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 1294177 = 970633) B970633
theorem B769891 : Blo 766334 769891 := bstep (se 1 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 769891 = 1154837) B1154837
theorem B3686257 : Blo 766334 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B769907 : Blo 766334 769907 := bstep (se 1 (by rfl) ⟨577430, by rfl⟩ : syracuseStep 769907 = 1154861) B1154861
theorem B1294211 : Blo 766334 1294211 := bstep (se 1 (by rfl) ⟨970658, by rfl⟩ : syracuseStep 1294211 = 1941317) B1941317
theorem B769923 : Blo 766334 769923 := bstep (se 1 (by rfl) ⟨577442, by rfl⟩ : syracuseStep 769923 = 1154885) B1154885
theorem B2080657 : Blo 766334 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B769939 : Blo 766334 769939 := bstep (se 1 (by rfl) ⟨577454, by rfl⟩ : syracuseStep 769939 = 1154909) B1154909
theorem B769955 : Blo 766334 769955 := bstep (se 1 (by rfl) ⟨577466, by rfl⟩ : syracuseStep 769955 = 1154933) B1154933
theorem B769971 : Blo 766334 769971 := bstep (se 1 (by rfl) ⟨577478, by rfl⟩ : syracuseStep 769971 = 1154957) B1154957
theorem B769987 : Blo 766334 769987 := bstep (se 1 (by rfl) ⟨577490, by rfl⟩ : syracuseStep 769987 = 1154981) B1154981
theorem B2768845 : Blo 766334 2768845 := bstep (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) B1038317
theorem B770003 : Blo 766334 770003 := bstep (se 1 (by rfl) ⟨577502, by rfl⟩ : syracuseStep 770003 = 1155005) B1155005
theorem B770019 : Blo 766334 770019 := bstep (se 1 (by rfl) ⟨577514, by rfl⟩ : syracuseStep 770019 = 1155029) B1155029
theorem B770035 : Blo 766334 770035 := bstep (se 1 (by rfl) ⟨577526, by rfl⟩ : syracuseStep 770035 = 1155053) B1155053
theorem B1294339 : Blo 766334 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B770051 : Blo 766334 770051 := bstep (se 1 (by rfl) ⟨577538, by rfl⟩ : syracuseStep 770051 = 1155077) B1155077
theorem B1228817 : Blo 766334 1228817 := bstep (se 2 (by rfl) ⟨460806, by rfl⟩ : syracuseStep 1228817 = 921613) B921613
theorem B770067 : Blo 766334 770067 := bstep (se 1 (by rfl) ⟨577550, by rfl⟩ : syracuseStep 770067 = 1155101) B1155101
theorem B770083 : Blo 766334 770083 := bstep (se 1 (by rfl) ⟨577562, by rfl⟩ : syracuseStep 770083 = 1155125) B1155125
theorem B901171 : Blo 766334 901171 := bstep (se 1 (by rfl) ⟨675878, by rfl⟩ : syracuseStep 901171 = 1351757) B1351757
theorem B770099 : Blo 766334 770099 := bstep (se 1 (by rfl) ⟨577574, by rfl⟩ : syracuseStep 770099 = 1155149) B1155149
theorem B770115 : Blo 766334 770115 := bstep (se 1 (by rfl) ⟨577586, by rfl⟩ : syracuseStep 770115 = 1155173) B1155173
theorem B770131 : Blo 766334 770131 := bstep (se 1 (by rfl) ⟨577598, by rfl⟩ : syracuseStep 770131 = 1155197) B1155197
theorem B10633315 : Blo 766334 10633315 := bstep (se 1 (by rfl) ⟨7974986, by rfl⟩ : syracuseStep 10633315 = 15949973) B15949973
theorem B770147 : Blo 766334 770147 := bstep (se 1 (by rfl) ⟨577610, by rfl⟩ : syracuseStep 770147 = 1155221) B1155221
theorem B770163 : Blo 766334 770163 := bstep (se 1 (by rfl) ⟨577622, by rfl⟩ : syracuseStep 770163 = 1155245) B1155245
theorem B770179 : Blo 766334 770179 := bstep (se 1 (by rfl) ⟨577634, by rfl⟩ : syracuseStep 770179 = 1155269) B1155269
theorem B1294481 : Blo 766334 1294481 := bstep (se 2 (by rfl) ⟨485430, by rfl⟩ : syracuseStep 1294481 = 970861) B970861
theorem B770195 : Blo 766334 770195 := bstep (se 1 (by rfl) ⟨577646, by rfl⟩ : syracuseStep 770195 = 1155293) B1155293
theorem B770211 : Blo 766334 770211 := bstep (se 1 (by rfl) ⟨577658, by rfl⟩ : syracuseStep 770211 = 1155317) B1155317
theorem B770227 : Blo 766334 770227 := bstep (se 1 (by rfl) ⟨577670, by rfl⟩ : syracuseStep 770227 = 1155341) B1155341
theorem B770243 : Blo 766334 770243 := bstep (se 1 (by rfl) ⟨577682, by rfl⟩ : syracuseStep 770243 = 1155365) B1155365
theorem B4145357 : Blo 766334 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B770259 : Blo 766334 770259 := bstep (se 1 (by rfl) ⟨577694, by rfl⟩ : syracuseStep 770259 = 1155389) B1155389
theorem B770275 : Blo 766334 770275 := bstep (se 1 (by rfl) ⟨577706, by rfl⟩ : syracuseStep 770275 = 1155413) B1155413
theorem B770291 : Blo 766334 770291 := bstep (se 1 (by rfl) ⟨577718, by rfl⟩ : syracuseStep 770291 = 1155437) B1155437
theorem B770307 : Blo 766334 770307 := bstep (se 1 (by rfl) ⟨577730, by rfl⟩ : syracuseStep 770307 = 1155461) B1155461
theorem B1294609 : Blo 766334 1294609 := bstep (se 2 (by rfl) ⟨485478, by rfl⟩ : syracuseStep 1294609 = 970957) B970957
theorem B770323 : Blo 766334 770323 := bstep (se 1 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 770323 = 1155485) B1155485
theorem B1294643 : Blo 766334 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B1458577 : Blo 766334 1458577 := bstep (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) B1093933
theorem B1294771 : Blo 766334 1294771 := bstep (se 1 (by rfl) ⟨971078, by rfl⟩ : syracuseStep 1294771 = 1942157) B1942157
theorem B1294913 : Blo 766334 1294913 := bstep (se 2 (by rfl) ⟨485592, by rfl⟩ : syracuseStep 1294913 = 971185) B971185
theorem B1295041 : Blo 766334 1295041 := bstep (se 2 (by rfl) ⟨485640, by rfl⟩ : syracuseStep 1295041 = 971281) B971281
theorem B1295075 : Blo 766334 1295075 := bstep (se 1 (by rfl) ⟨971306, by rfl⟩ : syracuseStep 1295075 = 1942613) B1942613
theorem B1295203 : Blo 766334 1295203 := bstep (se 1 (by rfl) ⟨971402, by rfl⟩ : syracuseStep 1295203 = 1942805) B1942805
theorem B3687373 : Blo 766334 3687373 := bstep (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) B1382765
theorem B1295345 : Blo 766334 1295345 := bstep (se 2 (by rfl) ⟨485754, by rfl⟩ : syracuseStep 1295345 = 971509) B971509
theorem B1295473 : Blo 766334 1295473 := bstep (se 2 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 1295473 = 971605) B971605
theorem B1295507 : Blo 766334 1295507 := bstep (se 1 (by rfl) ⟨971630, by rfl⟩ : syracuseStep 1295507 = 1943261) B1943261
theorem B3884273 : Blo 766334 3884273 := bstep (se 2 (by rfl) ⟨1456602, by rfl⟩ : syracuseStep 3884273 = 2913205) B2913205
theorem B1295635 : Blo 766334 1295635 := bstep (se 1 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 1295635 = 1943453) B1943453
theorem B2082161 : Blo 766334 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B1295777 : Blo 766334 1295777 := bstep (se 2 (by rfl) ⟨485916, by rfl⟩ : syracuseStep 1295777 = 971833) B971833
theorem B1459633 : Blo 766334 1459633 := bstep (se 2 (by rfl) ⟨547362, by rfl⟩ : syracuseStep 1459633 = 1094725) B1094725
theorem B23643589 : Blo 766334 23643589 := bstep (se 4 (by rfl) ⟨2216586, by rfl⟩ : syracuseStep 23643589 = 4433173) B4433173
theorem B1295905 : Blo 766334 1295905 := bstep (se 2 (by rfl) ⟨485964, by rfl⟩ : syracuseStep 1295905 = 971929) B971929
theorem B1295939 : Blo 766334 1295939 := bstep (se 1 (by rfl) ⟨971954, by rfl⟩ : syracuseStep 1295939 = 1943909) B1943909
theorem B1296067 : Blo 766334 1296067 := bstep (se 1 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 1296067 = 1944101) B1944101
theorem B1230547 : Blo 766334 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B4376369 : Blo 766334 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B1230643 : Blo 766334 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B1460035 : Blo 766334 1460035 := bstep (se 1 (by rfl) ⟨1095026, by rfl⟩ : syracuseStep 1460035 = 2190053) B2190053
theorem B1296209 : Blo 766334 1296209 := bstep (se 2 (by rfl) ⟨486078, by rfl⟩ : syracuseStep 1296209 = 972157) B972157
theorem B1460081 : Blo 766334 1460081 := bstep (se 2 (by rfl) ⟨547530, by rfl⟩ : syracuseStep 1460081 = 1095061) B1095061
theorem B1296337 : Blo 766334 1296337 := bstep (se 2 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 1296337 = 972253) B972253
theorem B1230803 : Blo 766334 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1296371 : Blo 766334 1296371 := bstep (se 1 (by rfl) ⟨972278, by rfl⟩ : syracuseStep 1296371 = 1944557) B1944557
theorem B4147213 : Blo 766334 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B1296499 : Blo 766334 1296499 := bstep (se 1 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 1296499 = 1944749) B1944749
theorem B1460369 : Blo 766334 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B1165523 : Blo 766334 1165523 := bstep (se 1 (by rfl) ⟨874142, by rfl⟩ : syracuseStep 1165523 = 1748285) B1748285
theorem B1296641 : Blo 766334 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B1296769 : Blo 766334 1296769 := bstep (se 2 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 1296769 = 972577) B972577
theorem B1296803 : Blo 766334 1296803 := bstep (se 1 (by rfl) ⟨972602, by rfl⟩ : syracuseStep 1296803 = 1945205) B1945205
theorem B1296931 : Blo 766334 1296931 := bstep (se 1 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 1296931 = 1945397) B1945397
theorem B3885731 : Blo 766334 3885731 := bstep (se 1 (by rfl) ⟨2914298, by rfl⟩ : syracuseStep 3885731 = 5828597) B5828597
theorem B1297073 : Blo 766334 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B1166113 : Blo 766334 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B1297201 : Blo 766334 1297201 := bstep (se 2 (by rfl) ⟨486450, by rfl⟩ : syracuseStep 1297201 = 972901) B972901
theorem B1297235 : Blo 766334 1297235 := bstep (se 1 (by rfl) ⟨972926, by rfl⟩ : syracuseStep 1297235 = 1945853) B1945853
theorem B1461091 : Blo 766334 1461091 := bstep (se 1 (by rfl) ⟨1095818, by rfl⟩ : syracuseStep 1461091 = 2191637) B2191637
theorem B13519757 : Blo 766334 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B1231777 : Blo 766334 1231777 := bstep (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) B923833
theorem B7392197 : Blo 766334 7392197 := bstep (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) B1386037
theorem B1297363 : Blo 766334 1297363 := bstep (se 1 (by rfl) ⟨973022, by rfl⟩ : syracuseStep 1297363 = 1946045) B1946045
theorem B5819363 : Blo 766334 5819363 := bstep (se 1 (by rfl) ⟨4364522, by rfl⟩ : syracuseStep 5819363 = 8729045) B8729045
theorem B1297505 : Blo 766334 1297505 := bstep (se 2 (by rfl) ⟨486564, by rfl⟩ : syracuseStep 1297505 = 973129) B973129
theorem B1297633 : Blo 766334 1297633 := bstep (se 2 (by rfl) ⟨486612, by rfl⟩ : syracuseStep 1297633 = 973225) B973225
theorem B4377827 : Blo 766334 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B9358577 : Blo 766334 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B1166593 : Blo 766334 1166593 := bstep (se 2 (by rfl) ⟨437472, by rfl⟩ : syracuseStep 1166593 = 874945) B874945
theorem B1297667 : Blo 766334 1297667 := bstep (se 1 (by rfl) ⟨973250, by rfl⟩ : syracuseStep 1297667 = 1946501) B1946501
theorem B1461539 : Blo 766334 1461539 := bstep (se 1 (by rfl) ⟨1096154, by rfl⟩ : syracuseStep 1461539 = 2192309) B2192309
theorem B970051 : Blo 766334 970051 := bstep (se 1 (by rfl) ⟨727538, by rfl⟩ : syracuseStep 970051 = 1455077) B1455077
theorem B1297795 : Blo 766334 1297795 := bstep (se 1 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 1297795 = 1946693) B1946693
theorem B970147 : Blo 766334 970147 := bstep (se 1 (by rfl) ⟨727610, by rfl⟩ : syracuseStep 970147 = 1455221) B1455221
theorem B2215363 : Blo 766334 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B3886541 : Blo 766334 3886541 := bstep (se 3 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 3886541 = 1457453) B1457453
theorem B1297937 : Blo 766334 1297937 := bstep (se 2 (by rfl) ⟨486726, by rfl⟩ : syracuseStep 1297937 = 973453) B973453
theorem B1461827 : Blo 766334 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B11062925 : Blo 766334 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B1298065 : Blo 766334 1298065 := bstep (se 2 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 1298065 = 973549) B973549
theorem B1298099 : Blo 766334 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B7884557 : Blo 766334 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B1298227 : Blo 766334 1298227 := bstep (se 1 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 1298227 = 1947341) B1947341
theorem B1724273 : Blo 766334 1724273 := bstep (se 2 (by rfl) ⟨646602, by rfl⟩ : syracuseStep 1724273 = 1293205) B1293205
theorem B1724291 : Blo 766334 1724291 := bstep (se 1 (by rfl) ⟨1293218, by rfl⟩ : syracuseStep 1724291 = 2586437) B2586437
theorem B970643 : Blo 766334 970643 := bstep (se 1 (by rfl) ⟨727982, by rfl⟩ : syracuseStep 970643 = 1455965) B1455965
theorem B1298369 : Blo 766334 1298369 := bstep (se 2 (by rfl) ⟨486888, by rfl⟩ : syracuseStep 1298369 = 973777) B973777
theorem B1298497 : Blo 766334 1298497 := bstep (se 2 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 1298497 = 973873) B973873
theorem B1298531 : Blo 766334 1298531 := bstep (se 1 (by rfl) ⟨973898, by rfl⟩ : syracuseStep 1298531 = 1947797) B1947797
theorem B1724561 : Blo 766334 1724561 := bstep (se 2 (by rfl) ⟨646710, by rfl⟩ : syracuseStep 1724561 = 1293421) B1293421
theorem B1560721 : Blo 766334 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B1724579 : Blo 766334 1724579 := bstep (se 1 (by rfl) ⟨1293434, by rfl⟩ : syracuseStep 1724579 = 2586869) B2586869
theorem B2183345 : Blo 766334 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B1298659 : Blo 766334 1298659 := bstep (se 1 (by rfl) ⟨973994, by rfl⟩ : syracuseStep 1298659 = 1947989) B1947989
theorem B1069331 : Blo 766334 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B2183537 : Blo 766334 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B1298801 : Blo 766334 1298801 := bstep (se 2 (by rfl) ⟨487050, by rfl⟩ : syracuseStep 1298801 = 974101) B974101
theorem B1724849 : Blo 766334 1724849 := bstep (se 2 (by rfl) ⟨646818, by rfl⟩ : syracuseStep 1724849 = 1293637) B1293637
theorem B1724867 : Blo 766334 1724867 := bstep (se 1 (by rfl) ⟨1293650, by rfl⟩ : syracuseStep 1724867 = 2587301) B2587301
theorem B1036739 : Blo 766334 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B1298929 : Blo 766334 1298929 := bstep (se 2 (by rfl) ⟨487098, by rfl⟩ : syracuseStep 1298929 = 974197) B974197
theorem B1298963 : Blo 766334 1298963 := bstep (se 1 (by rfl) ⟨974222, by rfl⟩ : syracuseStep 1298963 = 1948445) B1948445
theorem B1233443 : Blo 766334 1233443 := bstep (se 1 (by rfl) ⟨925082, by rfl⟩ : syracuseStep 1233443 = 1850165) B1850165
theorem B971347 : Blo 766334 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B5526157 : Blo 766334 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B1299091 : Blo 766334 1299091 := bstep (se 1 (by rfl) ⟨974318, by rfl⟩ : syracuseStep 1299091 = 1948637) B1948637
theorem B1233571 : Blo 766334 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B971443 : Blo 766334 971443 := bstep (se 1 (by rfl) ⟨728582, by rfl⟩ : syracuseStep 971443 = 1457165) B1457165
theorem B1725137 : Blo 766334 1725137 := bstep (se 2 (by rfl) ⟨646926, by rfl⟩ : syracuseStep 1725137 = 1293853) B1293853
theorem B1725155 : Blo 766334 1725155 := bstep (se 1 (by rfl) ⟨1293866, by rfl⟩ : syracuseStep 1725155 = 2587733) B2587733
theorem B1233635 : Blo 766334 1233635 := bstep (se 1 (by rfl) ⟨925226, by rfl⟩ : syracuseStep 1233635 = 1850453) B1850453
theorem B1299233 : Blo 766334 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B2216753 : Blo 766334 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B1299361 : Blo 766334 1299361 := bstep (se 2 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 1299361 = 974521) B974521
theorem B1299395 : Blo 766334 1299395 := bstep (se 1 (by rfl) ⟨974546, by rfl⟩ : syracuseStep 1299395 = 1949093) B1949093
theorem B1725425 : Blo 766334 1725425 := bstep (se 2 (by rfl) ⟨647034, by rfl⟩ : syracuseStep 1725425 = 1294069) B1294069
theorem B1725443 : Blo 766334 1725443 := bstep (se 1 (by rfl) ⟨1294082, by rfl⟩ : syracuseStep 1725443 = 2588165) B2588165
theorem B1299523 : Blo 766334 1299523 := bstep (se 1 (by rfl) ⟨974642, by rfl⟩ : syracuseStep 1299523 = 1949285) B1949285
theorem B971939 : Blo 766334 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B1299665 : Blo 766334 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B1037539 : Blo 766334 1037539 := bstep (se 1 (by rfl) ⟨778154, by rfl⟩ : syracuseStep 1037539 = 1556309) B1556309
theorem B4150499 : Blo 766334 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B22172899 : Blo 766334 22172899 := bstep (se 1 (by rfl) ⟨16629674, by rfl⟩ : syracuseStep 22172899 = 33259349) B33259349
theorem B1725713 : Blo 766334 1725713 := bstep (se 2 (by rfl) ⟨647142, by rfl⟩ : syracuseStep 1725713 = 1294285) B1294285
theorem B1725731 : Blo 766334 1725731 := bstep (se 1 (by rfl) ⟨1294298, by rfl⟩ : syracuseStep 1725731 = 2588597) B2588597
theorem B2184529 : Blo 766334 2184529 := bstep (se 2 (by rfl) ⟨819198, by rfl⟩ : syracuseStep 2184529 = 1638397) B1638397
theorem B1299793 : Blo 766334 1299793 := bstep (se 2 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 1299793 = 974845) B974845
theorem B1299827 : Blo 766334 1299827 := bstep (se 1 (by rfl) ⟨974870, by rfl⟩ : syracuseStep 1299827 = 1949741) B1949741
theorem B1037777 : Blo 766334 1037777 := bstep (se 2 (by rfl) ⟨389166, by rfl⟩ : syracuseStep 1037777 = 778333) B778333
theorem B1168849 : Blo 766334 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B1726001 : Blo 766334 1726001 := bstep (se 2 (by rfl) ⟨647250, by rfl⟩ : syracuseStep 1726001 = 1294501) B1294501
theorem B3331633 : Blo 766334 3331633 := bstep (se 2 (by rfl) ⟨1249362, by rfl⟩ : syracuseStep 3331633 = 2498725) B2498725
theorem B1726019 : Blo 766334 1726019 := bstep (se 1 (by rfl) ⟨1294514, by rfl⟩ : syracuseStep 1726019 = 2589029) B2589029
theorem B2184803 : Blo 766334 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B2184995 : Blo 766334 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B1726289 : Blo 766334 1726289 := bstep (se 2 (by rfl) ⟨647358, by rfl⟩ : syracuseStep 1726289 = 1294717) B1294717
theorem B1726307 : Blo 766334 1726307 := bstep (se 1 (by rfl) ⟨1294730, by rfl⟩ : syracuseStep 1726307 = 2589461) B2589461
theorem B972643 : Blo 766334 972643 := bstep (se 1 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 972643 = 1458965) B1458965
theorem B972739 : Blo 766334 972739 := bstep (se 1 (by rfl) ⟨729554, by rfl⟩ : syracuseStep 972739 = 1459109) B1459109
theorem B1726577 : Blo 766334 1726577 := bstep (se 2 (by rfl) ⟨647466, by rfl⟩ : syracuseStep 1726577 = 1294933) B1294933
theorem B1726595 : Blo 766334 1726595 := bstep (se 1 (by rfl) ⟨1294946, by rfl⟩ : syracuseStep 1726595 = 2589893) B2589893
theorem B1038529 : Blo 766334 1038529 := bstep (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) B778897
theorem B4446413 : Blo 766334 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B3889457 : Blo 766334 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1726865 : Blo 766334 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B1726883 : Blo 766334 1726883 := bstep (se 1 (by rfl) ⟨1295162, by rfl⟩ : syracuseStep 1726883 = 2590325) B2590325
theorem B973235 : Blo 766334 973235 := bstep (se 1 (by rfl) ⟨729926, by rfl⟩ : syracuseStep 973235 = 1459853) B1459853
theorem B2185805 : Blo 766334 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B1039009 : Blo 766334 1039009 := bstep (se 2 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 1039009 = 779257) B779257
theorem B1727153 : Blo 766334 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1727171 : Blo 766334 1727171 := bstep (se 1 (by rfl) ⟨1295378, by rfl⟩ : syracuseStep 1727171 = 2590757) B2590757
theorem B2185987 : Blo 766334 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B2218769 : Blo 766334 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B9820997 : Blo 766334 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B1727441 : Blo 766334 1727441 := bstep (se 2 (by rfl) ⟨647790, by rfl⟩ : syracuseStep 1727441 = 1295581) B1295581
theorem B1727459 : Blo 766334 1727459 := bstep (se 1 (by rfl) ⟨1295594, by rfl⟩ : syracuseStep 1727459 = 2591189) B2591189
theorem B973939 : Blo 766334 973939 := bstep (se 1 (by rfl) ⟨730454, by rfl⟩ : syracuseStep 973939 = 1460909) B1460909
theorem B974035 : Blo 766334 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B2186477 : Blo 766334 2186477 := bstep (se 3 (by rfl) ⟨409964, by rfl⟩ : syracuseStep 2186477 = 819929) B819929
theorem B1727729 : Blo 766334 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B1727747 : Blo 766334 1727747 := bstep (se 1 (by rfl) ⟨1295810, by rfl⟩ : syracuseStep 1727747 = 2591621) B2591621
theorem B1728017 : Blo 766334 1728017 := bstep (se 2 (by rfl) ⟨648006, by rfl⟩ : syracuseStep 1728017 = 1296013) B1296013
theorem B1728035 : Blo 766334 1728035 := bstep (se 1 (by rfl) ⟨1296026, by rfl⟩ : syracuseStep 1728035 = 2592053) B2592053
theorem B1171027 : Blo 766334 1171027 := bstep (se 1 (by rfl) ⟨878270, by rfl⟩ : syracuseStep 1171027 = 1756541) B1756541
theorem B974531 : Blo 766334 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B3890915 : Blo 766334 3890915 := bstep (se 1 (by rfl) ⟨2918186, by rfl⟩ : syracuseStep 3890915 = 5836373) B5836373
theorem B1728305 : Blo 766334 1728305 := bstep (se 2 (by rfl) ⟨648114, by rfl⟩ : syracuseStep 1728305 = 1296229) B1296229
theorem B1728323 : Blo 766334 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B778195 : Blo 766334 778195 := bstep (se 1 (by rfl) ⟨583646, by rfl⟩ : syracuseStep 778195 = 1167293) B1167293
theorem B1728593 : Blo 766334 1728593 := bstep (se 2 (by rfl) ⟨648222, by rfl⟩ : syracuseStep 1728593 = 1296445) B1296445
theorem B1728611 : Blo 766334 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B9003149 : Blo 766334 9003149 := bstep (se 3 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 9003149 = 3376181) B3376181
theorem B1106065 : Blo 766334 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B5824709 : Blo 766334 5824709 := bstep (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) B1092133
theorem B1728881 : Blo 766334 1728881 := bstep (se 2 (by rfl) ⟨648330, by rfl⟩ : syracuseStep 1728881 = 1296661) B1296661
theorem B1728899 : Blo 766334 1728899 := bstep (se 1 (by rfl) ⟨1296674, by rfl⟩ : syracuseStep 1728899 = 2593349) B2593349
theorem B2187661 : Blo 766334 2187661 := bstep (se 3 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 2187661 = 820373) B820373
theorem B3498481 : Blo 766334 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B3891725 : Blo 766334 3891725 := bstep (se 3 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 3891725 = 1459397) B1459397
theorem B8774243 : Blo 766334 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B1729169 : Blo 766334 1729169 := bstep (se 2 (by rfl) ⟨648438, by rfl⟩ : syracuseStep 1729169 = 1296877) B1296877
theorem B1729187 : Blo 766334 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B1106723 : Blo 766334 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B1729457 : Blo 766334 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1729475 : Blo 766334 1729475 := bstep (se 1 (by rfl) ⟨1297106, by rfl⟩ : syracuseStep 1729475 = 2594213) B2594213
theorem B1729745 : Blo 766334 1729745 := bstep (se 2 (by rfl) ⟨648654, by rfl⟩ : syracuseStep 1729745 = 1297309) B1297309
theorem B1729763 : Blo 766334 1729763 := bstep (se 1 (by rfl) ⟨1297322, by rfl⟩ : syracuseStep 1729763 = 2594645) B2594645
theorem B2221357 : Blo 766334 2221357 := bstep (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) B833009
theorem B2188721 : Blo 766334 2188721 := bstep (se 2 (by rfl) ⟨820770, by rfl⟩ : syracuseStep 2188721 = 1641541) B1641541
theorem B878051 : Blo 766334 878051 := bstep (se 1 (by rfl) ⟨658538, by rfl⟩ : syracuseStep 878051 = 1317077) B1317077
theorem B1730033 : Blo 766334 1730033 := bstep (se 2 (by rfl) ⟨648762, by rfl⟩ : syracuseStep 1730033 = 1297525) B1297525
theorem B1730051 : Blo 766334 1730051 := bstep (se 1 (by rfl) ⟨1297538, by rfl⟩ : syracuseStep 1730051 = 2595077) B2595077
theorem B1730321 : Blo 766334 1730321 := bstep (se 2 (by rfl) ⟨648870, by rfl⟩ : syracuseStep 1730321 = 1297741) B1297741
theorem B1730339 : Blo 766334 1730339 := bstep (se 1 (by rfl) ⟨1297754, by rfl⟩ : syracuseStep 1730339 = 2595509) B2595509
theorem B1730609 : Blo 766334 1730609 := bstep (se 2 (by rfl) ⟨648978, by rfl⟩ : syracuseStep 1730609 = 1297957) B1297957
theorem B1730627 : Blo 766334 1730627 := bstep (se 1 (by rfl) ⟨1297970, by rfl⟩ : syracuseStep 1730627 = 2595941) B2595941
theorem B2189393 : Blo 766334 2189393 := bstep (se 2 (by rfl) ⟨821022, by rfl⟩ : syracuseStep 2189393 = 1642045) B1642045
theorem B5335301 : Blo 766334 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B1730897 : Blo 766334 1730897 := bstep (se 2 (by rfl) ⟨649086, by rfl⟩ : syracuseStep 1730897 = 1298173) B1298173
theorem B2910563 : Blo 766334 2910563 := bstep (se 1 (by rfl) ⟨2182922, by rfl⟩ : syracuseStep 2910563 = 4365845) B4365845
theorem B1730915 : Blo 766334 1730915 := bstep (se 1 (by rfl) ⟨1298186, by rfl⟩ : syracuseStep 1730915 = 2596373) B2596373
theorem B6220273 : Blo 766334 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B8874481 : Blo 766334 8874481 := bstep (se 2 (by rfl) ⟨3327930, by rfl⟩ : syracuseStep 8874481 = 6655861) B6655861
theorem B1731185 : Blo 766334 1731185 := bstep (se 2 (by rfl) ⟨649194, by rfl⟩ : syracuseStep 1731185 = 1298389) B1298389
theorem B1731203 : Blo 766334 1731203 := bstep (se 1 (by rfl) ⟨1298402, by rfl⟩ : syracuseStep 1731203 = 2596805) B2596805
theorem B2190179 : Blo 766334 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B1731473 : Blo 766334 1731473 := bstep (se 2 (by rfl) ⟨649302, by rfl⟩ : syracuseStep 1731473 = 1298605) B1298605
theorem B1731491 : Blo 766334 1731491 := bstep (se 1 (by rfl) ⟨1298618, by rfl⟩ : syracuseStep 1731491 = 2597237) B2597237
theorem B2190509 : Blo 766334 2190509 := bstep (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) B821441
theorem B1731761 : Blo 766334 1731761 := bstep (se 2 (by rfl) ⟨649410, by rfl⟩ : syracuseStep 1731761 = 1298821) B1298821
theorem B9825461 : Blo 766334 9825461 := bstep (se 5 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 9825461 = 921137) B921137
theorem B1731779 : Blo 766334 1731779 := bstep (se 1 (by rfl) ⟨1298834, by rfl⟩ : syracuseStep 1731779 = 2597669) B2597669
theorem B2190577 : Blo 766334 2190577 := bstep (se 2 (by rfl) ⟨821466, by rfl⟩ : syracuseStep 2190577 = 1642933) B1642933
theorem B2911565 : Blo 766334 2911565 := bstep (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) B1091837
theorem B3894641 : Blo 766334 3894641 := bstep (se 2 (by rfl) ⟨1460490, by rfl⟩ : syracuseStep 3894641 = 2920981) B2920981
theorem B1732049 : Blo 766334 1732049 := bstep (se 2 (by rfl) ⟨649518, by rfl⟩ : syracuseStep 1732049 = 1299037) B1299037
theorem B1732067 : Blo 766334 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B2190851 : Blo 766334 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B1109569 : Blo 766334 1109569 := bstep (se 2 (by rfl) ⟨416088, by rfl⟩ : syracuseStep 1109569 = 832177) B832177
theorem B4910705 : Blo 766334 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B1732337 : Blo 766334 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B1732355 : Blo 766334 1732355 := bstep (se 1 (by rfl) ⟨1299266, by rfl⟩ : syracuseStep 1732355 = 2598533) B2598533
theorem B4386757 : Blo 766334 4386757 := bstep (se 4 (by rfl) ⟨411258, by rfl⟩ : syracuseStep 4386757 = 822517) B822517
theorem B1732625 : Blo 766334 1732625 := bstep (se 2 (by rfl) ⟨649734, by rfl⟩ : syracuseStep 1732625 = 1299469) B1299469
theorem B1732643 : Blo 766334 1732643 := bstep (se 1 (by rfl) ⟨1299482, by rfl⟩ : syracuseStep 1732643 = 2598965) B2598965
theorem B4550833 : Blo 766334 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B1732913 : Blo 766334 1732913 := bstep (se 2 (by rfl) ⟨649842, by rfl⟩ : syracuseStep 1732913 = 1299685) B1299685
theorem B1732931 : Blo 766334 1732931 := bstep (se 1 (by rfl) ⟨1299698, by rfl⟩ : syracuseStep 1732931 = 2599397) B2599397
theorem B2191693 : Blo 766334 2191693 := bstep (se 3 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 2191693 = 821885) B821885
theorem B2191853 : Blo 766334 2191853 := bstep (se 3 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 2191853 = 821945) B821945
theorem B1733201 : Blo 766334 1733201 := bstep (se 2 (by rfl) ⟨649950, by rfl⟩ : syracuseStep 1733201 = 1299901) B1299901
theorem B1733219 : Blo 766334 1733219 := bstep (se 1 (by rfl) ⟨1299914, by rfl⟩ : syracuseStep 1733219 = 2599829) B2599829
theorem B2192035 : Blo 766334 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B3896099 : Blo 766334 3896099 := bstep (se 1 (by rfl) ⟨2922074, by rfl⟩ : syracuseStep 3896099 = 5844149) B5844149
theorem B4912397 : Blo 766334 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B2913677 : Blo 766334 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B3503665 : Blo 766334 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B3896909 : Blo 766334 3896909 := bstep (se 3 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 3896909 = 1461341) B1461341
theorem B5830541 : Blo 766334 5830541 := bstep (se 3 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 5830541 = 2186453) B2186453
theorem B2586545 : Blo 766334 2586545 := bstep (se 2 (by rfl) ⟨969954, by rfl⟩ : syracuseStep 2586545 = 1939909) B1939909
theorem B2193425 : Blo 766334 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B15005749 : Blo 766334 15005749 := bstep (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) B1406789
theorem B3274829 : Blo 766334 3274829 := bstep (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) B1228061
theorem B3700849 : Blo 766334 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B2914481 : Blo 766334 2914481 := bstep (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) B2185861
theorem B2587085 : Blo 766334 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B2587139 : Blo 766334 2587139 := bstep (se 1 (by rfl) ⟨1940354, by rfl⟩ : syracuseStep 2587139 = 3880709) B3880709
theorem B2849293 : Blo 766334 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B9337457 : Blo 766334 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B2587409 : Blo 766334 2587409 := bstep (se 2 (by rfl) ⟨970278, by rfl⟩ : syracuseStep 2587409 = 1940557) B1940557
theorem B2915149 : Blo 766334 2915149 := bstep (se 3 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 2915149 = 1093181) B1093181
theorem B1637329 : Blo 766334 1637329 := bstep (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) B1227997
theorem B1637585 : Blo 766334 1637585 := bstep (se 2 (by rfl) ⟨614094, by rfl⟩ : syracuseStep 1637585 = 1228189) B1228189
theorem B4160753 : Blo 766334 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B2587949 : Blo 766334 2587949 := bstep (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) B970481
theorem B818515 : Blo 766334 818515 := bstep (se 1 (by rfl) ⟨613886, by rfl⟩ : syracuseStep 818515 = 1227773) B1227773
theorem B2588003 : Blo 766334 2588003 := bstep (se 1 (by rfl) ⟨1941002, by rfl⟩ : syracuseStep 2588003 = 3882005) B3882005
theorem B2915939 : Blo 766334 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B2588273 : Blo 766334 2588273 := bstep (se 2 (by rfl) ⟨970602, by rfl⟩ : syracuseStep 2588273 = 1941205) B1941205
theorem B3276845 : Blo 766334 3276845 := bstep (se 3 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 3276845 = 1228817) B1228817
theorem B2916881 : Blo 766334 2916881 := bstep (se 2 (by rfl) ⟨1093830, by rfl⟩ : syracuseStep 2916881 = 2187661) B2187661
theorem B3277529 : Blo 766334 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B4162265 : Blo 766334 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B2851549 : Blo 766334 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B16646897 : Blo 766334 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B5899013 : Blo 766334 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B2589515 : Blo 766334 2589515 := bstep (se 1 (by rfl) ⟨1942136, by rfl⟩ : syracuseStep 2589515 = 3884273) B3884273
theorem B2589785 : Blo 766334 2589785 := bstep (se 2 (by rfl) ⟨971169, by rfl⟩ : syracuseStep 2589785 = 1942339) B1942339
theorem B2917579 : Blo 766334 2917579 := bstep (se 1 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 2917579 = 4376369) B4376369
theorem B4916497 : Blo 766334 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B820535 : Blo 766334 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B1246603 : Blo 766334 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B984523 : Blo 766334 984523 := bstep (se 1 (by rfl) ⟨738392, by rfl⟩ : syracuseStep 984523 = 1476785) B1476785
theorem B2917853 : Blo 766334 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B5539421 : Blo 766334 5539421 := bstep (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) B2077283
theorem B2590487 : Blo 766334 2590487 := bstep (se 1 (by rfl) ⟨1942865, by rfl⟩ : syracuseStep 2590487 = 3885731) B3885731
theorem B1640243 : Blo 766334 1640243 := bstep (se 1 (by rfl) ⟨1230182, by rfl⟩ : syracuseStep 1640243 = 2460365) B2460365
theorem B31524785 : Blo 766334 31524785 := bstep (se 2 (by rfl) ⟨11821794, by rfl⟩ : syracuseStep 31524785 = 23643589) B23643589
theorem B2951261 : Blo 766334 2951261 := bstep (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) B1106723
theorem B2918551 : Blo 766334 2918551 := bstep (se 1 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 2918551 = 4377827) B4377827
theorem B1640729 : Blo 766334 1640729 := bstep (se 2 (by rfl) ⟨615273, by rfl⟩ : syracuseStep 1640729 = 1230547) B1230547
theorem B2591027 : Blo 766334 2591027 := bstep (se 1 (by rfl) ⟨1943270, by rfl⟩ : syracuseStep 2591027 = 3886541) B3886541
theorem B7375283 : Blo 766334 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B2591297 : Blo 766334 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B1149515 : Blo 766334 1149515 := bstep (se 1 (by rfl) ⟨862136, by rfl⟩ : syracuseStep 1149515 = 1724273) B1724273
theorem B1149527 : Blo 766334 1149527 := bstep (se 1 (by rfl) ⟨862145, by rfl⟩ : syracuseStep 1149527 = 1724291) B1724291
theorem B5900951 : Blo 766334 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1149593 : Blo 766334 1149593 := bstep (se 2 (by rfl) ⟨431097, by rfl⟩ : syracuseStep 1149593 = 862195) B862195
theorem B1149707 : Blo 766334 1149707 := bstep (se 1 (by rfl) ⟨862280, by rfl⟩ : syracuseStep 1149707 = 1724561) B1724561
theorem B1149719 : Blo 766334 1149719 := bstep (se 1 (by rfl) ⟨862289, by rfl⟩ : syracuseStep 1149719 = 1724579) B1724579
theorem B1149785 : Blo 766334 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B2919341 : Blo 766334 2919341 := bstep (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) B1094753
theorem B1149899 : Blo 766334 1149899 := bstep (se 1 (by rfl) ⟨862424, by rfl⟩ : syracuseStep 1149899 = 1724849) B1724849
theorem B1149911 : Blo 766334 1149911 := bstep (se 1 (by rfl) ⟨862433, by rfl⟩ : syracuseStep 1149911 = 1724867) B1724867
theorem B1248215 : Blo 766334 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B986135 : Blo 766334 986135 := bstep (se 1 (by rfl) ⟨739601, by rfl⟩ : syracuseStep 986135 = 1479203) B1479203
theorem B822295 : Blo 766334 822295 := bstep (se 1 (by rfl) ⟨616721, by rfl⟩ : syracuseStep 822295 = 1233443) B1233443
theorem B1149977 : Blo 766334 1149977 := bstep (se 2 (by rfl) ⟨431241, by rfl⟩ : syracuseStep 1149977 = 862483) B862483
theorem B2591837 : Blo 766334 2591837 := bstep (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) B971939
theorem B1150091 : Blo 766334 1150091 := bstep (se 1 (by rfl) ⟨862568, by rfl⟩ : syracuseStep 1150091 = 1725137) B1725137
theorem B1150103 : Blo 766334 1150103 := bstep (se 1 (by rfl) ⟨862577, by rfl⟩ : syracuseStep 1150103 = 1725155) B1725155
theorem B1477835 : Blo 766334 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B1150169 : Blo 766334 1150169 := bstep (se 2 (by rfl) ⟨431313, by rfl⟩ : syracuseStep 1150169 = 862627) B862627
theorem B1182937 : Blo 766334 1182937 := bstep (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) B887203
theorem B8293697 : Blo 766334 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B11832641 : Blo 766334 11832641 := bstep (se 2 (by rfl) ⟨4437240, by rfl⟩ : syracuseStep 11832641 = 8874481) B8874481
theorem B1150283 : Blo 766334 1150283 := bstep (se 1 (by rfl) ⟨862712, by rfl⟩ : syracuseStep 1150283 = 1725425) B1725425
theorem B1150295 : Blo 766334 1150295 := bstep (se 1 (by rfl) ⟨862721, by rfl⟩ : syracuseStep 1150295 = 1725443) B1725443
theorem B1150361 : Blo 766334 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B1150475 : Blo 766334 1150475 := bstep (se 1 (by rfl) ⟨862856, by rfl⟩ : syracuseStep 1150475 = 1725713) B1725713
theorem B1150487 : Blo 766334 1150487 := bstep (se 1 (by rfl) ⟨862865, by rfl⟩ : syracuseStep 1150487 = 1725731) B1725731
theorem B1150553 : Blo 766334 1150553 := bstep (se 2 (by rfl) ⟨431457, by rfl⟩ : syracuseStep 1150553 = 862915) B862915
theorem B1150667 : Blo 766334 1150667 := bstep (se 1 (by rfl) ⟨863000, by rfl⟩ : syracuseStep 1150667 = 1726001) B1726001
theorem B1150679 : Blo 766334 1150679 := bstep (se 1 (by rfl) ⟨863009, by rfl⟩ : syracuseStep 1150679 = 1726019) B1726019
theorem B1150745 : Blo 766334 1150745 := bstep (se 2 (by rfl) ⟨431529, by rfl⟩ : syracuseStep 1150745 = 863059) B863059
theorem B2461529 : Blo 766334 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1642369 : Blo 766334 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B1150859 : Blo 766334 1150859 := bstep (se 1 (by rfl) ⟨863144, by rfl⟩ : syracuseStep 1150859 = 1726289) B1726289
theorem B1150871 : Blo 766334 1150871 := bstep (se 1 (by rfl) ⟨863153, by rfl⟩ : syracuseStep 1150871 = 1726307) B1726307
theorem B1150937 : Blo 766334 1150937 := bstep (se 2 (by rfl) ⟨431601, by rfl⟩ : syracuseStep 1150937 = 863203) B863203
theorem B1151051 : Blo 766334 1151051 := bstep (se 1 (by rfl) ⟨863288, by rfl⟩ : syracuseStep 1151051 = 1726577) B1726577
theorem B1151063 : Blo 766334 1151063 := bstep (se 1 (by rfl) ⟨863297, by rfl⟩ : syracuseStep 1151063 = 1726595) B1726595
theorem B1151129 : Blo 766334 1151129 := bstep (se 2 (by rfl) ⟨431673, by rfl⟩ : syracuseStep 1151129 = 863347) B863347
theorem B2592971 : Blo 766334 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1151243 : Blo 766334 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B1151255 : Blo 766334 1151255 := bstep (se 1 (by rfl) ⟨863441, by rfl⟩ : syracuseStep 1151255 = 1726883) B1726883
theorem B2920769 : Blo 766334 2920769 := bstep (se 2 (by rfl) ⟨1095288, by rfl⟩ : syracuseStep 2920769 = 2190577) B2190577
theorem B1151321 : Blo 766334 1151321 := bstep (se 2 (by rfl) ⟨431745, by rfl⟩ : syracuseStep 1151321 = 863491) B863491
theorem B1151435 : Blo 766334 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B1151447 : Blo 766334 1151447 := bstep (se 1 (by rfl) ⟨863585, by rfl⟩ : syracuseStep 1151447 = 1727171) B1727171
theorem B2593241 : Blo 766334 2593241 := bstep (se 2 (by rfl) ⟨972465, by rfl⟩ : syracuseStep 2593241 = 1944931) B1944931
theorem B1479179 : Blo 766334 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B1151513 : Blo 766334 1151513 := bstep (se 2 (by rfl) ⟨431817, by rfl⟩ : syracuseStep 1151513 = 863635) B863635
theorem B2953817 : Blo 766334 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B1151627 : Blo 766334 1151627 := bstep (se 1 (by rfl) ⟨863720, by rfl⟩ : syracuseStep 1151627 = 1727441) B1727441
theorem B1151639 : Blo 766334 1151639 := bstep (se 1 (by rfl) ⟨863729, by rfl⟩ : syracuseStep 1151639 = 1727459) B1727459
theorem B1151705 : Blo 766334 1151705 := bstep (se 2 (by rfl) ⟨431889, by rfl⟩ : syracuseStep 1151705 = 863779) B863779
theorem B1479425 : Blo 766334 1479425 := bstep (se 2 (by rfl) ⟨554784, by rfl⟩ : syracuseStep 1479425 = 1109569) B1109569
theorem B10490629 : Blo 766334 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B1151819 : Blo 766334 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B1151831 : Blo 766334 1151831 := bstep (se 1 (by rfl) ⟨863873, by rfl⟩ : syracuseStep 1151831 = 1727747) B1727747
theorem B1151897 : Blo 766334 1151897 := bstep (se 2 (by rfl) ⟨431961, by rfl⟩ : syracuseStep 1151897 = 863923) B863923
theorem B3281867 : Blo 766334 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B1152011 : Blo 766334 1152011 := bstep (se 1 (by rfl) ⟨864008, by rfl⟩ : syracuseStep 1152011 = 1728017) B1728017
theorem B1152023 : Blo 766334 1152023 := bstep (se 1 (by rfl) ⟨864017, by rfl⟩ : syracuseStep 1152023 = 1728035) B1728035
theorem B922699 : Blo 766334 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B1152089 : Blo 766334 1152089 := bstep (se 2 (by rfl) ⟨432033, by rfl⟩ : syracuseStep 1152089 = 864067) B864067
theorem B2593943 : Blo 766334 2593943 := bstep (se 1 (by rfl) ⟨1945457, by rfl⟩ : syracuseStep 2593943 = 3890915) B3890915
theorem B1152203 : Blo 766334 1152203 := bstep (se 1 (by rfl) ⟨864152, by rfl⟩ : syracuseStep 1152203 = 1728305) B1728305
theorem B1578199 : Blo 766334 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B1152215 : Blo 766334 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B1152281 : Blo 766334 1152281 := bstep (se 2 (by rfl) ⟨432105, by rfl⟩ : syracuseStep 1152281 = 864211) B864211
theorem B2463041 : Blo 766334 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B1152395 : Blo 766334 1152395 := bstep (se 1 (by rfl) ⟨864296, by rfl⟩ : syracuseStep 1152395 = 1728593) B1728593
theorem B1152407 : Blo 766334 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B6002099 : Blo 766334 6002099 := bstep (se 1 (by rfl) ⟨4501574, by rfl⟩ : syracuseStep 6002099 = 9003149) B9003149
theorem B1152473 : Blo 766334 1152473 := bstep (se 2 (by rfl) ⟨432177, by rfl⟩ : syracuseStep 1152473 = 864355) B864355
theorem B6067777 : Blo 766334 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B1152587 : Blo 766334 1152587 := bstep (se 1 (by rfl) ⟨864440, by rfl⟩ : syracuseStep 1152587 = 1728881) B1728881
theorem B1152599 : Blo 766334 1152599 := bstep (se 1 (by rfl) ⟨864449, by rfl⟩ : syracuseStep 1152599 = 1728899) B1728899
theorem B1152665 : Blo 766334 1152665 := bstep (se 2 (by rfl) ⟨432249, by rfl⟩ : syracuseStep 1152665 = 864499) B864499
theorem B2594483 : Blo 766334 2594483 := bstep (se 1 (by rfl) ⟨1945862, by rfl⟩ : syracuseStep 2594483 = 3891725) B3891725
theorem B31495877 : Blo 766334 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B1644275 : Blo 766334 1644275 := bstep (se 1 (by rfl) ⟨1233206, by rfl⟩ : syracuseStep 1644275 = 2466413) B2466413
theorem B1152779 : Blo 766334 1152779 := bstep (se 1 (by rfl) ⟨864584, by rfl⟩ : syracuseStep 1152779 = 1729169) B1729169
theorem B2922257 : Blo 766334 2922257 := bstep (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) B2191693
theorem B1382167 : Blo 766334 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B1152791 : Blo 766334 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B22484789 : Blo 766334 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1152857 : Blo 766334 1152857 := bstep (se 2 (by rfl) ⟨432321, by rfl⟩ : syracuseStep 1152857 = 864643) B864643
theorem B3938179 : Blo 766334 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B2594753 : Blo 766334 2594753 := bstep (se 2 (by rfl) ⟨973032, by rfl⟩ : syracuseStep 2594753 = 1946065) B1946065
theorem B1152971 : Blo 766334 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B1152983 : Blo 766334 1152983 := bstep (se 1 (by rfl) ⟨864737, by rfl⟩ : syracuseStep 1152983 = 1729475) B1729475
theorem B1153049 : Blo 766334 1153049 := bstep (se 2 (by rfl) ⟨432393, by rfl⟩ : syracuseStep 1153049 = 864787) B864787
theorem B9836579 : Blo 766334 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B1153163 : Blo 766334 1153163 := bstep (se 1 (by rfl) ⟨864872, by rfl⟩ : syracuseStep 1153163 = 1729745) B1729745
theorem B1153175 : Blo 766334 1153175 := bstep (se 1 (by rfl) ⟨864881, by rfl⟩ : syracuseStep 1153175 = 1729763) B1729763
theorem B1153241 : Blo 766334 1153241 := bstep (se 2 (by rfl) ⟨432465, by rfl⟩ : syracuseStep 1153241 = 864931) B864931
theorem B2922713 : Blo 766334 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B1644761 : Blo 766334 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B3512641 : Blo 766334 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B1153355 : Blo 766334 1153355 := bstep (se 1 (by rfl) ⟨865016, by rfl⟩ : syracuseStep 1153355 = 1730033) B1730033
theorem B1153367 : Blo 766334 1153367 := bstep (se 1 (by rfl) ⟨865025, by rfl⟩ : syracuseStep 1153367 = 1730051) B1730051
theorem B11049317 : Blo 766334 11049317 := bstep (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) B2071747
theorem B1153433 : Blo 766334 1153433 := bstep (se 2 (by rfl) ⟨432537, by rfl⟩ : syracuseStep 1153433 = 865075) B865075
theorem B2922925 : Blo 766334 2922925 := bstep (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) B1096097
theorem B2595293 : Blo 766334 2595293 := bstep (se 3 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 2595293 = 973235) B973235
theorem B1153547 : Blo 766334 1153547 := bstep (se 1 (by rfl) ⟨865160, by rfl⟩ : syracuseStep 1153547 = 1730321) B1730321
theorem B1153559 : Blo 766334 1153559 := bstep (se 1 (by rfl) ⟨865169, by rfl⟩ : syracuseStep 1153559 = 1730339) B1730339
theorem B3283507 : Blo 766334 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B2333249 : Blo 766334 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B1153625 : Blo 766334 1153625 := bstep (se 2 (by rfl) ⟨432609, by rfl⟩ : syracuseStep 1153625 = 865219) B865219
theorem B1153739 : Blo 766334 1153739 := bstep (se 1 (by rfl) ⟨865304, by rfl⟩ : syracuseStep 1153739 = 1730609) B1730609
theorem B1153751 : Blo 766334 1153751 := bstep (se 1 (by rfl) ⟨865313, by rfl⟩ : syracuseStep 1153751 = 1730627) B1730627
theorem B2923229 : Blo 766334 2923229 := bstep (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) B1096211
theorem B1153817 : Blo 766334 1153817 := bstep (se 2 (by rfl) ⟨432681, by rfl⟩ : syracuseStep 1153817 = 865363) B865363
theorem B1153931 : Blo 766334 1153931 := bstep (se 1 (by rfl) ⟨865448, by rfl⟩ : syracuseStep 1153931 = 1730897) B1730897
theorem B1940375 : Blo 766334 1940375 := bstep (se 1 (by rfl) ⟨1455281, by rfl⟩ : syracuseStep 1940375 = 2910563) B2910563
theorem B1153943 : Blo 766334 1153943 := bstep (se 1 (by rfl) ⟨865457, by rfl⟩ : syracuseStep 1153943 = 1730915) B1730915
theorem B4201433 : Blo 766334 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B1383385 : Blo 766334 1383385 := bstep (se 2 (by rfl) ⟨518769, by rfl⟩ : syracuseStep 1383385 = 1037539) B1037539
theorem B29563865 : Blo 766334 29563865 := bstep (se 2 (by rfl) ⟨11086449, by rfl⟩ : syracuseStep 29563865 = 22172899) B22172899
theorem B1154009 : Blo 766334 1154009 := bstep (se 2 (by rfl) ⟨432753, by rfl⟩ : syracuseStep 1154009 = 865507) B865507
theorem B1154123 : Blo 766334 1154123 := bstep (se 1 (by rfl) ⟨865592, by rfl⟩ : syracuseStep 1154123 = 1731185) B1731185
theorem B1154135 : Blo 766334 1154135 := bstep (se 1 (by rfl) ⟨865601, by rfl⟩ : syracuseStep 1154135 = 1731203) B1731203
theorem B4365413 : Blo 766334 4365413 := bstep (se 4 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 4365413 = 818515) B818515
theorem B1154201 : Blo 766334 1154201 := bstep (se 2 (by rfl) ⟨432825, by rfl⟩ : syracuseStep 1154201 = 865651) B865651
theorem B1154315 : Blo 766334 1154315 := bstep (se 1 (by rfl) ⟨865736, by rfl⟩ : syracuseStep 1154315 = 1731473) B1731473
theorem B1154327 : Blo 766334 1154327 := bstep (se 1 (by rfl) ⟨865745, by rfl⟩ : syracuseStep 1154327 = 1731491) B1731491
theorem B1383731 : Blo 766334 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B1973555 : Blo 766334 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B1154393 : Blo 766334 1154393 := bstep (se 2 (by rfl) ⟨432897, by rfl⟩ : syracuseStep 1154393 = 865795) B865795
theorem B1154507 : Blo 766334 1154507 := bstep (se 1 (by rfl) ⟨865880, by rfl⟩ : syracuseStep 1154507 = 1731761) B1731761
theorem B5545421 : Blo 766334 5545421 := bstep (se 3 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 5545421 = 2079533) B2079533
theorem B1154519 : Blo 766334 1154519 := bstep (se 1 (by rfl) ⟨865889, by rfl⟩ : syracuseStep 1154519 = 1731779) B1731779
theorem B2465245 : Blo 766334 2465245 := bstep (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) B924467
theorem B1154585 : Blo 766334 1154585 := bstep (se 2 (by rfl) ⟨432969, by rfl⟩ : syracuseStep 1154585 = 865939) B865939
theorem B1941043 : Blo 766334 1941043 := bstep (se 1 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 1941043 = 2911565) B2911565
theorem B2596427 : Blo 766334 2596427 := bstep (se 1 (by rfl) ⟨1947320, by rfl⟩ : syracuseStep 2596427 = 3894641) B3894641
theorem B1154699 : Blo 766334 1154699 := bstep (se 1 (by rfl) ⟨866024, by rfl⟩ : syracuseStep 1154699 = 1732049) B1732049
theorem B1154711 : Blo 766334 1154711 := bstep (se 1 (by rfl) ⟨866033, by rfl⟩ : syracuseStep 1154711 = 1732067) B1732067
theorem B1941185 : Blo 766334 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B36052685 : Blo 766334 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B1154777 : Blo 766334 1154777 := bstep (se 2 (by rfl) ⟨433041, by rfl⟩ : syracuseStep 1154777 = 866083) B866083
theorem B6233861 : Blo 766334 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B1154891 : Blo 766334 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B1154903 : Blo 766334 1154903 := bstep (se 1 (by rfl) ⟨866177, by rfl⟩ : syracuseStep 1154903 = 1732355) B1732355
theorem B2596697 : Blo 766334 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B1154969 : Blo 766334 1154969 := bstep (se 2 (by rfl) ⟨433113, by rfl⟩ : syracuseStep 1154969 = 866227) B866227
theorem B3284995 : Blo 766334 3284995 := bstep (se 1 (by rfl) ⟨2463746, by rfl⟩ : syracuseStep 3284995 = 4927493) B4927493
theorem B1155083 : Blo 766334 1155083 := bstep (se 1 (by rfl) ⟨866312, by rfl⟩ : syracuseStep 1155083 = 1732625) B1732625
theorem B1155095 : Blo 766334 1155095 := bstep (se 1 (by rfl) ⟨866321, by rfl⟩ : syracuseStep 1155095 = 1732643) B1732643
theorem B1155161 : Blo 766334 1155161 := bstep (se 2 (by rfl) ⟨433185, by rfl⟩ : syracuseStep 1155161 = 866371) B866371
theorem B1155275 : Blo 766334 1155275 := bstep (se 1 (by rfl) ⟨866456, by rfl⟩ : syracuseStep 1155275 = 1732913) B1732913
theorem B6234317 : Blo 766334 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B1155287 : Blo 766334 1155287 := bstep (se 1 (by rfl) ⟨866465, by rfl⟩ : syracuseStep 1155287 = 1732931) B1732931
theorem B1384705 : Blo 766334 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B1155353 : Blo 766334 1155353 := bstep (se 2 (by rfl) ⟨433257, by rfl⟩ : syracuseStep 1155353 = 866515) B866515
theorem B6562093 : Blo 766334 6562093 := bstep (se 3 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 6562093 = 2460785) B2460785
theorem B1155467 : Blo 766334 1155467 := bstep (se 1 (by rfl) ⟨866600, by rfl⟩ : syracuseStep 1155467 = 1733201) B1733201
theorem B1155479 : Blo 766334 1155479 := bstep (se 1 (by rfl) ⟨866609, by rfl⟩ : syracuseStep 1155479 = 1733219) B1733219
theorem B4923827 : Blo 766334 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B2597399 : Blo 766334 2597399 := bstep (se 1 (by rfl) ⟨1948049, by rfl⟩ : syracuseStep 2597399 = 3896099) B3896099
theorem B1581619 : Blo 766334 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B3285593 : Blo 766334 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B1385345 : Blo 766334 1385345 := bstep (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) B1039009
theorem B1942451 : Blo 766334 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B12460979 : Blo 766334 12460979 := bstep (se 1 (by rfl) ⟨9345734, by rfl⟩ : syracuseStep 12460979 = 18691469) B18691469
theorem B3285953 : Blo 766334 3285953 := bstep (se 2 (by rfl) ⟨1232232, by rfl⟩ : syracuseStep 3285953 = 2464465) B2464465
theorem B2597939 : Blo 766334 2597939 := bstep (se 1 (by rfl) ⟨1948454, by rfl⟩ : syracuseStep 2597939 = 3896909) B3896909
theorem B2598209 : Blo 766334 2598209 := bstep (se 2 (by rfl) ⟨974328, by rfl⟩ : syracuseStep 2598209 = 1948657) B1948657
theorem B1942987 : Blo 766334 1942987 := bstep (se 1 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 1942987 = 2914481) B2914481
theorem B1943129 : Blo 766334 1943129 := bstep (se 2 (by rfl) ⟨728673, by rfl⟩ : syracuseStep 1943129 = 1457347) B1457347
theorem B6563429 : Blo 766334 6563429 := bstep (se 4 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 6563429 = 1230643) B1230643
theorem B2762561 : Blo 766334 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B2598749 : Blo 766334 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B862231 : Blo 766334 862231 := bstep (se 1 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 862231 = 1293347) B1293347
theorem B1976395 : Blo 766334 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1091723 : Blo 766334 1091723 := bstep (se 1 (by rfl) ⟨818792, by rfl⟩ : syracuseStep 1091723 = 1637585) B1637585
theorem B862411 : Blo 766334 862411 := bstep (se 1 (by rfl) ⟨646808, by rfl⟩ : syracuseStep 862411 = 1293617) B1293617
theorem B2074841 : Blo 766334 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B862519 : Blo 766334 862519 := bstep (se 1 (by rfl) ⟨646889, by rfl⟩ : syracuseStep 862519 = 1293779) B1293779
theorem B1943959 : Blo 766334 1943959 := bstep (se 1 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 1943959 = 2915939) B2915939
theorem B862699 : Blo 766334 862699 := bstep (se 1 (by rfl) ⟨647024, by rfl⟩ : syracuseStep 862699 = 1294049) B1294049
theorem B862807 : Blo 766334 862807 := bstep (se 1 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 862807 = 1294211) B1294211
theorem B862987 : Blo 766334 862987 := bstep (se 1 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 862987 = 1294481) B1294481
theorem B2763571 : Blo 766334 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1944395 : Blo 766334 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B22195043 : Blo 766334 22195043 := bstep (se 1 (by rfl) ⟨16646282, by rfl⟩ : syracuseStep 22195043 = 33292565) B33292565
theorem B863095 : Blo 766334 863095 := bstep (se 1 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 863095 = 1294643) B1294643
theorem B863275 : Blo 766334 863275 := bstep (se 1 (by rfl) ⟨647456, by rfl⟩ : syracuseStep 863275 = 1294913) B1294913
theorem B863383 : Blo 766334 863383 := bstep (se 1 (by rfl) ⟨647537, by rfl⟩ : syracuseStep 863383 = 1295075) B1295075
theorem B1944769 : Blo 766334 1944769 := bstep (se 2 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 1944769 = 1458577) B1458577
theorem B4664641 : Blo 766334 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B863563 : Blo 766334 863563 := bstep (se 1 (by rfl) ⟨647672, by rfl⟩ : syracuseStep 863563 = 1295345) B1295345
theorem B863671 : Blo 766334 863671 := bstep (se 1 (by rfl) ⟨647753, by rfl⟩ : syracuseStep 863671 = 1295507) B1295507
theorem B1388107 : Blo 766334 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B863851 : Blo 766334 863851 := bstep (se 1 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 863851 = 1295777) B1295777
theorem B863959 : Blo 766334 863959 := bstep (se 1 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 863959 = 1295939) B1295939
theorem B1945367 : Blo 766334 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B2764637 : Blo 766334 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B864139 : Blo 766334 864139 := bstep (se 1 (by rfl) ⟨648104, by rfl⟩ : syracuseStep 864139 = 1296209) B1296209
theorem B3321803 : Blo 766334 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B1093591 : Blo 766334 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B864247 : Blo 766334 864247 := bstep (se 1 (by rfl) ⟨648185, by rfl⟩ : syracuseStep 864247 = 1296371) B1296371
theorem B864427 : Blo 766334 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B864535 : Blo 766334 864535 := bstep (se 1 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 864535 = 1296803) B1296803
theorem B766347 : Blo 766334 766347 := bstep (se 1 (by rfl) ⟨574760, by rfl⟩ : syracuseStep 766347 = 1149521) B1149521
theorem B2961809 : Blo 766334 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B766359 : Blo 766334 766359 := bstep (se 1 (by rfl) ⟨574769, by rfl⟩ : syracuseStep 766359 = 1149539) B1149539
theorem B766379 : Blo 766334 766379 := bstep (se 1 (by rfl) ⟨574784, by rfl⟩ : syracuseStep 766379 = 1149569) B1149569
theorem B766391 : Blo 766334 766391 := bstep (se 1 (by rfl) ⟨574793, by rfl⟩ : syracuseStep 766391 = 1149587) B1149587
theorem B766411 : Blo 766334 766411 := bstep (se 1 (by rfl) ⟨574808, by rfl⟩ : syracuseStep 766411 = 1149617) B1149617
theorem B864715 : Blo 766334 864715 := bstep (se 1 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 864715 = 1297073) B1297073
theorem B766423 : Blo 766334 766423 := bstep (se 1 (by rfl) ⟨574817, by rfl⟩ : syracuseStep 766423 = 1149635) B1149635
theorem B766443 : Blo 766334 766443 := bstep (se 1 (by rfl) ⟨574832, by rfl⟩ : syracuseStep 766443 = 1149665) B1149665
theorem B766455 : Blo 766334 766455 := bstep (se 1 (by rfl) ⟨574841, by rfl⟩ : syracuseStep 766455 = 1149683) B1149683
theorem B766475 : Blo 766334 766475 := bstep (se 1 (by rfl) ⟨574856, by rfl⟩ : syracuseStep 766475 = 1149713) B1149713
theorem B766487 : Blo 766334 766487 := bstep (se 1 (by rfl) ⟨574865, by rfl⟩ : syracuseStep 766487 = 1149731) B1149731
theorem B766507 : Blo 766334 766507 := bstep (se 1 (by rfl) ⟨574880, by rfl⟩ : syracuseStep 766507 = 1149761) B1149761
theorem B766519 : Blo 766334 766519 := bstep (se 1 (by rfl) ⟨574889, by rfl⟩ : syracuseStep 766519 = 1149779) B1149779
theorem B864823 : Blo 766334 864823 := bstep (se 1 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 864823 = 1297235) B1297235
theorem B1946177 : Blo 766334 1946177 := bstep (se 2 (by rfl) ⟨729816, by rfl⟩ : syracuseStep 1946177 = 1459633) B1459633
theorem B766539 : Blo 766334 766539 := bstep (se 1 (by rfl) ⟨574904, by rfl⟩ : syracuseStep 766539 = 1149809) B1149809
theorem B766551 : Blo 766334 766551 := bstep (se 1 (by rfl) ⟨574913, by rfl⟩ : syracuseStep 766551 = 1149827) B1149827
theorem B1847897 : Blo 766334 1847897 := bstep (se 2 (by rfl) ⟨692961, by rfl⟩ : syracuseStep 1847897 = 1385923) B1385923
theorem B3289693 : Blo 766334 3289693 := bstep (se 3 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 3289693 = 1233635) B1233635
theorem B766571 : Blo 766334 766571 := bstep (se 1 (by rfl) ⟨574928, by rfl⟩ : syracuseStep 766571 = 1149857) B1149857
theorem B766583 : Blo 766334 766583 := bstep (se 1 (by rfl) ⟨574937, by rfl⟩ : syracuseStep 766583 = 1149875) B1149875
theorem B4928131 : Blo 766334 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B766603 : Blo 766334 766603 := bstep (se 1 (by rfl) ⟨574952, by rfl⟩ : syracuseStep 766603 = 1149905) B1149905
theorem B3879575 : Blo 766334 3879575 := bstep (se 1 (by rfl) ⟨2909681, by rfl⟩ : syracuseStep 3879575 = 5819363) B5819363
theorem B766615 : Blo 766334 766615 := bstep (se 1 (by rfl) ⟨574961, by rfl⟩ : syracuseStep 766615 = 1149923) B1149923
theorem B766635 : Blo 766334 766635 := bstep (se 1 (by rfl) ⟨574976, by rfl⟩ : syracuseStep 766635 = 1149953) B1149953
theorem B766647 : Blo 766334 766647 := bstep (se 1 (by rfl) ⟨574985, by rfl⟩ : syracuseStep 766647 = 1149971) B1149971
theorem B766667 : Blo 766334 766667 := bstep (se 1 (by rfl) ⟨575000, by rfl⟩ : syracuseStep 766667 = 1150001) B1150001
theorem B766679 : Blo 766334 766679 := bstep (se 1 (by rfl) ⟨575009, by rfl⟩ : syracuseStep 766679 = 1150019) B1150019
theorem B766699 : Blo 766334 766699 := bstep (se 1 (by rfl) ⟨575024, by rfl⟩ : syracuseStep 766699 = 1150049) B1150049
theorem B865003 : Blo 766334 865003 := bstep (se 1 (by rfl) ⟨648752, by rfl⟩ : syracuseStep 865003 = 1297505) B1297505
theorem B766711 : Blo 766334 766711 := bstep (se 1 (by rfl) ⟨575033, by rfl⟩ : syracuseStep 766711 = 1150067) B1150067
theorem B766731 : Blo 766334 766731 := bstep (se 1 (by rfl) ⟨575048, by rfl⟩ : syracuseStep 766731 = 1150097) B1150097
theorem B766743 : Blo 766334 766743 := bstep (se 1 (by rfl) ⟨575057, by rfl⟩ : syracuseStep 766743 = 1150115) B1150115
theorem B766763 : Blo 766334 766763 := bstep (se 1 (by rfl) ⟨575072, by rfl⟩ : syracuseStep 766763 = 1150145) B1150145
theorem B4371245 : Blo 766334 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B766775 : Blo 766334 766775 := bstep (se 1 (by rfl) ⟨575081, by rfl⟩ : syracuseStep 766775 = 1150163) B1150163
theorem B766795 : Blo 766334 766795 := bstep (se 1 (by rfl) ⟨575096, by rfl⟩ : syracuseStep 766795 = 1150193) B1150193
theorem B1422155 : Blo 766334 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B6239051 : Blo 766334 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B766807 : Blo 766334 766807 := bstep (se 1 (by rfl) ⟨575105, by rfl⟩ : syracuseStep 766807 = 1150211) B1150211
theorem B865111 : Blo 766334 865111 := bstep (se 1 (by rfl) ⟨648833, by rfl⟩ : syracuseStep 865111 = 1297667) B1297667
theorem B766827 : Blo 766334 766827 := bstep (se 1 (by rfl) ⟨575120, by rfl⟩ : syracuseStep 766827 = 1150241) B1150241
theorem B766839 : Blo 766334 766839 := bstep (se 1 (by rfl) ⟨575129, by rfl⟩ : syracuseStep 766839 = 1150259) B1150259
theorem B766859 : Blo 766334 766859 := bstep (se 1 (by rfl) ⟨575144, by rfl⟩ : syracuseStep 766859 = 1150289) B1150289
theorem B766871 : Blo 766334 766871 := bstep (se 1 (by rfl) ⟨575153, by rfl⟩ : syracuseStep 766871 = 1150307) B1150307
theorem B766891 : Blo 766334 766891 := bstep (se 1 (by rfl) ⟨575168, by rfl⟩ : syracuseStep 766891 = 1150337) B1150337
theorem B766903 : Blo 766334 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B766923 : Blo 766334 766923 := bstep (se 1 (by rfl) ⟨575192, by rfl⟩ : syracuseStep 766923 = 1150385) B1150385
theorem B766935 : Blo 766334 766935 := bstep (se 1 (by rfl) ⟨575201, by rfl⟩ : syracuseStep 766935 = 1150403) B1150403
theorem B766955 : Blo 766334 766955 := bstep (se 1 (by rfl) ⟨575216, by rfl⟩ : syracuseStep 766955 = 1150433) B1150433
theorem B766967 : Blo 766334 766967 := bstep (se 1 (by rfl) ⟨575225, by rfl⟩ : syracuseStep 766967 = 1150451) B1150451
theorem B766987 : Blo 766334 766987 := bstep (se 1 (by rfl) ⟨575240, by rfl⟩ : syracuseStep 766987 = 1150481) B1150481
theorem B865291 : Blo 766334 865291 := bstep (se 1 (by rfl) ⟨648968, by rfl⟩ : syracuseStep 865291 = 1297937) B1297937
theorem B766999 : Blo 766334 766999 := bstep (se 1 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 766999 = 1150499) B1150499
theorem B767019 : Blo 766334 767019 := bstep (se 1 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 767019 = 1150529) B1150529
theorem B767031 : Blo 766334 767031 := bstep (se 1 (by rfl) ⟨575273, by rfl⟩ : syracuseStep 767031 = 1150547) B1150547
theorem B767051 : Blo 766334 767051 := bstep (se 1 (by rfl) ⟨575288, by rfl⟩ : syracuseStep 767051 = 1150577) B1150577
theorem B767063 : Blo 766334 767063 := bstep (se 1 (by rfl) ⟨575297, by rfl⟩ : syracuseStep 767063 = 1150595) B1150595
theorem B1946713 : Blo 766334 1946713 := bstep (se 2 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 1946713 = 1460035) B1460035
theorem B767083 : Blo 766334 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B767095 : Blo 766334 767095 := bstep (se 1 (by rfl) ⟨575321, by rfl⟩ : syracuseStep 767095 = 1150643) B1150643
theorem B865399 : Blo 766334 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B767115 : Blo 766334 767115 := bstep (se 1 (by rfl) ⟨575336, by rfl⟩ : syracuseStep 767115 = 1150673) B1150673
theorem B767127 : Blo 766334 767127 := bstep (se 1 (by rfl) ⟨575345, by rfl⟩ : syracuseStep 767127 = 1150691) B1150691
theorem B767147 : Blo 766334 767147 := bstep (se 1 (by rfl) ⟨575360, by rfl⟩ : syracuseStep 767147 = 1150721) B1150721
theorem B5256371 : Blo 766334 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B767159 : Blo 766334 767159 := bstep (se 1 (by rfl) ⟨575369, by rfl⟩ : syracuseStep 767159 = 1150739) B1150739
theorem B767179 : Blo 766334 767179 := bstep (se 1 (by rfl) ⟨575384, by rfl⟩ : syracuseStep 767179 = 1150769) B1150769
theorem B767191 : Blo 766334 767191 := bstep (se 1 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 767191 = 1150787) B1150787
theorem B767211 : Blo 766334 767211 := bstep (se 1 (by rfl) ⟨575408, by rfl⟩ : syracuseStep 767211 = 1150817) B1150817
theorem B767223 : Blo 766334 767223 := bstep (se 1 (by rfl) ⟨575417, by rfl⟩ : syracuseStep 767223 = 1150835) B1150835
theorem B767243 : Blo 766334 767243 := bstep (se 1 (by rfl) ⟨575432, by rfl⟩ : syracuseStep 767243 = 1150865) B1150865
theorem B767255 : Blo 766334 767255 := bstep (se 1 (by rfl) ⟨575441, by rfl⟩ : syracuseStep 767255 = 1150883) B1150883
theorem B2077975 : Blo 766334 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B767275 : Blo 766334 767275 := bstep (se 1 (by rfl) ⟨575456, by rfl⟩ : syracuseStep 767275 = 1150913) B1150913
theorem B865579 : Blo 766334 865579 := bstep (se 1 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 865579 = 1298369) B1298369
theorem B767287 : Blo 766334 767287 := bstep (se 1 (by rfl) ⟨575465, by rfl⟩ : syracuseStep 767287 = 1150931) B1150931
theorem B1750337 : Blo 766334 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B767307 : Blo 766334 767307 := bstep (se 1 (by rfl) ⟨575480, by rfl⟩ : syracuseStep 767307 = 1150961) B1150961
theorem B767319 : Blo 766334 767319 := bstep (se 1 (by rfl) ⟨575489, by rfl⟩ : syracuseStep 767319 = 1150979) B1150979
theorem B1848665 : Blo 766334 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B767339 : Blo 766334 767339 := bstep (se 1 (by rfl) ⟨575504, by rfl⟩ : syracuseStep 767339 = 1151009) B1151009
theorem B767351 : Blo 766334 767351 := bstep (se 1 (by rfl) ⟨575513, by rfl⟩ : syracuseStep 767351 = 1151027) B1151027
theorem B767371 : Blo 766334 767371 := bstep (se 1 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 767371 = 1151057) B1151057
theorem B767383 : Blo 766334 767383 := bstep (se 1 (by rfl) ⟨575537, by rfl⟩ : syracuseStep 767383 = 1151075) B1151075
theorem B865687 : Blo 766334 865687 := bstep (se 1 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 865687 = 1298531) B1298531
theorem B767403 : Blo 766334 767403 := bstep (se 1 (by rfl) ⟨575552, by rfl⟩ : syracuseStep 767403 = 1151105) B1151105
theorem B1553843 : Blo 766334 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B767415 : Blo 766334 767415 := bstep (se 1 (by rfl) ⟨575561, by rfl⟩ : syracuseStep 767415 = 1151123) B1151123
theorem B1455563 : Blo 766334 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B767435 : Blo 766334 767435 := bstep (se 1 (by rfl) ⟨575576, by rfl⟩ : syracuseStep 767435 = 1151153) B1151153
theorem B767447 : Blo 766334 767447 := bstep (se 1 (by rfl) ⟨575585, by rfl⟩ : syracuseStep 767447 = 1151171) B1151171
theorem B767467 : Blo 766334 767467 := bstep (se 1 (by rfl) ⟨575600, by rfl⟩ : syracuseStep 767467 = 1151201) B1151201
theorem B767479 : Blo 766334 767479 := bstep (se 1 (by rfl) ⟨575609, by rfl⟩ : syracuseStep 767479 = 1151219) B1151219
theorem B767499 : Blo 766334 767499 := bstep (se 1 (by rfl) ⟨575624, by rfl⟩ : syracuseStep 767499 = 1151249) B1151249
theorem B767511 : Blo 766334 767511 := bstep (se 1 (by rfl) ⟨575633, by rfl⟩ : syracuseStep 767511 = 1151267) B1151267
theorem B767531 : Blo 766334 767531 := bstep (se 1 (by rfl) ⟨575648, by rfl⟩ : syracuseStep 767531 = 1151297) B1151297
theorem B767543 : Blo 766334 767543 := bstep (se 1 (by rfl) ⟨575657, by rfl⟩ : syracuseStep 767543 = 1151315) B1151315
theorem B767563 : Blo 766334 767563 := bstep (se 1 (by rfl) ⟨575672, by rfl⟩ : syracuseStep 767563 = 1151345) B1151345
theorem B865867 : Blo 766334 865867 := bstep (se 1 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 865867 = 1298801) B1298801
theorem B767575 : Blo 766334 767575 := bstep (se 1 (by rfl) ⟨575681, by rfl⟩ : syracuseStep 767575 = 1151363) B1151363
theorem B767595 : Blo 766334 767595 := bstep (se 1 (by rfl) ⟨575696, by rfl⟩ : syracuseStep 767595 = 1151393) B1151393
theorem B767607 : Blo 766334 767607 := bstep (se 1 (by rfl) ⟨575705, by rfl⟩ : syracuseStep 767607 = 1151411) B1151411
theorem B1455745 : Blo 766334 1455745 := bstep (se 2 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 1455745 = 1091809) B1091809
theorem B767627 : Blo 766334 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B767639 : Blo 766334 767639 := bstep (se 1 (by rfl) ⟨575729, by rfl⟩ : syracuseStep 767639 = 1151459) B1151459
theorem B767659 : Blo 766334 767659 := bstep (se 1 (by rfl) ⟨575744, by rfl⟩ : syracuseStep 767659 = 1151489) B1151489
theorem B767671 : Blo 766334 767671 := bstep (se 1 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 767671 = 1151507) B1151507
theorem B865975 : Blo 766334 865975 := bstep (se 1 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 865975 = 1298963) B1298963
theorem B767691 : Blo 766334 767691 := bstep (se 1 (by rfl) ⟨575768, by rfl⟩ : syracuseStep 767691 = 1151537) B1151537
theorem B767703 : Blo 766334 767703 := bstep (se 1 (by rfl) ⟨575777, by rfl⟩ : syracuseStep 767703 = 1151555) B1151555
theorem B767723 : Blo 766334 767723 := bstep (se 1 (by rfl) ⟨575792, by rfl⟩ : syracuseStep 767723 = 1151585) B1151585
theorem B767735 : Blo 766334 767735 := bstep (se 1 (by rfl) ⟨575801, by rfl⟩ : syracuseStep 767735 = 1151603) B1151603
theorem B767755 : Blo 766334 767755 := bstep (se 1 (by rfl) ⟨575816, by rfl⟩ : syracuseStep 767755 = 1151633) B1151633
theorem B767767 : Blo 766334 767767 := bstep (se 1 (by rfl) ⟨575825, by rfl⟩ : syracuseStep 767767 = 1151651) B1151651
theorem B767787 : Blo 766334 767787 := bstep (se 1 (by rfl) ⟨575840, by rfl⟩ : syracuseStep 767787 = 1151681) B1151681
theorem B767799 : Blo 766334 767799 := bstep (se 1 (by rfl) ⟨575849, by rfl⟩ : syracuseStep 767799 = 1151699) B1151699
theorem B767819 : Blo 766334 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B767831 : Blo 766334 767831 := bstep (se 1 (by rfl) ⟨575873, by rfl⟩ : syracuseStep 767831 = 1151747) B1151747
theorem B767851 : Blo 766334 767851 := bstep (se 1 (by rfl) ⟨575888, by rfl⟩ : syracuseStep 767851 = 1151777) B1151777
theorem B866155 : Blo 766334 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B767863 : Blo 766334 767863 := bstep (se 1 (by rfl) ⟨575897, by rfl⟩ : syracuseStep 767863 = 1151795) B1151795
theorem B767883 : Blo 766334 767883 := bstep (se 1 (by rfl) ⟨575912, by rfl⟩ : syracuseStep 767883 = 1151825) B1151825
theorem B767895 : Blo 766334 767895 := bstep (se 1 (by rfl) ⟨575921, by rfl⟩ : syracuseStep 767895 = 1151843) B1151843
theorem B767915 : Blo 766334 767915 := bstep (se 1 (by rfl) ⟨575936, by rfl⟩ : syracuseStep 767915 = 1151873) B1151873
theorem B767927 : Blo 766334 767927 := bstep (se 1 (by rfl) ⟨575945, by rfl⟩ : syracuseStep 767927 = 1151891) B1151891
theorem B767947 : Blo 766334 767947 := bstep (se 1 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 767947 = 1151921) B1151921
theorem B767959 : Blo 766334 767959 := bstep (se 1 (by rfl) ⟨575969, by rfl⟩ : syracuseStep 767959 = 1151939) B1151939
theorem B866263 : Blo 766334 866263 := bstep (se 1 (by rfl) ⟨649697, by rfl⟩ : syracuseStep 866263 = 1299395) B1299395
theorem B767979 : Blo 766334 767979 := bstep (se 1 (by rfl) ⟨575984, by rfl⟩ : syracuseStep 767979 = 1151969) B1151969
theorem B767991 : Blo 766334 767991 := bstep (se 1 (by rfl) ⟨575993, by rfl⟩ : syracuseStep 767991 = 1151987) B1151987
theorem B768011 : Blo 766334 768011 := bstep (se 1 (by rfl) ⟨576008, by rfl⟩ : syracuseStep 768011 = 1152017) B1152017
theorem B768023 : Blo 766334 768023 := bstep (se 1 (by rfl) ⟨576017, by rfl⟩ : syracuseStep 768023 = 1152035) B1152035
theorem B768043 : Blo 766334 768043 := bstep (se 1 (by rfl) ⟨576032, by rfl⟩ : syracuseStep 768043 = 1152065) B1152065
theorem B768055 : Blo 766334 768055 := bstep (se 1 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 768055 = 1152083) B1152083
theorem B1456193 : Blo 766334 1456193 := bstep (se 2 (by rfl) ⟨546072, by rfl⟩ : syracuseStep 1456193 = 1092145) B1092145
theorem B768075 : Blo 766334 768075 := bstep (se 1 (by rfl) ⟨576056, by rfl⟩ : syracuseStep 768075 = 1152113) B1152113
theorem B768087 : Blo 766334 768087 := bstep (se 1 (by rfl) ⟨576065, by rfl⟩ : syracuseStep 768087 = 1152131) B1152131
theorem B768107 : Blo 766334 768107 := bstep (se 1 (by rfl) ⟨576080, by rfl⟩ : syracuseStep 768107 = 1152161) B1152161
theorem B768119 : Blo 766334 768119 := bstep (se 1 (by rfl) ⟨576089, by rfl⟩ : syracuseStep 768119 = 1152179) B1152179
theorem B768139 : Blo 766334 768139 := bstep (se 1 (by rfl) ⟨576104, by rfl⟩ : syracuseStep 768139 = 1152209) B1152209
theorem B866443 : Blo 766334 866443 := bstep (se 1 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 866443 = 1299665) B1299665
theorem B768151 : Blo 766334 768151 := bstep (se 1 (by rfl) ⟨576113, by rfl⟩ : syracuseStep 768151 = 1152227) B1152227
theorem B768171 : Blo 766334 768171 := bstep (se 1 (by rfl) ⟨576128, by rfl⟩ : syracuseStep 768171 = 1152257) B1152257
theorem B1947827 : Blo 766334 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B768183 : Blo 766334 768183 := bstep (se 1 (by rfl) ⟨576137, by rfl⟩ : syracuseStep 768183 = 1152275) B1152275
theorem B768203 : Blo 766334 768203 := bstep (se 1 (by rfl) ⟨576152, by rfl⟩ : syracuseStep 768203 = 1152305) B1152305
theorem B768215 : Blo 766334 768215 := bstep (se 1 (by rfl) ⟨576161, by rfl⟩ : syracuseStep 768215 = 1152323) B1152323
theorem B768235 : Blo 766334 768235 := bstep (se 1 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 768235 = 1152353) B1152353
theorem B768247 : Blo 766334 768247 := bstep (se 1 (by rfl) ⟨576185, by rfl⟩ : syracuseStep 768247 = 1152371) B1152371
theorem B866551 : Blo 766334 866551 := bstep (se 1 (by rfl) ⟨649913, by rfl⟩ : syracuseStep 866551 = 1299827) B1299827
theorem B768267 : Blo 766334 768267 := bstep (se 1 (by rfl) ⟨576200, by rfl⟩ : syracuseStep 768267 = 1152401) B1152401
theorem B768279 : Blo 766334 768279 := bstep (se 1 (by rfl) ⟨576209, by rfl⟩ : syracuseStep 768279 = 1152419) B1152419
theorem B768299 : Blo 766334 768299 := bstep (se 1 (by rfl) ⟨576224, by rfl⟩ : syracuseStep 768299 = 1152449) B1152449
theorem B768311 : Blo 766334 768311 := bstep (se 1 (by rfl) ⟨576233, by rfl⟩ : syracuseStep 768311 = 1152467) B1152467
theorem B768331 : Blo 766334 768331 := bstep (se 1 (by rfl) ⟨576248, by rfl⟩ : syracuseStep 768331 = 1152497) B1152497
theorem B768343 : Blo 766334 768343 := bstep (se 1 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 768343 = 1152515) B1152515
theorem B7027037 : Blo 766334 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B768363 : Blo 766334 768363 := bstep (se 1 (by rfl) ⟨576272, by rfl⟩ : syracuseStep 768363 = 1152545) B1152545
theorem B768375 : Blo 766334 768375 := bstep (se 1 (by rfl) ⟨576281, by rfl⟩ : syracuseStep 768375 = 1152563) B1152563
theorem B1554817 : Blo 766334 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B768395 : Blo 766334 768395 := bstep (se 1 (by rfl) ⟨576296, by rfl⟩ : syracuseStep 768395 = 1152593) B1152593
theorem B1456535 : Blo 766334 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B768407 : Blo 766334 768407 := bstep (se 1 (by rfl) ⟨576305, by rfl⟩ : syracuseStep 768407 = 1152611) B1152611
theorem B768427 : Blo 766334 768427 := bstep (se 1 (by rfl) ⟨576320, by rfl⟩ : syracuseStep 768427 = 1152641) B1152641
theorem B768439 : Blo 766334 768439 := bstep (se 1 (by rfl) ⟨576329, by rfl⟩ : syracuseStep 768439 = 1152659) B1152659
theorem B768459 : Blo 766334 768459 := bstep (se 1 (by rfl) ⟨576344, by rfl⟩ : syracuseStep 768459 = 1152689) B1152689
theorem B768471 : Blo 766334 768471 := bstep (se 1 (by rfl) ⟨576353, by rfl⟩ : syracuseStep 768471 = 1152707) B1152707
theorem B1948121 : Blo 766334 1948121 := bstep (se 2 (by rfl) ⟨730545, by rfl⟩ : syracuseStep 1948121 = 1461091) B1461091
theorem B768491 : Blo 766334 768491 := bstep (se 1 (by rfl) ⟨576368, by rfl⟩ : syracuseStep 768491 = 1152737) B1152737
theorem B768503 : Blo 766334 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B768523 : Blo 766334 768523 := bstep (se 1 (by rfl) ⟨576392, by rfl⟩ : syracuseStep 768523 = 1152785) B1152785
theorem B5552657 : Blo 766334 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B768535 : Blo 766334 768535 := bstep (se 1 (by rfl) ⟨576401, by rfl⟩ : syracuseStep 768535 = 1152803) B1152803
theorem B768555 : Blo 766334 768555 := bstep (se 1 (by rfl) ⟨576416, by rfl⟩ : syracuseStep 768555 = 1152833) B1152833
theorem B2767405 : Blo 766334 2767405 := bstep (se 3 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 2767405 = 1037777) B1037777
theorem B768567 : Blo 766334 768567 := bstep (se 1 (by rfl) ⟨576425, by rfl⟩ : syracuseStep 768567 = 1152851) B1152851
theorem B768587 : Blo 766334 768587 := bstep (se 1 (by rfl) ⟨576440, by rfl⟩ : syracuseStep 768587 = 1152881) B1152881
theorem B768599 : Blo 766334 768599 := bstep (se 1 (by rfl) ⟨576449, by rfl⟩ : syracuseStep 768599 = 1152899) B1152899
theorem B2341469 : Blo 766334 2341469 := bstep (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) B878051
theorem B768619 : Blo 766334 768619 := bstep (se 1 (by rfl) ⟨576464, by rfl⟩ : syracuseStep 768619 = 1152929) B1152929
theorem B768631 : Blo 766334 768631 := bstep (se 1 (by rfl) ⟨576473, by rfl⟩ : syracuseStep 768631 = 1152947) B1152947
theorem B768651 : Blo 766334 768651 := bstep (se 1 (by rfl) ⟨576488, by rfl⟩ : syracuseStep 768651 = 1152977) B1152977
theorem B768663 : Blo 766334 768663 := bstep (se 1 (by rfl) ⟨576497, by rfl⟩ : syracuseStep 768663 = 1152995) B1152995
theorem B768683 : Blo 766334 768683 := bstep (se 1 (by rfl) ⟨576512, by rfl⟩ : syracuseStep 768683 = 1153025) B1153025
theorem B768695 : Blo 766334 768695 := bstep (se 1 (by rfl) ⟨576521, by rfl⟩ : syracuseStep 768695 = 1153043) B1153043
theorem B768715 : Blo 766334 768715 := bstep (se 1 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 768715 = 1153073) B1153073
theorem B768727 : Blo 766334 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B768747 : Blo 766334 768747 := bstep (se 1 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 768747 = 1153121) B1153121
theorem B768759 : Blo 766334 768759 := bstep (se 1 (by rfl) ⟨576569, by rfl⟩ : syracuseStep 768759 = 1153139) B1153139
theorem B768779 : Blo 766334 768779 := bstep (se 1 (by rfl) ⟨576584, by rfl⟩ : syracuseStep 768779 = 1153169) B1153169
theorem B768791 : Blo 766334 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B2341655 : Blo 766334 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B768811 : Blo 766334 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B2964275 : Blo 766334 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B768823 : Blo 766334 768823 := bstep (se 1 (by rfl) ⟨576617, by rfl⟩ : syracuseStep 768823 = 1153235) B1153235
theorem B768843 : Blo 766334 768843 := bstep (se 1 (by rfl) ⟨576632, by rfl⟩ : syracuseStep 768843 = 1153265) B1153265
theorem B768855 : Blo 766334 768855 := bstep (se 1 (by rfl) ⟨576641, by rfl⟩ : syracuseStep 768855 = 1153283) B1153283
theorem B768875 : Blo 766334 768875 := bstep (se 1 (by rfl) ⟨576656, by rfl⟩ : syracuseStep 768875 = 1153313) B1153313
theorem B768887 : Blo 766334 768887 := bstep (se 1 (by rfl) ⟨576665, by rfl⟩ : syracuseStep 768887 = 1153331) B1153331
theorem B768907 : Blo 766334 768907 := bstep (se 1 (by rfl) ⟨576680, by rfl⟩ : syracuseStep 768907 = 1153361) B1153361
theorem B768919 : Blo 766334 768919 := bstep (se 1 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 768919 = 1153379) B1153379
theorem B768939 : Blo 766334 768939 := bstep (se 1 (by rfl) ⟨576704, by rfl⟩ : syracuseStep 768939 = 1153409) B1153409
theorem B2341811 : Blo 766334 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B768951 : Blo 766334 768951 := bstep (se 1 (by rfl) ⟨576713, by rfl⟩ : syracuseStep 768951 = 1153427) B1153427
theorem B1293259 : Blo 766334 1293259 := bstep (se 1 (by rfl) ⟨969944, by rfl⟩ : syracuseStep 1293259 = 1939889) B1939889
theorem B768971 : Blo 766334 768971 := bstep (se 1 (by rfl) ⟨576728, by rfl⟩ : syracuseStep 768971 = 1153457) B1153457
theorem B768983 : Blo 766334 768983 := bstep (se 1 (by rfl) ⟨576737, by rfl⟩ : syracuseStep 768983 = 1153475) B1153475
theorem B769003 : Blo 766334 769003 := bstep (se 1 (by rfl) ⟨576752, by rfl⟩ : syracuseStep 769003 = 1153505) B1153505
theorem B769015 : Blo 766334 769015 := bstep (se 1 (by rfl) ⟨576761, by rfl⟩ : syracuseStep 769015 = 1153523) B1153523
theorem B1555457 : Blo 766334 1555457 := bstep (se 2 (by rfl) ⟨583296, by rfl⟩ : syracuseStep 1555457 = 1166593) B1166593
theorem B769035 : Blo 766334 769035 := bstep (se 1 (by rfl) ⟨576776, by rfl⟩ : syracuseStep 769035 = 1153553) B1153553
theorem B769047 : Blo 766334 769047 := bstep (se 1 (by rfl) ⟨576785, by rfl⟩ : syracuseStep 769047 = 1153571) B1153571
theorem B769067 : Blo 766334 769067 := bstep (se 1 (by rfl) ⟨576800, by rfl⟩ : syracuseStep 769067 = 1153601) B1153601
theorem B1457203 : Blo 766334 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B769079 : Blo 766334 769079 := bstep (se 1 (by rfl) ⟨576809, by rfl⟩ : syracuseStep 769079 = 1153619) B1153619
theorem B769099 : Blo 766334 769099 := bstep (se 1 (by rfl) ⟨576824, by rfl⟩ : syracuseStep 769099 = 1153649) B1153649
theorem B769111 : Blo 766334 769111 := bstep (se 1 (by rfl) ⟨576833, by rfl⟩ : syracuseStep 769111 = 1153667) B1153667
theorem B1293401 : Blo 766334 1293401 := bstep (se 2 (by rfl) ⟨485025, by rfl⟩ : syracuseStep 1293401 = 970051) B970051
theorem B769131 : Blo 766334 769131 := bstep (se 1 (by rfl) ⟨576848, by rfl⟩ : syracuseStep 769131 = 1153697) B1153697
theorem B769143 : Blo 766334 769143 := bstep (se 1 (by rfl) ⟨576857, by rfl⟩ : syracuseStep 769143 = 1153715) B1153715
theorem B4373635 : Blo 766334 4373635 := bstep (se 1 (by rfl) ⟨3280226, by rfl⟩ : syracuseStep 4373635 = 6560453) B6560453
theorem B769163 : Blo 766334 769163 := bstep (se 1 (by rfl) ⟨576872, by rfl⟩ : syracuseStep 769163 = 1153745) B1153745
theorem B769175 : Blo 766334 769175 := bstep (se 1 (by rfl) ⟨576881, by rfl⟩ : syracuseStep 769175 = 1153763) B1153763
theorem B769195 : Blo 766334 769195 := bstep (se 1 (by rfl) ⟨576896, by rfl⟩ : syracuseStep 769195 = 1153793) B1153793
theorem B769207 : Blo 766334 769207 := bstep (se 1 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 769207 = 1153811) B1153811
theorem B769227 : Blo 766334 769227 := bstep (se 1 (by rfl) ⟨576920, by rfl⟩ : syracuseStep 769227 = 1153841) B1153841
theorem B769239 : Blo 766334 769239 := bstep (se 1 (by rfl) ⟨576929, by rfl⟩ : syracuseStep 769239 = 1153859) B1153859
theorem B1293529 : Blo 766334 1293529 := bstep (se 2 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 1293529 = 970147) B970147
theorem B769259 : Blo 766334 769259 := bstep (se 1 (by rfl) ⟨576944, by rfl⟩ : syracuseStep 769259 = 1153889) B1153889
theorem B769271 : Blo 766334 769271 := bstep (se 1 (by rfl) ⟨576953, by rfl⟩ : syracuseStep 769271 = 1153907) B1153907
theorem B769291 : Blo 766334 769291 := bstep (se 1 (by rfl) ⟨576968, by rfl⟩ : syracuseStep 769291 = 1153937) B1153937
theorem B769303 : Blo 766334 769303 := bstep (se 1 (by rfl) ⟨576977, by rfl⟩ : syracuseStep 769303 = 1153955) B1153955
theorem B769323 : Blo 766334 769323 := bstep (se 1 (by rfl) ⟨576992, by rfl⟩ : syracuseStep 769323 = 1153985) B1153985
theorem B769335 : Blo 766334 769335 := bstep (se 1 (by rfl) ⟨577001, by rfl⟩ : syracuseStep 769335 = 1154003) B1154003
theorem B769355 : Blo 766334 769355 := bstep (se 1 (by rfl) ⟨577016, by rfl⟩ : syracuseStep 769355 = 1154033) B1154033
theorem B769367 : Blo 766334 769367 := bstep (se 1 (by rfl) ⟨577025, by rfl⟩ : syracuseStep 769367 = 1154051) B1154051
theorem B769387 : Blo 766334 769387 := bstep (se 1 (by rfl) ⟨577040, by rfl⟩ : syracuseStep 769387 = 1154081) B1154081
theorem B769399 : Blo 766334 769399 := bstep (se 1 (by rfl) ⟨577049, by rfl⟩ : syracuseStep 769399 = 1154099) B1154099
theorem B769419 : Blo 766334 769419 := bstep (se 1 (by rfl) ⟨577064, by rfl⟩ : syracuseStep 769419 = 1154129) B1154129
theorem B769431 : Blo 766334 769431 := bstep (se 1 (by rfl) ⟨577073, by rfl⟩ : syracuseStep 769431 = 1154147) B1154147
theorem B769451 : Blo 766334 769451 := bstep (se 1 (by rfl) ⟨577088, by rfl⟩ : syracuseStep 769451 = 1154177) B1154177
theorem B769463 : Blo 766334 769463 := bstep (se 1 (by rfl) ⟨577097, by rfl⟩ : syracuseStep 769463 = 1154195) B1154195
theorem B769483 : Blo 766334 769483 := bstep (se 1 (by rfl) ⟨577112, by rfl⟩ : syracuseStep 769483 = 1154225) B1154225
theorem B769495 : Blo 766334 769495 := bstep (se 1 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 769495 = 1154243) B1154243
theorem B769515 : Blo 766334 769515 := bstep (se 1 (by rfl) ⟨577136, by rfl⟩ : syracuseStep 769515 = 1154273) B1154273
theorem B1457651 : Blo 766334 1457651 := bstep (se 1 (by rfl) ⟨1093238, by rfl⟩ : syracuseStep 1457651 = 2186477) B2186477
theorem B769527 : Blo 766334 769527 := bstep (se 1 (by rfl) ⟨577145, by rfl⟩ : syracuseStep 769527 = 1154291) B1154291
theorem B769547 : Blo 766334 769547 := bstep (se 1 (by rfl) ⟨577160, by rfl⟩ : syracuseStep 769547 = 1154321) B1154321
theorem B769559 : Blo 766334 769559 := bstep (se 1 (by rfl) ⟨577169, by rfl⟩ : syracuseStep 769559 = 1154339) B1154339
theorem B1457689 : Blo 766334 1457689 := bstep (se 2 (by rfl) ⟨546633, by rfl⟩ : syracuseStep 1457689 = 1093267) B1093267
theorem B769579 : Blo 766334 769579 := bstep (se 1 (by rfl) ⟨577184, by rfl⟩ : syracuseStep 769579 = 1154369) B1154369
theorem B769591 : Blo 766334 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B769611 : Blo 766334 769611 := bstep (se 1 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 769611 = 1154417) B1154417
theorem B769623 : Blo 766334 769623 := bstep (se 1 (by rfl) ⟨577217, by rfl⟩ : syracuseStep 769623 = 1154435) B1154435
theorem B769643 : Blo 766334 769643 := bstep (se 1 (by rfl) ⟨577232, by rfl⟩ : syracuseStep 769643 = 1154465) B1154465
theorem B769655 : Blo 766334 769655 := bstep (se 1 (by rfl) ⟨577241, by rfl⟩ : syracuseStep 769655 = 1154483) B1154483
theorem B769675 : Blo 766334 769675 := bstep (se 1 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 769675 = 1154513) B1154513
theorem B769687 : Blo 766334 769687 := bstep (se 1 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 769687 = 1154531) B1154531
theorem B769707 : Blo 766334 769707 := bstep (se 1 (by rfl) ⟨577280, by rfl⟩ : syracuseStep 769707 = 1154561) B1154561
theorem B769719 : Blo 766334 769719 := bstep (se 1 (by rfl) ⟨577289, by rfl⟩ : syracuseStep 769719 = 1154579) B1154579
theorem B769739 : Blo 766334 769739 := bstep (se 1 (by rfl) ⟨577304, by rfl⟩ : syracuseStep 769739 = 1154609) B1154609
theorem B769751 : Blo 766334 769751 := bstep (se 1 (by rfl) ⟨577313, by rfl⟩ : syracuseStep 769751 = 1154627) B1154627
theorem B769771 : Blo 766334 769771 := bstep (se 1 (by rfl) ⟨577328, by rfl⟩ : syracuseStep 769771 = 1154657) B1154657
theorem B769783 : Blo 766334 769783 := bstep (se 1 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 769783 = 1154675) B1154675
theorem B769803 : Blo 766334 769803 := bstep (se 1 (by rfl) ⟨577352, by rfl⟩ : syracuseStep 769803 = 1154705) B1154705
theorem B1294103 : Blo 766334 1294103 := bstep (se 1 (by rfl) ⟨970577, by rfl⟩ : syracuseStep 1294103 = 1941155) B1941155
theorem B769815 : Blo 766334 769815 := bstep (se 1 (by rfl) ⟨577361, by rfl⟩ : syracuseStep 769815 = 1154723) B1154723
theorem B769835 : Blo 766334 769835 := bstep (se 1 (by rfl) ⟨577376, by rfl⟩ : syracuseStep 769835 = 1154753) B1154753
theorem B769847 : Blo 766334 769847 := bstep (se 1 (by rfl) ⟨577385, by rfl⟩ : syracuseStep 769847 = 1154771) B1154771
theorem B769867 : Blo 766334 769867 := bstep (se 1 (by rfl) ⟨577400, by rfl⟩ : syracuseStep 769867 = 1154801) B1154801
theorem B769879 : Blo 766334 769879 := bstep (se 1 (by rfl) ⟨577409, by rfl⟩ : syracuseStep 769879 = 1154819) B1154819
theorem B769899 : Blo 766334 769899 := bstep (se 1 (by rfl) ⟨577424, by rfl⟩ : syracuseStep 769899 = 1154849) B1154849
theorem B769911 : Blo 766334 769911 := bstep (se 1 (by rfl) ⟨577433, by rfl⟩ : syracuseStep 769911 = 1154867) B1154867
theorem B769931 : Blo 766334 769931 := bstep (se 1 (by rfl) ⟨577448, by rfl⟩ : syracuseStep 769931 = 1154897) B1154897
theorem B1294231 : Blo 766334 1294231 := bstep (se 1 (by rfl) ⟨970673, by rfl⟩ : syracuseStep 1294231 = 1941347) B1941347
theorem B769943 : Blo 766334 769943 := bstep (se 1 (by rfl) ⟨577457, by rfl⟩ : syracuseStep 769943 = 1154915) B1154915
theorem B769963 : Blo 766334 769963 := bstep (se 1 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 769963 = 1154945) B1154945
theorem B5849009 : Blo 766334 5849009 := bstep (se 2 (by rfl) ⟨2193378, by rfl⟩ : syracuseStep 5849009 = 4386757) B4386757
theorem B769975 : Blo 766334 769975 := bstep (se 1 (by rfl) ⟨577481, by rfl⟩ : syracuseStep 769975 = 1154963) B1154963
theorem B2768833 : Blo 766334 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B769995 : Blo 766334 769995 := bstep (se 1 (by rfl) ⟨577496, by rfl⟩ : syracuseStep 769995 = 1154993) B1154993
theorem B770007 : Blo 766334 770007 := bstep (se 1 (by rfl) ⟨577505, by rfl⟩ : syracuseStep 770007 = 1155011) B1155011
theorem B1458137 : Blo 766334 1458137 := bstep (se 2 (by rfl) ⟨546801, by rfl⟩ : syracuseStep 1458137 = 1093603) B1093603
theorem B770027 : Blo 766334 770027 := bstep (se 1 (by rfl) ⟨577520, by rfl⟩ : syracuseStep 770027 = 1155041) B1155041
theorem B770039 : Blo 766334 770039 := bstep (se 1 (by rfl) ⟨577529, by rfl⟩ : syracuseStep 770039 = 1155059) B1155059
theorem B770059 : Blo 766334 770059 := bstep (se 1 (by rfl) ⟨577544, by rfl⟩ : syracuseStep 770059 = 1155089) B1155089
theorem B770071 : Blo 766334 770071 := bstep (se 1 (by rfl) ⟨577553, by rfl⟩ : syracuseStep 770071 = 1155107) B1155107
theorem B770091 : Blo 766334 770091 := bstep (se 1 (by rfl) ⟨577568, by rfl⟩ : syracuseStep 770091 = 1155137) B1155137
theorem B770103 : Blo 766334 770103 := bstep (se 1 (by rfl) ⟨577577, by rfl⟩ : syracuseStep 770103 = 1155155) B1155155
theorem B4374593 : Blo 766334 4374593 := bstep (se 2 (by rfl) ⟨1640472, by rfl⟩ : syracuseStep 4374593 = 3280945) B3280945
theorem B770123 : Blo 766334 770123 := bstep (se 1 (by rfl) ⟨577592, by rfl⟩ : syracuseStep 770123 = 1155185) B1155185
theorem B1949771 : Blo 766334 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B770135 : Blo 766334 770135 := bstep (se 1 (by rfl) ⟨577601, by rfl⟩ : syracuseStep 770135 = 1155203) B1155203
theorem B770155 : Blo 766334 770155 := bstep (se 1 (by rfl) ⟨577616, by rfl⟩ : syracuseStep 770155 = 1155233) B1155233
theorem B770167 : Blo 766334 770167 := bstep (se 1 (by rfl) ⟨577625, by rfl⟩ : syracuseStep 770167 = 1155251) B1155251
theorem B3883139 : Blo 766334 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B770187 : Blo 766334 770187 := bstep (se 1 (by rfl) ⟨577640, by rfl⟩ : syracuseStep 770187 = 1155281) B1155281
theorem B770199 : Blo 766334 770199 := bstep (se 1 (by rfl) ⟨577649, by rfl⟩ : syracuseStep 770199 = 1155299) B1155299
theorem B770219 : Blo 766334 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B770231 : Blo 766334 770231 := bstep (se 1 (by rfl) ⟨577673, by rfl⟩ : syracuseStep 770231 = 1155347) B1155347
theorem B2080961 : Blo 766334 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B770251 : Blo 766334 770251 := bstep (se 1 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 770251 = 1155377) B1155377
theorem B770263 : Blo 766334 770263 := bstep (se 1 (by rfl) ⟨577697, by rfl⟩ : syracuseStep 770263 = 1155395) B1155395
theorem B770283 : Blo 766334 770283 := bstep (se 1 (by rfl) ⟨577712, by rfl⟩ : syracuseStep 770283 = 1155425) B1155425
theorem B770295 : Blo 766334 770295 := bstep (se 1 (by rfl) ⟨577721, by rfl⟩ : syracuseStep 770295 = 1155443) B1155443
theorem B770315 : Blo 766334 770315 := bstep (se 1 (by rfl) ⟨577736, by rfl⟩ : syracuseStep 770315 = 1155473) B1155473
theorem B770327 : Blo 766334 770327 := bstep (se 1 (by rfl) ⟨577745, by rfl⟩ : syracuseStep 770327 = 1155491) B1155491
theorem B5849495 : Blo 766334 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B1294859 : Blo 766334 1294859 := bstep (se 1 (by rfl) ⟨971144, by rfl⟩ : syracuseStep 1294859 = 1942289) B1942289
theorem B1294987 : Blo 766334 1294987 := bstep (se 1 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 1294987 = 1942481) B1942481
theorem B1458881 : Blo 766334 1458881 := bstep (se 2 (by rfl) ⟨547080, by rfl⟩ : syracuseStep 1458881 = 1094161) B1094161
theorem B1295129 : Blo 766334 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B1557299 : Blo 766334 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B1295257 : Blo 766334 1295257 := bstep (se 2 (by rfl) ⟨485721, by rfl⟩ : syracuseStep 1295257 = 971443) B971443
theorem B1459147 : Blo 766334 1459147 := bstep (se 1 (by rfl) ⟨1094360, by rfl⟩ : syracuseStep 1459147 = 2188721) B2188721
theorem B2802653 : Blo 766334 2802653 := bstep (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) B1050995
theorem B1459595 : Blo 766334 1459595 := bstep (se 1 (by rfl) ⟨1094696, by rfl⟩ : syracuseStep 1459595 = 2189393) B2189393
theorem B1230233 : Blo 766334 1230233 := bstep (se 2 (by rfl) ⟨461337, by rfl⟩ : syracuseStep 1230233 = 922675) B922675
theorem B1623449 : Blo 766334 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B1754561 : Blo 766334 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1295831 : Blo 766334 1295831 := bstep (se 1 (by rfl) ⟨971873, by rfl⟩ : syracuseStep 1295831 = 1943747) B1943747
theorem B3556867 : Blo 766334 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1459777 : Blo 766334 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B1295959 : Blo 766334 1295959 := bstep (se 1 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 1295959 = 1943939) B1943939
theorem B5916377 : Blo 766334 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B1460119 : Blo 766334 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B4671553 : Blo 766334 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B4442177 : Blo 766334 4442177 := bstep (se 2 (by rfl) ⟨1665816, by rfl⟩ : syracuseStep 4442177 = 3331633) B3331633
theorem B1460339 : Blo 766334 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B1296587 : Blo 766334 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B1296715 : Blo 766334 1296715 := bstep (se 1 (by rfl) ⟨972536, by rfl⟩ : syracuseStep 1296715 = 1945073) B1945073
theorem B1460567 : Blo 766334 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B1165771 : Blo 766334 1165771 := bstep (se 1 (by rfl) ⟨874328, by rfl⟩ : syracuseStep 1165771 = 1748657) B1748657
theorem B1296857 : Blo 766334 1296857 := bstep (se 2 (by rfl) ⟨486321, by rfl⟩ : syracuseStep 1296857 = 972643) B972643
theorem B1559027 : Blo 766334 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B1296985 : Blo 766334 1296985 := bstep (se 2 (by rfl) ⟨486369, by rfl⟩ : syracuseStep 1296985 = 972739) B972739
theorem B1460825 : Blo 766334 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B3787415 : Blo 766334 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B20007665 : Blo 766334 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B2771729 : Blo 766334 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B4934465 : Blo 766334 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B9849701 : Blo 766334 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B1461235 : Blo 766334 1461235 := bstep (se 1 (by rfl) ⟨1095926, by rfl⟩ : syracuseStep 1461235 = 2191853) B2191853
theorem B1297559 : Blo 766334 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B1756313 : Blo 766334 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B15191221 : Blo 766334 15191221 := bstep (se 5 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 15191221 = 1424177) B1424177
theorem B969995 : Blo 766334 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B1297687 : Blo 766334 1297687 := bstep (se 1 (by rfl) ⟨973265, by rfl⟩ : syracuseStep 1297687 = 1946531) B1946531
theorem B2805137 : Blo 766334 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B1756631 : Blo 766334 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B1461721 : Blo 766334 1461721 := bstep (se 2 (by rfl) ⟨548145, by rfl⟩ : syracuseStep 1461721 = 1096291) B1096291
theorem B3886865 : Blo 766334 3886865 := bstep (se 2 (by rfl) ⟨1457574, by rfl⟩ : syracuseStep 3886865 = 2915149) B2915149
theorem B1560395 : Blo 766334 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1298315 : Blo 766334 1298315 := bstep (se 1 (by rfl) ⟨973736, by rfl⟩ : syracuseStep 1298315 = 1947473) B1947473
theorem B3887027 : Blo 766334 3887027 := bstep (se 1 (by rfl) ⟨2915270, by rfl⟩ : syracuseStep 3887027 = 5830541) B5830541
theorem B2183105 : Blo 766334 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1724363 : Blo 766334 1724363 := bstep (se 1 (by rfl) ⟨1293272, by rfl⟩ : syracuseStep 1724363 = 2586545) B2586545
theorem B970699 : Blo 766334 970699 := bstep (se 1 (by rfl) ⟨728024, by rfl⟩ : syracuseStep 970699 = 1456049) B1456049
theorem B1724417 : Blo 766334 1724417 := bstep (se 2 (by rfl) ⟨646656, by rfl⟩ : syracuseStep 1724417 = 1293313) B1293313
theorem B1298443 : Blo 766334 1298443 := bstep (se 1 (by rfl) ⟨973832, by rfl⟩ : syracuseStep 1298443 = 1947665) B1947665
theorem B1462283 : Blo 766334 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B12439565 : Blo 766334 12439565 := bstep (se 3 (by rfl) ⟨2332418, by rfl⟩ : syracuseStep 12439565 = 4664837) B4664837
theorem B2183219 : Blo 766334 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B1298585 : Blo 766334 1298585 := bstep (se 2 (by rfl) ⟨486969, by rfl⟩ : syracuseStep 1298585 = 973939) B973939
theorem B970967 : Blo 766334 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B1724633 : Blo 766334 1724633 := bstep (se 2 (by rfl) ⟨646737, by rfl⟩ : syracuseStep 1724633 = 1293475) B1293475
theorem B1298713 : Blo 766334 1298713 := bstep (se 2 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 1298713 = 974035) B974035
theorem B1724723 : Blo 766334 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1724759 : Blo 766334 1724759 := bstep (se 1 (by rfl) ⟨1293569, by rfl⟩ : syracuseStep 1724759 = 2587139) B2587139
theorem B1724939 : Blo 766334 1724939 := bstep (se 1 (by rfl) ⟨1293704, by rfl⟩ : syracuseStep 1724939 = 2587409) B2587409
theorem B1724993 : Blo 766334 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B11096837 : Blo 766334 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B1725209 : Blo 766334 1725209 := bstep (se 2 (by rfl) ⟨646953, by rfl⟩ : syracuseStep 1725209 = 1293907) B1293907
theorem B1561369 : Blo 766334 1561369 := bstep (se 2 (by rfl) ⟨585513, by rfl⟩ : syracuseStep 1561369 = 1171027) B1171027
theorem B2773835 : Blo 766334 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B4379467 : Blo 766334 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B1299287 : Blo 766334 1299287 := bstep (se 1 (by rfl) ⟨974465, by rfl⟩ : syracuseStep 1299287 = 1948931) B1948931
theorem B1725299 : Blo 766334 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B1725335 : Blo 766334 1725335 := bstep (se 1 (by rfl) ⟨1294001, by rfl⟩ : syracuseStep 1725335 = 2588003) B2588003
theorem B971671 : Blo 766334 971671 := bstep (se 1 (by rfl) ⟨728753, by rfl⟩ : syracuseStep 971671 = 1457507) B1457507
theorem B1299415 : Blo 766334 1299415 := bstep (se 1 (by rfl) ⟨974561, by rfl⟩ : syracuseStep 1299415 = 1949123) B1949123
theorem B1037323 : Blo 766334 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B3691565 : Blo 766334 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B1725515 : Blo 766334 1725515 := bstep (se 1 (by rfl) ⟨1294136, by rfl⟩ : syracuseStep 1725515 = 2588273) B2588273
theorem B4379741 : Blo 766334 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1725569 : Blo 766334 1725569 := bstep (se 2 (by rfl) ⟨647088, by rfl⟩ : syracuseStep 1725569 = 1294177) B1294177
theorem B3691793 : Blo 766334 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B1037593 : Blo 766334 1037593 := bstep (se 2 (by rfl) ⟨389097, by rfl⟩ : syracuseStep 1037593 = 778195) B778195
theorem B1725785 : Blo 766334 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B1725875 : Blo 766334 1725875 := bstep (se 1 (by rfl) ⟨1294406, by rfl⟩ : syracuseStep 1725875 = 2588813) B2588813
theorem B1725911 : Blo 766334 1725911 := bstep (se 1 (by rfl) ⟨1294433, by rfl⟩ : syracuseStep 1725911 = 2588867) B2588867
theorem B14177753 : Blo 766334 14177753 := bstep (se 2 (by rfl) ⟨5316657, by rfl⟩ : syracuseStep 14177753 = 10633315) B10633315
theorem B4806245 : Blo 766334 4806245 := bstep (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) B901171
theorem B1726091 : Blo 766334 1726091 := bstep (se 1 (by rfl) ⟨1294568, by rfl⟩ : syracuseStep 1726091 = 2589137) B2589137
theorem B1726145 : Blo 766334 1726145 := bstep (se 2 (by rfl) ⟨647304, by rfl⟩ : syracuseStep 1726145 = 1294609) B1294609
theorem B9852677 : Blo 766334 9852677 := bstep (se 4 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 9852677 = 1847377) B1847377
theorem B3888971 : Blo 766334 3888971 := bstep (se 1 (by rfl) ⟨2916728, by rfl⟩ : syracuseStep 3888971 = 5833457) B5833457
theorem B1726361 : Blo 766334 1726361 := bstep (se 2 (by rfl) ⟨647385, by rfl⟩ : syracuseStep 1726361 = 1294771) B1294771
theorem B1726451 : Blo 766334 1726451 := bstep (se 1 (by rfl) ⟨1294838, by rfl⟩ : syracuseStep 1726451 = 2589677) B2589677
theorem B1726487 : Blo 766334 1726487 := bstep (se 1 (by rfl) ⟨1294865, by rfl⟩ : syracuseStep 1726487 = 2589731) B2589731
theorem B6576173 : Blo 766334 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B1726667 : Blo 766334 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1726721 : Blo 766334 1726721 := bstep (se 2 (by rfl) ⟨647520, by rfl⟩ : syracuseStep 1726721 = 1295041) B1295041
theorem B5822765 : Blo 766334 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B8739251 : Blo 766334 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B1726937 : Blo 766334 1726937 := bstep (se 2 (by rfl) ⟨647601, by rfl⟩ : syracuseStep 1726937 = 1295203) B1295203
theorem B1727027 : Blo 766334 1727027 := bstep (se 1 (by rfl) ⟨1295270, by rfl⟩ : syracuseStep 1727027 = 2590541) B2590541
theorem B973387 : Blo 766334 973387 := bstep (se 1 (by rfl) ⟨730040, by rfl⟩ : syracuseStep 973387 = 1460081) B1460081
theorem B1727063 : Blo 766334 1727063 := bstep (se 1 (by rfl) ⟨1295297, by rfl⟩ : syracuseStep 1727063 = 2590595) B2590595
theorem B1727243 : Blo 766334 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B1727297 : Blo 766334 1727297 := bstep (se 2 (by rfl) ⟨647736, by rfl⟩ : syracuseStep 1727297 = 1295473) B1295473
theorem B2186135 : Blo 766334 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B1727513 : Blo 766334 1727513 := bstep (se 2 (by rfl) ⟨647817, by rfl⟩ : syracuseStep 1727513 = 1295635) B1295635
theorem B1727603 : Blo 766334 1727603 := bstep (se 1 (by rfl) ⟨1295702, by rfl⟩ : syracuseStep 1727603 = 2591405) B2591405
theorem B1727639 : Blo 766334 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B1727819 : Blo 766334 1727819 := bstep (se 1 (by rfl) ⟨1295864, by rfl⟩ : syracuseStep 1727819 = 2591729) B2591729
theorem B3333469 : Blo 766334 3333469 := bstep (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) B1250051
theorem B1727873 : Blo 766334 1727873 := bstep (se 2 (by rfl) ⟨647952, by rfl⟩ : syracuseStep 1727873 = 1295905) B1295905
theorem B974359 : Blo 766334 974359 := bstep (se 1 (by rfl) ⟨730769, by rfl⟩ : syracuseStep 974359 = 1461539) B1461539
theorem B3890753 : Blo 766334 3890753 := bstep (se 2 (by rfl) ⟨1459032, by rfl⟩ : syracuseStep 3890753 = 2918065) B2918065
theorem B1728089 : Blo 766334 1728089 := bstep (se 2 (by rfl) ⟨648033, by rfl⟩ : syracuseStep 1728089 = 1296067) B1296067
theorem B1728179 : Blo 766334 1728179 := bstep (se 1 (by rfl) ⟨1296134, by rfl⟩ : syracuseStep 1728179 = 2592269) B2592269
theorem B1728215 : Blo 766334 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B876299 : Blo 766334 876299 := bstep (se 1 (by rfl) ⟨657224, by rfl⟩ : syracuseStep 876299 = 1314449) B1314449
theorem B8740709 : Blo 766334 8740709 := bstep (se 4 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 8740709 = 1638883) B1638883
theorem B1728395 : Blo 766334 1728395 := bstep (se 1 (by rfl) ⟨1296296, by rfl⟩ : syracuseStep 1728395 = 2592593) B2592593
theorem B1728449 : Blo 766334 1728449 := bstep (se 2 (by rfl) ⟨648168, by rfl⟩ : syracuseStep 1728449 = 1296337) B1296337
theorem B5529617 : Blo 766334 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B1400857 : Blo 766334 1400857 := bstep (se 2 (by rfl) ⟨525321, by rfl⟩ : syracuseStep 1400857 = 1050643) B1050643
theorem B1728665 : Blo 766334 1728665 := bstep (se 2 (by rfl) ⟨648249, by rfl⟩ : syracuseStep 1728665 = 1296499) B1296499
theorem B1728755 : Blo 766334 1728755 := bstep (se 1 (by rfl) ⟨1296566, by rfl⟩ : syracuseStep 1728755 = 2593133) B2593133
theorem B1728791 : Blo 766334 1728791 := bstep (se 1 (by rfl) ⟨1296593, by rfl⟩ : syracuseStep 1728791 = 2593187) B2593187
theorem B1728971 : Blo 766334 1728971 := bstep (se 1 (by rfl) ⟨1296728, by rfl⟩ : syracuseStep 1728971 = 2593457) B2593457
theorem B1729025 : Blo 766334 1729025 := bstep (se 2 (by rfl) ⟨648384, by rfl⟩ : syracuseStep 1729025 = 1296769) B1296769
theorem B11067997 : Blo 766334 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B1729241 : Blo 766334 1729241 := bstep (se 2 (by rfl) ⟨648465, by rfl⟩ : syracuseStep 1729241 = 1296931) B1296931
theorem B1729331 : Blo 766334 1729331 := bstep (se 1 (by rfl) ⟨1296998, by rfl⟩ : syracuseStep 1729331 = 2593997) B2593997
theorem B1729367 : Blo 766334 1729367 := bstep (se 1 (by rfl) ⟨1297025, by rfl⟩ : syracuseStep 1729367 = 2594051) B2594051
theorem B1729547 : Blo 766334 1729547 := bstep (se 1 (by rfl) ⟨1297160, by rfl⟩ : syracuseStep 1729547 = 2594321) B2594321
theorem B49832981 : Blo 766334 49832981 := bstep (se 6 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 49832981 = 2335921) B2335921
theorem B1729601 : Blo 766334 1729601 := bstep (se 2 (by rfl) ⟨648600, by rfl⟩ : syracuseStep 1729601 = 1297201) B1297201
theorem B1729817 : Blo 766334 1729817 := bstep (se 2 (by rfl) ⟨648681, by rfl⟩ : syracuseStep 1729817 = 1297363) B1297363
theorem B2188595 : Blo 766334 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B1729907 : Blo 766334 1729907 := bstep (se 1 (by rfl) ⟨1297430, by rfl⟩ : syracuseStep 1729907 = 2594861) B2594861
theorem B1729943 : Blo 766334 1729943 := bstep (se 1 (by rfl) ⟨1297457, by rfl⟩ : syracuseStep 1729943 = 2594915) B2594915
theorem B3696023 : Blo 766334 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B3892697 : Blo 766334 3892697 := bstep (se 2 (by rfl) ⟨1459761, by rfl⟩ : syracuseStep 3892697 = 2919523) B2919523
theorem B1730123 : Blo 766334 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B2909789 : Blo 766334 2909789 := bstep (se 3 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 2909789 = 1091171) B1091171
theorem B1730177 : Blo 766334 1730177 := bstep (se 2 (by rfl) ⟨648816, by rfl⟩ : syracuseStep 1730177 = 1297633) B1297633
theorem B6579863 : Blo 766334 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B1730393 : Blo 766334 1730393 := bstep (se 2 (by rfl) ⟨648897, by rfl⟩ : syracuseStep 1730393 = 1297795) B1297795
theorem B6547331 : Blo 766334 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B1730483 : Blo 766334 1730483 := bstep (se 1 (by rfl) ⟨1297862, by rfl⟩ : syracuseStep 1730483 = 2595725) B2595725
theorem B1730519 : Blo 766334 1730519 := bstep (se 1 (by rfl) ⟨1297889, by rfl⟩ : syracuseStep 1730519 = 2595779) B2595779
theorem B1402903 : Blo 766334 1402903 := bstep (se 1 (by rfl) ⟨1052177, by rfl⟩ : syracuseStep 1402903 = 2104355) B2104355
theorem B5826653 : Blo 766334 5826653 := bstep (se 3 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 5826653 = 2184995) B2184995
theorem B2779267 : Blo 766334 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B1730699 : Blo 766334 1730699 := bstep (se 1 (by rfl) ⟨1298024, by rfl⟩ : syracuseStep 1730699 = 2596049) B2596049
theorem B1730753 : Blo 766334 1730753 := bstep (se 2 (by rfl) ⟨649032, by rfl⟩ : syracuseStep 1730753 = 1298065) B1298065
theorem B4385117 : Blo 766334 4385117 := bstep (se 3 (by rfl) ⟨822209, by rfl⟩ : syracuseStep 4385117 = 1644419) B1644419
theorem B4155779 : Blo 766334 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B1730969 : Blo 766334 1730969 := bstep (se 2 (by rfl) ⟨649113, by rfl⟩ : syracuseStep 1730969 = 1298227) B1298227
theorem B1731059 : Blo 766334 1731059 := bstep (se 1 (by rfl) ⟨1298294, by rfl⟩ : syracuseStep 1731059 = 2596589) B2596589
theorem B1731095 : Blo 766334 1731095 := bstep (se 1 (by rfl) ⟨1298321, by rfl⟩ : syracuseStep 1731095 = 2596643) B2596643
theorem B1731275 : Blo 766334 1731275 := bstep (se 1 (by rfl) ⟨1298456, by rfl⟩ : syracuseStep 1731275 = 2596913) B2596913
theorem B1731329 : Blo 766334 1731329 := bstep (se 2 (by rfl) ⟨649248, by rfl⟩ : syracuseStep 1731329 = 1298497) B1298497
theorem B3697483 : Blo 766334 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1731545 : Blo 766334 1731545 := bstep (se 2 (by rfl) ⟨649329, by rfl⟩ : syracuseStep 1731545 = 1298659) B1298659
theorem B3894317 : Blo 766334 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B1731635 : Blo 766334 1731635 := bstep (se 1 (by rfl) ⟨1298726, by rfl⟩ : syracuseStep 1731635 = 2597453) B2597453
theorem B1731671 : Blo 766334 1731671 := bstep (se 1 (by rfl) ⟨1298753, by rfl⟩ : syracuseStep 1731671 = 2597507) B2597507
theorem B3108061 : Blo 766334 3108061 := bstep (se 3 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 3108061 = 1165523) B1165523
theorem B205090019 : Blo 766334 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B1731851 : Blo 766334 1731851 := bstep (se 1 (by rfl) ⟨1298888, by rfl⟩ : syracuseStep 1731851 = 2597777) B2597777
theorem B1731905 : Blo 766334 1731905 := bstep (se 2 (by rfl) ⟨649464, by rfl⟩ : syracuseStep 1731905 = 1298929) B1298929
theorem B3698099 : Blo 766334 3698099 := bstep (se 1 (by rfl) ⟨2773574, by rfl⟩ : syracuseStep 3698099 = 5547149) B5547149
theorem B2911747 : Blo 766334 2911747 := bstep (se 1 (by rfl) ⟨2183810, by rfl⟩ : syracuseStep 2911747 = 4367621) B4367621
theorem B7368209 : Blo 766334 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B1732121 : Blo 766334 1732121 := bstep (se 2 (by rfl) ⟨649545, by rfl⟩ : syracuseStep 1732121 = 1299091) B1299091
theorem B1732211 : Blo 766334 1732211 := bstep (se 1 (by rfl) ⟨1299158, by rfl⟩ : syracuseStep 1732211 = 2598317) B2598317
theorem B1732247 : Blo 766334 1732247 := bstep (se 1 (by rfl) ⟨1299185, by rfl⟩ : syracuseStep 1732247 = 2598371) B2598371
theorem B2912051 : Blo 766334 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B1732427 : Blo 766334 1732427 := bstep (se 1 (by rfl) ⟨1299320, by rfl⟩ : syracuseStep 1732427 = 2598641) B2598641
theorem B1732481 : Blo 766334 1732481 := bstep (se 2 (by rfl) ⟨649680, by rfl⟩ : syracuseStep 1732481 = 1299361) B1299361
theorem B2191283 : Blo 766334 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B21032921 : Blo 766334 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B1732697 : Blo 766334 1732697 := bstep (se 2 (by rfl) ⟨649761, by rfl⟩ : syracuseStep 1732697 = 1299523) B1299523
theorem B2191511 : Blo 766334 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B3698867 : Blo 766334 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B1732787 : Blo 766334 1732787 := bstep (se 1 (by rfl) ⟨1299590, by rfl⟩ : syracuseStep 1732787 = 2599181) B2599181
theorem B1732823 : Blo 766334 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B24899885 : Blo 766334 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B1733003 : Blo 766334 1733003 := bstep (se 1 (by rfl) ⟨1299752, by rfl⟩ : syracuseStep 1733003 = 2599505) B2599505
theorem B2912705 : Blo 766334 2912705 := bstep (se 2 (by rfl) ⟨1092264, by rfl⟩ : syracuseStep 2912705 = 2184529) B2184529
theorem B1733057 : Blo 766334 1733057 := bstep (se 2 (by rfl) ⟨649896, by rfl⟩ : syracuseStep 1733057 = 1299793) B1299793
theorem B2191819 : Blo 766334 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B2192093 : Blo 766334 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B6550307 : Blo 766334 6550307 := bstep (se 1 (by rfl) ⟨4912730, by rfl⟩ : syracuseStep 6550307 = 9825461) B9825461
theorem B3273803 : Blo 766334 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B2913965 : Blo 766334 2913965 := bstep (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) B1092737
theorem B2913995 : Blo 766334 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B3799057 : Blo 766334 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B3274931 : Blo 766334 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B4913369 : Blo 766334 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B2914649 : Blo 766334 2914649 := bstep (se 2 (by rfl) ⟨1092993, by rfl⟩ : syracuseStep 2914649 = 2185987) B2185987
theorem B2587031 : Blo 766334 2587031 := bstep (se 1 (by rfl) ⟨1940273, by rfl⟩ : syracuseStep 2587031 = 3880547) B3880547
theorem B2914967 : Blo 766334 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B1637209 : Blo 766334 1637209 := bstep (se 2 (by rfl) ⟨613953, by rfl⟩ : syracuseStep 1637209 = 1227907) B1227907
theorem B3898205 : Blo 766334 3898205 := bstep (se 3 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 3898205 = 1461827) B1461827
theorem B2587571 : Blo 766334 2587571 := bstep (se 1 (by rfl) ⟨1940678, by rfl⟩ : syracuseStep 2587571 = 3881357) B3881357
theorem B2587841 : Blo 766334 2587841 := bstep (se 2 (by rfl) ⟨970440, by rfl⟩ : syracuseStep 2587841 = 1940881) B1940881
theorem B1244441 : Blo 766334 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B2915635 : Blo 766334 2915635 := bstep (se 1 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 2915635 = 4373453) B4373453
theorem B818519 : Blo 766334 818519 := bstep (se 1 (by rfl) ⟨613889, by rfl⟩ : syracuseStep 818519 = 1227779) B1227779
theorem B2588381 : Blo 766334 2588381 := bstep (se 3 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 2588381 = 970643) B970643
theorem B4915009 : Blo 766334 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B819083 : Blo 766334 819083 := bstep (se 1 (by rfl) ⟨614312, by rfl⟩ : syracuseStep 819083 = 1228625) B1228625
theorem B2916395 : Blo 766334 2916395 := bstep (se 1 (by rfl) ⟨2187296, by rfl⟩ : syracuseStep 2916395 = 4374593) B4374593
theorem B2588759 : Blo 766334 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B7471237 : Blo 766334 7471237 := bstep (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) B1400857
theorem B3899663 : Blo 766334 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B8749457 : Blo 766334 8749457 := bstep (se 2 (by rfl) ⟨3281046, by rfl⟩ : syracuseStep 8749457 = 6562093) B6562093
theorem B3932675 : Blo 766334 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B2589245 : Blo 766334 2589245 := bstep (se 3 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 2589245 = 970967) B970967
theorem B1868435 : Blo 766334 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B1082299 : Blo 766334 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B1967507 : Blo 766334 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B4916855 : Blo 766334 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B6555329 : Blo 766334 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B2524943 : Blo 766334 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B13338443 : Blo 766334 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B1312697 : Blo 766334 1312697 := bstep (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) B984523
theorem B2590649 : Blo 766334 2590649 := bstep (se 2 (by rfl) ⟨971493, by rfl⟩ : syracuseStep 2590649 = 1942987) B1942987
theorem B985223 : Blo 766334 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B1870091 : Blo 766334 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B2591243 : Blo 766334 2591243 := bstep (se 1 (by rfl) ⟨1943432, by rfl⟩ : syracuseStep 2591243 = 3886865) B3886865
theorem B2591351 : Blo 766334 2591351 := bstep (se 1 (by rfl) ⟨1943513, by rfl⟩ : syracuseStep 2591351 = 3887027) B3887027
theorem B1149575 : Blo 766334 1149575 := bstep (se 1 (by rfl) ⟨862181, by rfl⟩ : syracuseStep 1149575 = 1724363) B1724363
theorem B1149611 : Blo 766334 1149611 := bstep (se 1 (by rfl) ⟨862208, by rfl⟩ : syracuseStep 1149611 = 1724417) B1724417
theorem B8293043 : Blo 766334 8293043 := bstep (se 1 (by rfl) ⟨6219782, by rfl⟩ : syracuseStep 8293043 = 12439565) B12439565
theorem B1149641 : Blo 766334 1149641 := bstep (se 2 (by rfl) ⟨431115, by rfl⟩ : syracuseStep 1149641 = 862231) B862231
theorem B6228737 : Blo 766334 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B1149755 : Blo 766334 1149755 := bstep (se 1 (by rfl) ⟨862316, by rfl⟩ : syracuseStep 1149755 = 1724633) B1724633
theorem B3705689 : Blo 766334 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B1149815 : Blo 766334 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B1149839 : Blo 766334 1149839 := bstep (se 1 (by rfl) ⟨862379, by rfl⟩ : syracuseStep 1149839 = 1724759) B1724759
theorem B1149881 : Blo 766334 1149881 := bstep (se 2 (by rfl) ⟨431205, by rfl⟩ : syracuseStep 1149881 = 862411) B862411
theorem B1149959 : Blo 766334 1149959 := bstep (se 1 (by rfl) ⟨862469, by rfl⟩ : syracuseStep 1149959 = 1724939) B1724939
theorem B1149995 : Blo 766334 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B1969211 : Blo 766334 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1150025 : Blo 766334 1150025 := bstep (se 2 (by rfl) ⟨431259, by rfl⟩ : syracuseStep 1150025 = 862519) B862519
theorem B1150139 : Blo 766334 1150139 := bstep (se 1 (by rfl) ⟨862604, by rfl⟩ : syracuseStep 1150139 = 1725209) B1725209
theorem B2591945 : Blo 766334 2591945 := bstep (se 2 (by rfl) ⟨971979, by rfl⟩ : syracuseStep 2591945 = 1943959) B1943959
theorem B8752373 : Blo 766334 8752373 := bstep (se 5 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 8752373 = 820535) B820535
theorem B1150199 : Blo 766334 1150199 := bstep (se 1 (by rfl) ⟨862649, by rfl⟩ : syracuseStep 1150199 = 1725299) B1725299
theorem B1150223 : Blo 766334 1150223 := bstep (se 1 (by rfl) ⟨862667, by rfl⟩ : syracuseStep 1150223 = 1725335) B1725335
theorem B1150265 : Blo 766334 1150265 := bstep (se 2 (by rfl) ⟨431349, by rfl⟩ : syracuseStep 1150265 = 862699) B862699
theorem B2461043 : Blo 766334 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B1150343 : Blo 766334 1150343 := bstep (se 1 (by rfl) ⟨862757, by rfl⟩ : syracuseStep 1150343 = 1725515) B1725515
theorem B2919827 : Blo 766334 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B1150379 : Blo 766334 1150379 := bstep (se 1 (by rfl) ⟨862784, by rfl⟩ : syracuseStep 1150379 = 1725569) B1725569
theorem B1150409 : Blo 766334 1150409 := bstep (se 2 (by rfl) ⟨431403, by rfl⟩ : syracuseStep 1150409 = 862807) B862807
theorem B2461195 : Blo 766334 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B1642027 : Blo 766334 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1150523 : Blo 766334 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B1150583 : Blo 766334 1150583 := bstep (se 1 (by rfl) ⟨862937, by rfl⟩ : syracuseStep 1150583 = 1725875) B1725875
theorem B4001399 : Blo 766334 4001399 := bstep (se 1 (by rfl) ⟨3001049, by rfl⟩ : syracuseStep 4001399 = 6002099) B6002099
theorem B1150607 : Blo 766334 1150607 := bstep (se 1 (by rfl) ⟨862955, by rfl⟩ : syracuseStep 1150607 = 1725911) B1725911
theorem B1150649 : Blo 766334 1150649 := bstep (se 2 (by rfl) ⟨431493, by rfl⟩ : syracuseStep 1150649 = 862987) B862987
theorem B3280621 : Blo 766334 3280621 := bstep (se 3 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 3280621 = 1230233) B1230233
theorem B1150727 : Blo 766334 1150727 := bstep (se 1 (by rfl) ⟨863045, by rfl⟩ : syracuseStep 1150727 = 1726091) B1726091
theorem B1150763 : Blo 766334 1150763 := bstep (se 1 (by rfl) ⟨863072, by rfl⟩ : syracuseStep 1150763 = 1726145) B1726145
theorem B1150793 : Blo 766334 1150793 := bstep (se 2 (by rfl) ⟨431547, by rfl⟩ : syracuseStep 1150793 = 863095) B863095
theorem B2592647 : Blo 766334 2592647 := bstep (se 1 (by rfl) ⟨1944485, by rfl⟩ : syracuseStep 2592647 = 3888971) B3888971
theorem B1150907 : Blo 766334 1150907 := bstep (se 1 (by rfl) ⟨863180, by rfl⟩ : syracuseStep 1150907 = 1726361) B1726361
theorem B1150967 : Blo 766334 1150967 := bstep (se 1 (by rfl) ⟨863225, by rfl⟩ : syracuseStep 1150967 = 1726451) B1726451
theorem B1150991 : Blo 766334 1150991 := bstep (se 1 (by rfl) ⟨863243, by rfl⟩ : syracuseStep 1150991 = 1726487) B1726487
theorem B6557719 : Blo 766334 6557719 := bstep (se 1 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 6557719 = 9836579) B9836579
theorem B1151033 : Blo 766334 1151033 := bstep (se 2 (by rfl) ⟨431637, by rfl⟩ : syracuseStep 1151033 = 863275) B863275
theorem B1151111 : Blo 766334 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B1151147 : Blo 766334 1151147 := bstep (se 1 (by rfl) ⟨863360, by rfl⟩ : syracuseStep 1151147 = 1726721) B1726721
theorem B1151177 : Blo 766334 1151177 := bstep (se 2 (by rfl) ⟨431691, by rfl⟩ : syracuseStep 1151177 = 863383) B863383
theorem B20254961 : Blo 766334 20254961 := bstep (se 2 (by rfl) ⟨7595610, by rfl⟩ : syracuseStep 20254961 = 15191221) B15191221
theorem B2593025 : Blo 766334 2593025 := bstep (se 2 (by rfl) ⟨972384, by rfl⟩ : syracuseStep 2593025 = 1944769) B1944769
theorem B1577249 : Blo 766334 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1151291 : Blo 766334 1151291 := bstep (se 1 (by rfl) ⟨863468, by rfl⟩ : syracuseStep 1151291 = 1726937) B1726937
theorem B1151351 : Blo 766334 1151351 := bstep (se 1 (by rfl) ⟨863513, by rfl⟩ : syracuseStep 1151351 = 1727027) B1727027
theorem B1151375 : Blo 766334 1151375 := bstep (se 1 (by rfl) ⟨863531, by rfl⟩ : syracuseStep 1151375 = 1727063) B1727063
theorem B1151417 : Blo 766334 1151417 := bstep (se 2 (by rfl) ⟨431781, by rfl⟩ : syracuseStep 1151417 = 863563) B863563
theorem B1151495 : Blo 766334 1151495 := bstep (se 1 (by rfl) ⟨863621, by rfl⟩ : syracuseStep 1151495 = 1727243) B1727243
theorem B1151531 : Blo 766334 1151531 := bstep (se 1 (by rfl) ⟨863648, by rfl⟩ : syracuseStep 1151531 = 1727297) B1727297
theorem B1151561 : Blo 766334 1151561 := bstep (se 2 (by rfl) ⟨431835, by rfl⟩ : syracuseStep 1151561 = 863671) B863671
theorem B1151675 : Blo 766334 1151675 := bstep (se 1 (by rfl) ⟨863756, by rfl⟩ : syracuseStep 1151675 = 1727513) B1727513
theorem B1151735 : Blo 766334 1151735 := bstep (se 1 (by rfl) ⟨863801, by rfl⟩ : syracuseStep 1151735 = 1727603) B1727603
theorem B1151759 : Blo 766334 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B1151801 : Blo 766334 1151801 := bstep (se 2 (by rfl) ⟨431925, by rfl⟩ : syracuseStep 1151801 = 863851) B863851
theorem B922487 : Blo 766334 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1315703 : Blo 766334 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1151879 : Blo 766334 1151879 := bstep (se 1 (by rfl) ⟨863909, by rfl⟩ : syracuseStep 1151879 = 1727819) B1727819
theorem B1151915 : Blo 766334 1151915 := bstep (se 1 (by rfl) ⟨863936, by rfl⟩ : syracuseStep 1151915 = 1727873) B1727873
theorem B1151945 : Blo 766334 1151945 := bstep (se 2 (by rfl) ⟨431979, by rfl⟩ : syracuseStep 1151945 = 863959) B863959
theorem B2593835 : Blo 766334 2593835 := bstep (se 1 (by rfl) ⟨1945376, by rfl⟩ : syracuseStep 2593835 = 3890753) B3890753
theorem B1152059 : Blo 766334 1152059 := bstep (se 1 (by rfl) ⟨864044, by rfl⟩ : syracuseStep 1152059 = 1728089) B1728089
theorem B1152119 : Blo 766334 1152119 := bstep (se 1 (by rfl) ⟨864089, by rfl⟩ : syracuseStep 1152119 = 1728179) B1728179
theorem B1152143 : Blo 766334 1152143 := bstep (se 1 (by rfl) ⟨864107, by rfl⟩ : syracuseStep 1152143 = 1728215) B1728215
theorem B1152185 : Blo 766334 1152185 := bstep (se 2 (by rfl) ⟨432069, by rfl⟩ : syracuseStep 1152185 = 864139) B864139
theorem B1152263 : Blo 766334 1152263 := bstep (se 1 (by rfl) ⟨864197, by rfl⟩ : syracuseStep 1152263 = 1728395) B1728395
theorem B1152299 : Blo 766334 1152299 := bstep (se 1 (by rfl) ⟨864224, by rfl⟩ : syracuseStep 1152299 = 1728449) B1728449
theorem B1152329 : Blo 766334 1152329 := bstep (se 2 (by rfl) ⟨432123, by rfl⟩ : syracuseStep 1152329 = 864247) B864247
theorem B1152443 : Blo 766334 1152443 := bstep (se 1 (by rfl) ⟨864332, by rfl⟩ : syracuseStep 1152443 = 1728665) B1728665
theorem B1152503 : Blo 766334 1152503 := bstep (se 1 (by rfl) ⟨864377, by rfl⟩ : syracuseStep 1152503 = 1728755) B1728755
theorem B1152527 : Blo 766334 1152527 := bstep (se 1 (by rfl) ⟨864395, by rfl⟩ : syracuseStep 1152527 = 1728791) B1728791
theorem B1152569 : Blo 766334 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B3282551 : Blo 766334 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B1152647 : Blo 766334 1152647 := bstep (se 1 (by rfl) ⟨864485, by rfl⟩ : syracuseStep 1152647 = 1728971) B1728971
theorem B1152683 : Blo 766334 1152683 := bstep (se 1 (by rfl) ⟨864512, by rfl⟩ : syracuseStep 1152683 = 1729025) B1729025
theorem B1152713 : Blo 766334 1152713 := bstep (se 2 (by rfl) ⟨432267, by rfl⟩ : syracuseStep 1152713 = 864535) B864535
theorem B1152827 : Blo 766334 1152827 := bstep (se 1 (by rfl) ⟨864620, by rfl⟩ : syracuseStep 1152827 = 1729241) B1729241
theorem B1152887 : Blo 766334 1152887 := bstep (se 1 (by rfl) ⟨864665, by rfl⟩ : syracuseStep 1152887 = 1729331) B1729331
theorem B1152911 : Blo 766334 1152911 := bstep (se 1 (by rfl) ⟨864683, by rfl⟩ : syracuseStep 1152911 = 1729367) B1729367
theorem B1152953 : Blo 766334 1152953 := bstep (se 2 (by rfl) ⟨432357, by rfl⟩ : syracuseStep 1152953 = 864715) B864715
theorem B2922425 : Blo 766334 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B1153031 : Blo 766334 1153031 := bstep (se 1 (by rfl) ⟨864773, by rfl⟩ : syracuseStep 1153031 = 1729547) B1729547
theorem B1153067 : Blo 766334 1153067 := bstep (se 1 (by rfl) ⟨864800, by rfl⟩ : syracuseStep 1153067 = 1729601) B1729601
theorem B1153097 : Blo 766334 1153097 := bstep (se 2 (by rfl) ⟨432411, by rfl⟩ : syracuseStep 1153097 = 864823) B864823
theorem B1153211 : Blo 766334 1153211 := bstep (se 1 (by rfl) ⟨864908, by rfl⟩ : syracuseStep 1153211 = 1729817) B1729817
theorem B1153271 : Blo 766334 1153271 := bstep (se 1 (by rfl) ⟨864953, by rfl⟩ : syracuseStep 1153271 = 1729907) B1729907
theorem B1153295 : Blo 766334 1153295 := bstep (se 1 (by rfl) ⟨864971, by rfl⟩ : syracuseStep 1153295 = 1729943) B1729943
theorem B2464015 : Blo 766334 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B1153337 : Blo 766334 1153337 := bstep (se 2 (by rfl) ⟨432501, by rfl⟩ : syracuseStep 1153337 = 865003) B865003
theorem B2595131 : Blo 766334 2595131 := bstep (se 1 (by rfl) ⟨1946348, by rfl⟩ : syracuseStep 2595131 = 3892697) B3892697
theorem B1153415 : Blo 766334 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B1939859 : Blo 766334 1939859 := bstep (se 1 (by rfl) ⟨1454894, by rfl⟩ : syracuseStep 1939859 = 2909789) B2909789
theorem B1153451 : Blo 766334 1153451 := bstep (se 1 (by rfl) ⟨865088, by rfl⟩ : syracuseStep 1153451 = 1730177) B1730177
theorem B5839289 : Blo 766334 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B1153481 : Blo 766334 1153481 := bstep (se 2 (by rfl) ⟨432555, by rfl⟩ : syracuseStep 1153481 = 865111) B865111
theorem B1841707 : Blo 766334 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B1153595 : Blo 766334 1153595 := bstep (se 1 (by rfl) ⟨865196, by rfl⟩ : syracuseStep 1153595 = 1730393) B1730393
theorem B4364887 : Blo 766334 4364887 := bstep (se 1 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 4364887 = 6547331) B6547331
theorem B1153655 : Blo 766334 1153655 := bstep (se 1 (by rfl) ⟨865241, by rfl⟩ : syracuseStep 1153655 = 1730483) B1730483
theorem B1153679 : Blo 766334 1153679 := bstep (se 1 (by rfl) ⟨865259, by rfl⟩ : syracuseStep 1153679 = 1730519) B1730519
theorem B1383097 : Blo 766334 1383097 := bstep (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) B1037323
theorem B1153721 : Blo 766334 1153721 := bstep (se 2 (by rfl) ⟨432645, by rfl⟩ : syracuseStep 1153721 = 865291) B865291
theorem B1153799 : Blo 766334 1153799 := bstep (se 1 (by rfl) ⟨865349, by rfl⟩ : syracuseStep 1153799 = 1730699) B1730699
theorem B2595617 : Blo 766334 2595617 := bstep (se 2 (by rfl) ⟨973356, by rfl⟩ : syracuseStep 2595617 = 1946713) B1946713
theorem B1153835 : Blo 766334 1153835 := bstep (se 1 (by rfl) ⟨865376, by rfl⟩ : syracuseStep 1153835 = 1730753) B1730753
theorem B1383227 : Blo 766334 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B1153865 : Blo 766334 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B2923411 : Blo 766334 2923411 := bstep (se 1 (by rfl) ⟨2192558, by rfl⟩ : syracuseStep 2923411 = 4385117) B4385117
theorem B1153979 : Blo 766334 1153979 := bstep (se 1 (by rfl) ⟨865484, by rfl⟩ : syracuseStep 1153979 = 1730969) B1730969
theorem B2104265 : Blo 766334 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B1154039 : Blo 766334 1154039 := bstep (se 1 (by rfl) ⟨865529, by rfl⟩ : syracuseStep 1154039 = 1731059) B1731059
theorem B1154063 : Blo 766334 1154063 := bstep (se 1 (by rfl) ⟨865547, by rfl⟩ : syracuseStep 1154063 = 1731095) B1731095
theorem B1154105 : Blo 766334 1154105 := bstep (se 2 (by rfl) ⟨432789, by rfl⟩ : syracuseStep 1154105 = 865579) B865579
theorem B15735869 : Blo 766334 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B1154183 : Blo 766334 1154183 := bstep (se 1 (by rfl) ⟨865637, by rfl⟩ : syracuseStep 1154183 = 1731275) B1731275
theorem B1154219 : Blo 766334 1154219 := bstep (se 1 (by rfl) ⟨865664, by rfl⟩ : syracuseStep 1154219 = 1731329) B1731329
theorem B1154249 : Blo 766334 1154249 := bstep (se 2 (by rfl) ⟨432843, by rfl⟩ : syracuseStep 1154249 = 865687) B865687
theorem B1154363 : Blo 766334 1154363 := bstep (se 1 (by rfl) ⟨865772, by rfl⟩ : syracuseStep 1154363 = 1731545) B1731545
theorem B2596211 : Blo 766334 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1154423 : Blo 766334 1154423 := bstep (se 1 (by rfl) ⟨865817, by rfl⟩ : syracuseStep 1154423 = 1731635) B1731635
theorem B1154447 : Blo 766334 1154447 := bstep (se 1 (by rfl) ⟨865835, by rfl⟩ : syracuseStep 1154447 = 1731671) B1731671
theorem B1154489 : Blo 766334 1154489 := bstep (se 2 (by rfl) ⟨432933, by rfl⟩ : syracuseStep 1154489 = 865867) B865867
theorem B1940993 : Blo 766334 1940993 := bstep (se 2 (by rfl) ⟨727872, by rfl⟩ : syracuseStep 1940993 = 1455745) B1455745
theorem B1154567 : Blo 766334 1154567 := bstep (se 1 (by rfl) ⟨865925, by rfl⟩ : syracuseStep 1154567 = 1731851) B1731851
theorem B1154603 : Blo 766334 1154603 := bstep (se 1 (by rfl) ⟨865952, by rfl⟩ : syracuseStep 1154603 = 1731905) B1731905
theorem B1154633 : Blo 766334 1154633 := bstep (se 2 (by rfl) ⟨432987, by rfl⟩ : syracuseStep 1154633 = 865975) B865975
theorem B2465399 : Blo 766334 2465399 := bstep (se 1 (by rfl) ⟨1849049, by rfl⟩ : syracuseStep 2465399 = 3698099) B3698099
theorem B1154747 : Blo 766334 1154747 := bstep (se 1 (by rfl) ⟨866060, by rfl⟩ : syracuseStep 1154747 = 1732121) B1732121
theorem B1154807 : Blo 766334 1154807 := bstep (se 1 (by rfl) ⟨866105, by rfl⟩ : syracuseStep 1154807 = 1732211) B1732211
theorem B1154831 : Blo 766334 1154831 := bstep (se 1 (by rfl) ⟨866123, by rfl⟩ : syracuseStep 1154831 = 1732247) B1732247
theorem B1154873 : Blo 766334 1154873 := bstep (se 2 (by rfl) ⟨433077, by rfl⟩ : syracuseStep 1154873 = 866155) B866155
theorem B5250905 : Blo 766334 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B1941367 : Blo 766334 1941367 := bstep (se 1 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 1941367 = 2912051) B2912051
theorem B1154951 : Blo 766334 1154951 := bstep (se 1 (by rfl) ⟨866213, by rfl⟩ : syracuseStep 1154951 = 1732427) B1732427
theorem B1843091 : Blo 766334 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1154987 : Blo 766334 1154987 := bstep (se 1 (by rfl) ⟨866240, by rfl⟩ : syracuseStep 1154987 = 1732481) B1732481
theorem B1155017 : Blo 766334 1155017 := bstep (se 2 (by rfl) ⟨433131, by rfl⟩ : syracuseStep 1155017 = 866263) B866263
theorem B1155131 : Blo 766334 1155131 := bstep (se 1 (by rfl) ⟨866348, by rfl⟩ : syracuseStep 1155131 = 1732697) B1732697
theorem B2629693 : Blo 766334 2629693 := bstep (se 3 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 2629693 = 986135) B986135
theorem B2465911 : Blo 766334 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B1155191 : Blo 766334 1155191 := bstep (se 1 (by rfl) ⟨866393, by rfl⟩ : syracuseStep 1155191 = 1732787) B1732787
theorem B1155215 : Blo 766334 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B1155257 : Blo 766334 1155257 := bstep (se 2 (by rfl) ⟨433221, by rfl⟩ : syracuseStep 1155257 = 866443) B866443
theorem B1155335 : Blo 766334 1155335 := bstep (se 1 (by rfl) ⟨866501, by rfl⟩ : syracuseStep 1155335 = 1733003) B1733003
theorem B1974539 : Blo 766334 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B1941803 : Blo 766334 1941803 := bstep (se 1 (by rfl) ⟨1456352, by rfl⟩ : syracuseStep 1941803 = 2912705) B2912705
theorem B1155371 : Blo 766334 1155371 := bstep (se 1 (by rfl) ⟨866528, by rfl⟩ : syracuseStep 1155371 = 1733057) B1733057
theorem B1155401 : Blo 766334 1155401 := bstep (se 2 (by rfl) ⟨433275, by rfl⟩ : syracuseStep 1155401 = 866551) B866551
theorem B2073089 : Blo 766334 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B4366871 : Blo 766334 4366871 := bstep (se 1 (by rfl) ⟨3275153, by rfl⟩ : syracuseStep 4366871 = 6550307) B6550307
theorem B3318509 : Blo 766334 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1942643 : Blo 766334 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B1942663 : Blo 766334 1942663 := bstep (se 1 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 1942663 = 2913995) B2913995
theorem B1844513 : Blo 766334 1844513 := bstep (se 2 (by rfl) ⟨691692, by rfl⟩ : syracuseStep 1844513 = 1383385) B1383385
theorem B1942937 : Blo 766334 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1943099 : Blo 766334 1943099 := bstep (se 1 (by rfl) ⟨1457324, by rfl⟩ : syracuseStep 1943099 = 2914649) B2914649
theorem B1943311 : Blo 766334 1943311 := bstep (se 1 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 1943311 = 2914967) B2914967
theorem B1976183 : Blo 766334 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B2598803 : Blo 766334 2598803 := bstep (se 1 (by rfl) ⟨1949102, by rfl⟩ : syracuseStep 2598803 = 3898205) B3898205
theorem B3286993 : Blo 766334 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B16623629 : Blo 766334 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B2336797 : Blo 766334 2336797 := bstep (se 3 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 2336797 = 876299) B876299
theorem B1943585 : Blo 766334 1943585 := bstep (se 2 (by rfl) ⟨728844, by rfl⟩ : syracuseStep 1943585 = 1457689) B1457689
theorem B862267 : Blo 766334 862267 := bstep (se 1 (by rfl) ⟨646700, by rfl⟩ : syracuseStep 862267 = 1293401) B1293401
theorem B6564077 : Blo 766334 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B862735 : Blo 766334 862735 := bstep (se 1 (by rfl) ⟨647051, by rfl⟩ : syracuseStep 862735 = 1294103) B1294103
theorem B7482149 : Blo 766334 7482149 := bstep (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) B1402903
theorem B1387307 : Blo 766334 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B1846273 : Blo 766334 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B863239 : Blo 766334 863239 := bstep (se 1 (by rfl) ⟨647429, by rfl⟩ : syracuseStep 863239 = 1294859) B1294859
theorem B1944587 : Blo 766334 1944587 := bstep (se 1 (by rfl) ⟨1458440, by rfl⟩ : syracuseStep 1944587 = 2916881) B2916881
theorem B863419 : Blo 766334 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B2108825 : Blo 766334 2108825 := bstep (se 2 (by rfl) ⟨790809, by rfl⟩ : syracuseStep 2108825 = 1581619) B1581619
theorem B14757329 : Blo 766334 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B863887 : Blo 766334 863887 := bstep (se 1 (by rfl) ⟨647915, by rfl⟩ : syracuseStep 863887 = 1295831) B1295831
theorem B1945235 : Blo 766334 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B3944251 : Blo 766334 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B1093495 : Blo 766334 1093495 := bstep (se 1 (by rfl) ⟨820121, by rfl⟩ : syracuseStep 1093495 = 1640243) B1640243
theorem B1945529 : Blo 766334 1945529 := bstep (se 2 (by rfl) ⟨729573, by rfl⟩ : syracuseStep 1945529 = 1459147) B1459147
theorem B21016523 : Blo 766334 21016523 := bstep (se 1 (by rfl) ⟨15762392, by rfl⟩ : syracuseStep 21016523 = 31524785) B31524785
theorem B3944477 : Blo 766334 3944477 := bstep (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) B1479179
theorem B2961451 : Blo 766334 2961451 := bstep (se 1 (by rfl) ⟨2221088, by rfl⟩ : syracuseStep 2961451 = 4442177) B4442177
theorem B864391 : Blo 766334 864391 := bstep (se 1 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 864391 = 1296587) B1296587
theorem B1093819 : Blo 766334 1093819 := bstep (se 1 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 1093819 = 1640729) B1640729
theorem B864571 : Blo 766334 864571 := bstep (se 1 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 864571 = 1296857) B1296857
theorem B766343 : Blo 766334 766343 := bstep (se 1 (by rfl) ⟨574757, by rfl⟩ : syracuseStep 766343 = 1149515) B1149515
theorem B766351 : Blo 766334 766351 := bstep (se 1 (by rfl) ⟨574763, by rfl⟩ : syracuseStep 766351 = 1149527) B1149527
theorem B766395 : Blo 766334 766395 := bstep (se 1 (by rfl) ⟨574796, by rfl⟩ : syracuseStep 766395 = 1149593) B1149593
theorem B766471 : Blo 766334 766471 := bstep (se 1 (by rfl) ⟨574853, by rfl⟩ : syracuseStep 766471 = 1149707) B1149707
theorem B1847819 : Blo 766334 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B766479 : Blo 766334 766479 := bstep (se 1 (by rfl) ⟨574859, by rfl⟩ : syracuseStep 766479 = 1149719) B1149719
theorem B3289643 : Blo 766334 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B766523 : Blo 766334 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B6566467 : Blo 766334 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B1946227 : Blo 766334 1946227 := bstep (se 1 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 1946227 = 2919341) B2919341
theorem B766599 : Blo 766334 766599 := bstep (se 1 (by rfl) ⟨574949, by rfl⟩ : syracuseStep 766599 = 1149899) B1149899
theorem B766607 : Blo 766334 766607 := bstep (se 1 (by rfl) ⟨574955, by rfl⟩ : syracuseStep 766607 = 1149911) B1149911
theorem B3945133 : Blo 766334 3945133 := bstep (se 3 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 3945133 = 1479425) B1479425
theorem B766651 : Blo 766334 766651 := bstep (se 1 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 766651 = 1149977) B1149977
theorem B1946369 : Blo 766334 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B766727 : Blo 766334 766727 := bstep (se 1 (by rfl) ⟨575045, by rfl⟩ : syracuseStep 766727 = 1150091) B1150091
theorem B766735 : Blo 766334 766735 := bstep (se 1 (by rfl) ⟨575051, by rfl⟩ : syracuseStep 766735 = 1150103) B1150103
theorem B865039 : Blo 766334 865039 := bstep (se 1 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 865039 = 1297559) B1297559
theorem B766779 : Blo 766334 766779 := bstep (se 1 (by rfl) ⟨575084, by rfl⟩ : syracuseStep 766779 = 1150169) B1150169
theorem B766855 : Blo 766334 766855 := bstep (se 1 (by rfl) ⟨575141, by rfl⟩ : syracuseStep 766855 = 1150283) B1150283
theorem B766863 : Blo 766334 766863 := bstep (se 1 (by rfl) ⟨575147, by rfl⟩ : syracuseStep 766863 = 1150295) B1150295
theorem B766907 : Blo 766334 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B766983 : Blo 766334 766983 := bstep (se 1 (by rfl) ⟨575237, by rfl⟩ : syracuseStep 766983 = 1150475) B1150475
theorem B766991 : Blo 766334 766991 := bstep (se 1 (by rfl) ⟨575243, by rfl⟩ : syracuseStep 766991 = 1150487) B1150487
theorem B767035 : Blo 766334 767035 := bstep (se 1 (by rfl) ⟨575276, by rfl⟩ : syracuseStep 767035 = 1150553) B1150553
theorem B767111 : Blo 766334 767111 := bstep (se 1 (by rfl) ⟨575333, by rfl⟩ : syracuseStep 767111 = 1150667) B1150667
theorem B767119 : Blo 766334 767119 := bstep (se 1 (by rfl) ⟨575339, by rfl⟩ : syracuseStep 767119 = 1150679) B1150679
theorem B767163 : Blo 766334 767163 := bstep (se 1 (by rfl) ⟨575372, by rfl⟩ : syracuseStep 767163 = 1150745) B1150745
theorem B1946825 : Blo 766334 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B767239 : Blo 766334 767239 := bstep (se 1 (by rfl) ⟨575429, by rfl⟩ : syracuseStep 767239 = 1150859) B1150859
theorem B865543 : Blo 766334 865543 := bstep (se 1 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 865543 = 1298315) B1298315
theorem B767247 : Blo 766334 767247 := bstep (se 1 (by rfl) ⟨575435, by rfl⟩ : syracuseStep 767247 = 1150871) B1150871
theorem B1455403 : Blo 766334 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B767291 : Blo 766334 767291 := bstep (se 1 (by rfl) ⟨575468, by rfl⟩ : syracuseStep 767291 = 1150937) B1150937
theorem B1455479 : Blo 766334 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B767367 : Blo 766334 767367 := bstep (se 1 (by rfl) ⟨575525, by rfl⟩ : syracuseStep 767367 = 1151051) B1151051
theorem B767375 : Blo 766334 767375 := bstep (se 1 (by rfl) ⟨575531, by rfl⟩ : syracuseStep 767375 = 1151063) B1151063
theorem B2635193 : Blo 766334 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B767419 : Blo 766334 767419 := bstep (se 1 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 767419 = 1151129) B1151129
theorem B865723 : Blo 766334 865723 := bstep (se 1 (by rfl) ⟨649292, by rfl⟩ : syracuseStep 865723 = 1298585) B1298585
theorem B767495 : Blo 766334 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B767503 : Blo 766334 767503 := bstep (se 1 (by rfl) ⟨575627, by rfl⟩ : syracuseStep 767503 = 1151255) B1151255
theorem B1947179 : Blo 766334 1947179 := bstep (se 1 (by rfl) ⟨1460384, by rfl⟩ : syracuseStep 1947179 = 2920769) B2920769
theorem B767547 : Blo 766334 767547 := bstep (se 1 (by rfl) ⟨575660, by rfl⟩ : syracuseStep 767547 = 1151321) B1151321
theorem B767623 : Blo 766334 767623 := bstep (se 1 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 767623 = 1151435) B1151435
theorem B767631 : Blo 766334 767631 := bstep (se 1 (by rfl) ⟨575723, by rfl⟩ : syracuseStep 767631 = 1151447) B1151447
theorem B767675 : Blo 766334 767675 := bstep (se 1 (by rfl) ⟨575756, by rfl⟩ : syracuseStep 767675 = 1151513) B1151513
theorem B767751 : Blo 766334 767751 := bstep (se 1 (by rfl) ⟨575813, by rfl⟩ : syracuseStep 767751 = 1151627) B1151627
theorem B767759 : Blo 766334 767759 := bstep (se 1 (by rfl) ⟨575819, by rfl⟩ : syracuseStep 767759 = 1151639) B1151639
theorem B767803 : Blo 766334 767803 := bstep (se 1 (by rfl) ⟨575852, by rfl⟩ : syracuseStep 767803 = 1151705) B1151705
theorem B1849223 : Blo 766334 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B767879 : Blo 766334 767879 := bstep (se 1 (by rfl) ⟨575909, by rfl⟩ : syracuseStep 767879 = 1151819) B1151819
theorem B767887 : Blo 766334 767887 := bstep (se 1 (by rfl) ⟨575915, by rfl⟩ : syracuseStep 767887 = 1151831) B1151831
theorem B866191 : Blo 766334 866191 := bstep (se 1 (by rfl) ⟨649643, by rfl⟩ : syracuseStep 866191 = 1299287) B1299287
theorem B767931 : Blo 766334 767931 := bstep (se 1 (by rfl) ⟨575948, by rfl⟩ : syracuseStep 767931 = 1151897) B1151897
theorem B768007 : Blo 766334 768007 := bstep (se 1 (by rfl) ⟨576005, by rfl⟩ : syracuseStep 768007 = 1152011) B1152011
theorem B768015 : Blo 766334 768015 := bstep (se 1 (by rfl) ⟨576011, by rfl⟩ : syracuseStep 768015 = 1152023) B1152023
theorem B768059 : Blo 766334 768059 := bstep (se 1 (by rfl) ⟨576044, by rfl⟩ : syracuseStep 768059 = 1152089) B1152089
theorem B768135 : Blo 766334 768135 := bstep (se 1 (by rfl) ⟨576101, by rfl⟩ : syracuseStep 768135 = 1152203) B1152203
theorem B768143 : Blo 766334 768143 := bstep (se 1 (by rfl) ⟨576107, by rfl⟩ : syracuseStep 768143 = 1152215) B1152215
theorem B768187 : Blo 766334 768187 := bstep (se 1 (by rfl) ⟨576140, by rfl⟩ : syracuseStep 768187 = 1152281) B1152281
theorem B768263 : Blo 766334 768263 := bstep (se 1 (by rfl) ⟨576197, by rfl⟩ : syracuseStep 768263 = 1152395) B1152395
theorem B768271 : Blo 766334 768271 := bstep (se 1 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 768271 = 1152407) B1152407
theorem B9451835 : Blo 766334 9451835 := bstep (se 1 (by rfl) ⟨7088876, by rfl⟩ : syracuseStep 9451835 = 14177753) B14177753
theorem B768315 : Blo 766334 768315 := bstep (se 1 (by rfl) ⟨576236, by rfl⟩ : syracuseStep 768315 = 1152473) B1152473
theorem B768391 : Blo 766334 768391 := bstep (se 1 (by rfl) ⟨576293, by rfl⟩ : syracuseStep 768391 = 1152587) B1152587
theorem B768399 : Blo 766334 768399 := bstep (se 1 (by rfl) ⟨576299, by rfl⟩ : syracuseStep 768399 = 1152599) B1152599
theorem B3684761 : Blo 766334 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B4929977 : Blo 766334 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B768443 : Blo 766334 768443 := bstep (se 1 (by rfl) ⟨576332, by rfl⟩ : syracuseStep 768443 = 1152665) B1152665
theorem B1096183 : Blo 766334 1096183 := bstep (se 1 (by rfl) ⟨822137, by rfl⟩ : syracuseStep 1096183 = 1644275) B1644275
theorem B6568451 : Blo 766334 6568451 := bstep (se 1 (by rfl) ⟨4926338, by rfl⟩ : syracuseStep 6568451 = 9852677) B9852677
theorem B768519 : Blo 766334 768519 := bstep (se 1 (by rfl) ⟨576389, by rfl⟩ : syracuseStep 768519 = 1152779) B1152779
theorem B1948171 : Blo 766334 1948171 := bstep (se 1 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 1948171 = 2922257) B2922257
theorem B768527 : Blo 766334 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B14989859 : Blo 766334 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B768571 : Blo 766334 768571 := bstep (se 1 (by rfl) ⟨576428, by rfl⟩ : syracuseStep 768571 = 1152857) B1152857
theorem B768647 : Blo 766334 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B768655 : Blo 766334 768655 := bstep (se 1 (by rfl) ⟨576491, by rfl⟩ : syracuseStep 768655 = 1152983) B1152983
theorem B1948313 : Blo 766334 1948313 := bstep (se 2 (by rfl) ⟨730617, by rfl⟩ : syracuseStep 1948313 = 1461235) B1461235
theorem B768699 : Blo 766334 768699 := bstep (se 1 (by rfl) ⟨576524, by rfl⟩ : syracuseStep 768699 = 1153049) B1153049
theorem B768775 : Blo 766334 768775 := bstep (se 1 (by rfl) ⟨576581, by rfl⟩ : syracuseStep 768775 = 1153163) B1153163
theorem B768783 : Blo 766334 768783 := bstep (se 1 (by rfl) ⟨576587, by rfl⟩ : syracuseStep 768783 = 1153175) B1153175
theorem B768827 : Blo 766334 768827 := bstep (se 1 (by rfl) ⟨576620, by rfl⟩ : syracuseStep 768827 = 1153241) B1153241
theorem B1948475 : Blo 766334 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B1096507 : Blo 766334 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B3881843 : Blo 766334 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B768903 : Blo 766334 768903 := bstep (se 1 (by rfl) ⟨576677, by rfl⟩ : syracuseStep 768903 = 1153355) B1153355
theorem B768911 : Blo 766334 768911 := bstep (se 1 (by rfl) ⟨576683, by rfl⟩ : syracuseStep 768911 = 1153367) B1153367
theorem B768955 : Blo 766334 768955 := bstep (se 1 (by rfl) ⟨576716, by rfl⟩ : syracuseStep 768955 = 1153433) B1153433
theorem B4144081 : Blo 766334 4144081 := bstep (se 2 (by rfl) ⟨1554030, by rfl⟩ : syracuseStep 4144081 = 3108061) B3108061
theorem B769031 : Blo 766334 769031 := bstep (se 1 (by rfl) ⟨576773, by rfl⟩ : syracuseStep 769031 = 1153547) B1153547
theorem B769039 : Blo 766334 769039 := bstep (se 1 (by rfl) ⟨576779, by rfl⟩ : syracuseStep 769039 = 1153559) B1153559
theorem B1555499 : Blo 766334 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B769083 : Blo 766334 769083 := bstep (se 1 (by rfl) ⟨576812, by rfl⟩ : syracuseStep 769083 = 1153625) B1153625
theorem B769159 : Blo 766334 769159 := bstep (se 1 (by rfl) ⟨576869, by rfl⟩ : syracuseStep 769159 = 1153739) B1153739
theorem B769167 : Blo 766334 769167 := bstep (se 1 (by rfl) ⟨576875, by rfl⟩ : syracuseStep 769167 = 1153751) B1153751
theorem B1948819 : Blo 766334 1948819 := bstep (se 1 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 1948819 = 2923229) B2923229
theorem B769211 : Blo 766334 769211 := bstep (se 1 (by rfl) ⟨576908, by rfl⟩ : syracuseStep 769211 = 1153817) B1153817
theorem B769287 : Blo 766334 769287 := bstep (se 1 (by rfl) ⟨576965, by rfl⟩ : syracuseStep 769287 = 1153931) B1153931
theorem B1293583 : Blo 766334 1293583 := bstep (se 1 (by rfl) ⟨970187, by rfl⟩ : syracuseStep 1293583 = 1940375) B1940375
theorem B1457423 : Blo 766334 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B769295 : Blo 766334 769295 := bstep (se 1 (by rfl) ⟨576971, by rfl⟩ : syracuseStep 769295 = 1153943) B1153943
theorem B60833045 : Blo 766334 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1948961 : Blo 766334 1948961 := bstep (se 2 (by rfl) ⟨730860, by rfl⟩ : syracuseStep 1948961 = 1461721) B1461721
theorem B2800955 : Blo 766334 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B19709243 : Blo 766334 19709243 := bstep (se 1 (by rfl) ⟨14781932, by rfl⟩ : syracuseStep 19709243 = 29563865) B29563865
theorem B769339 : Blo 766334 769339 := bstep (se 1 (by rfl) ⟨577004, by rfl⟩ : syracuseStep 769339 = 1154009) B1154009
theorem B3882329 : Blo 766334 3882329 := bstep (se 2 (by rfl) ⟨1455873, by rfl⟩ : syracuseStep 3882329 = 2911747) B2911747
theorem B769415 : Blo 766334 769415 := bstep (se 1 (by rfl) ⟨577061, by rfl⟩ : syracuseStep 769415 = 1154123) B1154123
theorem B769423 : Blo 766334 769423 := bstep (se 1 (by rfl) ⟨577067, by rfl⟩ : syracuseStep 769423 = 1154135) B1154135
theorem B769467 : Blo 766334 769467 := bstep (se 1 (by rfl) ⟨577100, by rfl⟩ : syracuseStep 769467 = 1154201) B1154201
theorem B769543 : Blo 766334 769543 := bstep (se 1 (by rfl) ⟨577157, by rfl⟩ : syracuseStep 769543 = 1154315) B1154315
theorem B769551 : Blo 766334 769551 := bstep (se 1 (by rfl) ⟨577163, by rfl⟩ : syracuseStep 769551 = 1154327) B1154327
theorem B769595 : Blo 766334 769595 := bstep (se 1 (by rfl) ⟨577196, by rfl⟩ : syracuseStep 769595 = 1154393) B1154393
theorem B769671 : Blo 766334 769671 := bstep (se 1 (by rfl) ⟨577253, by rfl⟩ : syracuseStep 769671 = 1154507) B1154507
theorem B769679 : Blo 766334 769679 := bstep (se 1 (by rfl) ⟨577259, by rfl⟩ : syracuseStep 769679 = 1154519) B1154519
theorem B769723 : Blo 766334 769723 := bstep (se 1 (by rfl) ⟨577292, by rfl⟩ : syracuseStep 769723 = 1154585) B1154585
theorem B769799 : Blo 766334 769799 := bstep (se 1 (by rfl) ⟨577349, by rfl⟩ : syracuseStep 769799 = 1154699) B1154699
theorem B769807 : Blo 766334 769807 := bstep (se 1 (by rfl) ⟨577355, by rfl⟩ : syracuseStep 769807 = 1154711) B1154711
theorem B1294123 : Blo 766334 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B24035123 : Blo 766334 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B769851 : Blo 766334 769851 := bstep (se 1 (by rfl) ⟨577388, by rfl⟩ : syracuseStep 769851 = 1154777) B1154777
theorem B769927 : Blo 766334 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B769935 : Blo 766334 769935 := bstep (se 1 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 769935 = 1154903) B1154903
theorem B1294265 : Blo 766334 1294265 := bstep (se 2 (by rfl) ⟨485349, by rfl⟩ : syracuseStep 1294265 = 970699) B970699
theorem B769979 : Blo 766334 769979 := bstep (se 1 (by rfl) ⟨577484, by rfl⟩ : syracuseStep 769979 = 1154969) B1154969
theorem B770055 : Blo 766334 770055 := bstep (se 1 (by rfl) ⟨577541, by rfl⟩ : syracuseStep 770055 = 1155083) B1155083
theorem B3686411 : Blo 766334 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B770063 : Blo 766334 770063 := bstep (se 1 (by rfl) ⟨577547, by rfl⟩ : syracuseStep 770063 = 1155095) B1155095
theorem B770107 : Blo 766334 770107 := bstep (se 1 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 770107 = 1155161) B1155161
theorem B770183 : Blo 766334 770183 := bstep (se 1 (by rfl) ⟨577637, by rfl⟩ : syracuseStep 770183 = 1155275) B1155275
theorem B770191 : Blo 766334 770191 := bstep (se 1 (by rfl) ⟨577643, by rfl⟩ : syracuseStep 770191 = 1155287) B1155287
theorem B770235 : Blo 766334 770235 := bstep (se 1 (by rfl) ⟨577676, by rfl⟩ : syracuseStep 770235 = 1155353) B1155353
theorem B770311 : Blo 766334 770311 := bstep (se 1 (by rfl) ⟨577733, by rfl⟩ : syracuseStep 770311 = 1155467) B1155467
theorem B770319 : Blo 766334 770319 := bstep (se 1 (by rfl) ⟨577739, by rfl⟩ : syracuseStep 770319 = 1155479) B1155479
theorem B1294967 : Blo 766334 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B8307319 : Blo 766334 8307319 := bstep (se 1 (by rfl) ⟨6230489, by rfl⟩ : syracuseStep 8307319 = 12460979) B12460979
theorem B6570841 : Blo 766334 6570841 := bstep (se 2 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 6570841 = 4928131) B4928131
theorem B1459063 : Blo 766334 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B2081825 : Blo 766334 2081825 := bstep (se 2 (by rfl) ⟨780684, by rfl⟩ : syracuseStep 2081825 = 1561369) B1561369
theorem B1295419 : Blo 766334 1295419 := bstep (se 1 (by rfl) ⟨971564, by rfl⟩ : syracuseStep 1295419 = 1943129) B1943129
theorem B4375619 : Blo 766334 4375619 := bstep (se 1 (by rfl) ⟨3281714, by rfl⟩ : syracuseStep 4375619 = 6563429) B6563429
theorem B1295561 : Blo 766334 1295561 := bstep (se 2 (by rfl) ⟨485835, by rfl⟩ : syracuseStep 1295561 = 971671) B971671
theorem B3884435 : Blo 766334 3884435 := bstep (se 1 (by rfl) ⟨2913326, by rfl⟩ : syracuseStep 3884435 = 5826653) B5826653
theorem B1230265 : Blo 766334 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B2770519 : Blo 766334 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B2770633 : Blo 766334 2770633 := bstep (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) B2077975
theorem B1296263 : Blo 766334 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B14796695 : Blo 766334 14796695 := bstep (se 1 (by rfl) ⟨11097521, by rfl⟩ : syracuseStep 14796695 = 22195043) B22195043
theorem B136726679 : Blo 766334 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B1296911 : Blo 766334 1296911 := bstep (se 1 (by rfl) ⟨972683, by rfl⟩ : syracuseStep 1296911 = 1945367) B1945367
theorem B3328573 : Blo 766334 3328573 := bstep (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) B1248215
theorem B1460855 : Blo 766334 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B2214535 : Blo 766334 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B4147885 : Blo 766334 4147885 := bstep (se 3 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 4147885 = 1555457) B1555457
theorem B5065409 : Blo 766334 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B1461007 : Blo 766334 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B16599923 : Blo 766334 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B1297451 : Blo 766334 1297451 := bstep (se 1 (by rfl) ⟨973088, by rfl⟩ : syracuseStep 1297451 = 1946177) B1946177
theorem B1231931 : Blo 766334 1231931 := bstep (se 1 (by rfl) ⟨923948, by rfl⟩ : syracuseStep 1231931 = 1847897) B1847897
theorem B1461395 : Blo 766334 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B2182535 : Blo 766334 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B3689873 : Blo 766334 3689873 := bstep (se 2 (by rfl) ⟨1383702, by rfl⟩ : syracuseStep 3689873 = 2767405) B2767405
theorem B4378009 : Blo 766334 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B1297849 : Blo 766334 1297849 := bstep (se 2 (by rfl) ⟨486693, by rfl⟩ : syracuseStep 1297849 = 973387) B973387
theorem B1166891 : Blo 766334 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B1232443 : Blo 766334 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B2182717 : Blo 766334 2182717 := bstep (se 3 (by rfl) ⟨409259, by rfl⟩ : syracuseStep 2182717 = 818519) B818519
theorem B1035895 : Blo 766334 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B970375 : Blo 766334 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B2182945 : Blo 766334 2182945 := bstep (se 2 (by rfl) ⟨818604, by rfl⟩ : syracuseStep 2182945 = 1637209) B1637209
theorem B1724345 : Blo 766334 1724345 := bstep (se 2 (by rfl) ⟨646629, by rfl⟩ : syracuseStep 1724345 = 1293259) B1293259
theorem B970795 : Blo 766334 970795 := bstep (se 1 (by rfl) ⟨728096, by rfl⟩ : syracuseStep 970795 = 1456193) B1456193
theorem B2183287 : Blo 766334 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B1298551 : Blo 766334 1298551 := bstep (se 1 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 1298551 = 1947827) B1947827
theorem B1724687 : Blo 766334 1724687 := bstep (se 1 (by rfl) ⟨1293515, by rfl⟩ : syracuseStep 1724687 = 2587031) B2587031
theorem B971023 : Blo 766334 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B1724705 : Blo 766334 1724705 := bstep (se 2 (by rfl) ⟨646764, by rfl⟩ : syracuseStep 1724705 = 1293529) B1293529
theorem B1298747 : Blo 766334 1298747 := bstep (se 1 (by rfl) ⟨974060, by rfl⟩ : syracuseStep 1298747 = 1948121) B1948121
theorem B1560979 : Blo 766334 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B3887513 : Blo 766334 3887513 := bstep (se 2 (by rfl) ⟨1457817, by rfl⟩ : syracuseStep 3887513 = 2915635) B2915635
theorem B4444625 : Blo 766334 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B1561103 : Blo 766334 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B1725047 : Blo 766334 1725047 := bstep (se 1 (by rfl) ⟨1293785, by rfl⟩ : syracuseStep 1725047 = 2587571) B2587571
theorem B1561207 : Blo 766334 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B1299145 : Blo 766334 1299145 := bstep (se 2 (by rfl) ⟨487179, by rfl⟩ : syracuseStep 1299145 = 974359) B974359
theorem B1725227 : Blo 766334 1725227 := bstep (se 1 (by rfl) ⟨1293920, by rfl⟩ : syracuseStep 1725227 = 2587841) B2587841
theorem B971767 : Blo 766334 971767 := bstep (se 1 (by rfl) ⟨728825, by rfl⟩ : syracuseStep 971767 = 1457651) B1457651
theorem B2184221 : Blo 766334 2184221 := bstep (se 3 (by rfl) ⟨409541, by rfl⟩ : syracuseStep 2184221 = 819083) B819083
theorem B1725587 : Blo 766334 1725587 := bstep (se 1 (by rfl) ⟨1294190, by rfl⟩ : syracuseStep 1725587 = 2588381) B2588381
theorem B1725641 : Blo 766334 1725641 := bstep (se 2 (by rfl) ⟨647115, by rfl⟩ : syracuseStep 1725641 = 1294231) B1294231
theorem B3691777 : Blo 766334 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B972091 : Blo 766334 972091 := bstep (se 1 (by rfl) ⟨729068, by rfl⟩ : syracuseStep 972091 = 1458137) B1458137
theorem B4379993 : Blo 766334 4379993 := bstep (se 2 (by rfl) ⟨1642497, by rfl⟩ : syracuseStep 4379993 = 3284995) B3284995
theorem B2184563 : Blo 766334 2184563 := bstep (se 1 (by rfl) ⟨1638422, by rfl⟩ : syracuseStep 2184563 = 3276845) B3276845
theorem B1299847 : Blo 766334 1299847 := bstep (se 1 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 1299847 = 1949771) B1949771
theorem B972587 : Blo 766334 972587 := bstep (se 1 (by rfl) ⟨729440, by rfl⟩ : syracuseStep 972587 = 1458881) B1458881
theorem B2185019 : Blo 766334 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B2774843 : Blo 766334 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B11097931 : Blo 766334 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B1038199 : Blo 766334 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B1726343 : Blo 766334 1726343 := bstep (se 1 (by rfl) ⟨1294757, by rfl⟩ : syracuseStep 1726343 = 2589515) B2589515
theorem B1726523 : Blo 766334 1726523 := bstep (se 1 (by rfl) ⟨1294892, by rfl⟩ : syracuseStep 1726523 = 2589785) B2589785
theorem B1726649 : Blo 766334 1726649 := bstep (se 2 (by rfl) ⟨647493, by rfl⟩ : syracuseStep 1726649 = 1294987) B1294987
theorem B973063 : Blo 766334 973063 := bstep (se 1 (by rfl) ⟨729797, by rfl⟩ : syracuseStep 973063 = 1459595) B1459595
theorem B3692947 : Blo 766334 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B1726991 : Blo 766334 1726991 := bstep (se 1 (by rfl) ⟨1295243, by rfl⟩ : syracuseStep 1726991 = 2590487) B2590487
theorem B1727009 : Blo 766334 1727009 := bstep (se 2 (by rfl) ⟨647628, by rfl⟩ : syracuseStep 1727009 = 1295257) B1295257
theorem B973559 : Blo 766334 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B1727351 : Blo 766334 1727351 := bstep (se 1 (by rfl) ⟨1295513, by rfl⟩ : syracuseStep 1727351 = 2591027) B2591027
theorem B973711 : Blo 766334 973711 := bstep (se 1 (by rfl) ⟨730283, by rfl⟩ : syracuseStep 973711 = 1460567) B1460567
theorem B3890105 : Blo 766334 3890105 := bstep (se 2 (by rfl) ⟨1458789, by rfl⟩ : syracuseStep 3890105 = 2917579) B2917579
theorem B1727531 : Blo 766334 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B973883 : Blo 766334 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B1662137 : Blo 766334 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B4742489 : Blo 766334 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B1727891 : Blo 766334 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B1170875 : Blo 766334 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1727945 : Blo 766334 1727945 := bstep (se 2 (by rfl) ⟨647979, by rfl⟩ : syracuseStep 1727945 = 1295959) B1295959
theorem B3792413 : Blo 766334 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B5529131 : Blo 766334 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B7888427 : Blo 766334 7888427 := bstep (se 1 (by rfl) ⟨5916320, by rfl⟩ : syracuseStep 7888427 = 11832641) B11832641
theorem B3694253 : Blo 766334 3694253 := bstep (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) B1385345
theorem B6217445 : Blo 766334 6217445 := bstep (se 4 (by rfl) ⟨582885, by rfl⟩ : syracuseStep 6217445 = 1165771) B1165771
theorem B974855 : Blo 766334 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B1728647 : Blo 766334 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B3891401 : Blo 766334 3891401 := bstep (se 2 (by rfl) ⟨1459275, by rfl⟩ : syracuseStep 3891401 = 2918551) B2918551
theorem B1728827 : Blo 766334 1728827 := bstep (se 1 (by rfl) ⟨1296620, by rfl⟩ : syracuseStep 1728827 = 2593241) B2593241
theorem B1728953 : Blo 766334 1728953 := bstep (se 2 (by rfl) ⟨648357, by rfl⟩ : syracuseStep 1728953 = 1296715) B1296715
theorem B14016989 : Blo 766334 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B7397891 : Blo 766334 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B2187911 : Blo 766334 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B1729295 : Blo 766334 1729295 := bstep (se 1 (by rfl) ⟨1296971, by rfl⟩ : syracuseStep 1729295 = 2593943) B2593943
theorem B1729313 : Blo 766334 1729313 := bstep (se 2 (by rfl) ⟨648492, by rfl⟩ : syracuseStep 1729313 = 1296985) B1296985
theorem B3204163 : Blo 766334 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B1729655 : Blo 766334 1729655 := bstep (se 1 (by rfl) ⟨1297241, by rfl⟩ : syracuseStep 1729655 = 2594483) B2594483
theorem B20997251 : Blo 766334 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B4678829 : Blo 766334 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1729835 : Blo 766334 1729835 := bstep (se 1 (by rfl) ⟨1297376, by rfl⟩ : syracuseStep 1729835 = 2594753) B2594753
theorem B4384115 : Blo 766334 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B7366211 : Blo 766334 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B5826167 : Blo 766334 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B1730195 : Blo 766334 1730195 := bstep (se 1 (by rfl) ⟨1297646, by rfl⟩ : syracuseStep 1730195 = 2595293) B2595293
theorem B1730249 : Blo 766334 1730249 := bstep (se 2 (by rfl) ⟨648843, by rfl⟩ : syracuseStep 1730249 = 1297687) B1297687
theorem B6219521 : Blo 766334 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B2910275 : Blo 766334 2910275 := bstep (se 1 (by rfl) ⟨2182706, by rfl⟩ : syracuseStep 2910275 = 4365413) B4365413
theorem B3696947 : Blo 766334 3696947 := bstep (se 1 (by rfl) ⟨2772710, by rfl⟩ : syracuseStep 3696947 = 5545421) B5545421
theorem B1730951 : Blo 766334 1730951 := bstep (se 1 (by rfl) ⟨1298213, by rfl⟩ : syracuseStep 1730951 = 2596427) B2596427
theorem B2189825 : Blo 766334 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B1731131 : Blo 766334 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B5827139 : Blo 766334 5827139 := bstep (se 1 (by rfl) ⟨4370354, by rfl⟩ : syracuseStep 5827139 = 8740709) B8740709
theorem B1731257 : Blo 766334 1731257 := bstep (se 2 (by rfl) ⟨649221, by rfl⟩ : syracuseStep 1731257 = 1298443) B1298443
theorem B4385573 : Blo 766334 4385573 := bstep (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) B822295
theorem B4156211 : Blo 766334 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B1731599 : Blo 766334 1731599 := bstep (se 1 (by rfl) ⟨1298699, by rfl⟩ : syracuseStep 1731599 = 2597399) B2597399
theorem B2911261 : Blo 766334 2911261 := bstep (se 3 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 2911261 = 1091723) B1091723
theorem B1731617 : Blo 766334 1731617 := bstep (se 2 (by rfl) ⟨649356, by rfl⟩ : syracuseStep 1731617 = 1298713) B1298713
theorem B2190395 : Blo 766334 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B2190635 : Blo 766334 2190635 := bstep (se 1 (by rfl) ⟨1642976, by rfl⟩ : syracuseStep 2190635 = 3285953) B3285953
theorem B33221987 : Blo 766334 33221987 := bstep (se 1 (by rfl) ⟨24916490, by rfl⟩ : syracuseStep 33221987 = 49832981) B49832981
theorem B1731959 : Blo 766334 1731959 := bstep (se 1 (by rfl) ⟨1298969, by rfl⟩ : syracuseStep 1731959 = 2597939) B2597939
theorem B4386257 : Blo 766334 4386257 := bstep (se 2 (by rfl) ⟨1644846, by rfl⟩ : syracuseStep 4386257 = 3289693) B3289693
theorem B1732139 : Blo 766334 1732139 := bstep (se 1 (by rfl) ⟨1299104, by rfl⟩ : syracuseStep 1732139 = 2598209) B2598209
theorem B13987505 : Blo 766334 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B4386575 : Blo 766334 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B1732499 : Blo 766334 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B1732553 : Blo 766334 1732553 := bstep (se 2 (by rfl) ⟨649707, by rfl⟩ : syracuseStep 1732553 = 1299415) B1299415
theorem B4157405 : Blo 766334 4157405 := bstep (se 3 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 4157405 = 1559027) B1559027
theorem B5533829 : Blo 766334 5533829 := bstep (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) B1037593
theorem B8090369 : Blo 766334 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B4912139 : Blo 766334 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B14021947 : Blo 766334 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B7403237 : Blo 766334 7403237 := bstep (se 4 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 7403237 = 1388107) B1388107
theorem B4683521 : Blo 766334 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B2586383 : Blo 766334 2586383 := bstep (se 1 (by rfl) ⟨1939787, by rfl⟩ : syracuseStep 2586383 = 3879575) B3879575
theorem B2914163 : Blo 766334 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B4159367 : Blo 766334 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B3897233 : Blo 766334 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B2586653 : Blo 766334 2586653 := bstep (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) B969995
theorem B4684349 : Blo 766334 4684349 := bstep (se 3 (by rfl) ⟨878315, by rfl⟩ : syracuseStep 4684349 = 1756631) B1756631
theorem B7371557 : Blo 766334 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B3275579 : Blo 766334 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B5831513 : Blo 766334 5831513 := bstep (se 2 (by rfl) ⟨2186817, by rfl⟩ : syracuseStep 5831513 = 4373635) B4373635
theorem B4684691 : Blo 766334 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B3701771 : Blo 766334 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B2588057 : Blo 766334 2588057 := bstep (se 2 (by rfl) ⟨970521, by rfl⟩ : syracuseStep 2588057 = 1941043) B1941043
theorem B4161053 : Blo 766334 4161053 := bstep (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) B1560395
theorem B6553345 : Blo 766334 6553345 := bstep (se 2 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 6553345 = 4915009) B4915009
theorem B5832485 : Blo 766334 5832485 := bstep (se 4 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 5832485 = 1093591) B1093591
theorem B3899339 : Blo 766334 3899339 := bstep (se 1 (by rfl) ⟨2924504, by rfl⟩ : syracuseStep 3899339 = 5849009) B5849009
theorem B9830429 : Blo 766334 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B10518605 : Blo 766334 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B3506257 : Blo 766334 3506257 := bstep (se 2 (by rfl) ⟨1314846, by rfl⟩ : syracuseStep 3506257 = 2629693) B2629693
theorem B9961649 : Blo 766334 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B5832971 : Blo 766334 5832971 := bstep (se 1 (by rfl) ⟨4374728, by rfl⟩ : syracuseStep 5832971 = 8749457) B8749457
theorem B2621783 : Blo 766334 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1245623 : Blo 766334 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B2917079 : Blo 766334 2917079 := bstep (se 1 (by rfl) ⟨2187809, by rfl⟩ : syracuseStep 2917079 = 4375619) B4375619
theorem B11076425 : Blo 766334 11076425 := bstep (se 2 (by rfl) ⟨4153659, by rfl⟩ : syracuseStep 11076425 = 8307319) B8307319
theorem B1311671 : Blo 766334 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B2589623 : Blo 766334 2589623 := bstep (se 1 (by rfl) ⟨1942217, by rfl⟩ : syracuseStep 2589623 = 3884435) B3884435
theorem B3277903 : Blo 766334 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B1443065 : Blo 766334 1443065 := bstep (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) B1082299
theorem B9864463 : Blo 766334 9864463 := bstep (se 1 (by rfl) ⟨7398347, by rfl⟩ : syracuseStep 9864463 = 14796695) B14796695
theorem B1246727 : Blo 766334 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B2590217 : Blo 766334 2590217 := bstep (se 2 (by rfl) ⟨971331, by rfl⟩ : syracuseStep 2590217 = 1942663) B1942663
theorem B5834429 : Blo 766334 5834429 := bstep (se 3 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 5834429 = 2187911) B2187911
theorem B3376939 : Blo 766334 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B1640353 : Blo 766334 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B821287 : Blo 766334 821287 := bstep (se 1 (by rfl) ⟨615965, by rfl⟩ : syracuseStep 821287 = 1231931) B1231931
theorem B5834915 : Blo 766334 5834915 := bstep (se 1 (by rfl) ⟨4376186, by rfl⟩ : syracuseStep 5834915 = 8752373) B8752373
theorem B1640695 : Blo 766334 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B2459915 : Blo 766334 2459915 := bstep (se 1 (by rfl) ⟨1844936, by rfl⟩ : syracuseStep 2459915 = 3689873) B3689873
theorem B2459965 : Blo 766334 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B3508541 : Blo 766334 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B2591081 : Blo 766334 2591081 := bstep (se 2 (by rfl) ⟨971655, by rfl⟩ : syracuseStep 2591081 = 1943311) B1943311
theorem B1149563 : Blo 766334 1149563 := bstep (se 1 (by rfl) ⟨862172, by rfl⟩ : syracuseStep 1149563 = 1724345) B1724345
theorem B3115729 : Blo 766334 3115729 := bstep (se 2 (by rfl) ⟨1168398, by rfl⟩ : syracuseStep 3115729 = 2336797) B2336797
theorem B1149689 : Blo 766334 1149689 := bstep (se 2 (by rfl) ⟨431133, by rfl⟩ : syracuseStep 1149689 = 862267) B862267
theorem B1149791 : Blo 766334 1149791 := bstep (se 1 (by rfl) ⟨862343, by rfl⟩ : syracuseStep 1149791 = 1724687) B1724687
theorem B1149803 : Blo 766334 1149803 := bstep (se 1 (by rfl) ⟨862352, by rfl⟩ : syracuseStep 1149803 = 1724705) B1724705
theorem B1051499 : Blo 766334 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B2591675 : Blo 766334 2591675 := bstep (se 1 (by rfl) ⟨1943756, by rfl⟩ : syracuseStep 2591675 = 3887513) B3887513
theorem B1150031 : Blo 766334 1150031 := bstep (se 1 (by rfl) ⟨862523, by rfl⟩ : syracuseStep 1150031 = 1725047) B1725047
theorem B1150151 : Blo 766334 1150151 := bstep (se 1 (by rfl) ⟨862613, by rfl⟩ : syracuseStep 1150151 = 1725227) B1725227
theorem B1150313 : Blo 766334 1150313 := bstep (se 2 (by rfl) ⟨431367, by rfl⟩ : syracuseStep 1150313 = 862735) B862735
theorem B1150391 : Blo 766334 1150391 := bstep (se 1 (by rfl) ⟨862793, by rfl⟩ : syracuseStep 1150391 = 1725587) B1725587
theorem B1150427 : Blo 766334 1150427 := bstep (se 1 (by rfl) ⟨862820, by rfl⟩ : syracuseStep 1150427 = 1725641) B1725641
theorem B2952713 : Blo 766334 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B2919995 : Blo 766334 2919995 := bstep (se 1 (by rfl) ⟨2189996, by rfl⟩ : syracuseStep 2919995 = 4379993) B4379993
theorem B1150895 : Blo 766334 1150895 := bstep (se 1 (by rfl) ⟨863171, by rfl⟩ : syracuseStep 1150895 = 1726343) B1726343
theorem B2461697 : Blo 766334 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B1150985 : Blo 766334 1150985 := bstep (se 2 (by rfl) ⟨431619, by rfl⟩ : syracuseStep 1150985 = 863239) B863239
theorem B1151015 : Blo 766334 1151015 := bstep (se 1 (by rfl) ⟨863261, by rfl⟩ : syracuseStep 1151015 = 1726523) B1726523
theorem B1151099 : Blo 766334 1151099 := bstep (se 1 (by rfl) ⟨863324, by rfl⟩ : syracuseStep 1151099 = 1726649) B1726649
theorem B1151225 : Blo 766334 1151225 := bstep (se 2 (by rfl) ⟨431709, by rfl⟩ : syracuseStep 1151225 = 863419) B863419
theorem B1151327 : Blo 766334 1151327 := bstep (se 1 (by rfl) ⟨863495, by rfl⟩ : syracuseStep 1151327 = 1726991) B1726991
theorem B1151339 : Blo 766334 1151339 := bstep (se 1 (by rfl) ⟨863504, by rfl⟩ : syracuseStep 1151339 = 1727009) B1727009
theorem B5837345 : Blo 766334 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B922151 : Blo 766334 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1151567 : Blo 766334 1151567 := bstep (se 1 (by rfl) ⟨863675, by rfl⟩ : syracuseStep 1151567 = 1727351) B1727351
theorem B2593403 : Blo 766334 2593403 := bstep (se 1 (by rfl) ⟨1945052, by rfl⟩ : syracuseStep 2593403 = 3890105) B3890105
theorem B12489389 : Blo 766334 12489389 := bstep (se 3 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 12489389 = 4683521) B4683521
theorem B1151687 : Blo 766334 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B10490579 : Blo 766334 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1643257 : Blo 766334 1643257 := bstep (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) B1232443
theorem B2593565 : Blo 766334 2593565 := bstep (se 3 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 2593565 = 972587) B972587
theorem B1381193 : Blo 766334 1381193 := bstep (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) B1035895
theorem B1151849 : Blo 766334 1151849 := bstep (se 2 (by rfl) ⟨431943, by rfl⟩ : syracuseStep 1151849 = 863887) B863887
theorem B1151927 : Blo 766334 1151927 := bstep (se 1 (by rfl) ⟨863945, by rfl⟩ : syracuseStep 1151927 = 1727891) B1727891
theorem B1151963 : Blo 766334 1151963 := bstep (se 1 (by rfl) ⟨863972, by rfl⟩ : syracuseStep 1151963 = 1727945) B1727945
theorem B2528275 : Blo 766334 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B1643599 : Blo 766334 1643599 := bstep (se 1 (by rfl) ⟨1232699, by rfl⟩ : syracuseStep 1643599 = 2465399) B2465399
theorem B1152431 : Blo 766334 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B2594267 : Blo 766334 2594267 := bstep (se 1 (by rfl) ⟨1945700, by rfl⟩ : syracuseStep 2594267 = 3891401) B3891401
theorem B1316359 : Blo 766334 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B1152521 : Blo 766334 1152521 := bstep (se 2 (by rfl) ⟨432195, by rfl⟩ : syracuseStep 1152521 = 864391) B864391
theorem B1152551 : Blo 766334 1152551 := bstep (se 1 (by rfl) ⟨864413, by rfl⟩ : syracuseStep 1152551 = 1728827) B1728827
theorem B1152635 : Blo 766334 1152635 := bstep (se 1 (by rfl) ⟨864476, by rfl⟩ : syracuseStep 1152635 = 1728953) B1728953
theorem B9344659 : Blo 766334 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B1382059 : Blo 766334 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B2627261 : Blo 766334 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B1152761 : Blo 766334 1152761 := bstep (se 2 (by rfl) ⟨432285, by rfl⟩ : syracuseStep 1152761 = 864571) B864571
theorem B1152863 : Blo 766334 1152863 := bstep (se 1 (by rfl) ⟨864647, by rfl⟩ : syracuseStep 1152863 = 1729295) B1729295
theorem B1152875 : Blo 766334 1152875 := bstep (se 1 (by rfl) ⟨864656, by rfl⟩ : syracuseStep 1152875 = 1729313) B1729313
theorem B1153103 : Blo 766334 1153103 := bstep (se 1 (by rfl) ⟨864827, by rfl⟩ : syracuseStep 1153103 = 1729655) B1729655
theorem B13998167 : Blo 766334 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B8755289 : Blo 766334 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B3119219 : Blo 766334 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2594969 : Blo 766334 2594969 := bstep (se 2 (by rfl) ⟨973113, by rfl⟩ : syracuseStep 2594969 = 1946227) B1946227
theorem B1153223 : Blo 766334 1153223 := bstep (se 1 (by rfl) ⟨864917, by rfl⟩ : syracuseStep 1153223 = 1729835) B1729835
theorem B2922743 : Blo 766334 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B1153385 : Blo 766334 1153385 := bstep (se 2 (by rfl) ⟨432519, by rfl⟩ : syracuseStep 1153385 = 865039) B865039
theorem B1153463 : Blo 766334 1153463 := bstep (se 1 (by rfl) ⟨865097, by rfl⟩ : syracuseStep 1153463 = 1730195) B1730195
theorem B1153499 : Blo 766334 1153499 := bstep (se 1 (by rfl) ⟨865124, by rfl⟩ : syracuseStep 1153499 = 1730249) B1730249
theorem B1317455 : Blo 766334 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B11082419 : Blo 766334 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B1940183 : Blo 766334 1940183 := bstep (se 1 (by rfl) ⟨1455137, by rfl⟩ : syracuseStep 1940183 = 2910275) B2910275
theorem B12491597 : Blo 766334 12491597 := bstep (se 3 (by rfl) ⟨2342174, by rfl⟩ : syracuseStep 12491597 = 4684349) B4684349
theorem B2464631 : Blo 766334 2464631 := bstep (se 1 (by rfl) ⟨1848473, by rfl⟩ : syracuseStep 2464631 = 3696947) B3696947
theorem B1153967 : Blo 766334 1153967 := bstep (se 1 (by rfl) ⟨865475, by rfl⟩ : syracuseStep 1153967 = 1730951) B1730951
theorem B4922369 : Blo 766334 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B1154057 : Blo 766334 1154057 := bstep (se 2 (by rfl) ⟨432771, by rfl⟩ : syracuseStep 1154057 = 865543) B865543
theorem B1154087 : Blo 766334 1154087 := bstep (se 1 (by rfl) ⟨865565, by rfl⟩ : syracuseStep 1154087 = 1731131) B1731131
theorem B1940537 : Blo 766334 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B1154171 : Blo 766334 1154171 := bstep (se 1 (by rfl) ⟨865628, by rfl⟩ : syracuseStep 1154171 = 1731257) B1731257
theorem B4988099 : Blo 766334 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B924871 : Blo 766334 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B2923715 : Blo 766334 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B1154297 : Blo 766334 1154297 := bstep (se 2 (by rfl) ⟨432861, by rfl⟩ : syracuseStep 1154297 = 865723) B865723
theorem B2596157 : Blo 766334 2596157 := bstep (se 3 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 2596157 = 973559) B973559
theorem B1154399 : Blo 766334 1154399 := bstep (se 1 (by rfl) ⟨865799, by rfl⟩ : syracuseStep 1154399 = 1731599) B1731599
theorem B1154411 : Blo 766334 1154411 := bstep (se 1 (by rfl) ⟨865808, by rfl⟩ : syracuseStep 1154411 = 1731617) B1731617
theorem B1154639 : Blo 766334 1154639 := bstep (se 1 (by rfl) ⟨865979, by rfl⟩ : syracuseStep 1154639 = 1731959) B1731959
theorem B9838219 : Blo 766334 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B2924171 : Blo 766334 2924171 := bstep (se 1 (by rfl) ⟨2193128, by rfl⟩ : syracuseStep 2924171 = 4386257) B4386257
theorem B1154759 : Blo 766334 1154759 := bstep (se 1 (by rfl) ⟨866069, by rfl⟩ : syracuseStep 1154759 = 1732139) B1732139
theorem B1384265 : Blo 766334 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B2924383 : Blo 766334 2924383 := bstep (se 1 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 2924383 = 4386575) B4386575
theorem B1154921 : Blo 766334 1154921 := bstep (se 2 (by rfl) ⟨433095, by rfl⟩ : syracuseStep 1154921 = 866191) B866191
theorem B5611373 : Blo 766334 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B1154999 : Blo 766334 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B1155035 : Blo 766334 1155035 := bstep (se 1 (by rfl) ⟨866276, by rfl⟩ : syracuseStep 1155035 = 1732553) B1732553
theorem B5251229 : Blo 766334 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B2597021 : Blo 766334 2597021 := bstep (se 3 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 2597021 = 973883) B973883
theorem B3285353 : Blo 766334 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B4923929 : Blo 766334 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B2597561 : Blo 766334 2597561 := bstep (se 2 (by rfl) ⟨974085, by rfl⟩ : syracuseStep 2597561 = 1948171) B1948171
theorem B1844129 : Blo 766334 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B3122333 : Blo 766334 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B1942775 : Blo 766334 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B2598155 : Blo 766334 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B2598425 : Blo 766334 2598425 := bstep (se 2 (by rfl) ⟨974409, by rfl⟩ : syracuseStep 2598425 = 1948819) B1948819
theorem B6301223 : Blo 766334 6301223 := bstep (se 1 (by rfl) ⟨4725917, by rfl⟩ : syracuseStep 6301223 = 9451835) B9451835
theorem B3286651 : Blo 766334 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B3123127 : Blo 766334 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B2467847 : Blo 766334 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B862843 : Blo 766334 862843 := bstep (se 1 (by rfl) ⟨647132, by rfl⟩ : syracuseStep 862843 = 1294265) B1294265
theorem B2599559 : Blo 766334 2599559 := bstep (se 1 (by rfl) ⟨1949669, by rfl⟩ : syracuseStep 2599559 = 3899339) B3899339
theorem B2599613 : Blo 766334 2599613 := bstep (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) B974855
theorem B1944263 : Blo 766334 1944263 := bstep (se 1 (by rfl) ⟨1458197, by rfl⟩ : syracuseStep 1944263 = 2916395) B2916395
theorem B3287881 : Blo 766334 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B2599775 : Blo 766334 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B863311 : Blo 766334 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B54013229 : Blo 766334 54013229 := bstep (se 3 (by rfl) ⟨10127480, by rfl⟩ : syracuseStep 54013229 = 20254961) B20254961
theorem B1387883 : Blo 766334 1387883 := bstep (se 1 (by rfl) ⟨1040912, by rfl⟩ : syracuseStep 1387883 = 2081825) B2081825
theorem B863707 : Blo 766334 863707 := bstep (se 1 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 863707 = 1295561) B1295561
theorem B8761121 : Blo 766334 8761121 := bstep (se 2 (by rfl) ⟨3285420, by rfl⟩ : syracuseStep 8761121 = 6570841) B6570841
theorem B4370219 : Blo 766334 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B1945417 : Blo 766334 1945417 := bstep (se 2 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 1945417 = 1459063) B1459063
theorem B864175 : Blo 766334 864175 := bstep (se 1 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 864175 = 1296263) B1296263
theorem B4927517 : Blo 766334 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B864607 : Blo 766334 864607 := bstep (se 1 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 864607 = 1296911) B1296911
theorem B766383 : Blo 766334 766383 := bstep (se 1 (by rfl) ⟨574787, by rfl⟩ : syracuseStep 766383 = 1149575) B1149575
theorem B766407 : Blo 766334 766407 := bstep (se 1 (by rfl) ⟨574805, by rfl⟩ : syracuseStep 766407 = 1149611) B1149611
theorem B766427 : Blo 766334 766427 := bstep (se 1 (by rfl) ⟨574820, by rfl⟩ : syracuseStep 766427 = 1149641) B1149641
theorem B766503 : Blo 766334 766503 := bstep (se 1 (by rfl) ⟨574877, by rfl⟩ : syracuseStep 766503 = 1149755) B1149755
theorem B2470459 : Blo 766334 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B766543 : Blo 766334 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B766559 : Blo 766334 766559 := bstep (se 1 (by rfl) ⟨574919, by rfl⟩ : syracuseStep 766559 = 1149839) B1149839
theorem B766587 : Blo 766334 766587 := bstep (se 1 (by rfl) ⟨574940, by rfl⟩ : syracuseStep 766587 = 1149881) B1149881
theorem B766639 : Blo 766334 766639 := bstep (se 1 (by rfl) ⟨574979, by rfl⟩ : syracuseStep 766639 = 1149959) B1149959
theorem B766663 : Blo 766334 766663 := bstep (se 1 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 766663 = 1149995) B1149995
theorem B864967 : Blo 766334 864967 := bstep (se 1 (by rfl) ⟨648725, by rfl⟩ : syracuseStep 864967 = 1297451) B1297451
theorem B766683 : Blo 766334 766683 := bstep (se 1 (by rfl) ⟨575012, by rfl⟩ : syracuseStep 766683 = 1150025) B1150025
theorem B766759 : Blo 766334 766759 := bstep (se 1 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 766759 = 1150139) B1150139
theorem B766799 : Blo 766334 766799 := bstep (se 1 (by rfl) ⟨575099, by rfl⟩ : syracuseStep 766799 = 1150199) B1150199
theorem B766815 : Blo 766334 766815 := bstep (se 1 (by rfl) ⟨575111, by rfl⟩ : syracuseStep 766815 = 1150223) B1150223
theorem B766843 : Blo 766334 766843 := bstep (se 1 (by rfl) ⟨575132, by rfl⟩ : syracuseStep 766843 = 1150265) B1150265
theorem B1455023 : Blo 766334 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B766895 : Blo 766334 766895 := bstep (se 1 (by rfl) ⟨575171, by rfl⟩ : syracuseStep 766895 = 1150343) B1150343
theorem B1946551 : Blo 766334 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B766919 : Blo 766334 766919 := bstep (se 1 (by rfl) ⟨575189, by rfl⟩ : syracuseStep 766919 = 1150379) B1150379
theorem B766939 : Blo 766334 766939 := bstep (se 1 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 766939 = 1150409) B1150409
theorem B767015 : Blo 766334 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B767055 : Blo 766334 767055 := bstep (se 1 (by rfl) ⟨575291, by rfl⟩ : syracuseStep 767055 = 1150583) B1150583
theorem B2667599 : Blo 766334 2667599 := bstep (se 1 (by rfl) ⟨2000699, by rfl⟩ : syracuseStep 2667599 = 4001399) B4001399
theorem B767071 : Blo 766334 767071 := bstep (se 1 (by rfl) ⟨575303, by rfl⟩ : syracuseStep 767071 = 1150607) B1150607
theorem B767099 : Blo 766334 767099 := bstep (se 1 (by rfl) ⟨575324, by rfl⟩ : syracuseStep 767099 = 1150649) B1150649
theorem B767151 : Blo 766334 767151 := bstep (se 1 (by rfl) ⟨575363, by rfl⟩ : syracuseStep 767151 = 1150727) B1150727
theorem B767175 : Blo 766334 767175 := bstep (se 1 (by rfl) ⟨575381, by rfl⟩ : syracuseStep 767175 = 1150763) B1150763
theorem B767195 : Blo 766334 767195 := bstep (se 1 (by rfl) ⟨575396, by rfl⟩ : syracuseStep 767195 = 1150793) B1150793
theorem B767271 : Blo 766334 767271 := bstep (se 1 (by rfl) ⟨575453, by rfl⟩ : syracuseStep 767271 = 1150907) B1150907
theorem B767311 : Blo 766334 767311 := bstep (se 1 (by rfl) ⟨575483, by rfl⟩ : syracuseStep 767311 = 1150967) B1150967
theorem B767327 : Blo 766334 767327 := bstep (se 1 (by rfl) ⟨575495, by rfl⟩ : syracuseStep 767327 = 1150991) B1150991
theorem B767355 : Blo 766334 767355 := bstep (se 1 (by rfl) ⟨575516, by rfl⟩ : syracuseStep 767355 = 1151033) B1151033
theorem B767407 : Blo 766334 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B767431 : Blo 766334 767431 := bstep (se 1 (by rfl) ⟨575573, by rfl⟩ : syracuseStep 767431 = 1151147) B1151147
theorem B767451 : Blo 766334 767451 := bstep (se 1 (by rfl) ⟨575588, by rfl⟩ : syracuseStep 767451 = 1151177) B1151177
theorem B767527 : Blo 766334 767527 := bstep (se 1 (by rfl) ⟨575645, by rfl⟩ : syracuseStep 767527 = 1151291) B1151291
theorem B865831 : Blo 766334 865831 := bstep (se 1 (by rfl) ⟨649373, by rfl⟩ : syracuseStep 865831 = 1298747) B1298747
theorem B767567 : Blo 766334 767567 := bstep (se 1 (by rfl) ⟨575675, by rfl⟩ : syracuseStep 767567 = 1151351) B1151351
theorem B767583 : Blo 766334 767583 := bstep (se 1 (by rfl) ⟨575687, by rfl⟩ : syracuseStep 767583 = 1151375) B1151375
theorem B767611 : Blo 766334 767611 := bstep (se 1 (by rfl) ⟨575708, by rfl⟩ : syracuseStep 767611 = 1151417) B1151417
theorem B2963083 : Blo 766334 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B767663 : Blo 766334 767663 := bstep (se 1 (by rfl) ⟨575747, by rfl⟩ : syracuseStep 767663 = 1151495) B1151495
theorem B767687 : Blo 766334 767687 := bstep (se 1 (by rfl) ⟨575765, by rfl⟩ : syracuseStep 767687 = 1151531) B1151531
theorem B767707 : Blo 766334 767707 := bstep (se 1 (by rfl) ⟨575780, by rfl⟩ : syracuseStep 767707 = 1151561) B1151561
theorem B767783 : Blo 766334 767783 := bstep (se 1 (by rfl) ⟨575837, by rfl⟩ : syracuseStep 767783 = 1151675) B1151675
theorem B767823 : Blo 766334 767823 := bstep (se 1 (by rfl) ⟨575867, by rfl⟩ : syracuseStep 767823 = 1151735) B1151735
theorem B767839 : Blo 766334 767839 := bstep (se 1 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 767839 = 1151759) B1151759
theorem B767867 : Blo 766334 767867 := bstep (se 1 (by rfl) ⟨575900, by rfl⟩ : syracuseStep 767867 = 1151801) B1151801
theorem B767919 : Blo 766334 767919 := bstep (se 1 (by rfl) ⟨575939, by rfl⟩ : syracuseStep 767919 = 1151879) B1151879
theorem B767943 : Blo 766334 767943 := bstep (se 1 (by rfl) ⟨575957, by rfl⟩ : syracuseStep 767943 = 1151915) B1151915
theorem B767963 : Blo 766334 767963 := bstep (se 1 (by rfl) ⟨575972, by rfl⟩ : syracuseStep 767963 = 1151945) B1151945
theorem B1456147 : Blo 766334 1456147 := bstep (se 1 (by rfl) ⟨1092110, by rfl⟩ : syracuseStep 1456147 = 2184221) B2184221
theorem B768039 : Blo 766334 768039 := bstep (se 1 (by rfl) ⟨576029, by rfl⟩ : syracuseStep 768039 = 1152059) B1152059
theorem B768079 : Blo 766334 768079 := bstep (se 1 (by rfl) ⟨576059, by rfl⟩ : syracuseStep 768079 = 1152119) B1152119
theorem B4438097 : Blo 766334 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B768095 : Blo 766334 768095 := bstep (se 1 (by rfl) ⟨576071, by rfl⟩ : syracuseStep 768095 = 1152143) B1152143
theorem B768123 : Blo 766334 768123 := bstep (se 1 (by rfl) ⟨576092, by rfl⟩ : syracuseStep 768123 = 1152185) B1152185
theorem B768175 : Blo 766334 768175 := bstep (se 1 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 768175 = 1152263) B1152263
theorem B768199 : Blo 766334 768199 := bstep (se 1 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 768199 = 1152299) B1152299
theorem B768219 : Blo 766334 768219 := bstep (se 1 (by rfl) ⟨576164, by rfl⟩ : syracuseStep 768219 = 1152329) B1152329
theorem B1456375 : Blo 766334 1456375 := bstep (se 1 (by rfl) ⟨1092281, by rfl⟩ : syracuseStep 1456375 = 2184563) B2184563
theorem B768295 : Blo 766334 768295 := bstep (se 1 (by rfl) ⟨576221, by rfl⟩ : syracuseStep 768295 = 1152443) B1152443
theorem B768335 : Blo 766334 768335 := bstep (se 1 (by rfl) ⟨576251, by rfl⟩ : syracuseStep 768335 = 1152503) B1152503
theorem B768351 : Blo 766334 768351 := bstep (se 1 (by rfl) ⟨576263, by rfl⟩ : syracuseStep 768351 = 1152527) B1152527
theorem B1948009 : Blo 766334 1948009 := bstep (se 2 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 1948009 = 1461007) B1461007
theorem B768379 : Blo 766334 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B768431 : Blo 766334 768431 := bstep (se 1 (by rfl) ⟨576323, by rfl⟩ : syracuseStep 768431 = 1152647) B1152647
theorem B768455 : Blo 766334 768455 := bstep (se 1 (by rfl) ⟨576341, by rfl⟩ : syracuseStep 768455 = 1152683) B1152683
theorem B768475 : Blo 766334 768475 := bstep (se 1 (by rfl) ⟨576356, by rfl⟩ : syracuseStep 768475 = 1152713) B1152713
theorem B7027181 : Blo 766334 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B1456679 : Blo 766334 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B768551 : Blo 766334 768551 := bstep (se 1 (by rfl) ⟨576413, by rfl⟩ : syracuseStep 768551 = 1152827) B1152827
theorem B1849895 : Blo 766334 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B768591 : Blo 766334 768591 := bstep (se 1 (by rfl) ⟨576443, by rfl⟩ : syracuseStep 768591 = 1152887) B1152887
theorem B768607 : Blo 766334 768607 := bstep (se 1 (by rfl) ⟨576455, by rfl⟩ : syracuseStep 768607 = 1152911) B1152911
theorem B768635 : Blo 766334 768635 := bstep (se 1 (by rfl) ⟨576476, by rfl⟩ : syracuseStep 768635 = 1152953) B1152953
theorem B1948283 : Blo 766334 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B768687 : Blo 766334 768687 := bstep (se 1 (by rfl) ⟨576515, by rfl⟩ : syracuseStep 768687 = 1153031) B1153031
theorem B768711 : Blo 766334 768711 := bstep (se 1 (by rfl) ⟨576533, by rfl⟩ : syracuseStep 768711 = 1153067) B1153067
theorem B3881681 : Blo 766334 3881681 := bstep (se 2 (by rfl) ⟨1455630, by rfl⟩ : syracuseStep 3881681 = 2911261) B2911261
theorem B768731 : Blo 766334 768731 := bstep (se 1 (by rfl) ⟨576548, by rfl⟩ : syracuseStep 768731 = 1153097) B1153097
theorem B768807 : Blo 766334 768807 := bstep (se 1 (by rfl) ⟨576605, by rfl⟩ : syracuseStep 768807 = 1153211) B1153211
theorem B768847 : Blo 766334 768847 := bstep (se 1 (by rfl) ⟨576635, by rfl⟩ : syracuseStep 768847 = 1153271) B1153271
theorem B768863 : Blo 766334 768863 := bstep (se 1 (by rfl) ⟨576647, by rfl⟩ : syracuseStep 768863 = 1153295) B1153295
theorem B768891 : Blo 766334 768891 := bstep (se 1 (by rfl) ⟨576668, by rfl⟩ : syracuseStep 768891 = 1153337) B1153337
theorem B768943 : Blo 766334 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B1293239 : Blo 766334 1293239 := bstep (se 1 (by rfl) ⟨969929, by rfl⟩ : syracuseStep 1293239 = 1939859) B1939859
theorem B768967 : Blo 766334 768967 := bstep (se 1 (by rfl) ⟨576725, by rfl⟩ : syracuseStep 768967 = 1153451) B1153451
theorem B768987 : Blo 766334 768987 := bstep (se 1 (by rfl) ⟨576740, by rfl⟩ : syracuseStep 768987 = 1153481) B1153481
theorem B5848037 : Blo 766334 5848037 := bstep (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) B1096507
theorem B769063 : Blo 766334 769063 := bstep (se 1 (by rfl) ⟨576797, by rfl⟩ : syracuseStep 769063 = 1153595) B1153595
theorem B769103 : Blo 766334 769103 := bstep (se 1 (by rfl) ⟨576827, by rfl⟩ : syracuseStep 769103 = 1153655) B1153655
theorem B769119 : Blo 766334 769119 := bstep (se 1 (by rfl) ⟨576839, by rfl⟩ : syracuseStep 769119 = 1153679) B1153679
theorem B769147 : Blo 766334 769147 := bstep (se 1 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 769147 = 1153721) B1153721
theorem B769199 : Blo 766334 769199 := bstep (se 1 (by rfl) ⟨576899, by rfl⟩ : syracuseStep 769199 = 1153799) B1153799
theorem B769223 : Blo 766334 769223 := bstep (se 1 (by rfl) ⟨576917, by rfl⟩ : syracuseStep 769223 = 1153835) B1153835
theorem B769243 : Blo 766334 769243 := bstep (se 1 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 769243 = 1153865) B1153865
theorem B769319 : Blo 766334 769319 := bstep (se 1 (by rfl) ⟨576989, by rfl⟩ : syracuseStep 769319 = 1153979) B1153979
theorem B769359 : Blo 766334 769359 := bstep (se 1 (by rfl) ⟨577019, by rfl⟩ : syracuseStep 769359 = 1154039) B1154039
theorem B769375 : Blo 766334 769375 := bstep (se 1 (by rfl) ⟨577031, by rfl⟩ : syracuseStep 769375 = 1154063) B1154063
theorem B769403 : Blo 766334 769403 := bstep (se 1 (by rfl) ⟨577052, by rfl⟩ : syracuseStep 769403 = 1154105) B1154105
theorem B6733181 : Blo 766334 6733181 := bstep (se 3 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 6733181 = 2524943) B2524943
theorem B769455 : Blo 766334 769455 := bstep (se 1 (by rfl) ⟨577091, by rfl⟩ : syracuseStep 769455 = 1154183) B1154183
theorem B769479 : Blo 766334 769479 := bstep (se 1 (by rfl) ⟨577109, by rfl⟩ : syracuseStep 769479 = 1154219) B1154219
theorem B769499 : Blo 766334 769499 := bstep (se 1 (by rfl) ⟨577124, by rfl⟩ : syracuseStep 769499 = 1154249) B1154249
theorem B1293833 : Blo 766334 1293833 := bstep (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) B970375
theorem B35569181 : Blo 766334 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B769575 : Blo 766334 769575 := bstep (se 1 (by rfl) ⟨577181, by rfl⟩ : syracuseStep 769575 = 1154363) B1154363
theorem B3161659 : Blo 766334 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B769615 : Blo 766334 769615 := bstep (se 1 (by rfl) ⟨577211, by rfl⟩ : syracuseStep 769615 = 1154423) B1154423
theorem B769631 : Blo 766334 769631 := bstep (se 1 (by rfl) ⟨577223, by rfl⟩ : syracuseStep 769631 = 1154447) B1154447
theorem B769659 : Blo 766334 769659 := bstep (se 1 (by rfl) ⟨577244, by rfl⟩ : syracuseStep 769659 = 1154489) B1154489
theorem B4374161 : Blo 766334 4374161 := bstep (se 2 (by rfl) ⟨1640310, by rfl⟩ : syracuseStep 4374161 = 3280621) B3280621
theorem B1293995 : Blo 766334 1293995 := bstep (se 1 (by rfl) ⟨970496, by rfl⟩ : syracuseStep 1293995 = 1940993) B1940993
theorem B769711 : Blo 766334 769711 := bstep (se 1 (by rfl) ⟨577283, by rfl⟩ : syracuseStep 769711 = 1154567) B1154567
theorem B3686087 : Blo 766334 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B5258951 : Blo 766334 5258951 := bstep (se 1 (by rfl) ⟨3944213, by rfl⟩ : syracuseStep 5258951 = 7888427) B7888427
theorem B769735 : Blo 766334 769735 := bstep (se 1 (by rfl) ⟨577301, by rfl⟩ : syracuseStep 769735 = 1154603) B1154603
theorem B769755 : Blo 766334 769755 := bstep (se 1 (by rfl) ⟨577316, by rfl⟩ : syracuseStep 769755 = 1154633) B1154633
theorem B5259001 : Blo 766334 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B769831 : Blo 766334 769831 := bstep (se 1 (by rfl) ⟨577373, by rfl⟩ : syracuseStep 769831 = 1154747) B1154747
theorem B1457993 : Blo 766334 1457993 := bstep (se 2 (by rfl) ⟨546747, by rfl⟩ : syracuseStep 1457993 = 1093495) B1093495
theorem B769871 : Blo 766334 769871 := bstep (se 1 (by rfl) ⟨577403, by rfl⟩ : syracuseStep 769871 = 1154807) B1154807
theorem B769887 : Blo 766334 769887 := bstep (se 1 (by rfl) ⟨577415, by rfl⟩ : syracuseStep 769887 = 1154831) B1154831
theorem B769915 : Blo 766334 769915 := bstep (se 1 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 769915 = 1154873) B1154873
theorem B769967 : Blo 766334 769967 := bstep (se 1 (by rfl) ⟨577475, by rfl⟩ : syracuseStep 769967 = 1154951) B1154951
theorem B1228727 : Blo 766334 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B769991 : Blo 766334 769991 := bstep (se 1 (by rfl) ⟨577493, by rfl⟩ : syracuseStep 769991 = 1154987) B1154987
theorem B770011 : Blo 766334 770011 := bstep (se 1 (by rfl) ⟨577508, by rfl⟩ : syracuseStep 770011 = 1155017) B1155017
theorem B770087 : Blo 766334 770087 := bstep (se 1 (by rfl) ⟨577565, by rfl⟩ : syracuseStep 770087 = 1155131) B1155131
theorem B1294393 : Blo 766334 1294393 := bstep (se 2 (by rfl) ⟨485397, by rfl⟩ : syracuseStep 1294393 = 970795) B970795
theorem B3948601 : Blo 766334 3948601 := bstep (se 2 (by rfl) ⟨1480725, by rfl⟩ : syracuseStep 3948601 = 2961451) B2961451
theorem B770127 : Blo 766334 770127 := bstep (se 1 (by rfl) ⟨577595, by rfl⟩ : syracuseStep 770127 = 1155191) B1155191
theorem B770143 : Blo 766334 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B770171 : Blo 766334 770171 := bstep (se 1 (by rfl) ⟨577628, by rfl⟩ : syracuseStep 770171 = 1155257) B1155257
theorem B770223 : Blo 766334 770223 := bstep (se 1 (by rfl) ⟨577667, by rfl⟩ : syracuseStep 770223 = 1155335) B1155335
theorem B1294535 : Blo 766334 1294535 := bstep (se 1 (by rfl) ⟨970901, by rfl⟩ : syracuseStep 1294535 = 1941803) B1941803
theorem B770247 : Blo 766334 770247 := bstep (se 1 (by rfl) ⟨577685, by rfl⟩ : syracuseStep 770247 = 1155371) B1155371
theorem B770267 : Blo 766334 770267 := bstep (se 1 (by rfl) ⟨577700, by rfl⟩ : syracuseStep 770267 = 1155401) B1155401
theorem B1458425 : Blo 766334 1458425 := bstep (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) B1093819
theorem B4931927 : Blo 766334 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B17088869 : Blo 766334 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B1294697 : Blo 766334 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B2212339 : Blo 766334 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B2081305 : Blo 766334 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B1295095 : Blo 766334 1295095 := bstep (se 1 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 1295095 = 1942643) B1942643
theorem B2081609 : Blo 766334 2081609 := bstep (se 2 (by rfl) ⟨780603, by rfl⟩ : syracuseStep 2081609 = 1561207) B1561207
theorem B1229675 : Blo 766334 1229675 := bstep (se 1 (by rfl) ⟨922256, by rfl⟩ : syracuseStep 1229675 = 1844513) B1844513
theorem B5260177 : Blo 766334 5260177 := bstep (se 2 (by rfl) ⟨1972566, by rfl⟩ : syracuseStep 5260177 = 3945133) B3945133
theorem B1295291 : Blo 766334 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1295399 : Blo 766334 1295399 := bstep (se 1 (by rfl) ⟨971549, by rfl⟩ : syracuseStep 1295399 = 1943099) B1943099
theorem B3884111 : Blo 766334 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B4146347 : Blo 766334 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B1295689 : Blo 766334 1295689 := bstep (se 2 (by rfl) ⟨485883, by rfl⟩ : syracuseStep 1295689 = 971767) B971767
theorem B1295723 : Blo 766334 1295723 := bstep (se 1 (by rfl) ⟨971792, by rfl⟩ : syracuseStep 1295723 = 1943585) B1943585
theorem B4376051 : Blo 766334 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B1459883 : Blo 766334 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B3884759 : Blo 766334 3884759 := bstep (se 1 (by rfl) ⟨2913569, by rfl⟩ : syracuseStep 3884759 = 5827139) B5827139
theorem B1296121 : Blo 766334 1296121 := bstep (se 2 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 1296121 = 972091) B972091
theorem B18695929 : Blo 766334 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B2770807 : Blo 766334 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B1296391 : Blo 766334 1296391 := bstep (se 1 (by rfl) ⟨972293, by rfl⟩ : syracuseStep 1296391 = 1944587) B1944587
theorem B1460263 : Blo 766334 1460263 := bstep (se 1 (by rfl) ⟨1095197, by rfl⟩ : syracuseStep 1460263 = 2190395) B2190395
theorem B8734877 : Blo 766334 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B1460423 : Blo 766334 1460423 := bstep (se 1 (by rfl) ⟨1095317, by rfl⟩ : syracuseStep 1460423 = 2190635) B2190635
theorem B1296823 : Blo 766334 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B14797241 : Blo 766334 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B9325003 : Blo 766334 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B1297019 : Blo 766334 1297019 := bstep (se 1 (by rfl) ⟨972764, by rfl⟩ : syracuseStep 1297019 = 1945529) B1945529
theorem B14011015 : Blo 766334 14011015 := bstep (se 1 (by rfl) ⟨10508261, by rfl⟩ : syracuseStep 14011015 = 21016523) B21016523
theorem B2771603 : Blo 766334 2771603 := bstep (se 1 (by rfl) ⟨2078702, by rfl⟩ : syracuseStep 2771603 = 4157405) B4157405
theorem B13126373 : Blo 766334 13126373 := bstep (se 4 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 13126373 = 2461195) B2461195
theorem B3689219 : Blo 766334 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B1297417 : Blo 766334 1297417 := bstep (se 2 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 1297417 = 973063) B973063
theorem B5393579 : Blo 766334 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B1297579 : Blo 766334 1297579 := bstep (se 1 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 1297579 = 1946369) B1946369
theorem B1461577 : Blo 766334 1461577 := bstep (se 2 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 1461577 = 1096183) B1096183
theorem B5819849 : Blo 766334 5819849 := bstep (se 2 (by rfl) ⟨2182443, by rfl⟩ : syracuseStep 5819849 = 4364887) B4364887
theorem B1297883 : Blo 766334 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B970319 : Blo 766334 970319 := bstep (se 1 (by rfl) ⟨727739, by rfl⟩ : syracuseStep 970319 = 1455479) B1455479
theorem B1298119 : Blo 766334 1298119 := bstep (se 1 (by rfl) ⟨973589, by rfl⟩ : syracuseStep 1298119 = 1947179) B1947179
theorem B4935491 : Blo 766334 4935491 := bstep (se 1 (by rfl) ⟨3701618, by rfl⟩ : syracuseStep 4935491 = 7403237) B7403237
theorem B1724255 : Blo 766334 1724255 := bstep (se 1 (by rfl) ⟨1293191, by rfl⟩ : syracuseStep 1724255 = 2586383) B2586383
theorem B1298281 : Blo 766334 1298281 := bstep (se 2 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 1298281 = 973711) B973711
theorem B2772911 : Blo 766334 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B1232815 : Blo 766334 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B5525441 : Blo 766334 5525441 := bstep (se 2 (by rfl) ⟨2072040, by rfl⟩ : syracuseStep 5525441 = 4144081) B4144081
theorem B1724435 : Blo 766334 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B4378967 : Blo 766334 4378967 := bstep (se 1 (by rfl) ⟨3284225, by rfl⟩ : syracuseStep 4378967 = 6568451) B6568451
theorem B1724777 : Blo 766334 1724777 := bstep (se 2 (by rfl) ⟨646791, by rfl⟩ : syracuseStep 1724777 = 1293583) B1293583
theorem B1298875 : Blo 766334 1298875 := bstep (se 1 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 1298875 = 1948313) B1948313
theorem B9851341 : Blo 766334 9851341 := bstep (se 3 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 9851341 = 3694253) B3694253
theorem B1298983 : Blo 766334 1298983 := bstep (se 1 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 1298983 = 1948475) B1948475
theorem B3887675 : Blo 766334 3887675 := bstep (se 1 (by rfl) ⟨2915756, by rfl⟩ : syracuseStep 3887675 = 5831513) B5831513
theorem B1036999 : Blo 766334 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B971615 : Blo 766334 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B40555363 : Blo 766334 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1299307 : Blo 766334 1299307 := bstep (se 1 (by rfl) ⟨974480, by rfl⟩ : syracuseStep 1299307 = 1948961) B1948961
theorem B1725371 : Blo 766334 1725371 := bstep (se 1 (by rfl) ⟨1294028, by rfl⟩ : syracuseStep 1725371 = 2588057) B2588057
theorem B8737793 : Blo 766334 8737793 := bstep (se 2 (by rfl) ⟨3276672, by rfl⟩ : syracuseStep 8737793 = 6553345) B6553345
theorem B2774035 : Blo 766334 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B1725497 : Blo 766334 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B3888323 : Blo 766334 3888323 := bstep (se 1 (by rfl) ⟨2916242, by rfl⟩ : syracuseStep 3888323 = 5832485) B5832485
theorem B1725839 : Blo 766334 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B1726163 : Blo 766334 1726163 := bstep (se 1 (by rfl) ⟨1294622, by rfl⟩ : syracuseStep 1726163 = 2589245) B2589245
theorem B1727099 : Blo 766334 1727099 := bstep (se 1 (by rfl) ⟨1295324, by rfl⟩ : syracuseStep 1727099 = 2590649) B2590649
theorem B1727225 : Blo 766334 1727225 := bstep (se 2 (by rfl) ⟨647709, by rfl⟩ : syracuseStep 1727225 = 1295419) B1295419
theorem B91151119 : Blo 766334 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B1727495 : Blo 766334 1727495 := bstep (se 1 (by rfl) ⟨1295621, by rfl⟩ : syracuseStep 1727495 = 2591243) B2591243
theorem B1727567 : Blo 766334 1727567 := bstep (se 1 (by rfl) ⟨1295675, by rfl⟩ : syracuseStep 1727567 = 2591351) B2591351
theorem B5528695 : Blo 766334 5528695 := bstep (se 1 (by rfl) ⟨4146521, by rfl⟩ : syracuseStep 5528695 = 8293043) B8293043
theorem B4152491 : Blo 766334 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B11066615 : Blo 766334 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B974263 : Blo 766334 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B3694025 : Blo 766334 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B1727963 : Blo 766334 1727963 := bstep (se 1 (by rfl) ⟨1295972, by rfl⟩ : syracuseStep 1727963 = 2591945) B2591945
theorem B3694177 : Blo 766334 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B1728431 : Blo 766334 1728431 := bstep (se 1 (by rfl) ⟨1296323, by rfl⟩ : syracuseStep 1728431 = 2592647) B2592647
theorem B4382657 : Blo 766334 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B1728683 : Blo 766334 1728683 := bstep (se 1 (by rfl) ⟨1296512, by rfl⟩ : syracuseStep 1728683 = 2593025) B2593025
theorem B1040735 : Blo 766334 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B1729223 : Blo 766334 1729223 := bstep (se 1 (by rfl) ⟨1296917, by rfl⟩ : syracuseStep 1729223 = 2593835) B2593835
theorem B5530513 : Blo 766334 5530513 := bstep (se 2 (by rfl) ⟨2073942, by rfl⟩ : syracuseStep 5530513 = 4147885) B4147885
theorem B2188367 : Blo 766334 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B1730087 : Blo 766334 1730087 := bstep (se 1 (by rfl) ⟨1297565, by rfl⟩ : syracuseStep 1730087 = 2595131) B2595131
theorem B3892859 : Blo 766334 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B1730411 : Blo 766334 1730411 := bstep (se 1 (by rfl) ⟨1297808, by rfl⟩ : syracuseStep 1730411 = 2595617) B2595617
theorem B1730465 : Blo 766334 1730465 := bstep (se 2 (by rfl) ⟨648924, by rfl⟩ : syracuseStep 1730465 = 1297849) B1297849
theorem B2189369 : Blo 766334 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B2910289 : Blo 766334 2910289 := bstep (se 2 (by rfl) ⟨1091358, by rfl⟩ : syracuseStep 2910289 = 2182717) B2182717
theorem B1108091 : Blo 766334 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B1730807 : Blo 766334 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B2910593 : Blo 766334 2910593 := bstep (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) B2182945
theorem B3500525 : Blo 766334 3500525 := bstep (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) B1312697
theorem B3500603 : Blo 766334 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B8743625 : Blo 766334 8743625 := bstep (se 2 (by rfl) ⟨3278859, by rfl⟩ : syracuseStep 8743625 = 6557719) B6557719
theorem B2911049 : Blo 766334 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B1731401 : Blo 766334 1731401 := bstep (se 2 (by rfl) ⟨649275, by rfl⟩ : syracuseStep 1731401 = 1298551) B1298551
theorem B2911247 : Blo 766334 2911247 := bstep (se 1 (by rfl) ⟨2183435, by rfl⟩ : syracuseStep 2911247 = 4366871) B4366871
theorem B1732193 : Blo 766334 1732193 := bstep (se 2 (by rfl) ⟨649572, by rfl⟩ : syracuseStep 1732193 = 1299145) B1299145
theorem B4910807 : Blo 766334 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B1732535 : Blo 766334 1732535 := bstep (se 1 (by rfl) ⟨1299401, by rfl⟩ : syracuseStep 1732535 = 2598803) B2598803
theorem B3895613 : Blo 766334 3895613 := bstep (se 3 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 3895613 = 1460855) B1460855
theorem B1733129 : Blo 766334 1733129 := bstep (se 2 (by rfl) ⟨649923, by rfl⟩ : syracuseStep 1733129 = 1299847) B1299847
theorem B22147991 : Blo 766334 22147991 := bstep (se 1 (by rfl) ⟨16610993, by rfl⟩ : syracuseStep 22147991 = 33221987) B33221987
theorem B1405883 : Blo 766334 1405883 := bstep (se 1 (by rfl) ⟨1054412, by rfl⟩ : syracuseStep 1405883 = 2108825) B2108825
theorem B2193095 : Blo 766334 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B3274759 : Blo 766334 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2455609 : Blo 766334 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B3897881 : Blo 766334 3897881 := bstep (se 2 (by rfl) ⟨1461705, by rfl⟩ : syracuseStep 3897881 = 2923411) B2923411
theorem B3111709 : Blo 766334 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B2456507 : Blo 766334 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B9993239 : Blo 766334 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B4914371 : Blo 766334 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B2587895 : Blo 766334 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B16579853 : Blo 766334 16579853 := bstep (se 3 (by rfl) ⟨3108722, by rfl⟩ : syracuseStep 16579853 = 6217445) B6217445
theorem B1867303 : Blo 766334 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B13139495 : Blo 766334 13139495 := bstep (se 1 (by rfl) ⟨9854621, by rfl⟩ : syracuseStep 13139495 = 19709243) B19709243
theorem B2588219 : Blo 766334 2588219 := bstep (se 1 (by rfl) ⟨1941164, by rfl⟩ : syracuseStep 2588219 = 3882329) B3882329
theorem B2588489 : Blo 766334 2588489 := bstep (se 2 (by rfl) ⟨970683, by rfl⟩ : syracuseStep 2588489 = 1941367) B1941367
theorem B16023415 : Blo 766334 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B6553619 : Blo 766334 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B7012403 : Blo 766334 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B2949785 : Blo 766334 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B2589407 : Blo 766334 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B2917367 : Blo 766334 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B2589839 : Blo 766334 2589839 := bstep (se 1 (by rfl) ⟨1942379, by rfl⟩ : syracuseStep 2589839 = 3884759) B3884759
theorem B7374017 : Blo 766334 7374017 := bstep (se 2 (by rfl) ⟨2765256, by rfl⟩ : syracuseStep 7374017 = 5530513) B5530513
theorem B7013569 : Blo 766334 7013569 := bstep (se 2 (by rfl) ⟨2630088, by rfl⟩ : syracuseStep 7013569 = 5260177) B5260177
theorem B2459069 : Blo 766334 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B1639943 : Blo 766334 1639943 := bstep (se 1 (by rfl) ⟨1229957, by rfl⟩ : syracuseStep 1639943 = 2459915) B2459915
theorem B9864827 : Blo 766334 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B8750915 : Blo 766334 8750915 := bstep (se 1 (by rfl) ⟨6563186, by rfl⟩ : syracuseStep 8750915 = 13126373) B13126373
theorem B2459479 : Blo 766334 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B2590973 : Blo 766334 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B3279133 : Blo 766334 3279133 := bstep (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) B1229675
theorem B1968475 : Blo 766334 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B1149503 : Blo 766334 1149503 := bstep (se 1 (by rfl) ⟨862127, by rfl⟩ : syracuseStep 1149503 = 1724255) B1724255
theorem B4164169 : Blo 766334 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B1641131 : Blo 766334 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B1149623 : Blo 766334 1149623 := bstep (se 1 (by rfl) ⟨862217, by rfl⟩ : syracuseStep 1149623 = 1724435) B1724435
theorem B2919311 : Blo 766334 2919311 := bstep (se 1 (by rfl) ⟨2189483, by rfl⟩ : syracuseStep 2919311 = 4378967) B4378967
theorem B1149851 : Blo 766334 1149851 := bstep (se 1 (by rfl) ⟨862388, by rfl⟩ : syracuseStep 1149851 = 1724777) B1724777
theorem B2591783 : Blo 766334 2591783 := bstep (se 1 (by rfl) ⟨1943837, by rfl⟩ : syracuseStep 2591783 = 3887675) B3887675
theorem B3279953 : Blo 766334 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B8326259 : Blo 766334 8326259 := bstep (se 1 (by rfl) ⟨6244694, by rfl⟩ : syracuseStep 8326259 = 12489389) B12489389
theorem B1150247 : Blo 766334 1150247 := bstep (se 1 (by rfl) ⟨862685, by rfl⟩ : syracuseStep 1150247 = 1725371) B1725371
theorem B1150331 : Blo 766334 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B2592215 : Blo 766334 2592215 := bstep (se 1 (by rfl) ⟨1944161, by rfl⟩ : syracuseStep 2592215 = 3888323) B3888323
theorem B1150457 : Blo 766334 1150457 := bstep (se 2 (by rfl) ⟨431421, by rfl⟩ : syracuseStep 1150457 = 862843) B862843
theorem B18681353 : Blo 766334 18681353 := bstep (se 2 (by rfl) ⟨7005507, by rfl⟩ : syracuseStep 18681353 = 14011015) B14011015
theorem B1150559 : Blo 766334 1150559 := bstep (se 1 (by rfl) ⟨862919, by rfl⟩ : syracuseStep 1150559 = 1725839) B1725839
theorem B16617221 : Blo 766334 16617221 := bstep (se 4 (by rfl) ⟨1557864, by rfl⟩ : syracuseStep 16617221 = 3115729) B3115729
theorem B1150775 : Blo 766334 1150775 := bstep (se 1 (by rfl) ⟨863081, by rfl⟩ : syracuseStep 1150775 = 1726163) B1726163
theorem B5836859 : Blo 766334 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B1151081 : Blo 766334 1151081 := bstep (se 2 (by rfl) ⟨431655, by rfl⟩ : syracuseStep 1151081 = 863311) B863311
theorem B1151399 : Blo 766334 1151399 := bstep (se 1 (by rfl) ⟨863549, by rfl⟩ : syracuseStep 1151399 = 1727099) B1727099
theorem B1151483 : Blo 766334 1151483 := bstep (se 1 (by rfl) ⟨863612, by rfl⟩ : syracuseStep 1151483 = 1727225) B1727225
theorem B8327731 : Blo 766334 8327731 := bstep (se 1 (by rfl) ⟨6245798, by rfl⟩ : syracuseStep 8327731 = 12491597) B12491597
theorem B1643087 : Blo 766334 1643087 := bstep (se 1 (by rfl) ⟨1232315, by rfl⟩ : syracuseStep 1643087 = 2464631) B2464631
theorem B1151609 : Blo 766334 1151609 := bstep (se 2 (by rfl) ⟨431853, by rfl⟩ : syracuseStep 1151609 = 863707) B863707
theorem B3281579 : Blo 766334 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B1151663 : Blo 766334 1151663 := bstep (se 1 (by rfl) ⟨863747, by rfl⟩ : syracuseStep 1151663 = 1727495) B1727495
theorem B1151711 : Blo 766334 1151711 := bstep (se 1 (by rfl) ⟨863783, by rfl⟩ : syracuseStep 1151711 = 1727567) B1727567
theorem B7377743 : Blo 766334 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B2462683 : Blo 766334 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B1151975 : Blo 766334 1151975 := bstep (se 1 (by rfl) ⟨863981, by rfl⟩ : syracuseStep 1151975 = 1727963) B1727963
theorem B2593889 : Blo 766334 2593889 := bstep (se 2 (by rfl) ⟨972708, by rfl⟩ : syracuseStep 2593889 = 1945417) B1945417
theorem B922843 : Blo 766334 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B1152233 : Blo 766334 1152233 := bstep (se 2 (by rfl) ⟨432087, by rfl⟩ : syracuseStep 1152233 = 864175) B864175
theorem B1643753 : Blo 766334 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B3740915 : Blo 766334 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B1152287 : Blo 766334 1152287 := bstep (se 1 (by rfl) ⟨864215, by rfl⟩ : syracuseStep 1152287 = 1728431) B1728431
theorem B2921771 : Blo 766334 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B1152455 : Blo 766334 1152455 := bstep (se 1 (by rfl) ⟨864341, by rfl⟩ : syracuseStep 1152455 = 1728683) B1728683
theorem B5838317 : Blo 766334 5838317 := bstep (se 3 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 5838317 = 2189369) B2189369
theorem B2954909 : Blo 766334 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B3282619 : Blo 766334 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B1152809 : Blo 766334 1152809 := bstep (se 2 (by rfl) ⟨432303, by rfl⟩ : syracuseStep 1152809 = 864607) B864607
theorem B1152815 : Blo 766334 1152815 := bstep (se 1 (by rfl) ⟨864611, by rfl⟩ : syracuseStep 1152815 = 1729223) B1729223
theorem B1382665 : Blo 766334 1382665 := bstep (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) B1036999
theorem B1153289 : Blo 766334 1153289 := bstep (se 2 (by rfl) ⟨432483, by rfl⟩ : syracuseStep 1153289 = 864967) B864967
theorem B4200815 : Blo 766334 4200815 := bstep (se 1 (by rfl) ⟨3150611, by rfl⟩ : syracuseStep 4200815 = 6301223) B6301223
theorem B1153391 : Blo 766334 1153391 := bstep (se 1 (by rfl) ⟨865043, by rfl⟩ : syracuseStep 1153391 = 1730087) B1730087
theorem B2595239 : Blo 766334 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B54073817 : Blo 766334 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1153607 : Blo 766334 1153607 := bstep (se 1 (by rfl) ⟨865205, by rfl⟩ : syracuseStep 1153607 = 1730411) B1730411
theorem B2595401 : Blo 766334 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B1153643 : Blo 766334 1153643 := bstep (se 1 (by rfl) ⟨865232, by rfl⟩ : syracuseStep 1153643 = 1730465) B1730465
theorem B1153871 : Blo 766334 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B1940395 : Blo 766334 1940395 := bstep (se 1 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 1940395 = 2910593) B2910593
theorem B2333683 : Blo 766334 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B2333735 : Blo 766334 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1940699 : Blo 766334 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B1154267 : Blo 766334 1154267 := bstep (se 1 (by rfl) ⟨865700, by rfl⟩ : syracuseStep 1154267 = 1731401) B1731401
theorem B1940831 : Blo 766334 1940831 := bstep (se 1 (by rfl) ⟨1455623, by rfl⟩ : syracuseStep 1940831 = 2911247) B2911247
theorem B1154441 : Blo 766334 1154441 := bstep (se 2 (by rfl) ⟨432915, by rfl⟩ : syracuseStep 1154441 = 865831) B865831
theorem B12459545 : Blo 766334 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B1842745 : Blo 766334 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B925255 : Blo 766334 925255 := bstep (se 1 (by rfl) ⟨693941, by rfl⟩ : syracuseStep 925255 = 1387883) B1387883
theorem B1154795 : Blo 766334 1154795 := bstep (se 1 (by rfl) ⟨866096, by rfl⟩ : syracuseStep 1154795 = 1732193) B1732193
theorem B5840747 : Blo 766334 5840747 := bstep (se 1 (by rfl) ⟨4380560, by rfl⟩ : syracuseStep 5840747 = 8761121) B8761121
theorem B1155023 : Blo 766334 1155023 := bstep (se 1 (by rfl) ⟨866267, by rfl⟩ : syracuseStep 1155023 = 1732535) B1732535
theorem B4366345 : Blo 766334 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B3285011 : Blo 766334 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B1941529 : Blo 766334 1941529 := bstep (se 2 (by rfl) ⟨728073, by rfl⟩ : syracuseStep 1941529 = 1456147) B1456147
theorem B2597075 : Blo 766334 2597075 := bstep (se 1 (by rfl) ⟨1947806, by rfl⟩ : syracuseStep 2597075 = 3895613) B3895613
theorem B1941833 : Blo 766334 1941833 := bstep (se 2 (by rfl) ⟨728187, by rfl⟩ : syracuseStep 1941833 = 1456375) B1456375
theorem B1155419 : Blo 766334 1155419 := bstep (se 1 (by rfl) ⟨866564, by rfl⟩ : syracuseStep 1155419 = 1733129) B1733129
theorem B2597345 : Blo 766334 2597345 := bstep (se 2 (by rfl) ⟨974004, by rfl⟩ : syracuseStep 2597345 = 1948009) B1948009
theorem B1778399 : Blo 766334 1778399 := bstep (se 1 (by rfl) ⟨1333799, by rfl⟩ : syracuseStep 1778399 = 2667599) B2667599
theorem B2958731 : Blo 766334 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B2598587 : Blo 766334 2598587 := bstep (se 1 (by rfl) ⟨1948940, by rfl⟩ : syracuseStep 2598587 = 3897881) B3897881
theorem B862159 : Blo 766334 862159 := bstep (se 1 (by rfl) ⟨646619, by rfl⟩ : syracuseStep 862159 = 1293239) B1293239
theorem B6662159 : Blo 766334 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B4925569 : Blo 766334 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B11053235 : Blo 766334 11053235 := bstep (se 1 (by rfl) ⟨8289926, by rfl⟩ : syracuseStep 11053235 = 16579853) B16579853
theorem B13117625 : Blo 766334 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B862555 : Blo 766334 862555 := bstep (se 1 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 862555 = 1293833) B1293833
theorem B8759663 : Blo 766334 8759663 := bstep (se 1 (by rfl) ⟨6569747, by rfl⟩ : syracuseStep 8759663 = 13139495) B13139495
theorem B862663 : Blo 766334 862663 := bstep (se 1 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 862663 = 1293995) B1293995
theorem B863023 : Blo 766334 863023 := bstep (se 1 (by rfl) ⟨647267, by rfl⟩ : syracuseStep 863023 = 1294535) B1294535
theorem B1747855 : Blo 766334 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B3287951 : Blo 766334 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B863131 : Blo 766334 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B1944719 : Blo 766334 1944719 := bstep (se 1 (by rfl) ⟨1458539, by rfl⟩ : syracuseStep 1944719 = 2917079) B2917079
theorem B7384283 : Blo 766334 7384283 := bstep (se 1 (by rfl) ⟨5538212, by rfl⟩ : syracuseStep 7384283 = 11076425) B11076425
theorem B1387739 : Blo 766334 1387739 := bstep (se 1 (by rfl) ⟨1040804, by rfl⟩ : syracuseStep 1387739 = 2081609) B2081609
theorem B863527 : Blo 766334 863527 := bstep (se 1 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 863527 = 1295291) B1295291
theorem B863599 : Blo 766334 863599 := bstep (se 1 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 863599 = 1295399) B1295399
theorem B863815 : Blo 766334 863815 := bstep (se 1 (by rfl) ⟨647861, by rfl⟩ : syracuseStep 863815 = 1295723) B1295723
theorem B831151 : Blo 766334 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B3321661 : Blo 766334 3321661 := bstep (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) B1245623
theorem B4370537 : Blo 766334 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B2339027 : Blo 766334 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B13152617 : Blo 766334 13152617 := bstep (se 2 (by rfl) ⟨4932231, by rfl⟩ : syracuseStep 13152617 = 9864463) B9864463
theorem B766375 : Blo 766334 766375 := bstep (se 1 (by rfl) ⟨574781, by rfl⟩ : syracuseStep 766375 = 1149563) B1149563
theorem B864679 : Blo 766334 864679 := bstep (se 1 (by rfl) ⟨648509, by rfl⟩ : syracuseStep 864679 = 1297019) B1297019
theorem B1847735 : Blo 766334 1847735 := bstep (se 1 (by rfl) ⟨1385801, by rfl⟩ : syracuseStep 1847735 = 2771603) B2771603
theorem B766459 : Blo 766334 766459 := bstep (se 1 (by rfl) ⟨574844, by rfl⟩ : syracuseStep 766459 = 1149689) B1149689
theorem B766527 : Blo 766334 766527 := bstep (se 1 (by rfl) ⟨574895, by rfl⟩ : syracuseStep 766527 = 1149791) B1149791
theorem B766535 : Blo 766334 766535 := bstep (se 1 (by rfl) ⟨574901, by rfl⟩ : syracuseStep 766535 = 1149803) B1149803
theorem B766687 : Blo 766334 766687 := bstep (se 1 (by rfl) ⟨575015, by rfl⟩ : syracuseStep 766687 = 1150031) B1150031
theorem B766767 : Blo 766334 766767 := bstep (se 1 (by rfl) ⟨575075, by rfl⟩ : syracuseStep 766767 = 1150151) B1150151
theorem B766875 : Blo 766334 766875 := bstep (se 1 (by rfl) ⟨575156, by rfl⟩ : syracuseStep 766875 = 1150313) B1150313
theorem B766927 : Blo 766334 766927 := bstep (se 1 (by rfl) ⟨575195, by rfl⟩ : syracuseStep 766927 = 1150391) B1150391
theorem B3879899 : Blo 766334 3879899 := bstep (se 1 (by rfl) ⟨2909924, by rfl⟩ : syracuseStep 3879899 = 5819849) B5819849
theorem B766951 : Blo 766334 766951 := bstep (se 1 (by rfl) ⟨575213, by rfl⟩ : syracuseStep 766951 = 1150427) B1150427
theorem B865255 : Blo 766334 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B1946663 : Blo 766334 1946663 := bstep (se 1 (by rfl) ⟨1459997, by rfl⟩ : syracuseStep 1946663 = 2919995) B2919995
theorem B4502585 : Blo 766334 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B3880061 : Blo 766334 3880061 := bstep (se 3 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 3880061 = 1455023) B1455023
theorem B3749021 : Blo 766334 3749021 := bstep (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) B1405883
theorem B3290327 : Blo 766334 3290327 := bstep (se 1 (by rfl) ⟨2467745, by rfl⟩ : syracuseStep 3290327 = 4935491) B4935491
theorem B767263 : Blo 766334 767263 := bstep (se 1 (by rfl) ⟨575447, by rfl⟩ : syracuseStep 767263 = 1150895) B1150895
theorem B3683627 : Blo 766334 3683627 := bstep (se 1 (by rfl) ⟨2762720, by rfl⟩ : syracuseStep 3683627 = 5525441) B5525441
theorem B767323 : Blo 766334 767323 := bstep (se 1 (by rfl) ⟨575492, by rfl⟩ : syracuseStep 767323 = 1150985) B1150985
theorem B767343 : Blo 766334 767343 := bstep (se 1 (by rfl) ⟨575507, by rfl⟩ : syracuseStep 767343 = 1151015) B1151015
theorem B1095049 : Blo 766334 1095049 := bstep (se 2 (by rfl) ⟨410643, by rfl⟩ : syracuseStep 1095049 = 821287) B821287
theorem B1947017 : Blo 766334 1947017 := bstep (se 2 (by rfl) ⟨730131, by rfl⟩ : syracuseStep 1947017 = 1460263) B1460263
theorem B767399 : Blo 766334 767399 := bstep (se 1 (by rfl) ⟨575549, by rfl⟩ : syracuseStep 767399 = 1151099) B1151099
theorem B3880385 : Blo 766334 3880385 := bstep (se 2 (by rfl) ⟨1455144, by rfl⟩ : syracuseStep 3880385 = 2910289) B2910289
theorem B767483 : Blo 766334 767483 := bstep (se 1 (by rfl) ⟨575612, by rfl⟩ : syracuseStep 767483 = 1151225) B1151225
theorem B767551 : Blo 766334 767551 := bstep (se 1 (by rfl) ⟨575663, by rfl⟩ : syracuseStep 767551 = 1151327) B1151327
theorem B767559 : Blo 766334 767559 := bstep (se 1 (by rfl) ⟨575669, by rfl⟩ : syracuseStep 767559 = 1151339) B1151339
theorem B767711 : Blo 766334 767711 := bstep (se 1 (by rfl) ⟨575783, by rfl⟩ : syracuseStep 767711 = 1151567) B1151567
theorem B11056925 : Blo 766334 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B767791 : Blo 766334 767791 := bstep (se 1 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 767791 = 1151687) B1151687
theorem B6993719 : Blo 766334 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B767899 : Blo 766334 767899 := bstep (se 1 (by rfl) ⟨575924, by rfl⟩ : syracuseStep 767899 = 1151849) B1151849
theorem B12433337 : Blo 766334 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B767951 : Blo 766334 767951 := bstep (se 1 (by rfl) ⟨575963, by rfl⟩ : syracuseStep 767951 = 1151927) B1151927
theorem B767975 : Blo 766334 767975 := bstep (se 1 (by rfl) ⟨575981, by rfl⟩ : syracuseStep 767975 = 1151963) B1151963
theorem B768287 : Blo 766334 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B768347 : Blo 766334 768347 := bstep (se 1 (by rfl) ⟨576260, by rfl⟩ : syracuseStep 768347 = 1152521) B1152521
theorem B768367 : Blo 766334 768367 := bstep (se 1 (by rfl) ⟨576275, by rfl⟩ : syracuseStep 768367 = 1152551) B1152551
theorem B768423 : Blo 766334 768423 := bstep (se 1 (by rfl) ⟨576317, by rfl⟩ : syracuseStep 768423 = 1152635) B1152635
theorem B1751507 : Blo 766334 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B768507 : Blo 766334 768507 := bstep (se 1 (by rfl) ⟨576380, by rfl⟩ : syracuseStep 768507 = 1152761) B1152761
theorem B768575 : Blo 766334 768575 := bstep (se 1 (by rfl) ⟨576431, by rfl⟩ : syracuseStep 768575 = 1152863) B1152863
theorem B768583 : Blo 766334 768583 := bstep (se 1 (by rfl) ⟨576437, by rfl⟩ : syracuseStep 768583 = 1152875) B1152875
theorem B8764037 : Blo 766334 8764037 := bstep (se 4 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 8764037 = 1643257) B1643257
theorem B768735 : Blo 766334 768735 := bstep (se 1 (by rfl) ⟨576551, by rfl⟩ : syracuseStep 768735 = 1153103) B1153103
theorem B2079479 : Blo 766334 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B768815 : Blo 766334 768815 := bstep (se 1 (by rfl) ⟨576611, by rfl⟩ : syracuseStep 768815 = 1153223) B1153223
theorem B1948495 : Blo 766334 1948495 := bstep (se 1 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 1948495 = 2922743) B2922743
theorem B768923 : Blo 766334 768923 := bstep (se 1 (by rfl) ⟨576692, by rfl⟩ : syracuseStep 768923 = 1153385) B1153385
theorem B768975 : Blo 766334 768975 := bstep (se 1 (by rfl) ⟨576731, by rfl⟩ : syracuseStep 768975 = 1153463) B1153463
theorem B768999 : Blo 766334 768999 := bstep (se 1 (by rfl) ⟨576749, by rfl⟩ : syracuseStep 768999 = 1153499) B1153499
theorem B1948769 : Blo 766334 1948769 := bstep (se 2 (by rfl) ⟨730788, by rfl⟩ : syracuseStep 1948769 = 1461577) B1461577
theorem B7388279 : Blo 766334 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B1293455 : Blo 766334 1293455 := bstep (se 1 (by rfl) ⟨970091, by rfl⟩ : syracuseStep 1293455 = 1940183) B1940183
theorem B769311 : Blo 766334 769311 := bstep (se 1 (by rfl) ⟨576983, by rfl⟩ : syracuseStep 769311 = 1153967) B1153967
theorem B769371 : Blo 766334 769371 := bstep (se 1 (by rfl) ⟨577028, by rfl⟩ : syracuseStep 769371 = 1154057) B1154057
theorem B769391 : Blo 766334 769391 := bstep (se 1 (by rfl) ⟨577043, by rfl⟩ : syracuseStep 769391 = 1154087) B1154087
theorem B1293691 : Blo 766334 1293691 := bstep (se 1 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 1293691 = 1940537) B1940537
theorem B769447 : Blo 766334 769447 := bstep (se 1 (by rfl) ⟨577085, by rfl⟩ : syracuseStep 769447 = 1154171) B1154171
theorem B2768327 : Blo 766334 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B1949143 : Blo 766334 1949143 := bstep (se 1 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 1949143 = 2923715) B2923715
theorem B769531 : Blo 766334 769531 := bstep (se 1 (by rfl) ⟨577148, by rfl⟩ : syracuseStep 769531 = 1154297) B1154297
theorem B769599 : Blo 766334 769599 := bstep (se 1 (by rfl) ⟨577199, by rfl⟩ : syracuseStep 769599 = 1154399) B1154399
theorem B769607 : Blo 766334 769607 := bstep (se 1 (by rfl) ⟨577205, by rfl⟩ : syracuseStep 769607 = 1154411) B1154411
theorem B769759 : Blo 766334 769759 := bstep (se 1 (by rfl) ⟨577319, by rfl⟩ : syracuseStep 769759 = 1154639) B1154639
theorem B1949447 : Blo 766334 1949447 := bstep (se 1 (by rfl) ⟨1462085, by rfl⟩ : syracuseStep 1949447 = 2924171) B2924171
theorem B769839 : Blo 766334 769839 := bstep (se 1 (by rfl) ⟨577379, by rfl⟩ : syracuseStep 769839 = 1154759) B1154759
theorem B769947 : Blo 766334 769947 := bstep (se 1 (by rfl) ⟨577460, by rfl⟩ : syracuseStep 769947 = 1154921) B1154921
theorem B769999 : Blo 766334 769999 := bstep (se 1 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 769999 = 1154999) B1154999
theorem B770023 : Blo 766334 770023 := bstep (se 1 (by rfl) ⟨577517, by rfl⟩ : syracuseStep 770023 = 1155035) B1155035
theorem B1229419 : Blo 766334 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B1458911 : Blo 766334 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B3293945 : Blo 766334 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B2081555 : Blo 766334 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B1295183 : Blo 766334 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B1296175 : Blo 766334 1296175 := bstep (se 1 (by rfl) ⟨972131, by rfl⟩ : syracuseStep 1296175 = 1944263) B1944263
theorem B1755145 : Blo 766334 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B3950777 : Blo 766334 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B2803997 : Blo 766334 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B14765327 : Blo 766334 14765327 := bstep (se 1 (by rfl) ⟨11073995, by rfl⟩ : syracuseStep 14765327 = 22147991) B22147991
theorem B14732725 : Blo 766334 14732725 := bstep (se 5 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 14732725 = 1381193) B1381193
theorem B4148945 : Blo 766334 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B1462063 : Blo 766334 1462063 := bstep (se 1 (by rfl) ⟨1096547, by rfl⟩ : syracuseStep 1462063 = 2193095) B2193095
theorem B1233161 : Blo 766334 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B971119 : Blo 766334 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B1233263 : Blo 766334 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1298855 : Blo 766334 1298855 := bstep (se 1 (by rfl) ⟨974141, by rfl⟩ : syracuseStep 1298855 = 1948283) B1948283
theorem B1299017 : Blo 766334 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B4215545 : Blo 766334 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B1725263 : Blo 766334 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B23712787 : Blo 766334 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B1725479 : Blo 766334 1725479 := bstep (se 1 (by rfl) ⟨1294109, by rfl⟩ : syracuseStep 1725479 = 2588219) B2588219
theorem B7394429 : Blo 766334 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B1725659 : Blo 766334 1725659 := bstep (se 1 (by rfl) ⟨1294244, by rfl⟩ : syracuseStep 1725659 = 2588489) B2588489
theorem B971995 : Blo 766334 971995 := bstep (se 1 (by rfl) ⟨728996, by rfl⟩ : syracuseStep 971995 = 1457993) B1457993
theorem B1725857 : Blo 766334 1725857 := bstep (se 2 (by rfl) ⟨647196, by rfl⟩ : syracuseStep 1725857 = 1294393) B1294393
theorem B5264801 : Blo 766334 5264801 := bstep (se 2 (by rfl) ⟨1974300, by rfl⟩ : syracuseStep 5264801 = 3948601) B3948601
theorem B4675009 : Blo 766334 4675009 := bstep (se 2 (by rfl) ⟨1753128, by rfl⟩ : syracuseStep 4675009 = 3506257) B3506257
theorem B6641099 : Blo 766334 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B3888647 : Blo 766334 3888647 := bstep (se 1 (by rfl) ⟨2916485, by rfl⟩ : syracuseStep 3888647 = 5832971) B5832971
theorem B11392579 : Blo 766334 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B1726415 : Blo 766334 1726415 := bstep (se 1 (by rfl) ⟨1294811, by rfl⟩ : syracuseStep 1726415 = 2589623) B2589623
theorem B3889133 : Blo 766334 3889133 := bstep (se 3 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 3889133 = 1458425) B1458425
theorem B2775073 : Blo 766334 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2775293 : Blo 766334 2775293 := bstep (se 3 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 2775293 = 1040735) B1040735
theorem B1726793 : Blo 766334 1726793 := bstep (se 2 (by rfl) ⟨647547, by rfl⟩ : syracuseStep 1726793 = 1295095) B1295095
theorem B1726811 : Blo 766334 1726811 := bstep (se 1 (by rfl) ⟨1295108, by rfl⟩ : syracuseStep 1726811 = 2590217) B2590217
theorem B3889619 : Blo 766334 3889619 := bstep (se 1 (by rfl) ⟨2917214, by rfl⟩ : syracuseStep 3889619 = 5834429) B5834429
theorem B5823251 : Blo 766334 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B3889943 : Blo 766334 3889943 := bstep (se 1 (by rfl) ⟨2917457, by rfl⟩ : syracuseStep 3889943 = 5834915) B5834915
theorem B973615 : Blo 766334 973615 := bstep (se 1 (by rfl) ⟨730211, by rfl⟩ : syracuseStep 973615 = 1460423) B1460423
theorem B1727387 : Blo 766334 1727387 := bstep (se 1 (by rfl) ⟨1295540, by rfl⟩ : syracuseStep 1727387 = 2591081) B2591081
theorem B1727585 : Blo 766334 1727585 := bstep (se 2 (by rfl) ⟨647844, by rfl⟩ : syracuseStep 1727585 = 1295689) B1295689
theorem B1727783 : Blo 766334 1727783 := bstep (se 1 (by rfl) ⟨1295837, by rfl⟩ : syracuseStep 1727783 = 2591675) B2591675
theorem B4382201 : Blo 766334 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B1728161 : Blo 766334 1728161 := bstep (se 2 (by rfl) ⟨648060, by rfl⟩ : syracuseStep 1728161 = 1296121) B1296121
theorem B24927905 : Blo 766334 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B3497789 : Blo 766334 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B3694409 : Blo 766334 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B2187137 : Blo 766334 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B15392693 : Blo 766334 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B1728521 : Blo 766334 1728521 := bstep (se 2 (by rfl) ⟨648195, by rfl⟩ : syracuseStep 1728521 = 1296391) B1296391
theorem B2187593 : Blo 766334 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B3891563 : Blo 766334 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B1728935 : Blo 766334 1728935 := bstep (se 1 (by rfl) ⟨1296701, by rfl⟩ : syracuseStep 1728935 = 2593403) B2593403
theorem B1729043 : Blo 766334 1729043 := bstep (se 1 (by rfl) ⟨1296782, by rfl⟩ : syracuseStep 1729043 = 2593565) B2593565
theorem B1729097 : Blo 766334 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B5825195 : Blo 766334 5825195 := bstep (se 1 (by rfl) ⟨4368896, by rfl⟩ : syracuseStep 5825195 = 8737793) B8737793
theorem B1729511 : Blo 766334 1729511 := bstep (se 1 (by rfl) ⟨1297133, by rfl⟩ : syracuseStep 1729511 = 2594267) B2594267
theorem B4383841 : Blo 766334 4383841 := bstep (se 2 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 4383841 = 3287881) B3287881
theorem B1729889 : Blo 766334 1729889 := bstep (se 2 (by rfl) ⟨648708, by rfl⟩ : syracuseStep 1729889 = 1297417) B1297417
theorem B9332111 : Blo 766334 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B1729979 : Blo 766334 1729979 := bstep (se 1 (by rfl) ⟨1297484, by rfl⟩ : syracuseStep 1729979 = 2594969) B2594969
theorem B1730105 : Blo 766334 1730105 := bstep (se 2 (by rfl) ⟨648789, by rfl⟩ : syracuseStep 1730105 = 1297579) B1297579
theorem B878303 : Blo 766334 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B3893021 : Blo 766334 3893021 := bstep (se 3 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 3893021 = 1459883) B1459883
theorem B1730771 : Blo 766334 1730771 := bstep (se 1 (by rfl) ⟨1298078, by rfl⟩ : syracuseStep 1730771 = 2596157) B2596157
theorem B1730825 : Blo 766334 1730825 := bstep (se 2 (by rfl) ⟨649059, by rfl⟩ : syracuseStep 1730825 = 1298119) B1298119
theorem B1731041 : Blo 766334 1731041 := bstep (se 2 (by rfl) ⟨649140, by rfl⟩ : syracuseStep 1731041 = 1298281) B1298281
theorem B6580925 : Blo 766334 6580925 := bstep (se 3 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 6580925 = 2467847) B2467847
theorem B3500819 : Blo 766334 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B1731347 : Blo 766334 1731347 := bstep (se 1 (by rfl) ⟨1298510, by rfl⟩ : syracuseStep 1731347 = 2597021) B2597021
theorem B2190235 : Blo 766334 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B1731707 : Blo 766334 1731707 := bstep (se 1 (by rfl) ⟨1298780, by rfl⟩ : syracuseStep 1731707 = 2597561) B2597561
theorem B1731833 : Blo 766334 1731833 := bstep (se 2 (by rfl) ⟨649437, by rfl⟩ : syracuseStep 1731833 = 1298875) B1298875
theorem B13135121 : Blo 766334 13135121 := bstep (se 2 (by rfl) ⟨4925670, by rfl⟩ : syracuseStep 13135121 = 9851341) B9851341
theorem B1731977 : Blo 766334 1731977 := bstep (se 2 (by rfl) ⟨649491, by rfl⟩ : syracuseStep 1731977 = 1298983) B1298983
theorem B1732103 : Blo 766334 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B1732283 : Blo 766334 1732283 := bstep (se 1 (by rfl) ⟨1299212, by rfl⟩ : syracuseStep 1732283 = 2598425) B2598425
theorem B1732409 : Blo 766334 1732409 := bstep (se 2 (by rfl) ⟨649653, by rfl⟩ : syracuseStep 1732409 = 1299307) B1299307
theorem B3371033 : Blo 766334 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B3698713 : Blo 766334 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B2191465 : Blo 766334 2191465 := bstep (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) B1643599
theorem B1733039 : Blo 766334 1733039 := bstep (se 1 (by rfl) ⟨1299779, by rfl⟩ : syracuseStep 1733039 = 2599559) B2599559
theorem B1733075 : Blo 766334 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B5829083 : Blo 766334 5829083 := bstep (se 1 (by rfl) ⟨4371812, by rfl⟩ : syracuseStep 5829083 = 8743625) B8743625
theorem B1733183 : Blo 766334 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B36008819 : Blo 766334 36008819 := bstep (se 1 (by rfl) ⟨27006614, by rfl⟩ : syracuseStep 36008819 = 54013229) B54013229
theorem B3273871 : Blo 766334 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B2913479 : Blo 766334 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B3274145 : Blo 766334 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B14382877 : Blo 766334 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B13301597 : Blo 766334 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B121534825 : Blo 766334 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B7371593 : Blo 766334 7371593 := bstep (se 2 (by rfl) ⟨2764347, by rfl⟩ : syracuseStep 7371593 = 5528695) B5528695
theorem B2587517 : Blo 766334 2587517 := bstep (se 3 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 2587517 = 970319) B970319
theorem B4684787 : Blo 766334 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B2587787 : Blo 766334 2587787 := bstep (se 1 (by rfl) ⟨1940840, by rfl⟩ : syracuseStep 2587787 = 3881681) B3881681
theorem B1637671 : Blo 766334 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B3898691 : Blo 766334 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B2489737 : Blo 766334 2489737 := bstep (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) B1867303
theorem B3276247 : Blo 766334 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B4488787 : Blo 766334 4488787 := bstep (se 1 (by rfl) ⟨3366590, by rfl⟩ : syracuseStep 4488787 = 6733181) B6733181
theorem B7012001 : Blo 766334 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B2916107 : Blo 766334 2916107 := bstep (se 1 (by rfl) ⟨2187080, by rfl⟩ : syracuseStep 2916107 = 4374161) B4374161
theorem B3899177 : Blo 766334 3899177 := bstep (se 2 (by rfl) ⟨1462191, by rfl⟩ : syracuseStep 3899177 = 2924383) B2924383
theorem B2457391 : Blo 766334 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B3505967 : Blo 766334 3505967 := bstep (se 1 (by rfl) ⟨2629475, by rfl⟩ : syracuseStep 3505967 = 5258951) B5258951
theorem B3276605 : Blo 766334 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B21364553 : Blo 766334 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B2588705 : Blo 766334 2588705 := bstep (se 2 (by rfl) ⟨970764, by rfl⟩ : syracuseStep 2588705 = 1941529) B1941529
theorem B1966523 : Blo 766334 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B2195963 : Blo 766334 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B4916011 : Blo 766334 4916011 := bstep (se 1 (by rfl) ⟨3687008, by rfl⟩ : syracuseStep 4916011 = 7374017) B7374017
theorem B1639225 : Blo 766334 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B1639379 : Blo 766334 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B5833943 : Blo 766334 5833943 := bstep (se 1 (by rfl) ⟨4375457, by rfl⟩ : syracuseStep 5833943 = 8750915) B8750915
theorem B1869331 : Blo 766334 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B12454235 : Blo 766334 12454235 := bstep (se 1 (by rfl) ⟨9340676, by rfl⟩ : syracuseStep 12454235 = 18681353) B18681353
theorem B3279305 : Blo 766334 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B11078147 : Blo 766334 11078147 := bstep (se 1 (by rfl) ⟨8308610, by rfl⟩ : syracuseStep 11078147 = 16617221) B16617221
theorem B1149545 : Blo 766334 1149545 := bstep (se 2 (by rfl) ⟨431079, by rfl⟩ : syracuseStep 1149545 = 862159) B862159
theorem B822107 : Blo 766334 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B1150073 : Blo 766334 1150073 := bstep (se 2 (by rfl) ⟨431277, by rfl⟩ : syracuseStep 1150073 = 862555) B862555
theorem B2624633 : Blo 766334 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B1150175 : Blo 766334 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B4918495 : Blo 766334 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B1150217 : Blo 766334 1150217 := bstep (se 2 (by rfl) ⟨431331, by rfl⟩ : syracuseStep 1150217 = 862663) B862663
theorem B1150319 : Blo 766334 1150319 := bstep (se 1 (by rfl) ⟨862739, by rfl⟩ : syracuseStep 1150319 = 1725479) B1725479
theorem B1150439 : Blo 766334 1150439 := bstep (se 1 (by rfl) ⟨862829, by rfl⟩ : syracuseStep 1150439 = 1725659) B1725659
theorem B1150571 : Blo 766334 1150571 := bstep (se 1 (by rfl) ⟨862928, by rfl⟩ : syracuseStep 1150571 = 1725857) B1725857
theorem B3509867 : Blo 766334 3509867 := bstep (se 1 (by rfl) ⟨2632400, by rfl⟩ : syracuseStep 3509867 = 5264801) B5264801
theorem B4427399 : Blo 766334 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B2592431 : Blo 766334 2592431 := bstep (se 1 (by rfl) ⟨1944323, by rfl⟩ : syracuseStep 2592431 = 3888647) B3888647
theorem B1150697 : Blo 766334 1150697 := bstep (se 2 (by rfl) ⟨431511, by rfl⟩ : syracuseStep 1150697 = 863023) B863023
theorem B1969939 : Blo 766334 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B2330473 : Blo 766334 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1150841 : Blo 766334 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B2920313 : Blo 766334 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B1150943 : Blo 766334 1150943 := bstep (se 1 (by rfl) ⟨863207, by rfl⟩ : syracuseStep 1150943 = 1726415) B1726415
theorem B2592755 : Blo 766334 2592755 := bstep (se 1 (by rfl) ⟨1944566, by rfl⟩ : syracuseStep 2592755 = 3889133) B3889133
theorem B1151195 : Blo 766334 1151195 := bstep (se 1 (by rfl) ⟨863396, by rfl⟩ : syracuseStep 1151195 = 1726793) B1726793
theorem B1151207 : Blo 766334 1151207 := bstep (se 1 (by rfl) ⟨863405, by rfl⟩ : syracuseStep 1151207 = 1726811) B1726811
theorem B2593079 : Blo 766334 2593079 := bstep (se 1 (by rfl) ⟨1944809, by rfl⟩ : syracuseStep 2593079 = 3889619) B3889619
theorem B36049211 : Blo 766334 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1151369 : Blo 766334 1151369 := bstep (se 2 (by rfl) ⟨431763, by rfl⟩ : syracuseStep 1151369 = 863527) B863527
theorem B1151465 : Blo 766334 1151465 := bstep (se 2 (by rfl) ⟨431799, by rfl⟩ : syracuseStep 1151465 = 863599) B863599
theorem B2593295 : Blo 766334 2593295 := bstep (se 1 (by rfl) ⟨1944971, by rfl⟩ : syracuseStep 2593295 = 3889943) B3889943
theorem B1151591 : Blo 766334 1151591 := bstep (se 1 (by rfl) ⟨863693, by rfl⟩ : syracuseStep 1151591 = 1727387) B1727387
theorem B1151723 : Blo 766334 1151723 := bstep (se 1 (by rfl) ⟨863792, by rfl⟩ : syracuseStep 1151723 = 1727585) B1727585
theorem B1151753 : Blo 766334 1151753 := bstep (se 2 (by rfl) ⟨431907, by rfl⟩ : syracuseStep 1151753 = 863815) B863815
theorem B1151855 : Blo 766334 1151855 := bstep (se 1 (by rfl) ⟨863891, by rfl⟩ : syracuseStep 1151855 = 1727783) B1727783
theorem B2921467 : Blo 766334 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B4428881 : Blo 766334 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B1152107 : Blo 766334 1152107 := bstep (se 1 (by rfl) ⟨864080, by rfl⟩ : syracuseStep 1152107 = 1728161) B1728161
theorem B16618603 : Blo 766334 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B2462939 : Blo 766334 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B1152347 : Blo 766334 1152347 := bstep (se 1 (by rfl) ⟨864260, by rfl⟩ : syracuseStep 1152347 = 1728521) B1728521
theorem B2921953 : Blo 766334 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B2594375 : Blo 766334 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B1152623 : Blo 766334 1152623 := bstep (se 1 (by rfl) ⟨864467, by rfl⟩ : syracuseStep 1152623 = 1728935) B1728935
theorem B1152695 : Blo 766334 1152695 := bstep (se 1 (by rfl) ⟨864521, by rfl⟩ : syracuseStep 1152695 = 1729043) B1729043
theorem B1152731 : Blo 766334 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B1185599 : Blo 766334 1185599 := bstep (se 1 (by rfl) ⟨889199, by rfl⟩ : syracuseStep 1185599 = 1778399) B1778399
theorem B1152905 : Blo 766334 1152905 := bstep (se 2 (by rfl) ⟨432339, by rfl⟩ : syracuseStep 1152905 = 864679) B864679
theorem B1153007 : Blo 766334 1153007 := bstep (se 1 (by rfl) ⟨864755, by rfl⟩ : syracuseStep 1153007 = 1729511) B1729511
theorem B1153259 : Blo 766334 1153259 := bstep (se 1 (by rfl) ⟨864944, by rfl⟩ : syracuseStep 1153259 = 1729889) B1729889
theorem B1972487 : Blo 766334 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B1153319 : Blo 766334 1153319 := bstep (se 1 (by rfl) ⟨864989, by rfl⟩ : syracuseStep 1153319 = 1729979) B1729979
theorem B1153403 : Blo 766334 1153403 := bstep (se 1 (by rfl) ⟨865052, by rfl⟩ : syracuseStep 1153403 = 1730105) B1730105
theorem B4921829 : Blo 766334 4921829 := bstep (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) B922843
theorem B2595347 : Blo 766334 2595347 := bstep (se 1 (by rfl) ⟨1946510, by rfl⟩ : syracuseStep 2595347 = 3893021) B3893021
theorem B3283577 : Blo 766334 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B1153673 : Blo 766334 1153673 := bstep (se 2 (by rfl) ⟨432627, by rfl⟩ : syracuseStep 1153673 = 865255) B865255
theorem B1153847 : Blo 766334 1153847 := bstep (se 1 (by rfl) ⟨865385, by rfl⟩ : syracuseStep 1153847 = 1730771) B1730771
theorem B1153883 : Blo 766334 1153883 := bstep (se 1 (by rfl) ⟨865412, by rfl⟩ : syracuseStep 1153883 = 1730825) B1730825
theorem B4365161 : Blo 766334 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B5839775 : Blo 766334 5839775 := bstep (se 1 (by rfl) ⟨4379831, by rfl⟩ : syracuseStep 5839775 = 8759663) B8759663
theorem B1154027 : Blo 766334 1154027 := bstep (se 1 (by rfl) ⟨865520, by rfl⟩ : syracuseStep 1154027 = 1731041) B1731041
theorem B1154231 : Blo 766334 1154231 := bstep (se 1 (by rfl) ⟨865673, by rfl⟩ : syracuseStep 1154231 = 1731347) B1731347
theorem B2333879 : Blo 766334 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B6233345 : Blo 766334 6233345 := bstep (se 2 (by rfl) ⟨2337504, by rfl⟩ : syracuseStep 6233345 = 4675009) B4675009
theorem B5840261 : Blo 766334 5840261 := bstep (se 4 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 5840261 = 1095049) B1095049
theorem B1154471 : Blo 766334 1154471 := bstep (se 1 (by rfl) ⟨865853, by rfl⟩ : syracuseStep 1154471 = 1731707) B1731707
theorem B4922855 : Blo 766334 4922855 := bstep (se 1 (by rfl) ⟨3692141, by rfl⟩ : syracuseStep 4922855 = 7384283) B7384283
theorem B1154555 : Blo 766334 1154555 := bstep (se 1 (by rfl) ⟨865916, by rfl⟩ : syracuseStep 1154555 = 1731833) B1731833
theorem B8756747 : Blo 766334 8756747 := bstep (se 1 (by rfl) ⟨6567560, by rfl⟩ : syracuseStep 8756747 = 13135121) B13135121
theorem B1154651 : Blo 766334 1154651 := bstep (se 1 (by rfl) ⟨865988, by rfl⟩ : syracuseStep 1154651 = 1731977) B1731977
theorem B1154735 : Blo 766334 1154735 := bstep (se 1 (by rfl) ⟨866051, by rfl⟩ : syracuseStep 1154735 = 1732103) B1732103
theorem B19177169 : Blo 766334 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B1154855 : Blo 766334 1154855 := bstep (se 1 (by rfl) ⟨866141, by rfl⟩ : syracuseStep 1154855 = 1732283) B1732283
theorem B1154939 : Blo 766334 1154939 := bstep (se 1 (by rfl) ⟨866204, by rfl⟩ : syracuseStep 1154939 = 1732409) B1732409
theorem B44965813 : Blo 766334 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B1155359 : Blo 766334 1155359 := bstep (se 1 (by rfl) ⟨866519, by rfl⟩ : syracuseStep 1155359 = 1733039) B1733039
theorem B1155383 : Blo 766334 1155383 := bstep (se 1 (by rfl) ⟨866537, by rfl⟩ : syracuseStep 1155383 = 1733075) B1733075
theorem B1843553 : Blo 766334 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B1155455 : Blo 766334 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B162046433 : Blo 766334 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B2499347 : Blo 766334 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B1942319 : Blo 766334 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B4432805 : Blo 766334 4432805 := bstep (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) B831151
theorem B2597993 : Blo 766334 2597993 := bstep (se 2 (by rfl) ⟨974247, by rfl⟩ : syracuseStep 2597993 = 1948495) B1948495
theorem B4662479 : Blo 766334 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B5842691 : Blo 766334 5842691 := bstep (se 1 (by rfl) ⟨4382018, by rfl⟩ : syracuseStep 5842691 = 8764037) B8764037
theorem B1386319 : Blo 766334 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B3319649 : Blo 766334 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B4368329 : Blo 766334 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B2598857 : Blo 766334 2598857 := bstep (se 2 (by rfl) ⟨974571, by rfl⟩ : syracuseStep 2598857 = 1949143) B1949143
theorem B3123191 : Blo 766334 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B4925519 : Blo 766334 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B862303 : Blo 766334 862303 := bstep (se 1 (by rfl) ⟨646727, by rfl⟩ : syracuseStep 862303 = 1293455) B1293455
theorem B2599127 : Blo 766334 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B1845551 : Blo 766334 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B1944071 : Blo 766334 1944071 := bstep (se 1 (by rfl) ⟨1458053, by rfl⟩ : syracuseStep 1944071 = 2916107) B2916107
theorem B2599451 : Blo 766334 2599451 := bstep (se 1 (by rfl) ⟨1949588, by rfl⟩ : syracuseStep 2599451 = 3899177) B3899177
theorem B2337311 : Blo 766334 2337311 := bstep (se 1 (by rfl) ⟨1752983, by rfl⟩ : syracuseStep 2337311 = 3505967) B3505967
theorem B4369079 : Blo 766334 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B1387703 : Blo 766334 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B863455 : Blo 766334 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B1944911 : Blo 766334 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B3288701 : Blo 766334 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B1093295 : Blo 766334 1093295 := bstep (se 1 (by rfl) ⟨819971, by rfl⟩ : syracuseStep 1093295 = 1639943) B1639943
theorem B2633851 : Blo 766334 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B5845121 : Blo 766334 5845121 := bstep (se 2 (by rfl) ⟨2191920, by rfl⟩ : syracuseStep 5845121 = 4383841) B4383841
theorem B9351425 : Blo 766334 9351425 := bstep (se 2 (by rfl) ⟨3506784, by rfl⟩ : syracuseStep 9351425 = 7013569) B7013569
theorem B766335 : Blo 766334 766335 := bstep (se 1 (by rfl) ⟨574751, by rfl⟩ : syracuseStep 766335 = 1149503) B1149503
theorem B1094087 : Blo 766334 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B766415 : Blo 766334 766415 := bstep (se 1 (by rfl) ⟨574811, by rfl⟩ : syracuseStep 766415 = 1149623) B1149623
theorem B1946207 : Blo 766334 1946207 := bstep (se 1 (by rfl) ⟨1459655, by rfl⟩ : syracuseStep 1946207 = 2919311) B2919311
theorem B766567 : Blo 766334 766567 := bstep (se 1 (by rfl) ⟨574925, by rfl⟩ : syracuseStep 766567 = 1149851) B1149851
theorem B5550839 : Blo 766334 5550839 := bstep (se 1 (by rfl) ⟨4163129, by rfl⟩ : syracuseStep 5550839 = 8326259) B8326259
theorem B9843551 : Blo 766334 9843551 := bstep (se 1 (by rfl) ⟨7382663, by rfl⟩ : syracuseStep 9843551 = 14765327) B14765327
theorem B766831 : Blo 766334 766831 := bstep (se 1 (by rfl) ⟨575123, by rfl⟩ : syracuseStep 766831 = 1150247) B1150247
theorem B766887 : Blo 766334 766887 := bstep (se 1 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 766887 = 1150331) B1150331
theorem B766971 : Blo 766334 766971 := bstep (se 1 (by rfl) ⟨575228, by rfl⟩ : syracuseStep 766971 = 1150457) B1150457
theorem B767039 : Blo 766334 767039 := bstep (se 1 (by rfl) ⟨575279, by rfl⟩ : syracuseStep 767039 = 1150559) B1150559
theorem B2765963 : Blo 766334 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B767183 : Blo 766334 767183 := bstep (se 1 (by rfl) ⟨575387, by rfl⟩ : syracuseStep 767183 = 1150775) B1150775
theorem B2340193 : Blo 766334 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B767387 : Blo 766334 767387 := bstep (se 1 (by rfl) ⟨575540, by rfl⟩ : syracuseStep 767387 = 1151081) B1151081
theorem B12006893 : Blo 766334 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B6567425 : Blo 766334 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B767599 : Blo 766334 767599 := bstep (se 1 (by rfl) ⟨575699, by rfl⟩ : syracuseStep 767599 = 1151399) B1151399
theorem B865903 : Blo 766334 865903 := bstep (se 1 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 865903 = 1298855) B1298855
theorem B767655 : Blo 766334 767655 := bstep (se 1 (by rfl) ⟨575741, by rfl⟩ : syracuseStep 767655 = 1151483) B1151483
theorem B4372177 : Blo 766334 4372177 := bstep (se 2 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 4372177 = 3279133) B3279133
theorem B866011 : Blo 766334 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B1095391 : Blo 766334 1095391 := bstep (se 1 (by rfl) ⟨821543, by rfl⟩ : syracuseStep 1095391 = 1643087) B1643087
theorem B767739 : Blo 766334 767739 := bstep (se 1 (by rfl) ⟨575804, by rfl⟩ : syracuseStep 767739 = 1151609) B1151609
theorem B767775 : Blo 766334 767775 := bstep (se 1 (by rfl) ⟨575831, by rfl⟩ : syracuseStep 767775 = 1151663) B1151663
theorem B767807 : Blo 766334 767807 := bstep (se 1 (by rfl) ⟨575855, by rfl⟩ : syracuseStep 767807 = 1151711) B1151711
theorem B9975773 : Blo 766334 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B767983 : Blo 766334 767983 := bstep (se 1 (by rfl) ⟨575987, by rfl⟩ : syracuseStep 767983 = 1151975) B1151975
theorem B4929619 : Blo 766334 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B5552225 : Blo 766334 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B768155 : Blo 766334 768155 := bstep (se 1 (by rfl) ⟨576116, by rfl⟩ : syracuseStep 768155 = 1152233) B1152233
theorem B768191 : Blo 766334 768191 := bstep (se 1 (by rfl) ⟨576143, by rfl⟩ : syracuseStep 768191 = 1152287) B1152287
theorem B1947847 : Blo 766334 1947847 := bstep (se 1 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 1947847 = 2921771) B2921771
theorem B768303 : Blo 766334 768303 := bstep (se 1 (by rfl) ⟨576227, by rfl⟩ : syracuseStep 768303 = 1152455) B1152455
theorem B768539 : Blo 766334 768539 := bstep (se 1 (by rfl) ⟨576404, by rfl⟩ : syracuseStep 768539 = 1152809) B1152809
theorem B768543 : Blo 766334 768543 := bstep (se 1 (by rfl) ⟨576407, by rfl⟩ : syracuseStep 768543 = 1152815) B1152815
theorem B1850195 : Blo 766334 1850195 := bstep (se 1 (by rfl) ⟨1387646, by rfl⟩ : syracuseStep 1850195 = 2775293) B2775293
theorem B768859 : Blo 766334 768859 := bstep (se 1 (by rfl) ⟨576644, by rfl⟩ : syracuseStep 768859 = 1153289) B1153289
theorem B2800543 : Blo 766334 2800543 := bstep (se 1 (by rfl) ⟨2100407, by rfl⟩ : syracuseStep 2800543 = 4200815) B4200815
theorem B768927 : Blo 766334 768927 := bstep (se 1 (by rfl) ⟨576695, by rfl⟩ : syracuseStep 768927 = 1153391) B1153391
theorem B769071 : Blo 766334 769071 := bstep (se 1 (by rfl) ⟨576803, by rfl⟩ : syracuseStep 769071 = 1153607) B1153607
theorem B769095 : Blo 766334 769095 := bstep (se 1 (by rfl) ⟨576821, by rfl⟩ : syracuseStep 769095 = 1153643) B1153643
theorem B3882167 : Blo 766334 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B769247 : Blo 766334 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B19643633 : Blo 766334 19643633 := bstep (se 2 (by rfl) ⟨7366362, by rfl⟩ : syracuseStep 19643633 = 14732725) B14732725
theorem B2342141 : Blo 766334 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B1555823 : Blo 766334 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B1293799 : Blo 766334 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B769511 : Blo 766334 769511 := bstep (se 1 (by rfl) ⟨577133, by rfl⟩ : syracuseStep 769511 = 1154267) B1154267
theorem B1293887 : Blo 766334 1293887 := bstep (se 1 (by rfl) ⟨970415, by rfl⟩ : syracuseStep 1293887 = 1940831) B1940831
theorem B769627 : Blo 766334 769627 := bstep (se 1 (by rfl) ⟨577220, by rfl⟩ : syracuseStep 769627 = 1154441) B1154441
theorem B8306363 : Blo 766334 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B1949417 : Blo 766334 1949417 := bstep (se 2 (by rfl) ⟨731031, by rfl⟩ : syracuseStep 1949417 = 1462063) B1462063
theorem B769863 : Blo 766334 769863 := bstep (se 1 (by rfl) ⟨577397, by rfl⟩ : syracuseStep 769863 = 1154795) B1154795
theorem B1458091 : Blo 766334 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B770015 : Blo 766334 770015 := bstep (se 1 (by rfl) ⟨577511, by rfl⟩ : syracuseStep 770015 = 1155023) B1155023
theorem B4931617 : Blo 766334 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B1294555 : Blo 766334 1294555 := bstep (se 1 (by rfl) ⟨970916, by rfl⟩ : syracuseStep 1294555 = 1941833) B1941833
theorem B1458395 : Blo 766334 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B770279 : Blo 766334 770279 := bstep (se 1 (by rfl) ⟨577709, by rfl⟩ : syracuseStep 770279 = 1155419) B1155419
theorem B3883463 : Blo 766334 3883463 := bstep (se 1 (by rfl) ⟨2912597, by rfl⟩ : syracuseStep 3883463 = 5825195) B5825195
theorem B1294825 : Blo 766334 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B4441439 : Blo 766334 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B1295993 : Blo 766334 1295993 := bstep (se 2 (by rfl) ⟨485997, by rfl⟩ : syracuseStep 1295993 = 971995) B971995
theorem B15190105 : Blo 766334 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B1296479 : Blo 766334 1296479 := bstep (se 1 (by rfl) ⟨972359, by rfl⟩ : syracuseStep 1296479 = 1944719) B1944719
theorem B4376825 : Blo 766334 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B2247355 : Blo 766334 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B1559351 : Blo 766334 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B8768411 : Blo 766334 8768411 := bstep (se 1 (by rfl) ⟨6576308, by rfl⟩ : syracuseStep 8768411 = 13152617) B13152617
theorem B1231823 : Blo 766334 1231823 := bstep (se 1 (by rfl) ⟨923867, by rfl⟩ : syracuseStep 1231823 = 1847735) B1847735
theorem B3886055 : Blo 766334 3886055 := bstep (se 1 (by rfl) ⟨2914541, by rfl⟩ : syracuseStep 3886055 = 5829083) B5829083
theorem B24005879 : Blo 766334 24005879 := bstep (se 1 (by rfl) ⟨18004409, by rfl⟩ : syracuseStep 24005879 = 36008819) B36008819
theorem B1297775 : Blo 766334 1297775 := bstep (se 1 (by rfl) ⟨973331, by rfl⟩ : syracuseStep 1297775 = 1946663) B1946663
theorem B1298011 : Blo 766334 1298011 := bstep (se 1 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 1298011 = 1947017) B1947017
theorem B2182763 : Blo 766334 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B1298153 : Blo 766334 1298153 := bstep (se 2 (by rfl) ⟨486807, by rfl⟩ : syracuseStep 1298153 = 973615) B973615
theorem B8867731 : Blo 766334 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B1167671 : Blo 766334 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B2183561 : Blo 766334 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B1724921 : Blo 766334 1724921 := bstep (se 2 (by rfl) ⟨646845, by rfl⟩ : syracuseStep 1724921 = 1293691) B1293691
theorem B1725011 : Blo 766334 1725011 := bstep (se 1 (by rfl) ⟨1293758, by rfl⟩ : syracuseStep 1725011 = 2587517) B2587517
theorem B1299179 : Blo 766334 1299179 := bstep (se 1 (by rfl) ⟨974384, by rfl⟩ : syracuseStep 1299179 = 1948769) B1948769
theorem B1725191 : Blo 766334 1725191 := bstep (se 1 (by rfl) ⟨1293893, by rfl⟩ : syracuseStep 1725191 = 2587787) B2587787
theorem B1233673 : Blo 766334 1233673 := bstep (se 2 (by rfl) ⟨462627, by rfl⟩ : syracuseStep 1233673 = 925255) B925255
theorem B5985049 : Blo 766334 5985049 := bstep (se 2 (by rfl) ⟨2244393, by rfl⟩ : syracuseStep 5985049 = 4488787) B4488787
theorem B9327437 : Blo 766334 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B4674667 : Blo 766334 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B41047181 : Blo 766334 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B1299631 : Blo 766334 1299631 := bstep (se 1 (by rfl) ⟨974723, by rfl⟩ : syracuseStep 1299631 = 1949447) B1949447
theorem B2184403 : Blo 766334 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B14243035 : Blo 766334 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B5821793 : Blo 766334 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B4674935 : Blo 766334 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B1726271 : Blo 766334 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B1726559 : Blo 766334 1726559 := bstep (se 1 (by rfl) ⟨1294919, by rfl⟩ : syracuseStep 1726559 = 2589839) B2589839
theorem B6576551 : Blo 766334 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B1727315 : Blo 766334 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B3890429 : Blo 766334 3890429 := bstep (se 3 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 3890429 = 1458911) B1458911
theorem B1727855 : Blo 766334 1727855 := bstep (se 1 (by rfl) ⟨1295891, by rfl⟩ : syracuseStep 1727855 = 2591783) B2591783
theorem B1728143 : Blo 766334 1728143 := bstep (se 1 (by rfl) ⟨1296107, by rfl⟩ : syracuseStep 1728143 = 2592215) B2592215
theorem B1728233 : Blo 766334 1728233 := bstep (se 2 (by rfl) ⟨648087, by rfl⟩ : syracuseStep 1728233 = 1296175) B1296175
theorem B3891239 : Blo 766334 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B2187719 : Blo 766334 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B4383341 : Blo 766334 4383341 := bstep (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) B1643753
theorem B1729259 : Blo 766334 1729259 := bstep (se 1 (by rfl) ⟨1296944, by rfl⟩ : syracuseStep 1729259 = 2593889) B2593889
theorem B3892211 : Blo 766334 3892211 := bstep (se 1 (by rfl) ⟨2919158, by rfl⟩ : syracuseStep 3892211 = 5838317) B5838317
theorem B1730159 : Blo 766334 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B1730267 : Blo 766334 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B29485133 : Blo 766334 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B3893831 : Blo 766334 3893831 := bstep (se 1 (by rfl) ⟨2920373, by rfl⟩ : syracuseStep 3893831 = 5840747) B5840747
theorem B2190007 : Blo 766334 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B1731383 : Blo 766334 1731383 := bstep (se 1 (by rfl) ⟨1298537, by rfl⟩ : syracuseStep 1731383 = 2597075) B2597075
theorem B1731563 : Blo 766334 1731563 := bstep (se 1 (by rfl) ⟨1298672, by rfl⟩ : syracuseStep 1731563 = 2597345) B2597345
theorem B11103641 : Blo 766334 11103641 := bstep (se 2 (by rfl) ⟨4163865, by rfl⟩ : syracuseStep 11103641 = 8327731) B8327731
theorem B6221407 : Blo 766334 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B1732391 : Blo 766334 1732391 := bstep (se 1 (by rfl) ⟨1299293, by rfl⟩ : syracuseStep 1732391 = 2598587) B2598587
theorem B31617049 : Blo 766334 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B7368823 : Blo 766334 7368823 := bstep (se 1 (by rfl) ⟨5526617, by rfl⟩ : syracuseStep 7368823 = 11053235) B11053235
theorem B8745083 : Blo 766334 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B4387283 : Blo 766334 4387283 := bstep (se 1 (by rfl) ⟨3290462, by rfl⟩ : syracuseStep 4387283 = 6580925) B6580925
theorem B2191967 : Blo 766334 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B3700097 : Blo 766334 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2913691 : Blo 766334 2913691 := bstep (se 1 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 2913691 = 4370537) B4370537
theorem B8746541 : Blo 766334 8746541 := bstep (se 3 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 8746541 = 3279953) B3279953
theorem B3700637 : Blo 766334 3700637 := bstep (se 3 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 3700637 = 1387739) B1387739
theorem B2586599 : Blo 766334 2586599 := bstep (se 1 (by rfl) ⟨1939949, by rfl⟩ : syracuseStep 2586599 = 3879899) B3879899
theorem B2586707 : Blo 766334 2586707 := bstep (se 1 (by rfl) ⟨1940030, by rfl⟩ : syracuseStep 2586707 = 3880061) B3880061
theorem B2193551 : Blo 766334 2193551 := bstep (se 1 (by rfl) ⟨1645163, by rfl⟩ : syracuseStep 2193551 = 3290327) B3290327
theorem B2455751 : Blo 766334 2455751 := bstep (se 1 (by rfl) ⟨1841813, by rfl⟩ : syracuseStep 2455751 = 3683627) B3683627
theorem B2586923 : Blo 766334 2586923 := bstep (se 1 (by rfl) ⟨1940192, by rfl⟩ : syracuseStep 2586923 = 3880385) B3880385
theorem B2587193 : Blo 766334 2587193 := bstep (se 2 (by rfl) ⟨970197, by rfl⟩ : syracuseStep 2587193 = 1940395) B1940395
theorem B8288891 : Blo 766334 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B3111577 : Blo 766334 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B4914395 : Blo 766334 4914395 := bstep (se 1 (by rfl) ⟨3685796, by rfl⟩ : syracuseStep 4914395 = 7371593) B7371593
theorem B2456993 : Blo 766334 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B3276521 : Blo 766334 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B2588975 : Blo 766334 2588975 := bstep (se 1 (by rfl) ⟨1941731, by rfl⟩ : syracuseStep 2588975 = 3883463) B3883463
theorem B6554681 : Blo 766334 6554681 := bstep (se 2 (by rfl) ⟨2458005, by rfl⟩ : syracuseStep 6554681 = 4916011) B4916011
theorem B5244061 : Blo 766334 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B2917565 : Blo 766334 2917565 := bstep (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) B1094087
theorem B2917883 : Blo 766334 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B821215 : Blo 766334 821215 := bstep (se 1 (by rfl) ⟨615911, by rfl⟩ : syracuseStep 821215 = 1231823) B1231823
theorem B2590703 : Blo 766334 2590703 := bstep (se 1 (by rfl) ⟨1943027, by rfl⟩ : syracuseStep 2590703 = 3886055) B3886055
theorem B2492441 : Blo 766334 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B20253473 : Blo 766334 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B1149737 : Blo 766334 1149737 := bstep (se 2 (by rfl) ⟨431151, by rfl⟩ : syracuseStep 1149737 = 862303) B862303
theorem B1149947 : Blo 766334 1149947 := bstep (se 1 (by rfl) ⟨862460, by rfl⟩ : syracuseStep 1149947 = 1724921) B1724921
theorem B1150007 : Blo 766334 1150007 := bstep (se 1 (by rfl) ⟨862505, by rfl⟩ : syracuseStep 1150007 = 1725011) B1725011
theorem B1150127 : Blo 766334 1150127 := bstep (se 1 (by rfl) ⟨862595, by rfl⟩ : syracuseStep 1150127 = 1725191) B1725191
theorem B2952587 : Blo 766334 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B27364787 : Blo 766334 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B1641959 : Blo 766334 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B2920009 : Blo 766334 2920009 := bstep (se 2 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 2920009 = 2190007) B2190007
theorem B1150847 : Blo 766334 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B790399 : Blo 766334 790399 := bstep (se 1 (by rfl) ⟨592799, by rfl⟩ : syracuseStep 790399 = 1185599) B1185599
theorem B1151039 : Blo 766334 1151039 := bstep (se 1 (by rfl) ⟨863279, by rfl⟩ : syracuseStep 1151039 = 1726559) B1726559
theorem B1314991 : Blo 766334 1314991 := bstep (se 1 (by rfl) ⟨986243, by rfl⟩ : syracuseStep 1314991 = 1972487) B1972487
theorem B1151273 : Blo 766334 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B6557993 : Blo 766334 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B3281219 : Blo 766334 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B1151543 : Blo 766334 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B8295209 : Blo 766334 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B2593619 : Blo 766334 2593619 := bstep (se 1 (by rfl) ⟨1945214, by rfl⟩ : syracuseStep 2593619 = 3890429) B3890429
theorem B1151903 : Blo 766334 1151903 := bstep (se 1 (by rfl) ⟨863927, by rfl⟩ : syracuseStep 1151903 = 1727855) B1727855
theorem B3281903 : Blo 766334 3281903 := bstep (se 1 (by rfl) ⟨2461427, by rfl⟩ : syracuseStep 3281903 = 4922855) B4922855
theorem B5837831 : Blo 766334 5837831 := bstep (se 1 (by rfl) ⟨4378373, by rfl⟩ : syracuseStep 5837831 = 8756747) B8756747
theorem B1152095 : Blo 766334 1152095 := bstep (se 1 (by rfl) ⟨864071, by rfl⟩ : syracuseStep 1152095 = 1728143) B1728143
theorem B1152155 : Blo 766334 1152155 := bstep (se 1 (by rfl) ⟨864116, by rfl⟩ : syracuseStep 1152155 = 1728233) B1728233
theorem B2594159 : Blo 766334 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B3511801 : Blo 766334 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B2922227 : Blo 766334 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B1152839 : Blo 766334 1152839 := bstep (se 1 (by rfl) ⟨864629, by rfl⟩ : syracuseStep 1152839 = 1729259) B1729259
theorem B2955203 : Blo 766334 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B2594807 : Blo 766334 2594807 := bstep (se 1 (by rfl) ⟨1946105, by rfl⟩ : syracuseStep 2594807 = 3892211) B3892211
theorem B4921469 : Blo 766334 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B1153439 : Blo 766334 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B1153511 : Blo 766334 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B3283679 : Blo 766334 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B22158137 : Blo 766334 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B6232889 : Blo 766334 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B2595887 : Blo 766334 2595887 := bstep (se 1 (by rfl) ⟨1946915, by rfl⟩ : syracuseStep 2595887 = 3893831) B3893831
theorem B3120257 : Blo 766334 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B1154255 : Blo 766334 1154255 := bstep (se 1 (by rfl) ⟨865691, by rfl⟩ : syracuseStep 1154255 = 1731383) B1731383
theorem B1154375 : Blo 766334 1154375 := bstep (se 1 (by rfl) ⟨865781, by rfl⟩ : syracuseStep 1154375 = 1731563) B1731563
theorem B1154537 : Blo 766334 1154537 := bstep (se 2 (by rfl) ⟨432951, by rfl⟩ : syracuseStep 1154537 = 865903) B865903
theorem B1154681 : Blo 766334 1154681 := bstep (se 2 (by rfl) ⟨433005, by rfl⟩ : syracuseStep 1154681 = 866011) B866011
theorem B1154927 : Blo 766334 1154927 := bstep (se 1 (by rfl) ⟨866195, by rfl⟩ : syracuseStep 1154927 = 1732391) B1732391
theorem B6234283 : Blo 766334 6234283 := bstep (se 1 (by rfl) ⟨4675712, by rfl⟩ : syracuseStep 6234283 = 9351425) B9351425
theorem B2597129 : Blo 766334 2597129 := bstep (se 2 (by rfl) ⟨973923, by rfl⟩ : syracuseStep 2597129 = 1947847) B1947847
theorem B2924855 : Blo 766334 2924855 := bstep (se 1 (by rfl) ⟨2193641, by rfl⟩ : syracuseStep 2924855 = 4387283) B4387283
theorem B6562367 : Blo 766334 6562367 := bstep (se 1 (by rfl) ⟨4921775, by rfl⟩ : syracuseStep 6562367 = 9843551) B9843551
theorem B1843975 : Blo 766334 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B2466731 : Blo 766334 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B8004595 : Blo 766334 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B2467091 : Blo 766334 2467091 := bstep (se 1 (by rfl) ⟨1850318, by rfl⟩ : syracuseStep 2467091 = 3700637) B3700637
theorem B11806397 : Blo 766334 11806397 := bstep (se 3 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 11806397 = 4427399) B4427399
theorem B862591 : Blo 766334 862591 := bstep (se 1 (by rfl) ⟨646943, by rfl⟩ : syracuseStep 862591 = 1293887) B1293887
theorem B1944121 : Blo 766334 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B2960959 : Blo 766334 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B863995 : Blo 766334 863995 := bstep (se 1 (by rfl) ⟨647996, by rfl⟩ : syracuseStep 863995 = 1295993) B1295993
theorem B864319 : Blo 766334 864319 := bstep (se 1 (by rfl) ⟨648239, by rfl⟩ : syracuseStep 864319 = 1296479) B1296479
theorem B8302823 : Blo 766334 8302823 := bstep (se 1 (by rfl) ⟨6227117, by rfl⟩ : syracuseStep 8302823 = 12454235) B12454235
theorem B7385431 : Blo 766334 7385431 := bstep (se 1 (by rfl) ⟨5539073, by rfl⟩ : syracuseStep 7385431 = 11078147) B11078147
theorem B766363 : Blo 766334 766363 := bstep (se 1 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 766363 = 1149545) B1149545
theorem B5845607 : Blo 766334 5845607 := bstep (se 1 (by rfl) ⟨4384205, by rfl⟩ : syracuseStep 5845607 = 8768411) B8768411
theorem B6664925 : Blo 766334 6664925 := bstep (se 3 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 6664925 = 2499347) B2499347
theorem B766715 : Blo 766334 766715 := bstep (se 1 (by rfl) ⟨575036, by rfl⟩ : syracuseStep 766715 = 1150073) B1150073
theorem B1749755 : Blo 766334 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B766783 : Blo 766334 766783 := bstep (se 1 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 766783 = 1150175) B1150175
theorem B16003919 : Blo 766334 16003919 := bstep (se 1 (by rfl) ⟨12002939, by rfl⟩ : syracuseStep 16003919 = 24005879) B24005879
theorem B766811 : Blo 766334 766811 := bstep (se 1 (by rfl) ⟨575108, by rfl⟩ : syracuseStep 766811 = 1150217) B1150217
theorem B766879 : Blo 766334 766879 := bstep (se 1 (by rfl) ⟨575159, by rfl⟩ : syracuseStep 766879 = 1150319) B1150319
theorem B865183 : Blo 766334 865183 := bstep (se 1 (by rfl) ⟨648887, by rfl⟩ : syracuseStep 865183 = 1297775) B1297775
theorem B766959 : Blo 766334 766959 := bstep (se 1 (by rfl) ⟨575219, by rfl⟩ : syracuseStep 766959 = 1150439) B1150439
theorem B1455175 : Blo 766334 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B767047 : Blo 766334 767047 := bstep (se 1 (by rfl) ⟨575285, by rfl⟩ : syracuseStep 767047 = 1150571) B1150571
theorem B2339911 : Blo 766334 2339911 := bstep (se 1 (by rfl) ⟨1754933, by rfl⟩ : syracuseStep 2339911 = 3509867) B3509867
theorem B1848425 : Blo 766334 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B767131 : Blo 766334 767131 := bstep (se 1 (by rfl) ⟨575348, by rfl⟩ : syracuseStep 767131 = 1150697) B1150697
theorem B865435 : Blo 766334 865435 := bstep (se 1 (by rfl) ⟨649076, by rfl⟩ : syracuseStep 865435 = 1298153) B1298153
theorem B4371677 : Blo 766334 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B767227 : Blo 766334 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B1946875 : Blo 766334 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B767295 : Blo 766334 767295 := bstep (se 1 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 767295 = 1150943) B1150943
theorem B767463 : Blo 766334 767463 := bstep (se 1 (by rfl) ⟨575597, by rfl⟩ : syracuseStep 767463 = 1151195) B1151195
theorem B767471 : Blo 766334 767471 := bstep (se 1 (by rfl) ⟨575603, by rfl⟩ : syracuseStep 767471 = 1151207) B1151207
theorem B24032807 : Blo 766334 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B1455707 : Blo 766334 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B767579 : Blo 766334 767579 := bstep (se 1 (by rfl) ⟨575684, by rfl⟩ : syracuseStep 767579 = 1151369) B1151369
theorem B767643 : Blo 766334 767643 := bstep (se 1 (by rfl) ⟨575732, by rfl⟩ : syracuseStep 767643 = 1151465) B1151465
theorem B767727 : Blo 766334 767727 := bstep (se 1 (by rfl) ⟨575795, by rfl⟩ : syracuseStep 767727 = 1151591) B1151591
theorem B767815 : Blo 766334 767815 := bstep (se 1 (by rfl) ⟨575861, by rfl⟩ : syracuseStep 767815 = 1151723) B1151723
theorem B866119 : Blo 766334 866119 := bstep (se 1 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 866119 = 1299179) B1299179
theorem B767835 : Blo 766334 767835 := bstep (se 1 (by rfl) ⟨575876, by rfl⟩ : syracuseStep 767835 = 1151753) B1151753
theorem B12433277 : Blo 766334 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B767903 : Blo 766334 767903 := bstep (se 1 (by rfl) ⟨575927, by rfl⟩ : syracuseStep 767903 = 1151855) B1151855
theorem B768071 : Blo 766334 768071 := bstep (se 1 (by rfl) ⟨576053, by rfl⟩ : syracuseStep 768071 = 1152107) B1152107
theorem B16595077 : Blo 766334 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B768231 : Blo 766334 768231 := bstep (se 1 (by rfl) ⟨576173, by rfl⟩ : syracuseStep 768231 = 1152347) B1152347
theorem B3881195 : Blo 766334 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B12466493 : Blo 766334 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B768415 : Blo 766334 768415 := bstep (se 1 (by rfl) ⟨576311, by rfl⟩ : syracuseStep 768415 = 1152623) B1152623
theorem B768463 : Blo 766334 768463 := bstep (se 1 (by rfl) ⟨576347, by rfl⟩ : syracuseStep 768463 = 1152695) B1152695
theorem B768487 : Blo 766334 768487 := bstep (se 1 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 768487 = 1152731) B1152731
theorem B768603 : Blo 766334 768603 := bstep (se 1 (by rfl) ⟨576452, by rfl⟩ : syracuseStep 768603 = 1152905) B1152905
theorem B768671 : Blo 766334 768671 := bstep (se 1 (by rfl) ⟨576503, by rfl⟩ : syracuseStep 768671 = 1153007) B1153007
theorem B768839 : Blo 766334 768839 := bstep (se 1 (by rfl) ⟨576629, by rfl⟩ : syracuseStep 768839 = 1153259) B1153259
theorem B768879 : Blo 766334 768879 := bstep (se 1 (by rfl) ⟨576659, by rfl⟩ : syracuseStep 768879 = 1153319) B1153319
theorem B768935 : Blo 766334 768935 := bstep (se 1 (by rfl) ⟨576701, by rfl⟩ : syracuseStep 768935 = 1153403) B1153403
theorem B769115 : Blo 766334 769115 := bstep (se 1 (by rfl) ⟨576836, by rfl⟩ : syracuseStep 769115 = 1153673) B1153673
theorem B769231 : Blo 766334 769231 := bstep (se 1 (by rfl) ⟨576923, by rfl⟩ : syracuseStep 769231 = 1153847) B1153847
theorem B769255 : Blo 766334 769255 := bstep (se 1 (by rfl) ⟨576941, by rfl⟩ : syracuseStep 769255 = 1153883) B1153883
theorem B769351 : Blo 766334 769351 := bstep (se 1 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 769351 = 1154027) B1154027
theorem B1555919 : Blo 766334 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B769487 : Blo 766334 769487 := bstep (se 1 (by rfl) ⟨577115, by rfl⟩ : syracuseStep 769487 = 1154231) B1154231
theorem B769647 : Blo 766334 769647 := bstep (se 1 (by rfl) ⟨577235, by rfl⟩ : syracuseStep 769647 = 1154471) B1154471
theorem B769703 : Blo 766334 769703 := bstep (se 1 (by rfl) ⟨577277, by rfl⟩ : syracuseStep 769703 = 1154555) B1154555
theorem B769767 : Blo 766334 769767 := bstep (se 1 (by rfl) ⟨577325, by rfl⟩ : syracuseStep 769767 = 1154651) B1154651
theorem B769823 : Blo 766334 769823 := bstep (se 1 (by rfl) ⟨577367, by rfl⟩ : syracuseStep 769823 = 1154735) B1154735
theorem B769903 : Blo 766334 769903 := bstep (se 1 (by rfl) ⟨577427, by rfl⟩ : syracuseStep 769903 = 1154855) B1154855
theorem B769959 : Blo 766334 769959 := bstep (se 1 (by rfl) ⟨577469, by rfl⟩ : syracuseStep 769959 = 1154939) B1154939
theorem B42156065 : Blo 766334 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B770239 : Blo 766334 770239 := bstep (se 1 (by rfl) ⟨577679, by rfl⟩ : syracuseStep 770239 = 1155359) B1155359
theorem B770255 : Blo 766334 770255 := bstep (se 1 (by rfl) ⟨577691, by rfl⟩ : syracuseStep 770255 = 1155383) B1155383
theorem B1229035 : Blo 766334 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B770303 : Blo 766334 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B1458479 : Blo 766334 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B1294879 : Blo 766334 1294879 := bstep (se 1 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 1294879 = 1942319) B1942319
theorem B7980065 : Blo 766334 7980065 := bstep (se 2 (by rfl) ⟨2992524, by rfl⟩ : syracuseStep 7980065 = 5985049) B5985049
theorem B2213099 : Blo 766334 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B2082127 : Blo 766334 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B18990713 : Blo 766334 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B1296047 : Blo 766334 1296047 := bstep (se 1 (by rfl) ⟨972035, by rfl⟩ : syracuseStep 1296047 = 1944071) B1944071
theorem B1558207 : Blo 766334 1558207 := bstep (se 1 (by rfl) ⟨1168655, by rfl⟩ : syracuseStep 1558207 = 2337311) B2337311
theorem B3884921 : Blo 766334 3884921 := bstep (se 2 (by rfl) ⟨1456845, by rfl⟩ : syracuseStep 3884921 = 2913691) B2913691
theorem B1296607 : Blo 766334 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B1460521 : Blo 766334 1460521 := bstep (se 2 (by rfl) ⟨547695, by rfl⟩ : syracuseStep 1460521 = 1095391) B1095391
theorem B6572825 : Blo 766334 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B1297471 : Blo 766334 1297471 := bstep (se 1 (by rfl) ⟨973103, by rfl⟩ : syracuseStep 1297471 = 1946207) B1946207
theorem B1461311 : Blo 766334 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B4378283 : Blo 766334 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B1724399 : Blo 766334 1724399 := bstep (se 1 (by rfl) ⟨1293299, by rfl⟩ : syracuseStep 1724399 = 2586599) B2586599
theorem B1724471 : Blo 766334 1724471 := bstep (se 1 (by rfl) ⟨1293353, by rfl⟩ : syracuseStep 1724471 = 2586707) B2586707
theorem B1462367 : Blo 766334 1462367 := bstep (se 1 (by rfl) ⟨1096775, by rfl⟩ : syracuseStep 1462367 = 2193551) B2193551
theorem B10506341 : Blo 766334 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B1724615 : Blo 766334 1724615 := bstep (se 1 (by rfl) ⟨1293461, by rfl⟩ : syracuseStep 1724615 = 2586923) B2586923
theorem B8769869 : Blo 766334 8769869 := bstep (se 3 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 8769869 = 3288701) B3288701
theorem B1724795 : Blo 766334 1724795 := bstep (se 1 (by rfl) ⟨1293596, by rfl⟩ : syracuseStep 1724795 = 2587193) B2587193
theorem B5525927 : Blo 766334 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B51139117 : Blo 766334 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B1233463 : Blo 766334 1233463 := bstep (se 1 (by rfl) ⟨925097, by rfl⟩ : syracuseStep 1233463 = 1850195) B1850195
theorem B1725065 : Blo 766334 1725065 := bstep (se 2 (by rfl) ⟨646899, by rfl⟩ : syracuseStep 1725065 = 1293799) B1293799
theorem B13095755 : Blo 766334 13095755 := bstep (se 1 (by rfl) ⟨9821816, by rfl⟩ : syracuseStep 13095755 = 19643633) B19643633
theorem B1561427 : Blo 766334 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1037215 : Blo 766334 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B2184347 : Blo 766334 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B1299611 : Blo 766334 1299611 := bstep (se 1 (by rfl) ⟨974708, by rfl⟩ : syracuseStep 1299611 = 1949417) B1949417
theorem B59954417 : Blo 766334 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B1725803 : Blo 766334 1725803 := bstep (se 1 (by rfl) ⟨1294352, by rfl⟩ : syracuseStep 1725803 = 2588705) B2588705
theorem B6575489 : Blo 766334 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B972263 : Blo 766334 972263 := bstep (se 1 (by rfl) ⟨729197, by rfl⟩ : syracuseStep 972263 = 1458395) B1458395
theorem B1726073 : Blo 766334 1726073 := bstep (se 2 (by rfl) ⟨647277, by rfl⟩ : syracuseStep 1726073 = 1294555) B1294555
theorem B1463975 : Blo 766334 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B1726433 : Blo 766334 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B3889295 : Blo 766334 3889295 := bstep (se 1 (by rfl) ⟨2916971, by rfl⟩ : syracuseStep 3889295 = 5833943) B5833943
theorem B2185633 : Blo 766334 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B2186203 : Blo 766334 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B1039567 : Blo 766334 1039567 := bstep (se 1 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 1039567 = 1559351) B1559351
theorem B1728287 : Blo 766334 1728287 := bstep (se 1 (by rfl) ⟨1296215, by rfl⟩ : syracuseStep 1728287 = 2592431) B2592431
theorem B1728503 : Blo 766334 1728503 := bstep (se 1 (by rfl) ⟨1296377, by rfl⟩ : syracuseStep 1728503 = 2592755) B2592755
theorem B778447 : Blo 766334 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B1728719 : Blo 766334 1728719 := bstep (se 1 (by rfl) ⟨1296539, by rfl⟩ : syracuseStep 1728719 = 2593079) B2593079
theorem B1728863 : Blo 766334 1728863 := bstep (se 1 (by rfl) ⟨1296647, by rfl⟩ : syracuseStep 1728863 = 2593295) B2593295
theorem B6218291 : Blo 766334 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B11985893 : Blo 766334 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B1729583 : Blo 766334 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B6579589 : Blo 766334 6579589 := bstep (se 4 (by rfl) ⟨616836, by rfl⟩ : syracuseStep 6579589 = 1233673) B1233673
theorem B4384367 : Blo 766334 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B1730231 : Blo 766334 1730231 := bstep (se 1 (by rfl) ⟨1297673, by rfl⟩ : syracuseStep 1730231 = 2595347) B2595347
theorem B2189051 : Blo 766334 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B2910107 : Blo 766334 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B3893183 : Blo 766334 3893183 := bstep (se 1 (by rfl) ⟨2919887, by rfl⟩ : syracuseStep 3893183 = 5839775) B5839775
theorem B1730681 : Blo 766334 1730681 := bstep (se 2 (by rfl) ⟨649005, by rfl⟩ : syracuseStep 1730681 = 1298011) B1298011
theorem B4155563 : Blo 766334 4155563 := bstep (se 1 (by rfl) ⟨3116672, by rfl⟩ : syracuseStep 4155563 = 6233345) B6233345
theorem B3893507 : Blo 766334 3893507 := bstep (se 1 (by rfl) ⟨2920130, by rfl⟩ : syracuseStep 3893507 = 5840261) B5840261
theorem B3107297 : Blo 766334 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B11823641 : Blo 766334 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B9825097 : Blo 766334 9825097 := bstep (se 2 (by rfl) ⟨3684411, by rfl⟩ : syracuseStep 9825097 = 7368823) B7368823
theorem B108030955 : Blo 766334 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B1731995 : Blo 766334 1731995 := bstep (se 1 (by rfl) ⟨1298996, by rfl⟩ : syracuseStep 1731995 = 2597993) B2597993
theorem B3895127 : Blo 766334 3895127 := bstep (se 1 (by rfl) ⟨2921345, by rfl⟩ : syracuseStep 3895127 = 5842691) B5842691
theorem B2912219 : Blo 766334 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B1732571 : Blo 766334 1732571 := bstep (se 1 (by rfl) ⟨1299428, by rfl⟩ : syracuseStep 1732571 = 2598857) B2598857
theorem B3895289 : Blo 766334 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B19656755 : Blo 766334 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B1732751 : Blo 766334 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B1732841 : Blo 766334 1732841 := bstep (se 2 (by rfl) ⟨649815, by rfl⟩ : syracuseStep 1732841 = 1299631) B1299631
theorem B2912537 : Blo 766334 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B1732967 : Blo 766334 1732967 := bstep (se 1 (by rfl) ⟨1299725, by rfl⟩ : syracuseStep 1732967 = 2599451) B2599451
theorem B2912719 : Blo 766334 2912719 := bstep (se 1 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 2912719 = 4369079) B4369079
theorem B3895937 : Blo 766334 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B2192285 : Blo 766334 2192285 := bstep (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) B822107
theorem B7402427 : Blo 766334 7402427 := bstep (se 1 (by rfl) ⟨5551820, by rfl⟩ : syracuseStep 7402427 = 11103641) B11103641
theorem B5829569 : Blo 766334 5829569 := bstep (se 2 (by rfl) ⟨2186088, by rfl⟩ : syracuseStep 5829569 = 4372177) B4372177
theorem B5830055 : Blo 766334 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B3896747 : Blo 766334 3896747 := bstep (se 1 (by rfl) ⟨2922560, by rfl⟩ : syracuseStep 3896747 = 5845121) B5845121
theorem B3700541 : Blo 766334 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B3700559 : Blo 766334 3700559 := bstep (se 1 (by rfl) ⟨2775419, by rfl⟩ : syracuseStep 3700559 = 5550839) B5550839
theorem B5831027 : Blo 766334 5831027 := bstep (se 1 (by rfl) ⟨4373270, by rfl⟩ : syracuseStep 5831027 = 8746541) B8746541
theorem B3734057 : Blo 766334 3734057 := bstep (se 2 (by rfl) ⟨1400271, by rfl⟩ : syracuseStep 3734057 = 2800543) B2800543
theorem B6650515 : Blo 766334 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B3701483 : Blo 766334 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B1637167 : Blo 766334 1637167 := bstep (se 1 (by rfl) ⟨1227875, by rfl⟩ : syracuseStep 1637167 = 2455751) B2455751
theorem B2915453 : Blo 766334 2915453 := bstep (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) B1093295
theorem B2588111 : Blo 766334 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B3276263 : Blo 766334 3276263 := bstep (se 1 (by rfl) ⟨2457197, by rfl⟩ : syracuseStep 3276263 = 4914395) B4914395
theorem B1637995 : Blo 766334 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B5537575 : Blo 766334 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B1638713 : Blo 766334 1638713 := bstep (se 2 (by rfl) ⟨614517, by rfl⟩ : syracuseStep 1638713 = 1229035) B1229035
theorem B1475399 : Blo 766334 1475399 := bstep (se 1 (by rfl) ⟨1106549, by rfl⟩ : syracuseStep 1475399 = 2213099) B2213099
theorem B2458633 : Blo 766334 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2589947 : Blo 766334 2589947 := bstep (se 1 (by rfl) ⟨1942460, by rfl⟩ : syracuseStep 2589947 = 3884921) B3884921
theorem B13502315 : Blo 766334 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B1968391 : Blo 766334 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B2918855 : Blo 766334 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B1149599 : Blo 766334 1149599 := bstep (se 1 (by rfl) ⟨862199, by rfl⟩ : syracuseStep 1149599 = 1724399) B1724399
theorem B1149647 : Blo 766334 1149647 := bstep (se 1 (by rfl) ⟨862235, by rfl⟩ : syracuseStep 1149647 = 1724471) B1724471
theorem B1149743 : Blo 766334 1149743 := bstep (se 1 (by rfl) ⟨862307, by rfl⟩ : syracuseStep 1149743 = 1724615) B1724615
theorem B1149863 : Blo 766334 1149863 := bstep (se 1 (by rfl) ⟨862397, by rfl⟩ : syracuseStep 1149863 = 1724795) B1724795
theorem B1150043 : Blo 766334 1150043 := bstep (se 1 (by rfl) ⟨862532, by rfl⟩ : syracuseStep 1150043 = 1725065) B1725065
theorem B1150121 : Blo 766334 1150121 := bstep (se 2 (by rfl) ⟨431295, by rfl⟩ : syracuseStep 1150121 = 862591) B862591
theorem B2592161 : Blo 766334 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B1150535 : Blo 766334 1150535 := bstep (se 1 (by rfl) ⟨862901, by rfl⟩ : syracuseStep 1150535 = 1725803) B1725803
theorem B1150715 : Blo 766334 1150715 := bstep (se 1 (by rfl) ⟨863036, by rfl⟩ : syracuseStep 1150715 = 1726073) B1726073
theorem B2592701 : Blo 766334 2592701 := bstep (se 3 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 2592701 = 972263) B972263
theorem B1970135 : Blo 766334 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B1150955 : Blo 766334 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B3280979 : Blo 766334 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B2592863 : Blo 766334 2592863 := bstep (se 1 (by rfl) ⟨1944647, by rfl⟩ : syracuseStep 2592863 = 3889295) B3889295
theorem B1151993 : Blo 766334 1151993 := bstep (se 2 (by rfl) ⟨431997, by rfl⟩ : syracuseStep 1151993 = 863995) B863995
theorem B1053865 : Blo 766334 1053865 := bstep (se 2 (by rfl) ⟨395199, by rfl⟩ : syracuseStep 1053865 = 790399) B790399
theorem B1152191 : Blo 766334 1152191 := bstep (se 1 (by rfl) ⟨864143, by rfl⟩ : syracuseStep 1152191 = 1728287) B1728287
theorem B1152335 : Blo 766334 1152335 := bstep (se 1 (by rfl) ⟨864251, by rfl⟩ : syracuseStep 1152335 = 1728503) B1728503
theorem B1152425 : Blo 766334 1152425 := bstep (se 2 (by rfl) ⟨432159, by rfl⟩ : syracuseStep 1152425 = 864319) B864319
theorem B1152479 : Blo 766334 1152479 := bstep (se 1 (by rfl) ⟨864359, by rfl⟩ : syracuseStep 1152479 = 1728719) B1728719
theorem B1152575 : Blo 766334 1152575 := bstep (se 1 (by rfl) ⟨864431, by rfl⟩ : syracuseStep 1152575 = 1728863) B1728863
theorem B1153055 : Blo 766334 1153055 := bstep (se 1 (by rfl) ⟨864791, by rfl⟩ : syracuseStep 1153055 = 1729583) B1729583
theorem B1644617 : Blo 766334 1644617 := bstep (se 2 (by rfl) ⟨616731, by rfl⟩ : syracuseStep 1644617 = 1233463) B1233463
theorem B1644727 : Blo 766334 1644727 := bstep (se 1 (by rfl) ⟨1233545, by rfl⟩ : syracuseStep 1644727 = 2467091) B2467091
theorem B2922911 : Blo 766334 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B1153487 : Blo 766334 1153487 := bstep (se 1 (by rfl) ⟨865115, by rfl⟩ : syracuseStep 1153487 = 1730231) B1730231
theorem B7870931 : Blo 766334 7870931 := bstep (se 1 (by rfl) ⟨5903198, by rfl⟩ : syracuseStep 7870931 = 11806397) B11806397
theorem B1153577 : Blo 766334 1153577 := bstep (se 2 (by rfl) ⟨432591, by rfl⟩ : syracuseStep 1153577 = 865183) B865183
theorem B1940071 : Blo 766334 1940071 := bstep (se 1 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 1940071 = 2910107) B2910107
theorem B2595455 : Blo 766334 2595455 := bstep (se 1 (by rfl) ⟨1946591, by rfl⟩ : syracuseStep 2595455 = 3893183) B3893183
theorem B1153787 : Blo 766334 1153787 := bstep (se 1 (by rfl) ⟨865340, by rfl⟩ : syracuseStep 1153787 = 1730681) B1730681
theorem B1940233 : Blo 766334 1940233 := bstep (se 2 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 1940233 = 1455175) B1455175
theorem B3119881 : Blo 766334 3119881 := bstep (se 2 (by rfl) ⟨1169955, by rfl⟩ : syracuseStep 3119881 = 2339911) B2339911
theorem B2595671 : Blo 766334 2595671 := bstep (se 1 (by rfl) ⟨1946753, by rfl⟩ : syracuseStep 2595671 = 3893507) B3893507
theorem B1153913 : Blo 766334 1153913 := bstep (se 2 (by rfl) ⟨432717, by rfl⟩ : syracuseStep 1153913 = 865435) B865435
theorem B2071531 : Blo 766334 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B2595833 : Blo 766334 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B1154663 : Blo 766334 1154663 := bstep (se 1 (by rfl) ⟨865997, by rfl⟩ : syracuseStep 1154663 = 1731995) B1731995
theorem B1154825 : Blo 766334 1154825 := bstep (se 2 (by rfl) ⟨433059, by rfl⟩ : syracuseStep 1154825 = 866119) B866119
theorem B2596751 : Blo 766334 2596751 := bstep (se 1 (by rfl) ⟨1947563, by rfl⟩ : syracuseStep 2596751 = 3895127) B3895127
theorem B1941479 : Blo 766334 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B1155047 : Blo 766334 1155047 := bstep (se 1 (by rfl) ⟨866285, by rfl⟩ : syracuseStep 1155047 = 1732571) B1732571
theorem B2596859 : Blo 766334 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B1155167 : Blo 766334 1155167 := bstep (se 1 (by rfl) ⟨866375, by rfl⟩ : syracuseStep 1155167 = 1732751) B1732751
theorem B1155227 : Blo 766334 1155227 := bstep (se 1 (by rfl) ⟨866420, by rfl⟩ : syracuseStep 1155227 = 1732841) B1732841
theorem B22126769 : Blo 766334 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B1941691 : Blo 766334 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B1155311 : Blo 766334 1155311 := bstep (se 1 (by rfl) ⟨866483, by rfl⟩ : syracuseStep 1155311 = 1732967) B1732967
theorem B2597291 : Blo 766334 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B2597831 : Blo 766334 2597831 := bstep (se 1 (by rfl) ⟨1948373, by rfl⟩ : syracuseStep 2597831 = 3896747) B3896747
theorem B2467027 : Blo 766334 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B2467039 : Blo 766334 2467039 := bstep (se 1 (by rfl) ⟨1850279, by rfl⟩ : syracuseStep 2467039 = 3700559) B3700559
theorem B1386089 : Blo 766334 1386089 := bstep (se 2 (by rfl) ⟨519783, by rfl⟩ : syracuseStep 1386089 = 1039567) B1039567
theorem B2467655 : Blo 766334 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B1943635 : Blo 766334 1943635 := bstep (se 1 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 1943635 = 2915453) B2915453
theorem B7383433 : Blo 766334 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B5320043 : Blo 766334 5320043 := bstep (se 1 (by rfl) ⟨3990032, by rfl⟩ : syracuseStep 5320043 = 7980065) B7980065
theorem B4369787 : Blo 766334 4369787 := bstep (se 1 (by rfl) ⟨3277340, by rfl⟩ : syracuseStep 4369787 = 6554681) B6554681
theorem B1945043 : Blo 766334 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B1945255 : Blo 766334 1945255 := bstep (se 1 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 1945255 = 2917883) B2917883
theorem B12660475 : Blo 766334 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B864031 : Blo 766334 864031 := bstep (se 1 (by rfl) ⟨648023, by rfl⟩ : syracuseStep 864031 = 1296047) B1296047
theorem B6992081 : Blo 766334 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B766491 : Blo 766334 766491 := bstep (se 1 (by rfl) ⟨574868, by rfl⟩ : syracuseStep 766491 = 1149737) B1149737
theorem B766631 : Blo 766334 766631 := bstep (se 1 (by rfl) ⟨574973, by rfl⟩ : syracuseStep 766631 = 1149947) B1149947
theorem B766671 : Blo 766334 766671 := bstep (se 1 (by rfl) ⟨575003, by rfl⟩ : syracuseStep 766671 = 1150007) B1150007
theorem B766751 : Blo 766334 766751 := bstep (se 1 (by rfl) ⟨575063, by rfl⟩ : syracuseStep 766751 = 1150127) B1150127
theorem B2077609 : Blo 766334 2077609 := bstep (se 2 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 2077609 = 1558207) B1558207
theorem B1094639 : Blo 766334 1094639 := bstep (se 1 (by rfl) ⟨820979, by rfl⟩ : syracuseStep 1094639 = 1641959) B1641959
theorem B5846093 : Blo 766334 5846093 := bstep (se 3 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 5846093 = 2192285) B2192285
theorem B767231 : Blo 766334 767231 := bstep (se 1 (by rfl) ⟨575423, by rfl⟩ : syracuseStep 767231 = 1150847) B1150847
theorem B1094953 : Blo 766334 1094953 := bstep (se 2 (by rfl) ⟨410607, by rfl⟩ : syracuseStep 1094953 = 821215) B821215
theorem B767359 : Blo 766334 767359 := bstep (se 1 (by rfl) ⟨575519, by rfl⟩ : syracuseStep 767359 = 1151039) B1151039
theorem B767515 : Blo 766334 767515 := bstep (se 1 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 767515 = 1151273) B1151273
theorem B4371995 : Blo 766334 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B5846579 : Blo 766334 5846579 := bstep (se 1 (by rfl) ⟨4384934, by rfl⟩ : syracuseStep 5846579 = 8769869) B8769869
theorem B4929133 : Blo 766334 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B3683951 : Blo 766334 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B767695 : Blo 766334 767695 := bstep (se 1 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 767695 = 1151543) B1151543
theorem B1947361 : Blo 766334 1947361 := bstep (se 2 (by rfl) ⟨730260, by rfl⟩ : syracuseStep 1947361 = 1460521) B1460521
theorem B8730503 : Blo 766334 8730503 := bstep (se 1 (by rfl) ⟨6547877, by rfl⟩ : syracuseStep 8730503 = 13095755) B13095755
theorem B767935 : Blo 766334 767935 := bstep (se 1 (by rfl) ⟨575951, by rfl⟩ : syracuseStep 767935 = 1151903) B1151903
theorem B768063 : Blo 766334 768063 := bstep (se 1 (by rfl) ⟨576047, by rfl⟩ : syracuseStep 768063 = 1152095) B1152095
theorem B1456231 : Blo 766334 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B768103 : Blo 766334 768103 := bstep (se 1 (by rfl) ⟨576077, by rfl⟩ : syracuseStep 768103 = 1152155) B1152155
theorem B866407 : Blo 766334 866407 := bstep (se 1 (by rfl) ⟨649805, by rfl⟩ : syracuseStep 866407 = 1299611) B1299611
theorem B1948151 : Blo 766334 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B768559 : Blo 766334 768559 := bstep (se 1 (by rfl) ⟨576419, by rfl⟩ : syracuseStep 768559 = 1152839) B1152839
theorem B768959 : Blo 766334 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B769007 : Blo 766334 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B3947945 : Blo 766334 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B2080171 : Blo 766334 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B769503 : Blo 766334 769503 := bstep (se 1 (by rfl) ⟨577127, by rfl⟩ : syracuseStep 769503 = 1154255) B1154255
theorem B769583 : Blo 766334 769583 := bstep (se 1 (by rfl) ⟨577187, by rfl⟩ : syracuseStep 769583 = 1154375) B1154375
theorem B769691 : Blo 766334 769691 := bstep (se 1 (by rfl) ⟨577268, by rfl⟩ : syracuseStep 769691 = 1154537) B1154537
theorem B769787 : Blo 766334 769787 := bstep (se 1 (by rfl) ⟨577340, by rfl⟩ : syracuseStep 769787 = 1154681) B1154681
theorem B769951 : Blo 766334 769951 := bstep (se 1 (by rfl) ⟨577463, by rfl⟩ : syracuseStep 769951 = 1154927) B1154927
theorem B1949903 : Blo 766334 1949903 := bstep (se 1 (by rfl) ⟨1462427, by rfl⟩ : syracuseStep 1949903 = 2924855) B2924855
theorem B1753321 : Blo 766334 1753321 := bstep (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) B1314991
theorem B4145527 : Blo 766334 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B4374911 : Blo 766334 4374911 := bstep (se 1 (by rfl) ⟨3281183, by rfl⟩ : syracuseStep 4374911 = 6562367) B6562367
theorem B9847241 : Blo 766334 9847241 := bstep (se 2 (by rfl) ⟨3692715, by rfl⟩ : syracuseStep 9847241 = 7385431) B7385431
theorem B3883625 : Blo 766334 3883625 := bstep (se 2 (by rfl) ⟨1456359, by rfl⟩ : syracuseStep 3883625 = 2912719) B2912719
theorem B1459367 : Blo 766334 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B2770375 : Blo 766334 2770375 := bstep (se 1 (by rfl) ⟨2077781, by rfl⟩ : syracuseStep 2770375 = 4155563) B4155563
theorem B7882427 : Blo 766334 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B18729605 : Blo 766334 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B4443283 : Blo 766334 4443283 := bstep (se 1 (by rfl) ⟨3332462, by rfl⟩ : syracuseStep 4443283 = 6664925) B6664925
theorem B1166503 : Blo 766334 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B10669279 : Blo 766334 10669279 := bstep (se 1 (by rfl) ⟨8001959, by rfl⟩ : syracuseStep 10669279 = 16003919) B16003919
theorem B4934951 : Blo 766334 4934951 := bstep (se 1 (by rfl) ⟨3701213, by rfl⟩ : syracuseStep 4934951 = 7402427) B7402427
theorem B3886379 : Blo 766334 3886379 := bstep (se 1 (by rfl) ⟨2914784, by rfl⟩ : syracuseStep 3886379 = 5829569) B5829569
theorem B8867353 : Blo 766334 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B3886703 : Blo 766334 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B970471 : Blo 766334 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B2182889 : Blo 766334 2182889 := bstep (se 2 (by rfl) ⟨818583, by rfl⟩ : syracuseStep 2182889 = 1637167) B1637167
theorem B8310995 : Blo 766334 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B3887351 : Blo 766334 3887351 := bstep (se 1 (by rfl) ⟨2915513, by rfl⟩ : syracuseStep 3887351 = 5831027) B5831027
theorem B2183993 : Blo 766334 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B1725407 : Blo 766334 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B1037279 : Blo 766334 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B2184175 : Blo 766334 2184175 := bstep (se 1 (by rfl) ⟨1638131, by rfl⟩ : syracuseStep 2184175 = 3276263) B3276263
theorem B28104043 : Blo 766334 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B1725983 : Blo 766334 1725983 := bstep (se 1 (by rfl) ⟨1294487, by rfl⟩ : syracuseStep 1725983 = 2588975) B2588975
theorem B972319 : Blo 766334 972319 := bstep (se 1 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 972319 = 1458479) B1458479
theorem B8312377 : Blo 766334 8312377 := bstep (se 2 (by rfl) ⟨3117141, by rfl⟩ : syracuseStep 8312377 = 6234283) B6234283
theorem B1037929 : Blo 766334 1037929 := bstep (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) B778447
theorem B1726505 : Blo 766334 1726505 := bstep (se 2 (by rfl) ⟨647439, by rfl⟩ : syracuseStep 1726505 = 1294879) B1294879
theorem B10672793 : Blo 766334 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B1727135 : Blo 766334 1727135 := bstep (se 1 (by rfl) ⟨1295351, by rfl⟩ : syracuseStep 1727135 = 2590703) B2590703
theorem B1661627 : Blo 766334 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B2776169 : Blo 766334 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B8772785 : Blo 766334 8772785 := bstep (se 2 (by rfl) ⟨3289794, by rfl⟩ : syracuseStep 8772785 = 6579589) B6579589
theorem B4381883 : Blo 766334 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B974207 : Blo 766334 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B18243191 : Blo 766334 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B6577949 : Blo 766334 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B974911 : Blo 766334 974911 := bstep (se 1 (by rfl) ⟨731183, by rfl⟩ : syracuseStep 974911 = 1462367) B1462367
theorem B7004227 : Blo 766334 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B2187479 : Blo 766334 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1728809 : Blo 766334 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B5530139 : Blo 766334 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B1729079 : Blo 766334 1729079 := bstep (se 1 (by rfl) ⟨1296809, by rfl⟩ : syracuseStep 1729079 = 2593619) B2593619
theorem B1040951 : Blo 766334 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B2187935 : Blo 766334 2187935 := bstep (se 1 (by rfl) ⟨1640951, by rfl⟩ : syracuseStep 2187935 = 3281903) B3281903
theorem B3891887 : Blo 766334 3891887 := bstep (se 1 (by rfl) ⟨2918915, by rfl⟩ : syracuseStep 3891887 = 5837831) B5837831
theorem B39969611 : Blo 766334 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B1729439 : Blo 766334 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B4383659 : Blo 766334 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B13100129 : Blo 766334 13100129 := bstep (se 2 (by rfl) ⟨4912548, by rfl⟩ : syracuseStep 13100129 = 9825097) B9825097
theorem B975983 : Blo 766334 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B144041273 : Blo 766334 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B1729871 : Blo 766334 1729871 := bstep (se 1 (by rfl) ⟨1297403, by rfl⟩ : syracuseStep 1729871 = 2594807) B2594807
theorem B1729961 : Blo 766334 1729961 := bstep (se 2 (by rfl) ⟨648735, by rfl⟩ : syracuseStep 1729961 = 1297471) B1297471
theorem B2189119 : Blo 766334 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B14772091 : Blo 766334 14772091 := bstep (se 1 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 14772091 = 22158137) B22158137
theorem B4155259 : Blo 766334 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B1730591 : Blo 766334 1730591 := bstep (se 1 (by rfl) ⟨1297943, by rfl⟩ : syracuseStep 1730591 = 2595887) B2595887
theorem B3893345 : Blo 766334 3893345 := bstep (se 2 (by rfl) ⟨1460004, by rfl⟩ : syracuseStep 3893345 = 2920009) B2920009
theorem B5531813 : Blo 766334 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B1731419 : Blo 766334 1731419 := bstep (se 1 (by rfl) ⟨1298564, by rfl⟩ : syracuseStep 1731419 = 2597129) B2597129
theorem B7990595 : Blo 766334 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B68185489 : Blo 766334 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B9957485 : Blo 766334 9957485 := bstep (se 3 (by rfl) ⟨1867028, by rfl⟩ : syracuseStep 9957485 = 3734057) B3734057
theorem B13104503 : Blo 766334 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B5535215 : Blo 766334 5535215 := bstep (se 1 (by rfl) ⟨4151411, by rfl⟩ : syracuseStep 5535215 = 8302823) B8302823
theorem B3897071 : Blo 766334 3897071 := bstep (se 1 (by rfl) ⟨2922803, by rfl⟩ : syracuseStep 3897071 = 5845607) B5845607
theorem B2914177 : Blo 766334 2914177 := bstep (se 2 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 2914177 = 2185633) B2185633
theorem B2914451 : Blo 766334 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B16021871 : Blo 766334 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B8288851 : Blo 766334 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B2914937 : Blo 766334 2914937 := bstep (se 2 (by rfl) ⟨1093101, by rfl⟩ : syracuseStep 2914937 = 2186203) B2186203
theorem B2587463 : Blo 766334 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B9338969 : Blo 766334 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B2588921 : Blo 766334 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B2916607 : Blo 766334 2916607 := bstep (se 1 (by rfl) ⟨2187455, by rfl⟩ : syracuseStep 2916607 = 4374911) B4374911
theorem B2589083 : Blo 766334 2589083 := bstep (se 1 (by rfl) ⟨1941812, by rfl⟩ : syracuseStep 2589083 = 3883625) B3883625
theorem B983599 : Blo 766334 983599 := bstep (se 1 (by rfl) ⟨737699, by rfl⟩ : syracuseStep 983599 = 1475399) B1475399
theorem B3278177 : Blo 766334 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B12486403 : Blo 766334 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B2590919 : Blo 766334 2590919 := bstep (se 1 (by rfl) ⟨1943189, by rfl⟩ : syracuseStep 2590919 = 3886379) B3886379
theorem B2591135 : Blo 766334 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B2918825 : Blo 766334 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B19696121 : Blo 766334 19696121 := bstep (se 2 (by rfl) ⟨7386045, by rfl⟩ : syracuseStep 19696121 = 14772091) B14772091
theorem B5540345 : Blo 766334 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B2919037 : Blo 766334 2919037 := bstep (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) B1094639
theorem B1313423 : Blo 766334 1313423 := bstep (se 1 (by rfl) ⟨985067, by rfl⟩ : syracuseStep 1313423 = 1970135) B1970135
theorem B2591513 : Blo 766334 2591513 := bstep (se 2 (by rfl) ⟨971817, by rfl⟩ : syracuseStep 2591513 = 1943635) B1943635
theorem B5540663 : Blo 766334 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B2591567 : Blo 766334 2591567 := bstep (se 1 (by rfl) ⟨1943675, by rfl⟩ : syracuseStep 2591567 = 3887351) B3887351
theorem B2624521 : Blo 766334 2624521 := bstep (se 2 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 2624521 = 1968391) B1968391
theorem B1150271 : Blo 766334 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B1150655 : Blo 766334 1150655 := bstep (se 1 (by rfl) ⟨862991, by rfl⟩ : syracuseStep 1150655 = 1725983) B1725983
theorem B1151003 : Blo 766334 1151003 := bstep (se 1 (by rfl) ⟨863252, by rfl⟩ : syracuseStep 1151003 = 1726505) B1726505
theorem B14225705 : Blo 766334 14225705 := bstep (se 2 (by rfl) ⟨5334639, by rfl⟩ : syracuseStep 14225705 = 10669279) B10669279
theorem B5247287 : Blo 766334 5247287 := bstep (se 1 (by rfl) ⟨3935465, by rfl⟩ : syracuseStep 5247287 = 7870931) B7870931
theorem B7115195 : Blo 766334 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B1151423 : Blo 766334 1151423 := bstep (se 1 (by rfl) ⟨863567, by rfl⟩ : syracuseStep 1151423 = 1727135) B1727135
theorem B2921255 : Blo 766334 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B2593673 : Blo 766334 2593673 := bstep (se 2 (by rfl) ⟨972627, by rfl⟩ : syracuseStep 2593673 = 1945255) B1945255
theorem B16880633 : Blo 766334 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B1152041 : Blo 766334 1152041 := bstep (se 2 (by rfl) ⟨432015, by rfl⟩ : syracuseStep 1152041 = 864031) B864031
theorem B14751179 : Blo 766334 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B1152539 : Blo 766334 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B1152719 : Blo 766334 1152719 := bstep (se 1 (by rfl) ⟨864539, by rfl⟩ : syracuseStep 1152719 = 1729079) B1729079
theorem B2594591 : Blo 766334 2594591 := bstep (se 1 (by rfl) ⟨1945943, by rfl⟩ : syracuseStep 2594591 = 3891887) B3891887
theorem B26646407 : Blo 766334 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B1152959 : Blo 766334 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B2922439 : Blo 766334 2922439 := bstep (se 1 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 2922439 = 4383659) B4383659
theorem B1153247 : Blo 766334 1153247 := bstep (se 1 (by rfl) ⟨864935, by rfl⟩ : syracuseStep 1153247 = 1729871) B1729871
theorem B1153307 : Blo 766334 1153307 := bstep (se 1 (by rfl) ⟨864980, by rfl⟩ : syracuseStep 1153307 = 1729961) B1729961
theorem B924059 : Blo 766334 924059 := bstep (se 1 (by rfl) ⟨693044, by rfl⟩ : syracuseStep 924059 = 1386089) B1386089
theorem B1645103 : Blo 766334 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B1153727 : Blo 766334 1153727 := bstep (se 1 (by rfl) ⟨865295, by rfl⟩ : syracuseStep 1153727 = 1730591) B1730591
theorem B2595563 : Blo 766334 2595563 := bstep (se 1 (by rfl) ⟨1946672, by rfl⟩ : syracuseStep 2595563 = 3893345) B3893345
theorem B1154279 : Blo 766334 1154279 := bstep (se 1 (by rfl) ⟨865709, by rfl⟩ : syracuseStep 1154279 = 1731419) B1731419
theorem B11083169 : Blo 766334 11083169 := bstep (se 2 (by rfl) ⟨4156188, by rfl⟩ : syracuseStep 11083169 = 8312377) B8312377
theorem B1383905 : Blo 766334 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B3546695 : Blo 766334 3546695 := bstep (se 1 (by rfl) ⟨2660021, by rfl⟩ : syracuseStep 3546695 = 5320043) B5320043
theorem B2596481 : Blo 766334 2596481 := bstep (se 2 (by rfl) ⟨973680, by rfl⟩ : syracuseStep 2596481 = 1947361) B1947361
theorem B1941641 : Blo 766334 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B1155209 : Blo 766334 1155209 := bstep (se 2 (by rfl) ⟨433203, by rfl⟩ : syracuseStep 1155209 = 866407) B866407
theorem B4661387 : Blo 766334 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B11051801 : Blo 766334 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B2597885 : Blo 766334 2597885 := bstep (se 3 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 2597885 = 974207) B974207
theorem B10527853 : Blo 766334 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B2598047 : Blo 766334 2598047 := bstep (se 1 (by rfl) ⟨1948535, by rfl⟩ : syracuseStep 2598047 = 3897071) B3897071
theorem B2762041 : Blo 766334 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B1942967 : Blo 766334 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B1943291 : Blo 766334 1943291 := bstep (se 1 (by rfl) ⟨1457468, by rfl⟩ : syracuseStep 1943291 = 2914937) B2914937
theorem B1092475 : Blo 766334 1092475 := bstep (se 1 (by rfl) ⟨819356, by rfl⟩ : syracuseStep 1092475 = 1638713) B1638713
theorem B6564827 : Blo 766334 6564827 := bstep (se 1 (by rfl) ⟨4923620, by rfl⟩ : syracuseStep 6564827 = 9847241) B9847241
theorem B2337761 : Blo 766334 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B5254951 : Blo 766334 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B3289369 : Blo 766334 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B3289385 : Blo 766334 3289385 := bstep (se 2 (by rfl) ⟨1233519, by rfl⟩ : syracuseStep 3289385 = 2467039) B2467039
theorem B1945903 : Blo 766334 1945903 := bstep (se 1 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 1945903 = 2918855) B2918855
theorem B766399 : Blo 766334 766399 := bstep (se 1 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 766399 = 1149599) B1149599
theorem B766431 : Blo 766334 766431 := bstep (se 1 (by rfl) ⟨574823, by rfl⟩ : syracuseStep 766431 = 1149647) B1149647
theorem B766495 : Blo 766334 766495 := bstep (se 1 (by rfl) ⟨574871, by rfl⟩ : syracuseStep 766495 = 1149743) B1149743
theorem B766575 : Blo 766334 766575 := bstep (se 1 (by rfl) ⟨574931, by rfl⟩ : syracuseStep 766575 = 1149863) B1149863
theorem B766695 : Blo 766334 766695 := bstep (se 1 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 766695 = 1150043) B1150043
theorem B766747 : Blo 766334 766747 := bstep (se 1 (by rfl) ⟨575060, by rfl⟩ : syracuseStep 766747 = 1150121) B1150121
theorem B3289967 : Blo 766334 3289967 := bstep (se 1 (by rfl) ⟨2467475, by rfl⟩ : syracuseStep 3289967 = 4934951) B4934951
theorem B767023 : Blo 766334 767023 := bstep (se 1 (by rfl) ⟨575267, by rfl⟩ : syracuseStep 767023 = 1150535) B1150535
theorem B1455259 : Blo 766334 1455259 := bstep (se 1 (by rfl) ⟨1091444, by rfl⟩ : syracuseStep 1455259 = 2182889) B2182889
theorem B767143 : Blo 766334 767143 := bstep (se 1 (by rfl) ⟨575357, by rfl⟩ : syracuseStep 767143 = 1150715) B1150715
theorem B2766077 : Blo 766334 2766077 := bstep (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) B1037279
theorem B767303 : Blo 766334 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B2602621 : Blo 766334 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B9844577 : Blo 766334 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B1455995 : Blo 766334 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B767995 : Blo 766334 767995 := bstep (se 1 (by rfl) ⟨575996, by rfl⟩ : syracuseStep 767995 = 1151993) B1151993
theorem B768127 : Blo 766334 768127 := bstep (se 1 (by rfl) ⟨576095, by rfl⟩ : syracuseStep 768127 = 1152191) B1152191
theorem B768223 : Blo 766334 768223 := bstep (se 1 (by rfl) ⟨576167, by rfl⟩ : syracuseStep 768223 = 1152335) B1152335
theorem B768283 : Blo 766334 768283 := bstep (se 1 (by rfl) ⟨576212, by rfl⟩ : syracuseStep 768283 = 1152425) B1152425
theorem B768319 : Blo 766334 768319 := bstep (se 1 (by rfl) ⟨576239, by rfl⟩ : syracuseStep 768319 = 1152479) B1152479
theorem B768383 : Blo 766334 768383 := bstep (se 1 (by rfl) ⟨576287, by rfl⟩ : syracuseStep 768383 = 1152575) B1152575
theorem B768703 : Blo 766334 768703 := bstep (se 1 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 768703 = 1153055) B1153055
theorem B1096411 : Blo 766334 1096411 := bstep (se 1 (by rfl) ⟨822308, by rfl⟩ : syracuseStep 1096411 = 1644617) B1644617
theorem B1555337 : Blo 766334 1555337 := bstep (se 2 (by rfl) ⟨583251, by rfl⟩ : syracuseStep 1555337 = 1166503) B1166503
theorem B1948607 : Blo 766334 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B768991 : Blo 766334 768991 := bstep (se 1 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 768991 = 1153487) B1153487
theorem B769051 : Blo 766334 769051 := bstep (se 1 (by rfl) ⟨576788, by rfl⟩ : syracuseStep 769051 = 1153577) B1153577
theorem B769191 : Blo 766334 769191 := bstep (se 1 (by rfl) ⟨576893, by rfl⟩ : syracuseStep 769191 = 1153787) B1153787
theorem B90913985 : Blo 766334 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B769275 : Blo 766334 769275 := bstep (se 1 (by rfl) ⟨576956, by rfl⟩ : syracuseStep 769275 = 1153913) B1153913
theorem B1850779 : Blo 766334 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B5848523 : Blo 766334 5848523 := bstep (se 1 (by rfl) ⟨4386392, by rfl⟩ : syracuseStep 5848523 = 8772785) B8772785
theorem B1293961 : Blo 766334 1293961 := bstep (se 2 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 1293961 = 970471) B970471
theorem B769775 : Blo 766334 769775 := bstep (se 1 (by rfl) ⟨577331, by rfl⟩ : syracuseStep 769775 = 1154663) B1154663
theorem B769883 : Blo 766334 769883 := bstep (se 1 (by rfl) ⟨577412, by rfl⟩ : syracuseStep 769883 = 1154825) B1154825
theorem B1294319 : Blo 766334 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B770031 : Blo 766334 770031 := bstep (se 1 (by rfl) ⟨577523, by rfl⟩ : syracuseStep 770031 = 1155047) B1155047
theorem B770111 : Blo 766334 770111 := bstep (se 1 (by rfl) ⟨577583, by rfl⟩ : syracuseStep 770111 = 1155167) B1155167
theorem B770151 : Blo 766334 770151 := bstep (se 1 (by rfl) ⟨577613, by rfl⟩ : syracuseStep 770151 = 1155227) B1155227
theorem B1458319 : Blo 766334 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B770207 : Blo 766334 770207 := bstep (se 1 (by rfl) ⟨577655, by rfl⟩ : syracuseStep 770207 = 1155311) B1155311
theorem B3686759 : Blo 766334 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B1458623 : Blo 766334 1458623 := bstep (se 1 (by rfl) ⟨1093967, by rfl⟩ : syracuseStep 1458623 = 2187935) B2187935
theorem B8733419 : Blo 766334 8733419 := bstep (se 1 (by rfl) ⟨6550064, by rfl⟩ : syracuseStep 8733419 = 13100129) B13100129
theorem B96027515 : Blo 766334 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B2770145 : Blo 766334 2770145 := bstep (se 2 (by rfl) ⟨1038804, by rfl⟩ : syracuseStep 2770145 = 2077609) B2077609
theorem B3687875 : Blo 766334 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B1459937 : Blo 766334 1459937 := bstep (se 2 (by rfl) ⟨547476, by rfl⟩ : syracuseStep 1459937 = 1094953) B1094953
theorem B37472057 : Blo 766334 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B1296425 : Blo 766334 1296425 := bstep (se 2 (by rfl) ⟨486159, by rfl⟩ : syracuseStep 1296425 = 972319) B972319
theorem B6572177 : Blo 766334 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B5327063 : Blo 766334 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B1296695 : Blo 766334 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B3885569 : Blo 766334 3885569 := bstep (se 2 (by rfl) ⟨1457088, by rfl⟩ : syracuseStep 3885569 = 2914177) B2914177
theorem B6638323 : Blo 766334 6638323 := bstep (se 1 (by rfl) ⟨4978742, by rfl⟩ : syracuseStep 6638323 = 9957485) B9957485
theorem B8736335 : Blo 766334 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B3690143 : Blo 766334 3690143 := bstep (se 1 (by rfl) ⟨2767607, by rfl⟩ : syracuseStep 3690143 = 5535215) B5535215
theorem B5820335 : Blo 766334 5820335 := bstep (se 1 (by rfl) ⟨4365251, by rfl⟩ : syracuseStep 5820335 = 8730503) B8730503
theorem B48648509 : Blo 766334 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B1298767 : Blo 766334 1298767 := bstep (se 1 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 1298767 = 1948151) B1948151
theorem B1724975 : Blo 766334 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B2773561 : Blo 766334 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B1299881 : Blo 766334 1299881 := bstep (se 2 (by rfl) ⟨487455, by rfl⟩ : syracuseStep 1299881 = 974911) B974911
theorem B1299935 : Blo 766334 1299935 := bstep (se 1 (by rfl) ⟨974951, by rfl⟩ : syracuseStep 1299935 = 1949903) B1949903
theorem B5527369 : Blo 766334 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B972911 : Blo 766334 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B1726631 : Blo 766334 1726631 := bstep (se 1 (by rfl) ⟨1294973, by rfl⟩ : syracuseStep 1726631 = 2589947) B2589947
theorem B9001543 : Blo 766334 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B2775869 : Blo 766334 2775869 := bstep (se 3 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 2775869 = 1040951) B1040951
theorem B3693833 : Blo 766334 3693833 := bstep (se 2 (by rfl) ⟨1385187, by rfl⟩ : syracuseStep 3693833 = 2770375) B2770375
theorem B1728107 : Blo 766334 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1728467 : Blo 766334 1728467 := bstep (se 1 (by rfl) ⟨1296350, by rfl⟩ : syracuseStep 1728467 = 2592701) B2592701
theorem B2187319 : Blo 766334 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B1728575 : Blo 766334 1728575 := bstep (se 1 (by rfl) ⟨1296431, by rfl⟩ : syracuseStep 1728575 = 2592863) B2592863
theorem B5924377 : Blo 766334 5924377 := bstep (se 2 (by rfl) ⟨2221641, by rfl⟩ : syracuseStep 5924377 = 4443283) B4443283
theorem B1730303 : Blo 766334 1730303 := bstep (se 1 (by rfl) ⟨1297727, by rfl⟩ : syracuseStep 1730303 = 2595455) B2595455
theorem B1107751 : Blo 766334 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B1730447 : Blo 766334 1730447 := bstep (se 1 (by rfl) ⟨1297835, by rfl⟩ : syracuseStep 1730447 = 2595671) B2595671
theorem B1730555 : Blo 766334 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B11823137 : Blo 766334 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B4385299 : Blo 766334 4385299 := bstep (se 1 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 4385299 = 6577949) B6577949
theorem B1731167 : Blo 766334 1731167 := bstep (se 1 (by rfl) ⟨1298375, by rfl⟩ : syracuseStep 1731167 = 2596751) B2596751
theorem B1731239 : Blo 766334 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B1731527 : Blo 766334 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B1731887 : Blo 766334 1731887 := bstep (se 1 (by rfl) ⟨1298915, by rfl⟩ : syracuseStep 1731887 = 2597831) B2597831
theorem B2912233 : Blo 766334 2912233 := bstep (se 2 (by rfl) ⟨1092087, by rfl⟩ : syracuseStep 2912233 = 2184175) B2184175
theorem B1405153 : Blo 766334 1405153 := bstep (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) B1053865
theorem B2913191 : Blo 766334 2913191 := bstep (se 1 (by rfl) ⟨2184893, by rfl⟩ : syracuseStep 2913191 = 4369787) B4369787
theorem B2192969 : Blo 766334 2192969 := bstep (se 2 (by rfl) ⟨822363, by rfl⟩ : syracuseStep 2192969 = 1644727) B1644727
theorem B3897395 : Blo 766334 3897395 := bstep (se 1 (by rfl) ⟨2923046, by rfl⟩ : syracuseStep 3897395 = 5846093) B5846093
theorem B2586761 : Blo 766334 2586761 := bstep (se 2 (by rfl) ⟨970035, by rfl⟩ : syracuseStep 2586761 = 1940071) B1940071
theorem B2586977 : Blo 766334 2586977 := bstep (se 2 (by rfl) ⟨970116, by rfl⟩ : syracuseStep 2586977 = 1940233) B1940233
theorem B4159841 : Blo 766334 4159841 := bstep (se 2 (by rfl) ⟨1559940, by rfl⟩ : syracuseStep 4159841 = 3119881) B3119881
theorem B2914663 : Blo 766334 2914663 := bstep (se 1 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 2914663 = 4371995) B4371995
theorem B3897719 : Blo 766334 3897719 := bstep (se 1 (by rfl) ⟨2923289, by rfl⟩ : syracuseStep 3897719 = 5846579) B5846579
theorem B2455967 : Blo 766334 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B10681247 : Blo 766334 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B6225979 : Blo 766334 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B2916425 : Blo 766334 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B2457839 : Blo 766334 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B2458583 : Blo 766334 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B2590379 : Blo 766334 2590379 := bstep (se 1 (by rfl) ⟨1942784, by rfl⟩ : syracuseStep 2590379 = 3885569) B3885569
theorem B7899169 : Blo 766334 7899169 := bstep (se 2 (by rfl) ⟨2962188, by rfl⟩ : syracuseStep 7899169 = 5924377) B5924377
theorem B16648537 : Blo 766334 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B1477001 : Blo 766334 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B2460095 : Blo 766334 2460095 := bstep (se 1 (by rfl) ⟨1845071, by rfl⟩ : syracuseStep 2460095 = 3690143) B3690143
theorem B1149983 : Blo 766334 1149983 := bstep (se 1 (by rfl) ⟨862487, by rfl⟩ : syracuseStep 1149983 = 1724975) B1724975
theorem B9834119 : Blo 766334 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B8851097 : Blo 766334 8851097 := bstep (se 2 (by rfl) ⟨3319161, by rfl⟩ : syracuseStep 8851097 = 6638323) B6638323
theorem B17764271 : Blo 766334 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B1151087 : Blo 766334 1151087 := bstep (se 1 (by rfl) ⟨863315, by rfl⟩ : syracuseStep 1151087 = 1726631) B1726631
theorem B2462555 : Blo 766334 2462555 := bstep (se 1 (by rfl) ⟨1846916, by rfl⟩ : syracuseStep 2462555 = 3693833) B3693833
theorem B922603 : Blo 766334 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B2364463 : Blo 766334 2364463 := bstep (se 1 (by rfl) ⟨1773347, by rfl⟩ : syracuseStep 2364463 = 3546695) B3546695
theorem B1152071 : Blo 766334 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B1152311 : Blo 766334 1152311 := bstep (se 1 (by rfl) ⟨864233, by rfl⟩ : syracuseStep 1152311 = 1728467) B1728467
theorem B1152383 : Blo 766334 1152383 := bstep (se 1 (by rfl) ⟨864287, by rfl⟩ : syracuseStep 1152383 = 1728575) B1728575
theorem B2594429 : Blo 766334 2594429 := bstep (se 3 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 2594429 = 972911) B972911
theorem B2594537 : Blo 766334 2594537 := bstep (se 2 (by rfl) ⟨972951, by rfl⟩ : syracuseStep 2594537 = 1945903) B1945903
theorem B2464157 : Blo 766334 2464157 := bstep (se 3 (by rfl) ⟨462029, by rfl⟩ : syracuseStep 2464157 = 924059) B924059
theorem B1153535 : Blo 766334 1153535 := bstep (se 1 (by rfl) ⟨865151, by rfl⟩ : syracuseStep 1153535 = 1730303) B1730303
theorem B1153631 : Blo 766334 1153631 := bstep (se 1 (by rfl) ⟨865223, by rfl⟩ : syracuseStep 1153631 = 1730447) B1730447
theorem B1153703 : Blo 766334 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B1940345 : Blo 766334 1940345 := bstep (se 2 (by rfl) ⟨727629, by rfl⟩ : syracuseStep 1940345 = 1455259) B1455259
theorem B1154111 : Blo 766334 1154111 := bstep (se 1 (by rfl) ⟨865583, by rfl⟩ : syracuseStep 1154111 = 1731167) B1731167
theorem B1154159 : Blo 766334 1154159 := bstep (se 1 (by rfl) ⟨865619, by rfl⟩ : syracuseStep 1154159 = 1731239) B1731239
theorem B1154351 : Blo 766334 1154351 := bstep (se 1 (by rfl) ⟨865763, by rfl⟩ : syracuseStep 1154351 = 1731527) B1731527
theorem B9870821 : Blo 766334 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B1154591 : Blo 766334 1154591 := bstep (se 1 (by rfl) ⟨865943, by rfl⟩ : syracuseStep 1154591 = 1731887) B1731887
theorem B6234029 : Blo 766334 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B1942127 : Blo 766334 1942127 := bstep (se 1 (by rfl) ⟨1456595, by rfl⟩ : syracuseStep 1942127 = 2913191) B2913191
theorem B12002057 : Blo 766334 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B1844051 : Blo 766334 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B6563051 : Blo 766334 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B2598263 : Blo 766334 2598263 := bstep (se 1 (by rfl) ⟨1948697, by rfl⟩ : syracuseStep 2598263 = 3897395) B3897395
theorem B2598479 : Blo 766334 2598479 := bstep (se 1 (by rfl) ⟨1948859, by rfl⟩ : syracuseStep 2598479 = 3897719) B3897719
theorem B7120831 : Blo 766334 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B862879 : Blo 766334 862879 := bstep (se 1 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 862879 = 1294319) B1294319
theorem B1944425 : Blo 766334 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B1846763 : Blo 766334 1846763 := bstep (se 1 (by rfl) ⟨1385072, by rfl⟩ : syracuseStep 1846763 = 2770145) B2770145
theorem B20983445 : Blo 766334 20983445 := bstep (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) B983599
theorem B24981371 : Blo 766334 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B864283 : Blo 766334 864283 := bstep (se 1 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 864283 = 1296425) B1296425
theorem B3551375 : Blo 766334 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B14037137 : Blo 766334 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B864463 : Blo 766334 864463 := bstep (se 1 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 864463 = 1296695) B1296695
theorem B1945883 : Blo 766334 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B3682721 : Blo 766334 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B766847 : Blo 766334 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B767103 : Blo 766334 767103 := bstep (se 1 (by rfl) ⟨575327, by rfl⟩ : syracuseStep 767103 = 1150655) B1150655
theorem B3880223 : Blo 766334 3880223 := bstep (se 1 (by rfl) ⟨2910167, by rfl⟩ : syracuseStep 3880223 = 5820335) B5820335
theorem B767335 : Blo 766334 767335 := bstep (se 1 (by rfl) ⟨575501, by rfl⟩ : syracuseStep 767335 = 1151003) B1151003
theorem B9483803 : Blo 766334 9483803 := bstep (se 1 (by rfl) ⟨7112852, by rfl⟩ : syracuseStep 9483803 = 14225705) B14225705
theorem B767615 : Blo 766334 767615 := bstep (se 1 (by rfl) ⟨575711, by rfl⟩ : syracuseStep 767615 = 1151423) B1151423
theorem B1947503 : Blo 766334 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B11253755 : Blo 766334 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B5847065 : Blo 766334 5847065 := bstep (se 2 (by rfl) ⟨2192649, by rfl⟩ : syracuseStep 5847065 = 4385299) B4385299
theorem B768027 : Blo 766334 768027 := bstep (se 1 (by rfl) ⟨576020, by rfl⟩ : syracuseStep 768027 = 1152041) B1152041
theorem B866587 : Blo 766334 866587 := bstep (se 1 (by rfl) ⟨649940, by rfl⟩ : syracuseStep 866587 = 1299881) B1299881
theorem B866623 : Blo 766334 866623 := bstep (se 1 (by rfl) ⟨649967, by rfl⟩ : syracuseStep 866623 = 1299935) B1299935
theorem B768359 : Blo 766334 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B768479 : Blo 766334 768479 := bstep (se 1 (by rfl) ⟨576359, by rfl⟩ : syracuseStep 768479 = 1152719) B1152719
theorem B1456633 : Blo 766334 1456633 := bstep (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) B1092475
theorem B768639 : Blo 766334 768639 := bstep (se 1 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 768639 = 1152959) B1152959
theorem B768831 : Blo 766334 768831 := bstep (se 1 (by rfl) ⟨576623, by rfl⟩ : syracuseStep 768831 = 1153247) B1153247
theorem B768871 : Blo 766334 768871 := bstep (se 1 (by rfl) ⟨576653, by rfl⟩ : syracuseStep 768871 = 1153307) B1153307
theorem B1096735 : Blo 766334 1096735 := bstep (se 1 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 1096735 = 1645103) B1645103
theorem B769151 : Blo 766334 769151 := bstep (se 1 (by rfl) ⟨576863, by rfl⟩ : syracuseStep 769151 = 1153727) B1153727
theorem B1850579 : Blo 766334 1850579 := bstep (se 1 (by rfl) ⟨1387934, by rfl⟩ : syracuseStep 1850579 = 2775869) B2775869
theorem B769519 : Blo 766334 769519 := bstep (se 1 (by rfl) ⟨577139, by rfl⟩ : syracuseStep 769519 = 1154279) B1154279
theorem B7388779 : Blo 766334 7388779 := bstep (se 1 (by rfl) ⟨5541584, by rfl⟩ : syracuseStep 7388779 = 11083169) B11083169
theorem B3882653 : Blo 766334 3882653 := bstep (se 3 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 3882653 = 1455995) B1455995
theorem B3882977 : Blo 766334 3882977 := bstep (se 2 (by rfl) ⟨1456116, by rfl⟩ : syracuseStep 3882977 = 2912233) B2912233
theorem B1294427 : Blo 766334 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B770139 : Blo 766334 770139 := bstep (se 1 (by rfl) ⟨577604, by rfl⟩ : syracuseStep 770139 = 1155209) B1155209
theorem B11092909 : Blo 766334 11092909 := bstep (se 3 (by rfl) ⟨2079920, by rfl⟩ : syracuseStep 11092909 = 4159841) B4159841
theorem B1295311 : Blo 766334 1295311 := bstep (se 1 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 1295311 = 1942967) B1942967
theorem B1295527 : Blo 766334 1295527 := bstep (se 1 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 1295527 = 1943291) B1943291
theorem B7882091 : Blo 766334 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B4376551 : Blo 766334 4376551 := bstep (se 1 (by rfl) ⟨3282413, by rfl⟩ : syracuseStep 4376551 = 6564827) B6564827
theorem B3886217 : Blo 766334 3886217 := bstep (se 2 (by rfl) ⟨1457331, by rfl⟩ : syracuseStep 3886217 = 2914663) B2914663
theorem B1461881 : Blo 766334 1461881 := bstep (se 2 (by rfl) ⟨548205, by rfl⟩ : syracuseStep 1461881 = 1096411) B1096411
theorem B1461979 : Blo 766334 1461979 := bstep (se 1 (by rfl) ⟨1096484, by rfl⟩ : syracuseStep 1461979 = 2192969) B2192969
theorem B1724507 : Blo 766334 1724507 := bstep (se 1 (by rfl) ⟨1293380, by rfl⟩ : syracuseStep 1724507 = 2586761) B2586761
theorem B1724651 : Blo 766334 1724651 := bstep (se 1 (by rfl) ⟨1293488, by rfl⟩ : syracuseStep 1724651 = 2586977) B2586977
theorem B1036891 : Blo 766334 1036891 := bstep (se 1 (by rfl) ⟨777668, by rfl⟩ : syracuseStep 1036891 = 1555337) B1555337
theorem B1299071 : Blo 766334 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B60609323 : Blo 766334 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B1725281 : Blo 766334 1725281 := bstep (se 2 (by rfl) ⟨646980, by rfl⟩ : syracuseStep 1725281 = 1293961) B1293961
theorem B1725947 : Blo 766334 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B1726055 : Blo 766334 1726055 := bstep (se 1 (by rfl) ⟨1294541, by rfl⟩ : syracuseStep 1726055 = 2589083) B2589083
theorem B972415 : Blo 766334 972415 := bstep (se 1 (by rfl) ⟨729311, by rfl⟩ : syracuseStep 972415 = 1458623) B1458623
theorem B3888809 : Blo 766334 3888809 := bstep (se 2 (by rfl) ⟨1458303, by rfl⟩ : syracuseStep 3888809 = 2916607) B2916607
theorem B5822279 : Blo 766334 5822279 := bstep (se 1 (by rfl) ⟨4366709, by rfl⟩ : syracuseStep 5822279 = 8733419) B8733419
theorem B64018343 : Blo 766334 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B2185451 : Blo 766334 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B973291 : Blo 766334 973291 := bstep (se 1 (by rfl) ⟨729968, by rfl⟩ : syracuseStep 973291 = 1459937) B1459937
theorem B7494149 : Blo 766334 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B4381451 : Blo 766334 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1727279 : Blo 766334 1727279 := bstep (se 1 (by rfl) ⟨1295459, by rfl⟩ : syracuseStep 1727279 = 2590919) B2590919
theorem B1727423 : Blo 766334 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B13130747 : Blo 766334 13130747 := bstep (se 1 (by rfl) ⟨9848060, by rfl⟩ : syracuseStep 13130747 = 19696121) B19696121
theorem B3693563 : Blo 766334 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B875615 : Blo 766334 875615 := bstep (se 1 (by rfl) ⟨656711, by rfl⟩ : syracuseStep 875615 = 1313423) B1313423
theorem B1727675 : Blo 766334 1727675 := bstep (se 1 (by rfl) ⟨1295756, by rfl⟩ : syracuseStep 1727675 = 2591513) B2591513
theorem B3693775 : Blo 766334 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B1727711 : Blo 766334 1727711 := bstep (se 1 (by rfl) ⟨1295783, by rfl⟩ : syracuseStep 1727711 = 2591567) B2591567
theorem B5824223 : Blo 766334 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B3498191 : Blo 766334 3498191 := bstep (se 1 (by rfl) ⟨2623643, by rfl⟩ : syracuseStep 3498191 = 5247287) B5247287
theorem B32432339 : Blo 766334 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B4743463 : Blo 766334 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B1729115 : Blo 766334 1729115 := bstep (se 1 (by rfl) ⟨1296836, by rfl⟩ : syracuseStep 1729115 = 2593673) B2593673
theorem B3892049 : Blo 766334 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B1729727 : Blo 766334 1729727 := bstep (se 1 (by rfl) ⟨1297295, by rfl⟩ : syracuseStep 1729727 = 2594591) B2594591
theorem B3499361 : Blo 766334 3499361 := bstep (se 2 (by rfl) ⟨1312260, by rfl⟩ : syracuseStep 3499361 = 2624521) B2624521
theorem B1730375 : Blo 766334 1730375 := bstep (se 1 (by rfl) ⟨1297781, by rfl⟩ : syracuseStep 1730375 = 2595563) B2595563
theorem B7006601 : Blo 766334 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B1730987 : Blo 766334 1730987 := bstep (se 1 (by rfl) ⟨1298240, by rfl⟩ : syracuseStep 1730987 = 2596481) B2596481
theorem B3107591 : Blo 766334 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B4385825 : Blo 766334 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B1731689 : Blo 766334 1731689 := bstep (se 2 (by rfl) ⟨649383, by rfl⟩ : syracuseStep 1731689 = 1298767) B1298767
theorem B7367867 : Blo 766334 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B1731923 : Blo 766334 1731923 := bstep (se 1 (by rfl) ⟨1298942, by rfl⟩ : syracuseStep 1731923 = 2597885) B2597885
theorem B3698081 : Blo 766334 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B1732031 : Blo 766334 1732031 := bstep (se 1 (by rfl) ⟨1299023, by rfl⟩ : syracuseStep 1732031 = 2598047) B2598047
theorem B6549245 : Blo 766334 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B3470161 : Blo 766334 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B7369825 : Blo 766334 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B3896585 : Blo 766334 3896585 := bstep (se 2 (by rfl) ⟨1461219, by rfl⟩ : syracuseStep 3896585 = 2922439) B2922439
theorem B2192923 : Blo 766334 2192923 := bstep (se 1 (by rfl) ⟨1644692, by rfl⟩ : syracuseStep 2192923 = 3289385) B3289385
theorem B2193311 : Blo 766334 2193311 := bstep (se 1 (by rfl) ⟨1644983, by rfl⟩ : syracuseStep 2193311 = 3289967) B3289967
theorem B3899015 : Blo 766334 3899015 := bstep (se 1 (by rfl) ⟨2924261, by rfl⟩ : syracuseStep 3899015 = 5848523) B5848523
theorem B1638559 : Blo 766334 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B9470333 : Blo 766334 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B6324617 : Blo 766334 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B1639055 : Blo 766334 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B9339893 : Blo 766334 9339893 := bstep (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) B875615
theorem B1640063 : Blo 766334 1640063 := bstep (se 1 (by rfl) ⟨1230047, by rfl⟩ : syracuseStep 1640063 = 2460095) B2460095
theorem B2590811 : Blo 766334 2590811 := bstep (se 1 (by rfl) ⟨1943108, by rfl⟩ : syracuseStep 2590811 = 3886217) B3886217
theorem B6556079 : Blo 766334 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B5900731 : Blo 766334 5900731 := bstep (se 1 (by rfl) ⟨4425548, by rfl⟩ : syracuseStep 5900731 = 8851097) B8851097
theorem B5835401 : Blo 766334 5835401 := bstep (se 2 (by rfl) ⟨2188275, by rfl⟩ : syracuseStep 5835401 = 4376551) B4376551
theorem B1149671 : Blo 766334 1149671 := bstep (se 1 (by rfl) ⟨862253, by rfl⟩ : syracuseStep 1149671 = 1724507) B1724507
theorem B1149767 : Blo 766334 1149767 := bstep (se 1 (by rfl) ⟨862325, by rfl⟩ : syracuseStep 1149767 = 1724651) B1724651
theorem B40406215 : Blo 766334 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B1641703 : Blo 766334 1641703 := bstep (se 1 (by rfl) ⟨1231277, by rfl⟩ : syracuseStep 1641703 = 2462555) B2462555
theorem B1150187 : Blo 766334 1150187 := bstep (se 1 (by rfl) ⟨862640, by rfl⟩ : syracuseStep 1150187 = 1725281) B1725281
theorem B1150505 : Blo 766334 1150505 := bstep (se 2 (by rfl) ⟨431439, by rfl⟩ : syracuseStep 1150505 = 862879) B862879
theorem B1150631 : Blo 766334 1150631 := bstep (se 1 (by rfl) ⟨862973, by rfl⟩ : syracuseStep 1150631 = 1725947) B1725947
theorem B1150703 : Blo 766334 1150703 := bstep (se 1 (by rfl) ⟨863027, by rfl⟩ : syracuseStep 1150703 = 1726055) B1726055
theorem B2592539 : Blo 766334 2592539 := bstep (se 1 (by rfl) ⟨1944404, by rfl⟩ : syracuseStep 2592539 = 3888809) B3888809
theorem B1642771 : Blo 766334 1642771 := bstep (se 1 (by rfl) ⟨1232078, by rfl⟩ : syracuseStep 1642771 = 2464157) B2464157
theorem B2920967 : Blo 766334 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B1151519 : Blo 766334 1151519 := bstep (se 1 (by rfl) ⟨863639, by rfl⟩ : syracuseStep 1151519 = 1727279) B1727279
theorem B1151615 : Blo 766334 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B8753831 : Blo 766334 8753831 := bstep (se 1 (by rfl) ⟨6565373, by rfl⟩ : syracuseStep 8753831 = 13130747) B13130747
theorem B2462375 : Blo 766334 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B1151783 : Blo 766334 1151783 := bstep (se 1 (by rfl) ⟨863837, by rfl⟩ : syracuseStep 1151783 = 1727675) B1727675
theorem B1151807 : Blo 766334 1151807 := bstep (se 1 (by rfl) ⟨863855, by rfl⟩ : syracuseStep 1151807 = 1727711) B1727711
theorem B1152377 : Blo 766334 1152377 := bstep (se 2 (by rfl) ⟨432141, by rfl⟩ : syracuseStep 1152377 = 864283) B864283
theorem B2332127 : Blo 766334 2332127 := bstep (se 1 (by rfl) ⟨1749095, by rfl⟩ : syracuseStep 2332127 = 3498191) B3498191
theorem B1152617 : Blo 766334 1152617 := bstep (se 2 (by rfl) ⟨432231, by rfl⟩ : syracuseStep 1152617 = 864463) B864463
theorem B1152743 : Blo 766334 1152743 := bstep (se 1 (by rfl) ⟨864557, by rfl⟩ : syracuseStep 1152743 = 1729115) B1729115
theorem B8001371 : Blo 766334 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B2594699 : Blo 766334 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B1382521 : Blo 766334 1382521 := bstep (se 2 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 1382521 = 1036891) B1036891
theorem B1153151 : Blo 766334 1153151 := bstep (se 1 (by rfl) ⟨864863, by rfl⟩ : syracuseStep 1153151 = 1729727) B1729727
theorem B2332907 : Blo 766334 2332907 := bstep (se 1 (by rfl) ⟨1749680, by rfl⟩ : syracuseStep 2332907 = 3499361) B3499361
theorem B3938669 : Blo 766334 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B4626881 : Blo 766334 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B1153583 : Blo 766334 1153583 := bstep (se 1 (by rfl) ⟨865187, by rfl⟩ : syracuseStep 1153583 = 1730375) B1730375
theorem B1153991 : Blo 766334 1153991 := bstep (se 1 (by rfl) ⟨865493, by rfl⟩ : syracuseStep 1153991 = 1730987) B1730987
theorem B2071727 : Blo 766334 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B2923883 : Blo 766334 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B2923897 : Blo 766334 2923897 := bstep (se 2 (by rfl) ⟨1096461, by rfl⟩ : syracuseStep 2923897 = 2192923) B2192923
theorem B1154459 : Blo 766334 1154459 := bstep (se 1 (by rfl) ⟨865844, by rfl⟩ : syracuseStep 1154459 = 1731689) B1731689
theorem B1154615 : Blo 766334 1154615 := bstep (se 1 (by rfl) ⟨865961, by rfl⟩ : syracuseStep 1154615 = 1731923) B1731923
theorem B2465387 : Blo 766334 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B1154687 : Blo 766334 1154687 := bstep (se 1 (by rfl) ⟨866015, by rfl⟩ : syracuseStep 1154687 = 1732031) B1732031
theorem B4366163 : Blo 766334 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B16654247 : Blo 766334 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B1155449 : Blo 766334 1155449 := bstep (se 2 (by rfl) ⟨433293, by rfl⟩ : syracuseStep 1155449 = 866587) B866587
theorem B1155497 : Blo 766334 1155497 := bstep (se 2 (by rfl) ⟨433311, by rfl⟩ : syracuseStep 1155497 = 866623) B866623
theorem B1942177 : Blo 766334 1942177 := bstep (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) B1456633
theorem B2597723 : Blo 766334 2597723 := bstep (se 1 (by rfl) ⟨1948292, by rfl⟩ : syracuseStep 2597723 = 3896585) B3896585
theorem B19669877 : Blo 766334 19669877 := bstep (se 5 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 19669877 = 1844051) B1844051
theorem B4925033 : Blo 766334 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B2599343 : Blo 766334 2599343 := bstep (se 1 (by rfl) ⟨1949507, by rfl⟩ : syracuseStep 2599343 = 3899015) B3899015
theorem B1944283 : Blo 766334 1944283 := bstep (se 1 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 1944283 = 2916425) B2916425
theorem B862951 : Blo 766334 862951 := bstep (se 1 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 862951 = 1294427) B1294427
theorem B8301305 : Blo 766334 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B86486237 : Blo 766334 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B5254727 : Blo 766334 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B14790545 : Blo 766334 14790545 := bstep (se 2 (by rfl) ⟨5546454, by rfl⟩ : syracuseStep 14790545 = 11092909) B11092909
theorem B766655 : Blo 766334 766655 := bstep (se 1 (by rfl) ⟨574991, by rfl⟩ : syracuseStep 766655 = 1149983) B1149983
theorem B11842847 : Blo 766334 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B10532225 : Blo 766334 10532225 := bstep (se 2 (by rfl) ⟨3949584, by rfl⟩ : syracuseStep 10532225 = 7899169) B7899169
theorem B767391 : Blo 766334 767391 := bstep (se 1 (by rfl) ⟨575543, by rfl⟩ : syracuseStep 767391 = 1151087) B1151087
theorem B866047 : Blo 766334 866047 := bstep (se 1 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 866047 = 1299071) B1299071
theorem B22198049 : Blo 766334 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B768047 : Blo 766334 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B768207 : Blo 766334 768207 := bstep (se 1 (by rfl) ⟨576155, by rfl⟩ : syracuseStep 768207 = 1152311) B1152311
theorem B768255 : Blo 766334 768255 := bstep (se 1 (by rfl) ⟨576191, by rfl⟩ : syracuseStep 768255 = 1152383) B1152383
theorem B3881519 : Blo 766334 3881519 := bstep (se 1 (by rfl) ⟨2911139, by rfl⟩ : syracuseStep 3881519 = 5822279) B5822279
theorem B42678895 : Blo 766334 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B1456967 : Blo 766334 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B769023 : Blo 766334 769023 := bstep (se 1 (by rfl) ⟨576767, by rfl⟩ : syracuseStep 769023 = 1153535) B1153535
theorem B4996099 : Blo 766334 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B769087 : Blo 766334 769087 := bstep (se 1 (by rfl) ⟨576815, by rfl⟩ : syracuseStep 769087 = 1153631) B1153631
theorem B769135 : Blo 766334 769135 := bstep (se 1 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 769135 = 1153703) B1153703
theorem B1293563 : Blo 766334 1293563 := bstep (se 1 (by rfl) ⟨970172, by rfl⟩ : syracuseStep 1293563 = 1940345) B1940345
theorem B769407 : Blo 766334 769407 := bstep (se 1 (by rfl) ⟨577055, by rfl⟩ : syracuseStep 769407 = 1154111) B1154111
theorem B769439 : Blo 766334 769439 := bstep (se 1 (by rfl) ⟨577079, by rfl⟩ : syracuseStep 769439 = 1154159) B1154159
theorem B769567 : Blo 766334 769567 := bstep (se 1 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 769567 = 1154351) B1154351
theorem B1949305 : Blo 766334 1949305 := bstep (se 2 (by rfl) ⟨730989, by rfl⟩ : syracuseStep 1949305 = 1461979) B1461979
theorem B769727 : Blo 766334 769727 := bstep (se 1 (by rfl) ⟨577295, by rfl⟩ : syracuseStep 769727 = 1154591) B1154591
theorem B3882815 : Blo 766334 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B1294751 : Blo 766334 1294751 := bstep (se 1 (by rfl) ⟨971063, by rfl⟩ : syracuseStep 1294751 = 1942127) B1942127
theorem B4375367 : Blo 766334 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B1230137 : Blo 766334 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B4671067 : Blo 766334 4671067 := bstep (se 1 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 4671067 = 7006601) B7006601
theorem B1296283 : Blo 766334 1296283 := bstep (se 1 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 1296283 = 1944425) B1944425
theorem B1296553 : Blo 766334 1296553 := bstep (se 2 (by rfl) ⟨486207, by rfl⟩ : syracuseStep 1296553 = 972415) B972415
theorem B1231175 : Blo 766334 1231175 := bstep (se 1 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 1231175 = 1846763) B1846763
theorem B9358091 : Blo 766334 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B1297255 : Blo 766334 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B1297721 : Blo 766334 1297721 := bstep (se 2 (by rfl) ⟨486645, by rfl⟩ : syracuseStep 1297721 = 973291) B973291
theorem B1298335 : Blo 766334 1298335 := bstep (se 1 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 1298335 = 1947503) B1947503
theorem B1462207 : Blo 766334 1462207 := bstep (se 1 (by rfl) ⟨1096655, by rfl⟩ : syracuseStep 1462207 = 2193311) B2193311
theorem B1462313 : Blo 766334 1462313 := bstep (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) B1096735
theorem B1233719 : Blo 766334 1233719 := bstep (se 1 (by rfl) ⟨925289, by rfl⟩ : syracuseStep 1233719 = 1850579) B1850579
theorem B9851705 : Blo 766334 9851705 := bstep (se 2 (by rfl) ⟨3694389, by rfl⟩ : syracuseStep 9851705 = 7388779) B7388779
theorem B1726919 : Blo 766334 1726919 := bstep (se 1 (by rfl) ⟨1295189, by rfl⟩ : syracuseStep 1726919 = 2590379) B2590379
theorem B1727081 : Blo 766334 1727081 := bstep (se 2 (by rfl) ⟨647655, by rfl⟩ : syracuseStep 1727081 = 1295311) B1295311
theorem B1727369 : Blo 766334 1727369 := bstep (se 2 (by rfl) ⟨647763, by rfl⟩ : syracuseStep 1727369 = 1295527) B1295527
theorem B974587 : Blo 766334 974587 := bstep (se 1 (by rfl) ⟨730940, by rfl⟩ : syracuseStep 974587 = 1461881) B1461881
theorem B9494441 : Blo 766334 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B1729619 : Blo 766334 1729619 := bstep (se 1 (by rfl) ⟨1297214, by rfl⟩ : syracuseStep 1729619 = 2594429) B2594429
theorem B1729691 : Blo 766334 1729691 := bstep (se 1 (by rfl) ⟨1297268, by rfl⟩ : syracuseStep 1729691 = 2594537) B2594537
theorem B6580547 : Blo 766334 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B4156019 : Blo 766334 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B12610469 : Blo 766334 12610469 := bstep (se 4 (by rfl) ⟨1182231, by rfl⟩ : syracuseStep 12610469 = 2364463) B2364463
theorem B1732175 : Blo 766334 1732175 := bstep (se 1 (by rfl) ⟨1299131, by rfl⟩ : syracuseStep 1732175 = 2598263) B2598263
theorem B1732319 : Blo 766334 1732319 := bstep (se 1 (by rfl) ⟨1299239, by rfl⟩ : syracuseStep 1732319 = 2598479) B2598479
theorem B9826433 : Blo 766334 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B4911911 : Blo 766334 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B13988963 : Blo 766334 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B2455147 : Blo 766334 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B2586815 : Blo 766334 2586815 := bstep (se 1 (by rfl) ⟨1940111, by rfl⟩ : syracuseStep 2586815 = 3880223) B3880223
theorem B6322535 : Blo 766334 6322535 := bstep (se 1 (by rfl) ⟨4741901, by rfl⟩ : syracuseStep 6322535 = 9483803) B9483803
theorem B7502503 : Blo 766334 7502503 := bstep (se 1 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 7502503 = 11253755) B11253755
theorem B3898043 : Blo 766334 3898043 := bstep (se 1 (by rfl) ⟨2923532, by rfl⟩ : syracuseStep 3898043 = 5847065) B5847065
theorem B2588435 : Blo 766334 2588435 := bstep (se 1 (by rfl) ⟨1941326, by rfl⟩ : syracuseStep 2588435 = 3882653) B3882653
theorem B2588651 : Blo 766334 2588651 := bstep (se 1 (by rfl) ⟨1941488, by rfl⟩ : syracuseStep 2588651 = 3882977) B3882977
theorem B3899501 : Blo 766334 3899501 := bstep (se 3 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 3899501 = 1462313) B1462313
theorem B2916911 : Blo 766334 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B6226595 : Blo 766334 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B820091 : Blo 766334 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B2589569 : Blo 766334 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B820783 : Blo 766334 820783 := bstep (se 1 (by rfl) ⟨615587, by rfl⟩ : syracuseStep 820783 = 1231175) B1231175
theorem B6228089 : Blo 766334 6228089 := bstep (se 2 (by rfl) ⟨2335533, by rfl⟩ : syracuseStep 6228089 = 4671067) B4671067
theorem B5835887 : Blo 766334 5835887 := bstep (se 1 (by rfl) ⟨4376915, by rfl⟩ : syracuseStep 5835887 = 8753831) B8753831
theorem B1641583 : Blo 766334 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B822479 : Blo 766334 822479 := bstep (se 1 (by rfl) ⟨616859, by rfl⟩ : syracuseStep 822479 = 1233719) B1233719
theorem B2592377 : Blo 766334 2592377 := bstep (se 2 (by rfl) ⟨972141, by rfl⟩ : syracuseStep 2592377 = 1944283) B1944283
theorem B1150601 : Blo 766334 1150601 := bstep (se 2 (by rfl) ⟨431475, by rfl⟩ : syracuseStep 1150601 = 862951) B862951
theorem B28085933 : Blo 766334 28085933 := bstep (se 3 (by rfl) ⟨5266112, by rfl⟩ : syracuseStep 28085933 = 10532225) B10532225
theorem B2625779 : Blo 766334 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B53874953 : Blo 766334 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B3084587 : Blo 766334 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B1151279 : Blo 766334 1151279 := bstep (se 1 (by rfl) ⟨863459, by rfl⟩ : syracuseStep 1151279 = 1726919) B1726919
theorem B1151387 : Blo 766334 1151387 := bstep (se 1 (by rfl) ⟨863540, by rfl⟩ : syracuseStep 1151387 = 1727081) B1727081
theorem B1151579 : Blo 766334 1151579 := bstep (se 1 (by rfl) ⟨863684, by rfl⟩ : syracuseStep 1151579 = 1727369) B1727369
theorem B1381151 : Blo 766334 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B1643591 : Blo 766334 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B6329627 : Blo 766334 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B26645861 : Blo 766334 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B13113251 : Blo 766334 13113251 := bstep (se 1 (by rfl) ⟨9834938, by rfl⟩ : syracuseStep 13113251 = 19669877) B19669877
theorem B1153079 : Blo 766334 1153079 := bstep (se 1 (by rfl) ⟨864809, by rfl⟩ : syracuseStep 1153079 = 1729619) B1729619
theorem B1153127 : Blo 766334 1153127 := bstep (se 1 (by rfl) ⟨864845, by rfl⟩ : syracuseStep 1153127 = 1729691) B1729691
theorem B3283355 : Blo 766334 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B1154729 : Blo 766334 1154729 := bstep (se 2 (by rfl) ⟨433023, by rfl⟩ : syracuseStep 1154729 = 866047) B866047
theorem B1154783 : Blo 766334 1154783 := bstep (se 1 (by rfl) ⟨866087, by rfl⟩ : syracuseStep 1154783 = 1732175) B1732175
theorem B1154879 : Blo 766334 1154879 := bstep (se 1 (by rfl) ⟨866159, by rfl⟩ : syracuseStep 1154879 = 1732319) B1732319
theorem B1843361 : Blo 766334 1843361 := bstep (se 2 (by rfl) ⟨691260, by rfl⟩ : syracuseStep 1843361 = 1382521) B1382521
theorem B10003337 : Blo 766334 10003337 := bstep (se 2 (by rfl) ⟨3751251, by rfl⟩ : syracuseStep 10003337 = 7502503) B7502503
theorem B2598695 : Blo 766334 2598695 := bstep (se 1 (by rfl) ⟨1949021, by rfl⟩ : syracuseStep 2598695 = 3898043) B3898043
theorem B2599073 : Blo 766334 2599073 := bstep (se 2 (by rfl) ⟨974652, by rfl⟩ : syracuseStep 2599073 = 1949305) B1949305
theorem B862375 : Blo 766334 862375 := bstep (se 1 (by rfl) ⟨646781, by rfl⟩ : syracuseStep 862375 = 1293563) B1293563
theorem B863167 : Blo 766334 863167 := bstep (se 1 (by rfl) ⟨647375, by rfl⟩ : syracuseStep 863167 = 1294751) B1294751
theorem B1092703 : Blo 766334 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B1093375 : Blo 766334 1093375 := bstep (se 1 (by rfl) ⟨820031, by rfl⟩ : syracuseStep 1093375 = 1640063) B1640063
theorem B4370719 : Blo 766334 4370719 := bstep (se 1 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 4370719 = 6556079) B6556079
theorem B766447 : Blo 766334 766447 := bstep (se 1 (by rfl) ⟨574835, by rfl⟩ : syracuseStep 766447 = 1149671) B1149671
theorem B6238727 : Blo 766334 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B766511 : Blo 766334 766511 := bstep (se 1 (by rfl) ⟨574883, by rfl⟩ : syracuseStep 766511 = 1149767) B1149767
theorem B766791 : Blo 766334 766791 := bstep (se 1 (by rfl) ⟨575093, by rfl⟩ : syracuseStep 766791 = 1150187) B1150187
theorem B865147 : Blo 766334 865147 := bstep (se 1 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 865147 = 1297721) B1297721
theorem B31470565 : Blo 766334 31470565 := bstep (se 4 (by rfl) ⟨2950365, by rfl⟩ : syracuseStep 31470565 = 5900731) B5900731
theorem B767003 : Blo 766334 767003 := bstep (se 1 (by rfl) ⟨575252, by rfl⟩ : syracuseStep 767003 = 1150505) B1150505
theorem B767087 : Blo 766334 767087 := bstep (se 1 (by rfl) ⟨575315, by rfl⟩ : syracuseStep 767087 = 1150631) B1150631
theorem B767135 : Blo 766334 767135 := bstep (se 1 (by rfl) ⟨575351, by rfl⟩ : syracuseStep 767135 = 1150703) B1150703
theorem B37303901 : Blo 766334 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B1947311 : Blo 766334 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B767679 : Blo 766334 767679 := bstep (se 1 (by rfl) ⟨575759, by rfl⟩ : syracuseStep 767679 = 1151519) B1151519
theorem B767743 : Blo 766334 767743 := bstep (se 1 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 767743 = 1151615) B1151615
theorem B767855 : Blo 766334 767855 := bstep (se 1 (by rfl) ⟨575891, by rfl⟩ : syracuseStep 767855 = 1151783) B1151783
theorem B6567803 : Blo 766334 6567803 := bstep (se 1 (by rfl) ⟨4925852, by rfl⟩ : syracuseStep 6567803 = 9851705) B9851705
theorem B767871 : Blo 766334 767871 := bstep (se 1 (by rfl) ⟨575903, by rfl⟩ : syracuseStep 767871 = 1151807) B1151807
theorem B768251 : Blo 766334 768251 := bstep (se 1 (by rfl) ⟨576188, by rfl⟩ : syracuseStep 768251 = 1152377) B1152377
theorem B1554751 : Blo 766334 1554751 := bstep (se 1 (by rfl) ⟨1166063, by rfl⟩ : syracuseStep 1554751 = 2332127) B2332127
theorem B768411 : Blo 766334 768411 := bstep (se 1 (by rfl) ⟨576308, by rfl⟩ : syracuseStep 768411 = 1152617) B1152617
theorem B768495 : Blo 766334 768495 := bstep (se 1 (by rfl) ⟨576371, by rfl⟩ : syracuseStep 768495 = 1152743) B1152743
theorem B768767 : Blo 766334 768767 := bstep (se 1 (by rfl) ⟨576575, by rfl⟩ : syracuseStep 768767 = 1153151) B1153151
theorem B1555271 : Blo 766334 1555271 := bstep (se 1 (by rfl) ⟨1166453, by rfl⟩ : syracuseStep 1555271 = 2332907) B2332907
theorem B769055 : Blo 766334 769055 := bstep (se 1 (by rfl) ⟨576791, by rfl⟩ : syracuseStep 769055 = 1153583) B1153583
theorem B769327 : Blo 766334 769327 := bstep (se 1 (by rfl) ⟨576995, by rfl⟩ : syracuseStep 769327 = 1153991) B1153991
theorem B1949255 : Blo 766334 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B769639 : Blo 766334 769639 := bstep (se 1 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 769639 = 1154459) B1154459
theorem B769743 : Blo 766334 769743 := bstep (se 1 (by rfl) ⟨577307, by rfl⟩ : syracuseStep 769743 = 1154615) B1154615
theorem B769791 : Blo 766334 769791 := bstep (se 1 (by rfl) ⟨577343, by rfl⟩ : syracuseStep 769791 = 1154687) B1154687
theorem B1949609 : Blo 766334 1949609 := bstep (se 2 (by rfl) ⟨731103, by rfl⟩ : syracuseStep 1949609 = 1462207) B1462207
theorem B770299 : Blo 766334 770299 := bstep (se 1 (by rfl) ⟨577724, by rfl⟩ : syracuseStep 770299 = 1155449) B1155449
theorem B770331 : Blo 766334 770331 := bstep (se 1 (by rfl) ⟨577748, by rfl⟩ : syracuseStep 770331 = 1155497) B1155497
theorem B2770679 : Blo 766334 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B8406979 : Blo 766334 8406979 := bstep (se 1 (by rfl) ⟨6305234, by rfl⟩ : syracuseStep 8406979 = 12610469) B12610469
theorem B22136813 : Blo 766334 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B57657491 : Blo 766334 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B3885245 : Blo 766334 3885245 := bstep (se 3 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 3885245 = 1456967) B1456967
theorem B56905193 : Blo 766334 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B14798699 : Blo 766334 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B1724543 : Blo 766334 1724543 := bstep (se 1 (by rfl) ⟨1293407, by rfl⟩ : syracuseStep 1724543 = 2586815) B2586815
theorem B14012605 : Blo 766334 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B4215023 : Blo 766334 4215023 := bstep (se 1 (by rfl) ⟨3161267, by rfl⟩ : syracuseStep 4215023 = 6322535) B6322535
theorem B1299449 : Blo 766334 1299449 := bstep (se 2 (by rfl) ⟨487293, by rfl⟩ : syracuseStep 1299449 = 974587) B974587
theorem B1725623 : Blo 766334 1725623 := bstep (se 1 (by rfl) ⟨1294217, by rfl⟩ : syracuseStep 1725623 = 2588435) B2588435
theorem B1725767 : Blo 766334 1725767 := bstep (se 1 (by rfl) ⟨1294325, by rfl⟩ : syracuseStep 1725767 = 2588651) B2588651
theorem B2184745 : Blo 766334 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B6313555 : Blo 766334 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B4216411 : Blo 766334 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1727207 : Blo 766334 1727207 := bstep (se 1 (by rfl) ⟨1295405, by rfl⟩ : syracuseStep 1727207 = 2590811) B2590811
theorem B3890267 : Blo 766334 3890267 := bstep (se 1 (by rfl) ⟨2917700, by rfl⟩ : syracuseStep 3890267 = 5835401) B5835401
theorem B1728359 : Blo 766334 1728359 := bstep (se 1 (by rfl) ⟨1296269, by rfl⟩ : syracuseStep 1728359 = 2592539) B2592539
theorem B1728377 : Blo 766334 1728377 := bstep (se 2 (by rfl) ⟨648141, by rfl⟩ : syracuseStep 1728377 = 1296283) B1296283
theorem B1728737 : Blo 766334 1728737 := bstep (se 2 (by rfl) ⟨648276, by rfl⟩ : syracuseStep 1728737 = 1296553) B1296553
theorem B1729673 : Blo 766334 1729673 := bstep (se 2 (by rfl) ⟨648627, by rfl⟩ : syracuseStep 1729673 = 1297255) B1297255
theorem B5334247 : Blo 766334 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B1729799 : Blo 766334 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B2188937 : Blo 766334 2188937 := bstep (se 2 (by rfl) ⟨820851, by rfl⟩ : syracuseStep 2188937 = 1641703) B1641703
theorem B1731113 : Blo 766334 1731113 := bstep (se 2 (by rfl) ⟨649167, by rfl⟩ : syracuseStep 1731113 = 1298335) B1298335
theorem B2910775 : Blo 766334 2910775 := bstep (se 1 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 2910775 = 4366163) B4366163
theorem B11102831 : Blo 766334 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B2190361 : Blo 766334 2190361 := bstep (se 2 (by rfl) ⟨821385, by rfl⟩ : syracuseStep 2190361 = 1642771) B1642771
theorem B1731815 : Blo 766334 1731815 := bstep (se 1 (by rfl) ⟨1298861, by rfl⟩ : syracuseStep 1731815 = 2597723) B2597723
theorem B4387031 : Blo 766334 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B1732895 : Blo 766334 1732895 := bstep (se 1 (by rfl) ⟨1299671, by rfl⟩ : syracuseStep 1732895 = 2599343) B2599343
theorem B3273529 : Blo 766334 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B9860363 : Blo 766334 9860363 := bstep (se 1 (by rfl) ⟨7395272, by rfl⟩ : syracuseStep 9860363 = 14790545) B14790545
theorem B6550955 : Blo 766334 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B3274607 : Blo 766334 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B7895231 : Blo 766334 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B2587679 : Blo 766334 2587679 := bstep (se 1 (by rfl) ⟨1940759, by rfl⟩ : syracuseStep 2587679 = 3881519) B3881519
theorem B3898529 : Blo 766334 3898529 := bstep (se 2 (by rfl) ⟨1461948, by rfl⟩ : syracuseStep 3898529 = 2923897) B2923897
theorem B2588543 : Blo 766334 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B38438327 : Blo 766334 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B2590163 : Blo 766334 2590163 := bstep (se 1 (by rfl) ⟨1942622, by rfl⟩ : syracuseStep 2590163 = 3885245) B3885245
theorem B7112329 : Blo 766334 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B9865799 : Blo 766334 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B1149695 : Blo 766334 1149695 := bstep (se 1 (by rfl) ⟨862271, by rfl⟩ : syracuseStep 1149695 = 1724543) B1724543
theorem B35916635 : Blo 766334 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B1149833 : Blo 766334 1149833 := bstep (se 2 (by rfl) ⟨431187, by rfl⟩ : syracuseStep 1149833 = 862375) B862375
theorem B1150415 : Blo 766334 1150415 := bstep (se 1 (by rfl) ⟨862811, by rfl⟩ : syracuseStep 1150415 = 1725623) B1725623
theorem B1150511 : Blo 766334 1150511 := bstep (se 1 (by rfl) ⟨862883, by rfl⟩ : syracuseStep 1150511 = 1725767) B1725767
theorem B17763907 : Blo 766334 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B1150889 : Blo 766334 1150889 := bstep (se 2 (by rfl) ⟨431583, by rfl⟩ : syracuseStep 1150889 = 863167) B863167
theorem B2920481 : Blo 766334 2920481 := bstep (se 2 (by rfl) ⟨1095180, by rfl⟩ : syracuseStep 2920481 = 2190361) B2190361
theorem B1151471 : Blo 766334 1151471 := bstep (se 1 (by rfl) ⟨863603, by rfl⟩ : syracuseStep 1151471 = 1727207) B1727207
theorem B2593511 : Blo 766334 2593511 := bstep (se 1 (by rfl) ⟨1945133, by rfl⟩ : syracuseStep 2593511 = 3890267) B3890267
theorem B1152239 : Blo 766334 1152239 := bstep (se 1 (by rfl) ⟨864179, by rfl⟩ : syracuseStep 1152239 = 1728359) B1728359
theorem B1152251 : Blo 766334 1152251 := bstep (se 1 (by rfl) ⟨864188, by rfl⟩ : syracuseStep 1152251 = 1728377) B1728377
theorem B1152491 : Blo 766334 1152491 := bstep (se 1 (by rfl) ⟨864368, by rfl⟩ : syracuseStep 1152491 = 1728737) B1728737
theorem B18683473 : Blo 766334 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B1153115 : Blo 766334 1153115 := bstep (se 1 (by rfl) ⟨864836, by rfl⟩ : syracuseStep 1153115 = 1729673) B1729673
theorem B1153199 : Blo 766334 1153199 := bstep (se 1 (by rfl) ⟨864899, by rfl⟩ : syracuseStep 1153199 = 1729799) B1729799
theorem B4364705 : Blo 766334 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B1153529 : Blo 766334 1153529 := bstep (se 2 (by rfl) ⟨432573, by rfl⟩ : syracuseStep 1153529 = 865147) B865147
theorem B1154075 : Blo 766334 1154075 := bstep (se 1 (by rfl) ⟨865556, by rfl⟩ : syracuseStep 1154075 = 1731113) B1731113
theorem B1154543 : Blo 766334 1154543 := bstep (se 1 (by rfl) ⟨865907, by rfl⟩ : syracuseStep 1154543 = 1731815) B1731815
theorem B2924687 : Blo 766334 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B1155263 : Blo 766334 1155263 := bstep (se 1 (by rfl) ⟨866447, by rfl⟩ : syracuseStep 1155263 = 1732895) B1732895
theorem B2073001 : Blo 766334 2073001 := bstep (se 2 (by rfl) ⟨777375, by rfl⟩ : syracuseStep 2073001 = 1554751) B1554751
theorem B4367303 : Blo 766334 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B2599019 : Blo 766334 2599019 := bstep (se 1 (by rfl) ⟨1949264, by rfl⟩ : syracuseStep 2599019 = 3898529) B3898529
theorem B44837221 : Blo 766334 44837221 := bstep (se 4 (by rfl) ⟨4203489, by rfl⟩ : syracuseStep 44837221 = 8406979) B8406979
theorem B2599667 : Blo 766334 2599667 := bstep (se 1 (by rfl) ⟨1949750, by rfl⟩ : syracuseStep 2599667 = 3899501) B3899501
theorem B1944607 : Blo 766334 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B1847119 : Blo 766334 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B14757875 : Blo 766334 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B3683069 : Blo 766334 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B767067 : Blo 766334 767067 := bstep (se 1 (by rfl) ⟨575300, by rfl⟩ : syracuseStep 767067 = 1150601) B1150601
theorem B18723955 : Blo 766334 18723955 := bstep (se 1 (by rfl) ⟨14042966, by rfl⟩ : syracuseStep 18723955 = 28085933) B28085933
theorem B1750519 : Blo 766334 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B767519 : Blo 766334 767519 := bstep (se 1 (by rfl) ⟨575639, by rfl⟩ : syracuseStep 767519 = 1151279) B1151279
theorem B767591 : Blo 766334 767591 := bstep (se 1 (by rfl) ⟨575693, by rfl⟩ : syracuseStep 767591 = 1151387) B1151387
theorem B767719 : Blo 766334 767719 := bstep (se 1 (by rfl) ⟨575789, by rfl⟩ : syracuseStep 767719 = 1151579) B1151579
theorem B866299 : Blo 766334 866299 := bstep (se 1 (by rfl) ⟨649724, by rfl⟩ : syracuseStep 866299 = 1299449) B1299449
theorem B3881033 : Blo 766334 3881033 := bstep (se 2 (by rfl) ⟨1455387, by rfl⟩ : syracuseStep 3881033 = 2910775) B2910775
theorem B768719 : Blo 766334 768719 := bstep (se 1 (by rfl) ⟨576539, by rfl⟩ : syracuseStep 768719 = 1153079) B1153079
theorem B768751 : Blo 766334 768751 := bstep (se 1 (by rfl) ⟨576563, by rfl⟩ : syracuseStep 768751 = 1153127) B1153127
theorem B1456937 : Blo 766334 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B1457833 : Blo 766334 1457833 := bstep (se 2 (by rfl) ⟨546687, by rfl⟩ : syracuseStep 1457833 = 1093375) B1093375
theorem B769819 : Blo 766334 769819 := bstep (se 1 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 769819 = 1154729) B1154729
theorem B769855 : Blo 766334 769855 := bstep (se 1 (by rfl) ⟨577391, by rfl⟩ : syracuseStep 769855 = 1154783) B1154783
theorem B769919 : Blo 766334 769919 := bstep (se 1 (by rfl) ⟨577439, by rfl⟩ : syracuseStep 769919 = 1154879) B1154879
theorem B1228907 : Blo 766334 1228907 := bstep (se 1 (by rfl) ⟨921680, by rfl⟩ : syracuseStep 1228907 = 1843361) B1843361
theorem B6668891 : Blo 766334 6668891 := bstep (se 1 (by rfl) ⟨5001668, by rfl⟩ : syracuseStep 6668891 = 10003337) B10003337
theorem B1459291 : Blo 766334 1459291 := bstep (se 1 (by rfl) ⟨1094468, by rfl⟩ : syracuseStep 1459291 = 2188937) B2188937
theorem B41960753 : Blo 766334 41960753 := bstep (se 2 (by rfl) ⟨15735282, by rfl⟩ : syracuseStep 41960753 = 31470565) B31470565
theorem B5621881 : Blo 766334 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B4377509 : Blo 766334 4377509 := bstep (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) B820783
theorem B6573575 : Blo 766334 6573575 := bstep (se 1 (by rfl) ⟨4930181, by rfl⟩ : syracuseStep 6573575 = 9860363) B9860363
theorem B1298207 : Blo 766334 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B2183071 : Blo 766334 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B4378535 : Blo 766334 4378535 := bstep (se 1 (by rfl) ⟨3283901, by rfl⟩ : syracuseStep 4378535 = 6567803) B6567803
theorem B5263487 : Blo 766334 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B1036847 : Blo 766334 1036847 := bstep (se 1 (by rfl) ⟨777635, by rfl⟩ : syracuseStep 1036847 = 1555271) B1555271
theorem B1725119 : Blo 766334 1725119 := bstep (se 1 (by rfl) ⟨1293839, by rfl⟩ : syracuseStep 1725119 = 2587679) B2587679
theorem B1299503 : Blo 766334 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B1725695 : Blo 766334 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B1299739 : Blo 766334 1299739 := bstep (se 1 (by rfl) ⟨974804, by rfl⟩ : syracuseStep 1299739 = 1949609) B1949609
theorem B4151063 : Blo 766334 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B1726379 : Blo 766334 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B4152059 : Blo 766334 4152059 := bstep (se 1 (by rfl) ⟨3114044, by rfl⟩ : syracuseStep 4152059 = 6228089) B6228089
theorem B3890591 : Blo 766334 3890591 := bstep (se 1 (by rfl) ⟨2917943, by rfl⟩ : syracuseStep 3890591 = 5835887) B5835887
theorem B37936795 : Blo 766334 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B2186909 : Blo 766334 2186909 := bstep (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) B820091
theorem B1728251 : Blo 766334 1728251 := bstep (se 1 (by rfl) ⟨1296188, by rfl⟩ : syracuseStep 1728251 = 2592377) B2592377
theorem B2810015 : Blo 766334 2810015 := bstep (se 1 (by rfl) ⟨2107511, by rfl⟩ : syracuseStep 2810015 = 4215023) B4215023
theorem B4382909 : Blo 766334 4382909 := bstep (se 3 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 4382909 = 1643591) B1643591
theorem B2056391 : Blo 766334 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B4219751 : Blo 766334 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B8742167 : Blo 766334 8742167 := bstep (se 1 (by rfl) ⟨6556625, by rfl⟩ : syracuseStep 8742167 = 13113251) B13113251
theorem B2188777 : Blo 766334 2188777 := bstep (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) B1641583
theorem B2188903 : Blo 766334 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B5827625 : Blo 766334 5827625 := bstep (se 2 (by rfl) ⟨2185359, by rfl⟩ : syracuseStep 5827625 = 4370719) B4370719
theorem B1732463 : Blo 766334 1732463 := bstep (se 1 (by rfl) ⟨1299347, by rfl⟩ : syracuseStep 1732463 = 2598695) B2598695
theorem B1732715 : Blo 766334 1732715 := bstep (se 1 (by rfl) ⟨1299536, by rfl⟩ : syracuseStep 1732715 = 2599073) B2599073
theorem B7401887 : Blo 766334 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B2912993 : Blo 766334 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B8418073 : Blo 766334 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B4159151 : Blo 766334 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B2193277 : Blo 766334 2193277 := bstep (se 3 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 2193277 = 822479) B822479
theorem B24869267 : Blo 766334 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B819271 : Blo 766334 819271 := bstep (se 1 (by rfl) ⟨614453, by rfl⟩ : syracuseStep 819271 = 1228907) B1228907
theorem B2918339 : Blo 766334 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B2918369 : Blo 766334 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B2918537 : Blo 766334 2918537 := bstep (se 2 (by rfl) ⟨1094451, by rfl⟩ : syracuseStep 2918537 = 2188903) B2188903
theorem B2919023 : Blo 766334 2919023 := bstep (se 1 (by rfl) ⟨2189267, by rfl⟩ : syracuseStep 2919023 = 4378535) B4378535
theorem B3508991 : Blo 766334 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B1150079 : Blo 766334 1150079 := bstep (se 1 (by rfl) ⟨862559, by rfl⟩ : syracuseStep 1150079 = 1725119) B1725119
theorem B1150463 : Blo 766334 1150463 := bstep (se 1 (by rfl) ⟨862847, by rfl⟩ : syracuseStep 1150463 = 1725695) B1725695
theorem B102502205 : Blo 766334 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B1150919 : Blo 766334 1150919 := bstep (se 1 (by rfl) ⟨863189, by rfl⟩ : syracuseStep 1150919 = 1726379) B1726379
theorem B2592809 : Blo 766334 2592809 := bstep (se 2 (by rfl) ⟨972303, by rfl⟩ : syracuseStep 2592809 = 1944607) B1944607
theorem B2593727 : Blo 766334 2593727 := bstep (se 1 (by rfl) ⟨1945295, by rfl⟩ : syracuseStep 2593727 = 3890591) B3890591
theorem B2462825 : Blo 766334 2462825 := bstep (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) B1847119
theorem B1152167 : Blo 766334 1152167 := bstep (se 1 (by rfl) ⟨864125, by rfl⟩ : syracuseStep 1152167 = 1728251) B1728251
theorem B1873343 : Blo 766334 1873343 := bstep (se 1 (by rfl) ⟨1405007, by rfl⟩ : syracuseStep 1873343 = 2810015) B2810015
theorem B2921939 : Blo 766334 2921939 := bstep (se 1 (by rfl) ⟨2191454, by rfl⟩ : syracuseStep 2921939 = 4382909) B4382909
theorem B2334025 : Blo 766334 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B24911297 : Blo 766334 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B2924369 : Blo 766334 2924369 := bstep (se 2 (by rfl) ⟨1096638, by rfl⟩ : syracuseStep 2924369 = 2193277) B2193277
theorem B1154975 : Blo 766334 1154975 := bstep (se 1 (by rfl) ⟨866231, by rfl⟩ : syracuseStep 1154975 = 1732463) B1732463
theorem B9838583 : Blo 766334 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B1155065 : Blo 766334 1155065 := bstep (se 2 (by rfl) ⟨433149, by rfl⟩ : syracuseStep 1155065 = 866299) B866299
theorem B1155143 : Blo 766334 1155143 := bstep (se 1 (by rfl) ⟨866357, by rfl⟩ : syracuseStep 1155143 = 1732715) B1732715
theorem B1941995 : Blo 766334 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B1943777 : Blo 766334 1943777 := bstep (se 2 (by rfl) ⟨728916, by rfl⟩ : syracuseStep 1943777 = 1457833) B1457833
theorem B2764001 : Blo 766334 2764001 := bstep (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) B2073001
theorem B1945721 : Blo 766334 1945721 := bstep (se 2 (by rfl) ⟨729645, by rfl⟩ : syracuseStep 1945721 = 1459291) B1459291
theorem B2764925 : Blo 766334 2764925 := bstep (se 3 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 2764925 = 1036847) B1036847
theorem B766463 : Blo 766334 766463 := bstep (se 1 (by rfl) ⟨574847, by rfl⟩ : syracuseStep 766463 = 1149695) B1149695
theorem B766555 : Blo 766334 766555 := bstep (se 1 (by rfl) ⟨574916, by rfl⟩ : syracuseStep 766555 = 1149833) B1149833
theorem B11252669 : Blo 766334 11252669 := bstep (se 3 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 11252669 = 4219751) B4219751
theorem B766943 : Blo 766334 766943 := bstep (se 1 (by rfl) ⟨575207, by rfl⟩ : syracuseStep 766943 = 1150415) B1150415
theorem B767007 : Blo 766334 767007 := bstep (se 1 (by rfl) ⟨575255, by rfl⟩ : syracuseStep 767007 = 1150511) B1150511
theorem B865471 : Blo 766334 865471 := bstep (se 1 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 865471 = 1298207) B1298207
theorem B767259 : Blo 766334 767259 := bstep (se 1 (by rfl) ⟨575444, by rfl⟩ : syracuseStep 767259 = 1150889) B1150889
theorem B1946987 : Blo 766334 1946987 := bstep (se 1 (by rfl) ⟨1460240, by rfl⟩ : syracuseStep 1946987 = 2920481) B2920481
theorem B767647 : Blo 766334 767647 := bstep (se 1 (by rfl) ⟨575735, by rfl⟩ : syracuseStep 767647 = 1151471) B1151471
theorem B59782961 : Blo 766334 59782961 := bstep (se 2 (by rfl) ⟨22418610, by rfl⟩ : syracuseStep 59782961 = 44837221) B44837221
theorem B866335 : Blo 766334 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B768159 : Blo 766334 768159 := bstep (se 1 (by rfl) ⟨576119, by rfl⟩ : syracuseStep 768159 = 1152239) B1152239
theorem B768167 : Blo 766334 768167 := bstep (se 1 (by rfl) ⟨576125, by rfl⟩ : syracuseStep 768167 = 1152251) B1152251
theorem B768327 : Blo 766334 768327 := bstep (se 1 (by rfl) ⟨576245, by rfl⟩ : syracuseStep 768327 = 1152491) B1152491
theorem B2767375 : Blo 766334 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B768743 : Blo 766334 768743 := bstep (se 1 (by rfl) ⟨576557, by rfl⟩ : syracuseStep 768743 = 1153115) B1153115
theorem B768799 : Blo 766334 768799 := bstep (se 1 (by rfl) ⟨576599, by rfl⟩ : syracuseStep 768799 = 1153199) B1153199
theorem B769019 : Blo 766334 769019 := bstep (se 1 (by rfl) ⟨576764, by rfl⟩ : syracuseStep 769019 = 1153529) B1153529
theorem B2768039 : Blo 766334 2768039 := bstep (se 1 (by rfl) ⟨2076029, by rfl⟩ : syracuseStep 2768039 = 4152059) B4152059
theorem B769383 : Blo 766334 769383 := bstep (se 1 (by rfl) ⟨577037, by rfl⟩ : syracuseStep 769383 = 1154075) B1154075
theorem B769695 : Blo 766334 769695 := bstep (se 1 (by rfl) ⟨577271, by rfl⟩ : syracuseStep 769695 = 1154543) B1154543
theorem B1457939 : Blo 766334 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B1949791 : Blo 766334 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B770175 : Blo 766334 770175 := bstep (se 1 (by rfl) ⟨577631, by rfl⟩ : syracuseStep 770175 = 1155263) B1155263
theorem B11224097 : Blo 766334 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B3885083 : Blo 766334 3885083 := bstep (se 1 (by rfl) ⟨2913812, by rfl⟩ : syracuseStep 3885083 = 5827625) B5827625
theorem B4934591 : Blo 766334 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B37932421 : Blo 766334 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B2772767 : Blo 766334 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B971291 : Blo 766334 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B50582393 : Blo 766334 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B4445927 : Blo 766334 4445927 := bstep (se 1 (by rfl) ⟨3334445, by rfl⟩ : syracuseStep 4445927 = 6668891) B6668891
theorem B27973835 : Blo 766334 27973835 := bstep (se 1 (by rfl) ⟨20980376, by rfl⟩ : syracuseStep 27973835 = 41960753) B41960753
theorem B1726775 : Blo 766334 1726775 := bstep (se 1 (by rfl) ⟨1295081, by rfl⟩ : syracuseStep 1726775 = 2590163) B2590163
theorem B6577199 : Blo 766334 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B23944423 : Blo 766334 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B4382383 : Blo 766334 4382383 := bstep (se 1 (by rfl) ⟨3286787, by rfl⟩ : syracuseStep 4382383 = 6573575) B6573575
theorem B7495841 : Blo 766334 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B1729007 : Blo 766334 1729007 := bstep (se 1 (by rfl) ⟨1296755, by rfl⟩ : syracuseStep 1729007 = 2593511) B2593511
theorem B2909803 : Blo 766334 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B23685209 : Blo 766334 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B2910761 : Blo 766334 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B1370927 : Blo 766334 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B2911535 : Blo 766334 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B5828111 : Blo 766334 5828111 := bstep (se 1 (by rfl) ⟨4371083, by rfl⟩ : syracuseStep 5828111 = 8742167) B8742167
theorem B1732679 : Blo 766334 1732679 := bstep (se 1 (by rfl) ⟨1299509, by rfl⟩ : syracuseStep 1732679 = 2599019) B2599019
theorem B24965273 : Blo 766334 24965273 := bstep (se 2 (by rfl) ⟨9361977, by rfl⟩ : syracuseStep 24965273 = 18723955) B18723955
theorem B1732985 : Blo 766334 1732985 := bstep (se 2 (by rfl) ⟨649869, by rfl⟩ : syracuseStep 1732985 = 1299739) B1299739
theorem B1733111 : Blo 766334 1733111 := bstep (se 1 (by rfl) ⟨1299833, by rfl⟩ : syracuseStep 1733111 = 2599667) B2599667
theorem B2455379 : Blo 766334 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B2587355 : Blo 766334 2587355 := bstep (se 1 (by rfl) ⟨1940516, by rfl⟩ : syracuseStep 2587355 = 3881033) B3881033
theorem B16579511 : Blo 766334 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B2590055 : Blo 766334 2590055 := bstep (se 1 (by rfl) ⟨1942541, by rfl⟩ : syracuseStep 2590055 = 3885083) B3885083
theorem B2590109 : Blo 766334 2590109 := bstep (se 3 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 2590109 = 971291) B971291
theorem B33721595 : Blo 766334 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B1641883 : Blo 766334 1641883 := bstep (se 1 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 1641883 = 2462825) B2462825
theorem B1248895 : Blo 766334 1248895 := bstep (se 1 (by rfl) ⟨936671, by rfl⟩ : syracuseStep 1248895 = 1873343) B1873343
theorem B18649223 : Blo 766334 18649223 := bstep (se 1 (by rfl) ⟨13986917, by rfl⟩ : syracuseStep 18649223 = 27973835) B27973835
theorem B1151183 : Blo 766334 1151183 := bstep (se 1 (by rfl) ⟨863387, by rfl⟩ : syracuseStep 1151183 = 1726775) B1726775
theorem B159421229 : Blo 766334 159421229 := bstep (se 3 (by rfl) ⟨29891480, by rfl⟩ : syracuseStep 159421229 = 59782961) B59782961
theorem B6559055 : Blo 766334 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B1152671 : Blo 766334 1152671 := bstep (se 1 (by rfl) ⟨864503, by rfl⟩ : syracuseStep 1152671 = 1729007) B1729007
theorem B1153961 : Blo 766334 1153961 := bstep (se 2 (by rfl) ⟨432735, by rfl⟩ : syracuseStep 1153961 = 865471) B865471
theorem B1940507 : Blo 766334 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B1941023 : Blo 766334 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B1155113 : Blo 766334 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B1155119 : Blo 766334 1155119 := bstep (se 1 (by rfl) ⟨866339, by rfl⟩ : syracuseStep 1155119 = 1732679) B1732679
theorem B1843283 : Blo 766334 1843283 := bstep (se 1 (by rfl) ⟨1382462, by rfl⟩ : syracuseStep 1843283 = 2764925) B2764925
theorem B1155323 : Blo 766334 1155323 := bstep (se 1 (by rfl) ⟨866492, by rfl⟩ : syracuseStep 1155323 = 1732985) B1732985
theorem B1155407 : Blo 766334 1155407 := bstep (se 1 (by rfl) ⟨866555, by rfl⟩ : syracuseStep 1155407 = 1733111) B1733111
theorem B31925897 : Blo 766334 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B11053007 : Blo 766334 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B1845359 : Blo 766334 1845359 := bstep (se 1 (by rfl) ⟨1384019, by rfl⟩ : syracuseStep 1845359 = 2768039) B2768039
theorem B5843177 : Blo 766334 5843177 := bstep (se 2 (by rfl) ⟨2191191, by rfl⟩ : syracuseStep 5843177 = 4382383) B4382383
theorem B1092361 : Blo 766334 1092361 := bstep (se 2 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 1092361 = 819271) B819271
theorem B2599721 : Blo 766334 2599721 := bstep (se 2 (by rfl) ⟨974895, by rfl⟩ : syracuseStep 2599721 = 1949791) B1949791
theorem B7482731 : Blo 766334 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B1945559 : Blo 766334 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B1945579 : Blo 766334 1945579 := bstep (se 1 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 1945579 = 2918369) B2918369
theorem B1945691 : Blo 766334 1945691 := bstep (se 1 (by rfl) ⟨1459268, by rfl⟩ : syracuseStep 1945691 = 2918537) B2918537
theorem B1946015 : Blo 766334 1946015 := bstep (se 1 (by rfl) ⟨1459511, by rfl⟩ : syracuseStep 1946015 = 2919023) B2919023
theorem B2339327 : Blo 766334 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B3289727 : Blo 766334 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B766719 : Blo 766334 766719 := bstep (se 1 (by rfl) ⟨575039, by rfl⟩ : syracuseStep 766719 = 1150079) B1150079
theorem B3879737 : Blo 766334 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B766975 : Blo 766334 766975 := bstep (se 1 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 766975 = 1150463) B1150463
theorem B1848511 : Blo 766334 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B68334803 : Blo 766334 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B767279 : Blo 766334 767279 := bstep (se 1 (by rfl) ⟨575459, by rfl⟩ : syracuseStep 767279 = 1150919) B1150919
theorem B14759333 : Blo 766334 14759333 := bstep (se 4 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 14759333 = 2767375) B2767375
theorem B768111 : Blo 766334 768111 := bstep (se 1 (by rfl) ⟨576083, by rfl⟩ : syracuseStep 768111 = 1152167) B1152167
theorem B1947959 : Blo 766334 1947959 := bstep (se 1 (by rfl) ⟨1460969, by rfl⟩ : syracuseStep 1947959 = 2921939) B2921939
theorem B2963951 : Blo 766334 2963951 := bstep (se 1 (by rfl) ⟨2222963, by rfl⟩ : syracuseStep 2963951 = 4445927) B4445927
theorem B50576561 : Blo 766334 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B1949579 : Blo 766334 1949579 := bstep (se 1 (by rfl) ⟨1462184, by rfl⟩ : syracuseStep 1949579 = 2924369) B2924369
theorem B769983 : Blo 766334 769983 := bstep (se 1 (by rfl) ⟨577487, by rfl⟩ : syracuseStep 769983 = 1154975) B1154975
theorem B770043 : Blo 766334 770043 := bstep (se 1 (by rfl) ⟨577532, by rfl⟩ : syracuseStep 770043 = 1155065) B1155065
theorem B770095 : Blo 766334 770095 := bstep (se 1 (by rfl) ⟨577571, by rfl⟩ : syracuseStep 770095 = 1155143) B1155143
theorem B4997227 : Blo 766334 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1294663 : Blo 766334 1294663 := bstep (se 1 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 1294663 = 1941995) B1941995
theorem B1295851 : Blo 766334 1295851 := bstep (se 1 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 1295851 = 1943777) B1943777
theorem B3885407 : Blo 766334 3885407 := bstep (se 1 (by rfl) ⟨2914055, by rfl⟩ : syracuseStep 3885407 = 5828111) B5828111
theorem B1297147 : Blo 766334 1297147 := bstep (se 1 (by rfl) ⟨972860, by rfl⟩ : syracuseStep 1297147 = 1945721) B1945721
theorem B1297991 : Blo 766334 1297991 := bstep (se 1 (by rfl) ⟨973493, by rfl⟩ : syracuseStep 1297991 = 1946987) B1946987
theorem B1724903 : Blo 766334 1724903 := bstep (se 1 (by rfl) ⟨1293677, by rfl⟩ : syracuseStep 1724903 = 2587355) B2587355
theorem B3887837 : Blo 766334 3887837 := bstep (se 3 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 3887837 = 1457939) B1457939
theorem B30007117 : Blo 766334 30007117 := bstep (se 3 (by rfl) ⟨5626334, by rfl⟩ : syracuseStep 30007117 = 11252669) B11252669
theorem B1728539 : Blo 766334 1728539 := bstep (se 1 (by rfl) ⟨1296404, by rfl⟩ : syracuseStep 1728539 = 2592809) B2592809
theorem B1729151 : Blo 766334 1729151 := bstep (se 1 (by rfl) ⟨1296863, by rfl⟩ : syracuseStep 1729151 = 2593727) B2593727
theorem B4384799 : Blo 766334 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B16607531 : Blo 766334 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B15790139 : Blo 766334 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B913951 : Blo 766334 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B16643515 : Blo 766334 16643515 := bstep (se 1 (by rfl) ⟨12482636, by rfl⟩ : syracuseStep 16643515 = 24965273) B24965273
theorem B7370669 : Blo 766334 7370669 := bstep (se 3 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 7370669 = 2764001) B2764001
theorem B1636919 : Blo 766334 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B3112033 : Blo 766334 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B2590271 : Blo 766334 2590271 := bstep (se 1 (by rfl) ⟨1942703, by rfl⟩ : syracuseStep 2590271 = 3885407) B3885407
theorem B22481063 : Blo 766334 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B1149935 : Blo 766334 1149935 := bstep (se 1 (by rfl) ⟨862451, by rfl⟩ : syracuseStep 1149935 = 1724903) B1724903
theorem B2591891 : Blo 766334 2591891 := bstep (se 1 (by rfl) ⟨1943918, by rfl⟩ : syracuseStep 2591891 = 3887837) B3887837
theorem B2594105 : Blo 766334 2594105 := bstep (se 2 (by rfl) ⟨972789, by rfl⟩ : syracuseStep 2594105 = 1945579) B1945579
theorem B1152359 : Blo 766334 1152359 := bstep (se 1 (by rfl) ⟨864269, by rfl⟩ : syracuseStep 1152359 = 1728539) B1728539
theorem B1152767 : Blo 766334 1152767 := bstep (se 1 (by rfl) ⟨864575, by rfl⟩ : syracuseStep 1152767 = 1729151) B1729151
theorem B1218601 : Blo 766334 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B2923199 : Blo 766334 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B2464681 : Blo 766334 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B22191353 : Blo 766334 22191353 := bstep (se 2 (by rfl) ⟨8321757, by rfl⟩ : syracuseStep 22191353 = 16643515) B16643515
theorem B10526759 : Blo 766334 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B45556535 : Blo 766334 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B9839555 : Blo 766334 9839555 := bstep (se 1 (by rfl) ⟨7379666, by rfl⟩ : syracuseStep 9839555 = 14759333) B14759333
theorem B1975967 : Blo 766334 1975967 := bstep (se 1 (by rfl) ⟨1481975, by rfl⟩ : syracuseStep 1975967 = 2963951) B2963951
theorem B1091279 : Blo 766334 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B6662969 : Blo 766334 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B6238205 : Blo 766334 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B865327 : Blo 766334 865327 := bstep (se 1 (by rfl) ⟨648995, by rfl⟩ : syracuseStep 865327 = 1297991) B1297991
theorem B12432815 : Blo 766334 12432815 := bstep (se 1 (by rfl) ⟨9324611, by rfl⟩ : syracuseStep 12432815 = 18649223) B18649223
theorem B767455 : Blo 766334 767455 := bstep (se 1 (by rfl) ⟨575591, by rfl⟩ : syracuseStep 767455 = 1151183) B1151183
theorem B106280819 : Blo 766334 106280819 := bstep (se 1 (by rfl) ⟨79710614, by rfl⟩ : syracuseStep 106280819 = 159421229) B159421229
theorem B4372703 : Blo 766334 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B1456481 : Blo 766334 1456481 := bstep (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) B1092361
theorem B768447 : Blo 766334 768447 := bstep (se 1 (by rfl) ⟨576335, by rfl⟩ : syracuseStep 768447 = 1152671) B1152671
theorem B769307 : Blo 766334 769307 := bstep (se 1 (by rfl) ⟨576980, by rfl⟩ : syracuseStep 769307 = 1153961) B1153961
theorem B1293671 : Blo 766334 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B1294015 : Blo 766334 1294015 := bstep (se 1 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 1294015 = 1941023) B1941023
theorem B770075 : Blo 766334 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B770079 : Blo 766334 770079 := bstep (se 1 (by rfl) ⟨577559, by rfl⟩ : syracuseStep 770079 = 1155119) B1155119
theorem B1228855 : Blo 766334 1228855 := bstep (se 1 (by rfl) ⟨921641, by rfl⟩ : syracuseStep 1228855 = 1843283) B1843283
theorem B770215 : Blo 766334 770215 := bstep (se 1 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 770215 = 1155323) B1155323
theorem B770271 : Blo 766334 770271 := bstep (se 1 (by rfl) ⟨577703, by rfl⟩ : syracuseStep 770271 = 1155407) B1155407
theorem B44286749 : Blo 766334 44286749 := bstep (se 3 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 44286749 = 16607531) B16607531
theorem B21283931 : Blo 766334 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B1230239 : Blo 766334 1230239 := bstep (se 1 (by rfl) ⟨922679, by rfl⟩ : syracuseStep 1230239 = 1845359) B1845359
theorem B1297039 : Blo 766334 1297039 := bstep (se 1 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 1297039 = 1945559) B1945559
theorem B1297127 : Blo 766334 1297127 := bstep (se 1 (by rfl) ⟨972845, by rfl⟩ : syracuseStep 1297127 = 1945691) B1945691
theorem B1297343 : Blo 766334 1297343 := bstep (se 1 (by rfl) ⟨973007, by rfl⟩ : syracuseStep 1297343 = 1946015) B1946015
theorem B4149377 : Blo 766334 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B1298639 : Blo 766334 1298639 := bstep (se 1 (by rfl) ⟨973979, by rfl⟩ : syracuseStep 1298639 = 1947959) B1947959
theorem B1299719 : Blo 766334 1299719 := bstep (se 1 (by rfl) ⟨974789, by rfl⟩ : syracuseStep 1299719 = 1949579) B1949579
theorem B1726217 : Blo 766334 1726217 := bstep (se 2 (by rfl) ⟨647331, by rfl⟩ : syracuseStep 1726217 = 1294663) B1294663
theorem B1726703 : Blo 766334 1726703 := bstep (se 1 (by rfl) ⟨1295027, by rfl⟩ : syracuseStep 1726703 = 2590055) B2590055
theorem B1726739 : Blo 766334 1726739 := bstep (se 1 (by rfl) ⟨1295054, by rfl⟩ : syracuseStep 1726739 = 2590109) B2590109
theorem B1727801 : Blo 766334 1727801 := bstep (se 2 (by rfl) ⟨647925, by rfl⟩ : syracuseStep 1727801 = 1295851) B1295851
theorem B1729529 : Blo 766334 1729529 := bstep (se 2 (by rfl) ⟨648573, by rfl⟩ : syracuseStep 1729529 = 1297147) B1297147
theorem B2189177 : Blo 766334 2189177 := bstep (se 2 (by rfl) ⟨820941, by rfl⟩ : syracuseStep 2189177 = 1641883) B1641883
theorem B1665193 : Blo 766334 1665193 := bstep (se 2 (by rfl) ⟨624447, by rfl⟩ : syracuseStep 1665193 = 1248895) B1248895
theorem B7368671 : Blo 766334 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B3895451 : Blo 766334 3895451 := bstep (se 1 (by rfl) ⟨2921588, by rfl⟩ : syracuseStep 3895451 = 5843177) B5843177
theorem B1733147 : Blo 766334 1733147 := bstep (se 1 (by rfl) ⟨1299860, by rfl⟩ : syracuseStep 1733147 = 2599721) B2599721
theorem B2193151 : Blo 766334 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B2586491 : Blo 766334 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B19953949 : Blo 766334 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B4913779 : Blo 766334 4913779 := bstep (se 1 (by rfl) ⟨3685334, by rfl⟩ : syracuseStep 4913779 = 7370669) B7370669
theorem B160037957 : Blo 766334 160037957 := bstep (se 4 (by rfl) ⟨15003558, by rfl⟩ : syracuseStep 160037957 = 30007117) B30007117
theorem B33717707 : Blo 766334 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B1638473 : Blo 766334 1638473 := bstep (se 2 (by rfl) ⟨614427, by rfl⟩ : syracuseStep 1638473 = 1228855) B1228855
theorem B29524499 : Blo 766334 29524499 := bstep (se 1 (by rfl) ⟨22143374, by rfl⟩ : syracuseStep 29524499 = 44286749) B44286749
theorem B14189287 : Blo 766334 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B3280637 : Blo 766334 3280637 := bstep (se 3 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 3280637 = 1230239) B1230239
theorem B1150811 : Blo 766334 1150811 := bstep (se 1 (by rfl) ⟨863108, by rfl⟩ : syracuseStep 1150811 = 1726217) B1726217
theorem B1151135 : Blo 766334 1151135 := bstep (se 1 (by rfl) ⟨863351, by rfl⟩ : syracuseStep 1151135 = 1726703) B1726703
theorem B1151159 : Blo 766334 1151159 := bstep (se 1 (by rfl) ⟨863369, by rfl⟩ : syracuseStep 1151159 = 1726739) B1726739
theorem B1151867 : Blo 766334 1151867 := bstep (se 1 (by rfl) ⟨863900, by rfl⟩ : syracuseStep 1151867 = 1727801) B1727801
theorem B7017839 : Blo 766334 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B6559703 : Blo 766334 6559703 := bstep (se 1 (by rfl) ⟨4919777, by rfl⟩ : syracuseStep 6559703 = 9839555) B9839555
theorem B1153019 : Blo 766334 1153019 := bstep (se 1 (by rfl) ⟨864764, by rfl⟩ : syracuseStep 1153019 = 1729529) B1729529
theorem B1317311 : Blo 766334 1317311 := bstep (se 1 (by rfl) ⟨987983, by rfl⟩ : syracuseStep 1317311 = 1975967) B1975967
theorem B1153769 : Blo 766334 1153769 := bstep (se 2 (by rfl) ⟨432663, by rfl⟩ : syracuseStep 1153769 = 865327) B865327
theorem B2924201 : Blo 766334 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B2596967 : Blo 766334 2596967 := bstep (se 1 (by rfl) ⟨1947725, by rfl⟩ : syracuseStep 2596967 = 3895451) B3895451
theorem B1155431 : Blo 766334 1155431 := bstep (se 1 (by rfl) ⟨866573, by rfl⟩ : syracuseStep 1155431 = 1733147) B1733147
theorem B3286241 : Blo 766334 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B70853879 : Blo 766334 70853879 := bstep (se 1 (by rfl) ⟨53140409, by rfl⟩ : syracuseStep 70853879 = 106280819) B106280819
theorem B862447 : Blo 766334 862447 := bstep (se 1 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 862447 = 1293671) B1293671
theorem B14987375 : Blo 766334 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B864751 : Blo 766334 864751 := bstep (se 1 (by rfl) ⟨648563, by rfl⟩ : syracuseStep 864751 = 1297127) B1297127
theorem B864895 : Blo 766334 864895 := bstep (se 1 (by rfl) ⟨648671, by rfl⟩ : syracuseStep 864895 = 1297343) B1297343
theorem B766623 : Blo 766334 766623 := bstep (se 1 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 766623 = 1149935) B1149935
theorem B2766251 : Blo 766334 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B865759 : Blo 766334 865759 := bstep (se 1 (by rfl) ⟨649319, by rfl⟩ : syracuseStep 865759 = 1298639) B1298639
theorem B866479 : Blo 766334 866479 := bstep (se 1 (by rfl) ⟨649859, by rfl⟩ : syracuseStep 866479 = 1299719) B1299719
theorem B768239 : Blo 766334 768239 := bstep (se 1 (by rfl) ⟨576179, by rfl⟩ : syracuseStep 768239 = 1152359) B1152359
theorem B768511 : Blo 766334 768511 := bstep (se 1 (by rfl) ⟨576383, by rfl⟩ : syracuseStep 768511 = 1152767) B1152767
theorem B1948799 : Blo 766334 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B14794235 : Blo 766334 14794235 := bstep (se 1 (by rfl) ⟨11095676, by rfl⟩ : syracuseStep 14794235 = 22191353) B22191353
theorem B3883949 : Blo 766334 3883949 := bstep (se 3 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 3883949 = 1456481) B1456481
theorem B1459451 : Blo 766334 1459451 := bstep (se 1 (by rfl) ⟨1094588, by rfl⟩ : syracuseStep 1459451 = 2189177) B2189177
theorem B4441979 : Blo 766334 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1624801 : Blo 766334 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B1724327 : Blo 766334 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B1725353 : Blo 766334 1725353 := bstep (se 2 (by rfl) ⟨647007, by rfl⟩ : syracuseStep 1725353 = 1294015) B1294015
theorem B1726847 : Blo 766334 1726847 := bstep (se 1 (by rfl) ⟨1295135, by rfl⟩ : syracuseStep 1726847 = 2590271) B2590271
theorem B1727927 : Blo 766334 1727927 := bstep (se 1 (by rfl) ⟨1295945, by rfl⟩ : syracuseStep 1727927 = 2591891) B2591891
theorem B2220257 : Blo 766334 2220257 := bstep (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) B1665193
theorem B1729385 : Blo 766334 1729385 := bstep (se 2 (by rfl) ⟨648519, by rfl⟩ : syracuseStep 1729385 = 1297039) B1297039
theorem B1729403 : Blo 766334 1729403 := bstep (se 1 (by rfl) ⟨1297052, by rfl⟩ : syracuseStep 1729403 = 2594105) B2594105
theorem B2910077 : Blo 766334 2910077 := bstep (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) B1091279
theorem B30371023 : Blo 766334 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B4912447 : Blo 766334 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B4158803 : Blo 766334 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B426767885 : Blo 766334 426767885 := bstep (se 3 (by rfl) ⟨80018978, by rfl⟩ : syracuseStep 426767885 = 160037957) B160037957
theorem B26605265 : Blo 766334 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B6551705 : Blo 766334 6551705 := bstep (se 2 (by rfl) ⟨2456889, by rfl⟩ : syracuseStep 6551705 = 4913779) B4913779
theorem B8288543 : Blo 766334 8288543 := bstep (se 1 (by rfl) ⟨6216407, by rfl⟩ : syracuseStep 8288543 = 12432815) B12432815
theorem B2915135 : Blo 766334 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B22478471 : Blo 766334 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B2589299 : Blo 766334 2589299 := bstep (se 1 (by rfl) ⟨1941974, by rfl⟩ : syracuseStep 2589299 = 3883949) B3883949
theorem B1149551 : Blo 766334 1149551 := bstep (se 1 (by rfl) ⟨862163, by rfl⟩ : syracuseStep 1149551 = 1724327) B1724327
theorem B1149929 : Blo 766334 1149929 := bstep (se 2 (by rfl) ⟨431223, by rfl⟩ : syracuseStep 1149929 = 862447) B862447
theorem B1150235 : Blo 766334 1150235 := bstep (se 1 (by rfl) ⟨862676, by rfl⟩ : syracuseStep 1150235 = 1725353) B1725353
theorem B2166401 : Blo 766334 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B7376669 : Blo 766334 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B1151231 : Blo 766334 1151231 := bstep (se 1 (by rfl) ⟨863423, by rfl⟩ : syracuseStep 1151231 = 1726847) B1726847
theorem B1151951 : Blo 766334 1151951 := bstep (se 1 (by rfl) ⟨863963, by rfl⟩ : syracuseStep 1151951 = 1727927) B1727927
theorem B1152923 : Blo 766334 1152923 := bstep (se 1 (by rfl) ⟨864692, by rfl⟩ : syracuseStep 1152923 = 1729385) B1729385
theorem B1152935 : Blo 766334 1152935 := bstep (se 1 (by rfl) ⟨864701, by rfl⟩ : syracuseStep 1152935 = 1729403) B1729403
theorem B1153001 : Blo 766334 1153001 := bstep (se 2 (by rfl) ⟨432375, by rfl⟩ : syracuseStep 1153001 = 864751) B864751
theorem B1153193 : Blo 766334 1153193 := bstep (se 2 (by rfl) ⟨432447, by rfl⟩ : syracuseStep 1153193 = 864895) B864895
theorem B1940051 : Blo 766334 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B1154345 : Blo 766334 1154345 := bstep (se 2 (by rfl) ⟨432879, by rfl⟩ : syracuseStep 1154345 = 865759) B865759
theorem B1155305 : Blo 766334 1155305 := bstep (se 2 (by rfl) ⟨433239, by rfl⟩ : syracuseStep 1155305 = 866479) B866479
theorem B4367803 : Blo 766334 4367803 := bstep (se 1 (by rfl) ⟨3275852, by rfl⟩ : syracuseStep 4367803 = 6551705) B6551705
theorem B1943423 : Blo 766334 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B14985647 : Blo 766334 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B4369261 : Blo 766334 4369261 := bstep (se 3 (by rfl) ⟨819236, by rfl⟩ : syracuseStep 4369261 = 1638473) B1638473
theorem B18919049 : Blo 766334 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B2961319 : Blo 766334 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B767207 : Blo 766334 767207 := bstep (se 1 (by rfl) ⟨575405, by rfl⟩ : syracuseStep 767207 = 1150811) B1150811
theorem B767423 : Blo 766334 767423 := bstep (se 1 (by rfl) ⟨575567, by rfl⟩ : syracuseStep 767423 = 1151135) B1151135
theorem B767439 : Blo 766334 767439 := bstep (se 1 (by rfl) ⟨575579, by rfl⟩ : syracuseStep 767439 = 1151159) B1151159
theorem B767911 : Blo 766334 767911 := bstep (se 1 (by rfl) ⟨575933, by rfl⟩ : syracuseStep 767911 = 1151867) B1151867
theorem B11090141 : Blo 766334 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B4373135 : Blo 766334 4373135 := bstep (se 1 (by rfl) ⟨3279851, by rfl⟩ : syracuseStep 4373135 = 6559703) B6559703
theorem B768679 : Blo 766334 768679 := bstep (se 1 (by rfl) ⟨576509, by rfl⟩ : syracuseStep 768679 = 1153019) B1153019
theorem B769179 : Blo 766334 769179 := bstep (se 1 (by rfl) ⟨576884, by rfl⟩ : syracuseStep 769179 = 1153769) B1153769
theorem B1949467 : Blo 766334 1949467 := bstep (se 1 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 1949467 = 2924201) B2924201
theorem B770287 : Blo 766334 770287 := bstep (se 1 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 770287 = 1155431) B1155431
theorem B47235919 : Blo 766334 47235919 := bstep (se 1 (by rfl) ⟨35426939, by rfl⟩ : syracuseStep 47235919 = 70853879) B70853879
theorem B283789493 : Blo 766334 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B284511923 : Blo 766334 284511923 := bstep (se 1 (by rfl) ⟨213383942, by rfl⟩ : syracuseStep 284511923 = 426767885) B426767885
theorem B5525695 : Blo 766334 5525695 := bstep (se 1 (by rfl) ⟨4144271, by rfl⟩ : syracuseStep 5525695 = 8288543) B8288543
theorem B1299199 : Blo 766334 1299199 := bstep (se 1 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 1299199 = 1948799) B1948799
theorem B19682999 : Blo 766334 19682999 := bstep (se 1 (by rfl) ⟨14762249, by rfl⟩ : syracuseStep 19682999 = 29524499) B29524499
theorem B5920685 : Blo 766334 5920685 := bstep (se 3 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 5920685 = 2220257) B2220257
theorem B972967 : Blo 766334 972967 := bstep (se 1 (by rfl) ⟨729725, by rfl⟩ : syracuseStep 972967 = 1459451) B1459451
theorem B2187091 : Blo 766334 2187091 := bstep (se 1 (by rfl) ⟨1640318, by rfl⟩ : syracuseStep 2187091 = 3280637) B3280637
theorem B4678559 : Blo 766334 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B40494697 : Blo 766334 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B878207 : Blo 766334 878207 := bstep (se 1 (by rfl) ⟨658655, by rfl⟩ : syracuseStep 878207 = 1317311) B1317311
theorem B1731311 : Blo 766334 1731311 := bstep (se 1 (by rfl) ⟨1298483, by rfl⟩ : syracuseStep 1731311 = 2596967) B2596967
theorem B2190827 : Blo 766334 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B6549929 : Blo 766334 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B9991583 : Blo 766334 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B9862823 : Blo 766334 9862823 := bstep (se 1 (by rfl) ⟨7397117, by rfl⟩ : syracuseStep 9862823 = 14794235) B14794235
theorem B62981225 : Blo 766334 62981225 := bstep (se 2 (by rfl) ⟨23617959, by rfl⟩ : syracuseStep 62981225 = 47235919) B47235919
theorem B1444267 : Blo 766334 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B4917779 : Blo 766334 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B3119039 : Blo 766334 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B1154207 : Blo 766334 1154207 := bstep (se 1 (by rfl) ⟨865655, by rfl⟩ : syracuseStep 1154207 = 1731311) B1731311
theorem B4366619 : Blo 766334 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B6661055 : Blo 766334 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B5842205 : Blo 766334 5842205 := bstep (se 3 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 5842205 = 2190827) B2190827
theorem B2599289 : Blo 766334 2599289 := bstep (se 2 (by rfl) ⟨974733, by rfl⟩ : syracuseStep 2599289 = 1949467) B1949467
theorem B766367 : Blo 766334 766367 := bstep (se 1 (by rfl) ⟨574775, by rfl⟩ : syracuseStep 766367 = 1149551) B1149551
theorem B766619 : Blo 766334 766619 := bstep (se 1 (by rfl) ⟨574964, by rfl⟩ : syracuseStep 766619 = 1149929) B1149929
theorem B766823 : Blo 766334 766823 := bstep (se 1 (by rfl) ⟨575117, by rfl⟩ : syracuseStep 766823 = 1150235) B1150235
theorem B189674615 : Blo 766334 189674615 := bstep (se 1 (by rfl) ⟨142255961, by rfl⟩ : syracuseStep 189674615 = 284511923) B284511923
theorem B767487 : Blo 766334 767487 := bstep (se 1 (by rfl) ⟨575615, by rfl⟩ : syracuseStep 767487 = 1151231) B1151231
theorem B767967 : Blo 766334 767967 := bstep (se 1 (by rfl) ⟨575975, by rfl⟩ : syracuseStep 767967 = 1151951) B1151951
theorem B13121999 : Blo 766334 13121999 := bstep (se 1 (by rfl) ⟨9841499, by rfl⟩ : syracuseStep 13121999 = 19682999) B19682999
theorem B768615 : Blo 766334 768615 := bstep (se 1 (by rfl) ⟨576461, by rfl⟩ : syracuseStep 768615 = 1152923) B1152923
theorem B768623 : Blo 766334 768623 := bstep (se 1 (by rfl) ⟨576467, by rfl⟩ : syracuseStep 768623 = 1152935) B1152935
theorem B3947123 : Blo 766334 3947123 := bstep (se 1 (by rfl) ⟨2960342, by rfl⟩ : syracuseStep 3947123 = 5920685) B5920685
theorem B768667 : Blo 766334 768667 := bstep (se 1 (by rfl) ⟨576500, by rfl⟩ : syracuseStep 768667 = 1153001) B1153001
theorem B768795 : Blo 766334 768795 := bstep (se 1 (by rfl) ⟨576596, by rfl⟩ : syracuseStep 768795 = 1153193) B1153193
theorem B2341885 : Blo 766334 2341885 := bstep (se 3 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 2341885 = 878207) B878207
theorem B1293367 : Blo 766334 1293367 := bstep (se 1 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 1293367 = 1940051) B1940051
theorem B769563 : Blo 766334 769563 := bstep (se 1 (by rfl) ⟨577172, by rfl⟩ : syracuseStep 769563 = 1154345) B1154345
theorem B3948425 : Blo 766334 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B770203 : Blo 766334 770203 := bstep (se 1 (by rfl) ⟨577652, by rfl⟩ : syracuseStep 770203 = 1155305) B1155305
theorem B1295615 : Blo 766334 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B1297289 : Blo 766334 1297289 := bstep (se 2 (by rfl) ⟨486483, by rfl⟩ : syracuseStep 1297289 = 972967) B972967
theorem B7393427 : Blo 766334 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B50450797 : Blo 766334 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B6575215 : Blo 766334 6575215 := bstep (se 1 (by rfl) ⟨4931411, by rfl⟩ : syracuseStep 6575215 = 9862823) B9862823
theorem B1726199 : Blo 766334 1726199 := bstep (se 1 (by rfl) ⟨1294649, by rfl⟩ : syracuseStep 1726199 = 2589299) B2589299
theorem B189192995 : Blo 766334 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B5823737 : Blo 766334 5823737 := bstep (se 2 (by rfl) ⟨2183901, by rfl⟩ : syracuseStep 5823737 = 4367803) B4367803
theorem B5825681 : Blo 766334 5825681 := bstep (se 2 (by rfl) ⟨2184630, by rfl⟩ : syracuseStep 5825681 = 4369261) B4369261
theorem B7367593 : Blo 766334 7367593 := bstep (se 2 (by rfl) ⟨2762847, by rfl⟩ : syracuseStep 7367593 = 5525695) B5525695
theorem B1732265 : Blo 766334 1732265 := bstep (se 2 (by rfl) ⟨649599, by rfl⟩ : syracuseStep 1732265 = 1299199) B1299199
theorem B9990431 : Blo 766334 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B215971717 : Blo 766334 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B2915423 : Blo 766334 2915423 := bstep (se 1 (by rfl) ⟨2186567, by rfl⟩ : syracuseStep 2915423 = 4373135) B4373135
theorem B2916121 : Blo 766334 2916121 := bstep (se 2 (by rfl) ⟨1093545, by rfl⟩ : syracuseStep 2916121 = 2187091) B2187091
theorem B3278519 : Blo 766334 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B1150799 : Blo 766334 1150799 := bstep (se 1 (by rfl) ⟨863099, by rfl⟩ : syracuseStep 1150799 = 1726199) B1726199
theorem B126128663 : Blo 766334 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B1154843 : Blo 766334 1154843 := bstep (se 1 (by rfl) ⟨866132, by rfl⟩ : syracuseStep 1154843 = 1732265) B1732265
theorem B6660287 : Blo 766334 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B3122513 : Blo 766334 3122513 := bstep (se 2 (by rfl) ⟨1170942, by rfl⟩ : syracuseStep 3122513 = 2341885) B2341885
theorem B2631415 : Blo 766334 2631415 := bstep (se 1 (by rfl) ⟨1973561, by rfl⟩ : syracuseStep 2631415 = 3947123) B3947123
theorem B1943615 : Blo 766334 1943615 := bstep (se 1 (by rfl) ⟨1457711, by rfl⟩ : syracuseStep 1943615 = 2915423) B2915423
theorem B2632283 : Blo 766334 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B41987483 : Blo 766334 41987483 := bstep (se 1 (by rfl) ⟨31490612, by rfl⟩ : syracuseStep 41987483 = 62981225) B62981225
theorem B863743 : Blo 766334 863743 := bstep (se 1 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 863743 = 1295615) B1295615
theorem B864859 : Blo 766334 864859 := bstep (se 1 (by rfl) ⟨648644, by rfl⟩ : syracuseStep 864859 = 1297289) B1297289
theorem B4928951 : Blo 766334 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B2079359 : Blo 766334 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B769471 : Blo 766334 769471 := bstep (se 1 (by rfl) ⟨577103, by rfl⟩ : syracuseStep 769471 = 1154207) B1154207
theorem B3882491 : Blo 766334 3882491 := bstep (se 1 (by rfl) ⟨2911868, by rfl⟩ : syracuseStep 3882491 = 5823737) B5823737
theorem B4440703 : Blo 766334 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B3883787 : Blo 766334 3883787 := bstep (se 1 (by rfl) ⟨2912840, by rfl⟩ : syracuseStep 3883787 = 5825681) B5825681
theorem B8766953 : Blo 766334 8766953 := bstep (se 2 (by rfl) ⟨3287607, by rfl⟩ : syracuseStep 8766953 = 6575215) B6575215
theorem B1724489 : Blo 766334 1724489 := bstep (se 2 (by rfl) ⟨646683, by rfl⟩ : syracuseStep 1724489 = 1293367) B1293367
theorem B3888161 : Blo 766334 3888161 := bstep (se 2 (by rfl) ⟨1458060, by rfl⟩ : syracuseStep 3888161 = 2916121) B2916121
theorem B1925689 : Blo 766334 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B9823457 : Blo 766334 9823457 := bstep (se 2 (by rfl) ⟨3683796, by rfl⟩ : syracuseStep 9823457 = 7367593) B7367593
theorem B2911079 : Blo 766334 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B67267729 : Blo 766334 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B3894803 : Blo 766334 3894803 := bstep (se 1 (by rfl) ⟨2921102, by rfl⟩ : syracuseStep 3894803 = 5842205) B5842205
theorem B1732859 : Blo 766334 1732859 := bstep (se 1 (by rfl) ⟨1299644, by rfl⟩ : syracuseStep 1732859 = 2599289) B2599289
theorem B287962289 : Blo 766334 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B126449743 : Blo 766334 126449743 := bstep (se 1 (by rfl) ⟨94837307, by rfl⟩ : syracuseStep 126449743 = 189674615) B189674615
theorem B8747999 : Blo 766334 8747999 := bstep (se 1 (by rfl) ⟨6560999, by rfl⟩ : syracuseStep 8747999 = 13121999) B13121999
theorem B2589191 : Blo 766334 2589191 := bstep (se 1 (by rfl) ⟨1941893, by rfl⟩ : syracuseStep 2589191 = 3883787) B3883787
theorem B3508553 : Blo 766334 3508553 := bstep (se 2 (by rfl) ⟨1315707, by rfl⟩ : syracuseStep 3508553 = 2631415) B2631415
theorem B1149659 : Blo 766334 1149659 := bstep (se 1 (by rfl) ⟨862244, by rfl⟩ : syracuseStep 1149659 = 1724489) B1724489
theorem B84085775 : Blo 766334 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B2592107 : Blo 766334 2592107 := bstep (se 1 (by rfl) ⟨1944080, by rfl⟩ : syracuseStep 2592107 = 3888161) B3888161
theorem B13143869 : Blo 766334 13143869 := bstep (se 3 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 13143869 = 4928951) B4928951
theorem B1151657 : Blo 766334 1151657 := bstep (se 2 (by rfl) ⟨431871, by rfl⟩ : syracuseStep 1151657 = 863743) B863743
theorem B1153145 : Blo 766334 1153145 := bstep (se 2 (by rfl) ⟨432429, by rfl⟩ : syracuseStep 1153145 = 864859) B864859
theorem B1940719 : Blo 766334 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B27991655 : Blo 766334 27991655 := bstep (se 1 (by rfl) ⟨20993741, by rfl⟩ : syracuseStep 27991655 = 41987483) B41987483
theorem B2596535 : Blo 766334 2596535 := bstep (se 1 (by rfl) ⟨1947401, by rfl⟩ : syracuseStep 2596535 = 3894803) B3894803
theorem B168599657 : Blo 766334 168599657 := bstep (se 2 (by rfl) ⟨63224871, by rfl⟩ : syracuseStep 168599657 = 126449743) B126449743
theorem B1155239 : Blo 766334 1155239 := bstep (se 1 (by rfl) ⟨866429, by rfl⟩ : syracuseStep 1155239 = 1732859) B1732859
theorem B1386239 : Blo 766334 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B2567585 : Blo 766334 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B5844635 : Blo 766334 5844635 := bstep (se 1 (by rfl) ⟨4383476, by rfl⟩ : syracuseStep 5844635 = 8766953) B8766953
theorem B767199 : Blo 766334 767199 := bstep (se 1 (by rfl) ⟨575399, by rfl⟩ : syracuseStep 767199 = 1150799) B1150799
theorem B769895 : Blo 766334 769895 := bstep (se 1 (by rfl) ⟨577421, by rfl⟩ : syracuseStep 769895 = 1154843) B1154843
theorem B4440191 : Blo 766334 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B358761221 : Blo 766334 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B2081675 : Blo 766334 2081675 := bstep (se 1 (by rfl) ⟨1561256, by rfl⟩ : syracuseStep 2081675 = 3122513) B3122513
theorem B1295743 : Blo 766334 1295743 := bstep (se 1 (by rfl) ⟨971807, by rfl⟩ : syracuseStep 1295743 = 1943615) B1943615
theorem B1754855 : Blo 766334 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B191974859 : Blo 766334 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B5920937 : Blo 766334 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B2185679 : Blo 766334 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B6548971 : Blo 766334 6548971 := bstep (se 1 (by rfl) ⟨4911728, by rfl⟩ : syracuseStep 6548971 = 9823457) B9823457
theorem B5831999 : Blo 766334 5831999 := bstep (se 1 (by rfl) ⟨4373999, by rfl⟩ : syracuseStep 5831999 = 8747999) B8747999
theorem B2588327 : Blo 766334 2588327 := bstep (se 1 (by rfl) ⟨1941245, by rfl⟩ : syracuseStep 2588327 = 3882491) B3882491
theorem B239174147 : Blo 766334 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B112399771 : Blo 766334 112399771 := bstep (se 1 (by rfl) ⟨84299828, by rfl⟩ : syracuseStep 112399771 = 168599657) B168599657
theorem B14786549 : Blo 766334 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B11840509 : Blo 766334 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B1387783 : Blo 766334 1387783 := bstep (se 1 (by rfl) ⟨1040837, by rfl⟩ : syracuseStep 1387783 = 2081675) B2081675
theorem B766439 : Blo 766334 766439 := bstep (se 1 (by rfl) ⟨574829, by rfl⟩ : syracuseStep 766439 = 1149659) B1149659
theorem B8762579 : Blo 766334 8762579 := bstep (se 1 (by rfl) ⟨6571934, by rfl⟩ : syracuseStep 8762579 = 13143869) B13143869
theorem B767771 : Blo 766334 767771 := bstep (se 1 (by rfl) ⟨575828, by rfl⟩ : syracuseStep 767771 = 1151657) B1151657
theorem B768763 : Blo 766334 768763 := bstep (se 1 (by rfl) ⟨576572, by rfl⟩ : syracuseStep 768763 = 1153145) B1153145
theorem B3947291 : Blo 766334 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B1457119 : Blo 766334 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B8731961 : Blo 766334 8731961 := bstep (se 2 (by rfl) ⟨3274485, by rfl⟩ : syracuseStep 8731961 = 6548971) B6548971
theorem B18661103 : Blo 766334 18661103 := bstep (se 1 (by rfl) ⟨13995827, by rfl⟩ : syracuseStep 18661103 = 27991655) B27991655
theorem B770159 : Blo 766334 770159 := bstep (se 1 (by rfl) ⟨577619, by rfl⟩ : syracuseStep 770159 = 1155239) B1155239
theorem B9356141 : Blo 766334 9356141 := bstep (se 3 (by rfl) ⟨1754276, by rfl⟩ : syracuseStep 9356141 = 3508553) B3508553
theorem B3887999 : Blo 766334 3887999 := bstep (se 1 (by rfl) ⟨2915999, by rfl⟩ : syracuseStep 3887999 = 5831999) B5831999
theorem B1725551 : Blo 766334 1725551 := bstep (se 1 (by rfl) ⟨1294163, by rfl⟩ : syracuseStep 1725551 = 2588327) B2588327
theorem B1726127 : Blo 766334 1726127 := bstep (se 1 (by rfl) ⟨1294595, by rfl⟩ : syracuseStep 1726127 = 2589191) B2589191
theorem B1169903 : Blo 766334 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B1727657 : Blo 766334 1727657 := bstep (se 2 (by rfl) ⟨647871, by rfl⟩ : syracuseStep 1727657 = 1295743) B1295743
theorem B56057183 : Blo 766334 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B1728071 : Blo 766334 1728071 := bstep (se 1 (by rfl) ⟨1296053, by rfl⟩ : syracuseStep 1728071 = 2592107) B2592107
theorem B127983239 : Blo 766334 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B1731023 : Blo 766334 1731023 := bstep (se 1 (by rfl) ⟨1298267, by rfl⟩ : syracuseStep 1731023 = 2596535) B2596535
theorem B3896423 : Blo 766334 3896423 := bstep (se 1 (by rfl) ⟨2922317, by rfl⟩ : syracuseStep 3896423 = 5844635) B5844635
theorem B6846893 : Blo 766334 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B2587625 : Blo 766334 2587625 := bstep (se 2 (by rfl) ⟨970359, by rfl⟩ : syracuseStep 2587625 = 1940719) B1940719
theorem B159449431 : Blo 766334 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B2591999 : Blo 766334 2591999 := bstep (se 1 (by rfl) ⟨1943999, by rfl⟩ : syracuseStep 2591999 = 3887999) B3887999
theorem B1150367 : Blo 766334 1150367 := bstep (se 1 (by rfl) ⟨862775, by rfl⟩ : syracuseStep 1150367 = 1725551) B1725551
theorem B1150751 : Blo 766334 1150751 := bstep (se 1 (by rfl) ⟨863063, by rfl⟩ : syracuseStep 1150751 = 1726127) B1726127
theorem B1151771 : Blo 766334 1151771 := bstep (se 1 (by rfl) ⟨863828, by rfl⟩ : syracuseStep 1151771 = 1727657) B1727657
theorem B1152047 : Blo 766334 1152047 := bstep (se 1 (by rfl) ⟨864035, by rfl⟩ : syracuseStep 1152047 = 1728071) B1728071
theorem B3119741 : Blo 766334 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B1154015 : Blo 766334 1154015 := bstep (se 1 (by rfl) ⟨865511, by rfl⟩ : syracuseStep 1154015 = 1731023) B1731023
theorem B2597615 : Blo 766334 2597615 := bstep (se 1 (by rfl) ⟨1948211, by rfl⟩ : syracuseStep 2597615 = 3896423) B3896423
theorem B5841719 : Blo 766334 5841719 := bstep (se 1 (by rfl) ⟨4381289, by rfl⟩ : syracuseStep 5841719 = 8762579) B8762579
theorem B1942825 : Blo 766334 1942825 := bstep (se 2 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 1942825 = 1457119) B1457119
theorem B4564595 : Blo 766334 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B2631527 : Blo 766334 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B6237427 : Blo 766334 6237427 := bstep (se 1 (by rfl) ⟨4678070, by rfl⟩ : syracuseStep 6237427 = 9356141) B9356141
theorem B1850377 : Blo 766334 1850377 := bstep (se 2 (by rfl) ⟨693891, by rfl⟩ : syracuseStep 1850377 = 1387783) B1387783
theorem B37371455 : Blo 766334 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B149866361 : Blo 766334 149866361 := bstep (se 2 (by rfl) ⟨56199885, by rfl⟩ : syracuseStep 149866361 = 112399771) B112399771
theorem B1725083 : Blo 766334 1725083 := bstep (se 1 (by rfl) ⟨1293812, by rfl⟩ : syracuseStep 1725083 = 2587625) B2587625
theorem B5821307 : Blo 766334 5821307 := bstep (se 1 (by rfl) ⟨4365980, by rfl⟩ : syracuseStep 5821307 = 8731961) B8731961
theorem B12440735 : Blo 766334 12440735 := bstep (se 1 (by rfl) ⟨9330551, by rfl⟩ : syracuseStep 12440735 = 18661103) B18661103
theorem B15787345 : Blo 766334 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B85322159 : Blo 766334 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B9857699 : Blo 766334 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B212599241 : Blo 766334 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B99910907 : Blo 766334 99910907 := bstep (se 1 (by rfl) ⟨74933180, by rfl⟩ : syracuseStep 99910907 = 149866361) B149866361
theorem B2590433 : Blo 766334 2590433 := bstep (se 2 (by rfl) ⟨971412, by rfl⟩ : syracuseStep 2590433 = 1942825) B1942825
theorem B1150055 : Blo 766334 1150055 := bstep (se 1 (by rfl) ⟨862541, by rfl⟩ : syracuseStep 1150055 = 1725083) B1725083
theorem B8293823 : Blo 766334 8293823 := bstep (se 1 (by rfl) ⟨6220367, by rfl⟩ : syracuseStep 8293823 = 12440735) B12440735
theorem B2467169 : Blo 766334 2467169 := bstep (se 2 (by rfl) ⟨925188, by rfl⟩ : syracuseStep 2467169 = 1850377) B1850377
theorem B24914303 : Blo 766334 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B21049793 : Blo 766334 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B766911 : Blo 766334 766911 := bstep (se 1 (by rfl) ⟨575183, by rfl⟩ : syracuseStep 766911 = 1150367) B1150367
theorem B767167 : Blo 766334 767167 := bstep (se 1 (by rfl) ⟨575375, by rfl⟩ : syracuseStep 767167 = 1150751) B1150751
theorem B767847 : Blo 766334 767847 := bstep (se 1 (by rfl) ⟨575885, by rfl⟩ : syracuseStep 767847 = 1151771) B1151771
theorem B3880871 : Blo 766334 3880871 := bstep (se 1 (by rfl) ⟨2910653, by rfl⟩ : syracuseStep 3880871 = 5821307) B5821307
theorem B768031 : Blo 766334 768031 := bstep (se 1 (by rfl) ⟨576023, by rfl⟩ : syracuseStep 768031 = 1152047) B1152047
theorem B2079827 : Blo 766334 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B769343 : Blo 766334 769343 := bstep (se 1 (by rfl) ⟨577007, by rfl⟩ : syracuseStep 769343 = 1154015) B1154015
theorem B1754351 : Blo 766334 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B6571799 : Blo 766334 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B1727999 : Blo 766334 1727999 := bstep (se 1 (by rfl) ⟨1295999, by rfl⟩ : syracuseStep 1727999 = 2591999) B2591999
theorem B8316569 : Blo 766334 8316569 := bstep (se 2 (by rfl) ⟨3118713, by rfl⟩ : syracuseStep 8316569 = 6237427) B6237427
theorem B1731743 : Blo 766334 1731743 := bstep (se 1 (by rfl) ⟨1298807, by rfl⟩ : syracuseStep 1731743 = 2597615) B2597615
theorem B3894479 : Blo 766334 3894479 := bstep (se 1 (by rfl) ⟨2920859, by rfl⟩ : syracuseStep 3894479 = 5841719) B5841719
theorem B3043063 : Blo 766334 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B56881439 : Blo 766334 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B1151999 : Blo 766334 1151999 := bstep (se 1 (by rfl) ⟨863999, by rfl⟩ : syracuseStep 1151999 = 1727999) B1727999
theorem B1644779 : Blo 766334 1644779 := bstep (se 1 (by rfl) ⟨1233584, by rfl⟩ : syracuseStep 1644779 = 2467169) B2467169
theorem B5544379 : Blo 766334 5544379 := bstep (se 1 (by rfl) ⟨4158284, by rfl⟩ : syracuseStep 5544379 = 8316569) B8316569
theorem B1154495 : Blo 766334 1154495 := bstep (se 1 (by rfl) ⟨865871, by rfl⟩ : syracuseStep 1154495 = 1731743) B1731743
theorem B2596319 : Blo 766334 2596319 := bstep (se 1 (by rfl) ⟨1947239, by rfl⟩ : syracuseStep 2596319 = 3894479) B3894479
theorem B37920959 : Blo 766334 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B14033195 : Blo 766334 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B1386551 : Blo 766334 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B141732827 : Blo 766334 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B766703 : Blo 766334 766703 := bstep (se 1 (by rfl) ⟨575027, by rfl⟩ : syracuseStep 766703 = 1150055) B1150055
theorem B1169567 : Blo 766334 1169567 := bstep (se 1 (by rfl) ⟨877175, by rfl⟩ : syracuseStep 1169567 = 1754351) B1754351
theorem B66607271 : Blo 766334 66607271 := bstep (se 1 (by rfl) ⟨49955453, by rfl⟩ : syracuseStep 66607271 = 99910907) B99910907
theorem B1726955 : Blo 766334 1726955 := bstep (se 1 (by rfl) ⟨1295216, by rfl⟩ : syracuseStep 1726955 = 2590433) B2590433
theorem B4381199 : Blo 766334 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B5529215 : Blo 766334 5529215 := bstep (se 1 (by rfl) ⟨4146911, by rfl⟩ : syracuseStep 5529215 = 8293823) B8293823
theorem B4057417 : Blo 766334 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B16609535 : Blo 766334 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B2587247 : Blo 766334 2587247 := bstep (se 1 (by rfl) ⟨1940435, by rfl⟩ : syracuseStep 2587247 = 3880871) B3880871
theorem B44404847 : Blo 766334 44404847 := bstep (se 1 (by rfl) ⟨33303635, by rfl⟩ : syracuseStep 44404847 = 66607271) B66607271
theorem B1151303 : Blo 766334 1151303 := bstep (se 1 (by rfl) ⟨863477, by rfl⟩ : syracuseStep 1151303 = 1726955) B1726955
theorem B2920799 : Blo 766334 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B924367 : Blo 766334 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B21639557 : Blo 766334 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B767999 : Blo 766334 767999 := bstep (se 1 (by rfl) ⟨575999, by rfl⟩ : syracuseStep 767999 = 1151999) B1151999
theorem B1096519 : Blo 766334 1096519 := bstep (se 1 (by rfl) ⟨822389, by rfl⟩ : syracuseStep 1096519 = 1644779) B1644779
theorem B769663 : Blo 766334 769663 := bstep (se 1 (by rfl) ⟨577247, by rfl⟩ : syracuseStep 769663 = 1154495) B1154495
theorem B3686143 : Blo 766334 3686143 := bstep (se 1 (by rfl) ⟨2764607, by rfl⟩ : syracuseStep 3686143 = 5529215) B5529215
theorem B25280639 : Blo 766334 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B9355463 : Blo 766334 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B94488551 : Blo 766334 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B7392505 : Blo 766334 7392505 := bstep (se 2 (by rfl) ⟨2772189, by rfl⟩ : syracuseStep 7392505 = 5544379) B5544379
theorem B1724831 : Blo 766334 1724831 := bstep (se 1 (by rfl) ⟨1293623, by rfl⟩ : syracuseStep 1724831 = 2587247) B2587247
theorem B779711 : Blo 766334 779711 := bstep (se 1 (by rfl) ⟨584783, by rfl⟩ : syracuseStep 779711 = 1169567) B1169567
theorem B1730879 : Blo 766334 1730879 := bstep (se 1 (by rfl) ⟨1298159, by rfl⟩ : syracuseStep 1730879 = 2596319) B2596319
theorem B11073023 : Blo 766334 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B1149887 : Blo 766334 1149887 := bstep (se 1 (by rfl) ⟨862415, by rfl⟩ : syracuseStep 1149887 = 1724831) B1724831
theorem B1153919 : Blo 766334 1153919 := bstep (se 1 (by rfl) ⟨865439, by rfl⟩ : syracuseStep 1153919 = 1730879) B1730879
theorem B14426371 : Blo 766334 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B7382015 : Blo 766334 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B16853759 : Blo 766334 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B6236975 : Blo 766334 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B62992367 : Blo 766334 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B29603231 : Blo 766334 29603231 := bstep (se 1 (by rfl) ⟨22202423, by rfl⟩ : syracuseStep 29603231 = 44404847) B44404847
theorem B767535 : Blo 766334 767535 := bstep (se 1 (by rfl) ⟨575651, by rfl⟩ : syracuseStep 767535 = 1151303) B1151303
theorem B1947199 : Blo 766334 1947199 := bstep (se 1 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 1947199 = 2920799) B2920799
theorem B1232489 : Blo 766334 1232489 := bstep (se 2 (by rfl) ⟨462183, by rfl⟩ : syracuseStep 1232489 = 924367) B924367
theorem B1462025 : Blo 766334 1462025 := bstep (se 2 (by rfl) ⟨548259, by rfl⟩ : syracuseStep 1462025 = 1096519) B1096519
theorem B9856673 : Blo 766334 9856673 := bstep (se 2 (by rfl) ⟨3696252, by rfl⟩ : syracuseStep 9856673 = 7392505) B7392505
theorem B8316917 : Blo 766334 8316917 := bstep (se 5 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 8316917 = 779711) B779711
theorem B4914857 : Blo 766334 4914857 := bstep (se 2 (by rfl) ⟨1843071, by rfl⟩ : syracuseStep 4914857 = 3686143) B3686143
theorem B19235161 : Blo 766334 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B821659 : Blo 766334 821659 := bstep (se 1 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 821659 = 1232489) B1232489
theorem B4921343 : Blo 766334 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B5544611 : Blo 766334 5544611 := bstep (se 1 (by rfl) ⟨4158458, by rfl⟩ : syracuseStep 5544611 = 8316917) B8316917
theorem B2596265 : Blo 766334 2596265 := bstep (se 2 (by rfl) ⟨973599, by rfl⟩ : syracuseStep 2596265 = 1947199) B1947199
theorem B19735487 : Blo 766334 19735487 := bstep (se 1 (by rfl) ⟨14801615, by rfl⟩ : syracuseStep 19735487 = 29603231) B29603231
theorem B766591 : Blo 766334 766591 := bstep (se 1 (by rfl) ⟨574943, by rfl⟩ : syracuseStep 766591 = 1149887) B1149887
theorem B769279 : Blo 766334 769279 := bstep (se 1 (by rfl) ⟨576959, by rfl⟩ : syracuseStep 769279 = 1153919) B1153919
theorem B6571115 : Blo 766334 6571115 := bstep (se 1 (by rfl) ⟨4928336, by rfl⟩ : syracuseStep 6571115 = 9856673) B9856673
theorem B41994911 : Blo 766334 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B974683 : Blo 766334 974683 := bstep (se 1 (by rfl) ⟨731012, by rfl⟩ : syracuseStep 974683 = 1462025) B1462025
theorem B11235839 : Blo 766334 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B4157983 : Blo 766334 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B3276571 : Blo 766334 3276571 := bstep (se 1 (by rfl) ⟨2457428, by rfl⟩ : syracuseStep 3276571 = 4914857) B4914857
theorem B3280895 : Blo 766334 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B5543977 : Blo 766334 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B4368761 : Blo 766334 4368761 := bstep (se 2 (by rfl) ⟨1638285, by rfl⟩ : syracuseStep 4368761 = 3276571) B3276571
theorem B29962237 : Blo 766334 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B27996607 : Blo 766334 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B1095545 : Blo 766334 1095545 := bstep (se 2 (by rfl) ⟨410829, by rfl⟩ : syracuseStep 1095545 = 821659) B821659
theorem B13156991 : Blo 766334 13156991 := bstep (se 1 (by rfl) ⟨9867743, by rfl⟩ : syracuseStep 13156991 = 19735487) B19735487
theorem B1299577 : Blo 766334 1299577 := bstep (se 2 (by rfl) ⟨487341, by rfl⟩ : syracuseStep 1299577 = 974683) B974683
theorem B25646881 : Blo 766334 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B4380743 : Blo 766334 4380743 := bstep (se 1 (by rfl) ⟨3285557, by rfl⟩ : syracuseStep 4380743 = 6571115) B6571115
theorem B3696407 : Blo 766334 3696407 := bstep (se 1 (by rfl) ⟨2772305, by rfl⟩ : syracuseStep 3696407 = 5544611) B5544611
theorem B1730843 : Blo 766334 1730843 := bstep (se 1 (by rfl) ⟨1298132, by rfl⟩ : syracuseStep 1730843 = 2596265) B2596265
theorem B2920495 : Blo 766334 2920495 := bstep (se 1 (by rfl) ⟨2190371, by rfl⟩ : syracuseStep 2920495 = 4380743) B4380743
theorem B2921453 : Blo 766334 2921453 := bstep (se 3 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 2921453 = 1095545) B1095545
theorem B39949649 : Blo 766334 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B37328809 : Blo 766334 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B2464271 : Blo 766334 2464271 := bstep (se 1 (by rfl) ⟨1848203, by rfl⟩ : syracuseStep 2464271 = 3696407) B3696407
theorem B1153895 : Blo 766334 1153895 := bstep (se 1 (by rfl) ⟨865421, by rfl⟩ : syracuseStep 1153895 = 1730843) B1730843
theorem B34195841 : Blo 766334 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B7391969 : Blo 766334 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B8771327 : Blo 766334 8771327 := bstep (se 1 (by rfl) ⟨6578495, by rfl⟩ : syracuseStep 8771327 = 13156991) B13156991
theorem B2187263 : Blo 766334 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B1732769 : Blo 766334 1732769 := bstep (se 2 (by rfl) ⟨649788, by rfl⟩ : syracuseStep 1732769 = 1299577) B1299577
theorem B2912507 : Blo 766334 2912507 := bstep (se 1 (by rfl) ⟨2184380, by rfl⟩ : syracuseStep 2912507 = 4368761) B4368761
theorem B1642847 : Blo 766334 1642847 := bstep (se 1 (by rfl) ⟨1232135, by rfl⟩ : syracuseStep 1642847 = 2464271) B2464271
theorem B1155179 : Blo 766334 1155179 := bstep (se 1 (by rfl) ⟨866384, by rfl⟩ : syracuseStep 1155179 = 1732769) B1732769
theorem B1941671 : Blo 766334 1941671 := bstep (se 1 (by rfl) ⟨1456253, by rfl⟩ : syracuseStep 1941671 = 2912507) B2912507
theorem B4927979 : Blo 766334 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B1947635 : Blo 766334 1947635 := bstep (se 1 (by rfl) ⟨1460726, by rfl⟩ : syracuseStep 1947635 = 2921453) B2921453
theorem B5847551 : Blo 766334 5847551 := bstep (se 1 (by rfl) ⟨4385663, by rfl⟩ : syracuseStep 5847551 = 8771327) B8771327
theorem B769263 : Blo 766334 769263 := bstep (se 1 (by rfl) ⟨576947, by rfl⟩ : syracuseStep 769263 = 1153895) B1153895
theorem B1458175 : Blo 766334 1458175 := bstep (se 1 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 1458175 = 2187263) B2187263
theorem B22797227 : Blo 766334 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B26633099 : Blo 766334 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B3893993 : Blo 766334 3893993 := bstep (se 2 (by rfl) ⟨1460247, by rfl⟩ : syracuseStep 3893993 = 2920495) B2920495
theorem B49771745 : Blo 766334 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B2595995 : Blo 766334 2595995 := bstep (se 1 (by rfl) ⟨1946996, by rfl⟩ : syracuseStep 2595995 = 3893993) B3893993
theorem B3285319 : Blo 766334 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B1944233 : Blo 766334 1944233 := bstep (se 2 (by rfl) ⟨729087, by rfl⟩ : syracuseStep 1944233 = 1458175) B1458175
theorem B770119 : Blo 766334 770119 := bstep (se 1 (by rfl) ⟨577589, by rfl⟩ : syracuseStep 770119 = 1155179) B1155179
theorem B1294447 : Blo 766334 1294447 := bstep (se 1 (by rfl) ⟨970835, by rfl⟩ : syracuseStep 1294447 = 1941671) B1941671
theorem B33181163 : Blo 766334 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B1298423 : Blo 766334 1298423 := bstep (se 1 (by rfl) ⟨973817, by rfl⟩ : syracuseStep 1298423 = 1947635) B1947635
theorem B4380925 : Blo 766334 4380925 := bstep (se 3 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 4380925 = 1642847) B1642847
theorem B15198151 : Blo 766334 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B17755399 : Blo 766334 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B3898367 : Blo 766334 3898367 := bstep (se 1 (by rfl) ⟨2923775, by rfl⟩ : syracuseStep 3898367 = 5847551) B5847551
theorem B22120775 : Blo 766334 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B5841233 : Blo 766334 5841233 := bstep (se 2 (by rfl) ⟨2190462, by rfl⟩ : syracuseStep 5841233 = 4380925) B4380925
theorem B2598911 : Blo 766334 2598911 := bstep (se 1 (by rfl) ⟨1949183, by rfl⟩ : syracuseStep 2598911 = 3898367) B3898367
theorem B20264201 : Blo 766334 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B865615 : Blo 766334 865615 := bstep (se 1 (by rfl) ⟨649211, by rfl⟩ : syracuseStep 865615 = 1298423) B1298423
theorem B23673865 : Blo 766334 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B1296155 : Blo 766334 1296155 := bstep (se 1 (by rfl) ⟨972116, by rfl⟩ : syracuseStep 1296155 = 1944233) B1944233
theorem B1725929 : Blo 766334 1725929 := bstep (se 2 (by rfl) ⟨647223, by rfl⟩ : syracuseStep 1725929 = 1294447) B1294447
theorem B4380425 : Blo 766334 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B1730663 : Blo 766334 1730663 := bstep (se 1 (by rfl) ⟨1297997, by rfl⟩ : syracuseStep 1730663 = 2595995) B2595995
theorem B14747183 : Blo 766334 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B1150619 : Blo 766334 1150619 := bstep (se 1 (by rfl) ⟨862964, by rfl⟩ : syracuseStep 1150619 = 1725929) B1725929
theorem B2920283 : Blo 766334 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B1153775 : Blo 766334 1153775 := bstep (se 1 (by rfl) ⟨865331, by rfl⟩ : syracuseStep 1153775 = 1730663) B1730663
theorem B1154153 : Blo 766334 1154153 := bstep (se 2 (by rfl) ⟨432807, by rfl⟩ : syracuseStep 1154153 = 865615) B865615
theorem B13509467 : Blo 766334 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B31565153 : Blo 766334 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B864103 : Blo 766334 864103 := bstep (se 1 (by rfl) ⟨648077, by rfl⟩ : syracuseStep 864103 = 1296155) B1296155
theorem B3894155 : Blo 766334 3894155 := bstep (se 1 (by rfl) ⟨2920616, by rfl⟩ : syracuseStep 3894155 = 5841233) B5841233
theorem B1732607 : Blo 766334 1732607 := bstep (se 1 (by rfl) ⟨1299455, by rfl⟩ : syracuseStep 1732607 = 2598911) B2598911
theorem B9831455 : Blo 766334 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B1152137 : Blo 766334 1152137 := bstep (se 2 (by rfl) ⟨432051, by rfl⟩ : syracuseStep 1152137 = 864103) B864103
theorem B21043435 : Blo 766334 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B2596103 : Blo 766334 2596103 := bstep (se 1 (by rfl) ⟨1947077, by rfl⟩ : syracuseStep 2596103 = 3894155) B3894155
theorem B1155071 : Blo 766334 1155071 := bstep (se 1 (by rfl) ⟨866303, by rfl⟩ : syracuseStep 1155071 = 1732607) B1732607
theorem B767079 : Blo 766334 767079 := bstep (se 1 (by rfl) ⟨575309, by rfl⟩ : syracuseStep 767079 = 1150619) B1150619
theorem B1946855 : Blo 766334 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B769183 : Blo 766334 769183 := bstep (se 1 (by rfl) ⟨576887, by rfl⟩ : syracuseStep 769183 = 1153775) B1153775
theorem B769435 : Blo 766334 769435 := bstep (se 1 (by rfl) ⟨577076, by rfl⟩ : syracuseStep 769435 = 1154153) B1154153
theorem B9006311 : Blo 766334 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B6554303 : Blo 766334 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B6004207 : Blo 766334 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B28057913 : Blo 766334 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B768091 : Blo 766334 768091 := bstep (se 1 (by rfl) ⟨576068, by rfl⟩ : syracuseStep 768091 = 1152137) B1152137
theorem B770047 : Blo 766334 770047 := bstep (se 1 (by rfl) ⟨577535, by rfl⟩ : syracuseStep 770047 = 1155071) B1155071
theorem B1297903 : Blo 766334 1297903 := bstep (se 1 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 1297903 = 1946855) B1946855
theorem B1730735 : Blo 766334 1730735 := bstep (se 1 (by rfl) ⟨1298051, by rfl⟩ : syracuseStep 1730735 = 2596103) B2596103
theorem B1153823 : Blo 766334 1153823 := bstep (se 1 (by rfl) ⟨865367, by rfl⟩ : syracuseStep 1153823 = 1730735) B1730735
theorem B8005609 : Blo 766334 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B4369535 : Blo 766334 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B1730537 : Blo 766334 1730537 := bstep (se 2 (by rfl) ⟨648951, by rfl⟩ : syracuseStep 1730537 = 1297903) B1297903
theorem B18705275 : Blo 766334 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B1153691 : Blo 766334 1153691 := bstep (se 1 (by rfl) ⟨865268, by rfl⟩ : syracuseStep 1153691 = 1730537) B1730537
theorem B769215 : Blo 766334 769215 := bstep (se 1 (by rfl) ⟨576911, by rfl⟩ : syracuseStep 769215 = 1153823) B1153823
theorem B12470183 : Blo 766334 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B10674145 : Blo 766334 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B2913023 : Blo 766334 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B1942015 : Blo 766334 1942015 := bstep (se 1 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 1942015 = 2913023) B2913023
theorem B14232193 : Blo 766334 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B769127 : Blo 766334 769127 := bstep (se 1 (by rfl) ⟨576845, by rfl⟩ : syracuseStep 769127 = 1153691) B1153691
theorem B8313455 : Blo 766334 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B2589353 : Blo 766334 2589353 := bstep (se 2 (by rfl) ⟨971007, by rfl⟩ : syracuseStep 2589353 = 1942015) B1942015
theorem B5542303 : Blo 766334 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B75905029 : Blo 766334 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B7389737 : Blo 766334 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B101206705 : Blo 766334 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B1726235 : Blo 766334 1726235 := bstep (se 1 (by rfl) ⟨1294676, by rfl⟩ : syracuseStep 1726235 = 2589353) B2589353
theorem B134942273 : Blo 766334 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B1150823 : Blo 766334 1150823 := bstep (se 1 (by rfl) ⟨863117, by rfl⟩ : syracuseStep 1150823 = 1726235) B1726235
theorem B4926491 : Blo 766334 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B3284327 : Blo 766334 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B89961515 : Blo 766334 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B767215 : Blo 766334 767215 := bstep (se 1 (by rfl) ⟨575411, by rfl⟩ : syracuseStep 767215 = 1150823) B1150823
theorem B59974343 : Blo 766334 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B8758205 : Blo 766334 8758205 := bstep (se 3 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 8758205 = 3284327) B3284327
theorem B39982895 : Blo 766334 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B5838803 : Blo 766334 5838803 := bstep (se 1 (by rfl) ⟨4379102, by rfl⟩ : syracuseStep 5838803 = 8758205) B8758205
theorem B26655263 : Blo 766334 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B3892535 : Blo 766334 3892535 := bstep (se 1 (by rfl) ⟨2919401, by rfl⟩ : syracuseStep 3892535 = 5838803) B5838803
theorem B2595023 : Blo 766334 2595023 := bstep (se 1 (by rfl) ⟨1946267, by rfl⟩ : syracuseStep 2595023 = 3892535) B3892535
theorem B17770175 : Blo 766334 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B11846783 : Blo 766334 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B1730015 : Blo 766334 1730015 := bstep (se 1 (by rfl) ⟨1297511, by rfl⟩ : syracuseStep 1730015 = 2595023) B2595023
theorem B31591421 : Blo 766334 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B1153343 : Blo 766334 1153343 := bstep (se 1 (by rfl) ⟨865007, by rfl⟩ : syracuseStep 1153343 = 1730015) B1730015
theorem B768895 : Blo 766334 768895 := bstep (se 1 (by rfl) ⟨576671, by rfl⟩ : syracuseStep 768895 = 1153343) B1153343
theorem B21060947 : Blo 766334 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B14040631 : Blo 766334 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B18720841 : Blo 766334 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B24961121 : Blo 766334 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B16640747 : Blo 766334 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B11093831 : Blo 766334 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B7395887 : Blo 766334 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B19722365 : Blo 766334 19722365 := bstep (se 3 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 19722365 = 7395887) B7395887
theorem B13148243 : Blo 766334 13148243 := bstep (se 1 (by rfl) ⟨9861182, by rfl⟩ : syracuseStep 13148243 = 19722365) B19722365
theorem B8765495 : Blo 766334 8765495 := bstep (se 1 (by rfl) ⟨6574121, by rfl⟩ : syracuseStep 8765495 = 13148243) B13148243
theorem B5843663 : Blo 766334 5843663 := bstep (se 1 (by rfl) ⟨4382747, by rfl⟩ : syracuseStep 5843663 = 8765495) B8765495
theorem B3895775 : Blo 766334 3895775 := bstep (se 1 (by rfl) ⟨2921831, by rfl⟩ : syracuseStep 3895775 = 5843663) B5843663
theorem B2597183 : Blo 766334 2597183 := bstep (se 1 (by rfl) ⟨1947887, by rfl⟩ : syracuseStep 2597183 = 3895775) B3895775
theorem B1731455 : Blo 766334 1731455 := bstep (se 1 (by rfl) ⟨1298591, by rfl⟩ : syracuseStep 1731455 = 2597183) B2597183
theorem B1154303 : Blo 766334 1154303 := bstep (se 1 (by rfl) ⟨865727, by rfl⟩ : syracuseStep 1154303 = 1731455) B1731455
theorem B769535 : Blo 766334 769535 := bstep (se 1 (by rfl) ⟨577151, by rfl⟩ : syracuseStep 769535 = 1154303) B1154303

theorem C0 (j : ℕ) (h1 : 191583 ≤ j) (h2 : j ≤ 192282) : Blo 766334 (4 * j + 3) := by
  interval_cases j
  · exact B766335
  · exact B766339
  · exact B766343
  · exact B766347
  · exact B766351
  · exact B766355
  · exact B766359
  · exact B766363
  · exact B766367
  · exact B766371
  · exact B766375
  · exact B766379
  · exact B766383
  · exact B766387
  · exact B766391
  · exact B766395
  · exact B766399
  · exact B766403
  · exact B766407
  · exact B766411
  · exact B766415
  · exact B766419
  · exact B766423
  · exact B766427
  · exact B766431
  · exact B766435
  · exact B766439
  · exact B766443
  · exact B766447
  · exact B766451
  · exact B766455
  · exact B766459
  · exact B766463
  · exact B766467
  · exact B766471
  · exact B766475
  · exact B766479
  · exact B766483
  · exact B766487
  · exact B766491
  · exact B766495
  · exact B766499
  · exact B766503
  · exact B766507
  · exact B766511
  · exact B766515
  · exact B766519
  · exact B766523
  · exact B766527
  · exact B766531
  · exact B766535
  · exact B766539
  · exact B766543
  · exact B766547
  · exact B766551
  · exact B766555
  · exact B766559
  · exact B766563
  · exact B766567
  · exact B766571
  · exact B766575
  · exact B766579
  · exact B766583
  · exact B766587
  · exact B766591
  · exact B766595
  · exact B766599
  · exact B766603
  · exact B766607
  · exact B766611
  · exact B766615
  · exact B766619
  · exact B766623
  · exact B766627
  · exact B766631
  · exact B766635
  · exact B766639
  · exact B766643
  · exact B766647
  · exact B766651
  · exact B766655
  · exact B766659
  · exact B766663
  · exact B766667
  · exact B766671
  · exact B766675
  · exact B766679
  · exact B766683
  · exact B766687
  · exact B766691
  · exact B766695
  · exact B766699
  · exact B766703
  · exact B766707
  · exact B766711
  · exact B766715
  · exact B766719
  · exact B766723
  · exact B766727
  · exact B766731
  · exact B766735
  · exact B766739
  · exact B766743
  · exact B766747
  · exact B766751
  · exact B766755
  · exact B766759
  · exact B766763
  · exact B766767
  · exact B766771
  · exact B766775
  · exact B766779
  · exact B766783
  · exact B766787
  · exact B766791
  · exact B766795
  · exact B766799
  · exact B766803
  · exact B766807
  · exact B766811
  · exact B766815
  · exact B766819
  · exact B766823
  · exact B766827
  · exact B766831
  · exact B766835
  · exact B766839
  · exact B766843
  · exact B766847
  · exact B766851
  · exact B766855
  · exact B766859
  · exact B766863
  · exact B766867
  · exact B766871
  · exact B766875
  · exact B766879
  · exact B766883
  · exact B766887
  · exact B766891
  · exact B766895
  · exact B766899
  · exact B766903
  · exact B766907
  · exact B766911
  · exact B766915
  · exact B766919
  · exact B766923
  · exact B766927
  · exact B766931
  · exact B766935
  · exact B766939
  · exact B766943
  · exact B766947
  · exact B766951
  · exact B766955
  · exact B766959
  · exact B766963
  · exact B766967
  · exact B766971
  · exact B766975
  · exact B766979
  · exact B766983
  · exact B766987
  · exact B766991
  · exact B766995
  · exact B766999
  · exact B767003
  · exact B767007
  · exact B767011
  · exact B767015
  · exact B767019
  · exact B767023
  · exact B767027
  · exact B767031
  · exact B767035
  · exact B767039
  · exact B767043
  · exact B767047
  · exact B767051
  · exact B767055
  · exact B767059
  · exact B767063
  · exact B767067
  · exact B767071
  · exact B767075
  · exact B767079
  · exact B767083
  · exact B767087
  · exact B767091
  · exact B767095
  · exact B767099
  · exact B767103
  · exact B767107
  · exact B767111
  · exact B767115
  · exact B767119
  · exact B767123
  · exact B767127
  · exact B767131
  · exact B767135
  · exact B767139
  · exact B767143
  · exact B767147
  · exact B767151
  · exact B767155
  · exact B767159
  · exact B767163
  · exact B767167
  · exact B767171
  · exact B767175
  · exact B767179
  · exact B767183
  · exact B767187
  · exact B767191
  · exact B767195
  · exact B767199
  · exact B767203
  · exact B767207
  · exact B767211
  · exact B767215
  · exact B767219
  · exact B767223
  · exact B767227
  · exact B767231
  · exact B767235
  · exact B767239
  · exact B767243
  · exact B767247
  · exact B767251
  · exact B767255
  · exact B767259
  · exact B767263
  · exact B767267
  · exact B767271
  · exact B767275
  · exact B767279
  · exact B767283
  · exact B767287
  · exact B767291
  · exact B767295
  · exact B767299
  · exact B767303
  · exact B767307
  · exact B767311
  · exact B767315
  · exact B767319
  · exact B767323
  · exact B767327
  · exact B767331
  · exact B767335
  · exact B767339
  · exact B767343
  · exact B767347
  · exact B767351
  · exact B767355
  · exact B767359
  · exact B767363
  · exact B767367
  · exact B767371
  · exact B767375
  · exact B767379
  · exact B767383
  · exact B767387
  · exact B767391
  · exact B767395
  · exact B767399
  · exact B767403
  · exact B767407
  · exact B767411
  · exact B767415
  · exact B767419
  · exact B767423
  · exact B767427
  · exact B767431
  · exact B767435
  · exact B767439
  · exact B767443
  · exact B767447
  · exact B767451
  · exact B767455
  · exact B767459
  · exact B767463
  · exact B767467
  · exact B767471
  · exact B767475
  · exact B767479
  · exact B767483
  · exact B767487
  · exact B767491
  · exact B767495
  · exact B767499
  · exact B767503
  · exact B767507
  · exact B767511
  · exact B767515
  · exact B767519
  · exact B767523
  · exact B767527
  · exact B767531
  · exact B767535
  · exact B767539
  · exact B767543
  · exact B767547
  · exact B767551
  · exact B767555
  · exact B767559
  · exact B767563
  · exact B767567
  · exact B767571
  · exact B767575
  · exact B767579
  · exact B767583
  · exact B767587
  · exact B767591
  · exact B767595
  · exact B767599
  · exact B767603
  · exact B767607
  · exact B767611
  · exact B767615
  · exact B767619
  · exact B767623
  · exact B767627
  · exact B767631
  · exact B767635
  · exact B767639
  · exact B767643
  · exact B767647
  · exact B767651
  · exact B767655
  · exact B767659
  · exact B767663
  · exact B767667
  · exact B767671
  · exact B767675
  · exact B767679
  · exact B767683
  · exact B767687
  · exact B767691
  · exact B767695
  · exact B767699
  · exact B767703
  · exact B767707
  · exact B767711
  · exact B767715
  · exact B767719
  · exact B767723
  · exact B767727
  · exact B767731
  · exact B767735
  · exact B767739
  · exact B767743
  · exact B767747
  · exact B767751
  · exact B767755
  · exact B767759
  · exact B767763
  · exact B767767
  · exact B767771
  · exact B767775
  · exact B767779
  · exact B767783
  · exact B767787
  · exact B767791
  · exact B767795
  · exact B767799
  · exact B767803
  · exact B767807
  · exact B767811
  · exact B767815
  · exact B767819
  · exact B767823
  · exact B767827
  · exact B767831
  · exact B767835
  · exact B767839
  · exact B767843
  · exact B767847
  · exact B767851
  · exact B767855
  · exact B767859
  · exact B767863
  · exact B767867
  · exact B767871
  · exact B767875
  · exact B767879
  · exact B767883
  · exact B767887
  · exact B767891
  · exact B767895
  · exact B767899
  · exact B767903
  · exact B767907
  · exact B767911
  · exact B767915
  · exact B767919
  · exact B767923
  · exact B767927
  · exact B767931
  · exact B767935
  · exact B767939
  · exact B767943
  · exact B767947
  · exact B767951
  · exact B767955
  · exact B767959
  · exact B767963
  · exact B767967
  · exact B767971
  · exact B767975
  · exact B767979
  · exact B767983
  · exact B767987
  · exact B767991
  · exact B767995
  · exact B767999
  · exact B768003
  · exact B768007
  · exact B768011
  · exact B768015
  · exact B768019
  · exact B768023
  · exact B768027
  · exact B768031
  · exact B768035
  · exact B768039
  · exact B768043
  · exact B768047
  · exact B768051
  · exact B768055
  · exact B768059
  · exact B768063
  · exact B768067
  · exact B768071
  · exact B768075
  · exact B768079
  · exact B768083
  · exact B768087
  · exact B768091
  · exact B768095
  · exact B768099
  · exact B768103
  · exact B768107
  · exact B768111
  · exact B768115
  · exact B768119
  · exact B768123
  · exact B768127
  · exact B768131
  · exact B768135
  · exact B768139
  · exact B768143
  · exact B768147
  · exact B768151
  · exact B768155
  · exact B768159
  · exact B768163
  · exact B768167
  · exact B768171
  · exact B768175
  · exact B768179
  · exact B768183
  · exact B768187
  · exact B768191
  · exact B768195
  · exact B768199
  · exact B768203
  · exact B768207
  · exact B768211
  · exact B768215
  · exact B768219
  · exact B768223
  · exact B768227
  · exact B768231
  · exact B768235
  · exact B768239
  · exact B768243
  · exact B768247
  · exact B768251
  · exact B768255
  · exact B768259
  · exact B768263
  · exact B768267
  · exact B768271
  · exact B768275
  · exact B768279
  · exact B768283
  · exact B768287
  · exact B768291
  · exact B768295
  · exact B768299
  · exact B768303
  · exact B768307
  · exact B768311
  · exact B768315
  · exact B768319
  · exact B768323
  · exact B768327
  · exact B768331
  · exact B768335
  · exact B768339
  · exact B768343
  · exact B768347
  · exact B768351
  · exact B768355
  · exact B768359
  · exact B768363
  · exact B768367
  · exact B768371
  · exact B768375
  · exact B768379
  · exact B768383
  · exact B768387
  · exact B768391
  · exact B768395
  · exact B768399
  · exact B768403
  · exact B768407
  · exact B768411
  · exact B768415
  · exact B768419
  · exact B768423
  · exact B768427
  · exact B768431
  · exact B768435
  · exact B768439
  · exact B768443
  · exact B768447
  · exact B768451
  · exact B768455
  · exact B768459
  · exact B768463
  · exact B768467
  · exact B768471
  · exact B768475
  · exact B768479
  · exact B768483
  · exact B768487
  · exact B768491
  · exact B768495
  · exact B768499
  · exact B768503
  · exact B768507
  · exact B768511
  · exact B768515
  · exact B768519
  · exact B768523
  · exact B768527
  · exact B768531
  · exact B768535
  · exact B768539
  · exact B768543
  · exact B768547
  · exact B768551
  · exact B768555
  · exact B768559
  · exact B768563
  · exact B768567
  · exact B768571
  · exact B768575
  · exact B768579
  · exact B768583
  · exact B768587
  · exact B768591
  · exact B768595
  · exact B768599
  · exact B768603
  · exact B768607
  · exact B768611
  · exact B768615
  · exact B768619
  · exact B768623
  · exact B768627
  · exact B768631
  · exact B768635
  · exact B768639
  · exact B768643
  · exact B768647
  · exact B768651
  · exact B768655
  · exact B768659
  · exact B768663
  · exact B768667
  · exact B768671
  · exact B768675
  · exact B768679
  · exact B768683
  · exact B768687
  · exact B768691
  · exact B768695
  · exact B768699
  · exact B768703
  · exact B768707
  · exact B768711
  · exact B768715
  · exact B768719
  · exact B768723
  · exact B768727
  · exact B768731
  · exact B768735
  · exact B768739
  · exact B768743
  · exact B768747
  · exact B768751
  · exact B768755
  · exact B768759
  · exact B768763
  · exact B768767
  · exact B768771
  · exact B768775
  · exact B768779
  · exact B768783
  · exact B768787
  · exact B768791
  · exact B768795
  · exact B768799
  · exact B768803
  · exact B768807
  · exact B768811
  · exact B768815
  · exact B768819
  · exact B768823
  · exact B768827
  · exact B768831
  · exact B768835
  · exact B768839
  · exact B768843
  · exact B768847
  · exact B768851
  · exact B768855
  · exact B768859
  · exact B768863
  · exact B768867
  · exact B768871
  · exact B768875
  · exact B768879
  · exact B768883
  · exact B768887
  · exact B768891
  · exact B768895
  · exact B768899
  · exact B768903
  · exact B768907
  · exact B768911
  · exact B768915
  · exact B768919
  · exact B768923
  · exact B768927
  · exact B768931
  · exact B768935
  · exact B768939
  · exact B768943
  · exact B768947
  · exact B768951
  · exact B768955
  · exact B768959
  · exact B768963
  · exact B768967
  · exact B768971
  · exact B768975
  · exact B768979
  · exact B768983
  · exact B768987
  · exact B768991
  · exact B768995
  · exact B768999
  · exact B769003
  · exact B769007
  · exact B769011
  · exact B769015
  · exact B769019
  · exact B769023
  · exact B769027
  · exact B769031
  · exact B769035
  · exact B769039
  · exact B769043
  · exact B769047
  · exact B769051
  · exact B769055
  · exact B769059
  · exact B769063
  · exact B769067
  · exact B769071
  · exact B769075
  · exact B769079
  · exact B769083
  · exact B769087
  · exact B769091
  · exact B769095
  · exact B769099
  · exact B769103
  · exact B769107
  · exact B769111
  · exact B769115
  · exact B769119
  · exact B769123
  · exact B769127
  · exact B769131

theorem C1 (j : ℕ) (h1 : 192283 ≤ j) (h2 : j ≤ 192582) : Blo 766334 (4 * j + 3) := by
  interval_cases j
  · exact B769135
  · exact B769139
  · exact B769143
  · exact B769147
  · exact B769151
  · exact B769155
  · exact B769159
  · exact B769163
  · exact B769167
  · exact B769171
  · exact B769175
  · exact B769179
  · exact B769183
  · exact B769187
  · exact B769191
  · exact B769195
  · exact B769199
  · exact B769203
  · exact B769207
  · exact B769211
  · exact B769215
  · exact B769219
  · exact B769223
  · exact B769227
  · exact B769231
  · exact B769235
  · exact B769239
  · exact B769243
  · exact B769247
  · exact B769251
  · exact B769255
  · exact B769259
  · exact B769263
  · exact B769267
  · exact B769271
  · exact B769275
  · exact B769279
  · exact B769283
  · exact B769287
  · exact B769291
  · exact B769295
  · exact B769299
  · exact B769303
  · exact B769307
  · exact B769311
  · exact B769315
  · exact B769319
  · exact B769323
  · exact B769327
  · exact B769331
  · exact B769335
  · exact B769339
  · exact B769343
  · exact B769347
  · exact B769351
  · exact B769355
  · exact B769359
  · exact B769363
  · exact B769367
  · exact B769371
  · exact B769375
  · exact B769379
  · exact B769383
  · exact B769387
  · exact B769391
  · exact B769395
  · exact B769399
  · exact B769403
  · exact B769407
  · exact B769411
  · exact B769415
  · exact B769419
  · exact B769423
  · exact B769427
  · exact B769431
  · exact B769435
  · exact B769439
  · exact B769443
  · exact B769447
  · exact B769451
  · exact B769455
  · exact B769459
  · exact B769463
  · exact B769467
  · exact B769471
  · exact B769475
  · exact B769479
  · exact B769483
  · exact B769487
  · exact B769491
  · exact B769495
  · exact B769499
  · exact B769503
  · exact B769507
  · exact B769511
  · exact B769515
  · exact B769519
  · exact B769523
  · exact B769527
  · exact B769531
  · exact B769535
  · exact B769539
  · exact B769543
  · exact B769547
  · exact B769551
  · exact B769555
  · exact B769559
  · exact B769563
  · exact B769567
  · exact B769571
  · exact B769575
  · exact B769579
  · exact B769583
  · exact B769587
  · exact B769591
  · exact B769595
  · exact B769599
  · exact B769603
  · exact B769607
  · exact B769611
  · exact B769615
  · exact B769619
  · exact B769623
  · exact B769627
  · exact B769631
  · exact B769635
  · exact B769639
  · exact B769643
  · exact B769647
  · exact B769651
  · exact B769655
  · exact B769659
  · exact B769663
  · exact B769667
  · exact B769671
  · exact B769675
  · exact B769679
  · exact B769683
  · exact B769687
  · exact B769691
  · exact B769695
  · exact B769699
  · exact B769703
  · exact B769707
  · exact B769711
  · exact B769715
  · exact B769719
  · exact B769723
  · exact B769727
  · exact B769731
  · exact B769735
  · exact B769739
  · exact B769743
  · exact B769747
  · exact B769751
  · exact B769755
  · exact B769759
  · exact B769763
  · exact B769767
  · exact B769771
  · exact B769775
  · exact B769779
  · exact B769783
  · exact B769787
  · exact B769791
  · exact B769795
  · exact B769799
  · exact B769803
  · exact B769807
  · exact B769811
  · exact B769815
  · exact B769819
  · exact B769823
  · exact B769827
  · exact B769831
  · exact B769835
  · exact B769839
  · exact B769843
  · exact B769847
  · exact B769851
  · exact B769855
  · exact B769859
  · exact B769863
  · exact B769867
  · exact B769871
  · exact B769875
  · exact B769879
  · exact B769883
  · exact B769887
  · exact B769891
  · exact B769895
  · exact B769899
  · exact B769903
  · exact B769907
  · exact B769911
  · exact B769915
  · exact B769919
  · exact B769923
  · exact B769927
  · exact B769931
  · exact B769935
  · exact B769939
  · exact B769943
  · exact B769947
  · exact B769951
  · exact B769955
  · exact B769959
  · exact B769963
  · exact B769967
  · exact B769971
  · exact B769975
  · exact B769979
  · exact B769983
  · exact B769987
  · exact B769991
  · exact B769995
  · exact B769999
  · exact B770003
  · exact B770007
  · exact B770011
  · exact B770015
  · exact B770019
  · exact B770023
  · exact B770027
  · exact B770031
  · exact B770035
  · exact B770039
  · exact B770043
  · exact B770047
  · exact B770051
  · exact B770055
  · exact B770059
  · exact B770063
  · exact B770067
  · exact B770071
  · exact B770075
  · exact B770079
  · exact B770083
  · exact B770087
  · exact B770091
  · exact B770095
  · exact B770099
  · exact B770103
  · exact B770107
  · exact B770111
  · exact B770115
  · exact B770119
  · exact B770123
  · exact B770127
  · exact B770131
  · exact B770135
  · exact B770139
  · exact B770143
  · exact B770147
  · exact B770151
  · exact B770155
  · exact B770159
  · exact B770163
  · exact B770167
  · exact B770171
  · exact B770175
  · exact B770179
  · exact B770183
  · exact B770187
  · exact B770191
  · exact B770195
  · exact B770199
  · exact B770203
  · exact B770207
  · exact B770211
  · exact B770215
  · exact B770219
  · exact B770223
  · exact B770227
  · exact B770231
  · exact B770235
  · exact B770239
  · exact B770243
  · exact B770247
  · exact B770251
  · exact B770255
  · exact B770259
  · exact B770263
  · exact B770267
  · exact B770271
  · exact B770275
  · exact B770279
  · exact B770283
  · exact B770287
  · exact B770291
  · exact B770295
  · exact B770299
  · exact B770303
  · exact B770307
  · exact B770311
  · exact B770315
  · exact B770319
  · exact B770323
  · exact B770327
  · exact B770331

theorem solution (m : ℕ) (hlo : 766334 ≤ m) (hhi : m ≤ 770334) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 191583 ≤ j := by omega
    have hj2 : j ≤ 192582 := by omega
    have hb : Blo 766334 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 192283 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
