-- Prove2me | solution 1 for syracuse_descends_range_251819_255819
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:03.564021+00:00
-- url     : https://prove2.me/submissions/4c76fa0e-55ee-4d13-b813-f26f5dd5c89d

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


theorem B426053 : Blo 251819 426053 := bbase (se 4 (by rfl) ⟨39942, by rfl⟩ : syracuseStep 426053 = 79885) (by norm_num)
theorem B917669 : Blo 251819 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B426181 : Blo 251819 426181 := bbase (se 4 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 426181 = 79909) (by norm_num)
theorem B524485 : Blo 251819 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B426269 : Blo 251819 426269 := bbase (se 3 (by rfl) ⟨79925, by rfl⟩ : syracuseStep 426269 = 159851) (by norm_num)
theorem B360821 : Blo 251819 360821 := bbase (se 5 (by rfl) ⟨16913, by rfl⟩ : syracuseStep 360821 = 33827) (by norm_num)
theorem B1278341 : Blo 251819 1278341 := bbase (se 4 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 1278341 = 239689) (by norm_num)
theorem B426397 : Blo 251819 426397 := bbase (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) (by norm_num)
theorem B852389 : Blo 251819 852389 := bbase (se 4 (by rfl) ⟨79911, by rfl⟩ : syracuseStep 852389 = 159823) (by norm_num)
theorem B1081781 : Blo 251819 1081781 := bbase (se 5 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 1081781 = 101417) (by norm_num)
theorem B459245 : Blo 251819 459245 := bbase (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) (by norm_num)
theorem B426485 : Blo 251819 426485 := bbase (se 5 (by rfl) ⟨19991, by rfl⟩ : syracuseStep 426485 = 39983) (by norm_num)
theorem B426613 : Blo 251819 426613 := bbase (se 5 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 426613 = 39995) (by norm_num)
theorem B426701 : Blo 251819 426701 := bbase (se 3 (by rfl) ⟨80006, by rfl⟩ : syracuseStep 426701 = 160013) (by norm_num)
theorem B3637973 : Blo 251819 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B426829 : Blo 251819 426829 := bbase (se 3 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 426829 = 160061) (by norm_num)
theorem B852821 : Blo 251819 852821 := bbase (se 9 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 852821 = 4997) (by norm_num)
theorem B983909 : Blo 251819 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B2196341 : Blo 251819 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B426917 : Blo 251819 426917 := bbase (se 4 (by rfl) ⟨40023, by rfl⟩ : syracuseStep 426917 = 80047) (by norm_num)
theorem B427045 : Blo 251819 427045 := bbase (se 4 (by rfl) ⟨40035, by rfl⟩ : syracuseStep 427045 = 80071) (by norm_num)
theorem B721973 : Blo 251819 721973 := bbase (se 5 (by rfl) ⟨33842, by rfl⟩ : syracuseStep 721973 = 67685) (by norm_num)
theorem B427133 : Blo 251819 427133 := bbase (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) (by norm_num)
theorem B3671189 : Blo 251819 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B427261 : Blo 251819 427261 := bbase (se 3 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 427261 = 160223) (by norm_num)
theorem B853253 : Blo 251819 853253 := bbase (se 4 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 853253 = 159985) (by norm_num)
theorem B1213717 : Blo 251819 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B427349 : Blo 251819 427349 := bbase (se 12 (by rfl) ⟨156, by rfl⟩ : syracuseStep 427349 = 313) (by norm_num)
theorem B427477 : Blo 251819 427477 := bbase (se 7 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 427477 = 10019) (by norm_num)
theorem B460325 : Blo 251819 460325 := bbase (se 4 (by rfl) ⟨43155, by rfl⟩ : syracuseStep 460325 = 86311) (by norm_num)
theorem B427565 : Blo 251819 427565 := bbase (se 3 (by rfl) ⟨80168, by rfl⟩ : syracuseStep 427565 = 160337) (by norm_num)
theorem B1279637 : Blo 251819 1279637 := bbase (se 6 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 1279637 = 59983) (by norm_num)
theorem B427693 : Blo 251819 427693 := bbase (se 3 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 427693 = 160385) (by norm_num)
theorem B853685 : Blo 251819 853685 := bbase (se 5 (by rfl) ⟨40016, by rfl⟩ : syracuseStep 853685 = 80033) (by norm_num)
theorem B722645 : Blo 251819 722645 := bbase (se 7 (by rfl) ⟨8468, by rfl⟩ : syracuseStep 722645 = 16937) (by norm_num)
theorem B427781 : Blo 251819 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B362245 : Blo 251819 362245 := bbase (se 4 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 362245 = 67921) (by norm_num)
theorem B427909 : Blo 251819 427909 := bbase (se 4 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 427909 = 80233) (by norm_num)
theorem B460733 : Blo 251819 460733 := bbase (se 3 (by rfl) ⟨86387, by rfl⟩ : syracuseStep 460733 = 172775) (by norm_num)
theorem B427997 : Blo 251819 427997 := bbase (se 3 (by rfl) ⟨80249, by rfl⟩ : syracuseStep 427997 = 160499) (by norm_num)
theorem B264173 : Blo 251819 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B428125 : Blo 251819 428125 := bbase (se 3 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 428125 = 160547) (by norm_num)
theorem B854117 : Blo 251819 854117 := bbase (se 4 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 854117 = 160147) (by norm_num)
theorem B723077 : Blo 251819 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B1083557 : Blo 251819 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B428213 : Blo 251819 428213 := bbase (se 5 (by rfl) ⟨20072, by rfl⟩ : syracuseStep 428213 = 40145) (by norm_num)
theorem B461069 : Blo 251819 461069 := bbase (se 3 (by rfl) ⟨86450, by rfl⟩ : syracuseStep 461069 = 172901) (by norm_num)
theorem B428341 : Blo 251819 428341 := bbase (se 5 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 428341 = 40157) (by norm_num)
theorem B1968437 : Blo 251819 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B362837 : Blo 251819 362837 := bbase (se 10 (by rfl) ⟨531, by rfl⟩ : syracuseStep 362837 = 1063) (by norm_num)
theorem B428429 : Blo 251819 428429 := bbase (se 3 (by rfl) ⟨80330, by rfl⟩ : syracuseStep 428429 = 160661) (by norm_num)
theorem B362917 : Blo 251819 362917 := bbase (se 4 (by rfl) ⟨34023, by rfl⟩ : syracuseStep 362917 = 68047) (by norm_num)
theorem B428557 : Blo 251819 428557 := bbase (se 3 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 428557 = 160709) (by norm_num)
theorem B854549 : Blo 251819 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B363037 : Blo 251819 363037 := bbase (se 3 (by rfl) ⟨68069, by rfl⟩ : syracuseStep 363037 = 136139) (by norm_num)
theorem B428645 : Blo 251819 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B363133 : Blo 251819 363133 := bbase (se 3 (by rfl) ⟨68087, by rfl⟩ : syracuseStep 363133 = 136175) (by norm_num)
theorem B428773 : Blo 251819 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B428861 : Blo 251819 428861 := bbase (se 3 (by rfl) ⟨80411, by rfl⟩ : syracuseStep 428861 = 160823) (by norm_num)
theorem B723829 : Blo 251819 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B1280933 : Blo 251819 1280933 := bbase (se 4 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 1280933 = 240175) (by norm_num)
theorem B428989 : Blo 251819 428989 := bbase (se 3 (by rfl) ⟨80435, by rfl⟩ : syracuseStep 428989 = 160871) (by norm_num)
theorem B854981 : Blo 251819 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B429077 : Blo 251819 429077 := bbase (se 6 (by rfl) ⟨10056, by rfl⟩ : syracuseStep 429077 = 20113) (by norm_num)
theorem B363629 : Blo 251819 363629 := bbase (se 3 (by rfl) ⟨68180, by rfl⟩ : syracuseStep 363629 = 136361) (by norm_num)
theorem B429205 : Blo 251819 429205 := bbase (se 6 (by rfl) ⟨10059, by rfl⟩ : syracuseStep 429205 = 20119) (by norm_num)
theorem B429293 : Blo 251819 429293 := bbase (se 3 (by rfl) ⟨80492, by rfl⟩ : syracuseStep 429293 = 160985) (by norm_num)
theorem B429421 : Blo 251819 429421 := bbase (se 3 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 429421 = 161033) (by norm_num)
theorem B855413 : Blo 251819 855413 := bbase (se 5 (by rfl) ⟨40097, by rfl⟩ : syracuseStep 855413 = 80195) (by norm_num)
theorem B429509 : Blo 251819 429509 := bbase (se 4 (by rfl) ⟨40266, by rfl⟩ : syracuseStep 429509 = 80533) (by norm_num)
theorem B1248821 : Blo 251819 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B429637 : Blo 251819 429637 := bbase (se 4 (by rfl) ⟨40278, by rfl⟩ : syracuseStep 429637 = 80557) (by norm_num)
theorem B364181 : Blo 251819 364181 := bbase (se 6 (by rfl) ⟨8535, by rfl⟩ : syracuseStep 364181 = 17071) (by norm_num)
theorem B429725 : Blo 251819 429725 := bbase (se 3 (by rfl) ⟨80573, by rfl⟩ : syracuseStep 429725 = 161147) (by norm_num)
theorem B429853 : Blo 251819 429853 := bbase (se 3 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 429853 = 161195) (by norm_num)
theorem B855845 : Blo 251819 855845 := bbase (se 4 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 855845 = 160471) (by norm_num)
theorem B429941 : Blo 251819 429941 := bbase (se 5 (by rfl) ⟨20153, by rfl⟩ : syracuseStep 429941 = 40307) (by norm_num)
theorem B397181 : Blo 251819 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B2625493 : Blo 251819 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B430069 : Blo 251819 430069 := bbase (se 5 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 430069 = 40319) (by norm_num)
theorem B430157 : Blo 251819 430157 := bbase (se 3 (by rfl) ⟨80654, by rfl⟩ : syracuseStep 430157 = 161309) (by norm_num)
theorem B1282229 : Blo 251819 1282229 := bbase (se 5 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 1282229 = 120209) (by norm_num)
theorem B430285 : Blo 251819 430285 := bbase (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) (by norm_num)
theorem B856277 : Blo 251819 856277 := bbase (se 7 (by rfl) ⟨10034, by rfl⟩ : syracuseStep 856277 = 20069) (by norm_num)
theorem B430373 : Blo 251819 430373 := bbase (se 4 (by rfl) ⟨40347, by rfl⟩ : syracuseStep 430373 = 80695) (by norm_num)
theorem B430501 : Blo 251819 430501 := bbase (se 4 (by rfl) ⟨40359, by rfl⟩ : syracuseStep 430501 = 80719) (by norm_num)
theorem B430589 : Blo 251819 430589 := bbase (se 3 (by rfl) ⟨80735, by rfl⟩ : syracuseStep 430589 = 161471) (by norm_num)
theorem B430717 : Blo 251819 430717 := bbase (se 3 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 430717 = 161519) (by norm_num)
theorem B856709 : Blo 251819 856709 := bbase (se 4 (by rfl) ⟨80316, by rfl⟩ : syracuseStep 856709 = 160633) (by norm_num)
theorem B2429621 : Blo 251819 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B430805 : Blo 251819 430805 := bbase (se 7 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 430805 = 10097) (by norm_num)
theorem B430933 : Blo 251819 430933 := bbase (se 9 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 430933 = 2525) (by norm_num)
theorem B431021 : Blo 251819 431021 := bbase (se 3 (by rfl) ⟨80816, by rfl⟩ : syracuseStep 431021 = 161633) (by norm_num)
theorem B431149 : Blo 251819 431149 := bbase (se 3 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 431149 = 161681) (by norm_num)
theorem B857141 : Blo 251819 857141 := bbase (se 5 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 857141 = 80357) (by norm_num)
theorem B431237 : Blo 251819 431237 := bbase (se 4 (by rfl) ⟨40428, by rfl⟩ : syracuseStep 431237 = 80857) (by norm_num)
theorem B431365 : Blo 251819 431365 := bbase (se 4 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 431365 = 80881) (by norm_num)
theorem B431453 : Blo 251819 431453 := bbase (se 3 (by rfl) ⟨80897, by rfl⟩ : syracuseStep 431453 = 161795) (by norm_num)
theorem B1283525 : Blo 251819 1283525 := bbase (se 4 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 1283525 = 240661) (by norm_num)
theorem B431581 : Blo 251819 431581 := bbase (se 3 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 431581 = 161843) (by norm_num)
theorem B857573 : Blo 251819 857573 := bbase (se 4 (by rfl) ⟨80397, by rfl⟩ : syracuseStep 857573 = 160795) (by norm_num)
theorem B431669 : Blo 251819 431669 := bbase (se 5 (by rfl) ⟨20234, by rfl⟩ : syracuseStep 431669 = 40469) (by norm_num)
theorem B726677 : Blo 251819 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B858005 : Blo 251819 858005 := bbase (se 6 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 858005 = 40219) (by norm_num)
theorem B956357 : Blo 251819 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B858437 : Blo 251819 858437 := bbase (se 4 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 858437 = 160957) (by norm_num)
theorem B1087829 : Blo 251819 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B1284821 : Blo 251819 1284821 := bbase (se 7 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 1284821 = 30113) (by norm_num)
theorem B531173 : Blo 251819 531173 := bbase (se 4 (by rfl) ⟨49797, by rfl⟩ : syracuseStep 531173 = 99595) (by norm_num)
theorem B858869 : Blo 251819 858869 := bbase (se 5 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 858869 = 80519) (by norm_num)
theorem B727861 : Blo 251819 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B662437 : Blo 251819 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B269249 : Blo 251819 269249 := bbase (se 2 (by rfl) ⟨100968, by rfl⟩ : syracuseStep 269249 = 201937) (by norm_num)
theorem B728021 : Blo 251819 728021 := bbase (se 7 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 728021 = 17063) (by norm_num)
theorem B367669 : Blo 251819 367669 := bbase (se 5 (by rfl) ⟨17234, by rfl⟩ : syracuseStep 367669 = 34469) (by norm_num)
theorem B957541 : Blo 251819 957541 := bbase (se 4 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 957541 = 179539) (by norm_num)
theorem B1940597 : Blo 251819 1940597 := bbase (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) (by norm_num)
theorem B859301 : Blo 251819 859301 := bbase (se 4 (by rfl) ⟨80559, by rfl⟩ : syracuseStep 859301 = 161119) (by norm_num)
theorem B269497 : Blo 251819 269497 := bbase (se 2 (by rfl) ⟨101061, by rfl⟩ : syracuseStep 269497 = 202123) (by norm_num)
theorem B728261 : Blo 251819 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B1187093 : Blo 251819 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B728453 : Blo 251819 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B957845 : Blo 251819 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B1121861 : Blo 251819 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B302665 : Blo 251819 302665 := bbase (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) (by norm_num)
theorem B859733 : Blo 251819 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B269941 : Blo 251819 269941 := bbase (se 5 (by rfl) ⟨12653, by rfl⟩ : syracuseStep 269941 = 25307) (by norm_num)
theorem B1023637 : Blo 251819 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B302761 : Blo 251819 302761 := bbase (se 2 (by rfl) ⟨113535, by rfl⟩ : syracuseStep 302761 = 227071) (by norm_num)
theorem B270001 : Blo 251819 270001 := bbase (se 2 (by rfl) ⟨101250, by rfl⟩ : syracuseStep 270001 = 202501) (by norm_num)
theorem B1449845 : Blo 251819 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B1220501 : Blo 251819 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B1286117 : Blo 251819 1286117 := bbase (se 4 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 1286117 = 241147) (by norm_num)
theorem B270317 : Blo 251819 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B860165 : Blo 251819 860165 := bbase (se 4 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 860165 = 161281) (by norm_num)
theorem B1089605 : Blo 251819 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B4923605 : Blo 251819 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B1646837 : Blo 251819 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B1089845 : Blo 251819 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B270761 : Blo 251819 270761 := bbase (se 2 (by rfl) ⟨101535, by rfl⟩ : syracuseStep 270761 = 203071) (by norm_num)
theorem B860597 : Blo 251819 860597 := bbase (se 5 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 860597 = 80681) (by norm_num)
theorem B303545 : Blo 251819 303545 := bbase (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) (by norm_num)
theorem B270821 : Blo 251819 270821 := bbase (se 4 (by rfl) ⟨25389, by rfl⟩ : syracuseStep 270821 = 50779) (by norm_num)
theorem B270949 : Blo 251819 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B303853 : Blo 251819 303853 := bbase (se 3 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 303853 = 113945) (by norm_num)
theorem B861029 : Blo 251819 861029 := bbase (se 4 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 861029 = 161443) (by norm_num)
theorem B697349 : Blo 251819 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B271393 : Blo 251819 271393 := bbase (se 2 (by rfl) ⟨101772, by rfl⟩ : syracuseStep 271393 = 203545) (by norm_num)
theorem B304241 : Blo 251819 304241 := bbase (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) (by norm_num)
theorem B271513 : Blo 251819 271513 := bbase (se 2 (by rfl) ⟨101817, by rfl⟩ : syracuseStep 271513 = 203635) (by norm_num)
theorem B1287413 : Blo 251819 1287413 := bbase (se 5 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 1287413 = 120695) (by norm_num)
theorem B861461 : Blo 251819 861461 := bbase (se 6 (by rfl) ⟨20190, by rfl⟩ : syracuseStep 861461 = 40381) (by norm_num)
theorem B1221925 : Blo 251819 1221925 := bbase (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) (by norm_num)
theorem B566621 : Blo 251819 566621 := bbase (se 3 (by rfl) ⟨106241, by rfl⟩ : syracuseStep 566621 = 212483) (by norm_num)
theorem B271765 : Blo 251819 271765 := bbase (se 6 (by rfl) ⟨6369, by rfl⟩ : syracuseStep 271765 = 12739) (by norm_num)
theorem B271769 : Blo 251819 271769 := bbase (se 2 (by rfl) ⟨101913, by rfl⟩ : syracuseStep 271769 = 203827) (by norm_num)
theorem B566693 : Blo 251819 566693 := bbase (se 4 (by rfl) ⟨53127, by rfl⟩ : syracuseStep 566693 = 106255) (by norm_num)
theorem B959957 : Blo 251819 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B304597 : Blo 251819 304597 := bbase (se 7 (by rfl) ⟨3569, by rfl⟩ : syracuseStep 304597 = 7139) (by norm_num)
theorem B566765 : Blo 251819 566765 := bbase (se 3 (by rfl) ⟨106268, by rfl⟩ : syracuseStep 566765 = 212537) (by norm_num)
theorem B435701 : Blo 251819 435701 := bbase (se 5 (by rfl) ⟨20423, by rfl⟩ : syracuseStep 435701 = 40847) (by norm_num)
theorem B566837 : Blo 251819 566837 := bbase (se 5 (by rfl) ⟨26570, by rfl⟩ : syracuseStep 566837 = 53141) (by norm_num)
theorem B1746517 : Blo 251819 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B566909 : Blo 251819 566909 := bbase (se 3 (by rfl) ⟨106295, by rfl⟩ : syracuseStep 566909 = 212591) (by norm_num)
theorem B566981 : Blo 251819 566981 := bbase (se 4 (by rfl) ⟨53154, by rfl⟩ : syracuseStep 566981 = 106309) (by norm_num)
theorem B861893 : Blo 251819 861893 := bbase (se 4 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 861893 = 161605) (by norm_num)
theorem B960245 : Blo 251819 960245 := bbase (se 5 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 960245 = 90023) (by norm_num)
theorem B567053 : Blo 251819 567053 := bbase (se 3 (by rfl) ⟨106322, by rfl⟩ : syracuseStep 567053 = 212645) (by norm_num)
theorem B304933 : Blo 251819 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B567125 : Blo 251819 567125 := bbase (se 9 (by rfl) ⟨1661, by rfl⟩ : syracuseStep 567125 = 3323) (by norm_num)
theorem B567197 : Blo 251819 567197 := bbase (se 3 (by rfl) ⟨106349, by rfl⟩ : syracuseStep 567197 = 212699) (by norm_num)
theorem B272333 : Blo 251819 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B567269 : Blo 251819 567269 := bbase (se 4 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 567269 = 106363) (by norm_num)
theorem B567341 : Blo 251819 567341 := bbase (se 3 (by rfl) ⟨106376, by rfl⟩ : syracuseStep 567341 = 212753) (by norm_num)
theorem B567413 : Blo 251819 567413 := bbase (se 5 (by rfl) ⟨26597, by rfl⟩ : syracuseStep 567413 = 53195) (by norm_num)
theorem B862325 : Blo 251819 862325 := bbase (se 5 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 862325 = 80843) (by norm_num)
theorem B272521 : Blo 251819 272521 := bbase (se 2 (by rfl) ⟨102195, by rfl⟩ : syracuseStep 272521 = 204391) (by norm_num)
theorem B567485 : Blo 251819 567485 := bbase (se 3 (by rfl) ⟨106403, by rfl⟩ : syracuseStep 567485 = 212807) (by norm_num)
theorem B567557 : Blo 251819 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B567629 : Blo 251819 567629 := bbase (se 3 (by rfl) ⟨106430, by rfl⟩ : syracuseStep 567629 = 212861) (by norm_num)
theorem B403861 : Blo 251819 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B567701 : Blo 251819 567701 := bbase (se 6 (by rfl) ⟨13305, by rfl⟩ : syracuseStep 567701 = 26611) (by norm_num)
theorem B567773 : Blo 251819 567773 := bbase (se 3 (by rfl) ⟨106457, by rfl⟩ : syracuseStep 567773 = 212915) (by norm_num)
theorem B403957 : Blo 251819 403957 := bbase (se 5 (by rfl) ⟨18935, by rfl⟩ : syracuseStep 403957 = 37871) (by norm_num)
theorem B1288709 : Blo 251819 1288709 := bbase (se 4 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 1288709 = 241633) (by norm_num)
theorem B567845 : Blo 251819 567845 := bbase (se 4 (by rfl) ⟨53235, by rfl⟩ : syracuseStep 567845 = 106471) (by norm_num)
theorem B862757 : Blo 251819 862757 := bbase (se 4 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 862757 = 161767) (by norm_num)
theorem B1092133 : Blo 251819 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B567917 : Blo 251819 567917 := bbase (se 3 (by rfl) ⟨106484, by rfl⟩ : syracuseStep 567917 = 212969) (by norm_num)
theorem B404117 : Blo 251819 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B305813 : Blo 251819 305813 := bbase (se 6 (by rfl) ⟨7167, by rfl⟩ : syracuseStep 305813 = 14335) (by norm_num)
theorem B567989 : Blo 251819 567989 := bbase (se 5 (by rfl) ⟨26624, by rfl⟩ : syracuseStep 567989 = 53249) (by norm_num)
theorem B568061 : Blo 251819 568061 := bbase (se 3 (by rfl) ⟨106511, by rfl⟩ : syracuseStep 568061 = 213023) (by norm_num)
theorem B568133 : Blo 251819 568133 := bbase (se 4 (by rfl) ⟨53262, by rfl⟩ : syracuseStep 568133 = 106525) (by norm_num)
theorem B437101 : Blo 251819 437101 := bbase (se 3 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 437101 = 163913) (by norm_num)
theorem B568205 : Blo 251819 568205 := bbase (se 3 (by rfl) ⟨106538, by rfl⟩ : syracuseStep 568205 = 213077) (by norm_num)
theorem B961429 : Blo 251819 961429 := bbase (se 6 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 961429 = 45067) (by norm_num)
theorem B1158085 : Blo 251819 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B306121 : Blo 251819 306121 := bbase (se 2 (by rfl) ⟨114795, by rfl⟩ : syracuseStep 306121 = 229591) (by norm_num)
theorem B568277 : Blo 251819 568277 := bbase (se 7 (by rfl) ⟨6659, by rfl⟩ : syracuseStep 568277 = 13319) (by norm_num)
theorem B863189 : Blo 251819 863189 := bbase (se 7 (by rfl) ⟨10115, by rfl⟩ : syracuseStep 863189 = 20231) (by norm_num)
theorem B568349 : Blo 251819 568349 := bbase (se 3 (by rfl) ⟨106565, by rfl⟩ : syracuseStep 568349 = 213131) (by norm_num)
theorem B568421 : Blo 251819 568421 := bbase (se 4 (by rfl) ⟨53289, by rfl⟩ : syracuseStep 568421 = 106579) (by norm_num)
theorem B568493 : Blo 251819 568493 := bbase (se 3 (by rfl) ⟨106592, by rfl⟩ : syracuseStep 568493 = 213185) (by norm_num)
theorem B961733 : Blo 251819 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B568565 : Blo 251819 568565 := bbase (se 5 (by rfl) ⟨26651, by rfl⟩ : syracuseStep 568565 = 53303) (by norm_num)
theorem B568637 : Blo 251819 568637 := bbase (se 3 (by rfl) ⟨106619, by rfl⟩ : syracuseStep 568637 = 213239) (by norm_num)
theorem B306505 : Blo 251819 306505 := bbase (se 2 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 306505 = 229879) (by norm_num)
theorem B306509 : Blo 251819 306509 := bbase (se 3 (by rfl) ⟨57470, by rfl⟩ : syracuseStep 306509 = 114941) (by norm_num)
theorem B568709 : Blo 251819 568709 := bbase (se 4 (by rfl) ⟨53316, by rfl⟩ : syracuseStep 568709 = 106633) (by norm_num)
theorem B568781 : Blo 251819 568781 := bbase (se 3 (by rfl) ⟨106646, by rfl⟩ : syracuseStep 568781 = 213293) (by norm_num)
theorem B568853 : Blo 251819 568853 := bbase (se 6 (by rfl) ⟨13332, by rfl⟩ : syracuseStep 568853 = 26665) (by norm_num)
theorem B568925 : Blo 251819 568925 := bbase (se 3 (by rfl) ⟨106673, by rfl⟩ : syracuseStep 568925 = 213347) (by norm_num)
theorem B568997 : Blo 251819 568997 := bbase (se 4 (by rfl) ⟨53343, by rfl⟩ : syracuseStep 568997 = 106687) (by norm_num)
theorem B306913 : Blo 251819 306913 := bbase (se 2 (by rfl) ⟨115092, by rfl⟩ : syracuseStep 306913 = 230185) (by norm_num)
theorem B569069 : Blo 251819 569069 := bbase (se 3 (by rfl) ⟨106700, by rfl⟩ : syracuseStep 569069 = 213401) (by norm_num)
theorem B405245 : Blo 251819 405245 := bbase (se 3 (by rfl) ⟨75983, by rfl⟩ : syracuseStep 405245 = 151967) (by norm_num)
theorem B1290005 : Blo 251819 1290005 := bbase (se 6 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 1290005 = 60469) (by norm_num)
theorem B569141 : Blo 251819 569141 := bbase (se 5 (by rfl) ⟨26678, by rfl⟩ : syracuseStep 569141 = 53357) (by norm_num)
theorem B569213 : Blo 251819 569213 := bbase (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) (by norm_num)
theorem B569285 : Blo 251819 569285 := bbase (se 4 (by rfl) ⟨53370, by rfl⟩ : syracuseStep 569285 = 106741) (by norm_num)
theorem B569357 : Blo 251819 569357 := bbase (se 3 (by rfl) ⟨106754, by rfl⟩ : syracuseStep 569357 = 213509) (by norm_num)
theorem B569429 : Blo 251819 569429 := bbase (se 8 (by rfl) ⟨3336, by rfl⟩ : syracuseStep 569429 = 6673) (by norm_num)
theorem B569501 : Blo 251819 569501 := bbase (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) (by norm_num)
theorem B569573 : Blo 251819 569573 := bbase (se 4 (by rfl) ⟨53397, by rfl⟩ : syracuseStep 569573 = 106795) (by norm_num)
theorem B405757 : Blo 251819 405757 := bbase (se 3 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 405757 = 152159) (by norm_num)
theorem B569645 : Blo 251819 569645 := bbase (se 3 (by rfl) ⟨106808, by rfl⟩ : syracuseStep 569645 = 213617) (by norm_num)
theorem B569717 : Blo 251819 569717 := bbase (se 5 (by rfl) ⟨26705, by rfl⟩ : syracuseStep 569717 = 53411) (by norm_num)
theorem B307585 : Blo 251819 307585 := bbase (se 2 (by rfl) ⟨115344, by rfl⟩ : syracuseStep 307585 = 230689) (by norm_num)
theorem B569789 : Blo 251819 569789 := bbase (se 3 (by rfl) ⟨106835, by rfl⟩ : syracuseStep 569789 = 213671) (by norm_num)
theorem B569861 : Blo 251819 569861 := bbase (se 4 (by rfl) ⟨53424, by rfl⟩ : syracuseStep 569861 = 106849) (by norm_num)
theorem B569933 : Blo 251819 569933 := bbase (se 3 (by rfl) ⟨106862, by rfl⟩ : syracuseStep 569933 = 213725) (by norm_num)
theorem B1618517 : Blo 251819 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B570005 : Blo 251819 570005 := bbase (se 6 (by rfl) ⟨13359, by rfl⟩ : syracuseStep 570005 = 26719) (by norm_num)
theorem B570077 : Blo 251819 570077 := bbase (se 3 (by rfl) ⟨106889, by rfl⟩ : syracuseStep 570077 = 213779) (by norm_num)
theorem B1946389 : Blo 251819 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B570149 : Blo 251819 570149 := bbase (se 4 (by rfl) ⟨53451, by rfl⟩ : syracuseStep 570149 = 106903) (by norm_num)
theorem B1160021 : Blo 251819 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B570221 : Blo 251819 570221 := bbase (se 3 (by rfl) ⟨106916, by rfl⟩ : syracuseStep 570221 = 213833) (by norm_num)
theorem B570293 : Blo 251819 570293 := bbase (se 5 (by rfl) ⟨26732, by rfl⟩ : syracuseStep 570293 = 53465) (by norm_num)
theorem B570365 : Blo 251819 570365 := bbase (se 3 (by rfl) ⟨106943, by rfl⟩ : syracuseStep 570365 = 213887) (by norm_num)
theorem B766997 : Blo 251819 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B1291301 : Blo 251819 1291301 := bbase (se 4 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 1291301 = 242119) (by norm_num)
theorem B570437 : Blo 251819 570437 := bbase (se 4 (by rfl) ⟨53478, by rfl⟩ : syracuseStep 570437 = 106957) (by norm_num)
theorem B275581 : Blo 251819 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B570509 : Blo 251819 570509 := bbase (se 3 (by rfl) ⟨106970, by rfl⟩ : syracuseStep 570509 = 213941) (by norm_num)
theorem B2897045 : Blo 251819 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B570581 : Blo 251819 570581 := bbase (se 7 (by rfl) ⟨6686, by rfl⟩ : syracuseStep 570581 = 13373) (by norm_num)
theorem B406757 : Blo 251819 406757 := bbase (se 4 (by rfl) ⟨38133, by rfl⟩ : syracuseStep 406757 = 76267) (by norm_num)
theorem B963845 : Blo 251819 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B570653 : Blo 251819 570653 := bbase (se 3 (by rfl) ⟨106997, by rfl⟩ : syracuseStep 570653 = 213995) (by norm_num)
theorem B865637 : Blo 251819 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B570725 : Blo 251819 570725 := bbase (se 4 (by rfl) ⟨53505, by rfl⟩ : syracuseStep 570725 = 107011) (by norm_num)
theorem B406885 : Blo 251819 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B406949 : Blo 251819 406949 := bbase (se 4 (by rfl) ⟨38151, by rfl⟩ : syracuseStep 406949 = 76303) (by norm_num)
theorem B570797 : Blo 251819 570797 := bbase (se 3 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 570797 = 214049) (by norm_num)
theorem B570869 : Blo 251819 570869 := bbase (se 5 (by rfl) ⟨26759, by rfl⟩ : syracuseStep 570869 = 53519) (by norm_num)
theorem B865829 : Blo 251819 865829 := bbase (se 4 (by rfl) ⟨81171, by rfl⟩ : syracuseStep 865829 = 162343) (by norm_num)
theorem B964133 : Blo 251819 964133 := bbase (se 4 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 964133 = 180775) (by norm_num)
theorem B538157 : Blo 251819 538157 := bbase (se 3 (by rfl) ⟨100904, by rfl⟩ : syracuseStep 538157 = 201809) (by norm_num)
theorem B570941 : Blo 251819 570941 := bbase (se 3 (by rfl) ⟨107051, by rfl⟩ : syracuseStep 570941 = 214103) (by norm_num)
theorem B571013 : Blo 251819 571013 := bbase (se 4 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 571013 = 107065) (by norm_num)
theorem B571085 : Blo 251819 571085 := bbase (se 3 (by rfl) ⟨107078, by rfl⟩ : syracuseStep 571085 = 214157) (by norm_num)
theorem B571157 : Blo 251819 571157 := bbase (se 6 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 571157 = 26773) (by norm_num)
theorem B276257 : Blo 251819 276257 := bbase (se 2 (by rfl) ⟨103596, by rfl⟩ : syracuseStep 276257 = 207193) (by norm_num)
theorem B571229 : Blo 251819 571229 := bbase (se 3 (by rfl) ⟨107105, by rfl⟩ : syracuseStep 571229 = 214211) (by norm_num)
theorem B571301 : Blo 251819 571301 := bbase (se 4 (by rfl) ⟨53559, by rfl⟩ : syracuseStep 571301 = 107119) (by norm_num)
theorem B571373 : Blo 251819 571373 := bbase (se 3 (by rfl) ⟨107132, by rfl⟩ : syracuseStep 571373 = 214265) (by norm_num)
theorem B276517 : Blo 251819 276517 := bbase (se 4 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 276517 = 51847) (by norm_num)
theorem B571445 : Blo 251819 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B571517 : Blo 251819 571517 := bbase (se 3 (by rfl) ⟨107159, by rfl⟩ : syracuseStep 571517 = 214319) (by norm_num)
theorem B571589 : Blo 251819 571589 := bbase (se 4 (by rfl) ⟨53586, by rfl⟩ : syracuseStep 571589 = 107173) (by norm_num)
theorem B571661 : Blo 251819 571661 := bbase (se 3 (by rfl) ⟨107186, by rfl⟩ : syracuseStep 571661 = 214373) (by norm_num)
theorem B1292597 : Blo 251819 1292597 := bbase (se 5 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 1292597 = 121181) (by norm_num)
theorem B571733 : Blo 251819 571733 := bbase (se 10 (by rfl) ⟨837, by rfl⟩ : syracuseStep 571733 = 1675) (by norm_num)
theorem B342397 : Blo 251819 342397 := bbase (se 3 (by rfl) ⟨64199, by rfl⟩ : syracuseStep 342397 = 128399) (by norm_num)
theorem B571805 : Blo 251819 571805 := bbase (se 3 (by rfl) ⟨107213, by rfl⟩ : syracuseStep 571805 = 214427) (by norm_num)
theorem B539045 : Blo 251819 539045 := bbase (se 4 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 539045 = 101071) (by norm_num)
theorem B571877 : Blo 251819 571877 := bbase (se 4 (by rfl) ⟨53613, by rfl⟩ : syracuseStep 571877 = 107227) (by norm_num)
theorem B637429 : Blo 251819 637429 := bbase (se 5 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 637429 = 59759) (by norm_num)
theorem B571949 : Blo 251819 571949 := bbase (se 3 (by rfl) ⟨107240, by rfl⟩ : syracuseStep 571949 = 214481) (by norm_num)
theorem B637541 : Blo 251819 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B572021 : Blo 251819 572021 := bbase (se 5 (by rfl) ⟨26813, by rfl⟩ : syracuseStep 572021 = 53627) (by norm_num)
theorem B539293 : Blo 251819 539293 := bbase (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) (by norm_num)
theorem B572093 : Blo 251819 572093 := bbase (se 3 (by rfl) ⟨107267, by rfl⟩ : syracuseStep 572093 = 214535) (by norm_num)
theorem B965317 : Blo 251819 965317 := bbase (se 4 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 965317 = 180997) (by norm_num)
theorem B408269 : Blo 251819 408269 := bbase (se 3 (by rfl) ⟨76550, by rfl⟩ : syracuseStep 408269 = 153101) (by norm_num)
theorem B572165 : Blo 251819 572165 := bbase (se 4 (by rfl) ⟨53640, by rfl⟩ : syracuseStep 572165 = 107281) (by norm_num)
theorem B637733 : Blo 251819 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B572237 : Blo 251819 572237 := bbase (se 3 (by rfl) ⟨107294, by rfl⟩ : syracuseStep 572237 = 214589) (by norm_num)
theorem B408397 : Blo 251819 408397 := bbase (se 3 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 408397 = 153149) (by norm_num)
theorem B2308949 : Blo 251819 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B572309 : Blo 251819 572309 := bbase (se 6 (by rfl) ⟨13413, by rfl⟩ : syracuseStep 572309 = 26827) (by norm_num)
theorem B572381 : Blo 251819 572381 := bbase (se 3 (by rfl) ⟨107321, by rfl⟩ : syracuseStep 572381 = 214643) (by norm_num)
theorem B965621 : Blo 251819 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B572453 : Blo 251819 572453 := bbase (se 4 (by rfl) ⟨53667, by rfl⟩ : syracuseStep 572453 = 107335) (by norm_num)
theorem B605245 : Blo 251819 605245 := bbase (se 3 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 605245 = 226967) (by norm_num)
theorem B572525 : Blo 251819 572525 := bbase (se 3 (by rfl) ⟨107348, by rfl⟩ : syracuseStep 572525 = 214697) (by norm_num)
theorem B638077 : Blo 251819 638077 := bbase (se 3 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 638077 = 239279) (by norm_num)
theorem B539797 : Blo 251819 539797 := bbase (se 6 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 539797 = 25303) (by norm_num)
theorem B572597 : Blo 251819 572597 := bbase (se 5 (by rfl) ⟨26840, by rfl⟩ : syracuseStep 572597 = 53681) (by norm_num)
theorem B343261 : Blo 251819 343261 := bbase (se 3 (by rfl) ⟨64361, by rfl⟩ : syracuseStep 343261 = 128723) (by norm_num)
theorem B638189 : Blo 251819 638189 := bbase (se 3 (by rfl) ⟨119660, by rfl⟩ : syracuseStep 638189 = 239321) (by norm_num)
theorem B572669 : Blo 251819 572669 := bbase (se 3 (by rfl) ⟨107375, by rfl⟩ : syracuseStep 572669 = 214751) (by norm_num)
theorem B933125 : Blo 251819 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B572741 : Blo 251819 572741 := bbase (se 4 (by rfl) ⟨53694, by rfl⟩ : syracuseStep 572741 = 107389) (by norm_num)
theorem B572813 : Blo 251819 572813 := bbase (se 3 (by rfl) ⟨107402, by rfl⟩ : syracuseStep 572813 = 214805) (by norm_num)
theorem B638381 : Blo 251819 638381 := bbase (se 3 (by rfl) ⟨119696, by rfl⟩ : syracuseStep 638381 = 239393) (by norm_num)
theorem B1228229 : Blo 251819 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B572885 : Blo 251819 572885 := bbase (se 7 (by rfl) ⟨6713, by rfl⟩ : syracuseStep 572885 = 13427) (by norm_num)
theorem B572957 : Blo 251819 572957 := bbase (se 3 (by rfl) ⟨107429, by rfl⟩ : syracuseStep 572957 = 214859) (by norm_num)
theorem B1293893 : Blo 251819 1293893 := bbase (se 4 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 1293893 = 242605) (by norm_num)
theorem B573029 : Blo 251819 573029 := bbase (se 4 (by rfl) ⟨53721, by rfl⟩ : syracuseStep 573029 = 107443) (by norm_num)
theorem B409205 : Blo 251819 409205 := bbase (se 5 (by rfl) ⟨19181, by rfl⟩ : syracuseStep 409205 = 38363) (by norm_num)
theorem B573101 : Blo 251819 573101 := bbase (se 3 (by rfl) ⟨107456, by rfl⟩ : syracuseStep 573101 = 214913) (by norm_num)
theorem B573173 : Blo 251819 573173 := bbase (se 5 (by rfl) ⟨26867, by rfl⟩ : syracuseStep 573173 = 53735) (by norm_num)
theorem B638725 : Blo 251819 638725 := bbase (se 4 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 638725 = 119761) (by norm_num)
theorem B573245 : Blo 251819 573245 := bbase (se 3 (by rfl) ⟨107483, by rfl⟩ : syracuseStep 573245 = 214967) (by norm_num)
theorem B638837 : Blo 251819 638837 := bbase (se 5 (by rfl) ⟨29945, by rfl⟩ : syracuseStep 638837 = 59891) (by norm_num)
theorem B573317 : Blo 251819 573317 := bbase (se 4 (by rfl) ⟨53748, by rfl⟩ : syracuseStep 573317 = 107497) (by norm_num)
theorem B409493 : Blo 251819 409493 := bbase (se 6 (by rfl) ⟨9597, by rfl⟩ : syracuseStep 409493 = 19195) (by norm_num)
theorem B573389 : Blo 251819 573389 := bbase (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) (by norm_num)
theorem B540685 : Blo 251819 540685 := bbase (se 3 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 540685 = 202757) (by norm_num)
theorem B573461 : Blo 251819 573461 := bbase (se 6 (by rfl) ⟨13440, by rfl⟩ : syracuseStep 573461 = 26881) (by norm_num)
theorem B639029 : Blo 251819 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B573533 : Blo 251819 573533 := bbase (se 3 (by rfl) ⟨107537, by rfl⟩ : syracuseStep 573533 = 215075) (by norm_num)
theorem B573605 : Blo 251819 573605 := bbase (se 4 (by rfl) ⟨53775, by rfl⟩ : syracuseStep 573605 = 107551) (by norm_num)
theorem B573677 : Blo 251819 573677 := bbase (se 3 (by rfl) ⟨107564, by rfl⟩ : syracuseStep 573677 = 215129) (by norm_num)
theorem B573749 : Blo 251819 573749 := bbase (se 5 (by rfl) ⟨26894, by rfl⟩ : syracuseStep 573749 = 53789) (by norm_num)
theorem B1917269 : Blo 251819 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B1622389 : Blo 251819 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B573821 : Blo 251819 573821 := bbase (se 3 (by rfl) ⟨107591, by rfl⟩ : syracuseStep 573821 = 215183) (by norm_num)
theorem B639373 : Blo 251819 639373 := bbase (se 3 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 639373 = 239765) (by norm_num)
theorem B573893 : Blo 251819 573893 := bbase (se 4 (by rfl) ⟨53802, by rfl⟩ : syracuseStep 573893 = 107605) (by norm_num)
theorem B639485 : Blo 251819 639485 := bbase (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) (by norm_num)
theorem B541181 : Blo 251819 541181 := bbase (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) (by norm_num)
theorem B573965 : Blo 251819 573965 := bbase (se 3 (by rfl) ⟨107618, by rfl⟩ : syracuseStep 573965 = 215237) (by norm_num)
theorem B574037 : Blo 251819 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B574109 : Blo 251819 574109 := bbase (se 3 (by rfl) ⟨107645, by rfl⟩ : syracuseStep 574109 = 215291) (by norm_num)
theorem B639677 : Blo 251819 639677 := bbase (se 3 (by rfl) ⟨119939, by rfl⟩ : syracuseStep 639677 = 239879) (by norm_num)
theorem B574181 : Blo 251819 574181 := bbase (se 4 (by rfl) ⟨53829, by rfl⟩ : syracuseStep 574181 = 107659) (by norm_num)
theorem B574253 : Blo 251819 574253 := bbase (se 3 (by rfl) ⟨107672, by rfl⟩ : syracuseStep 574253 = 215345) (by norm_num)
theorem B574325 : Blo 251819 574325 := bbase (se 5 (by rfl) ⟨26921, by rfl⟩ : syracuseStep 574325 = 53843) (by norm_num)
theorem B377741 : Blo 251819 377741 := bbase (se 3 (by rfl) ⟨70826, by rfl⟩ : syracuseStep 377741 = 141653) (by norm_num)
theorem B574373 : Blo 251819 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B377765 : Blo 251819 377765 := bbase (se 4 (by rfl) ⟨35415, by rfl⟩ : syracuseStep 377765 = 70831) (by norm_num)
theorem B377789 : Blo 251819 377789 := bbase (se 3 (by rfl) ⟨70835, by rfl⟩ : syracuseStep 377789 = 141671) (by norm_num)
theorem B574397 : Blo 251819 574397 := bbase (se 3 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 574397 = 215399) (by norm_num)
theorem B377813 : Blo 251819 377813 := bbase (se 7 (by rfl) ⟨4427, by rfl⟩ : syracuseStep 377813 = 8855) (by norm_num)
theorem B377837 : Blo 251819 377837 := bbase (se 3 (by rfl) ⟨70844, by rfl⟩ : syracuseStep 377837 = 141689) (by norm_num)
theorem B377861 : Blo 251819 377861 := bbase (se 4 (by rfl) ⟨35424, by rfl⟩ : syracuseStep 377861 = 70849) (by norm_num)
theorem B574469 : Blo 251819 574469 := bbase (se 4 (by rfl) ⟨53856, by rfl⟩ : syracuseStep 574469 = 107713) (by norm_num)
theorem B640021 : Blo 251819 640021 := bbase (se 6 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 640021 = 30001) (by norm_num)
theorem B377885 : Blo 251819 377885 := bbase (se 3 (by rfl) ⟨70853, by rfl⟩ : syracuseStep 377885 = 141707) (by norm_num)
theorem B574517 : Blo 251819 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B377909 : Blo 251819 377909 := bbase (se 5 (by rfl) ⟨17714, by rfl⟩ : syracuseStep 377909 = 35429) (by norm_num)
theorem B967733 : Blo 251819 967733 := bbase (se 5 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 967733 = 90725) (by norm_num)
theorem B377933 : Blo 251819 377933 := bbase (se 3 (by rfl) ⟨70862, by rfl⟩ : syracuseStep 377933 = 141725) (by norm_num)
theorem B574541 : Blo 251819 574541 := bbase (se 3 (by rfl) ⟨107726, by rfl⟩ : syracuseStep 574541 = 215453) (by norm_num)
theorem B377957 : Blo 251819 377957 := bbase (se 4 (by rfl) ⟨35433, by rfl⟩ : syracuseStep 377957 = 70867) (by norm_num)
theorem B377981 : Blo 251819 377981 := bbase (se 3 (by rfl) ⟨70871, by rfl⟩ : syracuseStep 377981 = 141743) (by norm_num)
theorem B640133 : Blo 251819 640133 := bbase (se 4 (by rfl) ⟨60012, by rfl⟩ : syracuseStep 640133 = 120025) (by norm_num)
theorem B378005 : Blo 251819 378005 := bbase (se 6 (by rfl) ⟨8859, by rfl⟩ : syracuseStep 378005 = 17719) (by norm_num)
theorem B574613 : Blo 251819 574613 := bbase (se 6 (by rfl) ⟨13467, by rfl⟩ : syracuseStep 574613 = 26935) (by norm_num)
theorem B378029 : Blo 251819 378029 := bbase (se 3 (by rfl) ⟨70880, by rfl⟩ : syracuseStep 378029 = 141761) (by norm_num)
theorem B378053 : Blo 251819 378053 := bbase (se 4 (by rfl) ⟨35442, by rfl⟩ : syracuseStep 378053 = 70885) (by norm_num)
theorem B378077 : Blo 251819 378077 := bbase (se 3 (by rfl) ⟨70889, by rfl⟩ : syracuseStep 378077 = 141779) (by norm_num)
theorem B574685 : Blo 251819 574685 := bbase (se 3 (by rfl) ⟨107753, by rfl⟩ : syracuseStep 574685 = 215507) (by norm_num)
theorem B378101 : Blo 251819 378101 := bbase (se 5 (by rfl) ⟨17723, by rfl⟩ : syracuseStep 378101 = 35447) (by norm_num)
theorem B378125 : Blo 251819 378125 := bbase (se 3 (by rfl) ⟨70898, by rfl⟩ : syracuseStep 378125 = 141797) (by norm_num)
theorem B378149 : Blo 251819 378149 := bbase (se 4 (by rfl) ⟨35451, by rfl⟩ : syracuseStep 378149 = 70903) (by norm_num)
theorem B574757 : Blo 251819 574757 := bbase (se 4 (by rfl) ⟨53883, by rfl⟩ : syracuseStep 574757 = 107767) (by norm_num)
theorem B378173 : Blo 251819 378173 := bbase (se 3 (by rfl) ⟨70907, by rfl⟩ : syracuseStep 378173 = 141815) (by norm_num)
theorem B640325 : Blo 251819 640325 := bbase (se 4 (by rfl) ⟨60030, by rfl⟩ : syracuseStep 640325 = 120061) (by norm_num)
theorem B378197 : Blo 251819 378197 := bbase (se 12 (by rfl) ⟨138, by rfl⟩ : syracuseStep 378197 = 277) (by norm_num)
theorem B968021 : Blo 251819 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B378221 : Blo 251819 378221 := bbase (se 3 (by rfl) ⟨70916, by rfl⟩ : syracuseStep 378221 = 141833) (by norm_num)
theorem B574829 : Blo 251819 574829 := bbase (se 3 (by rfl) ⟨107780, by rfl⟩ : syracuseStep 574829 = 215561) (by norm_num)
theorem B542069 : Blo 251819 542069 := bbase (se 5 (by rfl) ⟨25409, by rfl⟩ : syracuseStep 542069 = 50819) (by norm_num)
theorem B378245 : Blo 251819 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B607637 : Blo 251819 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B378269 : Blo 251819 378269 := bbase (se 3 (by rfl) ⟨70925, by rfl⟩ : syracuseStep 378269 = 141851) (by norm_num)
theorem B378293 : Blo 251819 378293 := bbase (se 5 (by rfl) ⟨17732, by rfl⟩ : syracuseStep 378293 = 35465) (by norm_num)
theorem B574901 : Blo 251819 574901 := bbase (se 5 (by rfl) ⟨26948, by rfl⟩ : syracuseStep 574901 = 53897) (by norm_num)
theorem B378317 : Blo 251819 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B378341 : Blo 251819 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B542189 : Blo 251819 542189 := bbase (se 3 (by rfl) ⟨101660, by rfl⟩ : syracuseStep 542189 = 203321) (by norm_num)
theorem B378365 : Blo 251819 378365 := bbase (se 3 (by rfl) ⟨70943, by rfl⟩ : syracuseStep 378365 = 141887) (by norm_num)
theorem B574973 : Blo 251819 574973 := bbase (se 3 (by rfl) ⟨107807, by rfl⟩ : syracuseStep 574973 = 215615) (by norm_num)
theorem B345613 : Blo 251819 345613 := bbase (se 3 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 345613 = 129605) (by norm_num)
theorem B378389 : Blo 251819 378389 := bbase (se 6 (by rfl) ⟨8868, by rfl⟩ : syracuseStep 378389 = 17737) (by norm_num)
theorem B607781 : Blo 251819 607781 := bbase (se 4 (by rfl) ⟨56979, by rfl⟩ : syracuseStep 607781 = 113959) (by norm_num)
theorem B378413 : Blo 251819 378413 := bbase (se 3 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 378413 = 141905) (by norm_num)
theorem B378437 : Blo 251819 378437 := bbase (se 4 (by rfl) ⟨35478, by rfl⟩ : syracuseStep 378437 = 70957) (by norm_num)
theorem B575045 : Blo 251819 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B4343381 : Blo 251819 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B378461 : Blo 251819 378461 := bbase (se 3 (by rfl) ⟨70961, by rfl⟩ : syracuseStep 378461 = 141923) (by norm_num)
theorem B378485 : Blo 251819 378485 := bbase (se 5 (by rfl) ⟨17741, by rfl⟩ : syracuseStep 378485 = 35483) (by norm_num)
theorem B378509 : Blo 251819 378509 := bbase (se 3 (by rfl) ⟨70970, by rfl⟩ : syracuseStep 378509 = 141941) (by norm_num)
theorem B575117 : Blo 251819 575117 := bbase (se 3 (by rfl) ⟨107834, by rfl⟩ : syracuseStep 575117 = 215669) (by norm_num)
theorem B640669 : Blo 251819 640669 := bbase (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) (by norm_num)
theorem B378533 : Blo 251819 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B378557 : Blo 251819 378557 := bbase (se 3 (by rfl) ⟨70979, by rfl⟩ : syracuseStep 378557 = 141959) (by norm_num)
theorem B378581 : Blo 251819 378581 := bbase (se 7 (by rfl) ⟨4436, by rfl⟩ : syracuseStep 378581 = 8873) (by norm_num)
theorem B575189 : Blo 251819 575189 := bbase (se 7 (by rfl) ⟨6740, by rfl⟩ : syracuseStep 575189 = 13481) (by norm_num)
theorem B378605 : Blo 251819 378605 := bbase (se 3 (by rfl) ⟨70988, by rfl⟩ : syracuseStep 378605 = 141977) (by norm_num)
theorem B378629 : Blo 251819 378629 := bbase (se 4 (by rfl) ⟨35496, by rfl⟩ : syracuseStep 378629 = 70993) (by norm_num)
theorem B640781 : Blo 251819 640781 := bbase (se 3 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 640781 = 240293) (by norm_num)
theorem B378653 : Blo 251819 378653 := bbase (se 3 (by rfl) ⟨70997, by rfl⟩ : syracuseStep 378653 = 141995) (by norm_num)
theorem B575261 : Blo 251819 575261 := bbase (se 3 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 575261 = 215723) (by norm_num)
theorem B378677 : Blo 251819 378677 := bbase (se 5 (by rfl) ⟨17750, by rfl⟩ : syracuseStep 378677 = 35501) (by norm_num)
theorem B378701 : Blo 251819 378701 := bbase (se 3 (by rfl) ⟨71006, by rfl⟩ : syracuseStep 378701 = 142013) (by norm_num)
theorem B378725 : Blo 251819 378725 := bbase (se 4 (by rfl) ⟨35505, by rfl⟩ : syracuseStep 378725 = 71011) (by norm_num)
theorem B575333 : Blo 251819 575333 := bbase (se 4 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 575333 = 107875) (by norm_num)
theorem B378749 : Blo 251819 378749 := bbase (se 3 (by rfl) ⟨71015, by rfl⟩ : syracuseStep 378749 = 142031) (by norm_num)
theorem B1034117 : Blo 251819 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B378773 : Blo 251819 378773 := bbase (se 6 (by rfl) ⟨8877, by rfl⟩ : syracuseStep 378773 = 17755) (by norm_num)
theorem B378797 : Blo 251819 378797 := bbase (se 3 (by rfl) ⟨71024, by rfl⟩ : syracuseStep 378797 = 142049) (by norm_num)
theorem B575405 : Blo 251819 575405 := bbase (se 3 (by rfl) ⟨107888, by rfl⟩ : syracuseStep 575405 = 215777) (by norm_num)
theorem B378821 : Blo 251819 378821 := bbase (se 4 (by rfl) ⟨35514, by rfl⟩ : syracuseStep 378821 = 71029) (by norm_num)
theorem B640973 : Blo 251819 640973 := bbase (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) (by norm_num)
theorem B378845 : Blo 251819 378845 := bbase (se 3 (by rfl) ⟨71033, by rfl⟩ : syracuseStep 378845 = 142067) (by norm_num)
theorem B378869 : Blo 251819 378869 := bbase (se 5 (by rfl) ⟨17759, by rfl⟩ : syracuseStep 378869 = 35519) (by norm_num)
theorem B575477 : Blo 251819 575477 := bbase (se 5 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 575477 = 53951) (by norm_num)
theorem B378893 : Blo 251819 378893 := bbase (se 3 (by rfl) ⟨71042, by rfl⟩ : syracuseStep 378893 = 142085) (by norm_num)
theorem B4769813 : Blo 251819 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B378917 : Blo 251819 378917 := bbase (se 4 (by rfl) ⟨35523, by rfl⟩ : syracuseStep 378917 = 71047) (by norm_num)
theorem B378941 : Blo 251819 378941 := bbase (se 3 (by rfl) ⟨71051, by rfl⟩ : syracuseStep 378941 = 142103) (by norm_num)
theorem B575549 : Blo 251819 575549 := bbase (se 3 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 575549 = 215831) (by norm_num)
theorem B378965 : Blo 251819 378965 := bbase (se 8 (by rfl) ⟨2220, by rfl⟩ : syracuseStep 378965 = 4441) (by norm_num)
theorem B542821 : Blo 251819 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B378989 : Blo 251819 378989 := bbase (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) (by norm_num)
theorem B379013 : Blo 251819 379013 := bbase (se 4 (by rfl) ⟨35532, by rfl⟩ : syracuseStep 379013 = 71065) (by norm_num)
theorem B379037 : Blo 251819 379037 := bbase (se 3 (by rfl) ⟨71069, by rfl⟩ : syracuseStep 379037 = 142139) (by norm_num)
theorem B379061 : Blo 251819 379061 := bbase (se 5 (by rfl) ⟨17768, by rfl⟩ : syracuseStep 379061 = 35537) (by norm_num)
theorem B379085 : Blo 251819 379085 := bbase (se 3 (by rfl) ⟨71078, by rfl⟩ : syracuseStep 379085 = 142157) (by norm_num)
theorem B379109 : Blo 251819 379109 := bbase (se 4 (by rfl) ⟨35541, by rfl⟩ : syracuseStep 379109 = 71083) (by norm_num)
theorem B379133 : Blo 251819 379133 := bbase (se 3 (by rfl) ⟨71087, by rfl⟩ : syracuseStep 379133 = 142175) (by norm_num)
theorem B379157 : Blo 251819 379157 := bbase (se 6 (by rfl) ⟨8886, by rfl⟩ : syracuseStep 379157 = 17773) (by norm_num)
theorem B641317 : Blo 251819 641317 := bbase (se 4 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 641317 = 120247) (by norm_num)
theorem B379181 : Blo 251819 379181 := bbase (se 3 (by rfl) ⟨71096, by rfl⟩ : syracuseStep 379181 = 142193) (by norm_num)
theorem B379205 : Blo 251819 379205 := bbase (se 4 (by rfl) ⟨35550, by rfl⟩ : syracuseStep 379205 = 71101) (by norm_num)
theorem B379229 : Blo 251819 379229 := bbase (se 3 (by rfl) ⟨71105, by rfl⟩ : syracuseStep 379229 = 142211) (by norm_num)
theorem B379253 : Blo 251819 379253 := bbase (se 5 (by rfl) ⟨17777, by rfl⟩ : syracuseStep 379253 = 35555) (by norm_num)
theorem B1296773 : Blo 251819 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B379277 : Blo 251819 379277 := bbase (se 3 (by rfl) ⟨71114, by rfl⟩ : syracuseStep 379277 = 142229) (by norm_num)
theorem B641429 : Blo 251819 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B379301 : Blo 251819 379301 := bbase (se 4 (by rfl) ⟨35559, by rfl⟩ : syracuseStep 379301 = 71119) (by norm_num)
theorem B379325 : Blo 251819 379325 := bbase (se 3 (by rfl) ⟨71123, by rfl⟩ : syracuseStep 379325 = 142247) (by norm_num)
theorem B379349 : Blo 251819 379349 := bbase (se 7 (by rfl) ⟨4445, by rfl⟩ : syracuseStep 379349 = 8891) (by norm_num)
theorem B379373 : Blo 251819 379373 := bbase (se 3 (by rfl) ⟨71132, by rfl⟩ : syracuseStep 379373 = 142265) (by norm_num)
theorem B969205 : Blo 251819 969205 := bbase (se 5 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 969205 = 90863) (by norm_num)
theorem B379397 : Blo 251819 379397 := bbase (se 4 (by rfl) ⟨35568, by rfl⟩ : syracuseStep 379397 = 71137) (by norm_num)
theorem B379421 : Blo 251819 379421 := bbase (se 3 (by rfl) ⟨71141, by rfl⟩ : syracuseStep 379421 = 142283) (by norm_num)
theorem B379445 : Blo 251819 379445 := bbase (se 5 (by rfl) ⟨17786, by rfl⟩ : syracuseStep 379445 = 35573) (by norm_num)
theorem B379469 : Blo 251819 379469 := bbase (se 3 (by rfl) ⟨71150, by rfl⟩ : syracuseStep 379469 = 142301) (by norm_num)
theorem B641621 : Blo 251819 641621 := bbase (se 8 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 641621 = 7519) (by norm_num)
theorem B11061845 : Blo 251819 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B379493 : Blo 251819 379493 := bbase (se 4 (by rfl) ⟨35577, by rfl⟩ : syracuseStep 379493 = 71155) (by norm_num)
theorem B379517 : Blo 251819 379517 := bbase (se 3 (by rfl) ⟨71159, by rfl⟩ : syracuseStep 379517 = 142319) (by norm_num)
theorem B379541 : Blo 251819 379541 := bbase (se 6 (by rfl) ⟨8895, by rfl⟩ : syracuseStep 379541 = 17791) (by norm_num)
theorem B379565 : Blo 251819 379565 := bbase (se 3 (by rfl) ⟨71168, by rfl⟩ : syracuseStep 379565 = 142337) (by norm_num)
theorem B379589 : Blo 251819 379589 := bbase (se 4 (by rfl) ⟨35586, by rfl⟩ : syracuseStep 379589 = 71173) (by norm_num)
theorem B379613 : Blo 251819 379613 := bbase (se 3 (by rfl) ⟨71177, by rfl⟩ : syracuseStep 379613 = 142355) (by norm_num)
theorem B379637 : Blo 251819 379637 := bbase (se 5 (by rfl) ⟨17795, by rfl⟩ : syracuseStep 379637 = 35591) (by norm_num)
theorem B379661 : Blo 251819 379661 := bbase (se 3 (by rfl) ⟨71186, by rfl⟩ : syracuseStep 379661 = 142373) (by norm_num)
theorem B379685 : Blo 251819 379685 := bbase (se 4 (by rfl) ⟨35595, by rfl⟩ : syracuseStep 379685 = 71191) (by norm_num)
theorem B969509 : Blo 251819 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B510781 : Blo 251819 510781 := bbase (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) (by norm_num)
theorem B379709 : Blo 251819 379709 := bbase (se 3 (by rfl) ⟨71195, by rfl⟩ : syracuseStep 379709 = 142391) (by norm_num)
theorem B379733 : Blo 251819 379733 := bbase (se 9 (by rfl) ⟨1112, by rfl⟩ : syracuseStep 379733 = 2225) (by norm_num)
theorem B379757 : Blo 251819 379757 := bbase (se 3 (by rfl) ⟨71204, by rfl⟩ : syracuseStep 379757 = 142409) (by norm_num)
theorem B379781 : Blo 251819 379781 := bbase (se 4 (by rfl) ⟨35604, by rfl⟩ : syracuseStep 379781 = 71209) (by norm_num)
theorem B379805 : Blo 251819 379805 := bbase (se 3 (by rfl) ⟨71213, by rfl⟩ : syracuseStep 379805 = 142427) (by norm_num)
theorem B641965 : Blo 251819 641965 := bbase (se 3 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 641965 = 240737) (by norm_num)
theorem B478133 : Blo 251819 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B379829 : Blo 251819 379829 := bbase (se 5 (by rfl) ⟨17804, by rfl⟩ : syracuseStep 379829 = 35609) (by norm_num)
theorem B379853 : Blo 251819 379853 := bbase (se 3 (by rfl) ⟨71222, by rfl⟩ : syracuseStep 379853 = 142445) (by norm_num)
theorem B543709 : Blo 251819 543709 := bbase (se 3 (by rfl) ⟨101945, by rfl⟩ : syracuseStep 543709 = 203891) (by norm_num)
theorem B379877 : Blo 251819 379877 := bbase (se 4 (by rfl) ⟨35613, by rfl⟩ : syracuseStep 379877 = 71227) (by norm_num)
theorem B379901 : Blo 251819 379901 := bbase (se 3 (by rfl) ⟨71231, by rfl⟩ : syracuseStep 379901 = 142463) (by norm_num)
theorem B379925 : Blo 251819 379925 := bbase (se 6 (by rfl) ⟨8904, by rfl⟩ : syracuseStep 379925 = 17809) (by norm_num)
theorem B642077 : Blo 251819 642077 := bbase (se 3 (by rfl) ⟨120389, by rfl⟩ : syracuseStep 642077 = 240779) (by norm_num)
theorem B379949 : Blo 251819 379949 := bbase (se 3 (by rfl) ⟨71240, by rfl⟩ : syracuseStep 379949 = 142481) (by norm_num)
theorem B379973 : Blo 251819 379973 := bbase (se 4 (by rfl) ⟨35622, by rfl⟩ : syracuseStep 379973 = 71245) (by norm_num)
theorem B543829 : Blo 251819 543829 := bbase (se 8 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 543829 = 6373) (by norm_num)
theorem B379997 : Blo 251819 379997 := bbase (se 3 (by rfl) ⟨71249, by rfl⟩ : syracuseStep 379997 = 142499) (by norm_num)
theorem B380021 : Blo 251819 380021 := bbase (se 5 (by rfl) ⟨17813, by rfl⟩ : syracuseStep 380021 = 35627) (by norm_num)
theorem B380045 : Blo 251819 380045 := bbase (se 3 (by rfl) ⟨71258, by rfl⟩ : syracuseStep 380045 = 142517) (by norm_num)
theorem B380069 : Blo 251819 380069 := bbase (se 4 (by rfl) ⟨35631, by rfl⟩ : syracuseStep 380069 = 71263) (by norm_num)
theorem B380093 : Blo 251819 380093 := bbase (se 3 (by rfl) ⟨71267, by rfl⟩ : syracuseStep 380093 = 142535) (by norm_num)
theorem B380117 : Blo 251819 380117 := bbase (se 7 (by rfl) ⟨4454, by rfl⟩ : syracuseStep 380117 = 8909) (by norm_num)
theorem B642269 : Blo 251819 642269 := bbase (se 3 (by rfl) ⟨120425, by rfl⟩ : syracuseStep 642269 = 240851) (by norm_num)
theorem B380141 : Blo 251819 380141 := bbase (se 3 (by rfl) ⟨71276, by rfl⟩ : syracuseStep 380141 = 142553) (by norm_num)
theorem B380165 : Blo 251819 380165 := bbase (se 4 (by rfl) ⟨35640, by rfl⟩ : syracuseStep 380165 = 71281) (by norm_num)
theorem B380189 : Blo 251819 380189 := bbase (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) (by norm_num)
theorem B380213 : Blo 251819 380213 := bbase (se 5 (by rfl) ⟨17822, by rfl⟩ : syracuseStep 380213 = 35645) (by norm_num)
theorem B380237 : Blo 251819 380237 := bbase (se 3 (by rfl) ⟨71294, by rfl⟩ : syracuseStep 380237 = 142589) (by norm_num)
theorem B544085 : Blo 251819 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B380261 : Blo 251819 380261 := bbase (se 4 (by rfl) ⟨35649, by rfl⟩ : syracuseStep 380261 = 71299) (by norm_num)
theorem B380285 : Blo 251819 380285 := bbase (se 3 (by rfl) ⟨71303, by rfl⟩ : syracuseStep 380285 = 142607) (by norm_num)
theorem B380309 : Blo 251819 380309 := bbase (se 6 (by rfl) ⟨8913, by rfl⟩ : syracuseStep 380309 = 17827) (by norm_num)
theorem B380333 : Blo 251819 380333 := bbase (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) (by norm_num)
theorem B380357 : Blo 251819 380357 := bbase (se 4 (by rfl) ⟨35658, by rfl⟩ : syracuseStep 380357 = 71317) (by norm_num)
theorem B380381 : Blo 251819 380381 := bbase (se 3 (by rfl) ⟨71321, by rfl⟩ : syracuseStep 380381 = 142643) (by norm_num)
theorem B380405 : Blo 251819 380405 := bbase (se 5 (by rfl) ⟨17831, by rfl⟩ : syracuseStep 380405 = 35663) (by norm_num)
theorem B609781 : Blo 251819 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B380429 : Blo 251819 380429 := bbase (se 3 (by rfl) ⟨71330, by rfl⟩ : syracuseStep 380429 = 142661) (by norm_num)
theorem B380453 : Blo 251819 380453 := bbase (se 4 (by rfl) ⟨35667, by rfl⟩ : syracuseStep 380453 = 71335) (by norm_num)
theorem B642613 : Blo 251819 642613 := bbase (se 5 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 642613 = 60245) (by norm_num)
theorem B380477 : Blo 251819 380477 := bbase (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) (by norm_num)
theorem B380501 : Blo 251819 380501 := bbase (se 8 (by rfl) ⟨2229, by rfl⟩ : syracuseStep 380501 = 4459) (by norm_num)
theorem B380525 : Blo 251819 380525 := bbase (se 3 (by rfl) ⟨71348, by rfl⟩ : syracuseStep 380525 = 142697) (by norm_num)
theorem B380549 : Blo 251819 380549 := bbase (se 4 (by rfl) ⟨35676, by rfl⟩ : syracuseStep 380549 = 71353) (by norm_num)
theorem B380573 : Blo 251819 380573 := bbase (se 3 (by rfl) ⟨71357, by rfl⟩ : syracuseStep 380573 = 142715) (by norm_num)
theorem B478885 : Blo 251819 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B642725 : Blo 251819 642725 := bbase (se 4 (by rfl) ⟨60255, by rfl⟩ : syracuseStep 642725 = 120511) (by norm_num)
theorem B380597 : Blo 251819 380597 := bbase (se 5 (by rfl) ⟨17840, by rfl⟩ : syracuseStep 380597 = 35681) (by norm_num)
theorem B380621 : Blo 251819 380621 := bbase (se 3 (by rfl) ⟨71366, by rfl⟩ : syracuseStep 380621 = 142733) (by norm_num)
theorem B380645 : Blo 251819 380645 := bbase (se 4 (by rfl) ⟨35685, by rfl⟩ : syracuseStep 380645 = 71371) (by norm_num)
theorem B380669 : Blo 251819 380669 := bbase (se 3 (by rfl) ⟨71375, by rfl⟩ : syracuseStep 380669 = 142751) (by norm_num)
theorem B380693 : Blo 251819 380693 := bbase (se 6 (by rfl) ⟨8922, by rfl⟩ : syracuseStep 380693 = 17845) (by norm_num)
theorem B380717 : Blo 251819 380717 := bbase (se 3 (by rfl) ⟨71384, by rfl⟩ : syracuseStep 380717 = 142769) (by norm_num)
theorem B479029 : Blo 251819 479029 := bbase (se 5 (by rfl) ⟨22454, by rfl⟩ : syracuseStep 479029 = 44909) (by norm_num)
theorem B380741 : Blo 251819 380741 := bbase (se 4 (by rfl) ⟨35694, by rfl⟩ : syracuseStep 380741 = 71389) (by norm_num)
theorem B380765 : Blo 251819 380765 := bbase (se 3 (by rfl) ⟨71393, by rfl⟩ : syracuseStep 380765 = 142787) (by norm_num)
theorem B642917 : Blo 251819 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B380789 : Blo 251819 380789 := bbase (se 5 (by rfl) ⟨17849, by rfl⟩ : syracuseStep 380789 = 35699) (by norm_num)
theorem B380813 : Blo 251819 380813 := bbase (se 3 (by rfl) ⟨71402, by rfl⟩ : syracuseStep 380813 = 142805) (by norm_num)
theorem B380837 : Blo 251819 380837 := bbase (se 4 (by rfl) ⟨35703, by rfl⟩ : syracuseStep 380837 = 71407) (by norm_num)
theorem B511933 : Blo 251819 511933 := bbase (se 3 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 511933 = 191975) (by norm_num)
theorem B380861 : Blo 251819 380861 := bbase (se 3 (by rfl) ⟨71411, by rfl⟩ : syracuseStep 380861 = 142823) (by norm_num)
theorem B479189 : Blo 251819 479189 := bbase (se 7 (by rfl) ⟨5615, by rfl⟩ : syracuseStep 479189 = 11231) (by norm_num)
theorem B380885 : Blo 251819 380885 := bbase (se 7 (by rfl) ⟨4463, by rfl⟩ : syracuseStep 380885 = 8927) (by norm_num)
theorem B380909 : Blo 251819 380909 := bbase (se 3 (by rfl) ⟨71420, by rfl⟩ : syracuseStep 380909 = 142841) (by norm_num)
theorem B380933 : Blo 251819 380933 := bbase (se 4 (by rfl) ⟨35712, by rfl⟩ : syracuseStep 380933 = 71425) (by norm_num)
theorem B380957 : Blo 251819 380957 := bbase (se 3 (by rfl) ⟨71429, by rfl⟩ : syracuseStep 380957 = 142859) (by norm_num)
theorem B380981 : Blo 251819 380981 := bbase (se 5 (by rfl) ⟨17858, by rfl⟩ : syracuseStep 380981 = 35717) (by norm_num)
theorem B381005 : Blo 251819 381005 := bbase (se 3 (by rfl) ⟨71438, by rfl⟩ : syracuseStep 381005 = 142877) (by norm_num)
theorem B479333 : Blo 251819 479333 := bbase (se 4 (by rfl) ⟨44937, by rfl⟩ : syracuseStep 479333 = 89875) (by norm_num)
theorem B381029 : Blo 251819 381029 := bbase (se 4 (by rfl) ⟨35721, by rfl⟩ : syracuseStep 381029 = 71443) (by norm_num)
theorem B381053 : Blo 251819 381053 := bbase (se 3 (by rfl) ⟨71447, by rfl⟩ : syracuseStep 381053 = 142895) (by norm_num)
theorem B381077 : Blo 251819 381077 := bbase (se 6 (by rfl) ⟨8931, by rfl⟩ : syracuseStep 381077 = 17863) (by norm_num)
theorem B2445461 : Blo 251819 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B381101 : Blo 251819 381101 := bbase (se 3 (by rfl) ⟨71456, by rfl⟩ : syracuseStep 381101 = 142913) (by norm_num)
theorem B643261 : Blo 251819 643261 := bbase (se 3 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 643261 = 241223) (by norm_num)
theorem B381125 : Blo 251819 381125 := bbase (se 4 (by rfl) ⟨35730, by rfl⟩ : syracuseStep 381125 = 71461) (by norm_num)
theorem B544973 : Blo 251819 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B381149 : Blo 251819 381149 := bbase (se 3 (by rfl) ⟨71465, by rfl⟩ : syracuseStep 381149 = 142931) (by norm_num)
theorem B381173 : Blo 251819 381173 := bbase (se 5 (by rfl) ⟨17867, by rfl⟩ : syracuseStep 381173 = 35735) (by norm_num)
theorem B381197 : Blo 251819 381197 := bbase (se 3 (by rfl) ⟨71474, by rfl⟩ : syracuseStep 381197 = 142949) (by norm_num)
theorem B381221 : Blo 251819 381221 := bbase (se 4 (by rfl) ⟨35739, by rfl⟩ : syracuseStep 381221 = 71479) (by norm_num)
theorem B643373 : Blo 251819 643373 := bbase (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) (by norm_num)
theorem B381245 : Blo 251819 381245 := bbase (se 3 (by rfl) ⟨71483, by rfl⟩ : syracuseStep 381245 = 142967) (by norm_num)
theorem B381269 : Blo 251819 381269 := bbase (se 10 (by rfl) ⟨558, by rfl⟩ : syracuseStep 381269 = 1117) (by norm_num)
theorem B381293 : Blo 251819 381293 := bbase (se 3 (by rfl) ⟨71492, by rfl⟩ : syracuseStep 381293 = 142985) (by norm_num)
theorem B479621 : Blo 251819 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B381317 : Blo 251819 381317 := bbase (se 4 (by rfl) ⟨35748, by rfl⟩ : syracuseStep 381317 = 71497) (by norm_num)
theorem B381341 : Blo 251819 381341 := bbase (se 3 (by rfl) ⟨71501, by rfl⟩ : syracuseStep 381341 = 143003) (by norm_num)
theorem B381365 : Blo 251819 381365 := bbase (se 5 (by rfl) ⟨17876, by rfl⟩ : syracuseStep 381365 = 35753) (by norm_num)
theorem B545213 : Blo 251819 545213 := bbase (se 3 (by rfl) ⟨102227, by rfl⟩ : syracuseStep 545213 = 204455) (by norm_num)
theorem B1036741 : Blo 251819 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B381389 : Blo 251819 381389 := bbase (se 3 (by rfl) ⟨71510, by rfl⟩ : syracuseStep 381389 = 143021) (by norm_num)
theorem B381413 : Blo 251819 381413 := bbase (se 4 (by rfl) ⟨35757, by rfl⟩ : syracuseStep 381413 = 71515) (by norm_num)
theorem B643565 : Blo 251819 643565 := bbase (se 3 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 643565 = 241337) (by norm_num)
theorem B807413 : Blo 251819 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B381437 : Blo 251819 381437 := bbase (se 3 (by rfl) ⟨71519, by rfl⟩ : syracuseStep 381437 = 143039) (by norm_num)
theorem B1364501 : Blo 251819 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B381461 : Blo 251819 381461 := bbase (se 6 (by rfl) ⟨8940, by rfl⟩ : syracuseStep 381461 = 17881) (by norm_num)
theorem B479773 : Blo 251819 479773 := bbase (se 3 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 479773 = 179915) (by norm_num)
theorem B381485 : Blo 251819 381485 := bbase (se 3 (by rfl) ⟨71528, by rfl⟩ : syracuseStep 381485 = 143057) (by norm_num)
theorem B1561141 : Blo 251819 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B381509 : Blo 251819 381509 := bbase (se 4 (by rfl) ⟨35766, by rfl⟩ : syracuseStep 381509 = 71533) (by norm_num)
theorem B381533 : Blo 251819 381533 := bbase (se 3 (by rfl) ⟨71537, by rfl⟩ : syracuseStep 381533 = 143075) (by norm_num)
theorem B971365 : Blo 251819 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B381557 : Blo 251819 381557 := bbase (se 5 (by rfl) ⟨17885, by rfl⟩ : syracuseStep 381557 = 35771) (by norm_num)
theorem B381581 : Blo 251819 381581 := bbase (se 3 (by rfl) ⟨71546, by rfl⟩ : syracuseStep 381581 = 143093) (by norm_num)
theorem B283297 : Blo 251819 283297 := bbase (se 2 (by rfl) ⟨106236, by rfl⟩ : syracuseStep 283297 = 212473) (by norm_num)
theorem B381605 : Blo 251819 381605 := bbase (se 4 (by rfl) ⟨35775, by rfl⟩ : syracuseStep 381605 = 71551) (by norm_num)
theorem B381629 : Blo 251819 381629 := bbase (se 3 (by rfl) ⟨71555, by rfl⟩ : syracuseStep 381629 = 143111) (by norm_num)
theorem B283333 : Blo 251819 283333 := bbase (se 4 (by rfl) ⟨26562, by rfl⟩ : syracuseStep 283333 = 53125) (by norm_num)
theorem B840389 : Blo 251819 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B381653 : Blo 251819 381653 := bbase (se 7 (by rfl) ⟨4472, by rfl⟩ : syracuseStep 381653 = 8945) (by norm_num)
theorem B283369 : Blo 251819 283369 := bbase (se 2 (by rfl) ⟨106263, by rfl⟩ : syracuseStep 283369 = 212527) (by norm_num)
theorem B381677 : Blo 251819 381677 := bbase (se 3 (by rfl) ⟨71564, by rfl⟩ : syracuseStep 381677 = 143129) (by norm_num)
theorem B381701 : Blo 251819 381701 := bbase (se 4 (by rfl) ⟨35784, by rfl⟩ : syracuseStep 381701 = 71569) (by norm_num)
theorem B283405 : Blo 251819 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B381725 : Blo 251819 381725 := bbase (se 3 (by rfl) ⟨71573, by rfl⟩ : syracuseStep 381725 = 143147) (by norm_num)
theorem B283441 : Blo 251819 283441 := bbase (se 2 (by rfl) ⟨106290, by rfl⟩ : syracuseStep 283441 = 212581) (by norm_num)
theorem B381749 : Blo 251819 381749 := bbase (se 5 (by rfl) ⟨17894, by rfl⟩ : syracuseStep 381749 = 35789) (by norm_num)
theorem B643909 : Blo 251819 643909 := bbase (se 4 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 643909 = 120733) (by norm_num)
theorem B480077 : Blo 251819 480077 := bbase (se 3 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 480077 = 180029) (by norm_num)
theorem B381773 : Blo 251819 381773 := bbase (se 3 (by rfl) ⟨71582, by rfl⟩ : syracuseStep 381773 = 143165) (by norm_num)
theorem B283477 : Blo 251819 283477 := bbase (se 9 (by rfl) ⟨830, by rfl⟩ : syracuseStep 283477 = 1661) (by norm_num)
theorem B611165 : Blo 251819 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B611173 : Blo 251819 611173 := bbase (se 4 (by rfl) ⟨57297, by rfl⟩ : syracuseStep 611173 = 114595) (by norm_num)
theorem B381797 : Blo 251819 381797 := bbase (se 4 (by rfl) ⟨35793, by rfl⟩ : syracuseStep 381797 = 71587) (by norm_num)
theorem B283513 : Blo 251819 283513 := bbase (se 2 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 283513 = 212635) (by norm_num)
theorem B381821 : Blo 251819 381821 := bbase (se 3 (by rfl) ⟨71591, by rfl⟩ : syracuseStep 381821 = 143183) (by norm_num)
theorem B381845 : Blo 251819 381845 := bbase (se 6 (by rfl) ⟨8949, by rfl⟩ : syracuseStep 381845 = 17899) (by norm_num)
theorem B283549 : Blo 251819 283549 := bbase (se 3 (by rfl) ⟨53165, by rfl⟩ : syracuseStep 283549 = 106331) (by norm_num)
theorem B381869 : Blo 251819 381869 := bbase (se 3 (by rfl) ⟨71600, by rfl⟩ : syracuseStep 381869 = 143201) (by norm_num)
theorem B644021 : Blo 251819 644021 := bbase (se 5 (by rfl) ⟨30188, by rfl⟩ : syracuseStep 644021 = 60377) (by norm_num)
theorem B545717 : Blo 251819 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B545725 : Blo 251819 545725 := bbase (se 3 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 545725 = 204647) (by norm_num)
theorem B283585 : Blo 251819 283585 := bbase (se 2 (by rfl) ⟨106344, by rfl⟩ : syracuseStep 283585 = 212689) (by norm_num)
theorem B381893 : Blo 251819 381893 := bbase (se 4 (by rfl) ⟨35802, by rfl⟩ : syracuseStep 381893 = 71605) (by norm_num)
theorem B381917 : Blo 251819 381917 := bbase (se 3 (by rfl) ⟨71609, by rfl⟩ : syracuseStep 381917 = 143219) (by norm_num)
theorem B283621 : Blo 251819 283621 := bbase (se 4 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 283621 = 53179) (by norm_num)
theorem B381941 : Blo 251819 381941 := bbase (se 5 (by rfl) ⟨17903, by rfl⟩ : syracuseStep 381941 = 35807) (by norm_num)
theorem B283657 : Blo 251819 283657 := bbase (se 2 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 283657 = 212743) (by norm_num)
theorem B381965 : Blo 251819 381965 := bbase (se 3 (by rfl) ⟨71618, by rfl⟩ : syracuseStep 381965 = 143237) (by norm_num)
theorem B381989 : Blo 251819 381989 := bbase (se 4 (by rfl) ⟨35811, by rfl⟩ : syracuseStep 381989 = 71623) (by norm_num)
theorem B283693 : Blo 251819 283693 := bbase (se 3 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 283693 = 106385) (by norm_num)
theorem B382013 : Blo 251819 382013 := bbase (se 3 (by rfl) ⟨71627, by rfl⟩ : syracuseStep 382013 = 143255) (by norm_num)
theorem B283729 : Blo 251819 283729 := bbase (se 2 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 283729 = 212797) (by norm_num)
theorem B382037 : Blo 251819 382037 := bbase (se 8 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 382037 = 4477) (by norm_num)
theorem B578669 : Blo 251819 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B382061 : Blo 251819 382061 := bbase (se 3 (by rfl) ⟨71636, by rfl⟩ : syracuseStep 382061 = 143273) (by norm_num)
theorem B283765 : Blo 251819 283765 := bbase (se 5 (by rfl) ⟨13301, by rfl⟩ : syracuseStep 283765 = 26603) (by norm_num)
theorem B644213 : Blo 251819 644213 := bbase (se 5 (by rfl) ⟨30197, by rfl⟩ : syracuseStep 644213 = 60395) (by norm_num)
theorem B382085 : Blo 251819 382085 := bbase (se 4 (by rfl) ⟨35820, by rfl⟩ : syracuseStep 382085 = 71641) (by norm_num)
theorem B283801 : Blo 251819 283801 := bbase (se 2 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 283801 = 212851) (by norm_num)
theorem B382109 : Blo 251819 382109 := bbase (se 3 (by rfl) ⟨71645, by rfl⟩ : syracuseStep 382109 = 143291) (by norm_num)
theorem B382133 : Blo 251819 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B283837 : Blo 251819 283837 := bbase (se 3 (by rfl) ⟨53219, by rfl⟩ : syracuseStep 283837 = 106439) (by norm_num)
theorem B382157 : Blo 251819 382157 := bbase (se 3 (by rfl) ⟨71654, by rfl⟩ : syracuseStep 382157 = 143309) (by norm_num)
theorem B513245 : Blo 251819 513245 := bbase (se 3 (by rfl) ⟨96233, by rfl⟩ : syracuseStep 513245 = 192467) (by norm_num)
theorem B283873 : Blo 251819 283873 := bbase (se 2 (by rfl) ⟨106452, by rfl⟩ : syracuseStep 283873 = 212905) (by norm_num)
theorem B382181 : Blo 251819 382181 := bbase (se 4 (by rfl) ⟨35829, by rfl⟩ : syracuseStep 382181 = 71659) (by norm_num)
theorem B382205 : Blo 251819 382205 := bbase (se 3 (by rfl) ⟨71663, by rfl⟩ : syracuseStep 382205 = 143327) (by norm_num)
theorem B283909 : Blo 251819 283909 := bbase (se 4 (by rfl) ⟨26616, by rfl⟩ : syracuseStep 283909 = 53233) (by norm_num)
theorem B382229 : Blo 251819 382229 := bbase (se 6 (by rfl) ⟨8958, by rfl⟩ : syracuseStep 382229 = 17917) (by norm_num)
theorem B283945 : Blo 251819 283945 := bbase (se 2 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 283945 = 212959) (by norm_num)
theorem B382253 : Blo 251819 382253 := bbase (se 3 (by rfl) ⟨71672, by rfl⟩ : syracuseStep 382253 = 143345) (by norm_num)
theorem B382277 : Blo 251819 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B283981 : Blo 251819 283981 := bbase (se 3 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 283981 = 106493) (by norm_num)
theorem B382301 : Blo 251819 382301 := bbase (se 3 (by rfl) ⟨71681, by rfl⟩ : syracuseStep 382301 = 143363) (by norm_num)
theorem B284017 : Blo 251819 284017 := bbase (se 2 (by rfl) ⟨106506, by rfl⟩ : syracuseStep 284017 = 213013) (by norm_num)
theorem B382325 : Blo 251819 382325 := bbase (se 5 (by rfl) ⟨17921, by rfl⟩ : syracuseStep 382325 = 35843) (by norm_num)
theorem B808325 : Blo 251819 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B382349 : Blo 251819 382349 := bbase (se 3 (by rfl) ⟨71690, by rfl⟩ : syracuseStep 382349 = 143381) (by norm_num)
theorem B284053 : Blo 251819 284053 := bbase (se 6 (by rfl) ⟨6657, by rfl⟩ : syracuseStep 284053 = 13315) (by norm_num)
theorem B382373 : Blo 251819 382373 := bbase (se 4 (by rfl) ⟨35847, by rfl⟩ : syracuseStep 382373 = 71695) (by norm_num)
theorem B284089 : Blo 251819 284089 := bbase (se 2 (by rfl) ⟨106533, by rfl⟩ : syracuseStep 284089 = 213067) (by norm_num)
theorem B382397 : Blo 251819 382397 := bbase (se 3 (by rfl) ⟨71699, by rfl⟩ : syracuseStep 382397 = 143399) (by norm_num)
theorem B644557 : Blo 251819 644557 := bbase (se 3 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 644557 = 241709) (by norm_num)
theorem B382421 : Blo 251819 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B284125 : Blo 251819 284125 := bbase (se 3 (by rfl) ⟨53273, by rfl⟩ : syracuseStep 284125 = 106547) (by norm_num)
theorem B382445 : Blo 251819 382445 := bbase (se 3 (by rfl) ⟨71708, by rfl⟩ : syracuseStep 382445 = 143417) (by norm_num)
theorem B284161 : Blo 251819 284161 := bbase (se 2 (by rfl) ⟨106560, by rfl⟩ : syracuseStep 284161 = 213121) (by norm_num)
theorem B382469 : Blo 251819 382469 := bbase (se 4 (by rfl) ⟨35856, by rfl⟩ : syracuseStep 382469 = 71713) (by norm_num)
theorem B382493 : Blo 251819 382493 := bbase (se 3 (by rfl) ⟨71717, by rfl⟩ : syracuseStep 382493 = 143435) (by norm_num)
theorem B284197 : Blo 251819 284197 := bbase (se 4 (by rfl) ⟨26643, by rfl⟩ : syracuseStep 284197 = 53287) (by norm_num)
theorem B382517 : Blo 251819 382517 := bbase (se 5 (by rfl) ⟨17930, by rfl⟩ : syracuseStep 382517 = 35861) (by norm_num)
theorem B874037 : Blo 251819 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B480829 : Blo 251819 480829 := bbase (se 3 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 480829 = 180311) (by norm_num)
theorem B644669 : Blo 251819 644669 := bbase (se 3 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 644669 = 241751) (by norm_num)
theorem B284233 : Blo 251819 284233 := bbase (se 2 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 284233 = 213175) (by norm_num)
theorem B382541 : Blo 251819 382541 := bbase (se 3 (by rfl) ⟨71726, by rfl⟩ : syracuseStep 382541 = 143453) (by norm_num)
theorem B382565 : Blo 251819 382565 := bbase (se 4 (by rfl) ⟨35865, by rfl⟩ : syracuseStep 382565 = 71731) (by norm_num)
theorem B284269 : Blo 251819 284269 := bbase (se 3 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 284269 = 106601) (by norm_num)
theorem B382589 : Blo 251819 382589 := bbase (se 3 (by rfl) ⟨71735, by rfl⟩ : syracuseStep 382589 = 143471) (by norm_num)
theorem B284305 : Blo 251819 284305 := bbase (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) (by norm_num)
theorem B382613 : Blo 251819 382613 := bbase (se 6 (by rfl) ⟨8967, by rfl⟩ : syracuseStep 382613 = 17935) (by norm_num)
theorem B382637 : Blo 251819 382637 := bbase (se 3 (by rfl) ⟨71744, by rfl⟩ : syracuseStep 382637 = 143489) (by norm_num)
theorem B284341 : Blo 251819 284341 := bbase (se 5 (by rfl) ⟨13328, by rfl⟩ : syracuseStep 284341 = 26657) (by norm_num)
theorem B382661 : Blo 251819 382661 := bbase (se 4 (by rfl) ⟨35874, by rfl⟩ : syracuseStep 382661 = 71749) (by norm_num)
theorem B480973 : Blo 251819 480973 := bbase (se 3 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 480973 = 180365) (by norm_num)
theorem B284377 : Blo 251819 284377 := bbase (se 2 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 284377 = 213283) (by norm_num)
theorem B382685 : Blo 251819 382685 := bbase (se 3 (by rfl) ⟨71753, by rfl⟩ : syracuseStep 382685 = 143507) (by norm_num)
theorem B382709 : Blo 251819 382709 := bbase (se 5 (by rfl) ⟨17939, by rfl⟩ : syracuseStep 382709 = 35879) (by norm_num)
theorem B284413 : Blo 251819 284413 := bbase (se 3 (by rfl) ⟨53327, by rfl⟩ : syracuseStep 284413 = 106655) (by norm_num)
theorem B644861 : Blo 251819 644861 := bbase (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) (by norm_num)
theorem B382733 : Blo 251819 382733 := bbase (se 3 (by rfl) ⟨71762, by rfl⟩ : syracuseStep 382733 = 143525) (by norm_num)
theorem B284449 : Blo 251819 284449 := bbase (se 2 (by rfl) ⟨106668, by rfl⟩ : syracuseStep 284449 = 213337) (by norm_num)
theorem B382757 : Blo 251819 382757 := bbase (se 4 (by rfl) ⟨35883, by rfl⟩ : syracuseStep 382757 = 71767) (by norm_num)
theorem B382781 : Blo 251819 382781 := bbase (se 3 (by rfl) ⟨71771, by rfl⟩ : syracuseStep 382781 = 143543) (by norm_num)
theorem B284485 : Blo 251819 284485 := bbase (se 4 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 284485 = 53341) (by norm_num)
theorem B612173 : Blo 251819 612173 := bbase (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) (by norm_num)
theorem B382805 : Blo 251819 382805 := bbase (se 9 (by rfl) ⟨1121, by rfl⟩ : syracuseStep 382805 = 2243) (by norm_num)
theorem B284521 : Blo 251819 284521 := bbase (se 2 (by rfl) ⟨106695, by rfl⟩ : syracuseStep 284521 = 213391) (by norm_num)
theorem B481133 : Blo 251819 481133 := bbase (se 3 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 481133 = 180425) (by norm_num)
theorem B382829 : Blo 251819 382829 := bbase (se 3 (by rfl) ⟨71780, by rfl⟩ : syracuseStep 382829 = 143561) (by norm_num)
theorem B382853 : Blo 251819 382853 := bbase (se 4 (by rfl) ⟨35892, by rfl⟩ : syracuseStep 382853 = 71785) (by norm_num)
theorem B284557 : Blo 251819 284557 := bbase (se 3 (by rfl) ⟨53354, by rfl⟩ : syracuseStep 284557 = 106709) (by norm_num)
theorem B382877 : Blo 251819 382877 := bbase (se 3 (by rfl) ⟨71789, by rfl⟩ : syracuseStep 382877 = 143579) (by norm_num)
theorem B284593 : Blo 251819 284593 := bbase (se 2 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 284593 = 213445) (by norm_num)
theorem B382901 : Blo 251819 382901 := bbase (se 5 (by rfl) ⟨17948, by rfl⟩ : syracuseStep 382901 = 35897) (by norm_num)
theorem B382925 : Blo 251819 382925 := bbase (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) (by norm_num)
theorem B284629 : Blo 251819 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B382949 : Blo 251819 382949 := bbase (se 4 (by rfl) ⟨35901, by rfl⟩ : syracuseStep 382949 = 71803) (by norm_num)
theorem B284665 : Blo 251819 284665 := bbase (se 2 (by rfl) ⟨106749, by rfl⟩ : syracuseStep 284665 = 213499) (by norm_num)
theorem B481277 : Blo 251819 481277 := bbase (se 3 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 481277 = 180479) (by norm_num)
theorem B382973 : Blo 251819 382973 := bbase (se 3 (by rfl) ⟨71807, by rfl⟩ : syracuseStep 382973 = 143615) (by norm_num)
theorem B382997 : Blo 251819 382997 := bbase (se 6 (by rfl) ⟨8976, by rfl⟩ : syracuseStep 382997 = 17953) (by norm_num)
theorem B284701 : Blo 251819 284701 := bbase (se 3 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 284701 = 106763) (by norm_num)
theorem B383021 : Blo 251819 383021 := bbase (se 3 (by rfl) ⟨71816, by rfl⟩ : syracuseStep 383021 = 143633) (by norm_num)
theorem B284737 : Blo 251819 284737 := bbase (se 2 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 284737 = 213553) (by norm_num)
theorem B383045 : Blo 251819 383045 := bbase (se 4 (by rfl) ⟨35910, by rfl⟩ : syracuseStep 383045 = 71821) (by norm_num)
theorem B645205 : Blo 251819 645205 := bbase (se 8 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 645205 = 7561) (by norm_num)
theorem B383069 : Blo 251819 383069 := bbase (se 3 (by rfl) ⟨71825, by rfl⟩ : syracuseStep 383069 = 143651) (by norm_num)
theorem B284773 : Blo 251819 284773 := bbase (se 4 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 284773 = 53395) (by norm_num)
theorem B383093 : Blo 251819 383093 := bbase (se 5 (by rfl) ⟨17957, by rfl⟩ : syracuseStep 383093 = 35915) (by norm_num)
theorem B284809 : Blo 251819 284809 := bbase (se 2 (by rfl) ⟨106803, by rfl⟩ : syracuseStep 284809 = 213607) (by norm_num)
theorem B383117 : Blo 251819 383117 := bbase (se 3 (by rfl) ⟨71834, by rfl⟩ : syracuseStep 383117 = 143669) (by norm_num)
theorem B383141 : Blo 251819 383141 := bbase (se 4 (by rfl) ⟨35919, by rfl⟩ : syracuseStep 383141 = 71839) (by norm_num)
theorem B284845 : Blo 251819 284845 := bbase (se 3 (by rfl) ⟨53408, by rfl⟩ : syracuseStep 284845 = 106817) (by norm_num)
theorem B383165 : Blo 251819 383165 := bbase (se 3 (by rfl) ⟨71843, by rfl⟩ : syracuseStep 383165 = 143687) (by norm_num)
theorem B645317 : Blo 251819 645317 := bbase (se 4 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 645317 = 120997) (by norm_num)
theorem B284881 : Blo 251819 284881 := bbase (se 2 (by rfl) ⟨106830, by rfl⟩ : syracuseStep 284881 = 213661) (by norm_num)
theorem B1300693 : Blo 251819 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B383189 : Blo 251819 383189 := bbase (se 7 (by rfl) ⟨4490, by rfl⟩ : syracuseStep 383189 = 8981) (by norm_num)
theorem B383213 : Blo 251819 383213 := bbase (se 3 (by rfl) ⟨71852, by rfl⟩ : syracuseStep 383213 = 143705) (by norm_num)
theorem B284917 : Blo 251819 284917 := bbase (se 5 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 284917 = 26711) (by norm_num)
theorem B383237 : Blo 251819 383237 := bbase (se 4 (by rfl) ⟨35928, by rfl⟩ : syracuseStep 383237 = 71857) (by norm_num)
theorem B284953 : Blo 251819 284953 := bbase (se 2 (by rfl) ⟨106857, by rfl⟩ : syracuseStep 284953 = 213715) (by norm_num)
theorem B481565 : Blo 251819 481565 := bbase (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) (by norm_num)
theorem B383261 : Blo 251819 383261 := bbase (se 3 (by rfl) ⟨71861, by rfl⟩ : syracuseStep 383261 = 143723) (by norm_num)
theorem B383285 : Blo 251819 383285 := bbase (se 5 (by rfl) ⟨17966, by rfl⟩ : syracuseStep 383285 = 35933) (by norm_num)
theorem B284989 : Blo 251819 284989 := bbase (se 3 (by rfl) ⟨53435, by rfl⟩ : syracuseStep 284989 = 106871) (by norm_num)
theorem B383309 : Blo 251819 383309 := bbase (se 3 (by rfl) ⟨71870, by rfl⟩ : syracuseStep 383309 = 143741) (by norm_num)
theorem B285025 : Blo 251819 285025 := bbase (se 2 (by rfl) ⟨106884, by rfl⟩ : syracuseStep 285025 = 213769) (by norm_num)
theorem B383333 : Blo 251819 383333 := bbase (se 4 (by rfl) ⟨35937, by rfl⟩ : syracuseStep 383333 = 71875) (by norm_num)
theorem B383357 : Blo 251819 383357 := bbase (se 3 (by rfl) ⟨71879, by rfl⟩ : syracuseStep 383357 = 143759) (by norm_num)
theorem B285061 : Blo 251819 285061 := bbase (se 4 (by rfl) ⟨26724, by rfl⟩ : syracuseStep 285061 = 53449) (by norm_num)
theorem B645509 : Blo 251819 645509 := bbase (se 4 (by rfl) ⟨60516, by rfl⟩ : syracuseStep 645509 = 121033) (by norm_num)
theorem B383381 : Blo 251819 383381 := bbase (se 6 (by rfl) ⟨8985, by rfl⟩ : syracuseStep 383381 = 17971) (by norm_num)
theorem B285097 : Blo 251819 285097 := bbase (se 2 (by rfl) ⟨106911, by rfl⟩ : syracuseStep 285097 = 213823) (by norm_num)
theorem B383405 : Blo 251819 383405 := bbase (se 3 (by rfl) ⟨71888, by rfl⟩ : syracuseStep 383405 = 143777) (by norm_num)
theorem B481717 : Blo 251819 481717 := bbase (se 5 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 481717 = 45161) (by norm_num)
theorem B383429 : Blo 251819 383429 := bbase (se 4 (by rfl) ⟨35946, by rfl⟩ : syracuseStep 383429 = 71893) (by norm_num)
theorem B285133 : Blo 251819 285133 := bbase (se 3 (by rfl) ⟨53462, by rfl⟩ : syracuseStep 285133 = 106925) (by norm_num)
theorem B383453 : Blo 251819 383453 := bbase (se 3 (by rfl) ⟨71897, by rfl⟩ : syracuseStep 383453 = 143795) (by norm_num)
theorem B285169 : Blo 251819 285169 := bbase (se 2 (by rfl) ⟨106938, by rfl⟩ : syracuseStep 285169 = 213877) (by norm_num)
theorem B383477 : Blo 251819 383477 := bbase (se 5 (by rfl) ⟨17975, by rfl⟩ : syracuseStep 383477 = 35951) (by norm_num)
theorem B383501 : Blo 251819 383501 := bbase (se 3 (by rfl) ⟨71906, by rfl⟩ : syracuseStep 383501 = 143813) (by norm_num)
theorem B285205 : Blo 251819 285205 := bbase (se 6 (by rfl) ⟨6684, by rfl⟩ : syracuseStep 285205 = 13369) (by norm_num)
theorem B383525 : Blo 251819 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B285241 : Blo 251819 285241 := bbase (se 2 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 285241 = 213931) (by norm_num)
theorem B383549 : Blo 251819 383549 := bbase (se 3 (by rfl) ⟨71915, by rfl⟩ : syracuseStep 383549 = 143831) (by norm_num)
theorem B612941 : Blo 251819 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B383573 : Blo 251819 383573 := bbase (se 8 (by rfl) ⟨2247, by rfl⟩ : syracuseStep 383573 = 4495) (by norm_num)
theorem B285277 : Blo 251819 285277 := bbase (se 3 (by rfl) ⟨53489, by rfl⟩ : syracuseStep 285277 = 106979) (by norm_num)
theorem B383597 : Blo 251819 383597 := bbase (se 3 (by rfl) ⟨71924, by rfl⟩ : syracuseStep 383597 = 143849) (by norm_num)
theorem B285313 : Blo 251819 285313 := bbase (se 2 (by rfl) ⟨106992, by rfl⟩ : syracuseStep 285313 = 213985) (by norm_num)
theorem B383621 : Blo 251819 383621 := bbase (se 4 (by rfl) ⟨35964, by rfl⟩ : syracuseStep 383621 = 71929) (by norm_num)
theorem B383645 : Blo 251819 383645 := bbase (se 3 (by rfl) ⟨71933, by rfl⟩ : syracuseStep 383645 = 143867) (by norm_num)
theorem B285349 : Blo 251819 285349 := bbase (se 4 (by rfl) ⟨26751, by rfl⟩ : syracuseStep 285349 = 53503) (by norm_num)
theorem B383669 : Blo 251819 383669 := bbase (se 5 (by rfl) ⟨17984, by rfl⟩ : syracuseStep 383669 = 35969) (by norm_num)
theorem B809669 : Blo 251819 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B285385 : Blo 251819 285385 := bbase (se 2 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 285385 = 214039) (by norm_num)
theorem B383693 : Blo 251819 383693 := bbase (se 3 (by rfl) ⟨71942, by rfl⟩ : syracuseStep 383693 = 143885) (by norm_num)
theorem B645853 : Blo 251819 645853 := bbase (se 3 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 645853 = 242195) (by norm_num)
theorem B482021 : Blo 251819 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B383717 : Blo 251819 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B285421 : Blo 251819 285421 := bbase (se 3 (by rfl) ⟨53516, by rfl⟩ : syracuseStep 285421 = 107033) (by norm_num)
theorem B514829 : Blo 251819 514829 := bbase (se 3 (by rfl) ⟨96530, by rfl⟩ : syracuseStep 514829 = 193061) (by norm_num)
theorem B285457 : Blo 251819 285457 := bbase (se 2 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 285457 = 214093) (by norm_num)
theorem B285493 : Blo 251819 285493 := bbase (se 5 (by rfl) ⟨13382, by rfl⟩ : syracuseStep 285493 = 26765) (by norm_num)
theorem B645965 : Blo 251819 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B285529 : Blo 251819 285529 := bbase (se 2 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 285529 = 214147) (by norm_num)
theorem B285565 : Blo 251819 285565 := bbase (se 3 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 285565 = 107087) (by norm_num)
theorem B285601 : Blo 251819 285601 := bbase (se 2 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 285601 = 214201) (by norm_num)
theorem B285637 : Blo 251819 285637 := bbase (se 4 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 285637 = 53557) (by norm_num)
theorem B285673 : Blo 251819 285673 := bbase (se 2 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 285673 = 214255) (by norm_num)
theorem B777205 : Blo 251819 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B285709 : Blo 251819 285709 := bbase (se 3 (by rfl) ⟨53570, by rfl⟩ : syracuseStep 285709 = 107141) (by norm_num)
theorem B646157 : Blo 251819 646157 := bbase (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) (by norm_num)
theorem B285745 : Blo 251819 285745 := bbase (se 2 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 285745 = 214309) (by norm_num)
theorem B777269 : Blo 251819 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B285781 : Blo 251819 285781 := bbase (se 8 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 285781 = 3349) (by norm_num)
theorem B285817 : Blo 251819 285817 := bbase (se 2 (by rfl) ⟨107181, by rfl⟩ : syracuseStep 285817 = 214363) (by norm_num)
theorem B285853 : Blo 251819 285853 := bbase (se 3 (by rfl) ⟨53597, by rfl⟩ : syracuseStep 285853 = 107195) (by norm_num)
theorem B285889 : Blo 251819 285889 := bbase (se 2 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 285889 = 214417) (by norm_num)
theorem B285925 : Blo 251819 285925 := bbase (se 4 (by rfl) ⟨26805, by rfl⟩ : syracuseStep 285925 = 53611) (by norm_num)
theorem B285961 : Blo 251819 285961 := bbase (se 2 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 285961 = 214471) (by norm_num)
theorem B318745 : Blo 251819 318745 := bbase (se 2 (by rfl) ⟨119529, by rfl⟩ : syracuseStep 318745 = 239059) (by norm_num)
theorem B285997 : Blo 251819 285997 := bbase (se 3 (by rfl) ⟨53624, by rfl⟩ : syracuseStep 285997 = 107249) (by norm_num)
theorem B286033 : Blo 251819 286033 := bbase (se 2 (by rfl) ⟨107262, by rfl⟩ : syracuseStep 286033 = 214525) (by norm_num)
theorem B646501 : Blo 251819 646501 := bbase (se 4 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 646501 = 121219) (by norm_num)
theorem B286069 : Blo 251819 286069 := bbase (se 5 (by rfl) ⟨13409, by rfl⟩ : syracuseStep 286069 = 26819) (by norm_num)
theorem B286105 : Blo 251819 286105 := bbase (se 2 (by rfl) ⟨107289, by rfl⟩ : syracuseStep 286105 = 214579) (by norm_num)
theorem B286141 : Blo 251819 286141 := bbase (se 3 (by rfl) ⟨53651, by rfl⟩ : syracuseStep 286141 = 107303) (by norm_num)
theorem B318917 : Blo 251819 318917 := bbase (se 4 (by rfl) ⟨29898, by rfl⟩ : syracuseStep 318917 = 59797) (by norm_num)
theorem B482773 : Blo 251819 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B646613 : Blo 251819 646613 := bbase (se 7 (by rfl) ⟨7577, by rfl⟩ : syracuseStep 646613 = 15155) (by norm_num)
theorem B286177 : Blo 251819 286177 := bbase (se 2 (by rfl) ⟨107316, by rfl⟩ : syracuseStep 286177 = 214633) (by norm_num)
theorem B777701 : Blo 251819 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B318973 : Blo 251819 318973 := bbase (se 3 (by rfl) ⟨59807, by rfl⟩ : syracuseStep 318973 = 119615) (by norm_num)
theorem B286213 : Blo 251819 286213 := bbase (se 4 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 286213 = 53665) (by norm_num)
theorem B286249 : Blo 251819 286249 := bbase (se 2 (by rfl) ⟨107343, by rfl⟩ : syracuseStep 286249 = 214687) (by norm_num)
theorem B286285 : Blo 251819 286285 := bbase (se 3 (by rfl) ⟨53678, by rfl⟩ : syracuseStep 286285 = 107357) (by norm_num)
theorem B319069 : Blo 251819 319069 := bbase (se 3 (by rfl) ⟨59825, by rfl⟩ : syracuseStep 319069 = 119651) (by norm_num)
theorem B482917 : Blo 251819 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B286321 : Blo 251819 286321 := bbase (se 2 (by rfl) ⟨107370, by rfl⟩ : syracuseStep 286321 = 214741) (by norm_num)
theorem B286357 : Blo 251819 286357 := bbase (se 6 (by rfl) ⟨6711, by rfl⟩ : syracuseStep 286357 = 13423) (by norm_num)
theorem B646805 : Blo 251819 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B286393 : Blo 251819 286393 := bbase (se 2 (by rfl) ⟨107397, by rfl⟩ : syracuseStep 286393 = 214795) (by norm_num)
theorem B286429 : Blo 251819 286429 := bbase (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) (by norm_num)
theorem B286465 : Blo 251819 286465 := bbase (se 2 (by rfl) ⟨107424, by rfl⟩ : syracuseStep 286465 = 214849) (by norm_num)
theorem B483077 : Blo 251819 483077 := bbase (se 4 (by rfl) ⟨45288, by rfl⟩ : syracuseStep 483077 = 90577) (by norm_num)
theorem B319241 : Blo 251819 319241 := bbase (se 2 (by rfl) ⟨119715, by rfl⟩ : syracuseStep 319241 = 239431) (by norm_num)
theorem B286501 : Blo 251819 286501 := bbase (se 4 (by rfl) ⟨26859, by rfl⟩ : syracuseStep 286501 = 53719) (by norm_num)
theorem B548669 : Blo 251819 548669 := bbase (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) (by norm_num)
theorem B319297 : Blo 251819 319297 := bbase (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) (by norm_num)
theorem B286537 : Blo 251819 286537 := bbase (se 2 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 286537 = 214903) (by norm_num)
theorem B286573 : Blo 251819 286573 := bbase (se 3 (by rfl) ⟨53732, by rfl⟩ : syracuseStep 286573 = 107465) (by norm_num)
theorem B286609 : Blo 251819 286609 := bbase (se 2 (by rfl) ⟨107478, by rfl⟩ : syracuseStep 286609 = 214957) (by norm_num)
theorem B483221 : Blo 251819 483221 := bbase (se 6 (by rfl) ⟨11325, by rfl⟩ : syracuseStep 483221 = 22651) (by norm_num)
theorem B581525 : Blo 251819 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B319393 : Blo 251819 319393 := bbase (se 2 (by rfl) ⟨119772, by rfl⟩ : syracuseStep 319393 = 239545) (by norm_num)
theorem B1925045 : Blo 251819 1925045 := bbase (se 5 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 1925045 = 180473) (by norm_num)
theorem B286645 : Blo 251819 286645 := bbase (se 5 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 286645 = 26873) (by norm_num)
theorem B286681 : Blo 251819 286681 := bbase (se 2 (by rfl) ⟨107505, by rfl⟩ : syracuseStep 286681 = 215011) (by norm_num)
theorem B647149 : Blo 251819 647149 := bbase (se 3 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 647149 = 242681) (by norm_num)
theorem B286717 : Blo 251819 286717 := bbase (se 3 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 286717 = 107519) (by norm_num)
theorem B286753 : Blo 251819 286753 := bbase (se 2 (by rfl) ⟨107532, by rfl⟩ : syracuseStep 286753 = 215065) (by norm_num)
theorem B286789 : Blo 251819 286789 := bbase (se 4 (by rfl) ⟨26886, by rfl⟩ : syracuseStep 286789 = 53773) (by norm_num)
theorem B319565 : Blo 251819 319565 := bbase (se 3 (by rfl) ⟨59918, by rfl⟩ : syracuseStep 319565 = 119837) (by norm_num)
theorem B811093 : Blo 251819 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B647261 : Blo 251819 647261 := bbase (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) (by norm_num)
theorem B286825 : Blo 251819 286825 := bbase (se 2 (by rfl) ⟨107559, by rfl⟩ : syracuseStep 286825 = 215119) (by norm_num)
theorem B319621 : Blo 251819 319621 := bbase (se 4 (by rfl) ⟨29964, by rfl⟩ : syracuseStep 319621 = 59929) (by norm_num)
theorem B286861 : Blo 251819 286861 := bbase (se 3 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 286861 = 107573) (by norm_num)
theorem B286897 : Blo 251819 286897 := bbase (se 2 (by rfl) ⟨107586, by rfl⟩ : syracuseStep 286897 = 215173) (by norm_num)
theorem B483509 : Blo 251819 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B286933 : Blo 251819 286933 := bbase (se 7 (by rfl) ⟨3362, by rfl⟩ : syracuseStep 286933 = 6725) (by norm_num)
theorem B319717 : Blo 251819 319717 := bbase (se 4 (by rfl) ⟨29973, by rfl⟩ : syracuseStep 319717 = 59947) (by norm_num)
theorem B286969 : Blo 251819 286969 := bbase (se 2 (by rfl) ⟨107613, by rfl⟩ : syracuseStep 286969 = 215227) (by norm_num)
theorem B287005 : Blo 251819 287005 := bbase (se 3 (by rfl) ⟨53813, by rfl⟩ : syracuseStep 287005 = 107627) (by norm_num)
theorem B647453 : Blo 251819 647453 := bbase (se 3 (by rfl) ⟨121397, by rfl⟩ : syracuseStep 647453 = 242795) (by norm_num)
theorem B287041 : Blo 251819 287041 := bbase (se 2 (by rfl) ⟨107640, by rfl⟩ : syracuseStep 287041 = 215281) (by norm_num)
theorem B483661 : Blo 251819 483661 := bbase (se 3 (by rfl) ⟨90686, by rfl⟩ : syracuseStep 483661 = 181373) (by norm_num)
theorem B287077 : Blo 251819 287077 := bbase (se 4 (by rfl) ⟨26913, by rfl⟩ : syracuseStep 287077 = 53827) (by norm_num)
theorem B287113 : Blo 251819 287113 := bbase (se 2 (by rfl) ⟨107667, by rfl⟩ : syracuseStep 287113 = 215335) (by norm_num)
theorem B319889 : Blo 251819 319889 := bbase (se 2 (by rfl) ⟨119958, by rfl⟩ : syracuseStep 319889 = 239917) (by norm_num)
theorem B287149 : Blo 251819 287149 := bbase (se 3 (by rfl) ⟨53840, by rfl⟩ : syracuseStep 287149 = 107681) (by norm_num)
theorem B319945 : Blo 251819 319945 := bbase (se 2 (by rfl) ⟨119979, by rfl⟩ : syracuseStep 319945 = 239959) (by norm_num)
theorem B287185 : Blo 251819 287185 := bbase (se 2 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 287185 = 215389) (by norm_num)
theorem B287221 : Blo 251819 287221 := bbase (se 5 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 287221 = 26927) (by norm_num)
theorem B287257 : Blo 251819 287257 := bbase (se 2 (by rfl) ⟨107721, by rfl⟩ : syracuseStep 287257 = 215443) (by norm_num)
theorem B320041 : Blo 251819 320041 := bbase (se 2 (by rfl) ⟨120015, by rfl⟩ : syracuseStep 320041 = 240031) (by norm_num)
theorem B287293 : Blo 251819 287293 := bbase (se 3 (by rfl) ⟨53867, by rfl⟩ : syracuseStep 287293 = 107735) (by norm_num)
theorem B287329 : Blo 251819 287329 := bbase (se 2 (by rfl) ⟨107748, by rfl⟩ : syracuseStep 287329 = 215497) (by norm_num)
theorem B483965 : Blo 251819 483965 := bbase (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) (by norm_num)
theorem B287365 : Blo 251819 287365 := bbase (se 4 (by rfl) ⟨26940, by rfl⟩ : syracuseStep 287365 = 53881) (by norm_num)
theorem B287401 : Blo 251819 287401 := bbase (se 2 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 287401 = 215551) (by norm_num)
theorem B287437 : Blo 251819 287437 := bbase (se 3 (by rfl) ⟨53894, by rfl⟩ : syracuseStep 287437 = 107789) (by norm_num)
theorem B287441 : Blo 251819 287441 := bbase (se 2 (by rfl) ⟨107790, by rfl⟩ : syracuseStep 287441 = 215581) (by norm_num)
theorem B320213 : Blo 251819 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B287473 : Blo 251819 287473 := bbase (se 2 (by rfl) ⟨107802, by rfl⟩ : syracuseStep 287473 = 215605) (by norm_num)
theorem B287497 : Blo 251819 287497 := bbase (se 2 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 287497 = 215623) (by norm_num)
theorem B320269 : Blo 251819 320269 := bbase (se 3 (by rfl) ⟨60050, by rfl⟩ : syracuseStep 320269 = 120101) (by norm_num)
theorem B1237781 : Blo 251819 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B287509 : Blo 251819 287509 := bbase (se 6 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 287509 = 13477) (by norm_num)
theorem B287545 : Blo 251819 287545 := bbase (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) (by norm_num)
theorem B287581 : Blo 251819 287581 := bbase (se 3 (by rfl) ⟨53921, by rfl⟩ : syracuseStep 287581 = 107843) (by norm_num)
theorem B615269 : Blo 251819 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B320365 : Blo 251819 320365 := bbase (se 3 (by rfl) ⟨60068, by rfl⟩ : syracuseStep 320365 = 120137) (by norm_num)
theorem B287617 : Blo 251819 287617 := bbase (se 2 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 287617 = 215713) (by norm_num)
theorem B615325 : Blo 251819 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B287653 : Blo 251819 287653 := bbase (se 4 (by rfl) ⟨26967, by rfl⟩ : syracuseStep 287653 = 53935) (by norm_num)
theorem B1041349 : Blo 251819 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B287689 : Blo 251819 287689 := bbase (se 2 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 287689 = 215767) (by norm_num)
theorem B1434581 : Blo 251819 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B287725 : Blo 251819 287725 := bbase (se 3 (by rfl) ⟨53948, by rfl⟩ : syracuseStep 287725 = 107897) (by norm_num)
theorem B287761 : Blo 251819 287761 := bbase (se 2 (by rfl) ⟨107910, by rfl⟩ : syracuseStep 287761 = 215821) (by norm_num)
theorem B2057237 : Blo 251819 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B320537 : Blo 251819 320537 := bbase (se 2 (by rfl) ⟨120201, by rfl⟩ : syracuseStep 320537 = 240403) (by norm_num)
theorem B287797 : Blo 251819 287797 := bbase (se 5 (by rfl) ⟨13490, by rfl⟩ : syracuseStep 287797 = 26981) (by norm_num)
theorem B320593 : Blo 251819 320593 := bbase (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) (by norm_num)
theorem B320689 : Blo 251819 320689 := bbase (se 2 (by rfl) ⟨120258, by rfl⟩ : syracuseStep 320689 = 240517) (by norm_num)
theorem B550141 : Blo 251819 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B582941 : Blo 251819 582941 := bbase (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) (by norm_num)
theorem B517429 : Blo 251819 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B386365 : Blo 251819 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B3106133 : Blo 251819 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B320861 : Blo 251819 320861 := bbase (se 3 (by rfl) ⟨60161, by rfl⟩ : syracuseStep 320861 = 120323) (by norm_num)
theorem B484717 : Blo 251819 484717 := bbase (se 3 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 484717 = 181769) (by norm_num)
theorem B681365 : Blo 251819 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B320917 : Blo 251819 320917 := bbase (se 6 (by rfl) ⟨7521, by rfl⟩ : syracuseStep 320917 = 15043) (by norm_num)
theorem B321013 : Blo 251819 321013 := bbase (se 5 (by rfl) ⟨15047, by rfl⟩ : syracuseStep 321013 = 30095) (by norm_num)
theorem B484861 : Blo 251819 484861 := bbase (se 3 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 484861 = 181823) (by norm_num)
theorem B812693 : Blo 251819 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B288409 : Blo 251819 288409 := bbase (se 2 (by rfl) ⟨108153, by rfl⟩ : syracuseStep 288409 = 216307) (by norm_num)
theorem B485021 : Blo 251819 485021 := bbase (se 3 (by rfl) ⟨90941, by rfl⟩ : syracuseStep 485021 = 181883) (by norm_num)
theorem B321185 : Blo 251819 321185 := bbase (se 2 (by rfl) ⟨120444, by rfl⟩ : syracuseStep 321185 = 240889) (by norm_num)
theorem B321241 : Blo 251819 321241 := bbase (se 2 (by rfl) ⟨120465, by rfl⟩ : syracuseStep 321241 = 240931) (by norm_num)
theorem B517853 : Blo 251819 517853 := bbase (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) (by norm_num)
theorem B583469 : Blo 251819 583469 := bbase (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) (by norm_num)
theorem B485165 : Blo 251819 485165 := bbase (se 3 (by rfl) ⟨90968, by rfl⟩ : syracuseStep 485165 = 181937) (by norm_num)
theorem B386869 : Blo 251819 386869 := bbase (se 5 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 386869 = 36269) (by norm_num)
theorem B321337 : Blo 251819 321337 := bbase (se 2 (by rfl) ⟨120501, by rfl⟩ : syracuseStep 321337 = 241003) (by norm_num)
theorem B321509 : Blo 251819 321509 := bbase (se 4 (by rfl) ⟨30141, by rfl⟩ : syracuseStep 321509 = 60283) (by norm_num)
theorem B550885 : Blo 251819 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B321565 : Blo 251819 321565 := bbase (se 3 (by rfl) ⟨60293, by rfl⟩ : syracuseStep 321565 = 120587) (by norm_num)
theorem B485453 : Blo 251819 485453 := bbase (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) (by norm_num)
theorem B1435765 : Blo 251819 1435765 := bbase (se 5 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 1435765 = 134603) (by norm_num)
theorem B321661 : Blo 251819 321661 := bbase (se 3 (by rfl) ⟨60311, by rfl⟩ : syracuseStep 321661 = 120623) (by norm_num)
theorem B387293 : Blo 251819 387293 := bbase (se 3 (by rfl) ⟨72617, by rfl⟩ : syracuseStep 387293 = 145235) (by norm_num)
theorem B485605 : Blo 251819 485605 := bbase (se 4 (by rfl) ⟨45525, by rfl⟩ : syracuseStep 485605 = 91051) (by norm_num)
theorem B321833 : Blo 251819 321833 := bbase (se 2 (by rfl) ⟨120687, by rfl⟩ : syracuseStep 321833 = 241375) (by norm_num)
theorem B321889 : Blo 251819 321889 := bbase (se 2 (by rfl) ⟨120708, by rfl⟩ : syracuseStep 321889 = 241417) (by norm_num)
theorem B289189 : Blo 251819 289189 := bbase (se 4 (by rfl) ⟨27111, by rfl⟩ : syracuseStep 289189 = 54223) (by norm_num)
theorem B321985 : Blo 251819 321985 := bbase (se 2 (by rfl) ⟨120744, by rfl⟩ : syracuseStep 321985 = 241489) (by norm_num)
theorem B256493 : Blo 251819 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B682597 : Blo 251819 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B322157 : Blo 251819 322157 := bbase (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) (by norm_num)
theorem B1174181 : Blo 251819 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B322213 : Blo 251819 322213 := bbase (se 4 (by rfl) ⟨30207, by rfl⟩ : syracuseStep 322213 = 60415) (by norm_num)
theorem B813797 : Blo 251819 813797 := bbase (se 4 (by rfl) ⟨76293, by rfl⟩ : syracuseStep 813797 = 152587) (by norm_num)
theorem B322309 : Blo 251819 322309 := bbase (se 4 (by rfl) ⟨30216, by rfl⟩ : syracuseStep 322309 = 60433) (by norm_num)
theorem B256801 : Blo 251819 256801 := bbase (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) (by norm_num)
theorem B486197 : Blo 251819 486197 := bbase (se 5 (by rfl) ⟨22790, by rfl⟩ : syracuseStep 486197 = 45581) (by norm_num)
theorem B322481 : Blo 251819 322481 := bbase (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) (by norm_num)
theorem B322537 : Blo 251819 322537 := bbase (se 2 (by rfl) ⟨120951, by rfl⟩ : syracuseStep 322537 = 241903) (by norm_num)
theorem B519229 : Blo 251819 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B322633 : Blo 251819 322633 := bbase (se 2 (by rfl) ⟨120987, by rfl⟩ : syracuseStep 322633 = 241975) (by norm_num)
theorem B650357 : Blo 251819 650357 := bbase (se 5 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 650357 = 60971) (by norm_num)
theorem B4942997 : Blo 251819 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2157749 : Blo 251819 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B2616533 : Blo 251819 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B322805 : Blo 251819 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B3239189 : Blo 251819 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B322861 : Blo 251819 322861 := bbase (se 3 (by rfl) ⟨60536, by rfl⟩ : syracuseStep 322861 = 121073) (by norm_num)
theorem B322957 : Blo 251819 322957 := bbase (se 3 (by rfl) ⟨60554, by rfl⟩ : syracuseStep 322957 = 121109) (by norm_num)
theorem B323129 : Blo 251819 323129 := bbase (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) (by norm_num)
theorem B323185 : Blo 251819 323185 := bbase (se 2 (by rfl) ⟨121194, by rfl⟩ : syracuseStep 323185 = 242389) (by norm_num)
theorem B323249 : Blo 251819 323249 := bbase (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) (by norm_num)
theorem B323281 : Blo 251819 323281 := bbase (se 2 (by rfl) ⟨121230, by rfl⟩ : syracuseStep 323281 = 242461) (by norm_num)
theorem B323285 : Blo 251819 323285 := bbase (se 7 (by rfl) ⟨3788, by rfl⟩ : syracuseStep 323285 = 7577) (by norm_num)
theorem B1732309 : Blo 251819 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B683765 : Blo 251819 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B323453 : Blo 251819 323453 := bbase (se 3 (by rfl) ⟨60647, by rfl⟩ : syracuseStep 323453 = 121295) (by norm_num)
theorem B913301 : Blo 251819 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B323509 : Blo 251819 323509 := bbase (se 5 (by rfl) ⟨15164, by rfl⟩ : syracuseStep 323509 = 30329) (by norm_num)
theorem B454589 : Blo 251819 454589 := bbase (se 3 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 454589 = 170471) (by norm_num)
theorem B1830869 : Blo 251819 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B2060245 : Blo 251819 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B323605 : Blo 251819 323605 := bbase (se 6 (by rfl) ⟨7584, by rfl⟩ : syracuseStep 323605 = 15169) (by norm_num)
theorem B1437749 : Blo 251819 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B1634357 : Blo 251819 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B684101 : Blo 251819 684101 := bbase (se 4 (by rfl) ⟨64134, by rfl⟩ : syracuseStep 684101 = 128269) (by norm_num)
theorem B684197 : Blo 251819 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B913589 : Blo 251819 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B1372373 : Blo 251819 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B618725 : Blo 251819 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B258301 : Blo 251819 258301 := bbase (se 3 (by rfl) ⟨48431, by rfl⟩ : syracuseStep 258301 = 96863) (by norm_num)
theorem B291173 : Blo 251819 291173 := bbase (se 4 (by rfl) ⟨27297, by rfl⟩ : syracuseStep 291173 = 54595) (by norm_num)
theorem B455093 : Blo 251819 455093 := bbase (se 5 (by rfl) ⟨21332, by rfl⟩ : syracuseStep 455093 = 42665) (by norm_num)
theorem B1077781 : Blo 251819 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B1110629 : Blo 251819 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B815717 : Blo 251819 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B258877 : Blo 251819 258877 := bbase (se 3 (by rfl) ⟨48539, by rfl⟩ : syracuseStep 258877 = 97079) (by norm_num)
theorem B652205 : Blo 251819 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B717781 : Blo 251819 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B1832341 : Blo 251819 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B325117 : Blo 251819 325117 := bbase (se 3 (by rfl) ⟨60959, by rfl⟩ : syracuseStep 325117 = 121919) (by norm_num)
theorem B1275749 : Blo 251819 1275749 := bbase (se 4 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 1275749 = 239203) (by norm_num)
theorem B817141 : Blo 251819 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B718885 : Blo 251819 718885 := bbase (se 4 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 718885 = 134791) (by norm_num)
theorem B1439957 : Blo 251819 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B522517 : Blo 251819 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B850229 : Blo 251819 850229 := bbase (se 5 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 850229 = 79709) (by norm_num)
theorem B817589 : Blo 251819 817589 := bbase (se 5 (by rfl) ⟨38324, by rfl⟩ : syracuseStep 817589 = 76649) (by norm_num)
theorem B981445 : Blo 251819 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B1735157 : Blo 251819 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B2423317 : Blo 251819 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B457285 : Blo 251819 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B916069 : Blo 251819 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B359101 : Blo 251819 359101 := bbase (se 3 (by rfl) ⟨67331, by rfl⟩ : syracuseStep 359101 = 134663) (by norm_num)
theorem B850661 : Blo 251819 850661 := bbase (se 4 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 850661 = 159499) (by norm_num)
theorem B1833749 : Blo 251819 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B424973 : Blo 251819 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B326749 : Blo 251819 326749 := bbase (se 3 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 326749 = 122531) (by norm_num)
theorem B1277045 : Blo 251819 1277045 := bbase (se 5 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 1277045 = 119723) (by norm_num)
theorem B457861 : Blo 251819 457861 := bbase (se 4 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 457861 = 85849) (by norm_num)
theorem B425101 : Blo 251819 425101 := bbase (se 3 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 425101 = 159413) (by norm_num)
theorem B851093 : Blo 251819 851093 := bbase (se 6 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 851093 = 39895) (by norm_num)
theorem B326873 : Blo 251819 326873 := bbase (se 2 (by rfl) ⟨122577, by rfl⟩ : syracuseStep 326873 = 245155) (by norm_num)
theorem B425189 : Blo 251819 425189 := bbase (se 4 (by rfl) ⟨39861, by rfl⟩ : syracuseStep 425189 = 79723) (by norm_num)
theorem B425317 : Blo 251819 425317 := bbase (se 4 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 425317 = 79747) (by norm_num)
theorem B425405 : Blo 251819 425405 := bbase (se 3 (by rfl) ⟨79763, by rfl⟩ : syracuseStep 425405 = 159527) (by norm_num)
theorem B1080773 : Blo 251819 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B359893 : Blo 251819 359893 := bbase (se 7 (by rfl) ⟨4217, by rfl⟩ : syracuseStep 359893 = 8435) (by norm_num)
theorem B720389 : Blo 251819 720389 := bbase (se 4 (by rfl) ⟨67536, by rfl⟩ : syracuseStep 720389 = 135073) (by norm_num)
theorem B1932821 : Blo 251819 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B425533 : Blo 251819 425533 := bbase (se 3 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 425533 = 159575) (by norm_num)
theorem B851525 : Blo 251819 851525 := bbase (se 4 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 851525 = 159661) (by norm_num)
theorem B425621 : Blo 251819 425621 := bbase (se 6 (by rfl) ⟨9975, by rfl⟩ : syracuseStep 425621 = 19951) (by norm_num)
theorem B1310453 : Blo 251819 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B425749 : Blo 251819 425749 := bbase (se 6 (by rfl) ⟨9978, by rfl⟩ : syracuseStep 425749 = 19957) (by norm_num)
theorem B360229 : Blo 251819 360229 := bbase (se 4 (by rfl) ⟨33771, by rfl⟩ : syracuseStep 360229 = 67543) (by norm_num)
theorem B327529 : Blo 251819 327529 := bbase (se 2 (by rfl) ⟨122823, by rfl⟩ : syracuseStep 327529 = 245647) (by norm_num)
theorem B425837 : Blo 251819 425837 := bbase (se 3 (by rfl) ⟨79844, by rfl⟩ : syracuseStep 425837 = 159689) (by norm_num)
theorem B556949 : Blo 251819 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B425965 : Blo 251819 425965 := bbase (se 3 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 425965 = 159737) (by norm_num)
theorem B851957 : Blo 251819 851957 := bbase (se 5 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 851957 = 79871) (by norm_num)
theorem B360445 : Blo 251819 360445 := bbase (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) (by norm_num)
theorem B720913 : Blo 251819 720913 := bstep (se 2 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 720913 = 540685) B540685
theorem B426019 : Blo 251819 426019 := bstep (se 1 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 426019 = 639029) B639029
theorem B1081457 : Blo 251819 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B426161 : Blo 251819 426161 := bstep (se 2 (by rfl) ⟨159810, by rfl⟩ : syracuseStep 426161 = 319621) B319621
theorem B1474757 : Blo 251819 1474757 := bstep (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) B276517
theorem B852173 : Blo 251819 852173 := bstep (se 3 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 852173 = 319565) B319565
theorem B1278179 : Blo 251819 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B852227 : Blo 251819 852227 := bstep (se 1 (by rfl) ⟨639170, by rfl⟩ : syracuseStep 852227 = 1278341) B1278341
theorem B721187 : Blo 251819 721187 := bstep (se 1 (by rfl) ⟨540890, by rfl⟩ : syracuseStep 721187 = 1081781) B1081781
theorem B426289 : Blo 251819 426289 := bstep (se 2 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 426289 = 319717) B319717
theorem B426323 : Blo 251819 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B360787 : Blo 251819 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B426451 : Blo 251819 426451 := bstep (se 1 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 426451 = 639677) B639677
theorem B2425315 : Blo 251819 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B2163185 : Blo 251819 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B852497 : Blo 251819 852497 := bstep (se 2 (by rfl) ⟨319686, by rfl⟩ : syracuseStep 852497 = 639373) B639373
theorem B655939 : Blo 251819 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B426593 : Blo 251819 426593 := bstep (se 2 (by rfl) ⟨159972, by rfl⟩ : syracuseStep 426593 = 319945) B319945
theorem B426721 : Blo 251819 426721 := bstep (se 2 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 426721 = 320041) B320041
theorem B426755 : Blo 251819 426755 := bstep (se 1 (by rfl) ⟨320066, by rfl⟩ : syracuseStep 426755 = 640133) B640133
theorem B361265 : Blo 251819 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B426883 : Blo 251819 426883 := bstep (se 1 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 426883 = 640325) B640325
theorem B361379 : Blo 251819 361379 := bstep (se 1 (by rfl) ⟨271034, by rfl⟩ : syracuseStep 361379 = 542069) B542069
theorem B361459 : Blo 251819 361459 := bstep (se 1 (by rfl) ⟨271094, by rfl⟩ : syracuseStep 361459 = 542189) B542189
theorem B1278989 : Blo 251819 1278989 := bstep (se 3 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 1278989 = 479621) B479621
theorem B427025 : Blo 251819 427025 := bstep (se 2 (by rfl) ⟨160134, by rfl⟩ : syracuseStep 427025 = 320269) B320269
theorem B853037 : Blo 251819 853037 := bstep (se 3 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 853037 = 319889) B319889
theorem B853091 : Blo 251819 853091 := bstep (se 1 (by rfl) ⟨639818, by rfl⟩ : syracuseStep 853091 = 1279637) B1279637
theorem B722029 : Blo 251819 722029 := bstep (se 3 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 722029 = 270761) B270761
theorem B427153 : Blo 251819 427153 := bstep (se 2 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 427153 = 320365) B320365
theorem B427187 : Blo 251819 427187 := bstep (se 1 (by rfl) ⟨320390, by rfl⟩ : syracuseStep 427187 = 640781) B640781
theorem B820433 : Blo 251819 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B689411 : Blo 251819 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B722189 : Blo 251819 722189 := bstep (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) B270821
theorem B427315 : Blo 251819 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B1377605 : Blo 251819 1377605 := bstep (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) B258301
theorem B853361 : Blo 251819 853361 := bstep (se 2 (by rfl) ⟨320010, by rfl⟩ : syracuseStep 853361 = 640021) B640021
theorem B427457 : Blo 251819 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B722371 : Blo 251819 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B362017 : Blo 251819 362017 := bstep (se 2 (by rfl) ⟨135756, by rfl⟩ : syracuseStep 362017 = 271513) B271513
theorem B1312291 : Blo 251819 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B427585 : Blo 251819 427585 := bstep (se 2 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 427585 = 320689) B320689
theorem B427619 : Blo 251819 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B427747 : Blo 251819 427747 := bstep (se 1 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 427747 = 641621) B641621
theorem B7374563 : Blo 251819 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B689905 : Blo 251819 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B427889 : Blo 251819 427889 := bstep (se 2 (by rfl) ⟨160458, by rfl⟩ : syracuseStep 427889 = 320917) B320917
theorem B853901 : Blo 251819 853901 := bstep (se 3 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 853901 = 320213) B320213
theorem B853955 : Blo 251819 853955 := bstep (se 1 (by rfl) ⟨640466, by rfl⟩ : syracuseStep 853955 = 1280933) B1280933
theorem B428017 : Blo 251819 428017 := bstep (se 2 (by rfl) ⟨160506, by rfl⟩ : syracuseStep 428017 = 321013) B321013
theorem B460817 : Blo 251819 460817 := bstep (se 2 (by rfl) ⟨172806, by rfl⟩ : syracuseStep 460817 = 345613) B345613
theorem B428051 : Blo 251819 428051 := bstep (se 1 (by rfl) ⟨321038, by rfl⟩ : syracuseStep 428051 = 642077) B642077
theorem B2328689 : Blo 251819 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B428179 : Blo 251819 428179 := bstep (se 1 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 428179 = 642269) B642269
theorem B1542341 : Blo 251819 1542341 := bstep (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) B289189
theorem B854225 : Blo 251819 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B362723 : Blo 251819 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B428321 : Blo 251819 428321 := bstep (se 2 (by rfl) ⟨160620, by rfl⟩ : syracuseStep 428321 = 321241) B321241
theorem B4131125 : Blo 251819 4131125 := bstep (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) B387293
theorem B428449 : Blo 251819 428449 := bstep (se 2 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 428449 = 321337) B321337
theorem B428483 : Blo 251819 428483 := bstep (se 1 (by rfl) ⟨321362, by rfl⟩ : syracuseStep 428483 = 642725) B642725
theorem B428611 : Blo 251819 428611 := bstep (se 1 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 428611 = 642917) B642917
theorem B428753 : Blo 251819 428753 := bstep (se 2 (by rfl) ⟨160782, by rfl⟩ : syracuseStep 428753 = 321565) B321565
theorem B854765 : Blo 251819 854765 := bstep (se 3 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 854765 = 320537) B320537
theorem B854819 : Blo 251819 854819 := bstep (se 1 (by rfl) ⟨641114, by rfl⟩ : syracuseStep 854819 = 1282229) B1282229
theorem B723761 : Blo 251819 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B428881 : Blo 251819 428881 := bstep (se 2 (by rfl) ⟨160830, by rfl⟩ : syracuseStep 428881 = 321661) B321661
theorem B363361 : Blo 251819 363361 := bstep (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) B272521
theorem B428915 : Blo 251819 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B1543117 : Blo 251819 1543117 := bstep (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) B578669
theorem B363475 : Blo 251819 363475 := bstep (se 1 (by rfl) ⟨272606, by rfl⟩ : syracuseStep 363475 = 545213) B545213
theorem B429043 : Blo 251819 429043 := bstep (se 1 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 429043 = 643565) B643565
theorem B855089 : Blo 251819 855089 := bstep (se 2 (by rfl) ⟨320658, by rfl⟩ : syracuseStep 855089 = 641317) B641317
theorem B429185 : Blo 251819 429185 := bstep (se 2 (by rfl) ⟨160944, by rfl⟩ : syracuseStep 429185 = 321889) B321889
theorem B429313 : Blo 251819 429313 := bstep (se 2 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 429313 = 321985) B321985
theorem B429347 : Blo 251819 429347 := bstep (se 1 (by rfl) ⟨322010, by rfl⟩ : syracuseStep 429347 = 644021) B644021
theorem B1936709 : Blo 251819 1936709 := bstep (se 4 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 1936709 = 363133) B363133
theorem B429475 : Blo 251819 429475 := bstep (se 1 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 429475 = 644213) B644213
theorem B429617 : Blo 251819 429617 := bstep (se 2 (by rfl) ⟨161106, by rfl⟩ : syracuseStep 429617 = 322213) B322213
theorem B855629 : Blo 251819 855629 := bstep (se 3 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 855629 = 320861) B320861
theorem B855683 : Blo 251819 855683 := bstep (se 1 (by rfl) ⟨641762, by rfl⟩ : syracuseStep 855683 = 1283525) B1283525
theorem B429745 : Blo 251819 429745 := bstep (se 2 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 429745 = 322309) B322309
theorem B429779 : Blo 251819 429779 := bstep (se 1 (by rfl) ⟨322334, by rfl⟩ : syracuseStep 429779 = 644669) B644669
theorem B724717 : Blo 251819 724717 := bstep (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) B271769
theorem B1085197 : Blo 251819 1085197 := bstep (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) B406949
theorem B429907 : Blo 251819 429907 := bstep (se 1 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 429907 = 644861) B644861
theorem B1281905 : Blo 251819 1281905 := bstep (se 2 (by rfl) ⟨480714, by rfl⟩ : syracuseStep 1281905 = 961429) B961429
theorem B855953 : Blo 251819 855953 := bstep (se 2 (by rfl) ⟨320982, by rfl⟩ : syracuseStep 855953 = 641965) B641965
theorem B1544113 : Blo 251819 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B724945 : Blo 251819 724945 := bstep (se 2 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 724945 = 543709) B543709
theorem B430049 : Blo 251819 430049 := bstep (se 2 (by rfl) ⟨161268, by rfl⟩ : syracuseStep 430049 = 322537) B322537
theorem B430177 : Blo 251819 430177 := bstep (se 2 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 430177 = 322633) B322633
theorem B725105 : Blo 251819 725105 := bstep (se 2 (by rfl) ⟨271914, by rfl⟩ : syracuseStep 725105 = 543829) B543829
theorem B430211 : Blo 251819 430211 := bstep (se 1 (by rfl) ⟨322658, by rfl⟩ : syracuseStep 430211 = 645317) B645317
theorem B2330765 : Blo 251819 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B725219 : Blo 251819 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B430339 : Blo 251819 430339 := bstep (se 1 (by rfl) ⟨322754, by rfl⟩ : syracuseStep 430339 = 645509) B645509
theorem B2167181 : Blo 251819 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B430481 : Blo 251819 430481 := bstep (se 2 (by rfl) ⟨161430, by rfl⟩ : syracuseStep 430481 = 322861) B322861
theorem B856493 : Blo 251819 856493 := bstep (se 3 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 856493 = 321185) B321185
theorem B856547 : Blo 251819 856547 := bstep (se 1 (by rfl) ⟨642410, by rfl⟩ : syracuseStep 856547 = 1284821) B1284821
theorem B430609 : Blo 251819 430609 := bstep (se 2 (by rfl) ⟨161478, by rfl⟩ : syracuseStep 430609 = 322957) B322957
theorem B430643 : Blo 251819 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B430771 : Blo 251819 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B856817 : Blo 251819 856817 := bstep (se 2 (by rfl) ⟨321306, by rfl⟩ : syracuseStep 856817 = 642613) B642613
theorem B430913 : Blo 251819 430913 := bstep (se 2 (by rfl) ⟨161592, by rfl⟩ : syracuseStep 430913 = 323185) B323185
theorem B431041 : Blo 251819 431041 := bstep (se 2 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 431041 = 323281) B323281
theorem B431075 : Blo 251819 431075 := bstep (se 1 (by rfl) ⟨323306, by rfl⟩ : syracuseStep 431075 = 646613) B646613
theorem B431203 : Blo 251819 431203 := bstep (se 1 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 431203 = 646805) B646805
theorem B726221 : Blo 251819 726221 := bstep (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) B272333
theorem B365779 : Blo 251819 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B431345 : Blo 251819 431345 := bstep (se 2 (by rfl) ⟨161754, by rfl⟩ : syracuseStep 431345 = 323509) B323509
theorem B857357 : Blo 251819 857357 := bstep (se 3 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 857357 = 321509) B321509
theorem B1283363 : Blo 251819 1283363 := bstep (se 1 (by rfl) ⟨962522, by rfl⟩ : syracuseStep 1283363 = 1925045) B1925045
theorem B857411 : Blo 251819 857411 := bstep (se 1 (by rfl) ⟨643058, by rfl⟩ : syracuseStep 857411 = 1286117) B1286117
theorem B431473 : Blo 251819 431473 := bstep (se 2 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 431473 = 323605) B323605
theorem B726403 : Blo 251819 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B12719501 : Blo 251819 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B431507 : Blo 251819 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B3282403 : Blo 251819 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B1447429 : Blo 251819 1447429 := bstep (se 4 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 1447429 = 271393) B271393
theorem B431635 : Blo 251819 431635 := bstep (se 1 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 431635 = 647453) B647453
theorem B726563 : Blo 251819 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B857681 : Blo 251819 857681 := bstep (se 2 (by rfl) ⟨321630, by rfl⟩ : syracuseStep 857681 = 643261) B643261
theorem B825187 : Blo 251819 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B1382321 : Blo 251819 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B956387 : Blo 251819 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B464899 : Blo 251819 464899 := bstep (se 1 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 464899 = 697349) B697349
theorem B1284173 : Blo 251819 1284173 := bstep (se 3 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 1284173 = 481565) B481565
theorem B858221 : Blo 251819 858221 := bstep (se 3 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 858221 = 321833) B321833
theorem B858275 : Blo 251819 858275 := bstep (se 1 (by rfl) ⟨643706, by rfl⟩ : syracuseStep 858275 = 1287413) B1287413
theorem B2070755 : Blo 251819 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B2595185 : Blo 251819 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B858545 : Blo 251819 858545 := bstep (se 2 (by rfl) ⟨321954, by rfl⟩ : syracuseStep 858545 = 643909) B643909
theorem B727633 : Blo 251819 727633 := bstep (se 2 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 727633 = 545725) B545725
theorem B957041 : Blo 251819 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B859085 : Blo 251819 859085 := bstep (se 3 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 859085 = 322157) B322157
theorem B859139 : Blo 251819 859139 := bstep (se 1 (by rfl) ⟨644354, by rfl⟩ : syracuseStep 859139 = 1288709) B1288709
theorem B269411 : Blo 251819 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B859409 : Blo 251819 859409 := bstep (se 2 (by rfl) ⟨322278, by rfl⟩ : syracuseStep 859409 = 644557) B644557
theorem B433571 : Blo 251819 433571 := bstep (se 1 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 433571 = 650357) B650357
theorem B1449413 : Blo 251819 1449413 := bstep (se 4 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 1449413 = 271765) B271765
theorem B1744355 : Blo 251819 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B859949 : Blo 251819 859949 := bstep (se 3 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 859949 = 322481) B322481
theorem B270163 : Blo 251819 270163 := bstep (se 1 (by rfl) ⟨202622, by rfl⟩ : syracuseStep 270163 = 405245) B405245
theorem B860003 : Blo 251819 860003 := bstep (se 1 (by rfl) ⟨645002, by rfl⟩ : syracuseStep 860003 = 1290005) B1290005
theorem B303059 : Blo 251819 303059 := bstep (se 1 (by rfl) ⟨227294, by rfl⟩ : syracuseStep 303059 = 454589) B454589
theorem B1220579 : Blo 251819 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B1089521 : Blo 251819 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B958499 : Blo 251819 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B1089571 : Blo 251819 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B958513 : Blo 251819 958513 := bstep (se 2 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 958513 = 718885) B718885
theorem B860273 : Blo 251819 860273 := bstep (se 2 (by rfl) ⟨322602, by rfl⟩ : syracuseStep 860273 = 645205) B645205
theorem B303395 : Blo 251819 303395 := bstep (se 1 (by rfl) ⟨227546, by rfl⟩ : syracuseStep 303395 = 455093) B455093
theorem B696689 : Blo 251819 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B434803 : Blo 251819 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B860813 : Blo 251819 860813 := bstep (se 3 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 860813 = 322805) B322805
theorem B860867 : Blo 251819 860867 := bstep (se 1 (by rfl) ⟨645650, by rfl⟩ : syracuseStep 860867 = 1291301) B1291301
theorem B12264149 : Blo 251819 12264149 := bstep (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) B287441
theorem B1221425 : Blo 251819 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B271171 : Blo 251819 271171 := bstep (se 1 (by rfl) ⟨203378, by rfl⟩ : syracuseStep 271171 = 406757) B406757
theorem B1614725 : Blo 251819 1614725 := bstep (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) B302761
theorem B1287089 : Blo 251819 1287089 := bstep (se 2 (by rfl) ⟨482658, by rfl⟩ : syracuseStep 1287089 = 965317) B965317
theorem B861137 : Blo 251819 861137 := bstep (se 2 (by rfl) ⟨322926, by rfl⟩ : syracuseStep 861137 = 645853) B645853
theorem B1942541 : Blo 251819 1942541 := bstep (se 3 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 1942541 = 728453) B728453
theorem B435665 : Blo 251819 435665 := bstep (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) B326749
theorem B959971 : Blo 251819 959971 := bstep (se 1 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 959971 = 1439957) B1439957
theorem B861677 : Blo 251819 861677 := bstep (se 3 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 861677 = 323129) B323129
theorem B2991629 : Blo 251819 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B566801 : Blo 251819 566801 := bstep (se 2 (by rfl) ⟨212550, by rfl⟩ : syracuseStep 566801 = 425101) B425101
theorem B566819 : Blo 251819 566819 := bstep (se 1 (by rfl) ⟨425114, by rfl⟩ : syracuseStep 566819 = 850229) B850229
theorem B861731 : Blo 251819 861731 := bstep (se 1 (by rfl) ⟨646298, by rfl⟩ : syracuseStep 861731 = 1292597) B1292597
theorem B1156771 : Blo 251819 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B861997 : Blo 251819 861997 := bstep (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) B323249
theorem B567089 : Blo 251819 567089 := bstep (se 2 (by rfl) ⟨212658, by rfl⟩ : syracuseStep 567089 = 425317) B425317
theorem B862001 : Blo 251819 862001 := bstep (se 2 (by rfl) ⟨323250, by rfl⟩ : syracuseStep 862001 = 646501) B646501
theorem B272179 : Blo 251819 272179 := bstep (se 1 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 272179 = 408269) B408269
theorem B567107 : Blo 251819 567107 := bstep (se 1 (by rfl) ⟨425330, by rfl⟩ : syracuseStep 567107 = 850661) B850661
theorem B1222499 : Blo 251819 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B1746821 : Blo 251819 1746821 := bstep (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) B327529
theorem B862093 : Blo 251819 862093 := bstep (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) B323285
theorem B567377 : Blo 251819 567377 := bstep (se 2 (by rfl) ⟨212766, by rfl⟩ : syracuseStep 567377 = 425533) B425533
theorem B403553 : Blo 251819 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B567395 : Blo 251819 567395 := bstep (se 1 (by rfl) ⟨425546, by rfl⟩ : syracuseStep 567395 = 851093) B851093
theorem B1059149 : Blo 251819 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B862541 : Blo 251819 862541 := bstep (se 3 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 862541 = 323453) B323453
theorem B1288547 : Blo 251819 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B567665 : Blo 251819 567665 := bstep (se 2 (by rfl) ⟨212874, by rfl⟩ : syracuseStep 567665 = 425749) B425749
theorem B567683 : Blo 251819 567683 := bstep (se 1 (by rfl) ⟨425762, by rfl⟩ : syracuseStep 567683 = 851525) B851525
theorem B862595 : Blo 251819 862595 := bstep (se 1 (by rfl) ⟨646946, by rfl⟩ : syracuseStep 862595 = 1293893) B1293893
theorem B1091981 : Blo 251819 1091981 := bstep (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) B409493
theorem B272803 : Blo 251819 272803 := bstep (se 1 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 272803 = 409205) B409205
theorem B371299 : Blo 251819 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B567953 : Blo 251819 567953 := bstep (se 2 (by rfl) ⟨212982, by rfl⟩ : syracuseStep 567953 = 425965) B425965
theorem B862865 : Blo 251819 862865 := bstep (se 2 (by rfl) ⟨323574, by rfl⟩ : syracuseStep 862865 = 647149) B647149
theorem B567971 : Blo 251819 567971 := bstep (se 1 (by rfl) ⟨425978, by rfl⟩ : syracuseStep 567971 = 851957) B851957
theorem B568241 : Blo 251819 568241 := bstep (se 2 (by rfl) ⟨213090, by rfl⟩ : syracuseStep 568241 = 426181) B426181
theorem B699313 : Blo 251819 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B568259 : Blo 251819 568259 := bstep (se 1 (by rfl) ⟨426194, by rfl⟩ : syracuseStep 568259 = 852389) B852389
theorem B306163 : Blo 251819 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B1289357 : Blo 251819 1289357 := bstep (se 3 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 1289357 = 483509) B483509
theorem B1453261 : Blo 251819 1453261 := bstep (se 3 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 1453261 = 544973) B544973
theorem B568529 : Blo 251819 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B568547 : Blo 251819 568547 := bstep (se 1 (by rfl) ⟨426410, by rfl⟩ : syracuseStep 568547 = 852821) B852821
theorem B1649933 : Blo 251819 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B568817 : Blo 251819 568817 := bstep (se 2 (by rfl) ⟨213306, by rfl⟩ : syracuseStep 568817 = 426613) B426613
theorem B568835 : Blo 251819 568835 := bstep (se 1 (by rfl) ⟨426626, by rfl⟩ : syracuseStep 568835 = 853253) B853253
theorem B405091 : Blo 251819 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B962189 : Blo 251819 962189 := bstep (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) B360821
theorem B405137 : Blo 251819 405137 := bstep (se 2 (by rfl) ⟨151926, by rfl⟩ : syracuseStep 405137 = 303853) B303853
theorem B306883 : Blo 251819 306883 := bstep (se 1 (by rfl) ⟨230162, by rfl⟩ : syracuseStep 306883 = 460325) B460325
theorem B2895587 : Blo 251819 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B569105 : Blo 251819 569105 := bstep (se 2 (by rfl) ⟨213414, by rfl⟩ : syracuseStep 569105 = 426829) B426829
theorem B569123 : Blo 251819 569123 := bstep (se 1 (by rfl) ⟨426842, by rfl⟩ : syracuseStep 569123 = 853685) B853685
theorem B1388465 : Blo 251819 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B569393 : Blo 251819 569393 := bstep (se 2 (by rfl) ⟨213522, by rfl⟩ : syracuseStep 569393 = 427045) B427045
theorem B569411 : Blo 251819 569411 := bstep (se 1 (by rfl) ⟨427058, by rfl⟩ : syracuseStep 569411 = 854117) B854117
theorem B307379 : Blo 251819 307379 := bstep (se 1 (by rfl) ⟨230534, by rfl⟩ : syracuseStep 307379 = 461069) B461069
theorem B864515 : Blo 251819 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B2961677 : Blo 251819 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B2175245 : Blo 251819 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B569681 : Blo 251819 569681 := bstep (se 2 (by rfl) ⟨213630, by rfl⟩ : syracuseStep 569681 = 427261) B427261
theorem B569699 : Blo 251819 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B1618289 : Blo 251819 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B2241037 : Blo 251819 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B569969 : Blo 251819 569969 := bstep (se 2 (by rfl) ⟨213738, by rfl⟩ : syracuseStep 569969 = 427477) B427477
theorem B406129 : Blo 251819 406129 := bstep (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) B304597
theorem B569987 : Blo 251819 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B3093389 : Blo 251819 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B570257 : Blo 251819 570257 := bstep (se 2 (by rfl) ⟨213846, by rfl⟩ : syracuseStep 570257 = 427693) B427693
theorem B570275 : Blo 251819 570275 := bstep (se 1 (by rfl) ⟨427706, by rfl⟩ : syracuseStep 570275 = 855413) B855413
theorem B832547 : Blo 251819 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B406577 : Blo 251819 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B1455245 : Blo 251819 1455245 := bstep (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) B545717
theorem B570545 : Blo 251819 570545 := bstep (se 2 (by rfl) ⟨213954, by rfl⟩ : syracuseStep 570545 = 427909) B427909
theorem B570563 : Blo 251819 570563 := bstep (se 1 (by rfl) ⟨427922, by rfl⟩ : syracuseStep 570563 = 855845) B855845
theorem B734513 : Blo 251819 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B570833 : Blo 251819 570833 := bstep (se 2 (by rfl) ⟨214062, by rfl⟩ : syracuseStep 570833 = 428125) B428125
theorem B570851 : Blo 251819 570851 := bstep (se 1 (by rfl) ⟨428138, by rfl⟩ : syracuseStep 570851 = 856277) B856277
theorem B1914353 : Blo 251819 1914353 := bstep (se 2 (by rfl) ⟨717882, by rfl⟩ : syracuseStep 1914353 = 1435765) B1435765
theorem B571121 : Blo 251819 571121 := bstep (se 2 (by rfl) ⟨214170, by rfl⟩ : syracuseStep 571121 = 428341) B428341
theorem B571139 : Blo 251819 571139 := bstep (se 1 (by rfl) ⟨428354, by rfl⟩ : syracuseStep 571139 = 856709) B856709
theorem B1619747 : Blo 251819 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B538481 : Blo 251819 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B407443 : Blo 251819 407443 := bstep (se 1 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 407443 = 611165) B611165
theorem B1292273 : Blo 251819 1292273 := bstep (se 2 (by rfl) ⟨484602, by rfl⟩ : syracuseStep 1292273 = 969205) B969205
theorem B571409 : Blo 251819 571409 := bstep (se 2 (by rfl) ⟨214278, by rfl⟩ : syracuseStep 571409 = 428557) B428557
theorem B571427 : Blo 251819 571427 := bstep (se 1 (by rfl) ⟨428570, by rfl⟩ : syracuseStep 571427 = 857141) B857141
theorem B1456177 : Blo 251819 1456177 := bstep (se 2 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 1456177 = 1092133) B1092133
theorem B1554509 : Blo 251819 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B342163 : Blo 251819 342163 := bstep (se 1 (by rfl) ⟨256622, by rfl⟩ : syracuseStep 342163 = 513245) B513245
theorem B538883 : Blo 251819 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B571697 : Blo 251819 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B571715 : Blo 251819 571715 := bstep (se 1 (by rfl) ⟨428786, by rfl⟩ : syracuseStep 571715 = 857573) B857573
theorem B342401 : Blo 251819 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B965105 : Blo 251819 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B408115 : Blo 251819 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B571985 : Blo 251819 571985 := bstep (se 2 (by rfl) ⟨214494, by rfl⟩ : syracuseStep 571985 = 428989) B428989
theorem B408161 : Blo 251819 408161 := bstep (se 2 (by rfl) ⟨153060, by rfl⟩ : syracuseStep 408161 = 306121) B306121
theorem B572003 : Blo 251819 572003 := bstep (se 1 (by rfl) ⟨429002, by rfl⟩ : syracuseStep 572003 = 858005) B858005
theorem B637571 : Blo 251819 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B1620749 : Blo 251819 1620749 := bstep (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) B607781
theorem B572273 : Blo 251819 572273 := bstep (se 2 (by rfl) ⟨214602, by rfl⟩ : syracuseStep 572273 = 429205) B429205
theorem B572291 : Blo 251819 572291 := bstep (se 1 (by rfl) ⟨429218, by rfl⟩ : syracuseStep 572291 = 858437) B858437
theorem B408673 : Blo 251819 408673 := bstep (se 2 (by rfl) ⟨153252, by rfl⟩ : syracuseStep 408673 = 306505) B306505
theorem B539779 : Blo 251819 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B572561 : Blo 251819 572561 := bstep (se 2 (by rfl) ⟨214710, by rfl⟩ : syracuseStep 572561 = 429421) B429421
theorem B572579 : Blo 251819 572579 := bstep (se 1 (by rfl) ⟨429434, by rfl⟩ : syracuseStep 572579 = 858869) B858869
theorem B343219 : Blo 251819 343219 := bstep (se 1 (by rfl) ⟨257414, by rfl⟩ : syracuseStep 343219 = 514829) B514829
theorem B1293731 : Blo 251819 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B736685 : Blo 251819 736685 := bstep (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) B276257
theorem B572849 : Blo 251819 572849 := bstep (se 2 (by rfl) ⟨214818, by rfl⟩ : syracuseStep 572849 = 429637) B429637
theorem B572867 : Blo 251819 572867 := bstep (se 1 (by rfl) ⟨429650, by rfl⟩ : syracuseStep 572867 = 859301) B859301
theorem B638513 : Blo 251819 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B638563 : Blo 251819 638563 := bstep (se 1 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 638563 = 957845) B957845
theorem B409217 : Blo 251819 409217 := bstep (se 2 (by rfl) ⟨153456, by rfl⟩ : syracuseStep 409217 = 306913) B306913
theorem B573137 : Blo 251819 573137 := bstep (se 2 (by rfl) ⟨214926, by rfl⟩ : syracuseStep 573137 = 429853) B429853
theorem B573155 : Blo 251819 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B638705 : Blo 251819 638705 := bstep (se 2 (by rfl) ⟨239514, by rfl⟩ : syracuseStep 638705 = 479029) B479029
theorem B966563 : Blo 251819 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B573425 : Blo 251819 573425 := bstep (se 2 (by rfl) ⟨215034, by rfl⟩ : syracuseStep 573425 = 430069) B430069
theorem B573443 : Blo 251819 573443 := bstep (se 1 (by rfl) ⟨430082, by rfl⟩ : syracuseStep 573443 = 860165) B860165
theorem B1097891 : Blo 251819 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B1294541 : Blo 251819 1294541 := bstep (se 3 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 1294541 = 485453) B485453
theorem B573713 : Blo 251819 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B573731 : Blo 251819 573731 := bstep (se 1 (by rfl) ⟨430298, by rfl⟩ : syracuseStep 573731 = 860597) B860597
theorem B2769221 : Blo 251819 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B541009 : Blo 251819 541009 := bstep (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) B405757
theorem B410113 : Blo 251819 410113 := bstep (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) B307585
theorem B574001 : Blo 251819 574001 := bstep (se 2 (by rfl) ⟨215250, by rfl⟩ : syracuseStep 574001 = 430501) B430501
theorem B410179 : Blo 251819 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B574019 : Blo 251819 574019 := bstep (se 1 (by rfl) ⟨430514, by rfl⟩ : syracuseStep 574019 = 861029) B861029
theorem B639697 : Blo 251819 639697 := bstep (se 2 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 639697 = 479773) B479773
theorem B2081521 : Blo 251819 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B1295153 : Blo 251819 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B574289 : Blo 251819 574289 := bstep (se 2 (by rfl) ⟨215358, by rfl⟩ : syracuseStep 574289 = 430717) B430717
theorem B574307 : Blo 251819 574307 := bstep (se 1 (by rfl) ⟨430730, by rfl⟩ : syracuseStep 574307 = 861461) B861461
theorem B377729 : Blo 251819 377729 := bstep (se 2 (by rfl) ⟨141648, by rfl⟩ : syracuseStep 377729 = 283297) B283297
theorem B967565 : Blo 251819 967565 := bstep (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) B362837
theorem B377747 : Blo 251819 377747 := bstep (se 1 (by rfl) ⟨283310, by rfl⟩ : syracuseStep 377747 = 566621) B566621
theorem B377777 : Blo 251819 377777 := bstep (se 2 (by rfl) ⟨141666, by rfl⟩ : syracuseStep 377777 = 283333) B283333
theorem B377795 : Blo 251819 377795 := bstep (se 1 (by rfl) ⟨283346, by rfl⟩ : syracuseStep 377795 = 566693) B566693
theorem B377825 : Blo 251819 377825 := bstep (se 2 (by rfl) ⟨141684, by rfl⟩ : syracuseStep 377825 = 283369) B283369
theorem B639971 : Blo 251819 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B377843 : Blo 251819 377843 := bstep (se 1 (by rfl) ⟨283382, by rfl⟩ : syracuseStep 377843 = 566765) B566765
theorem B377873 : Blo 251819 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B377891 : Blo 251819 377891 := bstep (se 1 (by rfl) ⟨283418, by rfl⟩ : syracuseStep 377891 = 566837) B566837
theorem B377921 : Blo 251819 377921 := bstep (se 2 (by rfl) ⟨141720, by rfl⟩ : syracuseStep 377921 = 283441) B283441
theorem B345169 : Blo 251819 345169 := bstep (se 2 (by rfl) ⟨129438, by rfl⟩ : syracuseStep 345169 = 258877) B258877
theorem B377939 : Blo 251819 377939 := bstep (se 1 (by rfl) ⟨283454, by rfl⟩ : syracuseStep 377939 = 566909) B566909
theorem B377969 : Blo 251819 377969 := bstep (se 2 (by rfl) ⟨141738, by rfl⟩ : syracuseStep 377969 = 283477) B283477
theorem B574577 : Blo 251819 574577 := bstep (se 2 (by rfl) ⟨215466, by rfl⟩ : syracuseStep 574577 = 430933) B430933
theorem B377987 : Blo 251819 377987 := bstep (se 1 (by rfl) ⟨283490, by rfl⟩ : syracuseStep 377987 = 566981) B566981
theorem B574595 : Blo 251819 574595 := bstep (se 1 (by rfl) ⟨430946, by rfl⟩ : syracuseStep 574595 = 861893) B861893
theorem B345235 : Blo 251819 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B378017 : Blo 251819 378017 := bstep (se 2 (by rfl) ⟨141756, by rfl⟩ : syracuseStep 378017 = 283513) B283513
theorem B640163 : Blo 251819 640163 := bstep (se 1 (by rfl) ⟨480122, by rfl⟩ : syracuseStep 640163 = 960245) B960245
theorem B378035 : Blo 251819 378035 := bstep (se 1 (by rfl) ⟨283526, by rfl⟩ : syracuseStep 378035 = 567053) B567053
theorem B378065 : Blo 251819 378065 := bstep (se 2 (by rfl) ⟨141774, by rfl⟩ : syracuseStep 378065 = 283549) B283549
theorem B378083 : Blo 251819 378083 := bstep (se 1 (by rfl) ⟨283562, by rfl⟩ : syracuseStep 378083 = 567125) B567125
theorem B378113 : Blo 251819 378113 := bstep (se 2 (by rfl) ⟨141792, by rfl⟩ : syracuseStep 378113 = 283585) B283585
theorem B378131 : Blo 251819 378131 := bstep (se 1 (by rfl) ⟨283598, by rfl⟩ : syracuseStep 378131 = 567197) B567197
theorem B378161 : Blo 251819 378161 := bstep (se 2 (by rfl) ⟨141810, by rfl⟩ : syracuseStep 378161 = 283621) B283621
theorem B378179 : Blo 251819 378179 := bstep (se 1 (by rfl) ⟨283634, by rfl⟩ : syracuseStep 378179 = 567269) B567269
theorem B2934085 : Blo 251819 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B378209 : Blo 251819 378209 := bstep (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) B283657
theorem B378227 : Blo 251819 378227 := bstep (se 1 (by rfl) ⟨283670, by rfl⟩ : syracuseStep 378227 = 567341) B567341
theorem B378257 : Blo 251819 378257 := bstep (se 2 (by rfl) ⟨141846, by rfl⟩ : syracuseStep 378257 = 283693) B283693
theorem B574865 : Blo 251819 574865 := bstep (se 2 (by rfl) ⟨215574, by rfl⟩ : syracuseStep 574865 = 431149) B431149
theorem B378275 : Blo 251819 378275 := bstep (se 1 (by rfl) ⟨283706, by rfl⟩ : syracuseStep 378275 = 567413) B567413
theorem B574883 : Blo 251819 574883 := bstep (se 1 (by rfl) ⟨431162, by rfl⟩ : syracuseStep 574883 = 862325) B862325
theorem B378305 : Blo 251819 378305 := bstep (se 2 (by rfl) ⟨141864, by rfl⟩ : syracuseStep 378305 = 283729) B283729
theorem B378323 : Blo 251819 378323 := bstep (se 1 (by rfl) ⟨283742, by rfl⟩ : syracuseStep 378323 = 567485) B567485
theorem B378353 : Blo 251819 378353 := bstep (se 2 (by rfl) ⟨141882, by rfl⟩ : syracuseStep 378353 = 283765) B283765
theorem B378371 : Blo 251819 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B378401 : Blo 251819 378401 := bstep (se 2 (by rfl) ⟨141900, by rfl⟩ : syracuseStep 378401 = 283801) B283801
theorem B378419 : Blo 251819 378419 := bstep (se 1 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 378419 = 567629) B567629
theorem B378449 : Blo 251819 378449 := bstep (se 2 (by rfl) ⟨141918, by rfl⟩ : syracuseStep 378449 = 283837) B283837
theorem B378467 : Blo 251819 378467 := bstep (se 1 (by rfl) ⟨283850, by rfl⟩ : syracuseStep 378467 = 567701) B567701
theorem B378497 : Blo 251819 378497 := bstep (se 2 (by rfl) ⟨141936, by rfl⟩ : syracuseStep 378497 = 283873) B283873
theorem B378515 : Blo 251819 378515 := bstep (se 1 (by rfl) ⟨283886, by rfl⟩ : syracuseStep 378515 = 567773) B567773
theorem B378545 : Blo 251819 378545 := bstep (se 2 (by rfl) ⟨141954, by rfl⟩ : syracuseStep 378545 = 283909) B283909
theorem B575153 : Blo 251819 575153 := bstep (se 2 (by rfl) ⟨215682, by rfl⟩ : syracuseStep 575153 = 431365) B431365
theorem B378563 : Blo 251819 378563 := bstep (se 1 (by rfl) ⟨283922, by rfl⟩ : syracuseStep 378563 = 567845) B567845
theorem B575171 : Blo 251819 575171 := bstep (se 1 (by rfl) ⟨431378, by rfl⟩ : syracuseStep 575171 = 862757) B862757
theorem B378593 : Blo 251819 378593 := bstep (se 2 (by rfl) ⟨141972, by rfl⟩ : syracuseStep 378593 = 283945) B283945
theorem B378611 : Blo 251819 378611 := bstep (se 1 (by rfl) ⟨283958, by rfl⟩ : syracuseStep 378611 = 567917) B567917
theorem B3131149 : Blo 251819 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B378641 : Blo 251819 378641 := bstep (se 2 (by rfl) ⟨141990, by rfl⟩ : syracuseStep 378641 = 283981) B283981
theorem B378659 : Blo 251819 378659 := bstep (se 1 (by rfl) ⟨283994, by rfl⟩ : syracuseStep 378659 = 567989) B567989
theorem B542513 : Blo 251819 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B378689 : Blo 251819 378689 := bstep (se 2 (by rfl) ⟨142008, by rfl⟩ : syracuseStep 378689 = 284017) B284017
theorem B542531 : Blo 251819 542531 := bstep (se 1 (by rfl) ⟨406898, by rfl⟩ : syracuseStep 542531 = 813797) B813797
theorem B378707 : Blo 251819 378707 := bstep (se 1 (by rfl) ⟨284030, by rfl⟩ : syracuseStep 378707 = 568061) B568061
theorem B378737 : Blo 251819 378737 := bstep (se 2 (by rfl) ⟨142026, by rfl⟩ : syracuseStep 378737 = 284053) B284053
theorem B2443121 : Blo 251819 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B378755 : Blo 251819 378755 := bstep (se 1 (by rfl) ⟨284066, by rfl⟩ : syracuseStep 378755 = 568133) B568133
theorem B378785 : Blo 251819 378785 := bstep (se 2 (by rfl) ⟨142044, by rfl⟩ : syracuseStep 378785 = 284089) B284089
theorem B378803 : Blo 251819 378803 := bstep (se 1 (by rfl) ⟨284102, by rfl⟩ : syracuseStep 378803 = 568205) B568205
theorem B378833 : Blo 251819 378833 := bstep (se 2 (by rfl) ⟨142062, by rfl⟩ : syracuseStep 378833 = 284125) B284125
theorem B575441 : Blo 251819 575441 := bstep (se 2 (by rfl) ⟨215790, by rfl⟩ : syracuseStep 575441 = 431581) B431581
theorem B378851 : Blo 251819 378851 := bstep (se 1 (by rfl) ⟨284138, by rfl⟩ : syracuseStep 378851 = 568277) B568277
theorem B575459 : Blo 251819 575459 := bstep (se 1 (by rfl) ⟨431594, by rfl⟩ : syracuseStep 575459 = 863189) B863189
theorem B378881 : Blo 251819 378881 := bstep (se 2 (by rfl) ⟨142080, by rfl⟩ : syracuseStep 378881 = 284161) B284161
theorem B378899 : Blo 251819 378899 := bstep (se 1 (by rfl) ⟨284174, by rfl⟩ : syracuseStep 378899 = 568349) B568349
theorem B378929 : Blo 251819 378929 := bstep (se 2 (by rfl) ⟨142098, by rfl⟩ : syracuseStep 378929 = 284197) B284197
theorem B378947 : Blo 251819 378947 := bstep (se 1 (by rfl) ⟨284210, by rfl⟩ : syracuseStep 378947 = 568421) B568421
theorem B641105 : Blo 251819 641105 := bstep (se 2 (by rfl) ⟨240414, by rfl⟩ : syracuseStep 641105 = 480829) B480829
theorem B378977 : Blo 251819 378977 := bstep (se 2 (by rfl) ⟨142116, by rfl⟩ : syracuseStep 378977 = 284233) B284233
theorem B3295331 : Blo 251819 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B378995 : Blo 251819 378995 := bstep (se 1 (by rfl) ⟨284246, by rfl⟩ : syracuseStep 378995 = 568493) B568493
theorem B641155 : Blo 251819 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B379025 : Blo 251819 379025 := bstep (se 2 (by rfl) ⟨142134, by rfl⟩ : syracuseStep 379025 = 284269) B284269
theorem B379043 : Blo 251819 379043 := bstep (se 1 (by rfl) ⟨284282, by rfl⟩ : syracuseStep 379043 = 568565) B568565
theorem B379073 : Blo 251819 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B379091 : Blo 251819 379091 := bstep (se 1 (by rfl) ⟨284318, by rfl⟩ : syracuseStep 379091 = 568637) B568637
theorem B379121 : Blo 251819 379121 := bstep (se 2 (by rfl) ⟨142170, by rfl⟩ : syracuseStep 379121 = 284341) B284341
theorem B379139 : Blo 251819 379139 := bstep (se 1 (by rfl) ⟨284354, by rfl⟩ : syracuseStep 379139 = 568709) B568709
theorem B641297 : Blo 251819 641297 := bstep (se 2 (by rfl) ⟨240486, by rfl⟩ : syracuseStep 641297 = 480973) B480973
theorem B9324821 : Blo 251819 9324821 := bstep (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) B437101
theorem B379169 : Blo 251819 379169 := bstep (se 2 (by rfl) ⟨142188, by rfl⟩ : syracuseStep 379169 = 284377) B284377
theorem B379187 : Blo 251819 379187 := bstep (se 1 (by rfl) ⟨284390, by rfl⟩ : syracuseStep 379187 = 568781) B568781
theorem B379217 : Blo 251819 379217 := bstep (se 2 (by rfl) ⟨142206, by rfl⟩ : syracuseStep 379217 = 284413) B284413
theorem B379235 : Blo 251819 379235 := bstep (se 1 (by rfl) ⟨284426, by rfl⟩ : syracuseStep 379235 = 568853) B568853
theorem B379265 : Blo 251819 379265 := bstep (se 2 (by rfl) ⟨142224, by rfl⟩ : syracuseStep 379265 = 284449) B284449
theorem B379283 : Blo 251819 379283 := bstep (se 1 (by rfl) ⟨284462, by rfl⟩ : syracuseStep 379283 = 568925) B568925
theorem B379313 : Blo 251819 379313 := bstep (se 2 (by rfl) ⟨142242, by rfl⟩ : syracuseStep 379313 = 284485) B284485
theorem B379331 : Blo 251819 379331 := bstep (se 1 (by rfl) ⟨284498, by rfl⟩ : syracuseStep 379331 = 568997) B568997
theorem B379361 : Blo 251819 379361 := bstep (se 2 (by rfl) ⟨142260, by rfl⟩ : syracuseStep 379361 = 284521) B284521
theorem B379379 : Blo 251819 379379 := bstep (se 1 (by rfl) ⟨284534, by rfl⟩ : syracuseStep 379379 = 569069) B569069
theorem B379409 : Blo 251819 379409 := bstep (se 2 (by rfl) ⟨142278, by rfl⟩ : syracuseStep 379409 = 284557) B284557
theorem B379427 : Blo 251819 379427 := bstep (se 1 (by rfl) ⟨284570, by rfl⟩ : syracuseStep 379427 = 569141) B569141
theorem B379457 : Blo 251819 379457 := bstep (se 2 (by rfl) ⟨142296, by rfl⟩ : syracuseStep 379457 = 284593) B284593
theorem B379475 : Blo 251819 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B608867 : Blo 251819 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B379505 : Blo 251819 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B379523 : Blo 251819 379523 := bstep (se 1 (by rfl) ⟨284642, by rfl⟩ : syracuseStep 379523 = 569285) B569285
theorem B379553 : Blo 251819 379553 := bstep (se 2 (by rfl) ⟨142332, by rfl⟩ : syracuseStep 379553 = 284665) B284665
theorem B379571 : Blo 251819 379571 := bstep (se 1 (by rfl) ⟨284678, by rfl⟩ : syracuseStep 379571 = 569357) B569357
theorem B379601 : Blo 251819 379601 := bstep (se 2 (by rfl) ⟨142350, by rfl⟩ : syracuseStep 379601 = 284701) B284701
theorem B379619 : Blo 251819 379619 := bstep (se 1 (by rfl) ⟨284714, by rfl⟩ : syracuseStep 379619 = 569429) B569429
theorem B379649 : Blo 251819 379649 := bstep (se 2 (by rfl) ⟨142368, by rfl⟩ : syracuseStep 379649 = 284737) B284737
theorem B379667 : Blo 251819 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B609059 : Blo 251819 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B379697 : Blo 251819 379697 := bstep (se 2 (by rfl) ⟨142386, by rfl⟩ : syracuseStep 379697 = 284773) B284773
theorem B379715 : Blo 251819 379715 := bstep (se 1 (by rfl) ⟨284786, by rfl⟩ : syracuseStep 379715 = 569573) B569573
theorem B379745 : Blo 251819 379745 := bstep (se 2 (by rfl) ⟨142404, by rfl⟩ : syracuseStep 379745 = 284809) B284809
theorem B379763 : Blo 251819 379763 := bstep (se 1 (by rfl) ⟨284822, by rfl⟩ : syracuseStep 379763 = 569645) B569645
theorem B379793 : Blo 251819 379793 := bstep (se 2 (by rfl) ⟨142422, by rfl⟩ : syracuseStep 379793 = 284845) B284845
theorem B379811 : Blo 251819 379811 := bstep (se 1 (by rfl) ⟨284858, by rfl⟩ : syracuseStep 379811 = 569717) B569717
theorem B379841 : Blo 251819 379841 := bstep (se 2 (by rfl) ⟨142440, by rfl⟩ : syracuseStep 379841 = 284881) B284881
theorem B969677 : Blo 251819 969677 := bstep (se 3 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 969677 = 363629) B363629
theorem B379859 : Blo 251819 379859 := bstep (se 1 (by rfl) ⟨284894, by rfl⟩ : syracuseStep 379859 = 569789) B569789
theorem B379889 : Blo 251819 379889 := bstep (se 2 (by rfl) ⟨142458, by rfl⟩ : syracuseStep 379889 = 284917) B284917
theorem B379907 : Blo 251819 379907 := bstep (se 1 (by rfl) ⟨284930, by rfl⟩ : syracuseStep 379907 = 569861) B569861
theorem B379937 : Blo 251819 379937 := bstep (se 2 (by rfl) ⟨142476, by rfl⟩ : syracuseStep 379937 = 284953) B284953
theorem B379955 : Blo 251819 379955 := bstep (se 1 (by rfl) ⟨284966, by rfl⟩ : syracuseStep 379955 = 569933) B569933
theorem B379985 : Blo 251819 379985 := bstep (se 2 (by rfl) ⟨142494, by rfl⟩ : syracuseStep 379985 = 284989) B284989
theorem B380003 : Blo 251819 380003 := bstep (se 1 (by rfl) ⟨285002, by rfl⟩ : syracuseStep 380003 = 570005) B570005
theorem B380033 : Blo 251819 380033 := bstep (se 2 (by rfl) ⟨142512, by rfl⟩ : syracuseStep 380033 = 285025) B285025
theorem B380051 : Blo 251819 380051 := bstep (se 1 (by rfl) ⟨285038, by rfl⟩ : syracuseStep 380051 = 570077) B570077
theorem B380081 : Blo 251819 380081 := bstep (se 2 (by rfl) ⟨142530, by rfl⟩ : syracuseStep 380081 = 285061) B285061
theorem B380099 : Blo 251819 380099 := bstep (se 1 (by rfl) ⟨285074, by rfl⟩ : syracuseStep 380099 = 570149) B570149
theorem B380129 : Blo 251819 380129 := bstep (se 2 (by rfl) ⟨142548, by rfl⟩ : syracuseStep 380129 = 285097) B285097
theorem B871661 : Blo 251819 871661 := bstep (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) B326873
theorem B642289 : Blo 251819 642289 := bstep (se 2 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 642289 = 481717) B481717
theorem B380147 : Blo 251819 380147 := bstep (se 1 (by rfl) ⟨285110, by rfl⟩ : syracuseStep 380147 = 570221) B570221
theorem B380177 : Blo 251819 380177 := bstep (se 2 (by rfl) ⟨142566, by rfl⟩ : syracuseStep 380177 = 285133) B285133
theorem B380195 : Blo 251819 380195 := bstep (se 1 (by rfl) ⟨285146, by rfl⟩ : syracuseStep 380195 = 570293) B570293
theorem B380225 : Blo 251819 380225 := bstep (se 2 (by rfl) ⟨142584, by rfl⟩ : syracuseStep 380225 = 285169) B285169
theorem B380243 : Blo 251819 380243 := bstep (se 1 (by rfl) ⟨285182, by rfl⟩ : syracuseStep 380243 = 570365) B570365
theorem B511331 : Blo 251819 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B3231089 : Blo 251819 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B380273 : Blo 251819 380273 := bstep (se 2 (by rfl) ⟨142602, by rfl⟩ : syracuseStep 380273 = 285205) B285205
theorem B380291 : Blo 251819 380291 := bstep (se 1 (by rfl) ⟨285218, by rfl⟩ : syracuseStep 380291 = 570437) B570437
theorem B3165581 : Blo 251819 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B380321 : Blo 251819 380321 := bstep (se 2 (by rfl) ⟨142620, by rfl⟩ : syracuseStep 380321 = 285241) B285241
theorem B609713 : Blo 251819 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B380339 : Blo 251819 380339 := bstep (se 1 (by rfl) ⟨285254, by rfl⟩ : syracuseStep 380339 = 570509) B570509
theorem B380369 : Blo 251819 380369 := bstep (se 2 (by rfl) ⟨142638, by rfl⟩ : syracuseStep 380369 = 285277) B285277
theorem B380387 : Blo 251819 380387 := bstep (se 1 (by rfl) ⟨285290, by rfl⟩ : syracuseStep 380387 = 570581) B570581
theorem B380417 : Blo 251819 380417 := bstep (se 2 (by rfl) ⟨142656, by rfl⟩ : syracuseStep 380417 = 285313) B285313
theorem B642563 : Blo 251819 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B380435 : Blo 251819 380435 := bstep (se 1 (by rfl) ⟨285326, by rfl⟩ : syracuseStep 380435 = 570653) B570653
theorem B380465 : Blo 251819 380465 := bstep (se 2 (by rfl) ⟨142674, by rfl⟩ : syracuseStep 380465 = 285349) B285349
theorem B577091 : Blo 251819 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B380483 : Blo 251819 380483 := bstep (se 1 (by rfl) ⟨285362, by rfl⟩ : syracuseStep 380483 = 570725) B570725
theorem B478801 : Blo 251819 478801 := bstep (se 2 (by rfl) ⟨179550, by rfl⟩ : syracuseStep 478801 = 359101) B359101
theorem B380513 : Blo 251819 380513 := bstep (se 2 (by rfl) ⟨142692, by rfl⟩ : syracuseStep 380513 = 285385) B285385
theorem B380531 : Blo 251819 380531 := bstep (se 1 (by rfl) ⟨285398, by rfl⟩ : syracuseStep 380531 = 570797) B570797
theorem B380561 : Blo 251819 380561 := bstep (se 2 (by rfl) ⟨142710, by rfl⟩ : syracuseStep 380561 = 285421) B285421
theorem B380579 : Blo 251819 380579 := bstep (se 1 (by rfl) ⟨285434, by rfl⟩ : syracuseStep 380579 = 570869) B570869
theorem B380609 : Blo 251819 380609 := bstep (se 2 (by rfl) ⟨142728, by rfl⟩ : syracuseStep 380609 = 285457) B285457
theorem B577219 : Blo 251819 577219 := bstep (se 1 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 577219 = 865829) B865829
theorem B642755 : Blo 251819 642755 := bstep (se 1 (by rfl) ⟨482066, by rfl⟩ : syracuseStep 642755 = 964133) B964133
theorem B380627 : Blo 251819 380627 := bstep (se 1 (by rfl) ⟨285470, by rfl⟩ : syracuseStep 380627 = 570941) B570941
theorem B380657 : Blo 251819 380657 := bstep (se 2 (by rfl) ⟨142746, by rfl⟩ : syracuseStep 380657 = 285493) B285493
theorem B970481 : Blo 251819 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B380675 : Blo 251819 380675 := bstep (se 1 (by rfl) ⟨285506, by rfl⟩ : syracuseStep 380675 = 571013) B571013
theorem B544529 : Blo 251819 544529 := bstep (se 2 (by rfl) ⟨204198, by rfl⟩ : syracuseStep 544529 = 408397) B408397
theorem B380705 : Blo 251819 380705 := bstep (se 2 (by rfl) ⟨142764, by rfl⟩ : syracuseStep 380705 = 285529) B285529
theorem B380723 : Blo 251819 380723 := bstep (se 1 (by rfl) ⟨285542, by rfl⟩ : syracuseStep 380723 = 571085) B571085
theorem B380753 : Blo 251819 380753 := bstep (se 2 (by rfl) ⟨142782, by rfl⟩ : syracuseStep 380753 = 285565) B285565
theorem B380771 : Blo 251819 380771 := bstep (se 1 (by rfl) ⟨285578, by rfl⟩ : syracuseStep 380771 = 571157) B571157
theorem B380801 : Blo 251819 380801 := bstep (se 2 (by rfl) ⟨142800, by rfl⟩ : syracuseStep 380801 = 285601) B285601
theorem B380819 : Blo 251819 380819 := bstep (se 1 (by rfl) ⟨285614, by rfl⟩ : syracuseStep 380819 = 571229) B571229
theorem B380849 : Blo 251819 380849 := bstep (se 2 (by rfl) ⟨142818, by rfl⟩ : syracuseStep 380849 = 285637) B285637
theorem B380867 : Blo 251819 380867 := bstep (se 1 (by rfl) ⟨285650, by rfl⟩ : syracuseStep 380867 = 571301) B571301
theorem B380897 : Blo 251819 380897 := bstep (se 2 (by rfl) ⟨142836, by rfl⟩ : syracuseStep 380897 = 285673) B285673
theorem B1036273 : Blo 251819 1036273 := bstep (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) B777205
theorem B380915 : Blo 251819 380915 := bstep (se 1 (by rfl) ⟨285686, by rfl⟩ : syracuseStep 380915 = 571373) B571373
theorem B380945 : Blo 251819 380945 := bstep (se 2 (by rfl) ⟨142854, by rfl⟩ : syracuseStep 380945 = 285709) B285709
theorem B380963 : Blo 251819 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B380993 : Blo 251819 380993 := bstep (se 2 (by rfl) ⟨142872, by rfl⟩ : syracuseStep 380993 = 285745) B285745
theorem B806993 : Blo 251819 806993 := bstep (se 2 (by rfl) ⟨302622, by rfl⟩ : syracuseStep 806993 = 605245) B605245
theorem B381011 : Blo 251819 381011 := bstep (se 1 (by rfl) ⟨285758, by rfl⟩ : syracuseStep 381011 = 571517) B571517
theorem B381041 : Blo 251819 381041 := bstep (se 2 (by rfl) ⟨142890, by rfl⟩ : syracuseStep 381041 = 285781) B285781
theorem B381059 : Blo 251819 381059 := bstep (se 1 (by rfl) ⟨285794, by rfl⟩ : syracuseStep 381059 = 571589) B571589
theorem B381089 : Blo 251819 381089 := bstep (se 2 (by rfl) ⟨142908, by rfl⟩ : syracuseStep 381089 = 285817) B285817
theorem B610481 : Blo 251819 610481 := bstep (se 2 (by rfl) ⟨228930, by rfl⟩ : syracuseStep 610481 = 457861) B457861
theorem B381107 : Blo 251819 381107 := bstep (se 1 (by rfl) ⟨285830, by rfl⟩ : syracuseStep 381107 = 571661) B571661
theorem B381137 : Blo 251819 381137 := bstep (se 2 (by rfl) ⟨142926, by rfl⟩ : syracuseStep 381137 = 285853) B285853
theorem B381155 : Blo 251819 381155 := bstep (se 1 (by rfl) ⟨285866, by rfl⟩ : syracuseStep 381155 = 571733) B571733
theorem B381185 : Blo 251819 381185 := bstep (se 2 (by rfl) ⟨142944, by rfl⟩ : syracuseStep 381185 = 285889) B285889
theorem B381203 : Blo 251819 381203 := bstep (se 1 (by rfl) ⟨285902, by rfl⟩ : syracuseStep 381203 = 571805) B571805
theorem B545059 : Blo 251819 545059 := bstep (se 1 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 545059 = 817589) B817589
theorem B381233 : Blo 251819 381233 := bstep (se 2 (by rfl) ⟨142962, by rfl⟩ : syracuseStep 381233 = 285925) B285925
theorem B381251 : Blo 251819 381251 := bstep (se 1 (by rfl) ⟨285938, by rfl⟩ : syracuseStep 381251 = 571877) B571877
theorem B381281 : Blo 251819 381281 := bstep (se 2 (by rfl) ⟨142980, by rfl⟩ : syracuseStep 381281 = 285961) B285961
theorem B381299 : Blo 251819 381299 := bstep (se 1 (by rfl) ⟨285974, by rfl⟩ : syracuseStep 381299 = 571949) B571949
theorem B971149 : Blo 251819 971149 := bstep (se 3 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 971149 = 364181) B364181
theorem B381329 : Blo 251819 381329 := bstep (se 2 (by rfl) ⟨142998, by rfl⟩ : syracuseStep 381329 = 285997) B285997
theorem B381347 : Blo 251819 381347 := bstep (se 1 (by rfl) ⟨286010, by rfl⟩ : syracuseStep 381347 = 572021) B572021
theorem B381377 : Blo 251819 381377 := bstep (se 2 (by rfl) ⟨143016, by rfl⟩ : syracuseStep 381377 = 286033) B286033
theorem B381395 : Blo 251819 381395 := bstep (se 1 (by rfl) ⟨286046, by rfl⟩ : syracuseStep 381395 = 572093) B572093
theorem B381425 : Blo 251819 381425 := bstep (se 2 (by rfl) ⟨143034, by rfl⟩ : syracuseStep 381425 = 286069) B286069
theorem B381443 : Blo 251819 381443 := bstep (se 1 (by rfl) ⟨286082, by rfl⟩ : syracuseStep 381443 = 572165) B572165
theorem B381473 : Blo 251819 381473 := bstep (se 2 (by rfl) ⟨143052, by rfl⟩ : syracuseStep 381473 = 286105) B286105
theorem B381491 : Blo 251819 381491 := bstep (se 1 (by rfl) ⟨286118, by rfl⟩ : syracuseStep 381491 = 572237) B572237
theorem B381521 : Blo 251819 381521 := bstep (se 2 (by rfl) ⟨143070, by rfl⟩ : syracuseStep 381521 = 286141) B286141
theorem B381539 : Blo 251819 381539 := bstep (se 1 (by rfl) ⟨286154, by rfl⟩ : syracuseStep 381539 = 572309) B572309
theorem B479857 : Blo 251819 479857 := bstep (se 2 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 479857 = 359893) B359893
theorem B643697 : Blo 251819 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B381569 : Blo 251819 381569 := bstep (se 2 (by rfl) ⟨143088, by rfl⟩ : syracuseStep 381569 = 286177) B286177
theorem B381587 : Blo 251819 381587 := bstep (se 1 (by rfl) ⟨286190, by rfl⟩ : syracuseStep 381587 = 572381) B572381
theorem B643747 : Blo 251819 643747 := bstep (se 1 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 643747 = 965621) B965621
theorem B381617 : Blo 251819 381617 := bstep (se 2 (by rfl) ⟨143106, by rfl⟩ : syracuseStep 381617 = 286213) B286213
theorem B283315 : Blo 251819 283315 := bstep (se 1 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 283315 = 424973) B424973
theorem B381635 : Blo 251819 381635 := bstep (se 1 (by rfl) ⟨286226, by rfl⟩ : syracuseStep 381635 = 572453) B572453
theorem B381665 : Blo 251819 381665 := bstep (se 2 (by rfl) ⟨143124, by rfl⟩ : syracuseStep 381665 = 286249) B286249
theorem B381683 : Blo 251819 381683 := bstep (se 1 (by rfl) ⟨286262, by rfl⟩ : syracuseStep 381683 = 572525) B572525
theorem B381713 : Blo 251819 381713 := bstep (se 2 (by rfl) ⟨143142, by rfl⟩ : syracuseStep 381713 = 286285) B286285
theorem B381731 : Blo 251819 381731 := bstep (se 1 (by rfl) ⟨286298, by rfl⟩ : syracuseStep 381731 = 572597) B572597
theorem B643889 : Blo 251819 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B381761 : Blo 251819 381761 := bstep (se 2 (by rfl) ⟨143160, by rfl⟩ : syracuseStep 381761 = 286321) B286321
theorem B283459 : Blo 251819 283459 := bstep (se 1 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 283459 = 425189) B425189
theorem B381779 : Blo 251819 381779 := bstep (se 1 (by rfl) ⟨286334, by rfl⟩ : syracuseStep 381779 = 572669) B572669
theorem B1364849 : Blo 251819 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B381809 : Blo 251819 381809 := bstep (se 2 (by rfl) ⟨143178, by rfl⟩ : syracuseStep 381809 = 286357) B286357
theorem B381827 : Blo 251819 381827 := bstep (se 1 (by rfl) ⟨286370, by rfl⟩ : syracuseStep 381827 = 572741) B572741
theorem B381857 : Blo 251819 381857 := bstep (se 2 (by rfl) ⟨143196, by rfl⟩ : syracuseStep 381857 = 286393) B286393
theorem B381875 : Blo 251819 381875 := bstep (se 1 (by rfl) ⟨286406, by rfl⟩ : syracuseStep 381875 = 572813) B572813
theorem B381905 : Blo 251819 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B283603 : Blo 251819 283603 := bstep (se 1 (by rfl) ⟨212702, by rfl⟩ : syracuseStep 283603 = 425405) B425405
theorem B381923 : Blo 251819 381923 := bstep (se 1 (by rfl) ⟨286442, by rfl⟩ : syracuseStep 381923 = 572885) B572885
theorem B381953 : Blo 251819 381953 := bstep (se 2 (by rfl) ⟨143232, by rfl⟩ : syracuseStep 381953 = 286465) B286465
theorem B480259 : Blo 251819 480259 := bstep (se 1 (by rfl) ⟨360194, by rfl⟩ : syracuseStep 480259 = 720389) B720389
theorem B381971 : Blo 251819 381971 := bstep (se 1 (by rfl) ⟨286478, by rfl⟩ : syracuseStep 381971 = 572957) B572957
theorem B480305 : Blo 251819 480305 := bstep (se 2 (by rfl) ⟨180114, by rfl⟩ : syracuseStep 480305 = 360229) B360229
theorem B382001 : Blo 251819 382001 := bstep (se 2 (by rfl) ⟨143250, by rfl⟩ : syracuseStep 382001 = 286501) B286501
theorem B382019 : Blo 251819 382019 := bstep (se 1 (by rfl) ⟨286514, by rfl⟩ : syracuseStep 382019 = 573029) B573029
theorem B382049 : Blo 251819 382049 := bstep (se 2 (by rfl) ⟨143268, by rfl⟩ : syracuseStep 382049 = 286537) B286537
theorem B283747 : Blo 251819 283747 := bstep (se 1 (by rfl) ⟨212810, by rfl⟩ : syracuseStep 283747 = 425621) B425621
theorem B382067 : Blo 251819 382067 := bstep (se 1 (by rfl) ⟨286550, by rfl⟩ : syracuseStep 382067 = 573101) B573101
theorem B382097 : Blo 251819 382097 := bstep (se 2 (by rfl) ⟨143286, by rfl⟩ : syracuseStep 382097 = 286573) B286573
theorem B873635 : Blo 251819 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B382115 : Blo 251819 382115 := bstep (se 1 (by rfl) ⟨286586, by rfl⟩ : syracuseStep 382115 = 573173) B573173
theorem B382145 : Blo 251819 382145 := bstep (se 2 (by rfl) ⟨143304, by rfl⟩ : syracuseStep 382145 = 286609) B286609
theorem B382163 : Blo 251819 382163 := bstep (se 1 (by rfl) ⟨286622, by rfl⟩ : syracuseStep 382163 = 573245) B573245
theorem B382193 : Blo 251819 382193 := bstep (se 2 (by rfl) ⟨143322, by rfl⟩ : syracuseStep 382193 = 286645) B286645
theorem B283891 : Blo 251819 283891 := bstep (se 1 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 283891 = 425837) B425837
theorem B382211 : Blo 251819 382211 := bstep (se 1 (by rfl) ⟨286658, by rfl⟩ : syracuseStep 382211 = 573317) B573317
theorem B382241 : Blo 251819 382241 := bstep (se 2 (by rfl) ⟨143340, by rfl⟩ : syracuseStep 382241 = 286681) B286681
theorem B382259 : Blo 251819 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B480593 : Blo 251819 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B382289 : Blo 251819 382289 := bstep (se 2 (by rfl) ⟨143358, by rfl⟩ : syracuseStep 382289 = 286717) B286717
theorem B382307 : Blo 251819 382307 := bstep (se 1 (by rfl) ⟨286730, by rfl⟩ : syracuseStep 382307 = 573461) B573461
theorem B382337 : Blo 251819 382337 := bstep (se 2 (by rfl) ⟨143376, by rfl⟩ : syracuseStep 382337 = 286753) B286753
theorem B284035 : Blo 251819 284035 := bstep (se 1 (by rfl) ⟨213026, by rfl⟩ : syracuseStep 284035 = 426053) B426053
theorem B382355 : Blo 251819 382355 := bstep (se 1 (by rfl) ⟨286766, by rfl⟩ : syracuseStep 382355 = 573533) B573533
theorem B382385 : Blo 251819 382385 := bstep (se 2 (by rfl) ⟨143394, by rfl⟩ : syracuseStep 382385 = 286789) B286789
theorem B382403 : Blo 251819 382403 := bstep (se 1 (by rfl) ⟨286802, by rfl⟩ : syracuseStep 382403 = 573605) B573605
theorem B382433 : Blo 251819 382433 := bstep (se 2 (by rfl) ⟨143412, by rfl⟩ : syracuseStep 382433 = 286825) B286825
theorem B382451 : Blo 251819 382451 := bstep (se 1 (by rfl) ⟨286838, by rfl⟩ : syracuseStep 382451 = 573677) B573677
theorem B382481 : Blo 251819 382481 := bstep (se 2 (by rfl) ⟨143430, by rfl⟩ : syracuseStep 382481 = 286861) B286861
theorem B284179 : Blo 251819 284179 := bstep (se 1 (by rfl) ⟨213134, by rfl⟩ : syracuseStep 284179 = 426269) B426269
theorem B382499 : Blo 251819 382499 := bstep (se 1 (by rfl) ⟨286874, by rfl⟩ : syracuseStep 382499 = 573749) B573749
theorem B382529 : Blo 251819 382529 := bstep (se 2 (by rfl) ⟨143448, by rfl⟩ : syracuseStep 382529 = 286897) B286897
theorem B382547 : Blo 251819 382547 := bstep (se 1 (by rfl) ⟨286910, by rfl⟩ : syracuseStep 382547 = 573821) B573821
theorem B382577 : Blo 251819 382577 := bstep (se 2 (by rfl) ⟨143466, by rfl⟩ : syracuseStep 382577 = 286933) B286933
theorem B382595 : Blo 251819 382595 := bstep (se 1 (by rfl) ⟨286946, by rfl⟩ : syracuseStep 382595 = 573893) B573893
theorem B382625 : Blo 251819 382625 := bstep (se 2 (by rfl) ⟨143484, by rfl⟩ : syracuseStep 382625 = 286969) B286969
theorem B284323 : Blo 251819 284323 := bstep (se 1 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 284323 = 426485) B426485
theorem B382643 : Blo 251819 382643 := bstep (se 1 (by rfl) ⟨286982, by rfl⟩ : syracuseStep 382643 = 573965) B573965
theorem B382673 : Blo 251819 382673 := bstep (se 2 (by rfl) ⟨143502, by rfl⟩ : syracuseStep 382673 = 287005) B287005
theorem B382691 : Blo 251819 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B382721 : Blo 251819 382721 := bstep (se 2 (by rfl) ⟨143520, by rfl⟩ : syracuseStep 382721 = 287041) B287041
theorem B2447117 : Blo 251819 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B644881 : Blo 251819 644881 := bstep (se 2 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 644881 = 483661) B483661
theorem B382739 : Blo 251819 382739 := bstep (se 1 (by rfl) ⟨287054, by rfl⟩ : syracuseStep 382739 = 574109) B574109
theorem B382769 : Blo 251819 382769 := bstep (se 2 (by rfl) ⟨143538, by rfl⟩ : syracuseStep 382769 = 287077) B287077
theorem B284467 : Blo 251819 284467 := bstep (se 1 (by rfl) ⟨213350, by rfl⟩ : syracuseStep 284467 = 426701) B426701
theorem B382787 : Blo 251819 382787 := bstep (se 1 (by rfl) ⟨287090, by rfl⟩ : syracuseStep 382787 = 574181) B574181
theorem B382817 : Blo 251819 382817 := bstep (se 2 (by rfl) ⟨143556, by rfl⟩ : syracuseStep 382817 = 287113) B287113
theorem B382835 : Blo 251819 382835 := bstep (se 1 (by rfl) ⟨287126, by rfl⟩ : syracuseStep 382835 = 574253) B574253
theorem B382865 : Blo 251819 382865 := bstep (se 2 (by rfl) ⟨143574, by rfl⟩ : syracuseStep 382865 = 287149) B287149
theorem B1464227 : Blo 251819 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B382883 : Blo 251819 382883 := bstep (se 1 (by rfl) ⟨287162, by rfl⟩ : syracuseStep 382883 = 574325) B574325
theorem B251827 : Blo 251819 251827 := bstep (se 1 (by rfl) ⟨188870, by rfl⟩ : syracuseStep 251827 = 377741) B377741
theorem B382913 : Blo 251819 382913 := bstep (se 2 (by rfl) ⟨143592, by rfl⟩ : syracuseStep 382913 = 287185) B287185
theorem B382915 : Blo 251819 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B251843 : Blo 251819 251843 := bstep (se 1 (by rfl) ⟨188882, by rfl⟩ : syracuseStep 251843 = 377765) B377765
theorem B284611 : Blo 251819 284611 := bstep (se 1 (by rfl) ⟨213458, by rfl⟩ : syracuseStep 284611 = 426917) B426917
theorem B251859 : Blo 251819 251859 := bstep (se 1 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 251859 = 377789) B377789
theorem B382931 : Blo 251819 382931 := bstep (se 1 (by rfl) ⟨287198, by rfl⟩ : syracuseStep 382931 = 574397) B574397
theorem B251875 : Blo 251819 251875 := bstep (se 1 (by rfl) ⟨188906, by rfl⟩ : syracuseStep 251875 = 377813) B377813
theorem B382961 : Blo 251819 382961 := bstep (se 2 (by rfl) ⟨143610, by rfl⟩ : syracuseStep 382961 = 287221) B287221
theorem B251891 : Blo 251819 251891 := bstep (se 1 (by rfl) ⟨188918, by rfl⟩ : syracuseStep 251891 = 377837) B377837
theorem B251907 : Blo 251819 251907 := bstep (se 1 (by rfl) ⟨188930, by rfl⟩ : syracuseStep 251907 = 377861) B377861
theorem B382979 : Blo 251819 382979 := bstep (se 1 (by rfl) ⟨287234, by rfl⟩ : syracuseStep 382979 = 574469) B574469
theorem B251923 : Blo 251819 251923 := bstep (se 1 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 251923 = 377885) B377885
theorem B383009 : Blo 251819 383009 := bstep (se 2 (by rfl) ⟨143628, by rfl⟩ : syracuseStep 383009 = 287257) B287257
theorem B645155 : Blo 251819 645155 := bstep (se 1 (by rfl) ⟨483866, by rfl⟩ : syracuseStep 645155 = 967733) B967733
theorem B251939 : Blo 251819 251939 := bstep (se 1 (by rfl) ⟨188954, by rfl⟩ : syracuseStep 251939 = 377909) B377909
theorem B481315 : Blo 251819 481315 := bstep (se 1 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 481315 = 721973) B721973
theorem B251955 : Blo 251819 251955 := bstep (se 1 (by rfl) ⟨188966, by rfl⟩ : syracuseStep 251955 = 377933) B377933
theorem B383027 : Blo 251819 383027 := bstep (se 1 (by rfl) ⟨287270, by rfl⟩ : syracuseStep 383027 = 574541) B574541
theorem B251971 : Blo 251819 251971 := bstep (se 1 (by rfl) ⟨188978, by rfl⟩ : syracuseStep 251971 = 377957) B377957
theorem B383057 : Blo 251819 383057 := bstep (se 2 (by rfl) ⟨143646, by rfl⟩ : syracuseStep 383057 = 287293) B287293
theorem B251987 : Blo 251819 251987 := bstep (se 1 (by rfl) ⟨188990, by rfl⟩ : syracuseStep 251987 = 377981) B377981
theorem B284755 : Blo 251819 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B252003 : Blo 251819 252003 := bstep (se 1 (by rfl) ⟨189002, by rfl⟩ : syracuseStep 252003 = 378005) B378005
theorem B2447459 : Blo 251819 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B383075 : Blo 251819 383075 := bstep (se 1 (by rfl) ⟨287306, by rfl⟩ : syracuseStep 383075 = 574613) B574613
theorem B252019 : Blo 251819 252019 := bstep (se 1 (by rfl) ⟨189014, by rfl⟩ : syracuseStep 252019 = 378029) B378029
theorem B383105 : Blo 251819 383105 := bstep (se 2 (by rfl) ⟨143664, by rfl⟩ : syracuseStep 383105 = 287329) B287329
theorem B252035 : Blo 251819 252035 := bstep (se 1 (by rfl) ⟨189026, by rfl⟩ : syracuseStep 252035 = 378053) B378053
theorem B252051 : Blo 251819 252051 := bstep (se 1 (by rfl) ⟨189038, by rfl⟩ : syracuseStep 252051 = 378077) B378077
theorem B383123 : Blo 251819 383123 := bstep (se 1 (by rfl) ⟨287342, by rfl⟩ : syracuseStep 383123 = 574685) B574685
theorem B252067 : Blo 251819 252067 := bstep (se 1 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 252067 = 378101) B378101
theorem B383153 : Blo 251819 383153 := bstep (se 2 (by rfl) ⟨143682, by rfl⟩ : syracuseStep 383153 = 287365) B287365
theorem B252083 : Blo 251819 252083 := bstep (se 1 (by rfl) ⟨189062, by rfl⟩ : syracuseStep 252083 = 378125) B378125
theorem B252099 : Blo 251819 252099 := bstep (se 1 (by rfl) ⟨189074, by rfl⟩ : syracuseStep 252099 = 378149) B378149
theorem B383171 : Blo 251819 383171 := bstep (se 1 (by rfl) ⟨287378, by rfl⟩ : syracuseStep 383171 = 574757) B574757
theorem B252115 : Blo 251819 252115 := bstep (se 1 (by rfl) ⟨189086, by rfl⟩ : syracuseStep 252115 = 378173) B378173
theorem B383201 : Blo 251819 383201 := bstep (se 2 (by rfl) ⟨143700, by rfl⟩ : syracuseStep 383201 = 287401) B287401
theorem B252131 : Blo 251819 252131 := bstep (se 1 (by rfl) ⟨189098, by rfl⟩ : syracuseStep 252131 = 378197) B378197
theorem B284899 : Blo 251819 284899 := bstep (se 1 (by rfl) ⟨213674, by rfl⟩ : syracuseStep 284899 = 427349) B427349
theorem B645347 : Blo 251819 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B252147 : Blo 251819 252147 := bstep (se 1 (by rfl) ⟨189110, by rfl⟩ : syracuseStep 252147 = 378221) B378221
theorem B383219 : Blo 251819 383219 := bstep (se 1 (by rfl) ⟨287414, by rfl⟩ : syracuseStep 383219 = 574829) B574829
theorem B252163 : Blo 251819 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B776461 : Blo 251819 776461 := bstep (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) B291173
theorem B383249 : Blo 251819 383249 := bstep (se 2 (by rfl) ⟨143718, by rfl⟩ : syracuseStep 383249 = 287437) B287437
theorem B252179 : Blo 251819 252179 := bstep (se 1 (by rfl) ⟨189134, by rfl⟩ : syracuseStep 252179 = 378269) B378269
theorem B252195 : Blo 251819 252195 := bstep (se 1 (by rfl) ⟨189146, by rfl⟩ : syracuseStep 252195 = 378293) B378293
theorem B383267 : Blo 251819 383267 := bstep (se 1 (by rfl) ⟨287450, by rfl⟩ : syracuseStep 383267 = 574901) B574901
theorem B252211 : Blo 251819 252211 := bstep (se 1 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 252211 = 378317) B378317
theorem B383297 : Blo 251819 383297 := bstep (se 2 (by rfl) ⟨143736, by rfl⟩ : syracuseStep 383297 = 287473) B287473
theorem B252227 : Blo 251819 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B252243 : Blo 251819 252243 := bstep (se 1 (by rfl) ⟨189182, by rfl⟩ : syracuseStep 252243 = 378365) B378365
theorem B383315 : Blo 251819 383315 := bstep (se 1 (by rfl) ⟨287486, by rfl⟩ : syracuseStep 383315 = 574973) B574973
theorem B383329 : Blo 251819 383329 := bstep (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) B287497
theorem B252259 : Blo 251819 252259 := bstep (se 1 (by rfl) ⟨189194, by rfl⟩ : syracuseStep 252259 = 378389) B378389
theorem B383345 : Blo 251819 383345 := bstep (se 2 (by rfl) ⟨143754, by rfl⟩ : syracuseStep 383345 = 287509) B287509
theorem B252275 : Blo 251819 252275 := bstep (se 1 (by rfl) ⟨189206, by rfl⟩ : syracuseStep 252275 = 378413) B378413
theorem B285043 : Blo 251819 285043 := bstep (se 1 (by rfl) ⟨213782, by rfl⟩ : syracuseStep 285043 = 427565) B427565
theorem B252291 : Blo 251819 252291 := bstep (se 1 (by rfl) ⟨189218, by rfl⟩ : syracuseStep 252291 = 378437) B378437
theorem B383363 : Blo 251819 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B252307 : Blo 251819 252307 := bstep (se 1 (by rfl) ⟨189230, by rfl⟩ : syracuseStep 252307 = 378461) B378461
theorem B383393 : Blo 251819 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B252323 : Blo 251819 252323 := bstep (se 1 (by rfl) ⟨189242, by rfl⟩ : syracuseStep 252323 = 378485) B378485
theorem B252339 : Blo 251819 252339 := bstep (se 1 (by rfl) ⟨189254, by rfl⟩ : syracuseStep 252339 = 378509) B378509
theorem B383411 : Blo 251819 383411 := bstep (se 1 (by rfl) ⟨287558, by rfl⟩ : syracuseStep 383411 = 575117) B575117
theorem B252355 : Blo 251819 252355 := bstep (se 1 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 252355 = 378533) B378533
theorem B383441 : Blo 251819 383441 := bstep (se 2 (by rfl) ⟨143790, by rfl⟩ : syracuseStep 383441 = 287581) B287581
theorem B252371 : Blo 251819 252371 := bstep (se 1 (by rfl) ⟨189278, by rfl⟩ : syracuseStep 252371 = 378557) B378557
theorem B252387 : Blo 251819 252387 := bstep (se 1 (by rfl) ⟨189290, by rfl⟩ : syracuseStep 252387 = 378581) B378581
theorem B481763 : Blo 251819 481763 := bstep (se 1 (by rfl) ⟨361322, by rfl⟩ : syracuseStep 481763 = 722645) B722645
theorem B383459 : Blo 251819 383459 := bstep (se 1 (by rfl) ⟨287594, by rfl⟩ : syracuseStep 383459 = 575189) B575189
theorem B809453 : Blo 251819 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B252403 : Blo 251819 252403 := bstep (se 1 (by rfl) ⟨189302, by rfl⟩ : syracuseStep 252403 = 378605) B378605
theorem B383489 : Blo 251819 383489 := bstep (se 2 (by rfl) ⟨143808, by rfl⟩ : syracuseStep 383489 = 287617) B287617
theorem B252419 : Blo 251819 252419 := bstep (se 1 (by rfl) ⟨189314, by rfl⟩ : syracuseStep 252419 = 378629) B378629
theorem B285187 : Blo 251819 285187 := bstep (se 1 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 285187 = 427781) B427781
theorem B252435 : Blo 251819 252435 := bstep (se 1 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 252435 = 378653) B378653
theorem B383507 : Blo 251819 383507 := bstep (se 1 (by rfl) ⟨287630, by rfl⟩ : syracuseStep 383507 = 575261) B575261
theorem B252451 : Blo 251819 252451 := bstep (se 1 (by rfl) ⟨189338, by rfl⟩ : syracuseStep 252451 = 378677) B378677
theorem B383537 : Blo 251819 383537 := bstep (se 2 (by rfl) ⟨143826, by rfl⟩ : syracuseStep 383537 = 287653) B287653
theorem B252467 : Blo 251819 252467 := bstep (se 1 (by rfl) ⟨189350, by rfl⟩ : syracuseStep 252467 = 378701) B378701
theorem B252483 : Blo 251819 252483 := bstep (se 1 (by rfl) ⟨189362, by rfl⟩ : syracuseStep 252483 = 378725) B378725
theorem B383555 : Blo 251819 383555 := bstep (se 1 (by rfl) ⟨287666, by rfl⟩ : syracuseStep 383555 = 575333) B575333
theorem B252499 : Blo 251819 252499 := bstep (se 1 (by rfl) ⟨189374, by rfl⟩ : syracuseStep 252499 = 378749) B378749
theorem B383585 : Blo 251819 383585 := bstep (se 2 (by rfl) ⟨143844, by rfl⟩ : syracuseStep 383585 = 287689) B287689
theorem B252515 : Blo 251819 252515 := bstep (se 1 (by rfl) ⟨189386, by rfl⟩ : syracuseStep 252515 = 378773) B378773
theorem B252531 : Blo 251819 252531 := bstep (se 1 (by rfl) ⟨189398, by rfl⟩ : syracuseStep 252531 = 378797) B378797
theorem B383603 : Blo 251819 383603 := bstep (se 1 (by rfl) ⟨287702, by rfl⟩ : syracuseStep 383603 = 575405) B575405
theorem B252547 : Blo 251819 252547 := bstep (se 1 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 252547 = 378821) B378821
theorem B2153101 : Blo 251819 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B383633 : Blo 251819 383633 := bstep (se 2 (by rfl) ⟨143862, by rfl⟩ : syracuseStep 383633 = 287725) B287725
theorem B252563 : Blo 251819 252563 := bstep (se 1 (by rfl) ⟨189422, by rfl⟩ : syracuseStep 252563 = 378845) B378845
theorem B285331 : Blo 251819 285331 := bstep (se 1 (by rfl) ⟨213998, by rfl⟩ : syracuseStep 285331 = 427997) B427997
theorem B252579 : Blo 251819 252579 := bstep (se 1 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 252579 = 378869) B378869
theorem B383651 : Blo 251819 383651 := bstep (se 1 (by rfl) ⟨287738, by rfl⟩ : syracuseStep 383651 = 575477) B575477
theorem B252595 : Blo 251819 252595 := bstep (se 1 (by rfl) ⟨189446, by rfl⟩ : syracuseStep 252595 = 378893) B378893
theorem B383681 : Blo 251819 383681 := bstep (se 2 (by rfl) ⟨143880, by rfl⟩ : syracuseStep 383681 = 287761) B287761
theorem B252611 : Blo 251819 252611 := bstep (se 1 (by rfl) ⟨189458, by rfl⟩ : syracuseStep 252611 = 378917) B378917
theorem B252627 : Blo 251819 252627 := bstep (se 1 (by rfl) ⟨189470, by rfl⟩ : syracuseStep 252627 = 378941) B378941
theorem B383699 : Blo 251819 383699 := bstep (se 1 (by rfl) ⟨287774, by rfl⟩ : syracuseStep 383699 = 575549) B575549
theorem B252643 : Blo 251819 252643 := bstep (se 1 (by rfl) ⟨189482, by rfl⟩ : syracuseStep 252643 = 378965) B378965
theorem B383729 : Blo 251819 383729 := bstep (se 2 (by rfl) ⟨143898, by rfl⟩ : syracuseStep 383729 = 287797) B287797
theorem B252659 : Blo 251819 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B252675 : Blo 251819 252675 := bstep (se 1 (by rfl) ⟨189506, by rfl⟩ : syracuseStep 252675 = 379013) B379013
theorem B482051 : Blo 251819 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B252691 : Blo 251819 252691 := bstep (se 1 (by rfl) ⟨189518, by rfl⟩ : syracuseStep 252691 = 379037) B379037
theorem B252707 : Blo 251819 252707 := bstep (se 1 (by rfl) ⟨189530, by rfl⟩ : syracuseStep 252707 = 379061) B379061
theorem B285475 : Blo 251819 285475 := bstep (se 1 (by rfl) ⟨214106, by rfl⟩ : syracuseStep 285475 = 428213) B428213
theorem B252723 : Blo 251819 252723 := bstep (se 1 (by rfl) ⟨189542, by rfl⟩ : syracuseStep 252723 = 379085) B379085
theorem B252739 : Blo 251819 252739 := bstep (se 1 (by rfl) ⟨189554, by rfl⟩ : syracuseStep 252739 = 379109) B379109
theorem B252755 : Blo 251819 252755 := bstep (se 1 (by rfl) ⟨189566, by rfl⟩ : syracuseStep 252755 = 379133) B379133
theorem B252771 : Blo 251819 252771 := bstep (se 1 (by rfl) ⟨189578, by rfl⟩ : syracuseStep 252771 = 379157) B379157
theorem B252787 : Blo 251819 252787 := bstep (se 1 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 252787 = 379181) B379181
theorem B252803 : Blo 251819 252803 := bstep (se 1 (by rfl) ⟨189602, by rfl⟩ : syracuseStep 252803 = 379205) B379205
theorem B252819 : Blo 251819 252819 := bstep (se 1 (by rfl) ⟨189614, by rfl⟩ : syracuseStep 252819 = 379229) B379229
theorem B252835 : Blo 251819 252835 := bstep (se 1 (by rfl) ⟨189626, by rfl⟩ : syracuseStep 252835 = 379253) B379253
theorem B252851 : Blo 251819 252851 := bstep (se 1 (by rfl) ⟨189638, by rfl⟩ : syracuseStep 252851 = 379277) B379277
theorem B285619 : Blo 251819 285619 := bstep (se 1 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 285619 = 428429) B428429
theorem B252867 : Blo 251819 252867 := bstep (se 1 (by rfl) ⟨189650, by rfl⟩ : syracuseStep 252867 = 379301) B379301
theorem B252883 : Blo 251819 252883 := bstep (se 1 (by rfl) ⟨189662, by rfl⟩ : syracuseStep 252883 = 379325) B379325
theorem B252899 : Blo 251819 252899 := bstep (se 1 (by rfl) ⟨189674, by rfl⟩ : syracuseStep 252899 = 379349) B379349
theorem B252915 : Blo 251819 252915 := bstep (se 1 (by rfl) ⟨189686, by rfl⟩ : syracuseStep 252915 = 379373) B379373
theorem B252931 : Blo 251819 252931 := bstep (se 1 (by rfl) ⟨189698, by rfl⟩ : syracuseStep 252931 = 379397) B379397
theorem B252947 : Blo 251819 252947 := bstep (se 1 (by rfl) ⟨189710, by rfl⟩ : syracuseStep 252947 = 379421) B379421
theorem B252963 : Blo 251819 252963 := bstep (se 1 (by rfl) ⟨189722, by rfl⟩ : syracuseStep 252963 = 379445) B379445
theorem B1629233 : Blo 251819 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B252979 : Blo 251819 252979 := bstep (se 1 (by rfl) ⟨189734, by rfl⟩ : syracuseStep 252979 = 379469) B379469
theorem B252995 : Blo 251819 252995 := bstep (se 1 (by rfl) ⟨189746, by rfl⟩ : syracuseStep 252995 = 379493) B379493
theorem B285763 : Blo 251819 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B515153 : Blo 251819 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B253011 : Blo 251819 253011 := bstep (se 1 (by rfl) ⟨189758, by rfl⟩ : syracuseStep 253011 = 379517) B379517
theorem B253027 : Blo 251819 253027 := bstep (se 1 (by rfl) ⟨189770, by rfl⟩ : syracuseStep 253027 = 379541) B379541
theorem B253043 : Blo 251819 253043 := bstep (se 1 (by rfl) ⟨189782, by rfl⟩ : syracuseStep 253043 = 379565) B379565
theorem B253059 : Blo 251819 253059 := bstep (se 1 (by rfl) ⟨189794, by rfl⟩ : syracuseStep 253059 = 379589) B379589
theorem B646289 : Blo 251819 646289 := bstep (se 2 (by rfl) ⟨242358, by rfl⟩ : syracuseStep 646289 = 484717) B484717
theorem B253075 : Blo 251819 253075 := bstep (se 1 (by rfl) ⟨189806, by rfl⟩ : syracuseStep 253075 = 379613) B379613
theorem B253091 : Blo 251819 253091 := bstep (se 1 (by rfl) ⟨189818, by rfl⟩ : syracuseStep 253091 = 379637) B379637
theorem B253107 : Blo 251819 253107 := bstep (se 1 (by rfl) ⟨189830, by rfl⟩ : syracuseStep 253107 = 379661) B379661
theorem B253123 : Blo 251819 253123 := bstep (se 1 (by rfl) ⟨189842, by rfl⟩ : syracuseStep 253123 = 379685) B379685
theorem B646339 : Blo 251819 646339 := bstep (se 1 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 646339 = 969509) B969509
theorem B253139 : Blo 251819 253139 := bstep (se 1 (by rfl) ⟨189854, by rfl⟩ : syracuseStep 253139 = 379709) B379709
theorem B285907 : Blo 251819 285907 := bstep (se 1 (by rfl) ⟨214430, by rfl⟩ : syracuseStep 285907 = 428861) B428861
theorem B253155 : Blo 251819 253155 := bstep (se 1 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 253155 = 379733) B379733
theorem B253171 : Blo 251819 253171 := bstep (se 1 (by rfl) ⟨189878, by rfl⟩ : syracuseStep 253171 = 379757) B379757
theorem B253187 : Blo 251819 253187 := bstep (se 1 (by rfl) ⟨189890, by rfl⟩ : syracuseStep 253187 = 379781) B379781
theorem B253203 : Blo 251819 253203 := bstep (se 1 (by rfl) ⟨189902, by rfl⟩ : syracuseStep 253203 = 379805) B379805
theorem B318755 : Blo 251819 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B253219 : Blo 251819 253219 := bstep (se 1 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 253219 = 379829) B379829
theorem B253235 : Blo 251819 253235 := bstep (se 1 (by rfl) ⟨189926, by rfl⟩ : syracuseStep 253235 = 379853) B379853
theorem B253251 : Blo 251819 253251 := bstep (se 1 (by rfl) ⟨189938, by rfl⟩ : syracuseStep 253251 = 379877) B379877
theorem B646481 : Blo 251819 646481 := bstep (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) B484861
theorem B253267 : Blo 251819 253267 := bstep (se 1 (by rfl) ⟨189950, by rfl⟩ : syracuseStep 253267 = 379901) B379901
theorem B253283 : Blo 251819 253283 := bstep (se 1 (by rfl) ⟨189962, by rfl⟩ : syracuseStep 253283 = 379925) B379925
theorem B286051 : Blo 251819 286051 := bstep (se 1 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 286051 = 429077) B429077
theorem B253299 : Blo 251819 253299 := bstep (se 1 (by rfl) ⟨189974, by rfl⟩ : syracuseStep 253299 = 379949) B379949
theorem B253315 : Blo 251819 253315 := bstep (se 1 (by rfl) ⟨189986, by rfl⟩ : syracuseStep 253315 = 379973) B379973
theorem B253331 : Blo 251819 253331 := bstep (se 1 (by rfl) ⟨189998, by rfl⟩ : syracuseStep 253331 = 379997) B379997
theorem B253347 : Blo 251819 253347 := bstep (se 1 (by rfl) ⟨190010, by rfl⟩ : syracuseStep 253347 = 380021) B380021
theorem B253363 : Blo 251819 253363 := bstep (se 1 (by rfl) ⟨190022, by rfl⟩ : syracuseStep 253363 = 380045) B380045
theorem B253379 : Blo 251819 253379 := bstep (se 1 (by rfl) ⟨190034, by rfl⟩ : syracuseStep 253379 = 380069) B380069
theorem B253395 : Blo 251819 253395 := bstep (se 1 (by rfl) ⟨190046, by rfl⟩ : syracuseStep 253395 = 380093) B380093
theorem B253411 : Blo 251819 253411 := bstep (se 1 (by rfl) ⟨190058, by rfl⟩ : syracuseStep 253411 = 380117) B380117
theorem B253427 : Blo 251819 253427 := bstep (se 1 (by rfl) ⟨190070, by rfl⟩ : syracuseStep 253427 = 380141) B380141
theorem B286195 : Blo 251819 286195 := bstep (se 1 (by rfl) ⟨214646, by rfl⟩ : syracuseStep 286195 = 429293) B429293
theorem B253443 : Blo 251819 253443 := bstep (se 1 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 253443 = 380165) B380165
theorem B253459 : Blo 251819 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B384545 : Blo 251819 384545 := bstep (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) B288409
theorem B253475 : Blo 251819 253475 := bstep (se 1 (by rfl) ⟨190106, by rfl⟩ : syracuseStep 253475 = 380213) B380213
theorem B253491 : Blo 251819 253491 := bstep (se 1 (by rfl) ⟨190118, by rfl⟩ : syracuseStep 253491 = 380237) B380237
theorem B253507 : Blo 251819 253507 := bstep (se 1 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 253507 = 380261) B380261
theorem B253523 : Blo 251819 253523 := bstep (se 1 (by rfl) ⟨190142, by rfl⟩ : syracuseStep 253523 = 380285) B380285
theorem B253539 : Blo 251819 253539 := bstep (se 1 (by rfl) ⟨190154, by rfl⟩ : syracuseStep 253539 = 380309) B380309
theorem B253555 : Blo 251819 253555 := bstep (se 1 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 253555 = 380333) B380333
theorem B253571 : Blo 251819 253571 := bstep (se 1 (by rfl) ⟨190178, by rfl⟩ : syracuseStep 253571 = 380357) B380357
theorem B286339 : Blo 251819 286339 := bstep (se 1 (by rfl) ⟨214754, by rfl⟩ : syracuseStep 286339 = 429509) B429509
theorem B253587 : Blo 251819 253587 := bstep (se 1 (by rfl) ⟨190190, by rfl⟩ : syracuseStep 253587 = 380381) B380381
theorem B253603 : Blo 251819 253603 := bstep (se 1 (by rfl) ⟨190202, by rfl⟩ : syracuseStep 253603 = 380405) B380405
theorem B482993 : Blo 251819 482993 := bstep (se 2 (by rfl) ⟨181122, by rfl⟩ : syracuseStep 482993 = 362245) B362245
theorem B253619 : Blo 251819 253619 := bstep (se 1 (by rfl) ⟨190214, by rfl⟩ : syracuseStep 253619 = 380429) B380429
theorem B253635 : Blo 251819 253635 := bstep (se 1 (by rfl) ⟨190226, by rfl⟩ : syracuseStep 253635 = 380453) B380453
theorem B253651 : Blo 251819 253651 := bstep (se 1 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 253651 = 380477) B380477
theorem B253667 : Blo 251819 253667 := bstep (se 1 (by rfl) ⟨190250, by rfl⟩ : syracuseStep 253667 = 380501) B380501
theorem B515825 : Blo 251819 515825 := bstep (se 2 (by rfl) ⟨193434, by rfl⟩ : syracuseStep 515825 = 386869) B386869
theorem B253683 : Blo 251819 253683 := bstep (se 1 (by rfl) ⟨190262, by rfl⟩ : syracuseStep 253683 = 380525) B380525
theorem B253699 : Blo 251819 253699 := bstep (se 1 (by rfl) ⟨190274, by rfl⟩ : syracuseStep 253699 = 380549) B380549
theorem B253715 : Blo 251819 253715 := bstep (se 1 (by rfl) ⟨190286, by rfl⟩ : syracuseStep 253715 = 380573) B380573
theorem B286483 : Blo 251819 286483 := bstep (se 1 (by rfl) ⟨214862, by rfl⟩ : syracuseStep 286483 = 429725) B429725
theorem B253731 : Blo 251819 253731 := bstep (se 1 (by rfl) ⟨190298, by rfl⟩ : syracuseStep 253731 = 380597) B380597
theorem B253747 : Blo 251819 253747 := bstep (se 1 (by rfl) ⟨190310, by rfl⟩ : syracuseStep 253747 = 380621) B380621
theorem B253763 : Blo 251819 253763 := bstep (se 1 (by rfl) ⟨190322, by rfl⟩ : syracuseStep 253763 = 380645) B380645
theorem B253779 : Blo 251819 253779 := bstep (se 1 (by rfl) ⟨190334, by rfl⟩ : syracuseStep 253779 = 380669) B380669
theorem B253795 : Blo 251819 253795 := bstep (se 1 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 253795 = 380693) B380693
theorem B253811 : Blo 251819 253811 := bstep (se 1 (by rfl) ⟨190358, by rfl⟩ : syracuseStep 253811 = 380717) B380717
theorem B253827 : Blo 251819 253827 := bstep (se 1 (by rfl) ⟨190370, by rfl⟩ : syracuseStep 253827 = 380741) B380741
theorem B253843 : Blo 251819 253843 := bstep (se 1 (by rfl) ⟨190382, by rfl⟩ : syracuseStep 253843 = 380765) B380765
theorem B253859 : Blo 251819 253859 := bstep (se 1 (by rfl) ⟨190394, by rfl⟩ : syracuseStep 253859 = 380789) B380789
theorem B286627 : Blo 251819 286627 := bstep (se 1 (by rfl) ⟨214970, by rfl⟩ : syracuseStep 286627 = 429941) B429941
theorem B253875 : Blo 251819 253875 := bstep (se 1 (by rfl) ⟨190406, by rfl⟩ : syracuseStep 253875 = 380813) B380813
theorem B253891 : Blo 251819 253891 := bstep (se 1 (by rfl) ⟨190418, by rfl⟩ : syracuseStep 253891 = 380837) B380837
theorem B2154437 : Blo 251819 2154437 := bstep (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) B403957
theorem B253907 : Blo 251819 253907 := bstep (se 1 (by rfl) ⟨190430, by rfl⟩ : syracuseStep 253907 = 380861) B380861
theorem B319459 : Blo 251819 319459 := bstep (se 1 (by rfl) ⟨239594, by rfl⟩ : syracuseStep 319459 = 479189) B479189
theorem B253923 : Blo 251819 253923 := bstep (se 1 (by rfl) ⟨190442, by rfl⟩ : syracuseStep 253923 = 380885) B380885
theorem B253939 : Blo 251819 253939 := bstep (se 1 (by rfl) ⟨190454, by rfl⟩ : syracuseStep 253939 = 380909) B380909
theorem B253955 : Blo 251819 253955 := bstep (se 1 (by rfl) ⟨190466, by rfl⟩ : syracuseStep 253955 = 380933) B380933
theorem B253971 : Blo 251819 253971 := bstep (se 1 (by rfl) ⟨190478, by rfl⟩ : syracuseStep 253971 = 380957) B380957
theorem B253987 : Blo 251819 253987 := bstep (se 1 (by rfl) ⟨190490, by rfl⟩ : syracuseStep 253987 = 380981) B380981
theorem B254003 : Blo 251819 254003 := bstep (se 1 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 254003 = 381005) B381005
theorem B286771 : Blo 251819 286771 := bstep (se 1 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 286771 = 430157) B430157
theorem B319555 : Blo 251819 319555 := bstep (se 1 (by rfl) ⟨239666, by rfl⟩ : syracuseStep 319555 = 479333) B479333
theorem B254019 : Blo 251819 254019 := bstep (se 1 (by rfl) ⟨190514, by rfl⟩ : syracuseStep 254019 = 381029) B381029
theorem B254035 : Blo 251819 254035 := bstep (se 1 (by rfl) ⟨190526, by rfl⟩ : syracuseStep 254035 = 381053) B381053
theorem B254051 : Blo 251819 254051 := bstep (se 1 (by rfl) ⟨190538, by rfl⟩ : syracuseStep 254051 = 381077) B381077
theorem B1630307 : Blo 251819 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B254067 : Blo 251819 254067 := bstep (se 1 (by rfl) ⟨190550, by rfl⟩ : syracuseStep 254067 = 381101) B381101
theorem B254083 : Blo 251819 254083 := bstep (se 1 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 254083 = 381125) B381125
theorem B1532045 : Blo 251819 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B254099 : Blo 251819 254099 := bstep (se 1 (by rfl) ⟨190574, by rfl⟩ : syracuseStep 254099 = 381149) B381149
theorem B254115 : Blo 251819 254115 := bstep (se 1 (by rfl) ⟨190586, by rfl⟩ : syracuseStep 254115 = 381173) B381173
theorem B254131 : Blo 251819 254131 := bstep (se 1 (by rfl) ⟨190598, by rfl⟩ : syracuseStep 254131 = 381197) B381197
theorem B254147 : Blo 251819 254147 := bstep (se 1 (by rfl) ⟨190610, by rfl⟩ : syracuseStep 254147 = 381221) B381221
theorem B286915 : Blo 251819 286915 := bstep (se 1 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 286915 = 430373) B430373
theorem B254163 : Blo 251819 254163 := bstep (se 1 (by rfl) ⟨190622, by rfl⟩ : syracuseStep 254163 = 381245) B381245
theorem B254179 : Blo 251819 254179 := bstep (se 1 (by rfl) ⟨190634, by rfl⟩ : syracuseStep 254179 = 381269) B381269
theorem B254195 : Blo 251819 254195 := bstep (se 1 (by rfl) ⟨190646, by rfl⟩ : syracuseStep 254195 = 381293) B381293
theorem B254211 : Blo 251819 254211 := bstep (se 1 (by rfl) ⟨190658, by rfl⟩ : syracuseStep 254211 = 381317) B381317
theorem B254227 : Blo 251819 254227 := bstep (se 1 (by rfl) ⟨190670, by rfl⟩ : syracuseStep 254227 = 381341) B381341
theorem B254243 : Blo 251819 254243 := bstep (se 1 (by rfl) ⟨190682, by rfl⟩ : syracuseStep 254243 = 381365) B381365
theorem B811309 : Blo 251819 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B647473 : Blo 251819 647473 := bstep (se 2 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 647473 = 485605) B485605
theorem B254259 : Blo 251819 254259 := bstep (se 1 (by rfl) ⟨190694, by rfl⟩ : syracuseStep 254259 = 381389) B381389
theorem B254275 : Blo 251819 254275 := bstep (se 1 (by rfl) ⟨190706, by rfl⟩ : syracuseStep 254275 = 381413) B381413
theorem B254291 : Blo 251819 254291 := bstep (se 1 (by rfl) ⟨190718, by rfl⟩ : syracuseStep 254291 = 381437) B381437
theorem B287059 : Blo 251819 287059 := bstep (se 1 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 287059 = 430589) B430589
theorem B909667 : Blo 251819 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B254307 : Blo 251819 254307 := bstep (se 1 (by rfl) ⟨190730, by rfl⟩ : syracuseStep 254307 = 381461) B381461
theorem B254323 : Blo 251819 254323 := bstep (se 1 (by rfl) ⟨190742, by rfl⟩ : syracuseStep 254323 = 381485) B381485
theorem B254339 : Blo 251819 254339 := bstep (se 1 (by rfl) ⟨190754, by rfl⟩ : syracuseStep 254339 = 381509) B381509
theorem B254355 : Blo 251819 254355 := bstep (se 1 (by rfl) ⟨190766, by rfl⟩ : syracuseStep 254355 = 381533) B381533
theorem B254371 : Blo 251819 254371 := bstep (se 1 (by rfl) ⟨190778, by rfl⟩ : syracuseStep 254371 = 381557) B381557
theorem B254387 : Blo 251819 254387 := bstep (se 1 (by rfl) ⟨190790, by rfl⟩ : syracuseStep 254387 = 381581) B381581
theorem B254403 : Blo 251819 254403 := bstep (se 1 (by rfl) ⟨190802, by rfl⟩ : syracuseStep 254403 = 381605) B381605
theorem B254419 : Blo 251819 254419 := bstep (se 1 (by rfl) ⟨190814, by rfl⟩ : syracuseStep 254419 = 381629) B381629
theorem B254435 : Blo 251819 254435 := bstep (se 1 (by rfl) ⟨190826, by rfl⟩ : syracuseStep 254435 = 381653) B381653
theorem B287203 : Blo 251819 287203 := bstep (se 1 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 287203 = 430805) B430805
theorem B254451 : Blo 251819 254451 := bstep (se 1 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 254451 = 381677) B381677
theorem B254467 : Blo 251819 254467 := bstep (se 1 (by rfl) ⟨190850, by rfl⟩ : syracuseStep 254467 = 381701) B381701
theorem B254483 : Blo 251819 254483 := bstep (se 1 (by rfl) ⟨190862, by rfl⟩ : syracuseStep 254483 = 381725) B381725
theorem B254499 : Blo 251819 254499 := bstep (se 1 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 254499 = 381749) B381749
theorem B483889 : Blo 251819 483889 := bstep (se 2 (by rfl) ⟨181458, by rfl⟩ : syracuseStep 483889 = 362917) B362917
theorem B320051 : Blo 251819 320051 := bstep (se 1 (by rfl) ⟨240038, by rfl⟩ : syracuseStep 320051 = 480077) B480077
theorem B254515 : Blo 251819 254515 := bstep (se 1 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 254515 = 381773) B381773
theorem B254531 : Blo 251819 254531 := bstep (se 1 (by rfl) ⟨190898, by rfl⟩ : syracuseStep 254531 = 381797) B381797
theorem B254547 : Blo 251819 254547 := bstep (se 1 (by rfl) ⟨190910, by rfl⟩ : syracuseStep 254547 = 381821) B381821
theorem B254563 : Blo 251819 254563 := bstep (se 1 (by rfl) ⟨190922, by rfl⟩ : syracuseStep 254563 = 381845) B381845
theorem B254579 : Blo 251819 254579 := bstep (se 1 (by rfl) ⟨190934, by rfl⟩ : syracuseStep 254579 = 381869) B381869
theorem B287347 : Blo 251819 287347 := bstep (se 1 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 287347 = 431021) B431021
theorem B254595 : Blo 251819 254595 := bstep (se 1 (by rfl) ⟨190946, by rfl⟩ : syracuseStep 254595 = 381893) B381893
theorem B254611 : Blo 251819 254611 := bstep (se 1 (by rfl) ⟨190958, by rfl⟩ : syracuseStep 254611 = 381917) B381917
theorem B254627 : Blo 251819 254627 := bstep (se 1 (by rfl) ⟨190970, by rfl⟩ : syracuseStep 254627 = 381941) B381941
theorem B254643 : Blo 251819 254643 := bstep (se 1 (by rfl) ⟨190982, by rfl⟩ : syracuseStep 254643 = 381965) B381965
theorem B254659 : Blo 251819 254659 := bstep (se 1 (by rfl) ⟨190994, by rfl⟩ : syracuseStep 254659 = 381989) B381989
theorem B484049 : Blo 251819 484049 := bstep (se 2 (by rfl) ⟨181518, by rfl⟩ : syracuseStep 484049 = 363037) B363037
theorem B254675 : Blo 251819 254675 := bstep (se 1 (by rfl) ⟨191006, by rfl⟩ : syracuseStep 254675 = 382013) B382013
theorem B254691 : Blo 251819 254691 := bstep (se 1 (by rfl) ⟨191018, by rfl⟩ : syracuseStep 254691 = 382037) B382037
theorem B254707 : Blo 251819 254707 := bstep (se 1 (by rfl) ⟨191030, by rfl⟩ : syracuseStep 254707 = 382061) B382061
theorem B254723 : Blo 251819 254723 := bstep (se 1 (by rfl) ⟨191042, by rfl⟩ : syracuseStep 254723 = 382085) B382085
theorem B287491 : Blo 251819 287491 := bstep (se 1 (by rfl) ⟨215618, by rfl⟩ : syracuseStep 287491 = 431237) B431237
theorem B254739 : Blo 251819 254739 := bstep (se 1 (by rfl) ⟨191054, by rfl⟩ : syracuseStep 254739 = 382109) B382109
theorem B254755 : Blo 251819 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B910129 : Blo 251819 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B254771 : Blo 251819 254771 := bstep (se 1 (by rfl) ⟨191078, by rfl⟩ : syracuseStep 254771 = 382157) B382157
theorem B3269429 : Blo 251819 3269429 := bstep (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) B306509
theorem B254787 : Blo 251819 254787 := bstep (se 1 (by rfl) ⟨191090, by rfl⟩ : syracuseStep 254787 = 382181) B382181
theorem B254803 : Blo 251819 254803 := bstep (se 1 (by rfl) ⟨191102, by rfl⟩ : syracuseStep 254803 = 382205) B382205
theorem B254819 : Blo 251819 254819 := bstep (se 1 (by rfl) ⟨191114, by rfl⟩ : syracuseStep 254819 = 382229) B382229
theorem B254835 : Blo 251819 254835 := bstep (se 1 (by rfl) ⟨191126, by rfl⟩ : syracuseStep 254835 = 382253) B382253
theorem B254851 : Blo 251819 254851 := bstep (se 1 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 254851 = 382277) B382277
theorem B254867 : Blo 251819 254867 := bstep (se 1 (by rfl) ⟨191150, by rfl⟩ : syracuseStep 254867 = 382301) B382301
theorem B287635 : Blo 251819 287635 := bstep (se 1 (by rfl) ⟨215726, by rfl⟩ : syracuseStep 287635 = 431453) B431453
theorem B254883 : Blo 251819 254883 := bstep (se 1 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 254883 = 382325) B382325
theorem B254899 : Blo 251819 254899 := bstep (se 1 (by rfl) ⟨191174, by rfl⟩ : syracuseStep 254899 = 382349) B382349
theorem B254915 : Blo 251819 254915 := bstep (se 1 (by rfl) ⟨191186, by rfl⟩ : syracuseStep 254915 = 382373) B382373
theorem B254931 : Blo 251819 254931 := bstep (se 1 (by rfl) ⟨191198, by rfl⟩ : syracuseStep 254931 = 382397) B382397
theorem B254947 : Blo 251819 254947 := bstep (se 1 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 254947 = 382421) B382421
theorem B254963 : Blo 251819 254963 := bstep (se 1 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 254963 = 382445) B382445
theorem B254979 : Blo 251819 254979 := bstep (se 1 (by rfl) ⟨191234, by rfl⟩ : syracuseStep 254979 = 382469) B382469
theorem B254995 : Blo 251819 254995 := bstep (se 1 (by rfl) ⟨191246, by rfl⟩ : syracuseStep 254995 = 382493) B382493
theorem B255011 : Blo 251819 255011 := bstep (se 1 (by rfl) ⟨191258, by rfl⟩ : syracuseStep 255011 = 382517) B382517
theorem B287779 : Blo 251819 287779 := bstep (se 1 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 287779 = 431669) B431669
theorem B255027 : Blo 251819 255027 := bstep (se 1 (by rfl) ⟨191270, by rfl⟩ : syracuseStep 255027 = 382541) B382541
theorem B255043 : Blo 251819 255043 := bstep (se 1 (by rfl) ⟨191282, by rfl⟩ : syracuseStep 255043 = 382565) B382565
theorem B681041 : Blo 251819 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B255059 : Blo 251819 255059 := bstep (se 1 (by rfl) ⟨191294, by rfl⟩ : syracuseStep 255059 = 382589) B382589
theorem B255075 : Blo 251819 255075 := bstep (se 1 (by rfl) ⟨191306, by rfl⟩ : syracuseStep 255075 = 382613) B382613
theorem B484451 : Blo 251819 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B255091 : Blo 251819 255091 := bstep (se 1 (by rfl) ⟨191318, by rfl⟩ : syracuseStep 255091 = 382637) B382637
theorem B255107 : Blo 251819 255107 := bstep (se 1 (by rfl) ⟨191330, by rfl⟩ : syracuseStep 255107 = 382661) B382661
theorem B255123 : Blo 251819 255123 := bstep (se 1 (by rfl) ⟨191342, by rfl⟩ : syracuseStep 255123 = 382685) B382685
theorem B255139 : Blo 251819 255139 := bstep (se 1 (by rfl) ⟨191354, by rfl⟩ : syracuseStep 255139 = 382709) B382709
theorem B255155 : Blo 251819 255155 := bstep (se 1 (by rfl) ⟨191366, by rfl⟩ : syracuseStep 255155 = 382733) B382733
theorem B255171 : Blo 251819 255171 := bstep (se 1 (by rfl) ⟨191378, by rfl⟩ : syracuseStep 255171 = 382757) B382757
theorem B255187 : Blo 251819 255187 := bstep (se 1 (by rfl) ⟨191390, by rfl⟩ : syracuseStep 255187 = 382781) B382781
theorem B255203 : Blo 251819 255203 := bstep (se 1 (by rfl) ⟨191402, by rfl⟩ : syracuseStep 255203 = 382805) B382805
theorem B320755 : Blo 251819 320755 := bstep (se 1 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 320755 = 481133) B481133
theorem B255219 : Blo 251819 255219 := bstep (se 1 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 255219 = 382829) B382829
theorem B255235 : Blo 251819 255235 := bstep (se 1 (by rfl) ⟨191426, by rfl⟩ : syracuseStep 255235 = 382853) B382853
theorem B255251 : Blo 251819 255251 := bstep (se 1 (by rfl) ⟨191438, by rfl⟩ : syracuseStep 255251 = 382877) B382877
theorem B255267 : Blo 251819 255267 := bstep (se 1 (by rfl) ⟨191450, by rfl⟩ : syracuseStep 255267 = 382901) B382901
theorem B255283 : Blo 251819 255283 := bstep (se 1 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 255283 = 382925) B382925
theorem B255299 : Blo 251819 255299 := bstep (se 1 (by rfl) ⟨191474, by rfl⟩ : syracuseStep 255299 = 382949) B382949
theorem B320851 : Blo 251819 320851 := bstep (se 1 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 320851 = 481277) B481277
theorem B255315 : Blo 251819 255315 := bstep (se 1 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 255315 = 382973) B382973
theorem B255331 : Blo 251819 255331 := bstep (se 1 (by rfl) ⟨191498, by rfl⟩ : syracuseStep 255331 = 382997) B382997
theorem B255347 : Blo 251819 255347 := bstep (se 1 (by rfl) ⟨191510, by rfl⟩ : syracuseStep 255347 = 383021) B383021
theorem B255363 : Blo 251819 255363 := bstep (se 1 (by rfl) ⟨191522, by rfl⟩ : syracuseStep 255363 = 383045) B383045
theorem B255379 : Blo 251819 255379 := bstep (se 1 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 255379 = 383069) B383069
theorem B255395 : Blo 251819 255395 := bstep (se 1 (by rfl) ⟨191546, by rfl⟩ : syracuseStep 255395 = 383093) B383093
theorem B255411 : Blo 251819 255411 := bstep (se 1 (by rfl) ⟨191558, by rfl⟩ : syracuseStep 255411 = 383117) B383117
theorem B255427 : Blo 251819 255427 := bstep (se 1 (by rfl) ⟨191570, by rfl⟩ : syracuseStep 255427 = 383141) B383141
theorem B255443 : Blo 251819 255443 := bstep (se 1 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 255443 = 383165) B383165
theorem B255459 : Blo 251819 255459 := bstep (se 1 (by rfl) ⟨191594, by rfl⟩ : syracuseStep 255459 = 383189) B383189
theorem B255475 : Blo 251819 255475 := bstep (se 1 (by rfl) ⟨191606, by rfl⟩ : syracuseStep 255475 = 383213) B383213
theorem B255491 : Blo 251819 255491 := bstep (se 1 (by rfl) ⟨191618, by rfl⟩ : syracuseStep 255491 = 383237) B383237
theorem B255507 : Blo 251819 255507 := bstep (se 1 (by rfl) ⟨191630, by rfl⟩ : syracuseStep 255507 = 383261) B383261
theorem B255523 : Blo 251819 255523 := bstep (se 1 (by rfl) ⟨191642, by rfl⟩ : syracuseStep 255523 = 383285) B383285
theorem B255539 : Blo 251819 255539 := bstep (se 1 (by rfl) ⟨191654, by rfl⟩ : syracuseStep 255539 = 383309) B383309
theorem B255555 : Blo 251819 255555 := bstep (se 1 (by rfl) ⟨191666, by rfl⟩ : syracuseStep 255555 = 383333) B383333
theorem B255571 : Blo 251819 255571 := bstep (se 1 (by rfl) ⟨191678, by rfl⟩ : syracuseStep 255571 = 383357) B383357
theorem B255587 : Blo 251819 255587 := bstep (se 1 (by rfl) ⟨191690, by rfl⟩ : syracuseStep 255587 = 383381) B383381
theorem B255603 : Blo 251819 255603 := bstep (se 1 (by rfl) ⟨191702, by rfl⟩ : syracuseStep 255603 = 383405) B383405
theorem B255619 : Blo 251819 255619 := bstep (se 1 (by rfl) ⟨191714, by rfl⟩ : syracuseStep 255619 = 383429) B383429
theorem B255635 : Blo 251819 255635 := bstep (se 1 (by rfl) ⟨191726, by rfl⟩ : syracuseStep 255635 = 383453) B383453
theorem B255651 : Blo 251819 255651 := bstep (se 1 (by rfl) ⟨191738, by rfl⟩ : syracuseStep 255651 = 383477) B383477
theorem B255667 : Blo 251819 255667 := bstep (se 1 (by rfl) ⟨191750, by rfl⟩ : syracuseStep 255667 = 383501) B383501
theorem B255683 : Blo 251819 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B255699 : Blo 251819 255699 := bstep (se 1 (by rfl) ⟨191774, by rfl⟩ : syracuseStep 255699 = 383549) B383549
theorem B255715 : Blo 251819 255715 := bstep (se 1 (by rfl) ⟨191786, by rfl⟩ : syracuseStep 255715 = 383573) B383573
theorem B255731 : Blo 251819 255731 := bstep (se 1 (by rfl) ⟨191798, by rfl⟩ : syracuseStep 255731 = 383597) B383597
theorem B255747 : Blo 251819 255747 := bstep (se 1 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 255747 = 383621) B383621
theorem B255763 : Blo 251819 255763 := bstep (se 1 (by rfl) ⟨191822, by rfl⟩ : syracuseStep 255763 = 383645) B383645
theorem B255779 : Blo 251819 255779 := bstep (se 1 (by rfl) ⟨191834, by rfl⟩ : syracuseStep 255779 = 383669) B383669
theorem B255795 : Blo 251819 255795 := bstep (se 1 (by rfl) ⟨191846, by rfl⟩ : syracuseStep 255795 = 383693) B383693
theorem B321347 : Blo 251819 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B354115 : Blo 251819 354115 := bstep (se 1 (by rfl) ⟨265586, by rfl⟩ : syracuseStep 354115 = 531173) B531173
theorem B255811 : Blo 251819 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B485347 : Blo 251819 485347 := bstep (se 1 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 485347 = 728021) B728021
theorem B813041 : Blo 251819 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B518179 : Blo 251819 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B485507 : Blo 251819 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B3532997 : Blo 251819 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B518467 : Blo 251819 518467 := bstep (se 1 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 518467 = 777701) B777701
theorem B322051 : Blo 251819 322051 := bstep (se 1 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 322051 = 483077) B483077
theorem B682577 : Blo 251819 682577 := bstep (se 2 (by rfl) ⟨255966, by rfl⟩ : syracuseStep 682577 = 511933) B511933
theorem B387683 : Blo 251819 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B813667 : Blo 251819 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B322147 : Blo 251819 322147 := bstep (se 1 (by rfl) ⟨241610, by rfl⟩ : syracuseStep 322147 = 483221) B483221
theorem B2746993 : Blo 251819 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B3500657 : Blo 251819 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B322643 : Blo 251819 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B1469765 : Blo 251819 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B1371491 : Blo 251819 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B1437041 : Blo 251819 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B454243 : Blo 251819 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B290467 : Blo 251819 290467 := bstep (se 1 (by rfl) ⟨217850, by rfl⟩ : syracuseStep 290467 = 435701) B435701
theorem B323347 : Blo 251819 323347 := bstep (se 1 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 323347 = 485021) B485021
theorem B814897 : Blo 251819 814897 := bstep (se 2 (by rfl) ⟨305586, by rfl⟩ : syracuseStep 814897 = 611173) B611173
theorem B1830725 : Blo 251819 1830725 := bstep (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) B343261
theorem B388979 : Blo 251819 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B323443 : Blo 251819 323443 := bstep (se 1 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 323443 = 485165) B485165
theorem B683981 : Blo 251819 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B1634509 : Blo 251819 1634509 := bstep (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) B612941
theorem B815501 : Blo 251819 815501 := bstep (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) B305813
theorem B324131 : Blo 251819 324131 := bstep (se 1 (by rfl) ⟨243098, by rfl⟩ : syracuseStep 324131 = 486197) B486197
theorem B1438499 : Blo 251819 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B2159459 : Blo 251819 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B455843 : Blo 251819 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B717997 : Blo 251819 717997 := bstep (se 3 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 717997 = 269249) B269249
theorem B1733957 : Blo 251819 1733957 := bstep (se 4 (by rfl) ⟨162558, by rfl⟩ : syracuseStep 1733957 = 325117) B325117
theorem B456067 : Blo 251819 456067 := bstep (se 1 (by rfl) ⟨342050, by rfl⟩ : syracuseStep 456067 = 684101) B684101
theorem B456131 : Blo 251819 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B914915 : Blo 251819 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B1734257 : Blo 251819 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B1079011 : Blo 251819 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B456529 : Blo 251819 456529 := bstep (se 2 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 456529 = 342397) B342397
theorem B1308593 : Blo 251819 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B849905 : Blo 251819 849905 := bstep (se 2 (by rfl) ⟨318714, by rfl⟩ : syracuseStep 849905 = 637429) B637429
theorem B2488333 : Blo 251819 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1931363 : Blo 251819 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B719057 : Blo 251819 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B358771 : Blo 251819 358771 := bstep (se 1 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 358771 = 538157) B538157
theorem B9238981 : Blo 251819 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B850445 : Blo 251819 850445 := bstep (se 3 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 850445 = 318917) B318917
theorem B850499 : Blo 251819 850499 := bstep (se 1 (by rfl) ⟨637874, by rfl⟩ : syracuseStep 850499 = 1275749) B1275749
theorem B490225 : Blo 251819 490225 := bstep (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) B367669
theorem B1276721 : Blo 251819 1276721 := bstep (se 2 (by rfl) ⟨478770, by rfl⟩ : syracuseStep 1276721 = 957541) B957541
theorem B850769 : Blo 251819 850769 := bstep (se 2 (by rfl) ⟨319038, by rfl⟩ : syracuseStep 850769 = 638077) B638077
theorem B719729 : Blo 251819 719729 := bstep (se 2 (by rfl) ⟨269898, by rfl⟩ : syracuseStep 719729 = 539797) B539797
theorem B359329 : Blo 251819 359329 := bstep (se 2 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 359329 = 269497) B269497
theorem B359363 : Blo 251819 359363 := bstep (se 1 (by rfl) ⟨269522, by rfl⟩ : syracuseStep 359363 = 539045) B539045
theorem B424993 : Blo 251819 424993 := bstep (se 2 (by rfl) ⟨159372, by rfl⟩ : syracuseStep 424993 = 318745) B318745
theorem B425027 : Blo 251819 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B425155 : Blo 251819 425155 := bstep (se 1 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 425155 = 637733) B637733
theorem B1539299 : Blo 251819 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B4914485 : Blo 251819 4914485 := bstep (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) B460733
theorem B425297 : Blo 251819 425297 := bstep (se 2 (by rfl) ⟨159486, by rfl⟩ : syracuseStep 425297 = 318973) B318973
theorem B851309 : Blo 251819 851309 := bstep (se 3 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 851309 = 319241) B319241
theorem B851363 : Blo 251819 851363 := bstep (se 1 (by rfl) ⟨638522, by rfl⟩ : syracuseStep 851363 = 1277045) B1277045
theorem B425425 : Blo 251819 425425 := bstep (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) B319069
theorem B359921 : Blo 251819 359921 := bstep (se 2 (by rfl) ⟨134970, by rfl⟩ : syracuseStep 359921 = 269941) B269941
theorem B425459 : Blo 251819 425459 := bstep (se 1 (by rfl) ⟨319094, by rfl⟩ : syracuseStep 425459 = 638189) B638189
theorem B360001 : Blo 251819 360001 := bstep (se 2 (by rfl) ⟨135000, by rfl⟩ : syracuseStep 360001 = 270001) B270001
theorem B425587 : Blo 251819 425587 := bstep (se 1 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 425587 = 638381) B638381
theorem B720515 : Blo 251819 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B818819 : Blo 251819 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B851633 : Blo 251819 851633 := bstep (se 2 (by rfl) ⟨319362, by rfl⟩ : syracuseStep 851633 = 638725) B638725
theorem B425729 : Blo 251819 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B2817845 : Blo 251819 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B425857 : Blo 251819 425857 := bstep (se 2 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 425857 = 319393) B319393
theorem B425891 : Blo 251819 425891 := bstep (se 1 (by rfl) ⟨319418, by rfl⟩ : syracuseStep 425891 = 638837) B638837
theorem B720845 : Blo 251819 720845 := bstep (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) B270317
theorem B1278017 : Blo 251819 1278017 := bstep (se 2 (by rfl) ⟨479256, by rfl⟩ : syracuseStep 1278017 = 958513) B958513
theorem B720971 : Blo 251819 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B426073 : Blo 251819 426073 := bstep (se 2 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 426073 = 319555) B319555
theorem B983171 : Blo 251819 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B852119 : Blo 251819 852119 := bstep (se 1 (by rfl) ⟨639089, by rfl⟩ : syracuseStep 852119 = 1278179) B1278179
theorem B1442123 : Blo 251819 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1081745 : Blo 251819 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B1212889 : Blo 251819 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B819677 : Blo 251819 819677 := bstep (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) B307379
theorem B426647 : Blo 251819 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B852659 : Blo 251819 852659 := bstep (se 1 (by rfl) ⟨639494, by rfl⟩ : syracuseStep 852659 = 1278989) B1278989
theorem B426775 : Blo 251819 426775 := bstep (se 1 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 426775 = 640163) B640163
theorem B459607 : Blo 251819 459607 := bstep (se 1 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 459607 = 689411) B689411
theorem B852929 : Blo 251819 852929 := bstep (se 2 (by rfl) ⟨319848, by rfl⟩ : syracuseStep 852929 = 639697) B639697
theorem B1213505 : Blo 251819 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B4916375 : Blo 251819 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B361675 : Blo 251819 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B361687 : Blo 251819 361687 := bstep (se 1 (by rfl) ⟨271265, by rfl⟩ : syracuseStep 361687 = 542531) B542531
theorem B427403 : Blo 251819 427403 := bstep (se 1 (by rfl) ⟨320552, by rfl⟩ : syracuseStep 427403 = 641105) B641105
theorem B2196887 : Blo 251819 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B460225 : Blo 251819 460225 := bstep (se 2 (by rfl) ⟨172584, by rfl⟩ : syracuseStep 460225 = 345169) B345169
theorem B853469 : Blo 251819 853469 := bstep (se 3 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 853469 = 320051) B320051
theorem B427531 : Blo 251819 427531 := bstep (se 1 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 427531 = 641297) B641297
theorem B460313 : Blo 251819 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B2754083 : Blo 251819 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B427673 : Blo 251819 427673 := bstep (se 2 (by rfl) ⟨160377, by rfl⟩ : syracuseStep 427673 = 320755) B320755
theorem B2885381 : Blo 251819 2885381 := bstep (se 4 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 2885381 = 541009) B541009
theorem B427801 : Blo 251819 427801 := bstep (se 2 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 427801 = 320851) B320851
theorem B1279961 : Blo 251819 1279961 := bstep (se 2 (by rfl) ⟨479985, by rfl⟩ : syracuseStep 1279961 = 959971) B959971
theorem B919873 : Blo 251819 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B428375 : Blo 251819 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B1149329 : Blo 251819 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B428503 : Blo 251819 428503 := bstep (se 1 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 428503 = 642755) B642755
theorem B1149457 : Blo 251819 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B854603 : Blo 251819 854603 := bstep (se 1 (by rfl) ⟨640952, by rfl⟩ : syracuseStep 854603 = 1281905) B1281905
theorem B690905 : Blo 251819 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B1084205 : Blo 251819 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B854873 : Blo 251819 854873 := bstep (se 2 (by rfl) ⟨320577, by rfl⟩ : syracuseStep 854873 = 641155) B641155
theorem B1444787 : Blo 251819 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B429131 : Blo 251819 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B691289 : Blo 251819 691289 := bstep (se 2 (by rfl) ⟨259233, by rfl⟩ : syracuseStep 691289 = 518467) B518467
theorem B7834805 : Blo 251819 7834805 := bstep (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) B734513
theorem B429259 : Blo 251819 429259 := bstep (se 1 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 429259 = 643889) B643889
theorem B363737 : Blo 251819 363737 := bstep (se 2 (by rfl) ⟨136401, by rfl⟩ : syracuseStep 363737 = 272803) B272803
theorem B429401 : Blo 251819 429401 := bstep (se 2 (by rfl) ⟨161025, by rfl⟩ : syracuseStep 429401 = 322051) B322051
theorem B495065 : Blo 251819 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B1084889 : Blo 251819 1084889 := bstep (se 2 (by rfl) ⟨406833, by rfl⟩ : syracuseStep 1084889 = 813667) B813667
theorem B429529 : Blo 251819 429529 := bstep (se 2 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 429529 = 322147) B322147
theorem B3673613 : Blo 251819 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B855575 : Blo 251819 855575 := bstep (se 1 (by rfl) ⟨641681, by rfl⟩ : syracuseStep 855575 = 1283363) B1283363
theorem B1281581 : Blo 251819 1281581 := bstep (se 3 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 1281581 = 480593) B480593
theorem B1216349 : Blo 251819 1216349 := bstep (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) B456131
theorem B921547 : Blo 251819 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B430103 : Blo 251819 430103 := bstep (se 1 (by rfl) ⟨322577, by rfl⟩ : syracuseStep 430103 = 645155) B645155
theorem B856115 : Blo 251819 856115 := bstep (se 1 (by rfl) ⟨642086, by rfl⟩ : syracuseStep 856115 = 1284173) B1284173
theorem B430231 : Blo 251819 430231 := bstep (se 1 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 430231 = 645347) B645347
theorem B1380503 : Blo 251819 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B1937681 : Blo 251819 1937681 := bstep (se 2 (by rfl) ⟨726630, by rfl⟩ : syracuseStep 1937681 = 1453261) B1453261
theorem B4624685 : Blo 251819 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B856385 : Blo 251819 856385 := bstep (se 2 (by rfl) ⟨321144, by rfl⟩ : syracuseStep 856385 = 642289) B642289
theorem B1446245 : Blo 251819 1446245 := bstep (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) B271171
theorem B1086155 : Blo 251819 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B430859 : Blo 251819 430859 := bstep (se 1 (by rfl) ⟨323144, by rfl⟩ : syracuseStep 430859 = 646289) B646289
theorem B856925 : Blo 251819 856925 := bstep (se 3 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 856925 = 321347) B321347
theorem B430987 : Blo 251819 430987 := bstep (se 1 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 430987 = 646481) B646481
theorem B1446929 : Blo 251819 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B431129 : Blo 251819 431129 := bstep (se 2 (by rfl) ⟨161673, by rfl⟩ : syracuseStep 431129 = 323347) B323347
theorem B1086529 : Blo 251819 1086529 := bstep (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) B814897
theorem B431257 : Blo 251819 431257 := bstep (se 2 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 431257 = 323443) B323443
theorem B1381697 : Blo 251819 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B726347 : Blo 251819 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B1086871 : Blo 251819 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B464459 : Blo 251819 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B726745 : Blo 251819 726745 := bstep (se 2 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 726745 = 545059) B545059
theorem B858059 : Blo 251819 858059 := bstep (se 1 (by rfl) ⟨643544, by rfl⟩ : syracuseStep 858059 = 1287089) B1287089
theorem B858329 : Blo 251819 858329 := bstep (se 2 (by rfl) ⟨321873, by rfl⟩ : syracuseStep 858329 = 643747) B643747
theorem B957329 : Blo 251819 957329 := bstep (se 2 (by rfl) ⟨358998, by rfl⟩ : syracuseStep 957329 = 717997) B717997
theorem B859031 : Blo 251819 859031 := bstep (se 1 (by rfl) ⟨644273, by rfl⟩ : syracuseStep 859031 = 1288547) B1288547
theorem B727987 : Blo 251819 727987 := bstep (se 1 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 727987 = 1091981) B1091981
theorem B2333771 : Blo 251819 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B1285469 : Blo 251819 1285469 := bstep (se 3 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 1285469 = 482051) B482051
theorem B859571 : Blo 251819 859571 := bstep (se 1 (by rfl) ⟨644678, by rfl⟩ : syracuseStep 859571 = 1289357) B1289357
theorem B958027 : Blo 251819 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B859841 : Blo 251819 859841 := bstep (se 2 (by rfl) ⟨322440, by rfl⟩ : syracuseStep 859841 = 644881) B644881
theorem B270091 : Blo 251819 270091 := bstep (se 1 (by rfl) ⟨202568, by rfl⟩ : syracuseStep 270091 = 405137) B405137
theorem B958301 : Blo 251819 958301 := bstep (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) B359363
theorem B1220483 : Blo 251819 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B925643 : Blo 251819 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B3317777 : Blo 251819 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B1941569 : Blo 251819 1941569 := bstep (se 2 (by rfl) ⟨728088, by rfl⟩ : syracuseStep 1941569 = 1456177) B1456177
theorem B1974451 : Blo 251819 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B1450163 : Blo 251819 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B860381 : Blo 251819 860381 := bstep (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) B322643
theorem B958999 : Blo 251819 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B303895 : Blo 251819 303895 := bstep (se 1 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 303895 = 455843) B455843
theorem B6169445 : Blo 251819 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B1155971 : Blo 251819 1155971 := bstep (se 1 (by rfl) ⟨866978, by rfl⟩ : syracuseStep 1155971 = 1733957) B1733957
theorem B1156189 : Blo 251819 1156189 := bstep (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) B433571
theorem B959789 : Blo 251819 959789 := bstep (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) B359921
theorem B566603 : Blo 251819 566603 := bstep (se 1 (by rfl) ⟨424952, by rfl⟩ : syracuseStep 566603 = 849905) B849905
theorem B861515 : Blo 251819 861515 := bstep (se 1 (by rfl) ⟨646136, by rfl⟩ : syracuseStep 861515 = 1292273) B1292273
theorem B566657 : Blo 251819 566657 := bstep (se 2 (by rfl) ⟨212496, by rfl⟩ : syracuseStep 566657 = 424993) B424993
theorem B1287575 : Blo 251819 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B1025453 : Blo 251819 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B566873 : Blo 251819 566873 := bstep (se 2 (by rfl) ⟨212577, by rfl⟩ : syracuseStep 566873 = 425155) B425155
theorem B861785 : Blo 251819 861785 := bstep (se 2 (by rfl) ⟨323169, by rfl⟩ : syracuseStep 861785 = 646339) B646339
theorem B1451621 : Blo 251819 1451621 := bstep (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) B272179
theorem B1091245 : Blo 251819 1091245 := bstep (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) B409217
theorem B566963 : Blo 251819 566963 := bstep (se 1 (by rfl) ⟨425222, by rfl⟩ : syracuseStep 566963 = 850445) B850445
theorem B566999 : Blo 251819 566999 := bstep (se 1 (by rfl) ⟨425249, by rfl⟩ : syracuseStep 566999 = 850499) B850499
theorem B272107 : Blo 251819 272107 := bstep (se 1 (by rfl) ⟨204080, by rfl⟩ : syracuseStep 272107 = 408161) B408161
theorem B567179 : Blo 251819 567179 := bstep (se 1 (by rfl) ⟨425384, by rfl⟩ : syracuseStep 567179 = 850769) B850769
theorem B567233 : Blo 251819 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B1452077 : Blo 251819 1452077 := bstep (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) B544529
theorem B1026199 : Blo 251819 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B567449 : Blo 251819 567449 := bstep (se 2 (by rfl) ⟨212793, by rfl⟩ : syracuseStep 567449 = 425587) B425587
theorem B567539 : Blo 251819 567539 := bstep (se 1 (by rfl) ⟨425654, by rfl⟩ : syracuseStep 567539 = 851309) B851309
theorem B567575 : Blo 251819 567575 := bstep (se 1 (by rfl) ⟨425681, by rfl⟩ : syracuseStep 567575 = 851363) B851363
theorem B862487 : Blo 251819 862487 := bstep (se 1 (by rfl) ⟨646865, by rfl⟩ : syracuseStep 862487 = 1293731) B1293731
theorem B567755 : Blo 251819 567755 := bstep (se 1 (by rfl) ⟨425816, by rfl⟩ : syracuseStep 567755 = 851633) B851633
theorem B567809 : Blo 251819 567809 := bstep (se 2 (by rfl) ⟨212928, by rfl⟩ : syracuseStep 567809 = 425857) B425857
theorem B1878563 : Blo 251819 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B961217 : Blo 251819 961217 := bstep (se 2 (by rfl) ⟨360456, by rfl⟩ : syracuseStep 961217 = 720913) B720913
theorem B568025 : Blo 251819 568025 := bstep (se 2 (by rfl) ⟨213009, by rfl⟩ : syracuseStep 568025 = 426019) B426019
theorem B1452761 : Blo 251819 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B731927 : Blo 251819 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B568115 : Blo 251819 568115 := bstep (se 1 (by rfl) ⟨426086, by rfl⟩ : syracuseStep 568115 = 852173) B852173
theorem B863027 : Blo 251819 863027 := bstep (se 1 (by rfl) ⟨647270, by rfl⟩ : syracuseStep 863027 = 1294541) B1294541
theorem B568151 : Blo 251819 568151 := bstep (se 1 (by rfl) ⟨426113, by rfl⟩ : syracuseStep 568151 = 852227) B852227
theorem B1846147 : Blo 251819 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B568331 : Blo 251819 568331 := bstep (se 1 (by rfl) ⟨426248, by rfl⟩ : syracuseStep 568331 = 852497) B852497
theorem B568385 : Blo 251819 568385 := bstep (se 2 (by rfl) ⟨213144, by rfl⟩ : syracuseStep 568385 = 426289) B426289
theorem B863297 : Blo 251819 863297 := bstep (se 2 (by rfl) ⟨323736, by rfl⟩ : syracuseStep 863297 = 647473) B647473
theorem B863435 : Blo 251819 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B568601 : Blo 251819 568601 := bstep (se 2 (by rfl) ⟨213225, by rfl⟩ : syracuseStep 568601 = 426451) B426451
theorem B568691 : Blo 251819 568691 := bstep (se 1 (by rfl) ⟨426518, by rfl⟩ : syracuseStep 568691 = 853037) B853037
theorem B568727 : Blo 251819 568727 := bstep (se 1 (by rfl) ⟨426545, by rfl⟩ : syracuseStep 568727 = 853091) B853091
theorem B568907 : Blo 251819 568907 := bstep (se 1 (by rfl) ⟨426680, by rfl⟩ : syracuseStep 568907 = 853361) B853361
theorem B568961 : Blo 251819 568961 := bstep (se 2 (by rfl) ⟨213360, by rfl⟩ : syracuseStep 568961 = 426721) B426721
theorem B569177 : Blo 251819 569177 := bstep (se 2 (by rfl) ⟨213441, by rfl⟩ : syracuseStep 569177 = 426883) B426883
theorem B569267 : Blo 251819 569267 := bstep (se 1 (by rfl) ⟨426950, by rfl⟩ : syracuseStep 569267 = 853901) B853901
theorem B569303 : Blo 251819 569303 := bstep (se 1 (by rfl) ⟨426977, by rfl⟩ : syracuseStep 569303 = 853955) B853955
theorem B307211 : Blo 251819 307211 := bstep (se 1 (by rfl) ⟨230408, by rfl⟩ : syracuseStep 307211 = 460817) B460817
theorem B1552459 : Blo 251819 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1028227 : Blo 251819 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B569483 : Blo 251819 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B962705 : Blo 251819 962705 := bstep (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) B722029
theorem B569537 : Blo 251819 569537 := bstep (se 2 (by rfl) ⟨213576, by rfl⟩ : syracuseStep 569537 = 427153) B427153
theorem B9318773 : Blo 251819 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B405911 : Blo 251819 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B569753 : Blo 251819 569753 := bstep (se 2 (by rfl) ⟨213657, by rfl⟩ : syracuseStep 569753 = 427315) B427315
theorem B3912113 : Blo 251819 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B569843 : Blo 251819 569843 := bstep (se 1 (by rfl) ⟨427382, by rfl⟩ : syracuseStep 569843 = 854765) B854765
theorem B569879 : Blo 251819 569879 := bstep (se 1 (by rfl) ⟨427409, by rfl⟩ : syracuseStep 569879 = 854819) B854819
theorem B963161 : Blo 251819 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B570059 : Blo 251819 570059 := bstep (se 1 (by rfl) ⟨427544, by rfl⟩ : syracuseStep 570059 = 855089) B855089
theorem B1749721 : Blo 251819 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B570113 : Blo 251819 570113 := bstep (se 2 (by rfl) ⟨213792, by rfl⟩ : syracuseStep 570113 = 427585) B427585
theorem B963373 : Blo 251819 963373 := bstep (se 3 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 963373 = 361265) B361265
theorem B1291139 : Blo 251819 1291139 := bstep (se 1 (by rfl) ⟨968354, by rfl⟩ : syracuseStep 1291139 = 1936709) B1936709
theorem B2110387 : Blo 251819 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B406475 : Blo 251819 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B570329 : Blo 251819 570329 := bstep (se 2 (by rfl) ⟨213873, by rfl⟩ : syracuseStep 570329 = 427747) B427747
theorem B4174865 : Blo 251819 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B570419 : Blo 251819 570419 := bstep (se 1 (by rfl) ⟨427814, by rfl⟩ : syracuseStep 570419 = 855629) B855629
theorem B570455 : Blo 251819 570455 := bstep (se 1 (by rfl) ⟨427841, by rfl⟩ : syracuseStep 570455 = 855683) B855683
theorem B472153 : Blo 251819 472153 := bstep (se 2 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 472153 = 354115) B354115
theorem B963677 : Blo 251819 963677 := bstep (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) B361379
theorem B570635 : Blo 251819 570635 := bstep (se 1 (by rfl) ⟨427976, by rfl⟩ : syracuseStep 570635 = 855953) B855953
theorem B570689 : Blo 251819 570689 := bstep (se 2 (by rfl) ⟨214008, by rfl⟩ : syracuseStep 570689 = 428017) B428017
theorem B537995 : Blo 251819 537995 := bstep (se 1 (by rfl) ⟨403496, by rfl⟩ : syracuseStep 537995 = 806993) B806993
theorem B1553843 : Blo 251819 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B406987 : Blo 251819 406987 := bstep (se 1 (by rfl) ⟨305240, by rfl⟩ : syracuseStep 406987 = 610481) B610481
theorem B570905 : Blo 251819 570905 := bstep (se 2 (by rfl) ⟨214089, by rfl⟩ : syracuseStep 570905 = 428179) B428179
theorem B570995 : Blo 251819 570995 := bstep (se 1 (by rfl) ⟨428246, by rfl⟩ : syracuseStep 570995 = 856493) B856493
theorem B571031 : Blo 251819 571031 := bstep (se 1 (by rfl) ⟨428273, by rfl⟩ : syracuseStep 571031 = 856547) B856547
theorem B571211 : Blo 251819 571211 := bstep (se 1 (by rfl) ⟨428408, by rfl⟩ : syracuseStep 571211 = 856817) B856817
theorem B571265 : Blo 251819 571265 := bstep (se 2 (by rfl) ⟨214224, by rfl⟩ : syracuseStep 571265 = 428449) B428449
theorem B571481 : Blo 251819 571481 := bstep (se 2 (by rfl) ⟨214305, by rfl⟩ : syracuseStep 571481 = 428611) B428611
theorem B571571 : Blo 251819 571571 := bstep (se 1 (by rfl) ⟨428678, by rfl⟩ : syracuseStep 571571 = 857357) B857357
theorem B571607 : Blo 251819 571607 := bstep (se 1 (by rfl) ⟨428705, by rfl⟩ : syracuseStep 571607 = 857411) B857411
theorem B571787 : Blo 251819 571787 := bstep (se 1 (by rfl) ⟨428840, by rfl⟩ : syracuseStep 571787 = 857681) B857681
theorem B571841 : Blo 251819 571841 := bstep (se 2 (by rfl) ⟨214440, by rfl⟩ : syracuseStep 571841 = 428881) B428881
theorem B1161773 : Blo 251819 1161773 := bstep (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) B435665
theorem B932417 : Blo 251819 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B637591 : Blo 251819 637591 := bstep (se 1 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 637591 = 956387) B956387
theorem B572057 : Blo 251819 572057 := bstep (se 2 (by rfl) ⟨214521, by rfl⟩ : syracuseStep 572057 = 429043) B429043
theorem B572147 : Blo 251819 572147 := bstep (se 1 (by rfl) ⟨429110, by rfl⟩ : syracuseStep 572147 = 858221) B858221
theorem B572183 : Blo 251819 572183 := bstep (se 1 (by rfl) ⟨429137, by rfl⟩ : syracuseStep 572183 = 858275) B858275
theorem B572363 : Blo 251819 572363 := bstep (se 1 (by rfl) ⟨429272, by rfl⟩ : syracuseStep 572363 = 858545) B858545
theorem B539635 : Blo 251819 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B572417 : Blo 251819 572417 := bstep (se 2 (by rfl) ⟨214656, by rfl⟩ : syracuseStep 572417 = 429313) B429313
theorem B638027 : Blo 251819 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B572633 : Blo 251819 572633 := bstep (se 2 (by rfl) ⟨214737, by rfl⟩ : syracuseStep 572633 = 429475) B429475
theorem B572723 : Blo 251819 572723 := bstep (se 1 (by rfl) ⟨429542, by rfl⟩ : syracuseStep 572723 = 859085) B859085
theorem B572759 : Blo 251819 572759 := bstep (se 1 (by rfl) ⟨429569, by rfl⟩ : syracuseStep 572759 = 859139) B859139
theorem B343435 : Blo 251819 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B638401 : Blo 251819 638401 := bstep (se 2 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 638401 = 478801) B478801
theorem B605657 : Blo 251819 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B540121 : Blo 251819 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B572939 : Blo 251819 572939 := bstep (se 1 (by rfl) ⟨429704, by rfl⟩ : syracuseStep 572939 = 859409) B859409
theorem B572993 : Blo 251819 572993 := bstep (se 2 (by rfl) ⟨214872, by rfl⟩ : syracuseStep 572993 = 429745) B429745
theorem B409177 : Blo 251819 409177 := bstep (se 2 (by rfl) ⟨153441, by rfl⟩ : syracuseStep 409177 = 306883) B306883
theorem B769625 : Blo 251819 769625 := bstep (se 2 (by rfl) ⟨288609, by rfl⟩ : syracuseStep 769625 = 577219) B577219
theorem B3259997 : Blo 251819 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B966275 : Blo 251819 966275 := bstep (se 1 (by rfl) ⟨724706, by rfl⟩ : syracuseStep 966275 = 1449413) B1449413
theorem B966289 : Blo 251819 966289 := bstep (se 2 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 966289 = 724717) B724717
theorem B573209 : Blo 251819 573209 := bstep (se 2 (by rfl) ⟨214953, by rfl⟩ : syracuseStep 573209 = 429907) B429907
theorem B3489581 : Blo 251819 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B343883 : Blo 251819 343883 := bstep (se 1 (by rfl) ⟨257912, by rfl⟩ : syracuseStep 343883 = 515825) B515825
theorem B573299 : Blo 251819 573299 := bstep (se 1 (by rfl) ⟨429974, by rfl⟩ : syracuseStep 573299 = 859949) B859949
theorem B573335 : Blo 251819 573335 := bstep (se 1 (by rfl) ⟨430001, by rfl⟩ : syracuseStep 573335 = 860003) B860003
theorem B966593 : Blo 251819 966593 := bstep (se 2 (by rfl) ⟨362472, by rfl⟩ : syracuseStep 966593 = 724945) B724945
theorem B638999 : Blo 251819 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B573515 : Blo 251819 573515 := bstep (se 1 (by rfl) ⟨430136, by rfl⟩ : syracuseStep 573515 = 860273) B860273
theorem B573569 : Blo 251819 573569 := bstep (se 2 (by rfl) ⟨215088, by rfl⟩ : syracuseStep 573569 = 430177) B430177
theorem B4145357 : Blo 251819 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B2179345 : Blo 251819 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B573785 : Blo 251819 573785 := bstep (se 2 (by rfl) ⟨215169, by rfl⟩ : syracuseStep 573785 = 430339) B430339
theorem B3457397 : Blo 251819 3457397 := bstep (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) B324131
theorem B573875 : Blo 251819 573875 := bstep (se 1 (by rfl) ⟨430406, by rfl⟩ : syracuseStep 573875 = 860813) B860813
theorem B573911 : Blo 251819 573911 := bstep (se 1 (by rfl) ⟨430433, by rfl⟩ : syracuseStep 573911 = 860867) B860867
theorem B8176099 : Blo 251819 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B1294865 : Blo 251819 1294865 := bstep (se 2 (by rfl) ⟨485574, by rfl⟩ : syracuseStep 1294865 = 971149) B971149
theorem B2179619 : Blo 251819 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B967261 : Blo 251819 967261 := bstep (se 3 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 967261 = 362723) B362723
theorem B574091 : Blo 251819 574091 := bstep (se 1 (by rfl) ⟨430568, by rfl⟩ : syracuseStep 574091 = 861137) B861137
theorem B1295027 : Blo 251819 1295027 := bstep (se 1 (by rfl) ⟨971270, by rfl⟩ : syracuseStep 1295027 = 1942541) B1942541
theorem B574145 : Blo 251819 574145 := bstep (se 2 (by rfl) ⟨215304, by rfl⟩ : syracuseStep 574145 = 430609) B430609
theorem B639809 : Blo 251819 639809 := bstep (se 2 (by rfl) ⟨239928, by rfl⟩ : syracuseStep 639809 = 479857) B479857
theorem B541505 : Blo 251819 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B377753 : Blo 251819 377753 := bstep (se 2 (by rfl) ⟨141657, by rfl⟩ : syracuseStep 377753 = 283315) B283315
theorem B574361 : Blo 251819 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B574451 : Blo 251819 574451 := bstep (se 1 (by rfl) ⟨430838, by rfl⟩ : syracuseStep 574451 = 861677) B861677
theorem B377867 : Blo 251819 377867 := bstep (se 1 (by rfl) ⟨283400, by rfl⟩ : syracuseStep 377867 = 566801) B566801
theorem B377879 : Blo 251819 377879 := bstep (se 1 (by rfl) ⟨283409, by rfl⟩ : syracuseStep 377879 = 566819) B566819
theorem B574487 : Blo 251819 574487 := bstep (se 1 (by rfl) ⟨430865, by rfl⟩ : syracuseStep 574487 = 861731) B861731
theorem B377945 : Blo 251819 377945 := bstep (se 2 (by rfl) ⟨141729, by rfl⟩ : syracuseStep 377945 = 283459) B283459
theorem B378059 : Blo 251819 378059 := bstep (se 1 (by rfl) ⟨283544, by rfl⟩ : syracuseStep 378059 = 567089) B567089
theorem B574667 : Blo 251819 574667 := bstep (se 1 (by rfl) ⟨431000, by rfl⟩ : syracuseStep 574667 = 862001) B862001
theorem B378071 : Blo 251819 378071 := bstep (se 1 (by rfl) ⟨283553, by rfl⟩ : syracuseStep 378071 = 567107) B567107
theorem B574721 : Blo 251819 574721 := bstep (se 2 (by rfl) ⟨215520, by rfl⟩ : syracuseStep 574721 = 431041) B431041
theorem B1164547 : Blo 251819 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B378137 : Blo 251819 378137 := bstep (se 2 (by rfl) ⟨141801, by rfl⟩ : syracuseStep 378137 = 283603) B283603
theorem B542027 : Blo 251819 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B640345 : Blo 251819 640345 := bstep (se 2 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 640345 = 480259) B480259
theorem B378251 : Blo 251819 378251 := bstep (se 1 (by rfl) ⟨283688, by rfl⟩ : syracuseStep 378251 = 567377) B567377
theorem B378263 : Blo 251819 378263 := bstep (se 1 (by rfl) ⟨283697, by rfl⟩ : syracuseStep 378263 = 567395) B567395
theorem B378329 : Blo 251819 378329 := bstep (se 2 (by rfl) ⟨141873, by rfl⟩ : syracuseStep 378329 = 283747) B283747
theorem B574937 : Blo 251819 574937 := bstep (se 2 (by rfl) ⟨215601, by rfl⟩ : syracuseStep 574937 = 431203) B431203
theorem B706099 : Blo 251819 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B575027 : Blo 251819 575027 := bstep (se 1 (by rfl) ⟨431270, by rfl⟩ : syracuseStep 575027 = 862541) B862541
theorem B378443 : Blo 251819 378443 := bstep (se 1 (by rfl) ⟨283832, by rfl⟩ : syracuseStep 378443 = 567665) B567665
theorem B378455 : Blo 251819 378455 := bstep (se 1 (by rfl) ⟨283841, by rfl⟩ : syracuseStep 378455 = 567683) B567683
theorem B575063 : Blo 251819 575063 := bstep (se 1 (by rfl) ⟨431297, by rfl⟩ : syracuseStep 575063 = 862595) B862595
theorem B378521 : Blo 251819 378521 := bstep (se 2 (by rfl) ⟨141945, by rfl⟩ : syracuseStep 378521 = 283891) B283891
theorem B378635 : Blo 251819 378635 := bstep (se 1 (by rfl) ⟨283976, by rfl⟩ : syracuseStep 378635 = 567953) B567953
theorem B575243 : Blo 251819 575243 := bstep (se 1 (by rfl) ⟨431432, by rfl⟩ : syracuseStep 575243 = 862865) B862865
theorem B378647 : Blo 251819 378647 := bstep (se 1 (by rfl) ⟨283985, by rfl⟩ : syracuseStep 378647 = 567971) B567971
theorem B575297 : Blo 251819 575297 := bstep (se 2 (by rfl) ⟨215736, by rfl⟩ : syracuseStep 575297 = 431473) B431473
theorem B378713 : Blo 251819 378713 := bstep (se 2 (by rfl) ⟨142017, by rfl⟩ : syracuseStep 378713 = 284035) B284035
theorem B608089 : Blo 251819 608089 := bstep (se 2 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 608089 = 456067) B456067
theorem B968537 : Blo 251819 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B378827 : Blo 251819 378827 := bstep (se 1 (by rfl) ⟨284120, by rfl⟩ : syracuseStep 378827 = 568241) B568241
theorem B378839 : Blo 251819 378839 := bstep (se 1 (by rfl) ⟨284129, by rfl⟩ : syracuseStep 378839 = 568259) B568259
theorem B4376537 : Blo 251819 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B378905 : Blo 251819 378905 := bstep (se 2 (by rfl) ⟨142089, by rfl⟩ : syracuseStep 378905 = 284179) B284179
theorem B575513 : Blo 251819 575513 := bstep (se 2 (by rfl) ⟨215817, by rfl⟩ : syracuseStep 575513 = 431635) B431635
theorem B1624157 : Blo 251819 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B379019 : Blo 251819 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B379031 : Blo 251819 379031 := bstep (se 1 (by rfl) ⟨284273, by rfl⟩ : syracuseStep 379031 = 568547) B568547
theorem B1099955 : Blo 251819 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B379097 : Blo 251819 379097 := bstep (se 2 (by rfl) ⟨142161, by rfl⟩ : syracuseStep 379097 = 284323) B284323
theorem B379211 : Blo 251819 379211 := bstep (se 1 (by rfl) ⟨284408, by rfl⟩ : syracuseStep 379211 = 568817) B568817
theorem B379223 : Blo 251819 379223 := bstep (se 1 (by rfl) ⟨284417, by rfl⟩ : syracuseStep 379223 = 568835) B568835
theorem B379289 : Blo 251819 379289 := bstep (se 2 (by rfl) ⟨142233, by rfl⟩ : syracuseStep 379289 = 284467) B284467
theorem B641459 : Blo 251819 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B608705 : Blo 251819 608705 := bstep (se 2 (by rfl) ⟨228264, by rfl⟩ : syracuseStep 608705 = 456529) B456529
theorem B1100249 : Blo 251819 1100249 := bstep (se 2 (by rfl) ⟨412593, by rfl⟩ : syracuseStep 1100249 = 825187) B825187
theorem B379403 : Blo 251819 379403 := bstep (se 1 (by rfl) ⟨284552, by rfl⟩ : syracuseStep 379403 = 569105) B569105
theorem B379415 : Blo 251819 379415 := bstep (se 1 (by rfl) ⟨284561, by rfl⟩ : syracuseStep 379415 = 569123) B569123
theorem B543257 : Blo 251819 543257 := bstep (se 2 (by rfl) ⟨203721, by rfl⟩ : syracuseStep 543257 = 407443) B407443
theorem B510553 : Blo 251819 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B379481 : Blo 251819 379481 := bstep (se 2 (by rfl) ⟨142305, by rfl⟩ : syracuseStep 379481 = 284611) B284611
theorem B379595 : Blo 251819 379595 := bstep (se 1 (by rfl) ⟨284696, by rfl⟩ : syracuseStep 379595 = 569393) B569393
theorem B379607 : Blo 251819 379607 := bstep (se 1 (by rfl) ⟨284705, by rfl⟩ : syracuseStep 379607 = 569411) B569411
theorem B641753 : Blo 251819 641753 := bstep (se 2 (by rfl) ⟨240657, by rfl⟩ : syracuseStep 641753 = 481315) B481315
theorem B379673 : Blo 251819 379673 := bstep (se 2 (by rfl) ⟨142377, by rfl⟩ : syracuseStep 379673 = 284755) B284755
theorem B576343 : Blo 251819 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B379787 : Blo 251819 379787 := bstep (se 1 (by rfl) ⟨284840, by rfl⟩ : syracuseStep 379787 = 569681) B569681
theorem B379799 : Blo 251819 379799 := bstep (se 1 (by rfl) ⟨284849, by rfl⟩ : syracuseStep 379799 = 569699) B569699
theorem B543667 : Blo 251819 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B379865 : Blo 251819 379865 := bstep (se 2 (by rfl) ⟨142449, by rfl⟩ : syracuseStep 379865 = 284899) B284899
theorem B1035281 : Blo 251819 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B379979 : Blo 251819 379979 := bstep (se 1 (by rfl) ⟨284984, by rfl⟩ : syracuseStep 379979 = 569969) B569969
theorem B379991 : Blo 251819 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B511105 : Blo 251819 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B478361 : Blo 251819 478361 := bstep (se 2 (by rfl) ⟨179385, by rfl⟩ : syracuseStep 478361 = 358771) B358771
theorem B380057 : Blo 251819 380057 := bstep (se 2 (by rfl) ⟨142521, by rfl⟩ : syracuseStep 380057 = 285043) B285043
theorem B380171 : Blo 251819 380171 := bstep (se 1 (by rfl) ⟨285128, by rfl⟩ : syracuseStep 380171 = 570257) B570257
theorem B380183 : Blo 251819 380183 := bstep (se 1 (by rfl) ⟨285137, by rfl⟩ : syracuseStep 380183 = 570275) B570275
theorem B380249 : Blo 251819 380249 := bstep (se 2 (by rfl) ⟨142593, by rfl⟩ : syracuseStep 380249 = 285187) B285187
theorem B544153 : Blo 251819 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B970163 : Blo 251819 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B970177 : Blo 251819 970177 := bstep (se 2 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 970177 = 727633) B727633
theorem B380363 : Blo 251819 380363 := bstep (se 1 (by rfl) ⟨285272, by rfl⟩ : syracuseStep 380363 = 570545) B570545
theorem B380375 : Blo 251819 380375 := bstep (se 1 (by rfl) ⟨285281, by rfl⟩ : syracuseStep 380375 = 570563) B570563
theorem B3919373 : Blo 251819 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B2870801 : Blo 251819 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B380441 : Blo 251819 380441 := bstep (se 2 (by rfl) ⟨142665, by rfl⟩ : syracuseStep 380441 = 285331) B285331
theorem B1363549 : Blo 251819 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B380555 : Blo 251819 380555 := bstep (se 1 (by rfl) ⟨285416, by rfl⟩ : syracuseStep 380555 = 570833) B570833
theorem B380567 : Blo 251819 380567 := bstep (se 1 (by rfl) ⟨285425, by rfl⟩ : syracuseStep 380567 = 570851) B570851
theorem B609943 : Blo 251819 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B380633 : Blo 251819 380633 := bstep (se 2 (by rfl) ⟨142737, by rfl⟩ : syracuseStep 380633 = 285475) B285475
theorem B380747 : Blo 251819 380747 := bstep (se 1 (by rfl) ⟨285560, by rfl⟩ : syracuseStep 380747 = 571121) B571121
theorem B380759 : Blo 251819 380759 := bstep (se 1 (by rfl) ⟨285569, by rfl⟩ : syracuseStep 380759 = 571139) B571139
theorem B479105 : Blo 251819 479105 := bstep (se 2 (by rfl) ⟨179664, by rfl⟩ : syracuseStep 479105 = 359329) B359329
theorem B380825 : Blo 251819 380825 := bstep (se 2 (by rfl) ⟨142809, by rfl⟩ : syracuseStep 380825 = 285619) B285619
theorem B380939 : Blo 251819 380939 := bstep (se 1 (by rfl) ⟨285704, by rfl⟩ : syracuseStep 380939 = 571409) B571409
theorem B380951 : Blo 251819 380951 := bstep (se 1 (by rfl) ⟨285713, by rfl⟩ : syracuseStep 380951 = 571427) B571427
theorem B381017 : Blo 251819 381017 := bstep (se 2 (by rfl) ⟨142881, by rfl⟩ : syracuseStep 381017 = 285763) B285763
theorem B544897 : Blo 251819 544897 := bstep (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) B408673
theorem B479371 : Blo 251819 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B381131 : Blo 251819 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B381143 : Blo 251819 381143 := bstep (se 1 (by rfl) ⟨285857, by rfl⟩ : syracuseStep 381143 = 571715) B571715
theorem B381209 : Blo 251819 381209 := bstep (se 2 (by rfl) ⟨142953, by rfl⟩ : syracuseStep 381209 = 285907) B285907
theorem B643403 : Blo 251819 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B381323 : Blo 251819 381323 := bstep (se 1 (by rfl) ⟨285992, by rfl⟩ : syracuseStep 381323 = 571985) B571985
theorem B381335 : Blo 251819 381335 := bstep (se 1 (by rfl) ⟨286001, by rfl⟩ : syracuseStep 381335 = 572003) B572003
theorem B381401 : Blo 251819 381401 := bstep (se 2 (by rfl) ⟨143025, by rfl⟩ : syracuseStep 381401 = 286051) B286051
theorem B479819 : Blo 251819 479819 := bstep (se 1 (by rfl) ⟨359864, by rfl⟩ : syracuseStep 479819 = 719729) B719729
theorem B381515 : Blo 251819 381515 := bstep (se 1 (by rfl) ⟨286136, by rfl⟩ : syracuseStep 381515 = 572273) B572273
theorem B381527 : Blo 251819 381527 := bstep (se 1 (by rfl) ⟨286145, by rfl⟩ : syracuseStep 381527 = 572291) B572291
theorem B381593 : Blo 251819 381593 := bstep (se 2 (by rfl) ⟨143097, by rfl⟩ : syracuseStep 381593 = 286195) B286195
theorem B283351 : Blo 251819 283351 := bstep (se 1 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 283351 = 425027) B425027
theorem B480001 : Blo 251819 480001 := bstep (se 2 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 480001 = 360001) B360001
theorem B381707 : Blo 251819 381707 := bstep (se 1 (by rfl) ⟨286280, by rfl⟩ : syracuseStep 381707 = 572561) B572561
theorem B381719 : Blo 251819 381719 := bstep (se 1 (by rfl) ⟨286289, by rfl⟩ : syracuseStep 381719 = 572579) B572579
theorem B381785 : Blo 251819 381785 := bstep (se 2 (by rfl) ⟨143169, by rfl⟩ : syracuseStep 381785 = 286339) B286339
theorem B283531 : Blo 251819 283531 := bstep (se 1 (by rfl) ⟨212648, by rfl⟩ : syracuseStep 283531 = 425297) B425297
theorem B381899 : Blo 251819 381899 := bstep (se 1 (by rfl) ⟨286424, by rfl⟩ : syracuseStep 381899 = 572849) B572849
theorem B381911 : Blo 251819 381911 := bstep (se 1 (by rfl) ⟨286433, by rfl⟩ : syracuseStep 381911 = 572867) B572867
theorem B283639 : Blo 251819 283639 := bstep (se 1 (by rfl) ⟨212729, by rfl⟩ : syracuseStep 283639 = 425459) B425459
theorem B381977 : Blo 251819 381977 := bstep (se 2 (by rfl) ⟨143241, by rfl⟩ : syracuseStep 381977 = 286483) B286483
theorem B480343 : Blo 251819 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B545879 : Blo 251819 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B382091 : Blo 251819 382091 := bstep (se 1 (by rfl) ⟨286568, by rfl⟩ : syracuseStep 382091 = 573137) B573137
theorem B382103 : Blo 251819 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B283819 : Blo 251819 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B382169 : Blo 251819 382169 := bstep (se 2 (by rfl) ⟨143313, by rfl⟩ : syracuseStep 382169 = 286627) B286627
theorem B808157 : Blo 251819 808157 := bstep (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) B303059
theorem B283927 : Blo 251819 283927 := bstep (se 1 (by rfl) ⟨212945, by rfl⟩ : syracuseStep 283927 = 425891) B425891
theorem B644375 : Blo 251819 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B480563 : Blo 251819 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B382283 : Blo 251819 382283 := bstep (se 1 (by rfl) ⟨286712, by rfl⟩ : syracuseStep 382283 = 573425) B573425
theorem B382295 : Blo 251819 382295 := bstep (se 1 (by rfl) ⟨286721, by rfl⟩ : syracuseStep 382295 = 573443) B573443
theorem B382361 : Blo 251819 382361 := bstep (se 2 (by rfl) ⟨143385, by rfl⟩ : syracuseStep 382361 = 286771) B286771
theorem B284107 : Blo 251819 284107 := bstep (se 1 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 284107 = 426161) B426161
theorem B382475 : Blo 251819 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B480791 : Blo 251819 480791 := bstep (se 1 (by rfl) ⟨360593, by rfl⟩ : syracuseStep 480791 = 721187) B721187
theorem B382487 : Blo 251819 382487 := bstep (se 1 (by rfl) ⟨286865, by rfl⟩ : syracuseStep 382487 = 573731) B573731
theorem B284215 : Blo 251819 284215 := bstep (se 1 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 284215 = 426323) B426323
theorem B382553 : Blo 251819 382553 := bstep (se 2 (by rfl) ⟨143457, by rfl⟩ : syracuseStep 382553 = 286915) B286915
theorem B382667 : Blo 251819 382667 := bstep (se 1 (by rfl) ⟨287000, by rfl⟩ : syracuseStep 382667 = 574001) B574001
theorem B4085453 : Blo 251819 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B382679 : Blo 251819 382679 := bstep (se 1 (by rfl) ⟨287009, by rfl⟩ : syracuseStep 382679 = 574019) B574019
theorem B284395 : Blo 251819 284395 := bstep (se 1 (by rfl) ⟨213296, by rfl⟩ : syracuseStep 284395 = 426593) B426593
theorem B481049 : Blo 251819 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B382745 : Blo 251819 382745 := bstep (se 2 (by rfl) ⟨143529, by rfl⟩ : syracuseStep 382745 = 287059) B287059
theorem B284503 : Blo 251819 284503 := bstep (se 1 (by rfl) ⟨213377, by rfl⟩ : syracuseStep 284503 = 426755) B426755
theorem B382859 : Blo 251819 382859 := bstep (se 1 (by rfl) ⟨287144, by rfl⟩ : syracuseStep 382859 = 574289) B574289
theorem B382871 : Blo 251819 382871 := bstep (se 1 (by rfl) ⟨287153, by rfl⟩ : syracuseStep 382871 = 574307) B574307
theorem B251819 : Blo 251819 251819 := bstep (se 1 (by rfl) ⟨188864, by rfl⟩ : syracuseStep 251819 = 377729) B377729
theorem B645043 : Blo 251819 645043 := bstep (se 1 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 645043 = 967565) B967565
theorem B251831 : Blo 251819 251831 := bstep (se 1 (by rfl) ⟨188873, by rfl⟩ : syracuseStep 251831 = 377747) B377747
theorem B251851 : Blo 251819 251851 := bstep (se 1 (by rfl) ⟨188888, by rfl⟩ : syracuseStep 251851 = 377777) B377777
theorem B251863 : Blo 251819 251863 := bstep (se 1 (by rfl) ⟨188897, by rfl⟩ : syracuseStep 251863 = 377795) B377795
theorem B3233753 : Blo 251819 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B382937 : Blo 251819 382937 := bstep (se 2 (by rfl) ⟨143601, by rfl⟩ : syracuseStep 382937 = 287203) B287203
theorem B251883 : Blo 251819 251883 := bstep (se 1 (by rfl) ⟨188912, by rfl⟩ : syracuseStep 251883 = 377825) B377825
theorem B251895 : Blo 251819 251895 := bstep (se 1 (by rfl) ⟨188921, by rfl⟩ : syracuseStep 251895 = 377843) B377843
theorem B546817 : Blo 251819 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B251915 : Blo 251819 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B284683 : Blo 251819 284683 := bstep (se 1 (by rfl) ⟨213512, by rfl⟩ : syracuseStep 284683 = 427025) B427025
theorem B251927 : Blo 251819 251927 := bstep (se 1 (by rfl) ⟨188945, by rfl⟩ : syracuseStep 251927 = 377891) B377891
theorem B251947 : Blo 251819 251947 := bstep (se 1 (by rfl) ⟨188960, by rfl⟩ : syracuseStep 251947 = 377921) B377921
theorem B251959 : Blo 251819 251959 := bstep (se 1 (by rfl) ⟨188969, by rfl⟩ : syracuseStep 251959 = 377939) B377939
theorem B645185 : Blo 251819 645185 := bstep (se 2 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 645185 = 483889) B483889
theorem B251979 : Blo 251819 251979 := bstep (se 1 (by rfl) ⟨188984, by rfl⟩ : syracuseStep 251979 = 377969) B377969
theorem B383051 : Blo 251819 383051 := bstep (se 1 (by rfl) ⟨287288, by rfl⟩ : syracuseStep 383051 = 574577) B574577
theorem B251991 : Blo 251819 251991 := bstep (se 1 (by rfl) ⟨188993, by rfl⟩ : syracuseStep 251991 = 377987) B377987
theorem B383063 : Blo 251819 383063 := bstep (se 1 (by rfl) ⟨287297, by rfl⟩ : syracuseStep 383063 = 574595) B574595
theorem B546905 : Blo 251819 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B874585 : Blo 251819 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B1824869 : Blo 251819 1824869 := bstep (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) B342163
theorem B252011 : Blo 251819 252011 := bstep (se 1 (by rfl) ⟨189008, by rfl⟩ : syracuseStep 252011 = 378017) B378017
theorem B252023 : Blo 251819 252023 := bstep (se 1 (by rfl) ⟨189017, by rfl⟩ : syracuseStep 252023 = 378035) B378035
theorem B284791 : Blo 251819 284791 := bstep (se 1 (by rfl) ⟨213593, by rfl⟩ : syracuseStep 284791 = 427187) B427187
theorem B252043 : Blo 251819 252043 := bstep (se 1 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 252043 = 378065) B378065
theorem B546955 : Blo 251819 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B252055 : Blo 251819 252055 := bstep (se 1 (by rfl) ⟨189041, by rfl⟩ : syracuseStep 252055 = 378083) B378083
theorem B579737 : Blo 251819 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B383129 : Blo 251819 383129 := bstep (se 2 (by rfl) ⟨143673, by rfl⟩ : syracuseStep 383129 = 287347) B287347
theorem B252075 : Blo 251819 252075 := bstep (se 1 (by rfl) ⟨189056, by rfl⟩ : syracuseStep 252075 = 378113) B378113
theorem B481459 : Blo 251819 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B252087 : Blo 251819 252087 := bstep (se 1 (by rfl) ⟨189065, by rfl⟩ : syracuseStep 252087 = 378131) B378131
theorem B252107 : Blo 251819 252107 := bstep (se 1 (by rfl) ⟨189080, by rfl⟩ : syracuseStep 252107 = 378161) B378161
theorem B252119 : Blo 251819 252119 := bstep (se 1 (by rfl) ⟨189089, by rfl⟩ : syracuseStep 252119 = 378179) B378179
theorem B252139 : Blo 251819 252139 := bstep (se 1 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 252139 = 378209) B378209
theorem B252151 : Blo 251819 252151 := bstep (se 1 (by rfl) ⟨189113, by rfl⟩ : syracuseStep 252151 = 378227) B378227
theorem B252171 : Blo 251819 252171 := bstep (se 1 (by rfl) ⟨189128, by rfl⟩ : syracuseStep 252171 = 378257) B378257
theorem B383243 : Blo 251819 383243 := bstep (se 1 (by rfl) ⟨287432, by rfl⟩ : syracuseStep 383243 = 574865) B574865
theorem B252183 : Blo 251819 252183 := bstep (se 1 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 252183 = 378275) B378275
theorem B383255 : Blo 251819 383255 := bstep (se 1 (by rfl) ⟨287441, by rfl⟩ : syracuseStep 383255 = 574883) B574883
theorem B252203 : Blo 251819 252203 := bstep (se 1 (by rfl) ⟨189152, by rfl⟩ : syracuseStep 252203 = 378305) B378305
theorem B284971 : Blo 251819 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B252215 : Blo 251819 252215 := bstep (se 1 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 252215 = 378323) B378323
theorem B252235 : Blo 251819 252235 := bstep (se 1 (by rfl) ⟨189176, by rfl⟩ : syracuseStep 252235 = 378353) B378353
theorem B252247 : Blo 251819 252247 := bstep (se 1 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 252247 = 378371) B378371
theorem B383321 : Blo 251819 383321 := bstep (se 2 (by rfl) ⟨143745, by rfl⟩ : syracuseStep 383321 = 287491) B287491
theorem B252267 : Blo 251819 252267 := bstep (se 1 (by rfl) ⟨189200, by rfl⟩ : syracuseStep 252267 = 378401) B378401
theorem B2873717 : Blo 251819 2873717 := bstep (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) B269411
theorem B252279 : Blo 251819 252279 := bstep (se 1 (by rfl) ⟨189209, by rfl⟩ : syracuseStep 252279 = 378419) B378419
theorem B252299 : Blo 251819 252299 := bstep (se 1 (by rfl) ⟨189224, by rfl⟩ : syracuseStep 252299 = 378449) B378449
theorem B252311 : Blo 251819 252311 := bstep (se 1 (by rfl) ⟨189233, by rfl⟩ : syracuseStep 252311 = 378467) B378467
theorem B285079 : Blo 251819 285079 := bstep (se 1 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 285079 = 427619) B427619
theorem B252331 : Blo 251819 252331 := bstep (se 1 (by rfl) ⟨189248, by rfl⟩ : syracuseStep 252331 = 378497) B378497
theorem B252343 : Blo 251819 252343 := bstep (se 1 (by rfl) ⟨189257, by rfl⟩ : syracuseStep 252343 = 378515) B378515
theorem B252363 : Blo 251819 252363 := bstep (se 1 (by rfl) ⟨189272, by rfl⟩ : syracuseStep 252363 = 378545) B378545
theorem B383435 : Blo 251819 383435 := bstep (se 1 (by rfl) ⟨287576, by rfl⟩ : syracuseStep 383435 = 575153) B575153
theorem B252375 : Blo 251819 252375 := bstep (se 1 (by rfl) ⟨189281, by rfl⟩ : syracuseStep 252375 = 378563) B378563
theorem B383447 : Blo 251819 383447 := bstep (se 1 (by rfl) ⟨287585, by rfl⟩ : syracuseStep 383447 = 575171) B575171
theorem B252395 : Blo 251819 252395 := bstep (se 1 (by rfl) ⟨189296, by rfl⟩ : syracuseStep 252395 = 378593) B378593
theorem B252407 : Blo 251819 252407 := bstep (se 1 (by rfl) ⟨189305, by rfl⟩ : syracuseStep 252407 = 378611) B378611
theorem B252427 : Blo 251819 252427 := bstep (se 1 (by rfl) ⟨189320, by rfl⟩ : syracuseStep 252427 = 378641) B378641
theorem B252439 : Blo 251819 252439 := bstep (se 1 (by rfl) ⟨189329, by rfl⟩ : syracuseStep 252439 = 378659) B378659
theorem B383513 : Blo 251819 383513 := bstep (se 2 (by rfl) ⟨143817, by rfl⟩ : syracuseStep 383513 = 287635) B287635
theorem B252459 : Blo 251819 252459 := bstep (se 1 (by rfl) ⟨189344, by rfl⟩ : syracuseStep 252459 = 378689) B378689
theorem B252471 : Blo 251819 252471 := bstep (se 1 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 252471 = 378707) B378707
theorem B252491 : Blo 251819 252491 := bstep (se 1 (by rfl) ⟨189368, by rfl⟩ : syracuseStep 252491 = 378737) B378737
theorem B285259 : Blo 251819 285259 := bstep (se 1 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 285259 = 427889) B427889
theorem B1628747 : Blo 251819 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B252503 : Blo 251819 252503 := bstep (se 1 (by rfl) ⟨189377, by rfl⟩ : syracuseStep 252503 = 378755) B378755
theorem B252523 : Blo 251819 252523 := bstep (se 1 (by rfl) ⟨189392, by rfl⟩ : syracuseStep 252523 = 378785) B378785
theorem B252535 : Blo 251819 252535 := bstep (se 1 (by rfl) ⟨189401, by rfl⟩ : syracuseStep 252535 = 378803) B378803
theorem B252555 : Blo 251819 252555 := bstep (se 1 (by rfl) ⟨189416, by rfl⟩ : syracuseStep 252555 = 378833) B378833
theorem B383627 : Blo 251819 383627 := bstep (se 1 (by rfl) ⟨287720, by rfl⟩ : syracuseStep 383627 = 575441) B575441
theorem B252567 : Blo 251819 252567 := bstep (se 1 (by rfl) ⟨189425, by rfl⟩ : syracuseStep 252567 = 378851) B378851
theorem B383639 : Blo 251819 383639 := bstep (se 1 (by rfl) ⟨287729, by rfl⟩ : syracuseStep 383639 = 575459) B575459
theorem B481945 : Blo 251819 481945 := bstep (se 2 (by rfl) ⟨180729, by rfl⟩ : syracuseStep 481945 = 361459) B361459
theorem B252587 : Blo 251819 252587 := bstep (se 1 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 252587 = 378881) B378881
theorem B252599 : Blo 251819 252599 := bstep (se 1 (by rfl) ⟨189449, by rfl⟩ : syracuseStep 252599 = 378899) B378899
theorem B285367 : Blo 251819 285367 := bstep (se 1 (by rfl) ⟨214025, by rfl⟩ : syracuseStep 285367 = 428051) B428051
theorem B252619 : Blo 251819 252619 := bstep (se 1 (by rfl) ⟨189464, by rfl⟩ : syracuseStep 252619 = 378929) B378929
theorem B252631 : Blo 251819 252631 := bstep (se 1 (by rfl) ⟨189473, by rfl⟩ : syracuseStep 252631 = 378947) B378947
theorem B383705 : Blo 251819 383705 := bstep (se 2 (by rfl) ⟨143889, by rfl⟩ : syracuseStep 383705 = 287779) B287779
theorem B252651 : Blo 251819 252651 := bstep (se 1 (by rfl) ⟨189488, by rfl⟩ : syracuseStep 252651 = 378977) B378977
theorem B252663 : Blo 251819 252663 := bstep (se 1 (by rfl) ⟨189497, by rfl⟩ : syracuseStep 252663 = 378995) B378995
theorem B252683 : Blo 251819 252683 := bstep (se 1 (by rfl) ⟨189512, by rfl⟩ : syracuseStep 252683 = 379025) B379025
theorem B252695 : Blo 251819 252695 := bstep (se 1 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 252695 = 379043) B379043
theorem B252715 : Blo 251819 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B252727 : Blo 251819 252727 := bstep (se 1 (by rfl) ⟨189545, by rfl⟩ : syracuseStep 252727 = 379091) B379091
theorem B252747 : Blo 251819 252747 := bstep (se 1 (by rfl) ⟨189560, by rfl⟩ : syracuseStep 252747 = 379121) B379121
theorem B252759 : Blo 251819 252759 := bstep (se 1 (by rfl) ⟨189569, by rfl⟩ : syracuseStep 252759 = 379139) B379139
theorem B6216547 : Blo 251819 6216547 := bstep (se 1 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 6216547 = 9324821) B9324821
theorem B252779 : Blo 251819 252779 := bstep (se 1 (by rfl) ⟨189584, by rfl⟩ : syracuseStep 252779 = 379169) B379169
theorem B285547 : Blo 251819 285547 := bstep (se 1 (by rfl) ⟨214160, by rfl⟩ : syracuseStep 285547 = 428321) B428321
theorem B252791 : Blo 251819 252791 := bstep (se 1 (by rfl) ⟨189593, by rfl⟩ : syracuseStep 252791 = 379187) B379187
theorem B252811 : Blo 251819 252811 := bstep (se 1 (by rfl) ⟨189608, by rfl⟩ : syracuseStep 252811 = 379217) B379217
theorem B252823 : Blo 251819 252823 := bstep (se 1 (by rfl) ⟨189617, by rfl⟩ : syracuseStep 252823 = 379235) B379235
theorem B252843 : Blo 251819 252843 := bstep (se 1 (by rfl) ⟨189632, by rfl⟩ : syracuseStep 252843 = 379265) B379265
theorem B252855 : Blo 251819 252855 := bstep (se 1 (by rfl) ⟨189641, by rfl⟩ : syracuseStep 252855 = 379283) B379283
theorem B252875 : Blo 251819 252875 := bstep (se 1 (by rfl) ⟨189656, by rfl⟩ : syracuseStep 252875 = 379313) B379313
theorem B252887 : Blo 251819 252887 := bstep (se 1 (by rfl) ⟨189665, by rfl⟩ : syracuseStep 252887 = 379331) B379331
theorem B285655 : Blo 251819 285655 := bstep (se 1 (by rfl) ⟨214241, by rfl⟩ : syracuseStep 285655 = 428483) B428483
theorem B252907 : Blo 251819 252907 := bstep (se 1 (by rfl) ⟨189680, by rfl⟩ : syracuseStep 252907 = 379361) B379361
theorem B252919 : Blo 251819 252919 := bstep (se 1 (by rfl) ⟨189689, by rfl⟩ : syracuseStep 252919 = 379379) B379379
theorem B252939 : Blo 251819 252939 := bstep (se 1 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 252939 = 379409) B379409
theorem B252951 : Blo 251819 252951 := bstep (se 1 (by rfl) ⟨189713, by rfl⟩ : syracuseStep 252951 = 379427) B379427
theorem B252971 : Blo 251819 252971 := bstep (se 1 (by rfl) ⟨189728, by rfl⟩ : syracuseStep 252971 = 379457) B379457
theorem B252983 : Blo 251819 252983 := bstep (se 1 (by rfl) ⟨189737, by rfl⟩ : syracuseStep 252983 = 379475) B379475
theorem B253003 : Blo 251819 253003 := bstep (se 1 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 253003 = 379505) B379505
theorem B253015 : Blo 251819 253015 := bstep (se 1 (by rfl) ⟨189761, by rfl⟩ : syracuseStep 253015 = 379523) B379523
theorem B253035 : Blo 251819 253035 := bstep (se 1 (by rfl) ⟨189776, by rfl⟩ : syracuseStep 253035 = 379553) B379553
theorem B253047 : Blo 251819 253047 := bstep (se 1 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 253047 = 379571) B379571
theorem B253067 : Blo 251819 253067 := bstep (se 1 (by rfl) ⟨189800, by rfl⟩ : syracuseStep 253067 = 379601) B379601
theorem B285835 : Blo 251819 285835 := bstep (se 1 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 285835 = 428753) B428753
theorem B253079 : Blo 251819 253079 := bstep (se 1 (by rfl) ⟨189809, by rfl⟩ : syracuseStep 253079 = 379619) B379619
theorem B253099 : Blo 251819 253099 := bstep (se 1 (by rfl) ⟨189824, by rfl⟩ : syracuseStep 253099 = 379649) B379649
theorem B253111 : Blo 251819 253111 := bstep (se 1 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 253111 = 379667) B379667
theorem B253131 : Blo 251819 253131 := bstep (se 1 (by rfl) ⟨189848, by rfl⟩ : syracuseStep 253131 = 379697) B379697
theorem B482507 : Blo 251819 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B253143 : Blo 251819 253143 := bstep (se 1 (by rfl) ⟨189857, by rfl⟩ : syracuseStep 253143 = 379715) B379715
theorem B253163 : Blo 251819 253163 := bstep (se 1 (by rfl) ⟨189872, by rfl⟩ : syracuseStep 253163 = 379745) B379745
theorem B253175 : Blo 251819 253175 := bstep (se 1 (by rfl) ⟨189881, by rfl⟩ : syracuseStep 253175 = 379763) B379763
theorem B285943 : Blo 251819 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B253195 : Blo 251819 253195 := bstep (se 1 (by rfl) ⟨189896, by rfl⟩ : syracuseStep 253195 = 379793) B379793
theorem B253207 : Blo 251819 253207 := bstep (se 1 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 253207 = 379811) B379811
theorem B253227 : Blo 251819 253227 := bstep (se 1 (by rfl) ⟨189920, by rfl⟩ : syracuseStep 253227 = 379841) B379841
theorem B646451 : Blo 251819 646451 := bstep (se 1 (by rfl) ⟨484838, by rfl⟩ : syracuseStep 646451 = 969677) B969677
theorem B253239 : Blo 251819 253239 := bstep (se 1 (by rfl) ⟨189929, by rfl⟩ : syracuseStep 253239 = 379859) B379859
theorem B253259 : Blo 251819 253259 := bstep (se 1 (by rfl) ⟨189944, by rfl⟩ : syracuseStep 253259 = 379889) B379889
theorem B253271 : Blo 251819 253271 := bstep (se 1 (by rfl) ⟨189953, by rfl⟩ : syracuseStep 253271 = 379907) B379907
theorem B253291 : Blo 251819 253291 := bstep (se 1 (by rfl) ⟨189968, by rfl⟩ : syracuseStep 253291 = 379937) B379937
theorem B253303 : Blo 251819 253303 := bstep (se 1 (by rfl) ⟨189977, by rfl⟩ : syracuseStep 253303 = 379955) B379955
theorem B482689 : Blo 251819 482689 := bstep (se 2 (by rfl) ⟨181008, by rfl⟩ : syracuseStep 482689 = 362017) B362017
theorem B253323 : Blo 251819 253323 := bstep (se 1 (by rfl) ⟨189992, by rfl⟩ : syracuseStep 253323 = 379985) B379985
theorem B253335 : Blo 251819 253335 := bstep (se 1 (by rfl) ⟨190001, by rfl⟩ : syracuseStep 253335 = 380003) B380003
theorem B253355 : Blo 251819 253355 := bstep (se 1 (by rfl) ⟨190016, by rfl⟩ : syracuseStep 253355 = 380033) B380033
theorem B286123 : Blo 251819 286123 := bstep (se 1 (by rfl) ⟨214592, by rfl⟩ : syracuseStep 286123 = 429185) B429185
theorem B253367 : Blo 251819 253367 := bstep (se 1 (by rfl) ⟨190025, by rfl⟩ : syracuseStep 253367 = 380051) B380051
theorem B253387 : Blo 251819 253387 := bstep (se 1 (by rfl) ⟨190040, by rfl⟩ : syracuseStep 253387 = 380081) B380081
theorem B253399 : Blo 251819 253399 := bstep (se 1 (by rfl) ⟨190049, by rfl⟩ : syracuseStep 253399 = 380099) B380099
theorem B253419 : Blo 251819 253419 := bstep (se 1 (by rfl) ⟨190064, by rfl⟩ : syracuseStep 253419 = 380129) B380129
theorem B581107 : Blo 251819 581107 := bstep (se 1 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 581107 = 871661) B871661
theorem B253431 : Blo 251819 253431 := bstep (se 1 (by rfl) ⟨190073, by rfl⟩ : syracuseStep 253431 = 380147) B380147
theorem B253451 : Blo 251819 253451 := bstep (se 1 (by rfl) ⟨190088, by rfl⟩ : syracuseStep 253451 = 380177) B380177
theorem B253463 : Blo 251819 253463 := bstep (se 1 (by rfl) ⟨190097, by rfl⟩ : syracuseStep 253463 = 380195) B380195
theorem B286231 : Blo 251819 286231 := bstep (se 1 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 286231 = 429347) B429347
theorem B253483 : Blo 251819 253483 := bstep (se 1 (by rfl) ⟨190112, by rfl⟩ : syracuseStep 253483 = 380225) B380225
theorem B253495 : Blo 251819 253495 := bstep (se 1 (by rfl) ⟨190121, by rfl⟩ : syracuseStep 253495 = 380243) B380243
theorem B2154059 : Blo 251819 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B253515 : Blo 251819 253515 := bstep (se 1 (by rfl) ⟨190136, by rfl⟩ : syracuseStep 253515 = 380273) B380273
theorem B253527 : Blo 251819 253527 := bstep (se 1 (by rfl) ⟨190145, by rfl⟩ : syracuseStep 253527 = 380291) B380291
theorem B253547 : Blo 251819 253547 := bstep (se 1 (by rfl) ⟨190160, by rfl⟩ : syracuseStep 253547 = 380321) B380321
theorem B253559 : Blo 251819 253559 := bstep (se 1 (by rfl) ⟨190169, by rfl⟩ : syracuseStep 253559 = 380339) B380339
theorem B253579 : Blo 251819 253579 := bstep (se 1 (by rfl) ⟨190184, by rfl⟩ : syracuseStep 253579 = 380369) B380369
theorem B253591 : Blo 251819 253591 := bstep (se 1 (by rfl) ⟨190193, by rfl⟩ : syracuseStep 253591 = 380387) B380387
theorem B253611 : Blo 251819 253611 := bstep (se 1 (by rfl) ⟨190208, by rfl⟩ : syracuseStep 253611 = 380417) B380417
theorem B253623 : Blo 251819 253623 := bstep (se 1 (by rfl) ⟨190217, by rfl⟩ : syracuseStep 253623 = 380435) B380435
theorem B253643 : Blo 251819 253643 := bstep (se 1 (by rfl) ⟨190232, by rfl⟩ : syracuseStep 253643 = 380465) B380465
theorem B286411 : Blo 251819 286411 := bstep (se 1 (by rfl) ⟨214808, by rfl⟩ : syracuseStep 286411 = 429617) B429617
theorem B253655 : Blo 251819 253655 := bstep (se 1 (by rfl) ⟨190241, by rfl⟩ : syracuseStep 253655 = 380483) B380483
theorem B253675 : Blo 251819 253675 := bstep (se 1 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 253675 = 380513) B380513
theorem B253687 : Blo 251819 253687 := bstep (se 1 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 253687 = 380531) B380531
theorem B253707 : Blo 251819 253707 := bstep (se 1 (by rfl) ⟨190280, by rfl⟩ : syracuseStep 253707 = 380561) B380561
theorem B253719 : Blo 251819 253719 := bstep (se 1 (by rfl) ⟨190289, by rfl⟩ : syracuseStep 253719 = 380579) B380579
theorem B253739 : Blo 251819 253739 := bstep (se 1 (by rfl) ⟨190304, by rfl⟩ : syracuseStep 253739 = 380609) B380609
theorem B253751 : Blo 251819 253751 := bstep (se 1 (by rfl) ⟨190313, by rfl⟩ : syracuseStep 253751 = 380627) B380627
theorem B286519 : Blo 251819 286519 := bstep (se 1 (by rfl) ⟨214889, by rfl⟩ : syracuseStep 286519 = 429779) B429779
theorem B253771 : Blo 251819 253771 := bstep (se 1 (by rfl) ⟨190328, by rfl⟩ : syracuseStep 253771 = 380657) B380657
theorem B646987 : Blo 251819 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B253783 : Blo 251819 253783 := bstep (se 1 (by rfl) ⟨190337, by rfl⟩ : syracuseStep 253783 = 380675) B380675
theorem B253803 : Blo 251819 253803 := bstep (se 1 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 253803 = 380705) B380705
theorem B253815 : Blo 251819 253815 := bstep (se 1 (by rfl) ⟨190361, by rfl⟩ : syracuseStep 253815 = 380723) B380723
theorem B253835 : Blo 251819 253835 := bstep (se 1 (by rfl) ⟨190376, by rfl⟩ : syracuseStep 253835 = 380753) B380753
theorem B253847 : Blo 251819 253847 := bstep (se 1 (by rfl) ⟨190385, by rfl⟩ : syracuseStep 253847 = 380771) B380771
theorem B253867 : Blo 251819 253867 := bstep (se 1 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 253867 = 380801) B380801
theorem B253879 : Blo 251819 253879 := bstep (se 1 (by rfl) ⟨190409, by rfl⟩ : syracuseStep 253879 = 380819) B380819
theorem B253899 : Blo 251819 253899 := bstep (se 1 (by rfl) ⟨190424, by rfl⟩ : syracuseStep 253899 = 380849) B380849
theorem B253911 : Blo 251819 253911 := bstep (se 1 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 253911 = 380867) B380867
theorem B647129 : Blo 251819 647129 := bstep (se 2 (by rfl) ⟨242673, by rfl⟩ : syracuseStep 647129 = 485347) B485347
theorem B253931 : Blo 251819 253931 := bstep (se 1 (by rfl) ⟨190448, by rfl⟩ : syracuseStep 253931 = 380897) B380897
theorem B286699 : Blo 251819 286699 := bstep (se 1 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 286699 = 430049) B430049
theorem B253943 : Blo 251819 253943 := bstep (se 1 (by rfl) ⟨190457, by rfl⟩ : syracuseStep 253943 = 380915) B380915
theorem B253963 : Blo 251819 253963 := bstep (se 1 (by rfl) ⟨190472, by rfl⟩ : syracuseStep 253963 = 380945) B380945
theorem B253975 : Blo 251819 253975 := bstep (se 1 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 253975 = 380963) B380963
theorem B253995 : Blo 251819 253995 := bstep (se 1 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 253995 = 380993) B380993
theorem B254007 : Blo 251819 254007 := bstep (se 1 (by rfl) ⟨190505, by rfl⟩ : syracuseStep 254007 = 381011) B381011
theorem B11952197 : Blo 251819 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B254027 : Blo 251819 254027 := bstep (se 1 (by rfl) ⟨190520, by rfl⟩ : syracuseStep 254027 = 381041) B381041
theorem B483403 : Blo 251819 483403 := bstep (se 1 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 483403 = 725105) B725105
theorem B254039 : Blo 251819 254039 := bstep (se 1 (by rfl) ⟨190529, by rfl⟩ : syracuseStep 254039 = 381059) B381059
theorem B286807 : Blo 251819 286807 := bstep (se 1 (by rfl) ⟨215105, by rfl⟩ : syracuseStep 286807 = 430211) B430211
theorem B254059 : Blo 251819 254059 := bstep (se 1 (by rfl) ⟨190544, by rfl⟩ : syracuseStep 254059 = 381089) B381089
theorem B254071 : Blo 251819 254071 := bstep (se 1 (by rfl) ⟨190553, by rfl⟩ : syracuseStep 254071 = 381107) B381107
theorem B254091 : Blo 251819 254091 := bstep (se 1 (by rfl) ⟨190568, by rfl⟩ : syracuseStep 254091 = 381137) B381137
theorem B254103 : Blo 251819 254103 := bstep (se 1 (by rfl) ⟨190577, by rfl⟩ : syracuseStep 254103 = 381155) B381155
theorem B483479 : Blo 251819 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B254123 : Blo 251819 254123 := bstep (se 1 (by rfl) ⟨190592, by rfl⟩ : syracuseStep 254123 = 381185) B381185
theorem B254135 : Blo 251819 254135 := bstep (se 1 (by rfl) ⟨190601, by rfl⟩ : syracuseStep 254135 = 381203) B381203
theorem B254155 : Blo 251819 254155 := bstep (se 1 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 254155 = 381233) B381233
theorem B254167 : Blo 251819 254167 := bstep (se 1 (by rfl) ⟨190625, by rfl⟩ : syracuseStep 254167 = 381251) B381251
theorem B254187 : Blo 251819 254187 := bstep (se 1 (by rfl) ⟨190640, by rfl⟩ : syracuseStep 254187 = 381281) B381281
theorem B254199 : Blo 251819 254199 := bstep (se 1 (by rfl) ⟨190649, by rfl⟩ : syracuseStep 254199 = 381299) B381299
theorem B254219 : Blo 251819 254219 := bstep (se 1 (by rfl) ⟨190664, by rfl⟩ : syracuseStep 254219 = 381329) B381329
theorem B286987 : Blo 251819 286987 := bstep (se 1 (by rfl) ⟨215240, by rfl⟩ : syracuseStep 286987 = 430481) B430481
theorem B254231 : Blo 251819 254231 := bstep (se 1 (by rfl) ⟨190673, by rfl⟩ : syracuseStep 254231 = 381347) B381347
theorem B254251 : Blo 251819 254251 := bstep (se 1 (by rfl) ⟨190688, by rfl⟩ : syracuseStep 254251 = 381377) B381377
theorem B254263 : Blo 251819 254263 := bstep (se 1 (by rfl) ⟨190697, by rfl⟩ : syracuseStep 254263 = 381395) B381395
theorem B254283 : Blo 251819 254283 := bstep (se 1 (by rfl) ⟨190712, by rfl⟩ : syracuseStep 254283 = 381425) B381425
theorem B254295 : Blo 251819 254295 := bstep (se 1 (by rfl) ⟨190721, by rfl⟩ : syracuseStep 254295 = 381443) B381443
theorem B254315 : Blo 251819 254315 := bstep (se 1 (by rfl) ⟨190736, by rfl⟩ : syracuseStep 254315 = 381473) B381473
theorem B3236213 : Blo 251819 3236213 := bstep (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) B303395
theorem B254327 : Blo 251819 254327 := bstep (se 1 (by rfl) ⟨190745, by rfl⟩ : syracuseStep 254327 = 381491) B381491
theorem B287095 : Blo 251819 287095 := bstep (se 1 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 287095 = 430643) B430643
theorem B254347 : Blo 251819 254347 := bstep (se 1 (by rfl) ⟨190760, by rfl⟩ : syracuseStep 254347 = 381521) B381521
theorem B254359 : Blo 251819 254359 := bstep (se 1 (by rfl) ⟨190769, by rfl⟩ : syracuseStep 254359 = 381539) B381539
theorem B254379 : Blo 251819 254379 := bstep (se 1 (by rfl) ⟨190784, by rfl⟩ : syracuseStep 254379 = 381569) B381569
theorem B254391 : Blo 251819 254391 := bstep (se 1 (by rfl) ⟨190793, by rfl⟩ : syracuseStep 254391 = 381587) B381587
theorem B254411 : Blo 251819 254411 := bstep (se 1 (by rfl) ⟨190808, by rfl⟩ : syracuseStep 254411 = 381617) B381617
theorem B254423 : Blo 251819 254423 := bstep (se 1 (by rfl) ⟨190817, by rfl⟩ : syracuseStep 254423 = 381635) B381635
theorem B254443 : Blo 251819 254443 := bstep (se 1 (by rfl) ⟨190832, by rfl⟩ : syracuseStep 254443 = 381665) B381665
theorem B254455 : Blo 251819 254455 := bstep (se 1 (by rfl) ⟨190841, by rfl⟩ : syracuseStep 254455 = 381683) B381683
theorem B254475 : Blo 251819 254475 := bstep (se 1 (by rfl) ⟨190856, by rfl⟩ : syracuseStep 254475 = 381713) B381713
theorem B254487 : Blo 251819 254487 := bstep (se 1 (by rfl) ⟨190865, by rfl⟩ : syracuseStep 254487 = 381731) B381731
theorem B254507 : Blo 251819 254507 := bstep (se 1 (by rfl) ⟨190880, by rfl⟩ : syracuseStep 254507 = 381761) B381761
theorem B287275 : Blo 251819 287275 := bstep (se 1 (by rfl) ⟨215456, by rfl⟩ : syracuseStep 287275 = 430913) B430913
theorem B254519 : Blo 251819 254519 := bstep (se 1 (by rfl) ⟨190889, by rfl⟩ : syracuseStep 254519 = 381779) B381779
theorem B909899 : Blo 251819 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B254539 : Blo 251819 254539 := bstep (se 1 (by rfl) ⟨190904, by rfl⟩ : syracuseStep 254539 = 381809) B381809
theorem B254551 : Blo 251819 254551 := bstep (se 1 (by rfl) ⟨190913, by rfl⟩ : syracuseStep 254551 = 381827) B381827
theorem B254571 : Blo 251819 254571 := bstep (se 1 (by rfl) ⟨190928, by rfl⟩ : syracuseStep 254571 = 381857) B381857
theorem B254583 : Blo 251819 254583 := bstep (se 1 (by rfl) ⟨190937, by rfl⟩ : syracuseStep 254583 = 381875) B381875
theorem B254603 : Blo 251819 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B254615 : Blo 251819 254615 := bstep (se 1 (by rfl) ⟨190961, by rfl⟩ : syracuseStep 254615 = 381923) B381923
theorem B287383 : Blo 251819 287383 := bstep (se 1 (by rfl) ⟨215537, by rfl⟩ : syracuseStep 287383 = 431075) B431075
theorem B254635 : Blo 251819 254635 := bstep (se 1 (by rfl) ⟨190976, by rfl⟩ : syracuseStep 254635 = 381953) B381953
theorem B254647 : Blo 251819 254647 := bstep (se 1 (by rfl) ⟨190985, by rfl⟩ : syracuseStep 254647 = 381971) B381971
theorem B320203 : Blo 251819 320203 := bstep (se 1 (by rfl) ⟨240152, by rfl⟩ : syracuseStep 320203 = 480305) B480305
theorem B254667 : Blo 251819 254667 := bstep (se 1 (by rfl) ⟨191000, by rfl⟩ : syracuseStep 254667 = 382001) B382001
theorem B254679 : Blo 251819 254679 := bstep (se 1 (by rfl) ⟨191009, by rfl⟩ : syracuseStep 254679 = 382019) B382019
theorem B254699 : Blo 251819 254699 := bstep (se 1 (by rfl) ⟨191024, by rfl⟩ : syracuseStep 254699 = 382049) B382049
theorem B254711 : Blo 251819 254711 := bstep (se 1 (by rfl) ⟨191033, by rfl⟩ : syracuseStep 254711 = 382067) B382067
theorem B254731 : Blo 251819 254731 := bstep (se 1 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 254731 = 382097) B382097
theorem B254743 : Blo 251819 254743 := bstep (se 1 (by rfl) ⟨191057, by rfl⟩ : syracuseStep 254743 = 382115) B382115
theorem B254763 : Blo 251819 254763 := bstep (se 1 (by rfl) ⟨191072, by rfl⟩ : syracuseStep 254763 = 382145) B382145
theorem B484147 : Blo 251819 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B254775 : Blo 251819 254775 := bstep (se 1 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 254775 = 382163) B382163
theorem B3662657 : Blo 251819 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B254795 : Blo 251819 254795 := bstep (se 1 (by rfl) ⟨191096, by rfl⟩ : syracuseStep 254795 = 382193) B382193
theorem B287563 : Blo 251819 287563 := bstep (se 1 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 287563 = 431345) B431345
theorem B254807 : Blo 251819 254807 := bstep (se 1 (by rfl) ⟨191105, by rfl⟩ : syracuseStep 254807 = 382211) B382211
theorem B254827 : Blo 251819 254827 := bstep (se 1 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 254827 = 382241) B382241
theorem B254839 : Blo 251819 254839 := bstep (se 1 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 254839 = 382259) B382259
theorem B254859 : Blo 251819 254859 := bstep (se 1 (by rfl) ⟨191144, by rfl⟩ : syracuseStep 254859 = 382289) B382289
theorem B254871 : Blo 251819 254871 := bstep (se 1 (by rfl) ⟨191153, by rfl⟩ : syracuseStep 254871 = 382307) B382307
theorem B254891 : Blo 251819 254891 := bstep (se 1 (by rfl) ⟨191168, by rfl⟩ : syracuseStep 254891 = 382337) B382337
theorem B8479667 : Blo 251819 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B254903 : Blo 251819 254903 := bstep (se 1 (by rfl) ⟨191177, by rfl⟩ : syracuseStep 254903 = 382355) B382355
theorem B287671 : Blo 251819 287671 := bstep (se 1 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 287671 = 431507) B431507
theorem B254923 : Blo 251819 254923 := bstep (se 1 (by rfl) ⟨191192, by rfl⟩ : syracuseStep 254923 = 382385) B382385
theorem B254935 : Blo 251819 254935 := bstep (se 1 (by rfl) ⟨191201, by rfl⟩ : syracuseStep 254935 = 382403) B382403
theorem B254955 : Blo 251819 254955 := bstep (se 1 (by rfl) ⟨191216, by rfl⟩ : syracuseStep 254955 = 382433) B382433
theorem B254967 : Blo 251819 254967 := bstep (se 1 (by rfl) ⟨191225, by rfl⟩ : syracuseStep 254967 = 382451) B382451
theorem B254987 : Blo 251819 254987 := bstep (se 1 (by rfl) ⟨191240, by rfl⟩ : syracuseStep 254987 = 382481) B382481
theorem B254999 : Blo 251819 254999 := bstep (se 1 (by rfl) ⟨191249, by rfl⟩ : syracuseStep 254999 = 382499) B382499
theorem B484375 : Blo 251819 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B255019 : Blo 251819 255019 := bstep (se 1 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 255019 = 382529) B382529
theorem B255031 : Blo 251819 255031 := bstep (se 1 (by rfl) ⟨191273, by rfl⟩ : syracuseStep 255031 = 382547) B382547
theorem B255051 : Blo 251819 255051 := bstep (se 1 (by rfl) ⟨191288, by rfl⟩ : syracuseStep 255051 = 382577) B382577
theorem B255063 : Blo 251819 255063 := bstep (se 1 (by rfl) ⟨191297, by rfl⟩ : syracuseStep 255063 = 382595) B382595
theorem B255083 : Blo 251819 255083 := bstep (se 1 (by rfl) ⟨191312, by rfl⟩ : syracuseStep 255083 = 382625) B382625
theorem B255095 : Blo 251819 255095 := bstep (se 1 (by rfl) ⟨191321, by rfl⟩ : syracuseStep 255095 = 382643) B382643
theorem B484481 : Blo 251819 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B255115 : Blo 251819 255115 := bstep (se 1 (by rfl) ⟨191336, by rfl⟩ : syracuseStep 255115 = 382673) B382673
theorem B255127 : Blo 251819 255127 := bstep (se 1 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 255127 = 382691) B382691
theorem B255147 : Blo 251819 255147 := bstep (se 1 (by rfl) ⟨191360, by rfl⟩ : syracuseStep 255147 = 382721) B382721
theorem B1631411 : Blo 251819 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B255159 : Blo 251819 255159 := bstep (se 1 (by rfl) ⟨191369, by rfl⟩ : syracuseStep 255159 = 382739) B382739
theorem B255179 : Blo 251819 255179 := bstep (se 1 (by rfl) ⟨191384, by rfl⟩ : syracuseStep 255179 = 382769) B382769
theorem B255191 : Blo 251819 255191 := bstep (se 1 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 255191 = 382787) B382787
theorem B255211 : Blo 251819 255211 := bstep (se 1 (by rfl) ⟨191408, by rfl⟩ : syracuseStep 255211 = 382817) B382817
theorem B255223 : Blo 251819 255223 := bstep (se 1 (by rfl) ⟨191417, by rfl⟩ : syracuseStep 255223 = 382835) B382835
theorem B11101445 : Blo 251819 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B255243 : Blo 251819 255243 := bstep (se 1 (by rfl) ⟨191432, by rfl⟩ : syracuseStep 255243 = 382865) B382865
theorem B2057489 : Blo 251819 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B976151 : Blo 251819 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B255255 : Blo 251819 255255 := bstep (se 1 (by rfl) ⟨191441, by rfl⟩ : syracuseStep 255255 = 382883) B382883
theorem B484633 : Blo 251819 484633 := bstep (se 2 (by rfl) ⟨181737, by rfl⟩ : syracuseStep 484633 = 363475) B363475
theorem B255275 : Blo 251819 255275 := bstep (se 1 (by rfl) ⟨191456, by rfl⟩ : syracuseStep 255275 = 382913) B382913
theorem B255287 : Blo 251819 255287 := bstep (se 1 (by rfl) ⟨191465, by rfl⟩ : syracuseStep 255287 = 382931) B382931
theorem B255307 : Blo 251819 255307 := bstep (se 1 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 255307 = 382961) B382961
theorem B255319 : Blo 251819 255319 := bstep (se 1 (by rfl) ⟨191489, by rfl⟩ : syracuseStep 255319 = 382979) B382979
theorem B255339 : Blo 251819 255339 := bstep (se 1 (by rfl) ⟨191504, by rfl⟩ : syracuseStep 255339 = 383009) B383009
theorem B255351 : Blo 251819 255351 := bstep (se 1 (by rfl) ⟨191513, by rfl⟩ : syracuseStep 255351 = 383027) B383027
theorem B255371 : Blo 251819 255371 := bstep (se 1 (by rfl) ⟨191528, by rfl⟩ : syracuseStep 255371 = 383057) B383057
theorem B1631639 : Blo 251819 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B255383 : Blo 251819 255383 := bstep (se 1 (by rfl) ⟨191537, by rfl⟩ : syracuseStep 255383 = 383075) B383075
theorem B255403 : Blo 251819 255403 := bstep (se 1 (by rfl) ⟨191552, by rfl⟩ : syracuseStep 255403 = 383105) B383105
theorem B255415 : Blo 251819 255415 := bstep (se 1 (by rfl) ⟨191561, by rfl⟩ : syracuseStep 255415 = 383123) B383123
theorem B255435 : Blo 251819 255435 := bstep (se 1 (by rfl) ⟨191576, by rfl⟩ : syracuseStep 255435 = 383153) B383153
theorem B255447 : Blo 251819 255447 := bstep (se 1 (by rfl) ⟨191585, by rfl⟩ : syracuseStep 255447 = 383171) B383171
theorem B255467 : Blo 251819 255467 := bstep (se 1 (by rfl) ⟨191600, by rfl⟩ : syracuseStep 255467 = 383201) B383201
theorem B255479 : Blo 251819 255479 := bstep (se 1 (by rfl) ⟨191609, by rfl⟩ : syracuseStep 255479 = 383219) B383219
theorem B255499 : Blo 251819 255499 := bstep (se 1 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 255499 = 383249) B383249
theorem B255511 : Blo 251819 255511 := bstep (se 1 (by rfl) ⟨191633, by rfl⟩ : syracuseStep 255511 = 383267) B383267
theorem B255531 : Blo 251819 255531 := bstep (se 1 (by rfl) ⟨191648, by rfl⟩ : syracuseStep 255531 = 383297) B383297
theorem B255543 : Blo 251819 255543 := bstep (se 1 (by rfl) ⟨191657, by rfl⟩ : syracuseStep 255543 = 383315) B383315
theorem B1730123 : Blo 251819 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B255563 : Blo 251819 255563 := bstep (se 1 (by rfl) ⟨191672, by rfl⟩ : syracuseStep 255563 = 383345) B383345
theorem B255575 : Blo 251819 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B255595 : Blo 251819 255595 := bstep (se 1 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 255595 = 383393) B383393
theorem B255607 : Blo 251819 255607 := bstep (se 1 (by rfl) ⟨191705, by rfl⟩ : syracuseStep 255607 = 383411) B383411
theorem B255627 : Blo 251819 255627 := bstep (se 1 (by rfl) ⟨191720, by rfl⟩ : syracuseStep 255627 = 383441) B383441
theorem B321175 : Blo 251819 321175 := bstep (se 1 (by rfl) ⟨240881, by rfl⟩ : syracuseStep 321175 = 481763) B481763
theorem B255639 : Blo 251819 255639 := bstep (se 1 (by rfl) ⟨191729, by rfl⟩ : syracuseStep 255639 = 383459) B383459
theorem B255659 : Blo 251819 255659 := bstep (se 1 (by rfl) ⟨191744, by rfl⟩ : syracuseStep 255659 = 383489) B383489
theorem B255671 : Blo 251819 255671 := bstep (se 1 (by rfl) ⟨191753, by rfl⟩ : syracuseStep 255671 = 383507) B383507
theorem B255691 : Blo 251819 255691 := bstep (se 1 (by rfl) ⟨191768, by rfl⟩ : syracuseStep 255691 = 383537) B383537
theorem B255703 : Blo 251819 255703 := bstep (se 1 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 255703 = 383555) B383555
theorem B255723 : Blo 251819 255723 := bstep (se 1 (by rfl) ⟨191792, by rfl⟩ : syracuseStep 255723 = 383585) B383585
theorem B255735 : Blo 251819 255735 := bstep (se 1 (by rfl) ⟨191801, by rfl⟩ : syracuseStep 255735 = 383603) B383603
theorem B255755 : Blo 251819 255755 := bstep (se 1 (by rfl) ⟨191816, by rfl⟩ : syracuseStep 255755 = 383633) B383633
theorem B255767 : Blo 251819 255767 := bstep (se 1 (by rfl) ⟨191825, by rfl⟩ : syracuseStep 255767 = 383651) B383651
theorem B255787 : Blo 251819 255787 := bstep (se 1 (by rfl) ⟨191840, by rfl⟩ : syracuseStep 255787 = 383681) B383681
theorem B255799 : Blo 251819 255799 := bstep (se 1 (by rfl) ⟨191849, by rfl⟩ : syracuseStep 255799 = 383699) B383699
theorem B255819 : Blo 251819 255819 := bstep (se 1 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 255819 = 383729) B383729
theorem B387289 : Blo 251819 387289 := bstep (se 2 (by rfl) ⟨145233, by rfl⟩ : syracuseStep 387289 = 290467) B290467
theorem B321995 : Blo 251819 321995 := bstep (se 1 (by rfl) ⟨241496, by rfl⟩ : syracuseStep 321995 = 482993) B482993
theorem B2058817 : Blo 251819 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1632869 : Blo 251819 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B1436291 : Blo 251819 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B813719 : Blo 251819 813719 := bstep (se 1 (by rfl) ⟨610289, by rfl⟩ : syracuseStep 813719 = 1220579) B1220579
theorem B1076141 : Blo 251819 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B322699 : Blo 251819 322699 := bstep (se 1 (by rfl) ⟨242024, by rfl⟩ : syracuseStep 322699 = 484049) B484049
theorem B814283 : Blo 251819 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B1076483 : Blo 251819 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B454027 : Blo 251819 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B322967 : Blo 251819 322967 := bstep (se 1 (by rfl) ⟨242225, by rfl⟩ : syracuseStep 322967 = 484451) B484451
theorem B913069 : Blo 251819 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B1994419 : Blo 251819 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B323671 : Blo 251819 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B2355331 : Blo 251819 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B487705 : Blo 251819 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B455051 : Blo 251819 455051 := bstep (se 1 (by rfl) ⟨341288, by rfl⟩ : syracuseStep 455051 = 682577) B682577
theorem B258455 : Blo 251819 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B1929905 : Blo 251819 1929905 := bstep (se 2 (by rfl) ⟨723714, by rfl⟩ : syracuseStep 1929905 = 1447429) B1447429
theorem B914327 : Blo 251819 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B1438681 : Blo 251819 1438681 := bstep (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) B1079011
theorem B1930391 : Blo 251819 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B259319 : Blo 251819 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B455987 : Blo 251819 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B619865 : Blo 251819 619865 := bstep (se 2 (by rfl) ⟨232449, by rfl⟩ : syracuseStep 619865 = 464899) B464899
theorem B1078859 : Blo 251819 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B1439639 : Blo 251819 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B12318641 : Blo 251819 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2062259 : Blo 251819 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B555031 : Blo 251819 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B850013 : Blo 251819 850013 := bstep (se 3 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 850013 = 318755) B318755
theorem B653633 : Blo 251819 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B1276235 : Blo 251819 1276235 := bstep (se 1 (by rfl) ⟨957176, by rfl⟩ : syracuseStep 1276235 = 1914353) B1914353
theorem B1079831 : Blo 251819 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B358987 : Blo 251819 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B4651613 : Blo 251819 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B359255 : Blo 251819 359255 := bstep (se 1 (by rfl) ⟨269441, by rfl⟩ : syracuseStep 359255 = 538883) B538883
theorem B719705 : Blo 251819 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1538909 : Blo 251819 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B457625 : Blo 251819 457625 := bstep (se 2 (by rfl) ⟨171609, by rfl⟩ : syracuseStep 457625 = 343219) B343219
theorem B425047 : Blo 251819 425047 := bstep (se 1 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 425047 = 637571) B637571
theorem B1080499 : Blo 251819 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B851147 : Blo 251819 851147 := bstep (se 1 (by rfl) ⟨638360, by rfl⟩ : syracuseStep 851147 = 1276721) B1276721
theorem B851417 : Blo 251819 851417 := bstep (se 2 (by rfl) ⟨319281, by rfl⟩ : syracuseStep 851417 = 638563) B638563
theorem B3276323 : Blo 251819 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B491123 : Blo 251819 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B425675 : Blo 251819 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B360217 : Blo 251819 360217 := bstep (se 2 (by rfl) ⟨135081, by rfl⟩ : syracuseStep 360217 = 270163) B270163
theorem B425803 : Blo 251819 425803 := bstep (se 1 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 425803 = 638705) B638705
theorem B425945 : Blo 251819 425945 := bstep (se 2 (by rfl) ⟨159729, by rfl⟩ : syracuseStep 425945 = 319459) B319459
theorem B425999 : Blo 251819 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B819229 : Blo 251819 819229 := bstep (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) B307211
theorem B852011 : Blo 251819 852011 := bstep (se 1 (by rfl) ⟨639008, by rfl⟩ : syracuseStep 852011 = 1278017) B1278017
theorem B655447 : Blo 251819 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B721163 : Blo 251819 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B426539 : Blo 251819 426539 := bstep (se 1 (by rfl) ⟨319904, by rfl⟩ : syracuseStep 426539 = 639809) B639809
theorem B1278665 : Blo 251819 1278665 := bstep (se 2 (by rfl) ⟨479499, by rfl⟩ : syracuseStep 1278665 = 958999) B958999
theorem B2917093 : Blo 251819 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B3277583 : Blo 251819 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B361351 : Blo 251819 361351 := bstep (se 1 (by rfl) ⟨271013, by rfl⟩ : syracuseStep 361351 = 542027) B542027
theorem B426937 : Blo 251819 426937 := bstep (se 2 (by rfl) ⟨160101, by rfl⟩ : syracuseStep 426937 = 320203) B320203
theorem B1836055 : Blo 251819 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B1082429 : Blo 251819 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B689213 : Blo 251819 689213 := bstep (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) B258455
theorem B2917691 : Blo 251819 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B853307 : Blo 251819 853307 := bstep (se 1 (by rfl) ⟨639980, by rfl⟩ : syracuseStep 853307 = 1279961) B1279961
theorem B1082771 : Blo 251819 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B1541585 : Blo 251819 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B427639 : Blo 251819 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B362171 : Blo 251819 362171 := bstep (se 1 (by rfl) ⟨271628, by rfl⟩ : syracuseStep 362171 = 543257) B543257
theorem B853793 : Blo 251819 853793 := bstep (se 2 (by rfl) ⟨320172, by rfl⟩ : syracuseStep 853793 = 640345) B640345
theorem B460603 : Blo 251819 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B427835 : Blo 251819 427835 := bstep (se 1 (by rfl) ⟨320876, by rfl⟩ : syracuseStep 427835 = 641753) B641753
theorem B690187 : Blo 251819 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B460859 : Blo 251819 460859 := bstep (se 1 (by rfl) ⟨345644, by rfl⟩ : syracuseStep 460859 = 691289) B691289
theorem B1444013 : Blo 251819 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B428233 : Blo 251819 428233 := bstep (se 2 (by rfl) ⟨160587, by rfl⟩ : syracuseStep 428233 = 321175) B321175
theorem B362809 : Blo 251819 362809 := bstep (se 2 (by rfl) ⟨136053, by rfl⟩ : syracuseStep 362809 = 272107) B272107
theorem B330043 : Blo 251819 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B723259 : Blo 251819 723259 := bstep (se 1 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 723259 = 1084889) B1084889
theorem B854387 : Blo 251819 854387 := bstep (se 1 (by rfl) ⟨640790, by rfl⟩ : syracuseStep 854387 = 1281581) B1281581
theorem B920335 : Blo 251819 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B3083123 : Blo 251819 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B428935 : Blo 251819 428935 := bstep (se 1 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 428935 = 643403) B643403
theorem B724103 : Blo 251819 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B691517 : Blo 251819 691517 := bstep (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) B259319
theorem B1215965 : Blo 251819 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B429583 : Blo 251819 429583 := bstep (se 1 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 429583 = 644375) B644375
theorem B921131 : Blo 251819 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B2723635 : Blo 251819 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B2461529 : Blo 251819 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B724889 : Blo 251819 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B430123 : Blo 251819 430123 := bstep (se 1 (by rfl) ⟨322592, by rfl⟩ : syracuseStep 430123 = 645185) B645185
theorem B364603 : Blo 251819 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B430265 : Blo 251819 430265 := bstep (se 2 (by rfl) ⟨161349, by rfl⟩ : syracuseStep 430265 = 322699) B322699
theorem B23433461 : Blo 251819 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1085831 : Blo 251819 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B725537 : Blo 251819 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B430967 : Blo 251819 430967 := bstep (se 1 (by rfl) ⟨323225, by rfl⟩ : syracuseStep 430967 = 646451) B646451
theorem B1217425 : Blo 251819 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B856979 : Blo 251819 856979 := bstep (se 1 (by rfl) ⟨642734, by rfl⟩ : syracuseStep 856979 = 1285469) B1285469
theorem B2659225 : Blo 251819 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B431419 : Blo 251819 431419 := bstep (se 1 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 431419 = 647129) B647129
theorem B7968131 : Blo 251819 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B2069945 : Blo 251819 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B431561 : Blo 251819 431561 := bstep (se 2 (by rfl) ⟨161835, by rfl⟩ : syracuseStep 431561 = 323671) B323671
theorem B726529 : Blo 251819 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B1545965 : Blo 251819 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B4954229 : Blo 251819 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B1087607 : Blo 251819 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B858383 : Blo 251819 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B1087759 : Blo 251819 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B2332961 : Blo 251819 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B1153415 : Blo 251819 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B1284497 : Blo 251819 1284497 := bstep (se 2 (by rfl) ⟨481686, by rfl⟩ : syracuseStep 1284497 = 963373) B963373
theorem B858653 : Blo 251819 858653 := bstep (se 3 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 858653 = 321995) B321995
theorem B1448705 : Blo 251819 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B629537 : Blo 251819 629537 := bstep (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) B472153
theorem B1088579 : Blo 251819 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B957527 : Blo 251819 957527 := bstep (se 1 (by rfl) ⟨718145, by rfl⟩ : syracuseStep 957527 = 1436291) B1436291
theorem B1449161 : Blo 251819 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B2891213 : Blo 251819 2891213 := bstep (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) B1084205
theorem B958013 : Blo 251819 958013 := bstep (se 3 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 958013 = 359255) B359255
theorem B2170597 : Blo 251819 2170597 := bstep (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) B406987
theorem B860057 : Blo 251819 860057 := bstep (se 2 (by rfl) ⟨322521, by rfl⟩ : syracuseStep 860057 = 645043) B645043
theorem B729089 : Blo 251819 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B303367 : Blo 251819 303367 := bstep (se 1 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 303367 = 455051) B455051
theorem B1286603 : Blo 251819 1286603 := bstep (se 1 (by rfl) ⟨964952, by rfl⟩ : syracuseStep 1286603 = 1929905) B1929905
theorem B860759 : Blo 251819 860759 := bstep (se 1 (by rfl) ⟨645569, by rfl⟩ : syracuseStep 860759 = 1291139) B1291139
theorem B270983 : Blo 251819 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B1286927 : Blo 251819 1286927 := bstep (se 1 (by rfl) ⟨965195, by rfl⟩ : syracuseStep 1286927 = 1930391) B1930391
theorem B861245 : Blo 251819 861245 := bstep (se 3 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 861245 = 322967) B322967
theorem B1615085 : Blo 251819 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B959759 : Blo 251819 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B566675 : Blo 251819 566675 := bstep (se 1 (by rfl) ⟨425006, by rfl⟩ : syracuseStep 566675 = 850013) B850013
theorem B566729 : Blo 251819 566729 := bstep (se 2 (by rfl) ⟨212523, by rfl⟩ : syracuseStep 566729 = 425047) B425047
theorem B435755 : Blo 251819 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B1025939 : Blo 251819 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B305083 : Blo 251819 305083 := bstep (se 1 (by rfl) ⟨228812, by rfl⟩ : syracuseStep 305083 = 457625) B457625
theorem B567431 : Blo 251819 567431 := bstep (se 1 (by rfl) ⟨425573, by rfl⟩ : syracuseStep 567431 = 851147) B851147
theorem B1288385 : Blo 251819 1288385 := bstep (se 2 (by rfl) ⟨483144, by rfl⟩ : syracuseStep 1288385 = 966289) B966289
theorem B567611 : Blo 251819 567611 := bstep (se 1 (by rfl) ⟨425708, by rfl⟩ : syracuseStep 567611 = 851417) B851417
theorem B2173331 : Blo 251819 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B567737 : Blo 251819 567737 := bstep (se 2 (by rfl) ⟨212901, by rfl⟩ : syracuseStep 567737 = 425803) B425803
theorem B862649 : Blo 251819 862649 := bstep (se 2 (by rfl) ⟨323493, by rfl⟩ : syracuseStep 862649 = 646987) B646987
theorem B2468381 : Blo 251819 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B568079 : Blo 251819 568079 := bstep (se 1 (by rfl) ⟨426059, by rfl⟩ : syracuseStep 568079 = 852119) B852119
theorem B568097 : Blo 251819 568097 := bstep (se 2 (by rfl) ⟨213036, by rfl⟩ : syracuseStep 568097 = 426073) B426073
theorem B2960165 : Blo 251819 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B2763571 : Blo 251819 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B961415 : Blo 251819 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B2632601 : Blo 251819 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B2304931 : Blo 251819 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B863243 : Blo 251819 863243 := bstep (se 1 (by rfl) ⟨647432, by rfl⟩ : syracuseStep 863243 = 1294865) B1294865
theorem B1453079 : Blo 251819 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B568439 : Blo 251819 568439 := bstep (se 1 (by rfl) ⟨426329, by rfl⟩ : syracuseStep 568439 = 852659) B852659
theorem B863351 : Blo 251819 863351 := bstep (se 1 (by rfl) ⟨647513, by rfl⟩ : syracuseStep 863351 = 1295027) B1295027
theorem B1617185 : Blo 251819 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B568619 : Blo 251819 568619 := bstep (se 1 (by rfl) ⟨426464, by rfl⟩ : syracuseStep 568619 = 852929) B852929
theorem B1289681 : Blo 251819 1289681 := bstep (se 2 (by rfl) ⟨483630, by rfl⟩ : syracuseStep 1289681 = 967261) B967261
theorem B24850061 : Blo 251819 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B568979 : Blo 251819 568979 := bstep (se 1 (by rfl) ⟨426734, by rfl⟩ : syracuseStep 568979 = 853469) B853469
theorem B306875 : Blo 251819 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B569033 : Blo 251819 569033 := bstep (se 2 (by rfl) ⟨213387, by rfl⟩ : syracuseStep 569033 = 426775) B426775
theorem B733303 : Blo 251819 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B405803 : Blo 251819 405803 := bstep (se 1 (by rfl) ⟨304352, by rfl⟩ : syracuseStep 405803 = 608705) B608705
theorem B733499 : Blo 251819 733499 := bstep (se 1 (by rfl) ⟨550124, by rfl⟩ : syracuseStep 733499 = 1100249) B1100249
theorem B1552729 : Blo 251819 1552729 := bstep (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) B1164547
theorem B569735 : Blo 251819 569735 := bstep (se 1 (by rfl) ⟨427301, by rfl⟩ : syracuseStep 569735 = 854603) B854603
theorem B569915 : Blo 251819 569915 := bstep (se 1 (by rfl) ⟨427436, by rfl⟩ : syracuseStep 569915 = 854873) B854873
theorem B963191 : Blo 251819 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B570041 : Blo 251819 570041 := bstep (se 2 (by rfl) ⟨213765, by rfl⟩ : syracuseStep 570041 = 427531) B427531
theorem B5223203 : Blo 251819 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B1454993 : Blo 251819 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B1913867 : Blo 251819 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B570383 : Blo 251819 570383 := bstep (se 1 (by rfl) ⟨427787, by rfl⟩ : syracuseStep 570383 = 855575) B855575
theorem B570401 : Blo 251819 570401 := bstep (se 2 (by rfl) ⟨213900, by rfl⟩ : syracuseStep 570401 = 427801) B427801
theorem B570743 : Blo 251819 570743 := bstep (se 1 (by rfl) ⟨428057, by rfl⟩ : syracuseStep 570743 = 856115) B856115
theorem B1291787 : Blo 251819 1291787 := bstep (se 1 (by rfl) ⟨968840, by rfl⟩ : syracuseStep 1291787 = 1937681) B1937681
theorem B570923 : Blo 251819 570923 := bstep (se 1 (by rfl) ⟨428192, by rfl⟩ : syracuseStep 570923 = 856385) B856385
theorem B1455677 : Blo 251819 1455677 := bstep (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) B545879
theorem B964163 : Blo 251819 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B1291949 : Blo 251819 1291949 := bstep (se 3 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 1291949 = 484481) B484481
theorem B1226497 : Blo 251819 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B571283 : Blo 251819 571283 := bstep (se 1 (by rfl) ⟨428462, by rfl⟩ : syracuseStep 571283 = 856925) B856925
theorem B571337 : Blo 251819 571337 := bstep (se 2 (by rfl) ⟨214251, by rfl⟩ : syracuseStep 571337 = 428503) B428503
theorem B964619 : Blo 251819 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B768457 : Blo 251819 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B4143581 : Blo 251819 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B572039 : Blo 251819 572039 := bstep (se 1 (by rfl) ⟨429029, by rfl⟩ : syracuseStep 572039 = 858059) B858059
theorem B1620773 : Blo 251819 1620773 := bstep (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) B303895
theorem B572219 : Blo 251819 572219 := bstep (se 1 (by rfl) ⟨429164, by rfl⟩ : syracuseStep 572219 = 858329) B858329
theorem B1915811 : Blo 251819 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B572345 : Blo 251819 572345 := bstep (se 2 (by rfl) ⟨214629, by rfl⟩ : syracuseStep 572345 = 429259) B429259
theorem B605369 : Blo 251819 605369 := bstep (se 2 (by rfl) ⟨227013, by rfl⟩ : syracuseStep 605369 = 454027) B454027
theorem B1293569 : Blo 251819 1293569 := bstep (se 2 (by rfl) ⟨485088, by rfl⟩ : syracuseStep 1293569 = 970177) B970177
theorem B638219 : Blo 251819 638219 := bstep (se 1 (by rfl) ⟨478664, by rfl⟩ : syracuseStep 638219 = 957329) B957329
theorem B572687 : Blo 251819 572687 := bstep (se 1 (by rfl) ⟨429515, by rfl⟩ : syracuseStep 572687 = 859031) B859031
theorem B572705 : Blo 251819 572705 := bstep (se 2 (by rfl) ⟨214764, by rfl⟩ : syracuseStep 572705 = 429529) B429529
theorem B1555847 : Blo 251819 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1818065 : Blo 251819 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B573047 : Blo 251819 573047 := bstep (se 1 (by rfl) ⟨429785, by rfl⟩ : syracuseStep 573047 = 859571) B859571
theorem B573227 : Blo 251819 573227 := bstep (se 1 (by rfl) ⟨429920, by rfl⟩ : syracuseStep 573227 = 859841) B859841
theorem B638867 : Blo 251819 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B1228729 : Blo 251819 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B2211851 : Blo 251819 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1294379 : Blo 251819 1294379 := bstep (se 1 (by rfl) ⟨970784, by rfl⟩ : syracuseStep 1294379 = 1941569) B1941569
theorem B966775 : Blo 251819 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B573587 : Blo 251819 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B639161 : Blo 251819 639161 := bstep (se 2 (by rfl) ⟨239685, by rfl⟩ : syracuseStep 639161 = 479371) B479371
theorem B573641 : Blo 251819 573641 := bstep (se 2 (by rfl) ⟨215115, by rfl⟩ : syracuseStep 573641 = 430231) B430231
theorem B4866317 : Blo 251819 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B606599 : Blo 251819 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B2441771 : Blo 251819 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B4112963 : Blo 251819 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B770647 : Blo 251819 770647 := bstep (se 1 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 770647 = 1155971) B1155971
theorem B5653111 : Blo 251819 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B639859 : Blo 251819 639859 := bstep (se 1 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 639859 = 959789) B959789
theorem B377735 : Blo 251819 377735 := bstep (se 1 (by rfl) ⟨283301, by rfl⟩ : syracuseStep 377735 = 566603) B566603
theorem B574343 : Blo 251819 574343 := bstep (se 1 (by rfl) ⟨430757, by rfl⟩ : syracuseStep 574343 = 861515) B861515
theorem B377771 : Blo 251819 377771 := bstep (se 1 (by rfl) ⟨283328, by rfl⟩ : syracuseStep 377771 = 566657) B566657
theorem B377801 : Blo 251819 377801 := bstep (se 2 (by rfl) ⟨141675, by rfl⟩ : syracuseStep 377801 = 283351) B283351
theorem B640001 : Blo 251819 640001 := bstep (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) B480001
theorem B3064877 : Blo 251819 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B377915 : Blo 251819 377915 := bstep (se 1 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 377915 = 566873) B566873
theorem B574523 : Blo 251819 574523 := bstep (se 1 (by rfl) ⟨430892, by rfl⟩ : syracuseStep 574523 = 861785) B861785
theorem B967747 : Blo 251819 967747 := bstep (se 1 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 967747 = 1451621) B1451621
theorem B377975 : Blo 251819 377975 := bstep (se 1 (by rfl) ⟨283481, by rfl⟩ : syracuseStep 377975 = 566963) B566963
theorem B377999 : Blo 251819 377999 := bstep (se 1 (by rfl) ⟨283499, by rfl⟩ : syracuseStep 377999 = 566999) B566999
theorem B378041 : Blo 251819 378041 := bstep (se 2 (by rfl) ⟨141765, by rfl⟩ : syracuseStep 378041 = 283531) B283531
theorem B574649 : Blo 251819 574649 := bstep (se 2 (by rfl) ⟨215493, by rfl⟩ : syracuseStep 574649 = 430987) B430987
theorem B378119 : Blo 251819 378119 := bstep (se 1 (by rfl) ⟨283589, by rfl⟩ : syracuseStep 378119 = 567179) B567179
theorem B1918241 : Blo 251819 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B378155 : Blo 251819 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B378185 : Blo 251819 378185 := bstep (se 2 (by rfl) ⟨141819, by rfl⟩ : syracuseStep 378185 = 283639) B283639
theorem B968051 : Blo 251819 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B378299 : Blo 251819 378299 := bstep (se 1 (by rfl) ⟨283724, by rfl⟩ : syracuseStep 378299 = 567449) B567449
theorem B640457 : Blo 251819 640457 := bstep (se 2 (by rfl) ⟨240171, by rfl⟩ : syracuseStep 640457 = 480343) B480343
theorem B378359 : Blo 251819 378359 := bstep (se 1 (by rfl) ⟨283769, by rfl⟩ : syracuseStep 378359 = 567539) B567539
theorem B378383 : Blo 251819 378383 := bstep (se 1 (by rfl) ⟨283787, by rfl⟩ : syracuseStep 378383 = 567575) B567575
theorem B574991 : Blo 251819 574991 := bstep (se 1 (by rfl) ⟨431243, by rfl⟩ : syracuseStep 574991 = 862487) B862487
theorem B575009 : Blo 251819 575009 := bstep (se 2 (by rfl) ⟨215628, by rfl⟩ : syracuseStep 575009 = 431257) B431257
theorem B378425 : Blo 251819 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B378503 : Blo 251819 378503 := bstep (se 1 (by rfl) ⟨283877, by rfl⟩ : syracuseStep 378503 = 567755) B567755
theorem B378539 : Blo 251819 378539 := bstep (se 1 (by rfl) ⟨283904, by rfl⟩ : syracuseStep 378539 = 567809) B567809
theorem B378569 : Blo 251819 378569 := bstep (se 2 (by rfl) ⟨141963, by rfl⟩ : syracuseStep 378569 = 283927) B283927
theorem B542479 : Blo 251819 542479 := bstep (se 1 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 542479 = 813719) B813719
theorem B640811 : Blo 251819 640811 := bstep (se 1 (by rfl) ⟨480608, by rfl⟩ : syracuseStep 640811 = 961217) B961217
theorem B378683 : Blo 251819 378683 := bstep (se 1 (by rfl) ⟨284012, by rfl⟩ : syracuseStep 378683 = 568025) B568025
theorem B968507 : Blo 251819 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B378743 : Blo 251819 378743 := bstep (se 1 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 378743 = 568115) B568115
theorem B575351 : Blo 251819 575351 := bstep (se 1 (by rfl) ⟨431513, by rfl⟩ : syracuseStep 575351 = 863027) B863027
theorem B378767 : Blo 251819 378767 := bstep (se 1 (by rfl) ⟨284075, by rfl⟩ : syracuseStep 378767 = 568151) B568151
theorem B378809 : Blo 251819 378809 := bstep (se 2 (by rfl) ⟨142053, by rfl⟩ : syracuseStep 378809 = 284107) B284107
theorem B378887 : Blo 251819 378887 := bstep (se 1 (by rfl) ⟨284165, by rfl⟩ : syracuseStep 378887 = 568331) B568331
theorem B378923 : Blo 251819 378923 := bstep (se 1 (by rfl) ⟨284192, by rfl⟩ : syracuseStep 378923 = 568385) B568385
theorem B575531 : Blo 251819 575531 := bstep (se 1 (by rfl) ⟨431648, by rfl⟩ : syracuseStep 575531 = 863297) B863297
theorem B378953 : Blo 251819 378953 := bstep (se 2 (by rfl) ⟨142107, by rfl⟩ : syracuseStep 378953 = 284215) B284215
theorem B542855 : Blo 251819 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B575623 : Blo 251819 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B379067 : Blo 251819 379067 := bstep (se 1 (by rfl) ⟨284300, by rfl⟩ : syracuseStep 379067 = 568601) B568601
theorem B1919213 : Blo 251819 1919213 := bstep (se 3 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 1919213 = 719705) B719705
theorem B379127 : Blo 251819 379127 := bstep (se 1 (by rfl) ⟨284345, by rfl⟩ : syracuseStep 379127 = 568691) B568691
theorem B379151 : Blo 251819 379151 := bstep (se 1 (by rfl) ⟨284363, by rfl⟩ : syracuseStep 379151 = 568727) B568727
theorem B968993 : Blo 251819 968993 := bstep (se 2 (by rfl) ⟨363372, by rfl⟩ : syracuseStep 968993 = 726745) B726745
theorem B379193 : Blo 251819 379193 := bstep (se 2 (by rfl) ⟨142197, by rfl⟩ : syracuseStep 379193 = 284395) B284395
theorem B379271 : Blo 251819 379271 := bstep (se 1 (by rfl) ⟨284453, by rfl⟩ : syracuseStep 379271 = 568907) B568907
theorem B379307 : Blo 251819 379307 := bstep (se 1 (by rfl) ⟨284480, by rfl⟩ : syracuseStep 379307 = 568961) B568961
theorem B379337 : Blo 251819 379337 := bstep (se 2 (by rfl) ⟨142251, by rfl⟩ : syracuseStep 379337 = 284503) B284503
theorem B379451 : Blo 251819 379451 := bstep (se 1 (by rfl) ⟨284588, by rfl⟩ : syracuseStep 379451 = 569177) B569177
theorem B379511 : Blo 251819 379511 := bstep (se 1 (by rfl) ⟨284633, by rfl⟩ : syracuseStep 379511 = 569267) B569267
theorem B379535 : Blo 251819 379535 := bstep (se 1 (by rfl) ⟨284651, by rfl⟩ : syracuseStep 379535 = 569303) B569303
theorem B379577 : Blo 251819 379577 := bstep (se 2 (by rfl) ⟨142341, by rfl⟩ : syracuseStep 379577 = 284683) B284683
theorem B379655 : Blo 251819 379655 := bstep (se 1 (by rfl) ⟨284741, by rfl⟩ : syracuseStep 379655 = 569483) B569483
theorem B641803 : Blo 251819 641803 := bstep (se 1 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 641803 = 962705) B962705
theorem B1166113 : Blo 251819 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B379691 : Blo 251819 379691 := bstep (se 1 (by rfl) ⟨284768, by rfl⟩ : syracuseStep 379691 = 569537) B569537
theorem B379721 : Blo 251819 379721 := bstep (se 2 (by rfl) ⟨142395, by rfl⟩ : syracuseStep 379721 = 284791) B284791
theorem B641945 : Blo 251819 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B379835 : Blo 251819 379835 := bstep (se 1 (by rfl) ⟨284876, by rfl⟩ : syracuseStep 379835 = 569753) B569753
theorem B2608075 : Blo 251819 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B379895 : Blo 251819 379895 := bstep (se 1 (by rfl) ⟨284921, by rfl⟩ : syracuseStep 379895 = 569843) B569843
theorem B379919 : Blo 251819 379919 := bstep (se 1 (by rfl) ⟨284939, by rfl⟩ : syracuseStep 379919 = 569879) B569879
theorem B379961 : Blo 251819 379961 := bstep (se 2 (by rfl) ⟨142485, by rfl⟩ : syracuseStep 379961 = 284971) B284971
theorem B642107 : Blo 251819 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B2182277 : Blo 251819 2182277 := bstep (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) B409177
theorem B380039 : Blo 251819 380039 := bstep (se 1 (by rfl) ⟨285029, by rfl⟩ : syracuseStep 380039 = 570059) B570059
theorem B380075 : Blo 251819 380075 := bstep (se 1 (by rfl) ⟨285056, by rfl⟩ : syracuseStep 380075 = 570113) B570113
theorem B380105 : Blo 251819 380105 := bstep (se 2 (by rfl) ⟨142539, by rfl⟩ : syracuseStep 380105 = 285079) B285079
theorem B969965 : Blo 251819 969965 := bstep (se 3 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 969965 = 363737) B363737
theorem B609551 : Blo 251819 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B380219 : Blo 251819 380219 := bstep (se 1 (by rfl) ⟨285164, by rfl⟩ : syracuseStep 380219 = 570329) B570329
theorem B380279 : Blo 251819 380279 := bstep (se 1 (by rfl) ⟨285209, by rfl⟩ : syracuseStep 380279 = 570419) B570419
theorem B380303 : Blo 251819 380303 := bstep (se 1 (by rfl) ⟨285227, by rfl⟩ : syracuseStep 380303 = 570455) B570455
theorem B642451 : Blo 251819 642451 := bstep (se 1 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 642451 = 963677) B963677
theorem B478649 : Blo 251819 478649 := bstep (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) B358987
theorem B380345 : Blo 251819 380345 := bstep (se 2 (by rfl) ⟨142629, by rfl⟩ : syracuseStep 380345 = 285259) B285259
theorem B380423 : Blo 251819 380423 := bstep (se 1 (by rfl) ⟨285317, by rfl⟩ : syracuseStep 380423 = 570635) B570635
theorem B642593 : Blo 251819 642593 := bstep (se 2 (by rfl) ⟨240972, by rfl⟩ : syracuseStep 642593 = 481945) B481945
theorem B380459 : Blo 251819 380459 := bstep (se 1 (by rfl) ⟨285344, by rfl⟩ : syracuseStep 380459 = 570689) B570689
theorem B413243 : Blo 251819 413243 := bstep (se 1 (by rfl) ⟨309932, by rfl⟩ : syracuseStep 413243 = 619865) B619865
theorem B380489 : Blo 251819 380489 := bstep (se 2 (by rfl) ⟨142683, by rfl⟩ : syracuseStep 380489 = 285367) B285367
theorem B380603 : Blo 251819 380603 := bstep (se 1 (by rfl) ⟨285452, by rfl⟩ : syracuseStep 380603 = 570905) B570905
theorem B380663 : Blo 251819 380663 := bstep (se 1 (by rfl) ⟨285497, by rfl⟩ : syracuseStep 380663 = 570995) B570995
theorem B380687 : Blo 251819 380687 := bstep (se 1 (by rfl) ⟨285515, by rfl⟩ : syracuseStep 380687 = 571031) B571031
theorem B380729 : Blo 251819 380729 := bstep (se 2 (by rfl) ⟨142773, by rfl⟩ : syracuseStep 380729 = 285547) B285547
theorem B380807 : Blo 251819 380807 := bstep (se 1 (by rfl) ⟨285605, by rfl⟩ : syracuseStep 380807 = 571211) B571211
theorem B970649 : Blo 251819 970649 := bstep (se 2 (by rfl) ⟨363993, by rfl⟩ : syracuseStep 970649 = 727987) B727987
theorem B380843 : Blo 251819 380843 := bstep (se 1 (by rfl) ⟨285632, by rfl⟩ : syracuseStep 380843 = 571265) B571265
theorem B380873 : Blo 251819 380873 := bstep (se 2 (by rfl) ⟨142827, by rfl⟩ : syracuseStep 380873 = 285655) B285655
theorem B8212427 : Blo 251819 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B380987 : Blo 251819 380987 := bstep (se 1 (by rfl) ⟨285740, by rfl⟩ : syracuseStep 380987 = 571481) B571481
theorem B381047 : Blo 251819 381047 := bstep (se 1 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 381047 = 571571) B571571
theorem B1921157 : Blo 251819 1921157 := bstep (se 4 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 1921157 = 360217) B360217
theorem B381071 : Blo 251819 381071 := bstep (se 1 (by rfl) ⟨285803, by rfl⟩ : syracuseStep 381071 = 571607) B571607
theorem B381113 : Blo 251819 381113 := bstep (se 2 (by rfl) ⟨142917, by rfl⟩ : syracuseStep 381113 = 285835) B285835
theorem B381191 : Blo 251819 381191 := bstep (se 1 (by rfl) ⟨285893, by rfl⟩ : syracuseStep 381191 = 571787) B571787
theorem B381227 : Blo 251819 381227 := bstep (se 1 (by rfl) ⟨285920, by rfl⟩ : syracuseStep 381227 = 571841) B571841
theorem B381257 : Blo 251819 381257 := bstep (se 2 (by rfl) ⟨142971, by rfl⟩ : syracuseStep 381257 = 285943) B285943
theorem B774515 : Blo 251819 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B3101075 : Blo 251819 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B381371 : Blo 251819 381371 := bstep (se 1 (by rfl) ⟨286028, by rfl⟩ : syracuseStep 381371 = 572057) B572057
theorem B381431 : Blo 251819 381431 := bstep (se 1 (by rfl) ⟨286073, by rfl⟩ : syracuseStep 381431 = 572147) B572147
theorem B643585 : Blo 251819 643585 := bstep (se 2 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 643585 = 482689) B482689
theorem B381455 : Blo 251819 381455 := bstep (se 1 (by rfl) ⟨286091, by rfl⟩ : syracuseStep 381455 = 572183) B572183
theorem B381497 : Blo 251819 381497 := bstep (se 2 (by rfl) ⟨143061, by rfl⟩ : syracuseStep 381497 = 286123) B286123
theorem B381575 : Blo 251819 381575 := bstep (se 1 (by rfl) ⟨286181, by rfl⟩ : syracuseStep 381575 = 572363) B572363
theorem B774809 : Blo 251819 774809 := bstep (se 2 (by rfl) ⟨290553, by rfl⟩ : syracuseStep 774809 = 581107) B581107
theorem B381611 : Blo 251819 381611 := bstep (se 1 (by rfl) ⟨286208, by rfl⟩ : syracuseStep 381611 = 572417) B572417
theorem B381641 : Blo 251819 381641 := bstep (se 2 (by rfl) ⟨143115, by rfl⟩ : syracuseStep 381641 = 286231) B286231
theorem B381755 : Blo 251819 381755 := bstep (se 1 (by rfl) ⟨286316, by rfl⟩ : syracuseStep 381755 = 572633) B572633
theorem B381815 : Blo 251819 381815 := bstep (se 1 (by rfl) ⟨286361, by rfl⟩ : syracuseStep 381815 = 572723) B572723
theorem B381839 : Blo 251819 381839 := bstep (se 1 (by rfl) ⟨286379, by rfl⟩ : syracuseStep 381839 = 572759) B572759
theorem B381881 : Blo 251819 381881 := bstep (se 2 (by rfl) ⟨143205, by rfl⟩ : syracuseStep 381881 = 286411) B286411
theorem B381959 : Blo 251819 381959 := bstep (se 1 (by rfl) ⟨286469, by rfl⟩ : syracuseStep 381959 = 572939) B572939
theorem B2184215 : Blo 251819 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B381995 : Blo 251819 381995 := bstep (se 1 (by rfl) ⟨286496, by rfl⟩ : syracuseStep 381995 = 572993) B572993
theorem B513083 : Blo 251819 513083 := bstep (se 1 (by rfl) ⟨384812, by rfl⟩ : syracuseStep 513083 = 769625) B769625
theorem B382025 : Blo 251819 382025 := bstep (se 2 (by rfl) ⟨143259, by rfl⟩ : syracuseStep 382025 = 286519) B286519
theorem B644183 : Blo 251819 644183 := bstep (se 1 (by rfl) ⟨483137, by rfl⟩ : syracuseStep 644183 = 966275) B966275
theorem B283783 : Blo 251819 283783 := bstep (se 1 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 283783 = 425675) B425675
theorem B382139 : Blo 251819 382139 := bstep (se 1 (by rfl) ⟨286604, by rfl⟩ : syracuseStep 382139 = 573209) B573209
theorem B382199 : Blo 251819 382199 := bstep (se 1 (by rfl) ⟨286649, by rfl⟩ : syracuseStep 382199 = 573299) B573299
theorem B382223 : Blo 251819 382223 := bstep (se 1 (by rfl) ⟨286667, by rfl⟩ : syracuseStep 382223 = 573335) B573335
theorem B644395 : Blo 251819 644395 := bstep (se 1 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 644395 = 966593) B966593
theorem B382265 : Blo 251819 382265 := bstep (se 2 (by rfl) ⟨143349, by rfl⟩ : syracuseStep 382265 = 286699) B286699
theorem B283963 : Blo 251819 283963 := bstep (se 1 (by rfl) ⟨212972, by rfl⟩ : syracuseStep 283963 = 425945) B425945
theorem B480647 : Blo 251819 480647 := bstep (se 1 (by rfl) ⟨360485, by rfl⟩ : syracuseStep 480647 = 720971) B720971
theorem B382343 : Blo 251819 382343 := bstep (se 1 (by rfl) ⟨286757, by rfl⟩ : syracuseStep 382343 = 573515) B573515
theorem B382379 : Blo 251819 382379 := bstep (se 1 (by rfl) ⟨286784, by rfl⟩ : syracuseStep 382379 = 573569) B573569
theorem B644537 : Blo 251819 644537 := bstep (se 2 (by rfl) ⟨241701, by rfl⟩ : syracuseStep 644537 = 483403) B483403
theorem B382409 : Blo 251819 382409 := bstep (se 2 (by rfl) ⟨143403, by rfl⟩ : syracuseStep 382409 = 286807) B286807
theorem B382523 : Blo 251819 382523 := bstep (se 1 (by rfl) ⟨286892, by rfl⟩ : syracuseStep 382523 = 573785) B573785
theorem B382583 : Blo 251819 382583 := bstep (se 1 (by rfl) ⟨286937, by rfl⟩ : syracuseStep 382583 = 573875) B573875
theorem B382607 : Blo 251819 382607 := bstep (se 1 (by rfl) ⟨286955, by rfl⟩ : syracuseStep 382607 = 573911) B573911
theorem B382649 : Blo 251819 382649 := bstep (se 2 (by rfl) ⟨143493, by rfl⟩ : syracuseStep 382649 = 286987) B286987
theorem B2905793 : Blo 251819 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B382727 : Blo 251819 382727 := bstep (se 1 (by rfl) ⟨287045, by rfl⟩ : syracuseStep 382727 = 574091) B574091
theorem B284431 : Blo 251819 284431 := bstep (se 1 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 284431 = 426647) B426647
theorem B382763 : Blo 251819 382763 := bstep (se 1 (by rfl) ⟨287072, by rfl⟩ : syracuseStep 382763 = 574145) B574145
theorem B382793 : Blo 251819 382793 := bstep (se 2 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 382793 = 287095) B287095
theorem B251835 : Blo 251819 251835 := bstep (se 1 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 251835 = 377753) B377753
theorem B382907 : Blo 251819 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B10901465 : Blo 251819 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B382967 : Blo 251819 382967 := bstep (se 1 (by rfl) ⟨287225, by rfl⟩ : syracuseStep 382967 = 574451) B574451
theorem B251911 : Blo 251819 251911 := bstep (se 1 (by rfl) ⟨188933, by rfl⟩ : syracuseStep 251911 = 377867) B377867
theorem B251919 : Blo 251819 251919 := bstep (se 1 (by rfl) ⟨188939, by rfl⟩ : syracuseStep 251919 = 377879) B377879
theorem B382991 : Blo 251819 382991 := bstep (se 1 (by rfl) ⟨287243, by rfl⟩ : syracuseStep 382991 = 574487) B574487
theorem B809003 : Blo 251819 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B383033 : Blo 251819 383033 := bstep (se 2 (by rfl) ⟨143637, by rfl⟩ : syracuseStep 383033 = 287275) B287275
theorem B251963 : Blo 251819 251963 := bstep (se 1 (by rfl) ⟨188972, by rfl⟩ : syracuseStep 251963 = 377945) B377945
theorem B252039 : Blo 251819 252039 := bstep (se 1 (by rfl) ⟨189029, by rfl⟩ : syracuseStep 252039 = 378059) B378059
theorem B383111 : Blo 251819 383111 := bstep (se 1 (by rfl) ⟨287333, by rfl⟩ : syracuseStep 383111 = 574667) B574667
theorem B252047 : Blo 251819 252047 := bstep (se 1 (by rfl) ⟨189035, by rfl⟩ : syracuseStep 252047 = 378071) B378071
theorem B383147 : Blo 251819 383147 := bstep (se 1 (by rfl) ⟨287360, by rfl⟩ : syracuseStep 383147 = 574721) B574721
theorem B252091 : Blo 251819 252091 := bstep (se 1 (by rfl) ⟨189068, by rfl⟩ : syracuseStep 252091 = 378137) B378137
theorem B383177 : Blo 251819 383177 := bstep (se 2 (by rfl) ⟨143691, by rfl⟩ : syracuseStep 383177 = 287383) B287383
theorem B252167 : Blo 251819 252167 := bstep (se 1 (by rfl) ⟨189125, by rfl⟩ : syracuseStep 252167 = 378251) B378251
theorem B284935 : Blo 251819 284935 := bstep (se 1 (by rfl) ⟨213701, by rfl⟩ : syracuseStep 284935 = 427403) B427403
theorem B252175 : Blo 251819 252175 := bstep (se 1 (by rfl) ⟨189131, by rfl⟩ : syracuseStep 252175 = 378263) B378263
theorem B252219 : Blo 251819 252219 := bstep (se 1 (by rfl) ⟨189164, by rfl⟩ : syracuseStep 252219 = 378329) B378329
theorem B383291 : Blo 251819 383291 := bstep (se 1 (by rfl) ⟨287468, by rfl⟩ : syracuseStep 383291 = 574937) B574937
theorem B383351 : Blo 251819 383351 := bstep (se 1 (by rfl) ⟨287513, by rfl⟩ : syracuseStep 383351 = 575027) B575027
theorem B252295 : Blo 251819 252295 := bstep (se 1 (by rfl) ⟨189221, by rfl⟩ : syracuseStep 252295 = 378443) B378443
theorem B252303 : Blo 251819 252303 := bstep (se 1 (by rfl) ⟨189227, by rfl⟩ : syracuseStep 252303 = 378455) B378455
theorem B383375 : Blo 251819 383375 := bstep (se 1 (by rfl) ⟨287531, by rfl⟩ : syracuseStep 383375 = 575063) B575063
theorem B645529 : Blo 251819 645529 := bstep (se 2 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 645529 = 484147) B484147
theorem B383417 : Blo 251819 383417 := bstep (se 2 (by rfl) ⟨143781, by rfl⟩ : syracuseStep 383417 = 287563) B287563
theorem B252347 : Blo 251819 252347 := bstep (se 1 (by rfl) ⟨189260, by rfl⟩ : syracuseStep 252347 = 378521) B378521
theorem B285115 : Blo 251819 285115 := bstep (se 1 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 285115 = 427673) B427673
theorem B612809 : Blo 251819 612809 := bstep (se 2 (by rfl) ⟨229803, by rfl⟩ : syracuseStep 612809 = 459607) B459607
theorem B1923587 : Blo 251819 1923587 := bstep (se 1 (by rfl) ⟨1442690, by rfl⟩ : syracuseStep 1923587 = 2885381) B2885381
theorem B252423 : Blo 251819 252423 := bstep (se 1 (by rfl) ⟨189317, by rfl⟩ : syracuseStep 252423 = 378635) B378635
theorem B383495 : Blo 251819 383495 := bstep (se 1 (by rfl) ⟨287621, by rfl⟩ : syracuseStep 383495 = 575243) B575243
theorem B252431 : Blo 251819 252431 := bstep (se 1 (by rfl) ⟨189323, by rfl⟩ : syracuseStep 252431 = 378647) B378647
theorem B383531 : Blo 251819 383531 := bstep (se 1 (by rfl) ⟨287648, by rfl⟩ : syracuseStep 383531 = 575297) B575297
theorem B252475 : Blo 251819 252475 := bstep (se 1 (by rfl) ⟨189356, by rfl⟩ : syracuseStep 252475 = 378713) B378713
theorem B645691 : Blo 251819 645691 := bstep (se 1 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 645691 = 968537) B968537
theorem B383561 : Blo 251819 383561 := bstep (se 2 (by rfl) ⟨143835, by rfl⟩ : syracuseStep 383561 = 287671) B287671
theorem B2185805 : Blo 251819 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B252551 : Blo 251819 252551 := bstep (se 1 (by rfl) ⟨189413, by rfl⟩ : syracuseStep 252551 = 378827) B378827
theorem B252559 : Blo 251819 252559 := bstep (se 1 (by rfl) ⟨189419, by rfl⟩ : syracuseStep 252559 = 378839) B378839
theorem B252603 : Blo 251819 252603 := bstep (se 1 (by rfl) ⟨189452, by rfl⟩ : syracuseStep 252603 = 378905) B378905
theorem B383675 : Blo 251819 383675 := bstep (se 1 (by rfl) ⟨287756, by rfl⟩ : syracuseStep 383675 = 575513) B575513
theorem B645833 : Blo 251819 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B252679 : Blo 251819 252679 := bstep (se 1 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 252679 = 379019) B379019
theorem B252687 : Blo 251819 252687 := bstep (se 1 (by rfl) ⟨189515, by rfl⟩ : syracuseStep 252687 = 379031) B379031
theorem B252731 : Blo 251819 252731 := bstep (se 1 (by rfl) ⟨189548, by rfl⟩ : syracuseStep 252731 = 379097) B379097
theorem B252807 : Blo 251819 252807 := bstep (se 1 (by rfl) ⟨189605, by rfl⟩ : syracuseStep 252807 = 379211) B379211
theorem B252815 : Blo 251819 252815 := bstep (se 1 (by rfl) ⟨189611, by rfl⟩ : syracuseStep 252815 = 379223) B379223
theorem B285583 : Blo 251819 285583 := bstep (se 1 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 285583 = 428375) B428375
theorem B252859 : Blo 251819 252859 := bstep (se 1 (by rfl) ⟨189644, by rfl⟩ : syracuseStep 252859 = 379289) B379289
theorem B482249 : Blo 251819 482249 := bstep (se 2 (by rfl) ⟨180843, by rfl⟩ : syracuseStep 482249 = 361687) B361687
theorem B252935 : Blo 251819 252935 := bstep (se 1 (by rfl) ⟨189701, by rfl⟩ : syracuseStep 252935 = 379403) B379403
theorem B252943 : Blo 251819 252943 := bstep (se 1 (by rfl) ⟨189707, by rfl⟩ : syracuseStep 252943 = 379415) B379415
theorem B646177 : Blo 251819 646177 := bstep (se 2 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 646177 = 484633) B484633
theorem B252987 : Blo 251819 252987 := bstep (se 1 (by rfl) ⟨189740, by rfl⟩ : syracuseStep 252987 = 379481) B379481
theorem B253063 : Blo 251819 253063 := bstep (se 1 (by rfl) ⟨189797, by rfl⟩ : syracuseStep 253063 = 379595) B379595
theorem B253071 : Blo 251819 253071 := bstep (se 1 (by rfl) ⟨189803, by rfl⟩ : syracuseStep 253071 = 379607) B379607
theorem B253115 : Blo 251819 253115 := bstep (se 1 (by rfl) ⟨189836, by rfl⟩ : syracuseStep 253115 = 379673) B379673
theorem B253191 : Blo 251819 253191 := bstep (se 1 (by rfl) ⟨189893, by rfl⟩ : syracuseStep 253191 = 379787) B379787
theorem B253199 : Blo 251819 253199 := bstep (se 1 (by rfl) ⟨189899, by rfl⟩ : syracuseStep 253199 = 379799) B379799
theorem B253243 : Blo 251819 253243 := bstep (se 1 (by rfl) ⟨189932, by rfl⟩ : syracuseStep 253243 = 379865) B379865
theorem B253319 : Blo 251819 253319 := bstep (se 1 (by rfl) ⟨189989, by rfl⟩ : syracuseStep 253319 = 379979) B379979
theorem B286087 : Blo 251819 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B253327 : Blo 251819 253327 := bstep (se 1 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 253327 = 379991) B379991
theorem B941465 : Blo 251819 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B318907 : Blo 251819 318907 := bstep (se 1 (by rfl) ⟨239180, by rfl⟩ : syracuseStep 318907 = 478361) B478361
theorem B253371 : Blo 251819 253371 := bstep (se 1 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 253371 = 380057) B380057
theorem B253447 : Blo 251819 253447 := bstep (se 1 (by rfl) ⟨190085, by rfl⟩ : syracuseStep 253447 = 380171) B380171
theorem B253455 : Blo 251819 253455 := bstep (se 1 (by rfl) ⟨190091, by rfl⟩ : syracuseStep 253455 = 380183) B380183
theorem B253499 : Blo 251819 253499 := bstep (se 1 (by rfl) ⟨190124, by rfl⟩ : syracuseStep 253499 = 380249) B380249
theorem B286267 : Blo 251819 286267 := bstep (se 1 (by rfl) ⟨214700, by rfl⟩ : syracuseStep 286267 = 429401) B429401
theorem B646775 : Blo 251819 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B253575 : Blo 251819 253575 := bstep (se 1 (by rfl) ⟨190181, by rfl⟩ : syracuseStep 253575 = 380363) B380363
theorem B253583 : Blo 251819 253583 := bstep (se 1 (by rfl) ⟨190187, by rfl⟩ : syracuseStep 253583 = 380375) B380375
theorem B2612915 : Blo 251819 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B2449075 : Blo 251819 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B253627 : Blo 251819 253627 := bstep (se 1 (by rfl) ⟨190220, by rfl⟩ : syracuseStep 253627 = 380441) B380441
theorem B253703 : Blo 251819 253703 := bstep (se 1 (by rfl) ⟨190277, by rfl⟩ : syracuseStep 253703 = 380555) B380555
theorem B253711 : Blo 251819 253711 := bstep (se 1 (by rfl) ⟨190283, by rfl⟩ : syracuseStep 253711 = 380567) B380567
theorem B810785 : Blo 251819 810785 := bstep (se 2 (by rfl) ⟨304044, by rfl⟩ : syracuseStep 810785 = 608089) B608089
theorem B253755 : Blo 251819 253755 := bstep (se 1 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 253755 = 380633) B380633
theorem B253831 : Blo 251819 253831 := bstep (se 1 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 253831 = 380747) B380747
theorem B253839 : Blo 251819 253839 := bstep (se 1 (by rfl) ⟨190379, by rfl⟩ : syracuseStep 253839 = 380759) B380759
theorem B810899 : Blo 251819 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B319403 : Blo 251819 319403 := bstep (se 1 (by rfl) ⟨239552, by rfl⟩ : syracuseStep 319403 = 479105) B479105
theorem B253883 : Blo 251819 253883 := bstep (se 1 (by rfl) ⟨190412, by rfl⟩ : syracuseStep 253883 = 380825) B380825
theorem B253959 : Blo 251819 253959 := bstep (se 1 (by rfl) ⟨190469, by rfl⟩ : syracuseStep 253959 = 380939) B380939
theorem B253967 : Blo 251819 253967 := bstep (se 1 (by rfl) ⟨190475, by rfl⟩ : syracuseStep 253967 = 380951) B380951
theorem B286735 : Blo 251819 286735 := bstep (se 1 (by rfl) ⟨215051, by rfl⟩ : syracuseStep 286735 = 430103) B430103
theorem B254011 : Blo 251819 254011 := bstep (se 1 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 254011 = 381017) B381017
theorem B254087 : Blo 251819 254087 := bstep (se 1 (by rfl) ⟨190565, by rfl⟩ : syracuseStep 254087 = 381131) B381131
theorem B254095 : Blo 251819 254095 := bstep (se 1 (by rfl) ⟨190571, by rfl⟩ : syracuseStep 254095 = 381143) B381143
theorem B254139 : Blo 251819 254139 := bstep (se 1 (by rfl) ⟨190604, by rfl⟩ : syracuseStep 254139 = 381209) B381209
theorem B1368265 : Blo 251819 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B254215 : Blo 251819 254215 := bstep (se 1 (by rfl) ⟨190661, by rfl⟩ : syracuseStep 254215 = 381323) B381323
theorem B254223 : Blo 251819 254223 := bstep (se 1 (by rfl) ⟨190667, by rfl⟩ : syracuseStep 254223 = 381335) B381335
theorem B516385 : Blo 251819 516385 := bstep (se 2 (by rfl) ⟨193644, by rfl⟩ : syracuseStep 516385 = 387289) B387289
theorem B254267 : Blo 251819 254267 := bstep (se 1 (by rfl) ⟨190700, by rfl⟩ : syracuseStep 254267 = 381401) B381401
theorem B319879 : Blo 251819 319879 := bstep (se 1 (by rfl) ⟨239909, by rfl⟩ : syracuseStep 319879 = 479819) B479819
theorem B254343 : Blo 251819 254343 := bstep (se 1 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 254343 = 381515) B381515
theorem B254351 : Blo 251819 254351 := bstep (se 1 (by rfl) ⟨190763, by rfl⟩ : syracuseStep 254351 = 381527) B381527
theorem B254395 : Blo 251819 254395 := bstep (se 1 (by rfl) ⟨190796, by rfl⟩ : syracuseStep 254395 = 381593) B381593
theorem B254471 : Blo 251819 254471 := bstep (se 1 (by rfl) ⟨190853, by rfl⟩ : syracuseStep 254471 = 381707) B381707
theorem B287239 : Blo 251819 287239 := bstep (se 1 (by rfl) ⟨215429, by rfl⟩ : syracuseStep 287239 = 430859) B430859
theorem B254479 : Blo 251819 254479 := bstep (se 1 (by rfl) ⟨190859, by rfl⟩ : syracuseStep 254479 = 381719) B381719
theorem B254523 : Blo 251819 254523 := bstep (se 1 (by rfl) ⟨190892, by rfl⟩ : syracuseStep 254523 = 381785) B381785
theorem B2155085 : Blo 251819 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B254599 : Blo 251819 254599 := bstep (se 1 (by rfl) ⟨190949, by rfl⟩ : syracuseStep 254599 = 381899) B381899
theorem B254607 : Blo 251819 254607 := bstep (se 1 (by rfl) ⟨190955, by rfl⟩ : syracuseStep 254607 = 381911) B381911
theorem B254651 : Blo 251819 254651 := bstep (se 1 (by rfl) ⟨190988, by rfl⟩ : syracuseStep 254651 = 381977) B381977
theorem B287419 : Blo 251819 287419 := bstep (se 1 (by rfl) ⟨215564, by rfl⟩ : syracuseStep 287419 = 431129) B431129
theorem B1532609 : Blo 251819 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B2745089 : Blo 251819 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B254727 : Blo 251819 254727 := bstep (se 1 (by rfl) ⟨191045, by rfl⟩ : syracuseStep 254727 = 382091) B382091
theorem B254735 : Blo 251819 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B680737 : Blo 251819 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B254779 : Blo 251819 254779 := bstep (se 1 (by rfl) ⟨191084, by rfl⟩ : syracuseStep 254779 = 382169) B382169
theorem B320375 : Blo 251819 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B254855 : Blo 251819 254855 := bstep (se 1 (by rfl) ⟨191141, by rfl⟩ : syracuseStep 254855 = 382283) B382283
theorem B484231 : Blo 251819 484231 := bstep (se 1 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 484231 = 726347) B726347
theorem B254863 : Blo 251819 254863 := bstep (se 1 (by rfl) ⟨191147, by rfl⟩ : syracuseStep 254863 = 382295) B382295
theorem B254907 : Blo 251819 254907 := bstep (se 1 (by rfl) ⟨191180, by rfl⟩ : syracuseStep 254907 = 382361) B382361
theorem B254983 : Blo 251819 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B320527 : Blo 251819 320527 := bstep (se 1 (by rfl) ⟨240395, by rfl⟩ : syracuseStep 320527 = 480791) B480791
theorem B254991 : Blo 251819 254991 := bstep (se 1 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 254991 = 382487) B382487
theorem B255035 : Blo 251819 255035 := bstep (se 1 (by rfl) ⟨191276, by rfl⟩ : syracuseStep 255035 = 382553) B382553
theorem B255111 : Blo 251819 255111 := bstep (se 1 (by rfl) ⟨191333, by rfl⟩ : syracuseStep 255111 = 382667) B382667
theorem B255119 : Blo 251819 255119 := bstep (se 1 (by rfl) ⟨191339, by rfl⟩ : syracuseStep 255119 = 382679) B382679
theorem B320699 : Blo 251819 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B255163 : Blo 251819 255163 := bstep (se 1 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 255163 = 382745) B382745
theorem B255239 : Blo 251819 255239 := bstep (se 1 (by rfl) ⟨191429, by rfl⟩ : syracuseStep 255239 = 382859) B382859
theorem B255247 : Blo 251819 255247 := bstep (se 1 (by rfl) ⟨191435, by rfl⟩ : syracuseStep 255247 = 382871) B382871
theorem B2155835 : Blo 251819 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B255291 : Blo 251819 255291 := bstep (se 1 (by rfl) ⟨191468, by rfl⟩ : syracuseStep 255291 = 382937) B382937
theorem B255367 : Blo 251819 255367 := bstep (se 1 (by rfl) ⟨191525, by rfl⟩ : syracuseStep 255367 = 383051) B383051
theorem B255375 : Blo 251819 255375 := bstep (se 1 (by rfl) ⟨191531, by rfl⟩ : syracuseStep 255375 = 383063) B383063
theorem B255419 : Blo 251819 255419 := bstep (se 1 (by rfl) ⟨191564, by rfl⟩ : syracuseStep 255419 = 383129) B383129
theorem B681473 : Blo 251819 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B255495 : Blo 251819 255495 := bstep (se 1 (by rfl) ⟨191621, by rfl⟩ : syracuseStep 255495 = 383243) B383243
theorem B255503 : Blo 251819 255503 := bstep (se 1 (by rfl) ⟨191627, by rfl⟩ : syracuseStep 255503 = 383255) B383255
theorem B255547 : Blo 251819 255547 := bstep (se 1 (by rfl) ⟨191660, by rfl⟩ : syracuseStep 255547 = 383321) B383321
theorem B255623 : Blo 251819 255623 := bstep (se 1 (by rfl) ⟨191717, by rfl⟩ : syracuseStep 255623 = 383435) B383435
theorem B255631 : Blo 251819 255631 := bstep (se 1 (by rfl) ⟨191723, by rfl⟩ : syracuseStep 255631 = 383447) B383447
theorem B255675 : Blo 251819 255675 := bstep (se 1 (by rfl) ⟨191756, by rfl⟩ : syracuseStep 255675 = 383513) B383513
theorem B255751 : Blo 251819 255751 := bstep (se 1 (by rfl) ⟨191813, by rfl⟩ : syracuseStep 255751 = 383627) B383627
theorem B255759 : Blo 251819 255759 := bstep (se 1 (by rfl) ⟨191819, by rfl⟩ : syracuseStep 255759 = 383639) B383639
theorem B255803 : Blo 251819 255803 := bstep (se 1 (by rfl) ⟨191852, by rfl⟩ : syracuseStep 255803 = 383705) B383705
theorem B321671 : Blo 251819 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B813257 : Blo 251819 813257 := bstep (se 2 (by rfl) ⟨304971, by rfl⟩ : syracuseStep 813257 = 609943) B609943
theorem B1436039 : Blo 251819 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B813655 : Blo 251819 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B322319 : Blo 251819 322319 := bstep (se 1 (by rfl) ⟨241739, by rfl⟩ : syracuseStep 322319 = 483479) B483479
theorem B1370969 : Blo 251819 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B3140441 : Blo 251819 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B2157475 : Blo 251819 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B650273 : Blo 251819 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B7400963 : Blo 251819 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B1371659 : Blo 251819 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B650767 : Blo 251819 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B683635 : Blo 251819 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B1928933 : Blo 251819 1928933 := bstep (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) B361675
theorem B2813849 : Blo 251819 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B2879549 : Blo 251819 2879549 := bstep (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) B1079831
theorem B5009501 : Blo 251819 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B487951 : Blo 251819 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B717427 : Blo 251819 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B717655 : Blo 251819 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B2454533 : Blo 251819 2454533 := bstep (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) B460225
theorem B2783243 : Blo 251819 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B850121 : Blo 251819 850121 := bstep (se 2 (by rfl) ⟨318795, by rfl⟩ : syracuseStep 850121 = 637591) B637591
theorem B358663 : Blo 251819 358663 := bstep (se 1 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 358663 = 537995) B537995
theorem B719239 : Blo 251819 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B8288729 : Blo 251819 8288729 := bstep (se 2 (by rfl) ⟨3108273, by rfl⟩ : syracuseStep 8288729 = 6216547) B6216547
theorem B1374839 : Blo 251819 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B719513 : Blo 251819 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B850823 : Blo 251819 850823 := bstep (se 1 (by rfl) ⟨638117, by rfl⟩ : syracuseStep 850823 = 1276235) B1276235
theorem B1440665 : Blo 251819 1440665 := bstep (se 2 (by rfl) ⟨540249, by rfl⟩ : syracuseStep 1440665 = 1080499) B1080499
theorem B1309661 : Blo 251819 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B621611 : Blo 251819 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B457913 : Blo 251819 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B851201 : Blo 251819 851201 := bstep (se 2 (by rfl) ⟨319200, by rfl⟩ : syracuseStep 851201 = 638401) B638401
theorem B720161 : Blo 251819 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B425351 : Blo 251819 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B1277369 : Blo 251819 1277369 := bstep (se 2 (by rfl) ⟨479013, by rfl⟩ : syracuseStep 1277369 = 958027) B958027
theorem B9305549 : Blo 251819 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B917021 : Blo 251819 917021 := bstep (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) B343883
theorem B360121 : Blo 251819 360121 := bstep (se 2 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 360121 = 270091) B270091
theorem B5898269 : Blo 251819 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B426107 : Blo 251819 426107 := bstep (se 1 (by rfl) ⟨319580, by rfl⟩ : syracuseStep 426107 = 639161) B639161
theorem B3244211 : Blo 251819 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B23298293 : Blo 251819 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B688513 : Blo 251819 688513 := bstep (se 2 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 688513 = 516385) B516385
theorem B852443 : Blo 251819 852443 := bstep (se 1 (by rfl) ⟨639332, by rfl⟩ : syracuseStep 852443 = 1278665) B1278665
theorem B426505 : Blo 251819 426505 := bstep (se 2 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 426505 = 319879) B319879
theorem B4915829 : Blo 251819 4915829 := bstep (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) B460859
theorem B426667 : Blo 251819 426667 := bstep (se 1 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 426667 = 640001) B640001
theorem B721619 : Blo 251819 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B459475 : Blo 251819 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B7537481 : Blo 251819 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B1278827 : Blo 251819 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B721847 : Blo 251819 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B426971 : Blo 251819 426971 := bstep (se 1 (by rfl) ⟨320228, by rfl⟩ : syracuseStep 426971 = 640457) B640457
theorem B853145 : Blo 251819 853145 := bstep (se 2 (by rfl) ⟨319929, by rfl⟩ : syracuseStep 853145 = 639859) B639859
theorem B427207 : Blo 251819 427207 := bstep (se 1 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 427207 = 640811) B640811
theorem B427369 : Blo 251819 427369 := bstep (se 2 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 427369 = 320527) B320527
theorem B1934765 : Blo 251819 1934765 := bstep (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) B725537
theorem B361903 : Blo 251819 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B1279475 : Blo 251819 1279475 := bstep (se 1 (by rfl) ⟨959606, by rfl⟩ : syracuseStep 1279475 = 1919213) B1919213
theorem B722621 : Blo 251819 722621 := bstep (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) B270983
theorem B427963 : Blo 251819 427963 := bstep (se 1 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 427963 = 641945) B641945
theorem B428071 : Blo 251819 428071 := bstep (se 1 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 428071 = 642107) B642107
theorem B854333 : Blo 251819 854333 := bstep (se 3 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 854333 = 320375) B320375
theorem B723305 : Blo 251819 723305 := bstep (se 2 (by rfl) ⟨271239, by rfl⟩ : syracuseStep 723305 = 542479) B542479
theorem B428395 : Blo 251819 428395 := bstep (se 1 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 428395 = 642593) B642593
theorem B4098437 : Blo 251819 4098437 := bstep (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) B768457
theorem B5474951 : Blo 251819 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B920249 : Blo 251819 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B1280771 : Blo 251819 1280771 := bstep (se 1 (by rfl) ⟨960578, by rfl⟩ : syracuseStep 1280771 = 1921157) B1921157
theorem B723887 : Blo 251819 723887 := bstep (se 1 (by rfl) ⟨542915, by rfl⟩ : syracuseStep 723887 = 1085831) B1085831
theorem B2067383 : Blo 251819 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B855197 : Blo 251819 855197 := bstep (se 3 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 855197 = 320699) B320699
theorem B429455 : Blo 251819 429455 := bstep (se 1 (by rfl) ⟨322091, by rfl⟩ : syracuseStep 429455 = 644183) B644183
theorem B1084873 : Blo 251819 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B5312087 : Blo 251819 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B429691 : Blo 251819 429691 := bstep (se 1 (by rfl) ⟨322268, by rfl⟩ : syracuseStep 429691 = 644537) B644537
theorem B1379963 : Blo 251819 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B855737 : Blo 251819 855737 := bstep (se 2 (by rfl) ⟨320901, by rfl⟩ : syracuseStep 855737 = 641803) B641803
theorem B1937195 : Blo 251819 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B3477433 : Blo 251819 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B725071 : Blo 251819 725071 := bstep (se 1 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 725071 = 1087607) B1087607
theorem B856331 : Blo 251819 856331 := bstep (se 1 (by rfl) ⟨642248, by rfl⟩ : syracuseStep 856331 = 1284497) B1284497
theorem B1282391 : Blo 251819 1282391 := bstep (se 1 (by rfl) ⟨961793, by rfl⟩ : syracuseStep 1282391 = 1923587) B1923587
theorem B430555 : Blo 251819 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B856601 : Blo 251819 856601 := bstep (se 2 (by rfl) ⟨321225, by rfl⟩ : syracuseStep 856601 = 642451) B642451
theorem B627643 : Blo 251819 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B431183 : Blo 251819 431183 := bstep (se 1 (by rfl) ⟨323387, by rfl⟩ : syracuseStep 431183 = 646775) B646775
theorem B1741943 : Blo 251819 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B857735 : Blo 251819 857735 := bstep (se 1 (by rfl) ⟨643301, by rfl⟩ : syracuseStep 857735 = 1286603) B1286603
theorem B857789 : Blo 251819 857789 := bstep (se 3 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 857789 = 321671) B321671
theorem B2070305 : Blo 251819 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B1021739 : Blo 251819 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B857951 : Blo 251819 857951 := bstep (se 1 (by rfl) ⟨643463, by rfl⟩ : syracuseStep 857951 = 1286927) B1286927
theorem B858113 : Blo 251819 858113 := bstep (se 2 (by rfl) ⟨321792, by rfl⟩ : syracuseStep 858113 = 643585) B643585
theorem B956569 : Blo 251819 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B956873 : Blo 251819 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B3545633 : Blo 251819 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B858923 : Blo 251819 858923 := bstep (se 1 (by rfl) ⟨644192, by rfl⟩ : syracuseStep 858923 = 1288385) B1288385
theorem B957359 : Blo 251819 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B1448887 : Blo 251819 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B859193 : Blo 251819 859193 := bstep (se 2 (by rfl) ⟨322197, by rfl⟩ : syracuseStep 859193 = 644395) B644395
theorem B1973443 : Blo 251819 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B859517 : Blo 251819 859517 := bstep (se 3 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 859517 = 322319) B322319
theorem B859787 : Blo 251819 859787 := bstep (se 1 (by rfl) ⟨644840, by rfl⟩ : syracuseStep 859787 = 1289681) B1289681
theorem B7020269 : Blo 251819 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B1285955 : Blo 251819 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B1875899 : Blo 251819 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B270535 : Blo 251819 270535 := bstep (se 1 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 270535 = 405803) B405803
theorem B1450345 : Blo 251819 1450345 := bstep (se 2 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 1450345 = 1087759) B1087759
theorem B958985 : Blo 251819 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B3482135 : Blo 251819 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B860705 : Blo 251819 860705 := bstep (se 2 (by rfl) ⟨322764, by rfl⟩ : syracuseStep 860705 = 645529) B645529
theorem B860921 : Blo 251819 860921 := bstep (se 2 (by rfl) ⟨322845, by rfl⟩ : syracuseStep 860921 = 645691) B645691
theorem B1844045 : Blo 251819 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B861191 : Blo 251819 861191 := bstep (se 1 (by rfl) ⟨645893, by rfl⟩ : syracuseStep 861191 = 1291787) B1291787
theorem B861299 : Blo 251819 861299 := bstep (se 1 (by rfl) ⟨645974, by rfl⟩ : syracuseStep 861299 = 1291949) B1291949
theorem B861569 : Blo 251819 861569 := bstep (se 2 (by rfl) ⟨323088, by rfl⟩ : syracuseStep 861569 = 646177) B646177
theorem B566747 : Blo 251819 566747 := bstep (se 1 (by rfl) ⟨425060, by rfl⟩ : syracuseStep 566747 = 850121) B850121
theorem B14526053 : Blo 251819 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B2762387 : Blo 251819 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B567215 : Blo 251819 567215 := bstep (se 1 (by rfl) ⟨425411, by rfl⟩ : syracuseStep 567215 = 850823) B850823
theorem B960443 : Blo 251819 960443 := bstep (se 1 (by rfl) ⟨720332, by rfl⟩ : syracuseStep 960443 = 1440665) B1440665
theorem B403579 : Blo 251819 403579 := bstep (se 1 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 403579 = 605369) B605369
theorem B305275 : Blo 251819 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B567467 : Blo 251819 567467 := bstep (se 1 (by rfl) ⟨425600, by rfl⟩ : syracuseStep 567467 = 851201) B851201
theorem B862379 : Blo 251819 862379 := bstep (se 1 (by rfl) ⟨646784, by rfl⟩ : syracuseStep 862379 = 1293569) B1293569
theorem B6564077 : Blo 251819 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B2894129 : Blo 251819 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B6203699 : Blo 251819 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B568007 : Blo 251819 568007 := bstep (se 1 (by rfl) ⟨426005, by rfl⟩ : syracuseStep 568007 = 852011) B852011
theorem B862919 : Blo 251819 862919 := bstep (se 1 (by rfl) ⟨647189, by rfl⟩ : syracuseStep 862919 = 1294379) B1294379
theorem B1092305 : Blo 251819 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B1289033 : Blo 251819 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B404399 : Blo 251819 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B404489 : Blo 251819 404489 := bstep (se 2 (by rfl) ⟨151683, by rfl⟩ : syracuseStep 404489 = 303367) B303367
theorem B3910949 : Blo 251819 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B2043251 : Blo 251819 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B1027529 : Blo 251819 1027529 := bstep (se 2 (by rfl) ⟨385323, by rfl⟩ : syracuseStep 1027529 = 770647) B770647
theorem B1945127 : Blo 251819 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B568871 : Blo 251819 568871 := bstep (se 1 (by rfl) ⟨426653, by rfl⟩ : syracuseStep 568871 = 853307) B853307
theorem B1027723 : Blo 251819 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B569195 : Blo 251819 569195 := bstep (se 1 (by rfl) ⟨426896, by rfl⟩ : syracuseStep 569195 = 853793) B853793
theorem B569249 : Blo 251819 569249 := bstep (se 2 (by rfl) ⟨213468, by rfl⟩ : syracuseStep 569249 = 426937) B426937
theorem B1290329 : Blo 251819 1290329 := bstep (se 2 (by rfl) ⟨483873, by rfl⟩ : syracuseStep 1290329 = 967747) B967747
theorem B962675 : Blo 251819 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B569591 : Blo 251819 569591 := bstep (se 1 (by rfl) ⟨427193, by rfl⟩ : syracuseStep 569591 = 854387) B854387
theorem B1454851 : Blo 251819 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B570185 : Blo 251819 570185 := bstep (se 2 (by rfl) ⟨213819, by rfl⟩ : syracuseStep 570185 = 427639) B427639
theorem B406367 : Blo 251819 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B275495 : Blo 251819 275495 := bstep (se 1 (by rfl) ⟨206621, by rfl⟩ : syracuseStep 275495 = 413243) B413243
theorem B406777 : Blo 251819 406777 := bstep (se 2 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 406777 = 305083) B305083
theorem B2602405 : Blo 251819 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B767497 : Blo 251819 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B570977 : Blo 251819 570977 := bstep (se 2 (by rfl) ⟨214116, by rfl⟩ : syracuseStep 570977 = 428233) B428233
theorem B440057 : Blo 251819 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B964345 : Blo 251819 964345 := bstep (se 2 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 964345 = 723259) B723259
theorem B571319 : Blo 251819 571319 := bstep (se 1 (by rfl) ⟨428489, by rfl⟩ : syracuseStep 571319 = 856979) B856979
theorem B342055 : Blo 251819 342055 := bstep (se 1 (by rfl) ⟨256541, by rfl⟩ : syracuseStep 342055 = 513083) B513083
theorem B1227113 : Blo 251819 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B1554817 : Blo 251819 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B3684761 : Blo 251819 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B1030643 : Blo 251819 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B571913 : Blo 251819 571913 := bstep (se 2 (by rfl) ⟨214467, by rfl⟩ : syracuseStep 571913 = 428935) B428935
theorem B1817261 : Blo 251819 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B539335 : Blo 251819 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B572255 : Blo 251819 572255 := bstep (se 1 (by rfl) ⟨429191, by rfl⟩ : syracuseStep 572255 = 858383) B858383
theorem B1555307 : Blo 251819 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B768943 : Blo 251819 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B408539 : Blo 251819 408539 := bstep (se 1 (by rfl) ⟨306404, by rfl⟩ : syracuseStep 408539 = 612809) B612809
theorem B572435 : Blo 251819 572435 := bstep (se 1 (by rfl) ⟨429326, by rfl⟩ : syracuseStep 572435 = 858653) B858653
theorem B1457203 : Blo 251819 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B965789 : Blo 251819 965789 := bstep (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) B362171
theorem B965803 : Blo 251819 965803 := bstep (se 1 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 965803 = 1448705) B1448705
theorem B867689 : Blo 251819 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B572777 : Blo 251819 572777 := bstep (se 2 (by rfl) ⟨214791, by rfl⟩ : syracuseStep 572777 = 429583) B429583
theorem B638351 : Blo 251819 638351 := bstep (se 1 (by rfl) ⟨478763, by rfl⟩ : syracuseStep 638351 = 957527) B957527
theorem B966107 : Blo 251819 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B638675 : Blo 251819 638675 := bstep (se 1 (by rfl) ⟨479006, by rfl⟩ : syracuseStep 638675 = 958013) B958013
theorem B540523 : Blo 251819 540523 := bstep (se 1 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 540523 = 810785) B810785
theorem B540599 : Blo 251819 540599 := bstep (se 1 (by rfl) ⟨405449, by rfl⟩ : syracuseStep 540599 = 810899) B810899
theorem B573371 : Blo 251819 573371 := bstep (se 1 (by rfl) ⟨430028, by rfl⟩ : syracuseStep 573371 = 860057) B860057
theorem B573497 : Blo 251819 573497 := bstep (se 2 (by rfl) ⟨215061, by rfl⟩ : syracuseStep 573497 = 430123) B430123
theorem B573839 : Blo 251819 573839 := bstep (se 1 (by rfl) ⟨430379, by rfl⟩ : syracuseStep 573839 = 860759) B860759
theorem B574163 : Blo 251819 574163 := bstep (se 1 (by rfl) ⟨430622, by rfl⟩ : syracuseStep 574163 = 861245) B861245
theorem B639839 : Blo 251819 639839 := bstep (se 1 (by rfl) ⟨479879, by rfl⟩ : syracuseStep 639839 = 959759) B959759
theorem B377783 : Blo 251819 377783 := bstep (se 1 (by rfl) ⟨283337, by rfl⟩ : syracuseStep 377783 = 566675) B566675
theorem B377819 : Blo 251819 377819 := bstep (se 1 (by rfl) ⟨283364, by rfl⟩ : syracuseStep 377819 = 566729) B566729
theorem B1623233 : Blo 251819 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B378287 : Blo 251819 378287 := bstep (se 1 (by rfl) ⟨283715, by rfl⟩ : syracuseStep 378287 = 567431) B567431
theorem B542171 : Blo 251819 542171 := bstep (se 1 (by rfl) ⟨406628, by rfl⟩ : syracuseStep 542171 = 813257) B813257
theorem B378377 : Blo 251819 378377 := bstep (se 2 (by rfl) ⟨141891, by rfl⟩ : syracuseStep 378377 = 283783) B283783
theorem B378407 : Blo 251819 378407 := bstep (se 1 (by rfl) ⟨283805, by rfl⟩ : syracuseStep 378407 = 567611) B567611
theorem B378491 : Blo 251819 378491 := bstep (se 1 (by rfl) ⟨283868, by rfl⟩ : syracuseStep 378491 = 567737) B567737
theorem B575099 : Blo 251819 575099 := bstep (se 1 (by rfl) ⟨431324, by rfl⟩ : syracuseStep 575099 = 862649) B862649
theorem B378617 : Blo 251819 378617 := bstep (se 2 (by rfl) ⟨141981, by rfl⟩ : syracuseStep 378617 = 283963) B283963
theorem B575225 : Blo 251819 575225 := bstep (se 2 (by rfl) ⟨215709, by rfl⟩ : syracuseStep 575225 = 431419) B431419
theorem B378719 : Blo 251819 378719 := bstep (se 1 (by rfl) ⟨284039, by rfl⟩ : syracuseStep 378719 = 568079) B568079
theorem B378731 : Blo 251819 378731 := bstep (se 1 (by rfl) ⟨284048, by rfl⟩ : syracuseStep 378731 = 568097) B568097
theorem B640943 : Blo 251819 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B968705 : Blo 251819 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B575495 : Blo 251819 575495 := bstep (se 1 (by rfl) ⟨431621, by rfl⟩ : syracuseStep 575495 = 863243) B863243
theorem B968719 : Blo 251819 968719 := bstep (se 1 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 968719 = 1453079) B1453079
theorem B378959 : Blo 251819 378959 := bstep (se 1 (by rfl) ⟨284219, by rfl⟩ : syracuseStep 378959 = 568439) B568439
theorem B575567 : Blo 251819 575567 := bstep (se 1 (by rfl) ⟨431675, by rfl⟩ : syracuseStep 575567 = 863351) B863351
theorem B379079 : Blo 251819 379079 := bstep (se 1 (by rfl) ⟨284309, by rfl⟩ : syracuseStep 379079 = 568619) B568619
theorem B4933975 : Blo 251819 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B379241 : Blo 251819 379241 := bstep (se 2 (by rfl) ⟨142215, by rfl⟩ : syracuseStep 379241 = 284431) B284431
theorem B16566707 : Blo 251819 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B379319 : Blo 251819 379319 := bstep (se 1 (by rfl) ⟨284489, by rfl⟩ : syracuseStep 379319 = 568979) B568979
theorem B379355 : Blo 251819 379355 := bstep (se 1 (by rfl) ⟨284516, by rfl⟩ : syracuseStep 379355 = 569033) B569033
theorem B1919699 : Blo 251819 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B2902877 : Blo 251819 2902877 := bstep (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) B1088579
theorem B379823 : Blo 251819 379823 := bstep (se 1 (by rfl) ⟨284867, by rfl⟩ : syracuseStep 379823 = 569735) B569735
theorem B478217 : Blo 251819 478217 := bstep (se 2 (by rfl) ⟨179331, by rfl⟩ : syracuseStep 478217 = 358663) B358663
theorem B379913 : Blo 251819 379913 := bstep (se 2 (by rfl) ⟨142467, by rfl⟩ : syracuseStep 379913 = 284935) B284935
theorem B379943 : Blo 251819 379943 := bstep (se 1 (by rfl) ⟨284957, by rfl⟩ : syracuseStep 379943 = 569915) B569915
theorem B642127 : Blo 251819 642127 := bstep (se 1 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 642127 = 963191) B963191
theorem B380027 : Blo 251819 380027 := bstep (se 1 (by rfl) ⟨285020, by rfl⟩ : syracuseStep 380027 = 570041) B570041
theorem B380153 : Blo 251819 380153 := bstep (se 2 (by rfl) ⟨142557, by rfl⟩ : syracuseStep 380153 = 285115) B285115
theorem B969995 : Blo 251819 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B380255 : Blo 251819 380255 := bstep (se 1 (by rfl) ⟨285191, by rfl⟩ : syracuseStep 380255 = 570383) B570383
theorem B380267 : Blo 251819 380267 := bstep (se 1 (by rfl) ⟨285200, by rfl⟩ : syracuseStep 380267 = 570401) B570401
theorem B380495 : Blo 251819 380495 := bstep (se 1 (by rfl) ⟨285371, by rfl⟩ : syracuseStep 380495 = 570743) B570743
theorem B380615 : Blo 251819 380615 := bstep (se 1 (by rfl) ⟨285461, by rfl⟩ : syracuseStep 380615 = 570923) B570923
theorem B970451 : Blo 251819 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B642775 : Blo 251819 642775 := bstep (se 1 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 642775 = 964163) B964163
theorem B380777 : Blo 251819 380777 := bstep (se 2 (by rfl) ⟨142791, by rfl⟩ : syracuseStep 380777 = 285583) B285583
theorem B380855 : Blo 251819 380855 := bstep (se 1 (by rfl) ⟨285641, by rfl⟩ : syracuseStep 380855 = 571283) B571283
theorem B380891 : Blo 251819 380891 := bstep (se 1 (by rfl) ⟨285668, by rfl⟩ : syracuseStep 380891 = 571337) B571337
theorem B1855495 : Blo 251819 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B643079 : Blo 251819 643079 := bstep (se 1 (by rfl) ⟨482309, by rfl⟩ : syracuseStep 643079 = 964619) B964619
theorem B3657757 : Blo 251819 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B5525819 : Blo 251819 5525819 := bstep (se 1 (by rfl) ⟨4144364, by rfl⟩ : syracuseStep 5525819 = 8288729) B8288729
theorem B381359 : Blo 251819 381359 := bstep (se 1 (by rfl) ⟨286019, by rfl⟩ : syracuseStep 381359 = 572039) B572039
theorem B479675 : Blo 251819 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B381449 : Blo 251819 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B381479 : Blo 251819 381479 := bstep (se 1 (by rfl) ⟨286109, by rfl⟩ : syracuseStep 381479 = 572219) B572219
theorem B381563 : Blo 251819 381563 := bstep (se 1 (by rfl) ⟨286172, by rfl⟩ : syracuseStep 381563 = 572345) B572345
theorem B873107 : Blo 251819 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B414407 : Blo 251819 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B381689 : Blo 251819 381689 := bstep (se 2 (by rfl) ⟨143133, by rfl⟩ : syracuseStep 381689 = 286267) B286267
theorem B381791 : Blo 251819 381791 := bstep (se 1 (by rfl) ⟨286343, by rfl⟩ : syracuseStep 381791 = 572687) B572687
theorem B480107 : Blo 251819 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B381803 : Blo 251819 381803 := bstep (se 1 (by rfl) ⟨286352, by rfl⟩ : syracuseStep 381803 = 572705) B572705
theorem B3265433 : Blo 251819 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B480161 : Blo 251819 480161 := bstep (se 2 (by rfl) ⟨180060, by rfl⟩ : syracuseStep 480161 = 360121) B360121
theorem B283567 : Blo 251819 283567 := bstep (se 1 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 283567 = 425351) B425351
theorem B1037231 : Blo 251819 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B611347 : Blo 251819 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B382031 : Blo 251819 382031 := bstep (se 1 (by rfl) ⟨286523, by rfl⟩ : syracuseStep 382031 = 573047) B573047
theorem B382151 : Blo 251819 382151 := bstep (se 1 (by rfl) ⟨286613, by rfl⟩ : syracuseStep 382151 = 573227) B573227
theorem B283999 : Blo 251819 283999 := bstep (se 1 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 283999 = 425999) B425999
theorem B382313 : Blo 251819 382313 := bstep (se 2 (by rfl) ⟨143367, by rfl⟩ : syracuseStep 382313 = 286735) B286735
theorem B382391 : Blo 251819 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B873929 : Blo 251819 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B382427 : Blo 251819 382427 := bstep (se 1 (by rfl) ⟨286820, by rfl⟩ : syracuseStep 382427 = 573641) B573641
theorem B1824353 : Blo 251819 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B284359 : Blo 251819 284359 := bstep (se 1 (by rfl) ⟨213269, by rfl⟩ : syracuseStep 284359 = 426539) B426539
theorem B1627847 : Blo 251819 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B2741975 : Blo 251819 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B2185055 : Blo 251819 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B251823 : Blo 251819 251823 := bstep (se 1 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 251823 = 377735) B377735
theorem B382895 : Blo 251819 382895 := bstep (se 1 (by rfl) ⟨287171, by rfl⟩ : syracuseStep 382895 = 574343) B574343
theorem B251847 : Blo 251819 251847 := bstep (se 1 (by rfl) ⟨188885, by rfl⟩ : syracuseStep 251847 = 377771) B377771
theorem B251867 : Blo 251819 251867 := bstep (se 1 (by rfl) ⟨188900, by rfl⟩ : syracuseStep 251867 = 377801) B377801
theorem B382985 : Blo 251819 382985 := bstep (se 2 (by rfl) ⟨143619, by rfl⟩ : syracuseStep 382985 = 287239) B287239
theorem B1923101 : Blo 251819 1923101 := bstep (se 3 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 1923101 = 721163) B721163
theorem B251943 : Blo 251819 251943 := bstep (se 1 (by rfl) ⟨188957, by rfl⟩ : syracuseStep 251943 = 377915) B377915
theorem B383015 : Blo 251819 383015 := bstep (se 1 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 383015 = 574523) B574523
theorem B251983 : Blo 251819 251983 := bstep (se 1 (by rfl) ⟨188987, by rfl⟩ : syracuseStep 251983 = 377975) B377975
theorem B251999 : Blo 251819 251999 := bstep (se 1 (by rfl) ⟨188999, by rfl⟩ : syracuseStep 251999 = 377999) B377999
theorem B252027 : Blo 251819 252027 := bstep (se 1 (by rfl) ⟨189020, by rfl⟩ : syracuseStep 252027 = 378041) B378041
theorem B383099 : Blo 251819 383099 := bstep (se 1 (by rfl) ⟨287324, by rfl⟩ : syracuseStep 383099 = 574649) B574649
theorem B252079 : Blo 251819 252079 := bstep (se 1 (by rfl) ⟨189059, by rfl⟩ : syracuseStep 252079 = 378119) B378119
theorem B252103 : Blo 251819 252103 := bstep (se 1 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 252103 = 378155) B378155
theorem B252123 : Blo 251819 252123 := bstep (se 1 (by rfl) ⟨189092, by rfl⟩ : syracuseStep 252123 = 378185) B378185
theorem B645367 : Blo 251819 645367 := bstep (se 1 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 645367 = 968051) B968051
theorem B383225 : Blo 251819 383225 := bstep (se 2 (by rfl) ⟨143709, by rfl⟩ : syracuseStep 383225 = 287419) B287419
theorem B252199 : Blo 251819 252199 := bstep (se 1 (by rfl) ⟨189149, by rfl⟩ : syracuseStep 252199 = 378299) B378299
theorem B3889457 : Blo 251819 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B252239 : Blo 251819 252239 := bstep (se 1 (by rfl) ⟨189179, by rfl⟩ : syracuseStep 252239 = 378359) B378359
theorem B252255 : Blo 251819 252255 := bstep (se 1 (by rfl) ⟨189191, by rfl⟩ : syracuseStep 252255 = 378383) B378383
theorem B383327 : Blo 251819 383327 := bstep (se 1 (by rfl) ⟨287495, by rfl⟩ : syracuseStep 383327 = 574991) B574991
theorem B383339 : Blo 251819 383339 := bstep (se 1 (by rfl) ⟨287504, by rfl⟩ : syracuseStep 383339 = 575009) B575009
theorem B252283 : Blo 251819 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B907649 : Blo 251819 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B252335 : Blo 251819 252335 := bstep (se 1 (by rfl) ⟨189251, by rfl⟩ : syracuseStep 252335 = 378503) B378503
theorem B252359 : Blo 251819 252359 := bstep (se 1 (by rfl) ⟨189269, by rfl⟩ : syracuseStep 252359 = 378539) B378539
theorem B252379 : Blo 251819 252379 := bstep (se 1 (by rfl) ⟨189284, by rfl⟩ : syracuseStep 252379 = 378569) B378569
theorem B481801 : Blo 251819 481801 := bstep (se 2 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 481801 = 361351) B361351
theorem B645641 : Blo 251819 645641 := bstep (se 2 (by rfl) ⟨242115, by rfl⟩ : syracuseStep 645641 = 484231) B484231
theorem B252455 : Blo 251819 252455 := bstep (se 1 (by rfl) ⟨189341, by rfl⟩ : syracuseStep 252455 = 378683) B378683
theorem B285223 : Blo 251819 285223 := bstep (se 1 (by rfl) ⟨213917, by rfl⟩ : syracuseStep 285223 = 427835) B427835
theorem B645671 : Blo 251819 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B252495 : Blo 251819 252495 := bstep (se 1 (by rfl) ⟨189371, by rfl⟩ : syracuseStep 252495 = 378743) B378743
theorem B383567 : Blo 251819 383567 := bstep (se 1 (by rfl) ⟨287675, by rfl⟩ : syracuseStep 383567 = 575351) B575351
theorem B252511 : Blo 251819 252511 := bstep (se 1 (by rfl) ⟨189383, by rfl⟩ : syracuseStep 252511 = 378767) B378767
theorem B252539 : Blo 251819 252539 := bstep (se 1 (by rfl) ⟨189404, by rfl⟩ : syracuseStep 252539 = 378809) B378809
theorem B252591 : Blo 251819 252591 := bstep (se 1 (by rfl) ⟨189443, by rfl⟩ : syracuseStep 252591 = 378887) B378887
theorem B252615 : Blo 251819 252615 := bstep (se 1 (by rfl) ⟨189461, by rfl⟩ : syracuseStep 252615 = 378923) B378923
theorem B383687 : Blo 251819 383687 := bstep (se 1 (by rfl) ⟨287765, by rfl⟩ : syracuseStep 383687 = 575531) B575531
theorem B2448073 : Blo 251819 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B252635 : Blo 251819 252635 := bstep (se 1 (by rfl) ⟨189476, by rfl⟩ : syracuseStep 252635 = 378953) B378953
theorem B252711 : Blo 251819 252711 := bstep (se 1 (by rfl) ⟨189533, by rfl⟩ : syracuseStep 252711 = 379067) B379067
theorem B252751 : Blo 251819 252751 := bstep (se 1 (by rfl) ⟨189563, by rfl⟩ : syracuseStep 252751 = 379127) B379127
theorem B252767 : Blo 251819 252767 := bstep (se 1 (by rfl) ⟨189575, by rfl⟩ : syracuseStep 252767 = 379151) B379151
theorem B645995 : Blo 251819 645995 := bstep (se 1 (by rfl) ⟨484496, by rfl⟩ : syracuseStep 645995 = 968993) B968993
theorem B252795 : Blo 251819 252795 := bstep (se 1 (by rfl) ⟨189596, by rfl⟩ : syracuseStep 252795 = 379193) B379193
theorem B252847 : Blo 251819 252847 := bstep (se 1 (by rfl) ⟨189635, by rfl⟩ : syracuseStep 252847 = 379271) B379271
theorem B252871 : Blo 251819 252871 := bstep (se 1 (by rfl) ⟨189653, by rfl⟩ : syracuseStep 252871 = 379307) B379307
theorem B252891 : Blo 251819 252891 := bstep (se 1 (by rfl) ⟨189668, by rfl⟩ : syracuseStep 252891 = 379337) B379337
theorem B252967 : Blo 251819 252967 := bstep (se 1 (by rfl) ⟨189725, by rfl⟩ : syracuseStep 252967 = 379451) B379451
theorem B253007 : Blo 251819 253007 := bstep (se 1 (by rfl) ⟨189755, by rfl⟩ : syracuseStep 253007 = 379511) B379511
theorem B253023 : Blo 251819 253023 := bstep (se 1 (by rfl) ⟨189767, by rfl⟩ : syracuseStep 253023 = 379535) B379535
theorem B253051 : Blo 251819 253051 := bstep (se 1 (by rfl) ⟨189788, by rfl⟩ : syracuseStep 253051 = 379577) B379577
theorem B253103 : Blo 251819 253103 := bstep (se 1 (by rfl) ⟨189827, by rfl⟩ : syracuseStep 253103 = 379655) B379655
theorem B253127 : Blo 251819 253127 := bstep (se 1 (by rfl) ⟨189845, by rfl⟩ : syracuseStep 253127 = 379691) B379691
theorem B253147 : Blo 251819 253147 := bstep (se 1 (by rfl) ⟨189860, by rfl⟩ : syracuseStep 253147 = 379721) B379721
theorem B2055415 : Blo 251819 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B253223 : Blo 251819 253223 := bstep (se 1 (by rfl) ⟨189917, by rfl⟩ : syracuseStep 253223 = 379835) B379835
theorem B253263 : Blo 251819 253263 := bstep (se 1 (by rfl) ⟨189947, by rfl⟩ : syracuseStep 253263 = 379895) B379895
theorem B253279 : Blo 251819 253279 := bstep (se 1 (by rfl) ⟨189959, by rfl⟩ : syracuseStep 253279 = 379919) B379919
theorem B253307 : Blo 251819 253307 := bstep (se 1 (by rfl) ⟨189980, by rfl⟩ : syracuseStep 253307 = 379961) B379961
theorem B253359 : Blo 251819 253359 := bstep (se 1 (by rfl) ⟨190019, by rfl⟩ : syracuseStep 253359 = 380039) B380039
theorem B482735 : Blo 251819 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B253383 : Blo 251819 253383 := bstep (se 1 (by rfl) ⟨190037, by rfl⟩ : syracuseStep 253383 = 380075) B380075
theorem B253403 : Blo 251819 253403 := bstep (se 1 (by rfl) ⟨190052, by rfl⟩ : syracuseStep 253403 = 380105) B380105
theorem B646643 : Blo 251819 646643 := bstep (se 1 (by rfl) ⟨484982, by rfl⟩ : syracuseStep 646643 = 969965) B969965
theorem B253479 : Blo 251819 253479 := bstep (se 1 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 253479 = 380219) B380219
theorem B253519 : Blo 251819 253519 := bstep (se 1 (by rfl) ⟨190139, by rfl⟩ : syracuseStep 253519 = 380279) B380279
theorem B253535 : Blo 251819 253535 := bstep (se 1 (by rfl) ⟨190151, by rfl⟩ : syracuseStep 253535 = 380303) B380303
theorem B253563 : Blo 251819 253563 := bstep (se 1 (by rfl) ⟨190172, by rfl⟩ : syracuseStep 253563 = 380345) B380345
theorem B810643 : Blo 251819 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B253615 : Blo 251819 253615 := bstep (se 1 (by rfl) ⟨190211, by rfl⟩ : syracuseStep 253615 = 380423) B380423
theorem B253639 : Blo 251819 253639 := bstep (se 1 (by rfl) ⟨190229, by rfl⟩ : syracuseStep 253639 = 380459) B380459
theorem B614087 : Blo 251819 614087 := bstep (se 1 (by rfl) ⟨460565, by rfl⟩ : syracuseStep 614087 = 921131) B921131
theorem B253659 : Blo 251819 253659 := bstep (se 1 (by rfl) ⟨190244, by rfl⟩ : syracuseStep 253659 = 380489) B380489
theorem B614137 : Blo 251819 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B253735 : Blo 251819 253735 := bstep (se 1 (by rfl) ⟨190301, by rfl⟩ : syracuseStep 253735 = 380603) B380603
theorem B253775 : Blo 251819 253775 := bstep (se 1 (by rfl) ⟨190331, by rfl⟩ : syracuseStep 253775 = 380663) B380663
theorem B253791 : Blo 251819 253791 := bstep (se 1 (by rfl) ⟨190343, by rfl⟩ : syracuseStep 253791 = 380687) B380687
theorem B253819 : Blo 251819 253819 := bstep (se 1 (by rfl) ⟨190364, by rfl⟩ : syracuseStep 253819 = 380729) B380729
theorem B253871 : Blo 251819 253871 := bstep (se 1 (by rfl) ⟨190403, by rfl⟩ : syracuseStep 253871 = 380807) B380807
theorem B483259 : Blo 251819 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B647099 : Blo 251819 647099 := bstep (se 1 (by rfl) ⟨485324, by rfl⟩ : syracuseStep 647099 = 970649) B970649
theorem B253895 : Blo 251819 253895 := bstep (se 1 (by rfl) ⟨190421, by rfl⟩ : syracuseStep 253895 = 380843) B380843
theorem B253915 : Blo 251819 253915 := bstep (se 1 (by rfl) ⟨190436, by rfl⟩ : syracuseStep 253915 = 380873) B380873
theorem B253991 : Blo 251819 253991 := bstep (se 1 (by rfl) ⟨190493, by rfl⟩ : syracuseStep 253991 = 380987) B380987
theorem B254031 : Blo 251819 254031 := bstep (se 1 (by rfl) ⟨190523, by rfl⟩ : syracuseStep 254031 = 381047) B381047
theorem B254047 : Blo 251819 254047 := bstep (se 1 (by rfl) ⟨190535, by rfl⟩ : syracuseStep 254047 = 381071) B381071
theorem B254075 : Blo 251819 254075 := bstep (se 1 (by rfl) ⟨190556, by rfl⟩ : syracuseStep 254075 = 381113) B381113
theorem B286843 : Blo 251819 286843 := bstep (se 1 (by rfl) ⟨215132, by rfl⟩ : syracuseStep 286843 = 430265) B430265
theorem B15622307 : Blo 251819 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B254127 : Blo 251819 254127 := bstep (se 1 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 254127 = 381191) B381191
theorem B254151 : Blo 251819 254151 := bstep (se 1 (by rfl) ⟨190613, by rfl⟩ : syracuseStep 254151 = 381227) B381227
theorem B254171 : Blo 251819 254171 := bstep (se 1 (by rfl) ⟨190628, by rfl⟩ : syracuseStep 254171 = 381257) B381257
theorem B516343 : Blo 251819 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B254247 : Blo 251819 254247 := bstep (se 1 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 254247 = 381371) B381371
theorem B254287 : Blo 251819 254287 := bstep (se 1 (by rfl) ⟨190715, by rfl⟩ : syracuseStep 254287 = 381431) B381431
theorem B254303 : Blo 251819 254303 := bstep (se 1 (by rfl) ⟨190727, by rfl⟩ : syracuseStep 254303 = 381455) B381455
theorem B254331 : Blo 251819 254331 := bstep (se 1 (by rfl) ⟨190748, by rfl⟩ : syracuseStep 254331 = 381497) B381497
theorem B483745 : Blo 251819 483745 := bstep (se 2 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 483745 = 362809) B362809
theorem B254383 : Blo 251819 254383 := bstep (se 1 (by rfl) ⟨190787, by rfl⟩ : syracuseStep 254383 = 381575) B381575
theorem B516539 : Blo 251819 516539 := bstep (se 1 (by rfl) ⟨387404, by rfl⟩ : syracuseStep 516539 = 774809) B774809
theorem B254407 : Blo 251819 254407 := bstep (se 1 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 254407 = 381611) B381611
theorem B254427 : Blo 251819 254427 := bstep (se 1 (by rfl) ⟨190820, by rfl⟩ : syracuseStep 254427 = 381641) B381641
theorem B254503 : Blo 251819 254503 := bstep (se 1 (by rfl) ⟨190877, by rfl⟩ : syracuseStep 254503 = 381755) B381755
theorem B254543 : Blo 251819 254543 := bstep (se 1 (by rfl) ⟨190907, by rfl⟩ : syracuseStep 254543 = 381815) B381815
theorem B287311 : Blo 251819 287311 := bstep (se 1 (by rfl) ⟨215483, by rfl⟩ : syracuseStep 287311 = 430967) B430967
theorem B254559 : Blo 251819 254559 := bstep (se 1 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 254559 = 381839) B381839
theorem B254587 : Blo 251819 254587 := bstep (se 1 (by rfl) ⟨190940, by rfl⟩ : syracuseStep 254587 = 381881) B381881
theorem B254639 : Blo 251819 254639 := bstep (se 1 (by rfl) ⟨190979, by rfl⟩ : syracuseStep 254639 = 381959) B381959
theorem B254663 : Blo 251819 254663 := bstep (se 1 (by rfl) ⟨190997, by rfl⟩ : syracuseStep 254663 = 381995) B381995
theorem B254683 : Blo 251819 254683 := bstep (se 1 (by rfl) ⟨191012, by rfl⟩ : syracuseStep 254683 = 382025) B382025
theorem B254759 : Blo 251819 254759 := bstep (se 1 (by rfl) ⟨191069, by rfl⟩ : syracuseStep 254759 = 382139) B382139
theorem B254799 : Blo 251819 254799 := bstep (se 1 (by rfl) ⟨191099, by rfl⟩ : syracuseStep 254799 = 382199) B382199
theorem B254815 : Blo 251819 254815 := bstep (se 1 (by rfl) ⟨191111, by rfl⟩ : syracuseStep 254815 = 382223) B382223
theorem B254843 : Blo 251819 254843 := bstep (se 1 (by rfl) ⟨191132, by rfl⟩ : syracuseStep 254843 = 382265) B382265
theorem B320431 : Blo 251819 320431 := bstep (se 1 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 320431 = 480647) B480647
theorem B254895 : Blo 251819 254895 := bstep (se 1 (by rfl) ⟨191171, by rfl⟩ : syracuseStep 254895 = 382343) B382343
theorem B254919 : Blo 251819 254919 := bstep (se 1 (by rfl) ⟨191189, by rfl⟩ : syracuseStep 254919 = 382379) B382379
theorem B254939 : Blo 251819 254939 := bstep (se 1 (by rfl) ⟨191204, by rfl⟩ : syracuseStep 254939 = 382409) B382409
theorem B287707 : Blo 251819 287707 := bstep (se 1 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 287707 = 431561) B431561
theorem B255015 : Blo 251819 255015 := bstep (se 1 (by rfl) ⟨191261, by rfl⟩ : syracuseStep 255015 = 382523) B382523
theorem B255055 : Blo 251819 255055 := bstep (se 1 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 255055 = 382583) B382583
theorem B255071 : Blo 251819 255071 := bstep (se 1 (by rfl) ⟨191303, by rfl⟩ : syracuseStep 255071 = 382607) B382607
theorem B255099 : Blo 251819 255099 := bstep (se 1 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 255099 = 382649) B382649
theorem B255151 : Blo 251819 255151 := bstep (se 1 (by rfl) ⟨191363, by rfl⟩ : syracuseStep 255151 = 382727) B382727
theorem B255175 : Blo 251819 255175 := bstep (se 1 (by rfl) ⟨191381, by rfl⟩ : syracuseStep 255175 = 382763) B382763
theorem B2876633 : Blo 251819 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B3073241 : Blo 251819 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B255195 : Blo 251819 255195 := bstep (se 1 (by rfl) ⟨191396, by rfl⟩ : syracuseStep 255195 = 382793) B382793
theorem B255271 : Blo 251819 255271 := bstep (se 1 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 255271 = 382907) B382907
theorem B7267643 : Blo 251819 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B255311 : Blo 251819 255311 := bstep (se 1 (by rfl) ⟨191483, by rfl⟩ : syracuseStep 255311 = 382967) B382967
theorem B255327 : Blo 251819 255327 := bstep (se 1 (by rfl) ⟨191495, by rfl⟩ : syracuseStep 255327 = 382991) B382991
theorem B255355 : Blo 251819 255355 := bstep (se 1 (by rfl) ⟨191516, by rfl⟩ : syracuseStep 255355 = 383033) B383033
theorem B3302819 : Blo 251819 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B255407 : Blo 251819 255407 := bstep (se 1 (by rfl) ⟨191555, by rfl⟩ : syracuseStep 255407 = 383111) B383111
theorem B255431 : Blo 251819 255431 := bstep (se 1 (by rfl) ⟨191573, by rfl⟩ : syracuseStep 255431 = 383147) B383147
theorem B255451 : Blo 251819 255451 := bstep (se 1 (by rfl) ⟨191588, by rfl⟩ : syracuseStep 255451 = 383177) B383177
theorem B255527 : Blo 251819 255527 := bstep (se 1 (by rfl) ⟨191645, by rfl⟩ : syracuseStep 255527 = 383291) B383291
theorem B255567 : Blo 251819 255567 := bstep (se 1 (by rfl) ⟨191675, by rfl⟩ : syracuseStep 255567 = 383351) B383351
theorem B255583 : Blo 251819 255583 := bstep (se 1 (by rfl) ⟨191687, by rfl⟩ : syracuseStep 255583 = 383375) B383375
theorem B255611 : Blo 251819 255611 := bstep (se 1 (by rfl) ⟨191708, by rfl⟩ : syracuseStep 255611 = 383417) B383417
theorem B255663 : Blo 251819 255663 := bstep (se 1 (by rfl) ⟨191747, by rfl⟩ : syracuseStep 255663 = 383495) B383495
theorem B255687 : Blo 251819 255687 := bstep (se 1 (by rfl) ⟨191765, by rfl⟩ : syracuseStep 255687 = 383531) B383531
theorem B255707 : Blo 251819 255707 := bstep (se 1 (by rfl) ⟨191780, by rfl⟩ : syracuseStep 255707 = 383561) B383561
theorem B255783 : Blo 251819 255783 := bstep (se 1 (by rfl) ⟨191837, by rfl⟩ : syracuseStep 255783 = 383675) B383675
theorem B321499 : Blo 251819 321499 := bstep (se 1 (by rfl) ⟨241124, by rfl⟩ : syracuseStep 321499 = 482249) B482249
theorem B911513 : Blo 251819 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B1927475 : Blo 251819 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B486059 : Blo 251819 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B486137 : Blo 251819 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B1436723 : Blo 251819 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1830059 : Blo 251819 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1076723 : Blo 251819 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1437223 : Blo 251819 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B290503 : Blo 251819 290503 := bstep (se 1 (by rfl) ⟨217877, by rfl⟩ : syracuseStep 290503 = 435755) B435755
theorem B683959 : Blo 251819 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B6582349 : Blo 251819 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B913979 : Blo 251819 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B2093627 : Blo 251819 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B1078123 : Blo 251819 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1635329 : Blo 251819 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B3339667 : Blo 251819 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B1734061 : Blo 251819 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B488999 : Blo 251819 488999 := bstep (se 1 (by rfl) ⟨366749, by rfl⟩ : syracuseStep 488999 = 733499) B733499
theorem B6715061 : Blo 251819 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B1636355 : Blo 251819 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B1275911 : Blo 251819 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B1276397 : Blo 251819 1276397 := bstep (se 3 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 1276397 = 478649) B478649
theorem B916559 : Blo 251819 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B818333 : Blo 251819 818333 := bstep (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) B306875
theorem B1080515 : Blo 251819 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B425209 : Blo 251819 425209 := bstep (se 2 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 425209 = 318907) B318907
theorem B1277207 : Blo 251819 1277207 := bstep (se 1 (by rfl) ⟨957905, by rfl⟩ : syracuseStep 1277207 = 1915811) B1915811
theorem B425479 : Blo 251819 425479 := bstep (se 1 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 425479 = 638219) B638219
theorem B851579 : Blo 251819 851579 := bstep (se 1 (by rfl) ⟨638684, by rfl⟩ : syracuseStep 851579 = 1277369) B1277369
theorem B1212043 : Blo 251819 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B851741 : Blo 251819 851741 := bstep (se 3 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 851741 = 319403) B319403
theorem B1638305 : Blo 251819 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B425911 : Blo 251819 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B15728717 : Blo 251819 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B2162807 : Blo 251819 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B15532195 : Blo 251819 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B360713 : Blo 251819 360713 := bstep (se 2 (by rfl) ⟨135267, by rfl⟩ : syracuseStep 360713 = 270535) B270535
theorem B688457 : Blo 251819 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B3277219 : Blo 251819 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B1933793 : Blo 251819 1933793 := bstep (se 2 (by rfl) ⟨725172, by rfl⟩ : syracuseStep 1933793 = 1450345) B1450345
theorem B918017 : Blo 251819 918017 := bstep (se 2 (by rfl) ⟨344256, by rfl⟩ : syracuseStep 918017 = 688513) B688513
theorem B426559 : Blo 251819 426559 := bstep (se 1 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 426559 = 639839) B639839
theorem B852551 : Blo 251819 852551 := bstep (se 1 (by rfl) ⟨639413, by rfl⟩ : syracuseStep 852551 = 1278827) B1278827
theorem B1082155 : Blo 251819 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B852983 : Blo 251819 852983 := bstep (se 1 (by rfl) ⟨639737, by rfl⟩ : syracuseStep 852983 = 1279475) B1279475
theorem B427241 : Blo 251819 427241 := bstep (se 2 (by rfl) ⟨160215, by rfl⟩ : syracuseStep 427241 = 320431) B320431
theorem B427295 : Blo 251819 427295 := bstep (se 1 (by rfl) ⟨320471, by rfl⟩ : syracuseStep 427295 = 640943) B640943
theorem B11044471 : Blo 251819 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B1279799 : Blo 251819 1279799 := bstep (se 1 (by rfl) ⟨959849, by rfl⟩ : syracuseStep 1279799 = 1919699) B1919699
theorem B853847 : Blo 251819 853847 := bstep (se 1 (by rfl) ⟨640385, by rfl⟩ : syracuseStep 853847 = 1280771) B1280771
theorem B1935251 : Blo 251819 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B1378255 : Blo 251819 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1280285 : Blo 251819 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B3541391 : Blo 251819 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B428665 : Blo 251819 428665 := bstep (se 2 (by rfl) ⟨160749, by rfl⟩ : syracuseStep 428665 = 321499) B321499
theorem B4360877 : Blo 251819 4360877 := bstep (se 3 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 4360877 = 1635329) B1635329
theorem B428719 : Blo 251819 428719 := bstep (se 1 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 428719 = 643079) B643079
theorem B854927 : Blo 251819 854927 := bstep (se 1 (by rfl) ⟨641195, by rfl⟩ : syracuseStep 854927 = 1282391) B1282391
theorem B691487 : Blo 251819 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B1216235 : Blo 251819 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B1085231 : Blo 251819 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B1380203 : Blo 251819 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B2330477 : Blo 251819 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B1445789 : Blo 251819 1445789 := bstep (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) B542171
theorem B1282067 : Blo 251819 1282067 := bstep (se 1 (by rfl) ⟨961550, by rfl⟩ : syracuseStep 1282067 = 1923101) B1923101
theorem B856169 : Blo 251819 856169 := bstep (se 2 (by rfl) ⟨321063, by rfl⟩ : syracuseStep 856169 = 642127) B642127
theorem B2592971 : Blo 251819 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B430427 : Blo 251819 430427 := bstep (se 1 (by rfl) ⟨322820, by rfl⟩ : syracuseStep 430427 = 645641) B645641
theorem B2363755 : Blo 251819 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B430447 : Blo 251819 430447 := bstep (se 1 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 430447 = 645671) B645671
theorem B9802133 : Blo 251819 9802133 := bstep (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) B459475
theorem B430663 : Blo 251819 430663 := bstep (se 1 (by rfl) ⟨322997, by rfl⟩ : syracuseStep 430663 = 645995) B645995
theorem B1446497 : Blo 251819 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B2724637 : Blo 251819 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B857033 : Blo 251819 857033 := bstep (se 2 (by rfl) ⟨321387, by rfl⟩ : syracuseStep 857033 = 642775) B642775
theorem B431095 : Blo 251819 431095 := bstep (se 1 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 431095 = 646643) B646643
theorem B857303 : Blo 251819 857303 := bstep (se 1 (by rfl) ⟨642977, by rfl⟩ : syracuseStep 857303 = 1285955) B1285955
theorem B431399 : Blo 251819 431399 := bstep (se 1 (by rfl) ⟨323549, by rfl⟩ : syracuseStep 431399 = 647099) B647099
theorem B2201879 : Blo 251819 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1939801 : Blo 251819 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B1841591 : Blo 251819 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1284983 : Blo 251819 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B4135799 : Blo 251819 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B728203 : Blo 251819 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B859355 : Blo 251819 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B269659 : Blo 251819 269659 := bstep (se 1 (by rfl) ⟨202244, by rfl⟩ : syracuseStep 269659 = 404489) B404489
theorem B1023329 : Blo 251819 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B957815 : Blo 251819 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B1220039 : Blo 251819 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1285793 : Blo 251819 1285793 := bstep (se 2 (by rfl) ⟨482172, by rfl⟩ : syracuseStep 1285793 = 964345) B964345
theorem B860219 : Blo 251819 860219 := bstep (se 1 (by rfl) ⟨645164, by rfl⟩ : syracuseStep 860219 = 1290329) B1290329
theorem B860489 : Blo 251819 860489 := bstep (se 2 (by rfl) ⟨322683, by rfl⟩ : syracuseStep 860489 = 645367) B645367
theorem B2073089 : Blo 251819 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B270911 : Blo 251819 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B1025257 : Blo 251819 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B1090903 : Blo 251819 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B1942937 : Blo 251819 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B1287737 : Blo 251819 1287737 := bstep (se 2 (by rfl) ⟨482901, by rfl⟩ : syracuseStep 1287737 = 965803) B965803
theorem B2631257 : Blo 251819 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B3679901 : Blo 251819 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B566945 : Blo 251819 566945 := bstep (se 2 (by rfl) ⟨212604, by rfl⟩ : syracuseStep 566945 = 425209) B425209
theorem B272359 : Blo 251819 272359 := bstep (se 1 (by rfl) ⟨204269, by rfl⟩ : syracuseStep 272359 = 408539) B408539
theorem B567305 : Blo 251819 567305 := bstep (se 2 (by rfl) ⟨212739, by rfl⟩ : syracuseStep 567305 = 425479) B425479
theorem B1616057 : Blo 251819 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B567719 : Blo 251819 567719 := bstep (se 1 (by rfl) ⟨425789, by rfl⟩ : syracuseStep 567719 = 851579) B851579
theorem B567827 : Blo 251819 567827 := bstep (se 1 (by rfl) ⟨425870, by rfl⟩ : syracuseStep 567827 = 851741) B851741
theorem B567881 : Blo 251819 567881 := bstep (se 2 (by rfl) ⟨212955, by rfl⟩ : syracuseStep 567881 = 425911) B425911
theorem B1092203 : Blo 251819 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B568295 : Blo 251819 568295 := bstep (se 1 (by rfl) ⟨426221, by rfl⟩ : syracuseStep 568295 = 852443) B852443
theorem B35105861 : Blo 251819 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B5024987 : Blo 251819 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B568673 : Blo 251819 568673 := bstep (se 2 (by rfl) ⟨213252, by rfl⟩ : syracuseStep 568673 = 426505) B426505
theorem B568763 : Blo 251819 568763 := bstep (se 1 (by rfl) ⟨426572, by rfl⟩ : syracuseStep 568763 = 853145) B853145
theorem B568889 : Blo 251819 568889 := bstep (se 2 (by rfl) ⟨213333, by rfl⟩ : syracuseStep 568889 = 426667) B426667
theorem B1289843 : Blo 251819 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B569555 : Blo 251819 569555 := bstep (se 1 (by rfl) ⟨427166, by rfl⟩ : syracuseStep 569555 = 854333) B854333
theorem B2732291 : Blo 251819 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B569609 : Blo 251819 569609 := bstep (se 2 (by rfl) ⟨213603, by rfl⟩ : syracuseStep 569609 = 427207) B427207
theorem B3649967 : Blo 251819 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B569825 : Blo 251819 569825 := bstep (se 2 (by rfl) ⟨213684, by rfl⟩ : syracuseStep 569825 = 427369) B427369
theorem B570131 : Blo 251819 570131 := bstep (se 1 (by rfl) ⟨427598, by rfl⟩ : syracuseStep 570131 = 855197) B855197
theorem B570491 : Blo 251819 570491 := bstep (se 1 (by rfl) ⟨427868, by rfl⟩ : syracuseStep 570491 = 855737) B855737
theorem B1291463 : Blo 251819 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B570617 : Blo 251819 570617 := bstep (se 2 (by rfl) ⟨213981, by rfl⟩ : syracuseStep 570617 = 427963) B427963
theorem B1291625 : Blo 251819 1291625 := bstep (se 2 (by rfl) ⟨484359, by rfl⟩ : syracuseStep 1291625 = 968719) B968719
theorem B570761 : Blo 251819 570761 := bstep (se 2 (by rfl) ⟨214035, by rfl⟩ : syracuseStep 570761 = 428071) B428071
theorem B734653 : Blo 251819 734653 := bstep (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) B275495
theorem B538105 : Blo 251819 538105 := bstep (se 2 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 538105 = 403579) B403579
theorem B407033 : Blo 251819 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B570887 : Blo 251819 570887 := bstep (se 1 (by rfl) ⟨428165, by rfl⟩ : syracuseStep 570887 = 856331) B856331
theorem B3683879 : Blo 251819 3683879 := bstep (se 1 (by rfl) ⟨2762909, by rfl⟩ : syracuseStep 3683879 = 5525819) B5525819
theorem B571067 : Blo 251819 571067 := bstep (se 1 (by rfl) ⟨428300, by rfl⟩ : syracuseStep 571067 = 856601) B856601
theorem B571193 : Blo 251819 571193 := bstep (se 2 (by rfl) ⟨214197, by rfl⟩ : syracuseStep 571193 = 428395) B428395
theorem B2176955 : Blo 251819 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B571823 : Blo 251819 571823 := bstep (se 1 (by rfl) ⟨428867, by rfl⟩ : syracuseStep 571823 = 857735) B857735
theorem B571859 : Blo 251819 571859 := bstep (se 1 (by rfl) ⟨428894, by rfl⟩ : syracuseStep 571859 = 857789) B857789
theorem B571967 : Blo 251819 571967 := bstep (se 1 (by rfl) ⟨428975, by rfl⟩ : syracuseStep 571967 = 857951) B857951
theorem B1456703 : Blo 251819 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B572075 : Blo 251819 572075 := bstep (se 1 (by rfl) ⟨429056, by rfl⟩ : syracuseStep 572075 = 858113) B858113
theorem B605099 : Blo 251819 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B637915 : Blo 251819 637915 := bstep (se 1 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 637915 = 956873) B956873
theorem B572615 : Blo 251819 572615 := bstep (se 1 (by rfl) ⟨429461, by rfl⟩ : syracuseStep 572615 = 858923) B858923
theorem B638239 : Blo 251819 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B572795 : Blo 251819 572795 := bstep (se 1 (by rfl) ⟨429596, by rfl⟩ : syracuseStep 572795 = 859193) B859193
theorem B1916297 : Blo 251819 1916297 := bstep (se 2 (by rfl) ⟨718611, by rfl⟩ : syracuseStep 1916297 = 1437223) B1437223
theorem B572921 : Blo 251819 572921 := bstep (se 2 (by rfl) ⟨214845, by rfl⟩ : syracuseStep 572921 = 429691) B429691
theorem B573011 : Blo 251819 573011 := bstep (se 1 (by rfl) ⟨429758, by rfl⟩ : syracuseStep 573011 = 859517) B859517
theorem B573191 : Blo 251819 573191 := bstep (se 1 (by rfl) ⟨429893, by rfl⟩ : syracuseStep 573191 = 859787) B859787
theorem B409391 : Blo 251819 409391 := bstep (se 1 (by rfl) ⟨307043, by rfl⟩ : syracuseStep 409391 = 614087) B614087
theorem B4636577 : Blo 251819 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B2473993 : Blo 251819 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B966761 : Blo 251819 966761 := bstep (se 2 (by rfl) ⟨362535, by rfl⟩ : syracuseStep 966761 = 725071) B725071
theorem B344359 : Blo 251819 344359 := bstep (se 1 (by rfl) ⟨258269, by rfl⟩ : syracuseStep 344359 = 516539) B516539
theorem B639323 : Blo 251819 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B573803 : Blo 251819 573803 := bstep (se 1 (by rfl) ⟨430352, by rfl⟩ : syracuseStep 573803 = 860705) B860705
theorem B573947 : Blo 251819 573947 := bstep (se 1 (by rfl) ⟨430460, by rfl⟩ : syracuseStep 573947 = 860921) B860921
theorem B1229363 : Blo 251819 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B574073 : Blo 251819 574073 := bstep (se 2 (by rfl) ⟨215277, by rfl⟩ : syracuseStep 574073 = 430555) B430555
theorem B574127 : Blo 251819 574127 := bstep (se 1 (by rfl) ⟨430595, by rfl⟩ : syracuseStep 574127 = 861191) B861191
theorem B574199 : Blo 251819 574199 := bstep (se 1 (by rfl) ⟨430649, by rfl⟩ : syracuseStep 574199 = 861299) B861299
theorem B1917755 : Blo 251819 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B2048827 : Blo 251819 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B574379 : Blo 251819 574379 := bstep (se 1 (by rfl) ⟨430784, by rfl⟩ : syracuseStep 574379 = 861569) B861569
theorem B377831 : Blo 251819 377831 := bstep (se 1 (by rfl) ⟨283373, by rfl⟩ : syracuseStep 377831 = 566747) B566747
theorem B9684035 : Blo 251819 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B378089 : Blo 251819 378089 := bstep (se 2 (by rfl) ⟨141783, by rfl⟩ : syracuseStep 378089 = 283567) B283567
theorem B836857 : Blo 251819 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B378143 : Blo 251819 378143 := bstep (se 1 (by rfl) ⟨283607, by rfl⟩ : syracuseStep 378143 = 567215) B567215
theorem B640295 : Blo 251819 640295 := bstep (se 1 (by rfl) ⟨480221, by rfl⟩ : syracuseStep 640295 = 960443) B960443
theorem B607675 : Blo 251819 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B378311 : Blo 251819 378311 := bstep (se 1 (by rfl) ⟨283733, by rfl⟩ : syracuseStep 378311 = 567467) B567467
theorem B574919 : Blo 251819 574919 := bstep (se 1 (by rfl) ⟨431189, by rfl⟩ : syracuseStep 574919 = 862379) B862379
theorem B4376051 : Blo 251819 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B542369 : Blo 251819 542369 := bstep (se 2 (by rfl) ⟨203388, by rfl⟩ : syracuseStep 542369 = 406777) B406777
theorem B1296157 : Blo 251819 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B378665 : Blo 251819 378665 := bstep (se 2 (by rfl) ⟨141999, by rfl⟩ : syracuseStep 378665 = 283999) B283999
theorem B378671 : Blo 251819 378671 := bstep (se 1 (by rfl) ⟨284003, by rfl⟩ : syracuseStep 378671 = 568007) B568007
theorem B575279 : Blo 251819 575279 := bstep (se 1 (by rfl) ⟨431459, by rfl⟩ : syracuseStep 575279 = 862919) B862919
theorem B2312081 : Blo 251819 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2607299 : Blo 251819 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B1362167 : Blo 251819 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B379145 : Blo 251819 379145 := bstep (se 2 (by rfl) ⟨142179, by rfl⟩ : syracuseStep 379145 = 284359) B284359
theorem B1296751 : Blo 251819 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B379247 : Blo 251819 379247 := bstep (se 1 (by rfl) ⟨284435, by rfl⟩ : syracuseStep 379247 = 568871) B568871
theorem B379463 : Blo 251819 379463 := bstep (se 1 (by rfl) ⟨284597, by rfl⟩ : syracuseStep 379463 = 569195) B569195
theorem B379499 : Blo 251819 379499 := bstep (se 1 (by rfl) ⟨284624, by rfl⟩ : syracuseStep 379499 = 569249) B569249
theorem B641783 : Blo 251819 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B379727 : Blo 251819 379727 := bstep (se 1 (by rfl) ⟨284795, by rfl⟩ : syracuseStep 379727 = 569591) B569591
theorem B609319 : Blo 251819 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B1395751 : Blo 251819 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B380123 : Blo 251819 380123 := bstep (se 1 (by rfl) ⟨285092, by rfl⟩ : syracuseStep 380123 = 570185) B570185
theorem B642401 : Blo 251819 642401 := bstep (se 2 (by rfl) ⟨240900, by rfl⟩ : syracuseStep 642401 = 481801) B481801
theorem B380297 : Blo 251819 380297 := bstep (se 2 (by rfl) ⟨142611, by rfl⟩ : syracuseStep 380297 = 285223) B285223
theorem B3264097 : Blo 251819 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B380651 : Blo 251819 380651 := bstep (se 1 (by rfl) ⟨285488, by rfl⟩ : syracuseStep 380651 = 570977) B570977
theorem B4476707 : Blo 251819 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B380879 : Blo 251819 380879 := bstep (se 1 (by rfl) ⟨285659, by rfl⟩ : syracuseStep 380879 = 571319) B571319
theorem B2740553 : Blo 251819 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B381275 : Blo 251819 381275 := bstep (se 1 (by rfl) ⟨285956, by rfl⟩ : syracuseStep 381275 = 571913) B571913
theorem B381503 : Blo 251819 381503 := bstep (se 1 (by rfl) ⟨286127, by rfl⟩ : syracuseStep 381503 = 572255) B572255
theorem B1036871 : Blo 251819 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B381623 : Blo 251819 381623 := bstep (se 1 (by rfl) ⟨286217, by rfl⟩ : syracuseStep 381623 = 572435) B572435
theorem B611039 : Blo 251819 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B643859 : Blo 251819 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B545555 : Blo 251819 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B578459 : Blo 251819 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B381851 : Blo 251819 381851 := bstep (se 1 (by rfl) ⟨286388, by rfl⟩ : syracuseStep 381851 = 572777) B572777
theorem B644071 : Blo 251819 644071 := bstep (se 1 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 644071 = 966107) B966107
theorem B5002397 : Blo 251819 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B644345 : Blo 251819 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B382247 : Blo 251819 382247 := bstep (se 1 (by rfl) ⟨286685, by rfl⟩ : syracuseStep 382247 = 573371) B573371
theorem B382331 : Blo 251819 382331 := bstep (se 1 (by rfl) ⟨286748, by rfl⟩ : syracuseStep 382331 = 573497) B573497
theorem B284071 : Blo 251819 284071 := bstep (se 1 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 284071 = 426107) B426107
theorem B382457 : Blo 251819 382457 := bstep (se 2 (by rfl) ⟨143421, by rfl⟩ : syracuseStep 382457 = 286843) B286843
theorem B382559 : Blo 251819 382559 := bstep (se 1 (by rfl) ⟨286919, by rfl⟩ : syracuseStep 382559 = 573839) B573839
theorem B481079 : Blo 251819 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B382775 : Blo 251819 382775 := bstep (se 1 (by rfl) ⟨287081, by rfl⟩ : syracuseStep 382775 = 574163) B574163
theorem B644993 : Blo 251819 644993 := bstep (se 2 (by rfl) ⟨241872, by rfl⟩ : syracuseStep 644993 = 483745) B483745
theorem B251855 : Blo 251819 251855 := bstep (se 1 (by rfl) ⟨188891, by rfl⟩ : syracuseStep 251855 = 377783) B377783
theorem B481231 : Blo 251819 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B251879 : Blo 251819 251879 := bstep (se 1 (by rfl) ⟨188909, by rfl⟩ : syracuseStep 251879 = 377819) B377819
theorem B284647 : Blo 251819 284647 := bstep (se 1 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 284647 = 426971) B426971
theorem B383081 : Blo 251819 383081 := bstep (se 2 (by rfl) ⟨143655, by rfl⟩ : syracuseStep 383081 = 287311) B287311
theorem B252191 : Blo 251819 252191 := bstep (se 1 (by rfl) ⟨189143, by rfl⟩ : syracuseStep 252191 = 378287) B378287
theorem B252251 : Blo 251819 252251 := bstep (se 1 (by rfl) ⟨189188, by rfl⟩ : syracuseStep 252251 = 378377) B378377
theorem B252271 : Blo 251819 252271 := bstep (se 1 (by rfl) ⟨189203, by rfl⟩ : syracuseStep 252271 = 378407) B378407
theorem B252327 : Blo 251819 252327 := bstep (se 1 (by rfl) ⟨189245, by rfl⟩ : syracuseStep 252327 = 378491) B378491
theorem B383399 : Blo 251819 383399 := bstep (se 1 (by rfl) ⟨287549, by rfl⟩ : syracuseStep 383399 = 575099) B575099
theorem B252411 : Blo 251819 252411 := bstep (se 1 (by rfl) ⟨189308, by rfl⟩ : syracuseStep 252411 = 378617) B378617
theorem B383483 : Blo 251819 383483 := bstep (se 1 (by rfl) ⟨287612, by rfl⟩ : syracuseStep 383483 = 575225) B575225
theorem B252479 : Blo 251819 252479 := bstep (se 1 (by rfl) ⟨189359, by rfl⟩ : syracuseStep 252479 = 378719) B378719
theorem B252487 : Blo 251819 252487 := bstep (se 1 (by rfl) ⟨189365, by rfl⟩ : syracuseStep 252487 = 378731) B378731
theorem B383609 : Blo 251819 383609 := bstep (se 2 (by rfl) ⟨143853, by rfl⟩ : syracuseStep 383609 = 287707) B287707
theorem B645803 : Blo 251819 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B383663 : Blo 251819 383663 := bstep (se 1 (by rfl) ⟨287747, by rfl⟩ : syracuseStep 383663 = 575495) B575495
theorem B252639 : Blo 251819 252639 := bstep (se 1 (by rfl) ⟨189479, by rfl⟩ : syracuseStep 252639 = 378959) B378959
theorem B383711 : Blo 251819 383711 := bstep (se 1 (by rfl) ⟨287783, by rfl⟩ : syracuseStep 383711 = 575567) B575567
theorem B252719 : Blo 251819 252719 := bstep (se 1 (by rfl) ⟨189539, by rfl⟩ : syracuseStep 252719 = 379079) B379079
theorem B252827 : Blo 251819 252827 := bstep (se 1 (by rfl) ⟨189620, by rfl⟩ : syracuseStep 252827 = 379241) B379241
theorem B482203 : Blo 251819 482203 := bstep (se 1 (by rfl) ⟨361652, by rfl⟩ : syracuseStep 482203 = 723305) B723305
theorem B252879 : Blo 251819 252879 := bstep (se 1 (by rfl) ⟨189659, by rfl⟩ : syracuseStep 252879 = 379319) B379319
theorem B252903 : Blo 251819 252903 := bstep (se 1 (by rfl) ⟨189677, by rfl⟩ : syracuseStep 252903 = 379355) B379355
theorem B613499 : Blo 251819 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B1105085 : Blo 251819 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B482537 : Blo 251819 482537 := bstep (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) B361903
theorem B253215 : Blo 251819 253215 := bstep (se 1 (by rfl) ⟨189911, by rfl⟩ : syracuseStep 253215 = 379823) B379823
theorem B482591 : Blo 251819 482591 := bstep (se 1 (by rfl) ⟨361943, by rfl⟩ : syracuseStep 482591 = 723887) B723887
theorem B318811 : Blo 251819 318811 := bstep (se 1 (by rfl) ⟨239108, by rfl⟩ : syracuseStep 318811 = 478217) B478217
theorem B253275 : Blo 251819 253275 := bstep (se 1 (by rfl) ⟨189956, by rfl⟩ : syracuseStep 253275 = 379913) B379913
theorem B253295 : Blo 251819 253295 := bstep (se 1 (by rfl) ⟨189971, by rfl⟩ : syracuseStep 253295 = 379943) B379943
theorem B253351 : Blo 251819 253351 := bstep (se 1 (by rfl) ⟨190013, by rfl⟩ : syracuseStep 253351 = 380027) B380027
theorem B253435 : Blo 251819 253435 := bstep (se 1 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 253435 = 380153) B380153
theorem B646663 : Blo 251819 646663 := bstep (se 1 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 646663 = 969995) B969995
theorem B253503 : Blo 251819 253503 := bstep (se 1 (by rfl) ⟨190127, by rfl⟩ : syracuseStep 253503 = 380255) B380255
theorem B253511 : Blo 251819 253511 := bstep (se 1 (by rfl) ⟨190133, by rfl⟩ : syracuseStep 253511 = 380267) B380267
theorem B286303 : Blo 251819 286303 := bstep (se 1 (by rfl) ⟨214727, by rfl⟩ : syracuseStep 286303 = 429455) B429455
theorem B253663 : Blo 251819 253663 := bstep (se 1 (by rfl) ⟨190247, by rfl⟩ : syracuseStep 253663 = 380495) B380495
theorem B253743 : Blo 251819 253743 := bstep (se 1 (by rfl) ⟨190307, by rfl⟩ : syracuseStep 253743 = 380615) B380615
theorem B646967 : Blo 251819 646967 := bstep (se 1 (by rfl) ⟨485225, by rfl⟩ : syracuseStep 646967 = 970451) B970451
theorem B253851 : Blo 251819 253851 := bstep (se 1 (by rfl) ⟨190388, by rfl⟩ : syracuseStep 253851 = 380777) B380777
theorem B253903 : Blo 251819 253903 := bstep (se 1 (by rfl) ⟨190427, by rfl⟩ : syracuseStep 253903 = 380855) B380855
theorem B253927 : Blo 251819 253927 := bstep (se 1 (by rfl) ⟨190445, by rfl⟩ : syracuseStep 253927 = 380891) B380891
theorem B254239 : Blo 251819 254239 := bstep (se 1 (by rfl) ⟨190679, by rfl⟩ : syracuseStep 254239 = 381359) B381359
theorem B319783 : Blo 251819 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B4645181 : Blo 251819 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B254299 : Blo 251819 254299 := bstep (se 1 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 254299 = 381449) B381449
theorem B254319 : Blo 251819 254319 := bstep (se 1 (by rfl) ⟨190739, by rfl⟩ : syracuseStep 254319 = 381479) B381479
theorem B254375 : Blo 251819 254375 := bstep (se 1 (by rfl) ⟨190781, by rfl⟩ : syracuseStep 254375 = 381563) B381563
theorem B582071 : Blo 251819 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B6578633 : Blo 251819 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B254459 : Blo 251819 254459 := bstep (se 1 (by rfl) ⟨190844, by rfl⟩ : syracuseStep 254459 = 381689) B381689
theorem B254527 : Blo 251819 254527 := bstep (se 1 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 254527 = 381791) B381791
theorem B254535 : Blo 251819 254535 := bstep (se 1 (by rfl) ⟨190901, by rfl⟩ : syracuseStep 254535 = 381803) B381803
theorem B320107 : Blo 251819 320107 := bstep (se 1 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 320107 = 480161) B480161
theorem B254687 : Blo 251819 254687 := bstep (se 1 (by rfl) ⟨191015, by rfl⟩ : syracuseStep 254687 = 382031) B382031
theorem B287455 : Blo 251819 287455 := bstep (se 1 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 287455 = 431183) B431183
theorem B254767 : Blo 251819 254767 := bstep (se 1 (by rfl) ⟨191075, by rfl⟩ : syracuseStep 254767 = 382151) B382151
theorem B254875 : Blo 251819 254875 := bstep (se 1 (by rfl) ⟨191156, by rfl⟩ : syracuseStep 254875 = 382313) B382313
theorem B254927 : Blo 251819 254927 := bstep (se 1 (by rfl) ⟨191195, by rfl⟩ : syracuseStep 254927 = 382391) B382391
theorem B254951 : Blo 251819 254951 := bstep (se 1 (by rfl) ⟨191213, by rfl⟩ : syracuseStep 254951 = 382427) B382427
theorem B1827983 : Blo 251819 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B255263 : Blo 251819 255263 := bstep (se 1 (by rfl) ⟨191447, by rfl⟩ : syracuseStep 255263 = 382895) B382895
theorem B255323 : Blo 251819 255323 := bstep (se 1 (by rfl) ⟨191492, by rfl⟩ : syracuseStep 255323 = 382985) B382985
theorem B255343 : Blo 251819 255343 := bstep (se 1 (by rfl) ⟨191507, by rfl⟩ : syracuseStep 255343 = 383015) B383015
theorem B255399 : Blo 251819 255399 := bstep (se 1 (by rfl) ⟨191549, by rfl⟩ : syracuseStep 255399 = 383099) B383099
theorem B255483 : Blo 251819 255483 := bstep (se 1 (by rfl) ⟨191612, by rfl⟩ : syracuseStep 255483 = 383225) B383225
theorem B255551 : Blo 251819 255551 := bstep (se 1 (by rfl) ⟨191663, by rfl⟩ : syracuseStep 255551 = 383327) B383327
theorem B255559 : Blo 251819 255559 := bstep (se 1 (by rfl) ⟨191669, by rfl⟩ : syracuseStep 255559 = 383339) B383339
theorem B255711 : Blo 251819 255711 := bstep (se 1 (by rfl) ⟨191783, by rfl⟩ : syracuseStep 255711 = 383567) B383567
theorem B255791 : Blo 251819 255791 := bstep (se 1 (by rfl) ⟨191843, by rfl⟩ : syracuseStep 255791 = 383687) B383687
theorem B1926989 : Blo 251819 1926989 := bstep (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) B722621
theorem B1370297 : Blo 251819 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B387337 : Blo 251819 387337 := bstep (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) B290503
theorem B321823 : Blo 251819 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B4680179 : Blo 251819 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B911945 : Blo 251819 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B4877009 : Blo 251819 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B10414871 : Blo 251819 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B2321423 : Blo 251819 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B4845095 : Blo 251819 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437497 : Blo 251819 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B815129 : Blo 251819 815129 := bstep (se 2 (by rfl) ⟨305673, by rfl⟩ : syracuseStep 815129 = 611347) B611347
theorem B1929419 : Blo 251819 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B324091 : Blo 251819 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B4452889 : Blo 251819 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B3469873 : Blo 251819 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B685019 : Blo 251819 685019 := bstep (se 1 (by rfl) ⟨513764, by rfl⟩ : syracuseStep 685019 = 1027529) B1027529
theorem B717815 : Blo 251819 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B1078397 : Blo 251819 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B456073 : Blo 251819 456073 := bstep (se 2 (by rfl) ⟨171027, by rfl⟩ : syracuseStep 456073 = 342055) B342055
theorem B1275425 : Blo 251819 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B719113 : Blo 251819 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B325999 : Blo 251819 325999 := bstep (se 1 (by rfl) ⟨244499, by rfl⟩ : syracuseStep 325999 = 488999) B488999
theorem B293371 : Blo 251819 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B1931849 : Blo 251819 1931849 := bstep (se 2 (by rfl) ⟨724443, by rfl⟩ : syracuseStep 1931849 = 1448887) B1448887
theorem B850607 : Blo 251819 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B818075 : Blo 251819 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B2456507 : Blo 251819 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B850931 : Blo 251819 850931 := bstep (se 1 (by rfl) ⟨638198, by rfl⟩ : syracuseStep 850931 = 1276397) B1276397
theorem B687095 : Blo 251819 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B1211507 : Blo 251819 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B720343 : Blo 251819 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B851471 : Blo 251819 851471 := bstep (se 1 (by rfl) ⟨638603, by rfl⟩ : syracuseStep 851471 = 1277207) B1277207
theorem B1080857 : Blo 251819 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B425567 : Blo 251819 425567 := bstep (se 1 (by rfl) ⟨319175, by rfl⟩ : syracuseStep 425567 = 638351) B638351
theorem B818849 : Blo 251819 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B425783 : Blo 251819 425783 := bstep (se 1 (by rfl) ⟨319337, by rfl⟩ : syracuseStep 425783 = 638675) B638675
theorem B720697 : Blo 251819 720697 := bstep (se 2 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 720697 = 540523) B540523
theorem B1441597 : Blo 251819 1441597 := bstep (se 3 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 1441597 = 540599) B540599
theorem B10485811 : Blo 251819 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B1441871 : Blo 251819 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B20709593 : Blo 251819 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B426215 : Blo 251819 426215 := bstep (se 1 (by rfl) ⟨319661, by rfl⟩ : syracuseStep 426215 = 639323) B639323
theorem B819575 : Blo 251819 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B426377 : Blo 251819 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B459145 : Blo 251819 459145 := bstep (se 2 (by rfl) ⟨172179, by rfl⟩ : syracuseStep 459145 = 344359) B344359
theorem B1278503 : Blo 251819 1278503 := bstep (se 1 (by rfl) ⟨958877, by rfl⟩ : syracuseStep 1278503 = 1917755) B1917755
theorem B6456023 : Blo 251819 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B426809 : Blo 251819 426809 := bstep (se 2 (by rfl) ⟨160053, by rfl⟩ : syracuseStep 426809 = 320107) B320107
theorem B1835885 : Blo 251819 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B426863 : Blo 251819 426863 := bstep (se 1 (by rfl) ⟨320147, by rfl⟩ : syracuseStep 426863 = 640295) B640295
theorem B2917367 : Blo 251819 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B1442873 : Blo 251819 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B361579 : Blo 251819 361579 := bstep (se 1 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 361579 = 542369) B542369
theorem B853199 : Blo 251819 853199 := bstep (se 1 (by rfl) ⟨639899, by rfl⟩ : syracuseStep 853199 = 1279799) B1279799
theorem B1541387 : Blo 251819 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1738199 : Blo 251819 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B722429 : Blo 251819 722429 := bstep (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) B270911
theorem B853523 : Blo 251819 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B2360927 : Blo 251819 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B427855 : Blo 251819 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B460991 : Blo 251819 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B428267 : Blo 251819 428267 := bstep (se 1 (by rfl) ⟨321200, by rfl⟩ : syracuseStep 428267 = 642401) B642401
theorem B1542557 : Blo 251819 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B2984471 : Blo 251819 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B723487 : Blo 251819 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B920135 : Blo 251819 920135 := bstep (se 1 (by rfl) ⟨690101, by rfl⟩ : syracuseStep 920135 = 1380203) B1380203
theorem B1837673 : Blo 251819 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B363145 : Blo 251819 363145 := bstep (se 2 (by rfl) ⟨136179, by rfl⟩ : syracuseStep 363145 = 272359) B272359
theorem B854711 : Blo 251819 854711 := bstep (se 1 (by rfl) ⟨641033, by rfl⟩ : syracuseStep 854711 = 1282067) B1282067
theorem B429097 : Blo 251819 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B691247 : Blo 251819 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B429239 : Blo 251819 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B363703 : Blo 251819 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B429563 : Blo 251819 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B429995 : Blo 251819 429995 := bstep (se 1 (by rfl) ⟨322496, by rfl⟩ : syracuseStep 429995 = 644993) B644993
theorem B430535 : Blo 251819 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B856655 : Blo 251819 856655 := bstep (se 1 (by rfl) ⟨642491, by rfl⟩ : syracuseStep 856655 = 1284983) B1284983
theorem B2757199 : Blo 251819 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B1282877 : Blo 251819 1282877 := bstep (se 3 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 1282877 = 481079) B481079
theorem B857195 : Blo 251819 857195 := bstep (se 1 (by rfl) ⟨642896, by rfl⟩ : syracuseStep 857195 = 1285793) B1285793
theorem B431311 : Blo 251819 431311 := bstep (se 1 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 431311 = 646967) B646967
theorem B1382059 : Blo 251819 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B3151673 : Blo 251819 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B432121 : Blo 251819 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B5937185 : Blo 251819 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B4626497 : Blo 251819 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B1218655 : Blo 251819 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B858491 : Blo 251819 858491 := bstep (se 1 (by rfl) ⟨643868, by rfl⟩ : syracuseStep 858491 = 1287737) B1287737
theorem B1284659 : Blo 251819 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B4463237 : Blo 251819 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B858761 : Blo 251819 858761 := bstep (se 2 (by rfl) ⟨322035, by rfl⟩ : syracuseStep 858761 = 644071) B644071
theorem B2431853 : Blo 251819 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B3120119 : Blo 251819 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B728135 : Blo 251819 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B3251339 : Blo 251819 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B1547615 : Blo 251819 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B23403907 : Blo 251819 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B2432389 : Blo 251819 2432389 := bstep (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) B456073
theorem B3349991 : Blo 251819 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B859895 : Blo 251819 859895 := bstep (se 1 (by rfl) ⟨644921, by rfl⟩ : syracuseStep 859895 = 1289843) B1289843
theorem B958331 : Blo 251819 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B1286279 : Blo 251819 1286279 := bstep (se 1 (by rfl) ⟨964709, by rfl⟩ : syracuseStep 1286279 = 1929419) B1929419
theorem B2433311 : Blo 251819 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B958817 : Blo 251819 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B434665 : Blo 251819 434665 := bstep (se 2 (by rfl) ⟨162999, by rfl⟩ : syracuseStep 434665 = 325999) B325999
theorem B1286765 : Blo 251819 1286765 := bstep (se 3 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 1286765 = 482537) B482537
theorem B860975 : Blo 251819 860975 := bstep (se 1 (by rfl) ⟨645731, by rfl⟩ : syracuseStep 860975 = 1291463) B1291463
theorem B861083 : Blo 251819 861083 := bstep (se 1 (by rfl) ⟨645812, by rfl⟩ : syracuseStep 861083 = 1291625) B1291625
theorem B271355 : Blo 251819 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B1451303 : Blo 251819 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B1287899 : Blo 251819 1287899 := bstep (se 1 (by rfl) ⟨965924, by rfl⟩ : syracuseStep 1287899 = 1931849) B1931849
theorem B567071 : Blo 251819 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B403399 : Blo 251819 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B960457 : Blo 251819 960457 := bstep (se 2 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 960457 = 720343) B720343
theorem B567287 : Blo 251819 567287 := bstep (se 1 (by rfl) ⟨425465, by rfl⟩ : syracuseStep 567287 = 850931) B850931
theorem B862217 : Blo 251819 862217 := bstep (se 2 (by rfl) ⟨323331, by rfl⟩ : syracuseStep 862217 = 646663) B646663
theorem B567647 : Blo 251819 567647 := bstep (se 1 (by rfl) ⟨425735, by rfl⟩ : syracuseStep 567647 = 851471) B851471
theorem B960929 : Blo 251819 960929 := bstep (se 2 (by rfl) ⟨360348, by rfl⟩ : syracuseStep 960929 = 720697) B720697
theorem B272927 : Blo 251819 272927 := bstep (se 1 (by rfl) ⟨204695, by rfl⟩ : syracuseStep 272927 = 409391) B409391
theorem B3091051 : Blo 251819 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B1289195 : Blo 251819 1289195 := bstep (se 1 (by rfl) ⟨966896, by rfl⟩ : syracuseStep 1289195 = 1933793) B1933793
theorem B568367 : Blo 251819 568367 := bstep (se 1 (by rfl) ⟨426275, by rfl⟩ : syracuseStep 568367 = 852551) B852551
theorem B4369625 : Blo 251819 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B568655 : Blo 251819 568655 := bstep (se 1 (by rfl) ⟨426491, by rfl⟩ : syracuseStep 568655 = 852983) B852983
theorem B961901 : Blo 251819 961901 := bstep (se 3 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 961901 = 360713) B360713
theorem B568745 : Blo 251819 568745 := bstep (se 2 (by rfl) ⟨213279, by rfl⟩ : syracuseStep 568745 = 426559) B426559
theorem B2731769 : Blo 251819 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B569231 : Blo 251819 569231 := bstep (se 1 (by rfl) ⟨426923, by rfl⟩ : syracuseStep 569231 = 853847) B853847
theorem B1290167 : Blo 251819 1290167 := bstep (se 1 (by rfl) ⟨967625, by rfl⟩ : syracuseStep 1290167 = 1935251) B1935251
theorem B1454537 : Blo 251819 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B569951 : Blo 251819 569951 := bstep (se 1 (by rfl) ⟨427463, by rfl⟩ : syracuseStep 569951 = 854927) B854927
theorem B14725961 : Blo 251819 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B1553651 : Blo 251819 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B963859 : Blo 251819 963859 := bstep (se 1 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 963859 = 1445789) B1445789
theorem B570779 : Blo 251819 570779 := bstep (se 1 (by rfl) ⟨428084, by rfl⟩ : syracuseStep 570779 = 856169) B856169
theorem B6534755 : Blo 251819 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B964331 : Blo 251819 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B407359 : Blo 251819 407359 := bstep (se 1 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 407359 = 611039) B611039
theorem B571355 : Blo 251819 571355 := bstep (se 1 (by rfl) ⟨428516, by rfl⟩ : syracuseStep 571355 = 857033) B857033
theorem B571535 : Blo 251819 571535 := bstep (se 1 (by rfl) ⟨428651, by rfl⟩ : syracuseStep 571535 = 857303) B857303
theorem B571553 : Blo 251819 571553 := bstep (se 2 (by rfl) ⟨214332, by rfl⟩ : syracuseStep 571553 = 428665) B428665
theorem B571625 : Blo 251819 571625 := bstep (se 2 (by rfl) ⟨214359, by rfl⟩ : syracuseStep 571625 = 428719) B428719
theorem B1227727 : Blo 251819 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B6208757 : Blo 251819 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B736723 : Blo 251819 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B572903 : Blo 251819 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B638543 : Blo 251819 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B573479 : Blo 251819 573479 := bstep (se 1 (by rfl) ⟨430109, by rfl⟩ : syracuseStep 573479 = 860219) B860219
theorem B3096787 : Blo 251819 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B573659 : Blo 251819 573659 := bstep (se 1 (by rfl) ⟨430244, by rfl⟩ : syracuseStep 573659 = 860489) B860489
theorem B573929 : Blo 251819 573929 := bstep (se 2 (by rfl) ⟨215223, by rfl⟩ : syracuseStep 573929 = 430447) B430447
theorem B574217 : Blo 251819 574217 := bstep (se 2 (by rfl) ⟨215331, by rfl⟩ : syracuseStep 574217 = 430663) B430663
theorem B1295291 : Blo 251819 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1754171 : Blo 251819 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B377963 : Blo 251819 377963 := bstep (se 1 (by rfl) ⟨283472, by rfl⟩ : syracuseStep 377963 = 566945) B566945
theorem B574793 : Blo 251819 574793 := bstep (se 2 (by rfl) ⟨215547, by rfl⟩ : syracuseStep 574793 = 431095) B431095
theorem B378203 : Blo 251819 378203 := bstep (se 1 (by rfl) ⟨283652, by rfl⟩ : syracuseStep 378203 = 567305) B567305
theorem B378479 : Blo 251819 378479 := bstep (se 1 (by rfl) ⟨283859, by rfl⟩ : syracuseStep 378479 = 567719) B567719
theorem B378551 : Blo 251819 378551 := bstep (se 1 (by rfl) ⟨283913, by rfl⟩ : syracuseStep 378551 = 567827) B567827
theorem B378587 : Blo 251819 378587 := bstep (se 1 (by rfl) ⟨283940, by rfl⟩ : syracuseStep 378587 = 567881) B567881
theorem B378761 : Blo 251819 378761 := bstep (se 2 (by rfl) ⟨142035, by rfl⟩ : syracuseStep 378761 = 284071) B284071
theorem B378863 : Blo 251819 378863 := bstep (se 1 (by rfl) ⟨284147, by rfl⟩ : syracuseStep 378863 = 568295) B568295
theorem B379115 : Blo 251819 379115 := bstep (se 1 (by rfl) ⟨284336, by rfl⟩ : syracuseStep 379115 = 568673) B568673
theorem B379175 : Blo 251819 379175 := bstep (se 1 (by rfl) ⟨284381, by rfl⟩ : syracuseStep 379175 = 568763) B568763
theorem B3230063 : Blo 251819 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B379259 : Blo 251819 379259 := bstep (se 1 (by rfl) ⟨284444, by rfl⟩ : syracuseStep 379259 = 568889) B568889
theorem B641641 : Blo 251819 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B379529 : Blo 251819 379529 := bstep (se 2 (by rfl) ⟨142323, by rfl⟩ : syracuseStep 379529 = 284647) B284647
theorem B543419 : Blo 251819 543419 := bstep (se 1 (by rfl) ⟨407564, by rfl⟩ : syracuseStep 543419 = 815129) B815129
theorem B379703 : Blo 251819 379703 := bstep (se 1 (by rfl) ⟨284777, by rfl⟩ : syracuseStep 379703 = 569555) B569555
theorem B1821527 : Blo 251819 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B379739 : Blo 251819 379739 := bstep (se 1 (by rfl) ⟨284804, by rfl⟩ : syracuseStep 379739 = 569609) B569609
theorem B379883 : Blo 251819 379883 := bstep (se 1 (by rfl) ⟨284912, by rfl⟩ : syracuseStep 379883 = 569825) B569825
theorem B380087 : Blo 251819 380087 := bstep (se 1 (by rfl) ⟨285065, by rfl⟩ : syracuseStep 380087 = 570131) B570131
theorem B478543 : Blo 251819 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B380327 : Blo 251819 380327 := bstep (se 1 (by rfl) ⟨285245, by rfl⟩ : syracuseStep 380327 = 570491) B570491
theorem B380411 : Blo 251819 380411 := bstep (se 1 (by rfl) ⟨285308, by rfl⟩ : syracuseStep 380411 = 570617) B570617
theorem B380507 : Blo 251819 380507 := bstep (se 1 (by rfl) ⟨285380, by rfl⟩ : syracuseStep 380507 = 570761) B570761
theorem B380591 : Blo 251819 380591 := bstep (se 1 (by rfl) ⟨285443, by rfl⟩ : syracuseStep 380591 = 570887) B570887
theorem B380711 : Blo 251819 380711 := bstep (se 1 (by rfl) ⟨285533, by rfl⟩ : syracuseStep 380711 = 571067) B571067
theorem B642937 : Blo 251819 642937 := bstep (se 2 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 642937 = 482203) B482203
theorem B380795 : Blo 251819 380795 := bstep (se 1 (by rfl) ⟨285596, by rfl⟩ : syracuseStep 380795 = 571193) B571193
theorem B970937 : Blo 251819 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B381215 : Blo 251819 381215 := bstep (se 1 (by rfl) ⟨285911, by rfl⟩ : syracuseStep 381215 = 571823) B571823
theorem B381239 : Blo 251819 381239 := bstep (se 1 (by rfl) ⟨285929, by rfl⟩ : syracuseStep 381239 = 571859) B571859
theorem B381311 : Blo 251819 381311 := bstep (se 1 (by rfl) ⟨285983, by rfl⟩ : syracuseStep 381311 = 571967) B571967
theorem B971135 : Blo 251819 971135 := bstep (se 1 (by rfl) ⟨728351, by rfl⟩ : syracuseStep 971135 = 1456703) B1456703
theorem B2183597 : Blo 251819 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B381383 : Blo 251819 381383 := bstep (se 1 (by rfl) ⟨286037, by rfl⟩ : syracuseStep 381383 = 572075) B572075
theorem B545383 : Blo 251819 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B807671 : Blo 251819 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B381737 : Blo 251819 381737 := bstep (se 2 (by rfl) ⟨143151, by rfl⟩ : syracuseStep 381737 = 286303) B286303
theorem B381743 : Blo 251819 381743 := bstep (se 1 (by rfl) ⟨286307, by rfl⟩ : syracuseStep 381743 = 572615) B572615
theorem B381863 : Blo 251819 381863 := bstep (se 1 (by rfl) ⟨286397, by rfl⟩ : syracuseStep 381863 = 572795) B572795
theorem B381947 : Blo 251819 381947 := bstep (se 1 (by rfl) ⟨286460, by rfl⟩ : syracuseStep 381947 = 572921) B572921
theorem B382007 : Blo 251819 382007 := bstep (se 1 (by rfl) ⟨286505, by rfl⟩ : syracuseStep 382007 = 573011) B573011
theorem B283711 : Blo 251819 283711 := bstep (se 1 (by rfl) ⟨212783, by rfl⟩ : syracuseStep 283711 = 425567) B425567
theorem B1922129 : Blo 251819 1922129 := bstep (se 2 (by rfl) ⟨720798, by rfl⟩ : syracuseStep 1922129 = 1441597) B1441597
theorem B382127 : Blo 251819 382127 := bstep (se 1 (by rfl) ⟨286595, by rfl⟩ : syracuseStep 382127 = 573191) B573191
theorem B283855 : Blo 251819 283855 := bstep (se 1 (by rfl) ⟨212891, by rfl⟩ : syracuseStep 283855 = 425783) B425783
theorem B3298657 : Blo 251819 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B644507 : Blo 251819 644507 := bstep (se 1 (by rfl) ⟨483380, by rfl⟩ : syracuseStep 644507 = 966761) B966761
theorem B382535 : Blo 251819 382535 := bstep (se 1 (by rfl) ⟨286901, by rfl⟩ : syracuseStep 382535 = 573803) B573803
theorem B382631 : Blo 251819 382631 := bstep (se 1 (by rfl) ⟨286973, by rfl⟩ : syracuseStep 382631 = 573947) B573947
theorem B612011 : Blo 251819 612011 := bstep (se 1 (by rfl) ⟨459008, by rfl⟩ : syracuseStep 612011 = 918017) B918017
theorem B382715 : Blo 251819 382715 := bstep (se 1 (by rfl) ⟨287036, by rfl⟩ : syracuseStep 382715 = 574073) B574073
theorem B382751 : Blo 251819 382751 := bstep (se 1 (by rfl) ⟨287063, by rfl⟩ : syracuseStep 382751 = 574127) B574127
theorem B382799 : Blo 251819 382799 := bstep (se 1 (by rfl) ⟨287099, by rfl⟩ : syracuseStep 382799 = 574199) B574199
theorem B382919 : Blo 251819 382919 := bstep (se 1 (by rfl) ⟨287189, by rfl⟩ : syracuseStep 382919 = 574379) B574379
theorem B251887 : Blo 251819 251887 := bstep (se 1 (by rfl) ⟨188915, by rfl⟩ : syracuseStep 251887 = 377831) B377831
theorem B252059 : Blo 251819 252059 := bstep (se 1 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 252059 = 378089) B378089
theorem B284827 : Blo 251819 284827 := bstep (se 1 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 284827 = 427241) B427241
theorem B252095 : Blo 251819 252095 := bstep (se 1 (by rfl) ⟨189071, by rfl⟩ : syracuseStep 252095 = 378143) B378143
theorem B284863 : Blo 251819 284863 := bstep (se 1 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 284863 = 427295) B427295
theorem B383273 : Blo 251819 383273 := bstep (se 2 (by rfl) ⟨143727, by rfl⟩ : syracuseStep 383273 = 287455) B287455
theorem B252207 : Blo 251819 252207 := bstep (se 1 (by rfl) ⟨189155, by rfl⟩ : syracuseStep 252207 = 378311) B378311
theorem B383279 : Blo 251819 383279 := bstep (se 1 (by rfl) ⟨287459, by rfl⟩ : syracuseStep 383279 = 574919) B574919
theorem B252443 : Blo 251819 252443 := bstep (se 1 (by rfl) ⟨189332, by rfl⟩ : syracuseStep 252443 = 378665) B378665
theorem B252447 : Blo 251819 252447 := bstep (se 1 (by rfl) ⟨189335, by rfl⟩ : syracuseStep 252447 = 378671) B378671
theorem B383519 : Blo 251819 383519 := bstep (se 1 (by rfl) ⟨287639, by rfl⟩ : syracuseStep 383519 = 575279) B575279
theorem B908111 : Blo 251819 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B252763 : Blo 251819 252763 := bstep (se 1 (by rfl) ⟨189572, by rfl⟩ : syracuseStep 252763 = 379145) B379145
theorem B252831 : Blo 251819 252831 := bstep (se 1 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 252831 = 379247) B379247
theorem B1367009 : Blo 251819 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B252975 : Blo 251819 252975 := bstep (se 1 (by rfl) ⟨189731, by rfl⟩ : syracuseStep 252975 = 379463) B379463
theorem B252999 : Blo 251819 252999 := bstep (se 1 (by rfl) ⟨189749, by rfl⟩ : syracuseStep 252999 = 379499) B379499
theorem B2907251 : Blo 251819 2907251 := bstep (se 1 (by rfl) ⟨2180438, by rfl⟩ : syracuseStep 2907251 = 4360877) B4360877
theorem B253151 : Blo 251819 253151 := bstep (se 1 (by rfl) ⟨189863, by rfl⟩ : syracuseStep 253151 = 379727) B379727
theorem B810233 : Blo 251819 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B253415 : Blo 251819 253415 := bstep (se 1 (by rfl) ⟨190061, by rfl⟩ : syracuseStep 253415 = 380123) B380123
theorem B253531 : Blo 251819 253531 := bstep (se 1 (by rfl) ⟨190148, by rfl⟩ : syracuseStep 253531 = 380297) B380297
theorem B1728209 : Blo 251819 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B810823 : Blo 251819 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B253767 : Blo 251819 253767 := bstep (se 1 (by rfl) ⟨190325, by rfl⟩ : syracuseStep 253767 = 380651) B380651
theorem B253919 : Blo 251819 253919 := bstep (se 1 (by rfl) ⟨190439, by rfl⟩ : syracuseStep 253919 = 380879) B380879
theorem B1564645 : Blo 251819 1564645 := bstep (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) B293371
theorem B1728647 : Blo 251819 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B1827035 : Blo 251819 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B254183 : Blo 251819 254183 := bstep (se 1 (by rfl) ⟨190637, by rfl⟩ : syracuseStep 254183 = 381275) B381275
theorem B286951 : Blo 251819 286951 := bstep (se 1 (by rfl) ⟨215213, by rfl⟩ : syracuseStep 286951 = 430427) B430427
theorem B516449 : Blo 251819 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B254335 : Blo 251819 254335 := bstep (se 1 (by rfl) ⟨190751, by rfl⟩ : syracuseStep 254335 = 381503) B381503
theorem B254415 : Blo 251819 254415 := bstep (se 1 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 254415 = 381623) B381623
theorem B1729001 : Blo 251819 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B254567 : Blo 251819 254567 := bstep (se 1 (by rfl) ⟨190925, by rfl⟩ : syracuseStep 254567 = 381851) B381851
theorem B3334931 : Blo 251819 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B254831 : Blo 251819 254831 := bstep (se 1 (by rfl) ⟨191123, by rfl⟩ : syracuseStep 254831 = 382247) B382247
theorem B287599 : Blo 251819 287599 := bstep (se 1 (by rfl) ⟨215699, by rfl⟩ : syracuseStep 287599 = 431399) B431399
theorem B254887 : Blo 251819 254887 := bstep (se 1 (by rfl) ⟨191165, by rfl⟩ : syracuseStep 254887 = 382331) B382331
theorem B254971 : Blo 251819 254971 := bstep (se 1 (by rfl) ⟨191228, by rfl⟩ : syracuseStep 254971 = 382457) B382457
theorem B255039 : Blo 251819 255039 := bstep (se 1 (by rfl) ⟨191279, by rfl⟩ : syracuseStep 255039 = 382559) B382559
theorem B255183 : Blo 251819 255183 := bstep (se 1 (by rfl) ⟨191387, by rfl⟩ : syracuseStep 255183 = 382775) B382775
theorem B812425 : Blo 251819 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B1861001 : Blo 251819 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B255387 : Blo 251819 255387 := bstep (se 1 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 255387 = 383081) B383081
theorem B1467919 : Blo 251819 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B255599 : Blo 251819 255599 := bstep (se 1 (by rfl) ⟨191699, by rfl⟩ : syracuseStep 255599 = 383399) B383399
theorem B255655 : Blo 251819 255655 := bstep (se 1 (by rfl) ⟨191741, by rfl⟩ : syracuseStep 255655 = 383483) B383483
theorem B255739 : Blo 251819 255739 := bstep (se 1 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 255739 = 383609) B383609
theorem B255775 : Blo 251819 255775 := bstep (se 1 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 255775 = 383663) B383663
theorem B255807 : Blo 251819 255807 := bstep (se 1 (by rfl) ⟨191855, by rfl⟩ : syracuseStep 255807 = 383711) B383711
theorem B4352129 : Blo 251819 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B321727 : Blo 251819 321727 := bstep (se 1 (by rfl) ⟨241295, by rfl⟩ : syracuseStep 321727 = 482591) B482591
theorem B682219 : Blo 251819 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B813359 : Blo 251819 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B4385755 : Blo 251819 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B3632849 : Blo 251819 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B2453267 : Blo 251819 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B1077371 : Blo 251819 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B913531 : Blo 251819 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B1438181 : Blo 251819 1438181 := bstep (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) B269659
theorem B6943247 : Blo 251819 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B979537 : Blo 251819 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B717473 : Blo 251819 717473 := bstep (se 2 (by rfl) ⟨269052, by rfl⟩ : syracuseStep 717473 = 538105) B538105
theorem B1635997 : Blo 251819 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B2586401 : Blo 251819 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B456679 : Blo 251819 456679 := bstep (se 1 (by rfl) ⟨342509, by rfl⟩ : syracuseStep 456679 = 685019) B685019
theorem B718931 : Blo 251819 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B850283 : Blo 251819 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B2455919 : Blo 251819 2455919 := bstep (se 1 (by rfl) ⟨1841939, by rfl⟩ : syracuseStep 2455919 = 3683879) B3683879
theorem B850553 : Blo 251819 850553 := bstep (se 2 (by rfl) ⟨318957, by rfl⟩ : syracuseStep 850553 = 637915) B637915
theorem B850985 : Blo 251819 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B425081 : Blo 251819 425081 := bstep (se 2 (by rfl) ⟨159405, by rfl⟩ : syracuseStep 425081 = 318811) B318811
theorem B1637671 : Blo 251819 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B458063 : Blo 251819 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B1277531 : Blo 251819 1277531 := bstep (se 1 (by rfl) ⟨958148, by rfl⟩ : syracuseStep 1277531 = 1916297) B1916297
theorem B720571 : Blo 251819 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B4129049 : Blo 251819 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B852335 : Blo 251819 852335 := bstep (se 1 (by rfl) ⟨639251, by rfl⟩ : syracuseStep 852335 = 1278503) B1278503
theorem B362279 : Blo 251819 362279 := bstep (se 1 (by rfl) ⟨271709, by rfl⟩ : syracuseStep 362279 = 543419) B543419
theorem B1083233 : Blo 251819 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B1214351 : Blo 251819 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B460831 : Blo 251819 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B1280609 : Blo 251819 1280609 := bstep (se 2 (by rfl) ⟨480228, by rfl⟩ : syracuseStep 1280609 = 960457) B960457
theorem B723613 : Blo 251819 723613 := bstep (se 3 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 723613 = 271355) B271355
theorem B428969 : Blo 251819 428969 := bstep (se 2 (by rfl) ⟨160863, by rfl⟩ : syracuseStep 428969 = 321727) B321727
theorem B855251 : Blo 251819 855251 := bstep (se 1 (by rfl) ⟨641438, by rfl⟩ : syracuseStep 855251 = 1282877) B1282877
theorem B1281419 : Blo 251819 1281419 := bstep (se 1 (by rfl) ⟨961064, by rfl⟩ : syracuseStep 1281419 = 1922129) B1922129
theorem B855521 : Blo 251819 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B429671 : Blo 251819 429671 := bstep (se 1 (by rfl) ⟨322253, by rfl⟩ : syracuseStep 429671 = 644507) B644507
theorem B2101115 : Blo 251819 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B3084331 : Blo 251819 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B6295805 : Blo 251819 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B856439 : Blo 251819 856439 := bstep (se 1 (by rfl) ⟨642329, by rfl⟩ : syracuseStep 856439 = 1284659) B1284659
theorem B1938167 : Blo 251819 1938167 := bstep (se 1 (by rfl) ⟨1453625, by rfl⟩ : syracuseStep 1938167 = 2907251) B2907251
theorem B2167559 : Blo 251819 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B2233327 : Blo 251819 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B1152139 : Blo 251819 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B857249 : Blo 251819 857249 := bstep (se 2 (by rfl) ⟨321468, by rfl⟩ : syracuseStep 857249 = 642937) B642937
theorem B15832493 : Blo 251819 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B1152431 : Blo 251819 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B857519 : Blo 251819 857519 := bstep (se 1 (by rfl) ⟨643139, by rfl⟩ : syracuseStep 857519 = 1286279) B1286279
theorem B1218023 : Blo 251819 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1218041 : Blo 251819 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B1152667 : Blo 251819 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B857843 : Blo 251819 857843 := bstep (se 1 (by rfl) ⟨643382, by rfl⟩ : syracuseStep 857843 = 1286765) B1286765
theorem B3676265 : Blo 251819 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B2168957 : Blo 251819 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B858599 : Blo 251819 858599 := bstep (se 1 (by rfl) ⟨643949, by rfl⟩ : syracuseStep 858599 = 1287899) B1287899
theorem B727805 : Blo 251819 727805 := bstep (se 3 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 727805 = 272927) B272927
theorem B1285145 : Blo 251819 1285145 := bstep (se 2 (by rfl) ⟨481929, by rfl⟩ : syracuseStep 1285145 = 963859) B963859
theorem B4398209 : Blo 251819 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B859463 : Blo 251819 859463 := bstep (se 1 (by rfl) ⟨644597, by rfl⟩ : syracuseStep 859463 = 1289195) B1289195
theorem B1842745 : Blo 251819 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B860111 : Blo 251819 860111 := bstep (se 1 (by rfl) ⟨645083, by rfl⟩ : syracuseStep 860111 = 1290167) B1290167
theorem B958787 : Blo 251819 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B4628831 : Blo 251819 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B566855 : Blo 251819 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B2172581 : Blo 251819 2172581 := bstep (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) B407359
theorem B567035 : Blo 251819 567035 := bstep (se 1 (by rfl) ⟨425276, by rfl⟩ : syracuseStep 567035 = 850553) B850553
theorem B31205209 : Blo 251819 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B567323 : Blo 251819 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B4139171 : Blo 251819 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B305375 : Blo 251819 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B960761 : Blo 251819 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B961247 : Blo 251819 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B13806395 : Blo 251819 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B4304015 : Blo 251819 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B1223923 : Blo 251819 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1944911 : Blo 251819 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B961915 : Blo 251819 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B568799 : Blo 251819 568799 := bstep (se 1 (by rfl) ⟨426599, by rfl⟩ : syracuseStep 568799 = 853199) B853199
theorem B1158799 : Blo 251819 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B569015 : Blo 251819 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B307327 : Blo 251819 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B1028371 : Blo 251819 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B1225115 : Blo 251819 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B569807 : Blo 251819 569807 := bstep (se 1 (by rfl) ⟨427355, by rfl⟩ : syracuseStep 569807 = 854711) B854711
theorem B570473 : Blo 251819 570473 := bstep (se 2 (by rfl) ⟨213927, by rfl⟩ : syracuseStep 570473 = 427855) B427855
theorem B3454109 : Blo 251819 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B1455731 : Blo 251819 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B571103 : Blo 251819 571103 := bstep (se 1 (by rfl) ⟨428327, by rfl⟩ : syracuseStep 571103 = 856655) B856655
theorem B538447 : Blo 251819 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B4110365 : Blo 251819 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B964649 : Blo 251819 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B571463 : Blo 251819 571463 := bstep (se 1 (by rfl) ⟨428597, by rfl⟩ : syracuseStep 571463 = 857195) B857195
theorem B408007 : Blo 251819 408007 := bstep (se 1 (by rfl) ⟨306005, by rfl⟩ : syracuseStep 408007 = 612011) B612011
theorem B5847673 : Blo 251819 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B572129 : Blo 251819 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B572327 : Blo 251819 572327 := bstep (se 1 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 572327 = 858491) B858491
theorem B572507 : Blo 251819 572507 := bstep (se 1 (by rfl) ⟨429380, by rfl⟩ : syracuseStep 572507 = 858761) B858761
theorem B638057 : Blo 251819 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B605407 : Blo 251819 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B1621235 : Blo 251819 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2080079 : Blo 251819 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B540155 : Blo 251819 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B1031743 : Blo 251819 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B573263 : Blo 251819 573263 := bstep (se 1 (by rfl) ⟨429947, by rfl⟩ : syracuseStep 573263 = 859895) B859895
theorem B638887 : Blo 251819 638887 := bstep (se 1 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 638887 = 958331) B958331
theorem B1622207 : Blo 251819 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B639211 : Blo 251819 639211 := bstep (se 1 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 639211 = 958817) B958817
theorem B344299 : Blo 251819 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B573983 : Blo 251819 573983 := bstep (se 1 (by rfl) ⟨430487, by rfl⟩ : syracuseStep 573983 = 860975) B860975
theorem B574055 : Blo 251819 574055 := bstep (se 1 (by rfl) ⟨430541, by rfl⟩ : syracuseStep 574055 = 861083) B861083
theorem B967535 : Blo 251819 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B378047 : Blo 251819 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B378191 : Blo 251819 378191 := bstep (se 1 (by rfl) ⟨283643, by rfl⟩ : syracuseStep 378191 = 567287) B567287
theorem B574811 : Blo 251819 574811 := bstep (se 1 (by rfl) ⟨431108, by rfl⟩ : syracuseStep 574811 = 862217) B862217
theorem B378281 : Blo 251819 378281 := bstep (se 2 (by rfl) ⟨141855, by rfl⟩ : syracuseStep 378281 = 283711) B283711
theorem B2901419 : Blo 251819 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B378431 : Blo 251819 378431 := bstep (se 1 (by rfl) ⟨283823, by rfl⟩ : syracuseStep 378431 = 567647) B567647
theorem B378473 : Blo 251819 378473 := bstep (se 2 (by rfl) ⟨141927, by rfl⟩ : syracuseStep 378473 = 283855) B283855
theorem B575081 : Blo 251819 575081 := bstep (se 2 (by rfl) ⟨215655, by rfl⟩ : syracuseStep 575081 = 431311) B431311
theorem B640619 : Blo 251819 640619 := bstep (se 1 (by rfl) ⟨480464, by rfl⟩ : syracuseStep 640619 = 960929) B960929
theorem B378911 : Blo 251819 378911 := bstep (se 1 (by rfl) ⟨284183, by rfl⟩ : syracuseStep 378911 = 568367) B568367
theorem B2181329 : Blo 251819 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B379103 : Blo 251819 379103 := bstep (se 1 (by rfl) ⟨284327, by rfl⟩ : syracuseStep 379103 = 568655) B568655
theorem B641267 : Blo 251819 641267 := bstep (se 1 (by rfl) ⟨480950, by rfl⟩ : syracuseStep 641267 = 961901) B961901
theorem B379163 : Blo 251819 379163 := bstep (se 1 (by rfl) ⟨284372, by rfl⟩ : syracuseStep 379163 = 568745) B568745
theorem B1821179 : Blo 251819 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B379487 : Blo 251819 379487 := bstep (se 1 (by rfl) ⟨284615, by rfl⟩ : syracuseStep 379487 = 569231) B569231
theorem B608905 : Blo 251819 608905 := bstep (se 2 (by rfl) ⟨228339, by rfl⟩ : syracuseStep 608905 = 456679) B456679
theorem B576161 : Blo 251819 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B1624873 : Blo 251819 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B379769 : Blo 251819 379769 := bstep (se 2 (by rfl) ⟨142413, by rfl⟩ : syracuseStep 379769 = 284827) B284827
theorem B379817 : Blo 251819 379817 := bstep (se 2 (by rfl) ⟨142431, by rfl⟩ : syracuseStep 379817 = 284863) B284863
theorem B969691 : Blo 251819 969691 := bstep (se 1 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 969691 = 1454537) B1454537
theorem B379967 : Blo 251819 379967 := bstep (se 1 (by rfl) ⟨284975, by rfl⟩ : syracuseStep 379967 = 569951) B569951
theorem B478315 : Blo 251819 478315 := bstep (se 1 (by rfl) ⟨358736, by rfl⟩ : syracuseStep 478315 = 717473) B717473
theorem B9817307 : Blo 251819 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B1035767 : Blo 251819 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B380519 : Blo 251819 380519 := bstep (se 1 (by rfl) ⟨285389, by rfl⟩ : syracuseStep 380519 = 570779) B570779
theorem B642887 : Blo 251819 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B1724267 : Blo 251819 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B380903 : Blo 251819 380903 := bstep (se 1 (by rfl) ⟨285677, by rfl⟩ : syracuseStep 380903 = 571355) B571355
theorem B479287 : Blo 251819 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B381023 : Blo 251819 381023 := bstep (se 1 (by rfl) ⟨285767, by rfl⟩ : syracuseStep 381023 = 571535) B571535
theorem B381035 : Blo 251819 381035 := bstep (se 1 (by rfl) ⟨285776, by rfl⟩ : syracuseStep 381035 = 571553) B571553
theorem B381083 : Blo 251819 381083 := bstep (se 1 (by rfl) ⟨285812, by rfl⟩ : syracuseStep 381083 = 571625) B571625
theorem B2183561 : Blo 251819 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B283387 : Blo 251819 283387 := bstep (se 1 (by rfl) ⟨212540, by rfl⟩ : syracuseStep 283387 = 425081) B425081
theorem B381935 : Blo 251819 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B2151461 : Blo 251819 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B2086193 : Blo 251819 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B382319 : Blo 251819 382319 := bstep (se 1 (by rfl) ⟨286739, by rfl⟩ : syracuseStep 382319 = 573479) B573479
theorem B13981081 : Blo 251819 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B382439 : Blo 251819 382439 := bstep (se 1 (by rfl) ⟨286829, by rfl⟩ : syracuseStep 382439 = 573659) B573659
theorem B284143 : Blo 251819 284143 := bstep (se 1 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 284143 = 426215) B426215
theorem B546383 : Blo 251819 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B284251 : Blo 251819 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B382601 : Blo 251819 382601 := bstep (se 2 (by rfl) ⟨143475, by rfl⟩ : syracuseStep 382601 = 286951) B286951
theorem B382619 : Blo 251819 382619 := bstep (se 1 (by rfl) ⟨286964, by rfl⟩ : syracuseStep 382619 = 573929) B573929
theorem B382811 : Blo 251819 382811 := bstep (se 1 (by rfl) ⟨287108, by rfl⟩ : syracuseStep 382811 = 574217) B574217
theorem B612193 : Blo 251819 612193 := bstep (se 2 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 612193 = 459145) B459145
theorem B284539 : Blo 251819 284539 := bstep (se 1 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 284539 = 426809) B426809
theorem B284575 : Blo 251819 284575 := bstep (se 1 (by rfl) ⟨213431, by rfl⟩ : syracuseStep 284575 = 426863) B426863
theorem B1169447 : Blo 251819 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B251975 : Blo 251819 251975 := bstep (se 1 (by rfl) ⟨188981, by rfl⟩ : syracuseStep 251975 = 377963) B377963
theorem B383195 : Blo 251819 383195 := bstep (se 1 (by rfl) ⟨287396, by rfl⟩ : syracuseStep 383195 = 574793) B574793
theorem B252135 : Blo 251819 252135 := bstep (se 1 (by rfl) ⟨189101, by rfl⟩ : syracuseStep 252135 = 378203) B378203
theorem B481619 : Blo 251819 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B252319 : Blo 251819 252319 := bstep (se 1 (by rfl) ⟨189239, by rfl⟩ : syracuseStep 252319 = 378479) B378479
theorem B252367 : Blo 251819 252367 := bstep (se 1 (by rfl) ⟨189275, by rfl⟩ : syracuseStep 252367 = 378551) B378551
theorem B252391 : Blo 251819 252391 := bstep (se 1 (by rfl) ⟨189293, by rfl⟩ : syracuseStep 252391 = 378587) B378587
theorem B383465 : Blo 251819 383465 := bstep (se 2 (by rfl) ⟨143799, by rfl⟩ : syracuseStep 383465 = 287599) B287599
theorem B252507 : Blo 251819 252507 := bstep (se 1 (by rfl) ⟨189380, by rfl⟩ : syracuseStep 252507 = 378761) B378761
theorem B252575 : Blo 251819 252575 := bstep (se 1 (by rfl) ⟨189431, by rfl⟩ : syracuseStep 252575 = 378863) B378863
theorem B482105 : Blo 251819 482105 := bstep (se 2 (by rfl) ⟨180789, by rfl⟩ : syracuseStep 482105 = 361579) B361579
theorem B252743 : Blo 251819 252743 := bstep (se 1 (by rfl) ⟨189557, by rfl⟩ : syracuseStep 252743 = 379115) B379115
theorem B285511 : Blo 251819 285511 := bstep (se 1 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 285511 = 428267) B428267
theorem B252783 : Blo 251819 252783 := bstep (se 1 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 252783 = 379175) B379175
theorem B2153375 : Blo 251819 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B252839 : Blo 251819 252839 := bstep (se 1 (by rfl) ⟨189629, by rfl⟩ : syracuseStep 252839 = 379259) B379259
theorem B1989647 : Blo 251819 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B613423 : Blo 251819 613423 := bstep (se 1 (by rfl) ⟨460067, by rfl⟩ : syracuseStep 613423 = 920135) B920135
theorem B253019 : Blo 251819 253019 := bstep (se 1 (by rfl) ⟨189764, by rfl⟩ : syracuseStep 253019 = 379529) B379529
theorem B253135 : Blo 251819 253135 := bstep (se 1 (by rfl) ⟨189851, by rfl⟩ : syracuseStep 253135 = 379703) B379703
theorem B253159 : Blo 251819 253159 := bstep (se 1 (by rfl) ⟨189869, by rfl⟩ : syracuseStep 253159 = 379739) B379739
theorem B253255 : Blo 251819 253255 := bstep (se 1 (by rfl) ⟨189941, by rfl⟩ : syracuseStep 253255 = 379883) B379883
theorem B1957225 : Blo 251819 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B286159 : Blo 251819 286159 := bstep (se 1 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 286159 = 429239) B429239
theorem B253391 : Blo 251819 253391 := bstep (se 1 (by rfl) ⟨190043, by rfl⟩ : syracuseStep 253391 = 380087) B380087
theorem B253551 : Blo 251819 253551 := bstep (se 1 (by rfl) ⟨190163, by rfl⟩ : syracuseStep 253551 = 380327) B380327
theorem B253607 : Blo 251819 253607 := bstep (se 1 (by rfl) ⟨190205, by rfl⟩ : syracuseStep 253607 = 380411) B380411
theorem B286375 : Blo 251819 286375 := bstep (se 1 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 286375 = 429563) B429563
theorem B253671 : Blo 251819 253671 := bstep (se 1 (by rfl) ⟨190253, by rfl⟩ : syracuseStep 253671 = 380507) B380507
theorem B253727 : Blo 251819 253727 := bstep (se 1 (by rfl) ⟨190295, by rfl⟩ : syracuseStep 253727 = 380591) B380591
theorem B253807 : Blo 251819 253807 := bstep (se 1 (by rfl) ⟨190355, by rfl⟩ : syracuseStep 253807 = 380711) B380711
theorem B2318213 : Blo 251819 2318213 := bstep (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) B434665
theorem B253863 : Blo 251819 253863 := bstep (se 1 (by rfl) ⟨190397, by rfl⟩ : syracuseStep 253863 = 380795) B380795
theorem B286663 : Blo 251819 286663 := bstep (se 1 (by rfl) ⟨214997, by rfl⟩ : syracuseStep 286663 = 429995) B429995
theorem B647291 : Blo 251819 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B254143 : Blo 251819 254143 := bstep (se 1 (by rfl) ⟨190607, by rfl⟩ : syracuseStep 254143 = 381215) B381215
theorem B254159 : Blo 251819 254159 := bstep (se 1 (by rfl) ⟨190619, by rfl⟩ : syracuseStep 254159 = 381239) B381239
theorem B254207 : Blo 251819 254207 := bstep (se 1 (by rfl) ⟨190655, by rfl⟩ : syracuseStep 254207 = 381311) B381311
theorem B647423 : Blo 251819 647423 := bstep (se 1 (by rfl) ⟨485567, by rfl⟩ : syracuseStep 647423 = 971135) B971135
theorem B254255 : Blo 251819 254255 := bstep (se 1 (by rfl) ⟨190691, by rfl⟩ : syracuseStep 254255 = 381383) B381383
theorem B287023 : Blo 251819 287023 := bstep (se 1 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 287023 = 430535) B430535
theorem B909625 : Blo 251819 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B254491 : Blo 251819 254491 := bstep (se 1 (by rfl) ⟨190868, by rfl⟩ : syracuseStep 254491 = 381737) B381737
theorem B254495 : Blo 251819 254495 := bstep (se 1 (by rfl) ⟨190871, by rfl⟩ : syracuseStep 254495 = 381743) B381743
theorem B2908709 : Blo 251819 2908709 := bstep (se 4 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 2908709 = 545383) B545383
theorem B254575 : Blo 251819 254575 := bstep (se 1 (by rfl) ⟨190931, by rfl⟩ : syracuseStep 254575 = 381863) B381863
theorem B254631 : Blo 251819 254631 := bstep (se 1 (by rfl) ⟨190973, by rfl⟩ : syracuseStep 254631 = 381947) B381947
theorem B254671 : Blo 251819 254671 := bstep (se 1 (by rfl) ⟨191003, by rfl⟩ : syracuseStep 254671 = 382007) B382007
theorem B254751 : Blo 251819 254751 := bstep (se 1 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 254751 = 382127) B382127
theorem B4121401 : Blo 251819 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B484193 : Blo 251819 484193 := bstep (se 2 (by rfl) ⟨181572, by rfl⟩ : syracuseStep 484193 = 363145) B363145
theorem B255023 : Blo 251819 255023 := bstep (se 1 (by rfl) ⟨191267, by rfl⟩ : syracuseStep 255023 = 382535) B382535
theorem B255087 : Blo 251819 255087 := bstep (se 1 (by rfl) ⟨191315, by rfl⟩ : syracuseStep 255087 = 382631) B382631
theorem B255143 : Blo 251819 255143 := bstep (se 1 (by rfl) ⟨191357, by rfl⟩ : syracuseStep 255143 = 382715) B382715
theorem B255167 : Blo 251819 255167 := bstep (se 1 (by rfl) ⟨191375, by rfl⟩ : syracuseStep 255167 = 382751) B382751
theorem B255199 : Blo 251819 255199 := bstep (se 1 (by rfl) ⟨191399, by rfl⟩ : syracuseStep 255199 = 382799) B382799
theorem B255279 : Blo 251819 255279 := bstep (se 1 (by rfl) ⟨191459, by rfl⟩ : syracuseStep 255279 = 382919) B382919
theorem B255515 : Blo 251819 255515 := bstep (se 1 (by rfl) ⟨191636, by rfl⟩ : syracuseStep 255515 = 383273) B383273
theorem B255519 : Blo 251819 255519 := bstep (se 1 (by rfl) ⟨191639, by rfl⟩ : syracuseStep 255519 = 383279) B383279
theorem B484937 : Blo 251819 484937 := bstep (se 2 (by rfl) ⟨181851, by rfl⟩ : syracuseStep 484937 = 363703) B363703
theorem B255679 : Blo 251819 255679 := bstep (se 1 (by rfl) ⟨191759, by rfl⟩ : syracuseStep 255679 = 383519) B383519
theorem B2975491 : Blo 251819 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B911339 : Blo 251819 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B485423 : Blo 251819 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B6547877 : Blo 251819 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B2223287 : Blo 251819 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B1306049 : Blo 251819 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B1240667 : Blo 251819 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B2913083 : Blo 251819 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B2421899 : Blo 251819 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B1635511 : Blo 251819 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B718247 : Blo 251819 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B4356503 : Blo 251819 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B1637279 : Blo 251819 1637279 := bstep (se 1 (by rfl) ⟨1227959, by rfl⟩ : syracuseStep 1637279 = 2455919) B2455919
theorem B3243185 : Blo 251819 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B982297 : Blo 251819 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B425695 : Blo 251819 425695 := bstep (se 1 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 425695 = 638543) B638543
theorem B851687 : Blo 251819 851687 := bstep (se 1 (by rfl) ⟨638765, by rfl⟩ : syracuseStep 851687 = 1277531) B1277531
theorem B1081097 : Blo 251819 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B2752699 : Blo 251819 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B852281 : Blo 251819 852281 := bstep (se 2 (by rfl) ⟨319605, by rfl⟩ : syracuseStep 852281 = 639211) B639211
theorem B459065 : Blo 251819 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B1212833 : Blo 251819 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B4325885 : Blo 251819 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B1934279 : Blo 251819 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B427079 : Blo 251819 427079 := bstep (se 1 (by rfl) ⟨320309, by rfl⟩ : syracuseStep 427079 = 640619) B640619
theorem B722155 : Blo 251819 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B427511 : Blo 251819 427511 := bstep (se 1 (by rfl) ⟨320633, by rfl⟩ : syracuseStep 427511 = 641267) B641267
theorem B1214119 : Blo 251819 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B853739 : Blo 251819 853739 := bstep (se 1 (by rfl) ⟨640304, by rfl⟩ : syracuseStep 853739 = 1280609) B1280609
theorem B854279 : Blo 251819 854279 := bstep (se 1 (by rfl) ⟨640709, by rfl⟩ : syracuseStep 854279 = 1281419) B1281419
theorem B3967321 : Blo 251819 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B428591 : Blo 251819 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B4197203 : Blo 251819 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B1445039 : Blo 251819 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B10554995 : Blo 251819 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B2166497 : Blo 251819 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B1445971 : Blo 251819 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B1282553 : Blo 251819 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B13931189 : Blo 251819 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B856763 : Blo 251819 856763 := bstep (se 1 (by rfl) ⟨642572, by rfl⟩ : syracuseStep 856763 = 1285145) B1285145
theorem B1545065 : Blo 251819 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1545475 : Blo 251819 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B431527 : Blo 251819 431527 := bstep (se 1 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 431527 = 647291) B647291
theorem B431615 : Blo 251819 431615 := bstep (se 1 (by rfl) ⟨323711, by rfl⟩ : syracuseStep 431615 = 647423) B647423
theorem B1939139 : Blo 251819 1939139 := bstep (se 1 (by rfl) ⟨1454354, by rfl⟩ : syracuseStep 1939139 = 2908709) B2908709
theorem B1448387 : Blo 251819 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B2759447 : Blo 251819 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B4365251 : Blo 251819 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B1482191 : Blo 251819 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B827111 : Blo 251819 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B1942055 : Blo 251819 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B1614599 : Blo 251819 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B2302739 : Blo 251819 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B2762045 : Blo 251819 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1091519 : Blo 251819 1091519 := bstep (se 1 (by rfl) ⟨818639, by rfl⟩ : syracuseStep 1091519 = 1637279) B1637279
theorem B1386719 : Blo 251819 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B4598045 : Blo 251819 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B567593 : Blo 251819 567593 := bstep (se 2 (by rfl) ⟨212847, by rfl⟩ : syracuseStep 567593 = 425695) B425695
theorem B567791 : Blo 251819 567791 := bstep (se 1 (by rfl) ⟨425843, by rfl⟩ : syracuseStep 567791 = 851687) B851687
theorem B568223 : Blo 251819 568223 := bstep (se 1 (by rfl) ⟨426167, by rfl⟩ : syracuseStep 568223 = 852335) B852335
theorem B1454219 : Blo 251819 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B570167 : Blo 251819 570167 := bstep (se 1 (by rfl) ⟨427625, by rfl⟩ : syracuseStep 570167 = 855251) B855251
theorem B570347 : Blo 251819 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B3257333 : Blo 251819 3257333 := bstep (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) B305375
theorem B570959 : Blo 251819 570959 := bstep (se 1 (by rfl) ⟨428219, by rfl⟩ : syracuseStep 570959 = 856439) B856439
theorem B1455707 : Blo 251819 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B1292111 : Blo 251819 1292111 := bstep (se 1 (by rfl) ⟨969083, by rfl⟩ : syracuseStep 1292111 = 1938167) B1938167
theorem B571499 : Blo 251819 571499 := bstep (se 1 (by rfl) ⟨428624, by rfl⟩ : syracuseStep 571499 = 857249) B857249
theorem B964817 : Blo 251819 964817 := bstep (se 2 (by rfl) ⟨361806, by rfl⟩ : syracuseStep 964817 = 723613) B723613
theorem B768287 : Blo 251819 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B571679 : Blo 251819 571679 := bstep (se 1 (by rfl) ⟨428759, by rfl⟩ : syracuseStep 571679 = 857519) B857519
theorem B1915325 : Blo 251819 1915325 := bstep (se 3 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 1915325 = 718247) B718247
theorem B571895 : Blo 251819 571895 := bstep (se 1 (by rfl) ⟨428921, by rfl⟩ : syracuseStep 571895 = 857843) B857843
theorem B1292921 : Blo 251819 1292921 := bstep (se 2 (by rfl) ⟨484845, by rfl⟩ : syracuseStep 1292921 = 969691) B969691
theorem B637753 : Blo 251819 637753 := bstep (se 2 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 637753 = 478315) B478315
theorem B1457021 : Blo 251819 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B572399 : Blo 251819 572399 := bstep (se 1 (by rfl) ⟨429299, by rfl⟩ : syracuseStep 572399 = 858599) B858599
theorem B1326431 : Blo 251819 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B2932139 : Blo 251819 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B966077 : Blo 251819 966077 := bstep (se 3 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 966077 = 362279) B362279
theorem B572975 : Blo 251819 572975 := bstep (se 1 (by rfl) ⟨429731, by rfl⟩ : syracuseStep 572975 = 859463) B859463
theorem B573407 : Blo 251819 573407 := bstep (se 1 (by rfl) ⟨430055, by rfl⟩ : syracuseStep 573407 = 860111) B860111
theorem B4112441 : Blo 251819 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B639049 : Blo 251819 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B409769 : Blo 251819 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B639191 : Blo 251819 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B377849 : Blo 251819 377849 := bstep (se 2 (by rfl) ⟨141693, by rfl⟩ : syracuseStep 377849 = 283387) B283387
theorem B377903 : Blo 251819 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B378023 : Blo 251819 378023 := bstep (se 1 (by rfl) ⟨283517, by rfl⟩ : syracuseStep 378023 = 567035) B567035
theorem B607559 : Blo 251819 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B378215 : Blo 251819 378215 := bstep (se 1 (by rfl) ⟨283661, by rfl⟩ : syracuseStep 378215 = 567323) B567323
theorem B640507 : Blo 251819 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B2180681 : Blo 251819 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B640831 : Blo 251819 640831 := bstep (se 1 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 640831 = 961247) B961247
theorem B378857 : Blo 251819 378857 := bstep (se 2 (by rfl) ⟨142071, by rfl⟩ : syracuseStep 378857 = 284143) B284143
theorem B2869343 : Blo 251819 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B379001 : Blo 251819 379001 := bstep (se 2 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 379001 = 284251) B284251
theorem B1296607 : Blo 251819 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B379199 : Blo 251819 379199 := bstep (se 1 (by rfl) ⟨284399, by rfl⟩ : syracuseStep 379199 = 568799) B568799
theorem B379343 : Blo 251819 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B379385 : Blo 251819 379385 := bstep (se 2 (by rfl) ⟨142269, by rfl⟩ : syracuseStep 379385 = 284539) B284539
theorem B379433 : Blo 251819 379433 := bstep (se 2 (by rfl) ⟨142287, by rfl⟩ : syracuseStep 379433 = 284575) B284575
theorem B379871 : Blo 251819 379871 := bstep (se 1 (by rfl) ⟨284903, by rfl⟩ : syracuseStep 379871 = 569807) B569807
theorem B544009 : Blo 251819 544009 := bstep (se 2 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 544009 = 408007) B408007
theorem B380315 : Blo 251819 380315 := bstep (se 1 (by rfl) ⟨285236, by rfl⟩ : syracuseStep 380315 = 570473) B570473
theorem B970487 : Blo 251819 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B380681 : Blo 251819 380681 := bstep (se 2 (by rfl) ⟨142755, by rfl⟩ : syracuseStep 380681 = 285511) B285511
theorem B380735 : Blo 251819 380735 := bstep (se 1 (by rfl) ⟨285551, by rfl⟩ : syracuseStep 380735 = 571103) B571103
theorem B2740243 : Blo 251819 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B643099 : Blo 251819 643099 := bstep (se 1 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 643099 = 964649) B964649
theorem B380975 : Blo 251819 380975 := bstep (se 1 (by rfl) ⟨285731, by rfl⟩ : syracuseStep 380975 = 571463) B571463
theorem B2904335 : Blo 251819 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B807209 : Blo 251819 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B2609633 : Blo 251819 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B381419 : Blo 251819 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B381545 : Blo 251819 381545 := bstep (se 2 (by rfl) ⟨143079, by rfl⟩ : syracuseStep 381545 = 286159) B286159
theorem B381551 : Blo 251819 381551 := bstep (se 1 (by rfl) ⟨286163, by rfl⟩ : syracuseStep 381551 = 572327) B572327
theorem B381671 : Blo 251819 381671 := bstep (se 1 (by rfl) ⟨286253, by rfl⟩ : syracuseStep 381671 = 572507) B572507
theorem B381833 : Blo 251819 381833 := bstep (se 2 (by rfl) ⟨143187, by rfl⟩ : syracuseStep 381833 = 286375) B286375
theorem B382175 : Blo 251819 382175 := bstep (se 1 (by rfl) ⟨286631, by rfl⟩ : syracuseStep 382175 = 573263) B573263
theorem B382217 : Blo 251819 382217 := bstep (se 2 (by rfl) ⟨143331, by rfl⟩ : syracuseStep 382217 = 286663) B286663
theorem B382655 : Blo 251819 382655 := bstep (se 1 (by rfl) ⟨286991, by rfl⟩ : syracuseStep 382655 = 573983) B573983
theorem B382697 : Blo 251819 382697 := bstep (se 2 (by rfl) ⟨143511, by rfl⟩ : syracuseStep 382697 = 287023) B287023
theorem B382703 : Blo 251819 382703 := bstep (se 1 (by rfl) ⟨287027, by rfl⟩ : syracuseStep 382703 = 574055) B574055
theorem B12474101 : Blo 251819 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B645023 : Blo 251819 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B252031 : Blo 251819 252031 := bstep (se 1 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 252031 = 378047) B378047
theorem B252127 : Blo 251819 252127 := bstep (se 1 (by rfl) ⟨189095, by rfl⟩ : syracuseStep 252127 = 378191) B378191
theorem B383207 : Blo 251819 383207 := bstep (se 1 (by rfl) ⟨287405, by rfl⟩ : syracuseStep 383207 = 574811) B574811
theorem B12343549 : Blo 251819 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B252187 : Blo 251819 252187 := bstep (se 1 (by rfl) ⟨189140, by rfl⟩ : syracuseStep 252187 = 378281) B378281
theorem B252287 : Blo 251819 252287 := bstep (se 1 (by rfl) ⟨189215, by rfl⟩ : syracuseStep 252287 = 378431) B378431
theorem B252315 : Blo 251819 252315 := bstep (se 1 (by rfl) ⟨189236, by rfl⟩ : syracuseStep 252315 = 378473) B378473
theorem B383387 : Blo 251819 383387 := bstep (se 1 (by rfl) ⟨287540, by rfl⟩ : syracuseStep 383387 = 575081) B575081
theorem B5495201 : Blo 251819 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B809567 : Blo 251819 809567 := bstep (se 1 (by rfl) ⟨607175, by rfl⟩ : syracuseStep 809567 = 1214351) B1214351
theorem B252607 : Blo 251819 252607 := bstep (se 1 (by rfl) ⟨189455, by rfl⟩ : syracuseStep 252607 = 378911) B378911
theorem B252735 : Blo 251819 252735 := bstep (se 1 (by rfl) ⟨189551, by rfl⟩ : syracuseStep 252735 = 379103) B379103
theorem B252775 : Blo 251819 252775 := bstep (se 1 (by rfl) ⟨189581, by rfl⟩ : syracuseStep 252775 = 379163) B379163
theorem B252991 : Blo 251819 252991 := bstep (se 1 (by rfl) ⟨189743, by rfl⟩ : syracuseStep 252991 = 379487) B379487
theorem B384107 : Blo 251819 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B253179 : Blo 251819 253179 := bstep (se 1 (by rfl) ⟨189884, by rfl⟩ : syracuseStep 253179 = 379769) B379769
theorem B253211 : Blo 251819 253211 := bstep (se 1 (by rfl) ⟨189908, by rfl⟩ : syracuseStep 253211 = 379817) B379817
theorem B285979 : Blo 251819 285979 := bstep (se 1 (by rfl) ⟨214484, by rfl⟩ : syracuseStep 285979 = 428969) B428969
theorem B253311 : Blo 251819 253311 := bstep (se 1 (by rfl) ⟨189983, by rfl⟩ : syracuseStep 253311 = 379967) B379967
theorem B6544871 : Blo 251819 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B253679 : Blo 251819 253679 := bstep (se 1 (by rfl) ⟨190259, by rfl⟩ : syracuseStep 253679 = 380519) B380519
theorem B286447 : Blo 251819 286447 := bstep (se 1 (by rfl) ⟨214835, by rfl⟩ : syracuseStep 286447 = 429671) B429671
theorem B41606945 : Blo 251819 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1400743 : Blo 251819 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B253935 : Blo 251819 253935 := bstep (se 1 (by rfl) ⟨190451, by rfl⟩ : syracuseStep 253935 = 380903) B380903
theorem B614441 : Blo 251819 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B254015 : Blo 251819 254015 := bstep (se 1 (by rfl) ⟨190511, by rfl⟩ : syracuseStep 254015 = 381023) B381023
theorem B254023 : Blo 251819 254023 := bstep (se 1 (by rfl) ⟨190517, by rfl⟩ : syracuseStep 254023 = 381035) B381035
theorem B254055 : Blo 251819 254055 := bstep (se 1 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 254055 = 381083) B381083
theorem B254623 : Blo 251819 254623 := bstep (se 1 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 254623 = 381935) B381935
theorem B1434307 : Blo 251819 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B5563181 : Blo 251819 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B811873 : Blo 251819 811873 := bstep (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) B608905
theorem B254879 : Blo 251819 254879 := bstep (se 1 (by rfl) ⟨191159, by rfl⟩ : syracuseStep 254879 = 382319) B382319
theorem B812015 : Blo 251819 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B254959 : Blo 251819 254959 := bstep (se 1 (by rfl) ⟨191219, by rfl⟩ : syracuseStep 254959 = 382439) B382439
theorem B812027 : Blo 251819 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B255067 : Blo 251819 255067 := bstep (se 1 (by rfl) ⟨191300, by rfl⟩ : syracuseStep 255067 = 382601) B382601
theorem B255079 : Blo 251819 255079 := bstep (se 1 (by rfl) ⟨191309, by rfl⟩ : syracuseStep 255079 = 382619) B382619
theorem B255207 : Blo 251819 255207 := bstep (se 1 (by rfl) ⟨191405, by rfl⟩ : syracuseStep 255207 = 382811) B382811
theorem B2450843 : Blo 251819 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B255463 : Blo 251819 255463 := bstep (se 1 (by rfl) ⟨191597, by rfl⟩ : syracuseStep 255463 = 383195) B383195
theorem B321079 : Blo 251819 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B1631897 : Blo 251819 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B255643 : Blo 251819 255643 := bstep (se 1 (by rfl) ⟨191732, by rfl⟩ : syracuseStep 255643 = 383465) B383465
theorem B485203 : Blo 251819 485203 := bstep (se 1 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 485203 = 727805) B727805
theorem B321403 : Blo 251819 321403 := bstep (se 1 (by rfl) ⟨241052, by rfl⟩ : syracuseStep 321403 = 482105) B482105
theorem B1435583 : Blo 251819 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B1371161 : Blo 251819 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B322795 : Blo 251819 322795 := bstep (se 1 (by rfl) ⟨242096, by rfl⟩ : syracuseStep 322795 = 484193) B484193
theorem B323291 : Blo 251819 323291 := bstep (se 1 (by rfl) ⟨242468, by rfl⟩ : syracuseStep 323291 = 484937) B484937
theorem B2977769 : Blo 251819 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B323615 : Blo 251819 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B1536185 : Blo 251819 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B18641441 : Blo 251819 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B9204263 : Blo 251819 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B1536889 : Blo 251819 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B717929 : Blo 251819 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B816257 : Blo 251819 816257 := bstep (se 2 (by rfl) ⟨306096, by rfl⟩ : syracuseStep 816257 = 612193) B612193
theorem B816743 : Blo 251819 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B5502629 : Blo 251819 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B7796897 : Blo 251819 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B1440413 : Blo 251819 1440413 := bstep (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) B540155
theorem B817897 : Blo 251819 817897 := bstep (se 2 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 817897 = 613423) B613423
theorem B1309729 : Blo 251819 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B425371 : Blo 251819 425371 := bstep (se 1 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 425371 = 638057) B638057
theorem B2456993 : Blo 251819 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B2162123 : Blo 251819 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B1080823 : Blo 251819 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B720731 : Blo 251819 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B851849 : Blo 251819 851849 := bstep (se 2 (by rfl) ⟨319443, by rfl⟩ : syracuseStep 851849 = 638887) B638887
theorem B852065 : Blo 251819 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B426127 : Blo 251819 426127 := bstep (se 1 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 426127 = 639191) B639191
theorem B3670265 : Blo 251819 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B2883923 : Blo 251819 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B4096493 : Blo 251819 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B4097141 : Blo 251819 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B1082497 : Blo 251819 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B854009 : Blo 251819 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B428105 : Blo 251819 428105 := bstep (se 2 (by rfl) ⟨160539, by rfl⟩ : syracuseStep 428105 = 321079) B321079
theorem B854441 : Blo 251819 854441 := bstep (se 2 (by rfl) ⟨320415, by rfl⟩ : syracuseStep 854441 = 640831) B640831
theorem B1444331 : Blo 251819 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B428537 : Blo 251819 428537 := bstep (se 2 (by rfl) ⟨160701, by rfl⟩ : syracuseStep 428537 = 321403) B321403
theorem B1936223 : Blo 251819 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B1739755 : Blo 251819 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B855035 : Blo 251819 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B430015 : Blo 251819 430015 := bstep (se 1 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 430015 = 645023) B645023
theorem B430393 : Blo 251819 430393 := bstep (se 2 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 430393 = 322795) B322795
theorem B725345 : Blo 251819 725345 := bstep (se 2 (by rfl) ⟨272004, by rfl⟩ : syracuseStep 725345 = 544009) B544009
theorem B988127 : Blo 251819 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B4363247 : Blo 251819 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B857465 : Blo 251819 857465 := bstep (se 2 (by rfl) ⟨321549, by rfl⟩ : syracuseStep 857465 = 643099) B643099
theorem B3708787 : Blo 251819 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B1841363 : Blo 251819 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B1087931 : Blo 251819 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B957055 : Blo 251819 957055 := bstep (se 1 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 957055 = 1435583) B1435583
theorem B727679 : Blo 251819 727679 := bstep (se 1 (by rfl) ⟨545759, by rfl⟩ : syracuseStep 727679 = 1091519) B1091519
theorem B924479 : Blo 251819 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B16458065 : Blo 251819 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B12427627 : Blo 251819 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B6136175 : Blo 251819 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2171555 : Blo 251819 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B1090529 : Blo 251819 1090529 := bstep (se 2 (by rfl) ⟨408948, by rfl⟩ : syracuseStep 1090529 = 817897) B817897
theorem B861407 : Blo 251819 861407 := bstep (se 1 (by rfl) ⟨646055, by rfl⟩ : syracuseStep 861407 = 1292111) B1292111
theorem B1746305 : Blo 251819 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B861947 : Blo 251819 861947 := bstep (se 1 (by rfl) ⟨646460, by rfl⟩ : syracuseStep 861947 = 1292921) B1292921
theorem B960275 : Blo 251819 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B567161 : Blo 251819 567161 := bstep (se 2 (by rfl) ⟨212685, by rfl⟩ : syracuseStep 567161 = 425371) B425371
theorem B862109 : Blo 251819 862109 := bstep (se 3 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 862109 = 323291) B323291
theorem B567899 : Blo 251819 567899 := bstep (se 1 (by rfl) ⟨425924, by rfl⟩ : syracuseStep 567899 = 851849) B851849
theorem B7940717 : Blo 251819 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B862973 : Blo 251819 862973 := bstep (se 3 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 862973 = 323615) B323615
theorem B273179 : Blo 251819 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B568187 : Blo 251819 568187 := bstep (se 1 (by rfl) ⟨426140, by rfl⟩ : syracuseStep 568187 = 852281) B852281
theorem B1289519 : Blo 251819 1289519 := bstep (se 1 (by rfl) ⟨967139, by rfl⟩ : syracuseStep 1289519 = 1934279) B1934279
theorem B1224173 : Blo 251819 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B1912409 : Blo 251819 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B1453787 : Blo 251819 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B569159 : Blo 251819 569159 := bstep (se 1 (by rfl) ⟨426869, by rfl⟩ : syracuseStep 569159 = 853739) B853739
theorem B1912895 : Blo 251819 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B569519 : Blo 251819 569519 := bstep (se 1 (by rfl) ⟨427139, by rfl⟩ : syracuseStep 569519 = 854279) B854279
theorem B962873 : Blo 251819 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B2798135 : Blo 251819 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B963359 : Blo 251819 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B1618825 : Blo 251819 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B538139 : Blo 251819 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B5289761 : Blo 251819 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B9287459 : Blo 251819 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B571175 : Blo 251819 571175 := bstep (se 1 (by rfl) ⟨428381, by rfl⟩ : syracuseStep 571175 = 856763) B856763
theorem B1030043 : Blo 251819 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B1620157 : Blo 251819 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B1292759 : Blo 251819 1292759 := bstep (se 1 (by rfl) ⟨969569, by rfl⟩ : syracuseStep 1292759 = 1939139) B1939139
theorem B965591 : Blo 251819 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B539711 : Blo 251819 539711 := bstep (se 1 (by rfl) ⟨404783, by rfl⟩ : syracuseStep 539711 = 809567) B809567
theorem B27737963 : Blo 251819 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B3653657 : Blo 251819 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B409627 : Blo 251819 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B1294703 : Blo 251819 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B541343 : Blo 251819 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B541351 : Blo 251819 541351 := bstep (se 1 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 541351 = 812027) B812027
theorem B2049185 : Blo 251819 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B3065363 : Blo 251819 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B378395 : Blo 251819 378395 := bstep (se 1 (by rfl) ⟨283796, by rfl⟩ : syracuseStep 378395 = 567593) B567593
theorem B378527 : Blo 251819 378527 := bstep (se 1 (by rfl) ⟨283895, by rfl⟩ : syracuseStep 378527 = 567791) B567791
theorem B575369 : Blo 251819 575369 := bstep (se 2 (by rfl) ⟨215763, by rfl⟩ : syracuseStep 575369 = 431527) B431527
theorem B378815 : Blo 251819 378815 := bstep (se 1 (by rfl) ⟨284111, by rfl⟩ : syracuseStep 378815 = 568223) B568223
theorem B7358525 : Blo 251819 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B969479 : Blo 251819 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B380111 : Blo 251819 380111 := bstep (se 1 (by rfl) ⟨285083, by rfl⟩ : syracuseStep 380111 = 570167) B570167
theorem B380231 : Blo 251819 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B478619 : Blo 251819 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B544171 : Blo 251819 544171 := bstep (se 1 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 544171 = 816257) B816257
theorem B380639 : Blo 251819 380639 := bstep (se 1 (by rfl) ⟨285479, by rfl⟩ : syracuseStep 380639 = 570959) B570959
theorem B970471 : Blo 251819 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B544495 : Blo 251819 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B380999 : Blo 251819 380999 := bstep (se 1 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 380999 = 571499) B571499
theorem B5197931 : Blo 251819 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B643211 : Blo 251819 643211 := bstep (se 1 (by rfl) ⟨482408, by rfl⟩ : syracuseStep 643211 = 964817) B964817
theorem B512191 : Blo 251819 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B381119 : Blo 251819 381119 := bstep (se 1 (by rfl) ⟨285839, by rfl⟩ : syracuseStep 381119 = 571679) B571679
theorem B381263 : Blo 251819 381263 := bstep (se 1 (by rfl) ⟨285947, by rfl⟩ : syracuseStep 381263 = 571895) B571895
theorem B381305 : Blo 251819 381305 := bstep (se 2 (by rfl) ⟨142989, by rfl⟩ : syracuseStep 381305 = 285979) B285979
theorem B971347 : Blo 251819 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B381599 : Blo 251819 381599 := bstep (se 1 (by rfl) ⟨286199, by rfl⟩ : syracuseStep 381599 = 572399) B572399
theorem B1954759 : Blo 251819 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B644051 : Blo 251819 644051 := bstep (se 1 (by rfl) ⟨483038, by rfl⟩ : syracuseStep 644051 = 966077) B966077
theorem B381929 : Blo 251819 381929 := bstep (se 2 (by rfl) ⟨143223, by rfl⟩ : syracuseStep 381929 = 286447) B286447
theorem B381983 : Blo 251819 381983 := bstep (se 1 (by rfl) ⟨286487, by rfl⟩ : syracuseStep 381983 = 572975) B572975
theorem B480487 : Blo 251819 480487 := bstep (se 1 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 480487 = 720731) B720731
theorem B382271 : Blo 251819 382271 := bstep (se 1 (by rfl) ⟨286703, by rfl⟩ : syracuseStep 382271 = 573407) B573407
theorem B2741627 : Blo 251819 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B808555 : Blo 251819 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B251899 : Blo 251819 251899 := bstep (se 1 (by rfl) ⟨188924, by rfl⟩ : syracuseStep 251899 = 377849) B377849
theorem B251935 : Blo 251819 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B284719 : Blo 251819 284719 := bstep (se 1 (by rfl) ⟨213539, by rfl⟩ : syracuseStep 284719 = 427079) B427079
theorem B252015 : Blo 251819 252015 := bstep (se 1 (by rfl) ⟨189011, by rfl⟩ : syracuseStep 252015 = 378023) B378023
theorem B252143 : Blo 251819 252143 := bstep (se 1 (by rfl) ⟨189107, by rfl⟩ : syracuseStep 252143 = 378215) B378215
theorem B285007 : Blo 251819 285007 := bstep (se 1 (by rfl) ⟨213755, by rfl⟩ : syracuseStep 285007 = 427511) B427511
theorem B252571 : Blo 251819 252571 := bstep (se 1 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 252571 = 378857) B378857
theorem B252667 : Blo 251819 252667 := bstep (se 1 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 252667 = 379001) B379001
theorem B252799 : Blo 251819 252799 := bstep (se 1 (by rfl) ⟨189599, by rfl⟩ : syracuseStep 252799 = 379199) B379199
theorem B252895 : Blo 251819 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B252923 : Blo 251819 252923 := bstep (se 1 (by rfl) ⟨189692, by rfl⟩ : syracuseStep 252923 = 379385) B379385
theorem B252955 : Blo 251819 252955 := bstep (se 1 (by rfl) ⟨189716, by rfl⟩ : syracuseStep 252955 = 379433) B379433
theorem B285727 : Blo 251819 285727 := bstep (se 1 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 285727 = 428591) B428591
theorem B253247 : Blo 251819 253247 := bstep (se 1 (by rfl) ⟨189935, by rfl⟩ : syracuseStep 253247 = 379871) B379871
theorem B253543 : Blo 251819 253543 := bstep (se 1 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 253543 = 380315) B380315
theorem B646937 : Blo 251819 646937 := bstep (se 2 (by rfl) ⟨242601, by rfl⟩ : syracuseStep 646937 = 485203) B485203
theorem B646991 : Blo 251819 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B253787 : Blo 251819 253787 := bstep (se 1 (by rfl) ⟨190340, by rfl⟩ : syracuseStep 253787 = 380681) B380681
theorem B253823 : Blo 251819 253823 := bstep (se 1 (by rfl) ⟨190367, by rfl⟩ : syracuseStep 253823 = 380735) B380735
theorem B253983 : Blo 251819 253983 := bstep (se 1 (by rfl) ⟨190487, by rfl⟩ : syracuseStep 253983 = 380975) B380975
theorem B1728809 : Blo 251819 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B254279 : Blo 251819 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B254363 : Blo 251819 254363 := bstep (se 1 (by rfl) ⟨190772, by rfl⟩ : syracuseStep 254363 = 381545) B381545
theorem B254367 : Blo 251819 254367 := bstep (se 1 (by rfl) ⟨190775, by rfl⟩ : syracuseStep 254367 = 381551) B381551
theorem B254447 : Blo 251819 254447 := bstep (se 1 (by rfl) ⟨190835, by rfl⟩ : syracuseStep 254447 = 381671) B381671
theorem B254555 : Blo 251819 254555 := bstep (se 1 (by rfl) ⟨190916, by rfl⟩ : syracuseStep 254555 = 381833) B381833
theorem B254783 : Blo 251819 254783 := bstep (se 1 (by rfl) ⟨191087, by rfl⟩ : syracuseStep 254783 = 382175) B382175
theorem B254811 : Blo 251819 254811 := bstep (se 1 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 254811 = 382217) B382217
theorem B287743 : Blo 251819 287743 := bstep (se 1 (by rfl) ⟨215807, by rfl⟩ : syracuseStep 287743 = 431615) B431615
theorem B255103 : Blo 251819 255103 := bstep (se 1 (by rfl) ⟨191327, by rfl⟩ : syracuseStep 255103 = 382655) B382655
theorem B255131 : Blo 251819 255131 := bstep (se 1 (by rfl) ⟨191348, by rfl⟩ : syracuseStep 255131 = 382697) B382697
theorem B255135 : Blo 251819 255135 := bstep (se 1 (by rfl) ⟨191351, by rfl⟩ : syracuseStep 255135 = 382703) B382703
theorem B8316067 : Blo 251819 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B255471 : Blo 251819 255471 := bstep (se 1 (by rfl) ⟨191603, by rfl⟩ : syracuseStep 255471 = 383207) B383207
theorem B255591 : Blo 251819 255591 := bstep (se 1 (by rfl) ⟨191693, by rfl⟩ : syracuseStep 255591 = 383387) B383387
theorem B3663467 : Blo 251819 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B2910167 : Blo 251819 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B551407 : Blo 251819 551407 := bstep (se 1 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 551407 = 827111) B827111
theorem B1927961 : Blo 251819 1927961 := bstep (se 2 (by rfl) ⟨722985, by rfl⟩ : syracuseStep 1927961 = 1445971) B1445971
theorem B1076399 : Blo 251819 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B1535159 : Blo 251819 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1633895 : Blo 251819 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B2060633 : Blo 251819 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B914107 : Blo 251819 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B850337 : Blo 251819 850337 := bstep (se 2 (by rfl) ⟨318876, by rfl⟩ : syracuseStep 850337 = 637753) B637753
theorem B3668419 : Blo 251819 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B1276883 : Blo 251819 1276883 := bstep (se 1 (by rfl) ⟨957662, by rfl⟩ : syracuseStep 1276883 = 1915325) B1915325
theorem B28146653 : Blo 251819 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B1441097 : Blo 251819 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B884287 : Blo 251819 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B1637995 : Blo 251819 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B1441415 : Blo 251819 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B1867657 : Blo 251819 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B721801 : Blo 251819 721801 := bstep (se 2 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 721801 = 541351) B541351
theorem B1443329 : Blo 251819 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B1443581 : Blo 251819 1443581 := bstep (se 3 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 1443581 = 541343) B541343
theorem B428807 : Blo 251819 428807 := bstep (se 1 (by rfl) ⟨321605, by rfl⟩ : syracuseStep 428807 = 643211) B643211
theorem B429367 : Blo 251819 429367 := bstep (se 1 (by rfl) ⟨322025, by rfl⟩ : syracuseStep 429367 = 644051) B644051
theorem B658751 : Blo 251819 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B7311005 : Blo 251819 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B725287 : Blo 251819 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B725561 : Blo 251819 725561 := bstep (se 2 (by rfl) ⟨272085, by rfl⟩ : syracuseStep 725561 = 544171) B544171
theorem B725993 : Blo 251819 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B431291 : Blo 251819 431291 := bstep (se 1 (by rfl) ⟨323468, by rfl⟩ : syracuseStep 431291 = 646937) B646937
theorem B431327 : Blo 251819 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B1152539 : Blo 251819 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B1447703 : Blo 251819 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B727019 : Blo 251819 727019 := bstep (se 1 (by rfl) ⟨545264, by rfl⟩ : syracuseStep 727019 = 1090529) B1090529
theorem B1218809 : Blo 251819 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B1940111 : Blo 251819 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B1285307 : Blo 251819 1285307 := bstep (se 1 (by rfl) ⟨963980, by rfl⟩ : syracuseStep 1285307 = 1927961) B1927961
theorem B728477 : Blo 251819 728477 := bstep (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) B273179
theorem B859679 : Blo 251819 859679 := bstep (se 1 (by rfl) ⟨644759, by rfl⟩ : syracuseStep 859679 = 1289519) B1289519
theorem B1089263 : Blo 251819 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B4891225 : Blo 251819 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B566891 : Blo 251819 566891 := bstep (se 1 (by rfl) ⟨425168, by rfl⟩ : syracuseStep 566891 = 850337) B850337
theorem B861839 : Blo 251819 861839 := bstep (se 1 (by rfl) ⟨646379, by rfl⟩ : syracuseStep 861839 = 1292759) B1292759
theorem B960731 : Blo 251819 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B960943 : Blo 251819 960943 := bstep (se 1 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 960943 = 1441415) B1441415
theorem B18491975 : Blo 251819 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B2435771 : Blo 251819 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B568043 : Blo 251819 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B568169 : Blo 251819 568169 := bstep (se 2 (by rfl) ⟨213063, by rfl⟩ : syracuseStep 568169 = 426127) B426127
theorem B863135 : Blo 251819 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B2730995 : Blo 251819 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B2731427 : Blo 251819 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2043575 : Blo 251819 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B569339 : Blo 251819 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B11088089 : Blo 251819 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B569627 : Blo 251819 569627 := bstep (se 1 (by rfl) ⟨427220, by rfl⟩ : syracuseStep 569627 = 854441) B854441
theorem B962887 : Blo 251819 962887 := bstep (se 1 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 962887 = 1444331) B1444331
theorem B1290815 : Blo 251819 1290815 := bstep (se 1 (by rfl) ⟨968111, by rfl⟩ : syracuseStep 1290815 = 1936223) B1936223
theorem B570023 : Blo 251819 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B735209 : Blo 251819 735209 := bstep (se 2 (by rfl) ⟨275703, by rfl⟩ : syracuseStep 735209 = 551407) B551407
theorem B571643 : Blo 251819 571643 := bstep (se 1 (by rfl) ⟨428732, by rfl⟩ : syracuseStep 571643 = 857465) B857465
theorem B1227575 : Blo 251819 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B573353 : Blo 251819 573353 := bstep (se 2 (by rfl) ⟨215007, by rfl⟩ : syracuseStep 573353 = 430015) B430015
theorem B573857 : Blo 251819 573857 := bstep (se 2 (by rfl) ⟨215196, by rfl⟩ : syracuseStep 573857 = 430393) B430393
theorem B1295129 : Blo 251819 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B574271 : Blo 251819 574271 := bstep (se 1 (by rfl) ⟨430703, by rfl⟩ : syracuseStep 574271 = 861407) B861407
theorem B1164203 : Blo 251819 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B2442311 : Blo 251819 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B574631 : Blo 251819 574631 := bstep (se 1 (by rfl) ⟨430973, by rfl⟩ : syracuseStep 574631 = 861947) B861947
theorem B640183 : Blo 251819 640183 := bstep (se 1 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 640183 = 960275) B960275
theorem B378107 : Blo 251819 378107 := bstep (se 1 (by rfl) ⟨283580, by rfl⟩ : syracuseStep 378107 = 567161) B567161
theorem B2606345 : Blo 251819 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B574739 : Blo 251819 574739 := bstep (se 1 (by rfl) ⟨431054, by rfl⟩ : syracuseStep 574739 = 862109) B862109
theorem B640649 : Blo 251819 640649 := bstep (se 2 (by rfl) ⟨240243, by rfl⟩ : syracuseStep 640649 = 480487) B480487
theorem B378599 : Blo 251819 378599 := bstep (se 1 (by rfl) ⟨283949, by rfl⟩ : syracuseStep 378599 = 567899) B567899
theorem B5293811 : Blo 251819 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B575315 : Blo 251819 575315 := bstep (se 1 (by rfl) ⟨431486, by rfl⟩ : syracuseStep 575315 = 862973) B862973
theorem B378791 : Blo 251819 378791 := bstep (se 1 (by rfl) ⟨284093, by rfl⟩ : syracuseStep 378791 = 568187) B568187
theorem B969191 : Blo 251819 969191 := bstep (se 1 (by rfl) ⟨726893, by rfl⟩ : syracuseStep 969191 = 1453787) B1453787
theorem B379439 : Blo 251819 379439 := bstep (se 1 (by rfl) ⟨284579, by rfl⟩ : syracuseStep 379439 = 569159) B569159
theorem B379625 : Blo 251819 379625 := bstep (se 2 (by rfl) ⟨142359, by rfl⟩ : syracuseStep 379625 = 284719) B284719
theorem B379679 : Blo 251819 379679 := bstep (se 1 (by rfl) ⟨284759, by rfl⟩ : syracuseStep 379679 = 569519) B569519
theorem B641915 : Blo 251819 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B380009 : Blo 251819 380009 := bstep (se 2 (by rfl) ⟨142503, by rfl⟩ : syracuseStep 380009 = 285007) B285007
theorem B642239 : Blo 251819 642239 := bstep (se 1 (by rfl) ⟨481679, by rfl⟩ : syracuseStep 642239 = 963359) B963359
theorem B3526507 : Blo 251819 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B380783 : Blo 251819 380783 := bstep (se 1 (by rfl) ⟨285587, by rfl⟩ : syracuseStep 380783 = 571175) B571175
theorem B3264461 : Blo 251819 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B380969 : Blo 251819 380969 := bstep (se 2 (by rfl) ⟨142863, by rfl⟩ : syracuseStep 380969 = 285727) B285727
theorem B643727 : Blo 251819 643727 := bstep (se 1 (by rfl) ⟨482795, by rfl⟩ : syracuseStep 643727 = 965591) B965591
theorem B18764435 : Blo 251819 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B2183993 : Blo 251819 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B2184677 : Blo 251819 2184677 := bstep (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) B409627
theorem B2446843 : Blo 251819 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B1922615 : Blo 251819 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B16570169 : Blo 251819 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B252263 : Blo 251819 252263 := bstep (se 1 (by rfl) ⟨189197, by rfl⟩ : syracuseStep 252263 = 378395) B378395
theorem B252351 : Blo 251819 252351 := bstep (se 1 (by rfl) ⟨189263, by rfl⟩ : syracuseStep 252351 = 378527) B378527
theorem B383579 : Blo 251819 383579 := bstep (se 1 (by rfl) ⟨287684, by rfl⟩ : syracuseStep 383579 = 575369) B575369
theorem B252543 : Blo 251819 252543 := bstep (se 1 (by rfl) ⟨189407, by rfl⟩ : syracuseStep 252543 = 378815) B378815
theorem B383657 : Blo 251819 383657 := bstep (se 2 (by rfl) ⟨143871, by rfl⟩ : syracuseStep 383657 = 287743) B287743
theorem B4905683 : Blo 251819 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B285403 : Blo 251819 285403 := bstep (se 1 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 285403 = 428105) B428105
theorem B285691 : Blo 251819 285691 := bstep (se 1 (by rfl) ⟨214268, by rfl⟩ : syracuseStep 285691 = 428537) B428537
theorem B646319 : Blo 251819 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B253407 : Blo 251819 253407 := bstep (se 1 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 253407 = 380111) B380111
theorem B253487 : Blo 251819 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B319079 : Blo 251819 319079 := bstep (se 1 (by rfl) ⟨239309, by rfl⟩ : syracuseStep 319079 = 478619) B478619
theorem B253759 : Blo 251819 253759 := bstep (se 1 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 253759 = 380639) B380639
theorem B253999 : Blo 251819 253999 := bstep (se 1 (by rfl) ⟨190499, by rfl⟩ : syracuseStep 253999 = 380999) B380999
theorem B3465287 : Blo 251819 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B254079 : Blo 251819 254079 := bstep (se 1 (by rfl) ⟨190559, by rfl⟩ : syracuseStep 254079 = 381119) B381119
theorem B254175 : Blo 251819 254175 := bstep (se 1 (by rfl) ⟨190631, by rfl⟩ : syracuseStep 254175 = 381263) B381263
theorem B483563 : Blo 251819 483563 := bstep (se 1 (by rfl) ⟨362672, by rfl⟩ : syracuseStep 483563 = 725345) B725345
theorem B254203 : Blo 251819 254203 := bstep (se 1 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 254203 = 381305) B381305
theorem B5464493 : Blo 251819 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B254399 : Blo 251819 254399 := bstep (se 1 (by rfl) ⟨190799, by rfl⟩ : syracuseStep 254399 = 381599) B381599
theorem B254619 : Blo 251819 254619 := bstep (se 1 (by rfl) ⟨190964, by rfl⟩ : syracuseStep 254619 = 381929) B381929
theorem B2908831 : Blo 251819 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B254655 : Blo 251819 254655 := bstep (se 1 (by rfl) ⟨190991, by rfl⟩ : syracuseStep 254655 = 381983) B381983
theorem B254847 : Blo 251819 254847 := bstep (se 1 (by rfl) ⟨191135, by rfl⟩ : syracuseStep 254847 = 382271) B382271
theorem B2319673 : Blo 251819 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B485119 : Blo 251819 485119 := bstep (se 1 (by rfl) ⟨363839, by rfl⟩ : syracuseStep 485119 = 727679) B727679
theorem B616319 : Blo 251819 616319 := bstep (se 1 (by rfl) ⟨462239, by rfl⟩ : syracuseStep 616319 = 924479) B924479
theorem B2746781 : Blo 251819 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B10972043 : Blo 251819 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B4090783 : Blo 251819 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B682921 : Blo 251819 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B2158433 : Blo 251819 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B717599 : Blo 251819 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B1078073 : Blo 251819 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B1274939 : Blo 251819 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B4945049 : Blo 251819 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B1275263 : Blo 251819 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B1373755 : Blo 251819 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B2160209 : Blo 251819 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B1865423 : Blo 251819 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B4093757 : Blo 251819 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B1276073 : Blo 251819 1276073 := bstep (se 2 (by rfl) ⟨478527, by rfl⟩ : syracuseStep 1276073 = 957055) B957055
theorem B358759 : Blo 251819 358759 := bstep (se 1 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 358759 = 538139) B538139
theorem B6191639 : Blo 251819 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B5175845 : Blo 251819 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B851255 : Blo 251819 851255 := bstep (se 1 (by rfl) ⟨638441, by rfl⟩ : syracuseStep 851255 = 1276883) B1276883
theorem B359807 : Blo 251819 359807 := bstep (se 1 (by rfl) ⟨269855, by rfl⟩ : syracuseStep 359807 = 539711) B539711
theorem B1179049 : Blo 251819 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B2490209 : Blo 251819 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B6521633 : Blo 251819 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B1737563 : Blo 251819 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B427099 : Blo 251819 427099 := bstep (se 1 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 427099 = 640649) B640649
theorem B853577 : Blo 251819 853577 := bstep (se 2 (by rfl) ⟨320091, by rfl⟩ : syracuseStep 853577 = 640183) B640183
theorem B427943 : Blo 251819 427943 := bstep (se 1 (by rfl) ⟨320957, by rfl⟩ : syracuseStep 427943 = 641915) B641915
theorem B428159 : Blo 251819 428159 := bstep (se 1 (by rfl) ⟨321119, by rfl⟩ : syracuseStep 428159 = 642239) B642239
theorem B429151 : Blo 251819 429151 := bstep (se 1 (by rfl) ⟨321863, by rfl⟩ : syracuseStep 429151 = 643727) B643727
theorem B1281257 : Blo 251819 1281257 := bstep (se 2 (by rfl) ⟨480471, by rfl⟩ : syracuseStep 1281257 = 960943) B960943
theorem B1281743 : Blo 251819 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B11046779 : Blo 251819 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B430879 : Blo 251819 430879 := bstep (se 1 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 430879 = 646319) B646319
theorem B856871 : Blo 251819 856871 := bstep (se 1 (by rfl) ⟨642653, by rfl⟩ : syracuseStep 856871 = 1285307) B1285307
theorem B3642245 : Blo 251819 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B726175 : Blo 251819 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B3642995 : Blo 251819 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B1283849 : Blo 251819 1283849 := bstep (se 2 (by rfl) ⟨481443, by rfl⟩ : syracuseStep 1283849 = 962887) B962887
theorem B12327983 : Blo 251819 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B6495389 : Blo 251819 6495389 := bstep (se 3 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 6495389 = 2435771) B2435771
theorem B7314695 : Blo 251819 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B860543 : Blo 251819 860543 := bstep (se 1 (by rfl) ⟨645407, by rfl⟩ : syracuseStep 860543 = 1290815) B1290815
theorem B959485 : Blo 251819 959485 := bstep (se 3 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 959485 = 359807) B359807
theorem B2729171 : Blo 251819 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B3450563 : Blo 251819 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B567503 : Blo 251819 567503 := bstep (se 1 (by rfl) ⟨425627, by rfl⟩ : syracuseStep 567503 = 851255) B851255
theorem B3878441 : Blo 251819 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B962219 : Blo 251819 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B962387 : Blo 251819 962387 := bstep (se 1 (by rfl) ⟨721790, by rfl⟩ : syracuseStep 962387 = 1443581) B1443581
theorem B962401 : Blo 251819 962401 := bstep (se 2 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 962401 = 721801) B721801
theorem B3092897 : Blo 251819 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B1913381 : Blo 251819 1913381 := bstep (se 4 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 1913381 = 358759) B358759
theorem B3453677 : Blo 251819 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B2176307 : Blo 251819 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B1455995 : Blo 251819 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B1456451 : Blo 251819 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B768359 : Blo 251819 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B965135 : Blo 251819 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B5454377 : Blo 251819 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B572489 : Blo 251819 572489 := bstep (se 2 (by rfl) ⟨214683, by rfl⟩ : syracuseStep 572489 = 429367) B429367
theorem B1293407 : Blo 251819 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B573119 : Blo 251819 573119 := bstep (se 1 (by rfl) ⟨429839, by rfl⟩ : syracuseStep 573119 = 859679) B859679
theorem B4702009 : Blo 251819 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B2310191 : Blo 251819 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B967049 : Blo 251819 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B377927 : Blo 251819 377927 := bstep (se 1 (by rfl) ⟨283445, by rfl⟩ : syracuseStep 377927 = 566891) B566891
theorem B574559 : Blo 251819 574559 := bstep (se 1 (by rfl) ⟨430919, by rfl⟩ : syracuseStep 574559 = 861839) B861839
theorem B410879 : Blo 251819 410879 := bstep (se 1 (by rfl) ⟨308159, by rfl⟩ : syracuseStep 410879 = 616319) B616319
theorem B640487 : Blo 251819 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B378695 : Blo 251819 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B378779 : Blo 251819 378779 := bstep (se 1 (by rfl) ⟨284084, by rfl⟩ : syracuseStep 378779 = 568169) B568169
theorem B575423 : Blo 251819 575423 := bstep (se 1 (by rfl) ⟨431567, by rfl⟩ : syracuseStep 575423 = 863135) B863135
theorem B1820663 : Blo 251819 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B3262457 : Blo 251819 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1820951 : Blo 251819 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B1362383 : Blo 251819 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B379559 : Blo 251819 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B7392059 : Blo 251819 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B379751 : Blo 251819 379751 := bstep (se 1 (by rfl) ⟨284813, by rfl⟩ : syracuseStep 379751 = 569627) B569627
theorem B380015 : Blo 251819 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B478399 : Blo 251819 478399 := bstep (se 1 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 478399 = 717599) B717599
theorem B3296699 : Blo 251819 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B1756669 : Blo 251819 1756669 := bstep (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) B658751
theorem B380537 : Blo 251819 380537 := bstep (se 2 (by rfl) ⟨142701, by rfl⟩ : syracuseStep 380537 = 285403) B285403
theorem B380921 : Blo 251819 380921 := bstep (se 2 (by rfl) ⟨142845, by rfl⟩ : syracuseStep 380921 = 285691) B285691
theorem B381095 : Blo 251819 381095 := bstep (se 1 (by rfl) ⟨285821, by rfl⟩ : syracuseStep 381095 = 571643) B571643
theorem B1660139 : Blo 251819 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B382235 : Blo 251819 382235 := bstep (se 1 (by rfl) ⟨286676, by rfl⟩ : syracuseStep 382235 = 573353) B573353
theorem B382571 : Blo 251819 382571 := bstep (se 1 (by rfl) ⟨286928, by rfl⟩ : syracuseStep 382571 = 573857) B573857
theorem B382847 : Blo 251819 382847 := bstep (se 1 (by rfl) ⟨287135, by rfl⟩ : syracuseStep 382847 = 574271) B574271
theorem B776135 : Blo 251819 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B1628207 : Blo 251819 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B383087 : Blo 251819 383087 := bstep (se 1 (by rfl) ⟨287315, by rfl⟩ : syracuseStep 383087 = 574631) B574631
theorem B252071 : Blo 251819 252071 := bstep (se 1 (by rfl) ⟨189053, by rfl⟩ : syracuseStep 252071 = 378107) B378107
theorem B383159 : Blo 251819 383159 := bstep (se 1 (by rfl) ⟨287369, by rfl⟩ : syracuseStep 383159 = 574739) B574739
theorem B252399 : Blo 251819 252399 := bstep (se 1 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 252399 = 378599) B378599
theorem B3529207 : Blo 251819 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B383543 : Blo 251819 383543 := bstep (se 1 (by rfl) ⟨287657, by rfl⟩ : syracuseStep 383543 = 575315) B575315
theorem B252527 : Blo 251819 252527 := bstep (se 1 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 252527 = 378791) B378791
theorem B646127 : Blo 251819 646127 := bstep (se 1 (by rfl) ⟨484595, by rfl⟩ : syracuseStep 646127 = 969191) B969191
theorem B252959 : Blo 251819 252959 := bstep (se 1 (by rfl) ⟨189719, by rfl⟩ : syracuseStep 252959 = 379439) B379439
theorem B253083 : Blo 251819 253083 := bstep (se 1 (by rfl) ⟨189812, by rfl⟩ : syracuseStep 253083 = 379625) B379625
theorem B285871 : Blo 251819 285871 := bstep (se 1 (by rfl) ⟨214403, by rfl⟩ : syracuseStep 285871 = 428807) B428807
theorem B253119 : Blo 251819 253119 := bstep (se 1 (by rfl) ⟨189839, by rfl⟩ : syracuseStep 253119 = 379679) B379679
theorem B253339 : Blo 251819 253339 := bstep (se 1 (by rfl) ⟨190004, by rfl⟩ : syracuseStep 253339 = 380009) B380009
theorem B646825 : Blo 251819 646825 := bstep (se 2 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 646825 = 485119) B485119
theorem B4874003 : Blo 251819 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B253855 : Blo 251819 253855 := bstep (se 1 (by rfl) ⟨190391, by rfl⟩ : syracuseStep 253855 = 380783) B380783
theorem B253979 : Blo 251819 253979 := bstep (se 1 (by rfl) ⟨190484, by rfl⟩ : syracuseStep 253979 = 380969) B380969
theorem B483707 : Blo 251819 483707 := bstep (se 1 (by rfl) ⟨362780, by rfl⟩ : syracuseStep 483707 = 725561) B725561
theorem B12509623 : Blo 251819 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B483995 : Blo 251819 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B287527 : Blo 251819 287527 := bstep (se 1 (by rfl) ⟨215645, by rfl⟩ : syracuseStep 287527 = 431291) B431291
theorem B287551 : Blo 251819 287551 := bstep (se 1 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 287551 = 431327) B431327
theorem B484679 : Blo 251819 484679 := bstep (se 1 (by rfl) ⟨363509, by rfl⟩ : syracuseStep 484679 = 727019) B727019
theorem B812539 : Blo 251819 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B255719 : Blo 251819 255719 := bstep (se 1 (by rfl) ⟨191789, by rfl⟩ : syracuseStep 255719 = 383579) B383579
theorem B255771 : Blo 251819 255771 := bstep (se 1 (by rfl) ⟨191828, by rfl⟩ : syracuseStep 255771 = 383657) B383657
theorem B3270455 : Blo 251819 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B485651 : Blo 251819 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B322375 : Blo 251819 322375 := bstep (se 1 (by rfl) ⟨241781, by rfl⟩ : syracuseStep 322375 = 483563) B483563
theorem B1831187 : Blo 251819 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1831673 : Blo 251819 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1438955 : Blo 251819 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B718715 : Blo 251819 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B849959 : Blo 251819 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B850175 : Blo 251819 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B1440139 : Blo 251819 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B1243615 : Blo 251819 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B490139 : Blo 251819 490139 := bstep (se 1 (by rfl) ⟨367604, by rfl⟩ : syracuseStep 490139 = 735209) B735209
theorem B850715 : Blo 251819 850715 := bstep (se 1 (by rfl) ⟨638036, by rfl⟩ : syracuseStep 850715 = 1276073) B1276073
theorem B850877 : Blo 251819 850877 := bstep (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) B319079
theorem B4127759 : Blo 251819 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B818383 : Blo 251819 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1572065 : Blo 251819 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1540127 : Blo 251819 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B426991 : Blo 251819 426991 := bstep (se 1 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 426991 = 640487) B640487
theorem B1213775 : Blo 251819 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B1279313 : Blo 251819 1279313 := bstep (se 2 (by rfl) ⟨479742, by rfl⟩ : syracuseStep 1279313 = 959485) B959485
theorem B1213967 : Blo 251819 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B4884461 : Blo 251819 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B1083385 : Blo 251819 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B854171 : Blo 251819 854171 := bstep (se 1 (by rfl) ⟨640628, by rfl⟩ : syracuseStep 854171 = 1281257) B1281257
theorem B66717989 : Blo 251819 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B2197799 : Blo 251819 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B854495 : Blo 251819 854495 := bstep (se 1 (by rfl) ⟨640871, by rfl⟩ : syracuseStep 854495 = 1281743) B1281743
theorem B7277789 : Blo 251819 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B2428163 : Blo 251819 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B2428663 : Blo 251819 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B429833 : Blo 251819 429833 := bstep (se 2 (by rfl) ⟨161187, by rfl⟩ : syracuseStep 429833 = 322375) B322375
theorem B855899 : Blo 251819 855899 := bstep (se 1 (by rfl) ⟨641924, by rfl⟩ : syracuseStep 855899 = 1283849) B1283849
theorem B1085471 : Blo 251819 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B430751 : Blo 251819 430751 := bstep (se 1 (by rfl) ⟨323063, by rfl⟩ : syracuseStep 430751 = 646127) B646127
theorem B4330259 : Blo 251819 4330259 := bstep (se 1 (by rfl) ⟨3247694, by rfl⟩ : syracuseStep 4330259 = 6495389) B6495389
theorem B1283201 : Blo 251819 1283201 := bstep (se 2 (by rfl) ⟨481200, by rfl⟩ : syracuseStep 1283201 = 962401) B962401
theorem B3249335 : Blo 251819 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2300375 : Blo 251819 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B1220791 : Blo 251819 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B2302451 : Blo 251819 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B959303 : Blo 251819 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B1450871 : Blo 251819 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B566639 : Blo 251819 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B566783 : Blo 251819 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B1091177 : Blo 251819 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B567143 : Blo 251819 567143 := bstep (se 1 (by rfl) ⟨425357, by rfl⟩ : syracuseStep 567143 = 850715) B850715
theorem B567251 : Blo 251819 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B862271 : Blo 251819 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B862433 : Blo 251819 862433 := bstep (se 2 (by rfl) ⟨323412, by rfl⟩ : syracuseStep 862433 = 646825) B646825
theorem B6269345 : Blo 251819 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B569051 : Blo 251819 569051 := bstep (se 1 (by rfl) ⟨426788, by rfl⟩ : syracuseStep 569051 = 853577) B853577
theorem B2174971 : Blo 251819 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B569465 : Blo 251819 569465 := bstep (se 2 (by rfl) ⟨213549, by rfl⟩ : syracuseStep 569465 = 427099) B427099
theorem B1290653 : Blo 251819 1290653 := bstep (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) B483995
theorem B4928039 : Blo 251819 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B571247 : Blo 251819 571247 := bstep (se 1 (by rfl) ⟨428435, by rfl⟩ : syracuseStep 571247 = 856871) B856871
theorem B1095677 : Blo 251819 1095677 := bstep (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) B410879
theorem B572201 : Blo 251819 572201 := bstep (se 2 (by rfl) ⟨214575, by rfl⟩ : syracuseStep 572201 = 429151) B429151
theorem B637865 : Blo 251819 637865 := bstep (se 2 (by rfl) ⟨239199, by rfl⟩ : syracuseStep 637865 = 478399) B478399
theorem B2342225 : Blo 251819 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B573695 : Blo 251819 573695 := bstep (se 1 (by rfl) ⟨430271, by rfl⟩ : syracuseStep 573695 = 860543) B860543
theorem B574505 : Blo 251819 574505 := bstep (se 2 (by rfl) ⟨215439, by rfl⟩ : syracuseStep 574505 = 430879) B430879
theorem B2180303 : Blo 251819 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B378335 : Blo 251819 378335 := bstep (se 1 (by rfl) ⟨283751, by rfl⟩ : syracuseStep 378335 = 567503) B567503
theorem B968233 : Blo 251819 968233 := bstep (se 2 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 968233 = 726175) B726175
theorem B641479 : Blo 251819 641479 := bstep (se 1 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 641479 = 962219) B962219
theorem B641591 : Blo 251819 641591 := bstep (se 1 (by rfl) ⟨481193, by rfl⟩ : syracuseStep 641591 = 962387) B962387
theorem B1920185 : Blo 251819 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B1658153 : Blo 251819 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B4705609 : Blo 251819 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B18534005 : Blo 251819 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B479143 : Blo 251819 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B970663 : Blo 251819 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B970967 : Blo 251819 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B381161 : Blo 251819 381161 := bstep (se 2 (by rfl) ⟨142935, by rfl⟩ : syracuseStep 381161 = 285871) B285871
theorem B512239 : Blo 251819 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B643423 : Blo 251819 643423 := bstep (se 1 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 643423 = 965135) B965135
theorem B381659 : Blo 251819 381659 := bstep (se 1 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 381659 = 572489) B572489
theorem B382079 : Blo 251819 382079 := bstep (se 1 (by rfl) ⟨286559, by rfl⟩ : syracuseStep 382079 = 573119) B573119
theorem B644699 : Blo 251819 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B4347755 : Blo 251819 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B251951 : Blo 251819 251951 := bstep (se 1 (by rfl) ⟨188963, by rfl⟩ : syracuseStep 251951 = 377927) B377927
theorem B383039 : Blo 251819 383039 := bstep (se 1 (by rfl) ⟨287279, by rfl⟩ : syracuseStep 383039 = 574559) B574559
theorem B383369 : Blo 251819 383369 := bstep (se 2 (by rfl) ⟨143763, by rfl⟩ : syracuseStep 383369 = 287527) B287527
theorem B383401 : Blo 251819 383401 := bstep (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) B287551
theorem B252463 : Blo 251819 252463 := bstep (se 1 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 252463 = 378695) B378695
theorem B252519 : Blo 251819 252519 := bstep (se 1 (by rfl) ⟨189389, by rfl⟩ : syracuseStep 252519 = 378779) B378779
theorem B285295 : Blo 251819 285295 := bstep (se 1 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 285295 = 427943) B427943
theorem B383615 : Blo 251819 383615 := bstep (se 1 (by rfl) ⟨287711, by rfl⟩ : syracuseStep 383615 = 575423) B575423
theorem B285439 : Blo 251819 285439 := bstep (se 1 (by rfl) ⟨214079, by rfl⟩ : syracuseStep 285439 = 428159) B428159
theorem B908255 : Blo 251819 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B253039 : Blo 251819 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B253167 : Blo 251819 253167 := bstep (se 1 (by rfl) ⟨189875, by rfl⟩ : syracuseStep 253167 = 379751) B379751
theorem B253343 : Blo 251819 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B253691 : Blo 251819 253691 := bstep (se 1 (by rfl) ⟨190268, by rfl⟩ : syracuseStep 253691 = 380537) B380537
theorem B7364519 : Blo 251819 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B253947 : Blo 251819 253947 := bstep (se 1 (by rfl) ⟨190460, by rfl⟩ : syracuseStep 253947 = 380921) B380921
theorem B254063 : Blo 251819 254063 := bstep (se 1 (by rfl) ⟨190547, by rfl⟩ : syracuseStep 254063 = 381095) B381095
theorem B1106759 : Blo 251819 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B254823 : Blo 251819 254823 := bstep (se 1 (by rfl) ⟨191117, by rfl⟩ : syracuseStep 254823 = 382235) B382235
theorem B255047 : Blo 251819 255047 := bstep (se 1 (by rfl) ⟨191285, by rfl⟩ : syracuseStep 255047 = 382571) B382571
theorem B255231 : Blo 251819 255231 := bstep (se 1 (by rfl) ⟨191423, by rfl⟩ : syracuseStep 255231 = 382847) B382847
theorem B517423 : Blo 251819 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B255391 : Blo 251819 255391 := bstep (se 1 (by rfl) ⟨191543, by rfl⟩ : syracuseStep 255391 = 383087) B383087
theorem B255439 : Blo 251819 255439 := bstep (se 1 (by rfl) ⟨191579, by rfl⟩ : syracuseStep 255439 = 383159) B383159
theorem B255695 : Blo 251819 255695 := bstep (se 1 (by rfl) ⟨191771, by rfl⟩ : syracuseStep 255695 = 383543) B383543
theorem B8218655 : Blo 251819 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4876463 : Blo 251819 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B322471 : Blo 251819 322471 := bstep (se 1 (by rfl) ⟨241853, by rfl⟩ : syracuseStep 322471 = 483707) B483707
theorem B323119 : Blo 251819 323119 := bstep (se 1 (by rfl) ⟨242339, by rfl⟩ : syracuseStep 323119 = 484679) B484679
theorem B323767 : Blo 251819 323767 := bstep (se 1 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 323767 = 485651) B485651
theorem B2585627 : Blo 251819 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B2061931 : Blo 251819 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1275587 : Blo 251819 1275587 := bstep (se 1 (by rfl) ⟨956690, by rfl⟩ : syracuseStep 1275587 = 1913381) B1913381
theorem B3636251 : Blo 251819 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B326759 : Blo 251819 326759 := bstep (se 1 (by rfl) ⟨245069, by rfl⟩ : syracuseStep 326759 = 490139) B490139
theorem B2751839 : Blo 251819 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B1048043 : Blo 251819 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B852875 : Blo 251819 852875 := bstep (se 1 (by rfl) ⟨639656, by rfl⟩ : syracuseStep 852875 = 1279313) B1279313
theorem B427727 : Blo 251819 427727 := bstep (se 1 (by rfl) ⟨320795, by rfl⟩ : syracuseStep 427727 = 641591) B641591
theorem B689897 : Blo 251819 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B1280123 : Blo 251819 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B4851859 : Blo 251819 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B12356003 : Blo 251819 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B1444513 : Blo 251819 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B723647 : Blo 251819 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B2886839 : Blo 251819 2886839 := bstep (se 1 (by rfl) ⟨2165129, by rfl⟩ : syracuseStep 2886839 = 4330259) B4330259
theorem B855305 : Blo 251819 855305 := bstep (se 2 (by rfl) ⟨320739, by rfl⟩ : syracuseStep 855305 = 641479) B641479
theorem B855467 : Blo 251819 855467 := bstep (se 1 (by rfl) ⟨641600, by rfl⟩ : syracuseStep 855467 = 1283201) B1283201
theorem B2166223 : Blo 251819 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B429799 : Blo 251819 429799 := bstep (se 1 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 429799 = 644699) B644699
theorem B429961 : Blo 251819 429961 := bstep (se 2 (by rfl) ⟨161235, by rfl⟩ : syracuseStep 429961 = 322471) B322471
theorem B430825 : Blo 251819 430825 := bstep (se 2 (by rfl) ⟨161559, by rfl⟩ : syracuseStep 430825 = 323119) B323119
theorem B431689 : Blo 251819 431689 := bstep (se 2 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 431689 = 323767) B323767
theorem B857897 : Blo 251819 857897 := bstep (se 2 (by rfl) ⟨321711, by rfl⟩ : syracuseStep 857897 = 643423) B643423
theorem B727451 : Blo 251819 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B5479103 : Blo 251819 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B3250975 : Blo 251819 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B860435 : Blo 251819 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B3285359 : Blo 251819 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B2794781 : Blo 251819 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B730451 : Blo 251819 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B1026751 : Blo 251819 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B1453535 : Blo 251819 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B569321 : Blo 251819 569321 := bstep (se 2 (by rfl) ⟨213495, by rfl⟩ : syracuseStep 569321 = 426991) B426991
theorem B3256307 : Blo 251819 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B569447 : Blo 251819 569447 := bstep (se 1 (by rfl) ⟨427085, by rfl⟩ : syracuseStep 569447 = 854171) B854171
theorem B44478659 : Blo 251819 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B569663 : Blo 251819 569663 := bstep (se 1 (by rfl) ⟨427247, by rfl⟩ : syracuseStep 569663 = 854495) B854495
theorem B1290977 : Blo 251819 1290977 := bstep (se 2 (by rfl) ⟨484116, by rfl⟩ : syracuseStep 1290977 = 968233) B968233
theorem B1618775 : Blo 251819 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B570599 : Blo 251819 570599 := bstep (se 1 (by rfl) ⟨427949, by rfl⟩ : syracuseStep 570599 = 855899) B855899
theorem B2898503 : Blo 251819 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B6274145 : Blo 251819 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B605503 : Blo 251819 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B638857 : Blo 251819 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B1294217 : Blo 251819 1294217 := bstep (se 2 (by rfl) ⟨485331, by rfl⟩ : syracuseStep 1294217 = 970663) B970663
theorem B2899961 : Blo 251819 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B639535 : Blo 251819 639535 := bstep (se 1 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 639535 = 959303) B959303
theorem B737839 : Blo 251819 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B967247 : Blo 251819 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B377759 : Blo 251819 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B377855 : Blo 251819 377855 := bstep (se 1 (by rfl) ⟨283391, by rfl⟩ : syracuseStep 377855 = 566783) B566783
theorem B378095 : Blo 251819 378095 := bstep (se 1 (by rfl) ⟨283571, by rfl⟩ : syracuseStep 378095 = 567143) B567143
theorem B378167 : Blo 251819 378167 := bstep (se 1 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 378167 = 567251) B567251
theorem B574847 : Blo 251819 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B574955 : Blo 251819 574955 := bstep (se 1 (by rfl) ⟨431216, by rfl⟩ : syracuseStep 574955 = 862433) B862433
theorem B4179563 : Blo 251819 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B379367 : Blo 251819 379367 := bstep (se 1 (by rfl) ⟨284525, by rfl⟩ : syracuseStep 379367 = 569051) B569051
theorem B379643 : Blo 251819 379643 := bstep (se 1 (by rfl) ⟨284732, by rfl⟩ : syracuseStep 379643 = 569465) B569465
theorem B871357 : Blo 251819 871357 := bstep (se 3 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 871357 = 326759) B326759
theorem B511201 : Blo 251819 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B1723751 : Blo 251819 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B380393 : Blo 251819 380393 := bstep (se 2 (by rfl) ⟨142647, by rfl⟩ : syracuseStep 380393 = 285295) B285295
theorem B380585 : Blo 251819 380585 := bstep (se 2 (by rfl) ⟨142719, by rfl⟩ : syracuseStep 380585 = 285439) B285439
theorem B380831 : Blo 251819 380831 := bstep (se 1 (by rfl) ⟨285623, by rfl⟩ : syracuseStep 380831 = 571247) B571247
theorem B381467 : Blo 251819 381467 := bstep (se 1 (by rfl) ⟨286100, by rfl⟩ : syracuseStep 381467 = 572201) B572201
theorem B1561483 : Blo 251819 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B382463 : Blo 251819 382463 := bstep (se 1 (by rfl) ⟨286847, by rfl⟩ : syracuseStep 382463 = 573695) B573695
theorem B1627721 : Blo 251819 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B383003 : Blo 251819 383003 := bstep (se 1 (by rfl) ⟨287252, by rfl⟩ : syracuseStep 383003 = 574505) B574505
theorem B809183 : Blo 251819 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B252223 : Blo 251819 252223 := bstep (se 1 (by rfl) ⟨189167, by rfl⟩ : syracuseStep 252223 = 378335) B378335
theorem B809311 : Blo 251819 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B1465199 : Blo 251819 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B1105435 : Blo 251819 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B286555 : Blo 251819 286555 := bstep (se 1 (by rfl) ⟨214916, by rfl⟩ : syracuseStep 286555 = 429833) B429833
theorem B647311 : Blo 251819 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B254107 : Blo 251819 254107 := bstep (se 1 (by rfl) ⟨190580, by rfl⟩ : syracuseStep 254107 = 381161) B381161
theorem B287167 : Blo 251819 287167 := bstep (se 1 (by rfl) ⟨215375, by rfl⟩ : syracuseStep 287167 = 430751) B430751
theorem B254439 : Blo 251819 254439 := bstep (se 1 (by rfl) ⟨190829, by rfl⟩ : syracuseStep 254439 = 381659) B381659
theorem B254719 : Blo 251819 254719 := bstep (se 1 (by rfl) ⟨191039, by rfl⟩ : syracuseStep 254719 = 382079) B382079
theorem B255359 : Blo 251819 255359 := bstep (se 1 (by rfl) ⟨191519, by rfl⟩ : syracuseStep 255359 = 383039) B383039
theorem B255579 : Blo 251819 255579 := bstep (se 1 (by rfl) ⟨191684, by rfl⟩ : syracuseStep 255579 = 383369) B383369
theorem B1533583 : Blo 251819 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B255743 : Blo 251819 255743 := bstep (se 1 (by rfl) ⟨191807, by rfl⟩ : syracuseStep 255743 = 383615) B383615
theorem B3238217 : Blo 251819 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B4909679 : Blo 251819 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B682985 : Blo 251819 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B1534967 : Blo 251819 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B2749241 : Blo 251819 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B850391 : Blo 251819 850391 := bstep (se 1 (by rfl) ⟨637793, by rfl⟩ : syracuseStep 850391 = 1275587) B1275587
theorem B425243 : Blo 251819 425243 := bstep (se 1 (by rfl) ⟨318932, by rfl⟩ : syracuseStep 425243 = 637865) B637865
theorem B2424167 : Blo 251819 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B1834559 : Blo 251819 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B852713 : Blo 251819 852713 := bstep (se 2 (by rfl) ⟨319767, by rfl⟩ : syracuseStep 852713 = 639535) B639535
theorem B2786375 : Blo 251819 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B459931 : Blo 251819 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B853415 : Blo 251819 853415 := bstep (se 1 (by rfl) ⟨640061, by rfl⟩ : syracuseStep 853415 = 1280123) B1280123
theorem B1149167 : Blo 251819 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B3935141 : Blo 251819 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B1085147 : Blo 251819 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B2888297 : Blo 251819 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B8327909 : Blo 251819 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B2726405 : Blo 251819 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B1023311 : Blo 251819 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B2170871 : Blo 251819 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B860651 : Blo 251819 860651 := bstep (se 1 (by rfl) ⟨645488, by rfl⟩ : syracuseStep 860651 = 1290977) B1290977
theorem B4334633 : Blo 251819 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B566927 : Blo 251819 566927 := bstep (se 1 (by rfl) ⟨425195, by rfl⟩ : syracuseStep 566927 = 850391) B850391
theorem B1616111 : Blo 251819 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B1223039 : Blo 251819 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B862811 : Blo 251819 862811 := bstep (se 1 (by rfl) ⟨647108, by rfl⟩ : syracuseStep 862811 = 1294217) B1294217
theorem B863081 : Blo 251819 863081 := bstep (se 2 (by rfl) ⟨323655, by rfl⟩ : syracuseStep 863081 = 647311) B647311
theorem B568583 : Blo 251819 568583 := bstep (se 1 (by rfl) ⟨426437, by rfl⟩ : syracuseStep 568583 = 852875) B852875
theorem B570203 : Blo 251819 570203 := bstep (se 1 (by rfl) ⟨427652, by rfl⟩ : syracuseStep 570203 = 855305) B855305
theorem B2044777 : Blo 251819 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B570311 : Blo 251819 570311 := bstep (se 1 (by rfl) ⟨427733, by rfl⟩ : syracuseStep 570311 = 855467) B855467
theorem B6469145 : Blo 251819 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B7452749 : Blo 251819 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B571931 : Blo 251819 571931 := bstep (se 1 (by rfl) ⟨428948, by rfl⟩ : syracuseStep 571931 = 857897) B857897
theorem B1161809 : Blo 251819 1161809 := bstep (se 2 (by rfl) ⟨435678, by rfl⟩ : syracuseStep 1161809 = 871357) B871357
theorem B539455 : Blo 251819 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B3652735 : Blo 251819 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B573065 : Blo 251819 573065 := bstep (se 2 (by rfl) ⟨214899, by rfl⟩ : syracuseStep 573065 = 429799) B429799
theorem B573281 : Blo 251819 573281 := bstep (se 2 (by rfl) ⟨214980, by rfl⟩ : syracuseStep 573281 = 429961) B429961
theorem B573623 : Blo 251819 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B574433 : Blo 251819 574433 := bstep (se 2 (by rfl) ⟨215412, by rfl⟩ : syracuseStep 574433 = 430825) B430825
theorem B32949341 : Blo 251819 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B575585 : Blo 251819 575585 := bstep (se 2 (by rfl) ⟨215844, by rfl⟩ : syracuseStep 575585 = 431689) B431689
theorem B969023 : Blo 251819 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B1821293 : Blo 251819 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B379547 : Blo 251819 379547 := bstep (se 1 (by rfl) ⟨284660, by rfl⟩ : syracuseStep 379547 = 569321) B569321
theorem B379631 : Blo 251819 379631 := bstep (se 1 (by rfl) ⟨284723, by rfl⟩ : syracuseStep 379631 = 569447) B569447
theorem B379775 : Blo 251819 379775 := bstep (se 1 (by rfl) ⟨284831, by rfl⟩ : syracuseStep 379775 = 569663) B569663
theorem B380399 : Blo 251819 380399 := bstep (se 1 (by rfl) ⟨285299, by rfl⟩ : syracuseStep 380399 = 570599) B570599
theorem B807337 : Blo 251819 807337 := bstep (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) B605503
theorem B4182763 : Blo 251819 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B283495 : Blo 251819 283495 := bstep (se 1 (by rfl) ⟨212621, by rfl⟩ : syracuseStep 283495 = 425243) B425243
theorem B382073 : Blo 251819 382073 := bstep (se 2 (by rfl) ⟨143277, by rfl⟩ : syracuseStep 382073 = 286555) B286555
theorem B644831 : Blo 251819 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B382889 : Blo 251819 382889 := bstep (se 2 (by rfl) ⟨143583, by rfl⟩ : syracuseStep 382889 = 287167) B287167
theorem B251839 : Blo 251819 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B251903 : Blo 251819 251903 := bstep (se 1 (by rfl) ⟨188927, by rfl⟩ : syracuseStep 251903 = 377855) B377855
theorem B252063 : Blo 251819 252063 := bstep (se 1 (by rfl) ⟨189047, by rfl⟩ : syracuseStep 252063 = 378095) B378095
theorem B252111 : Blo 251819 252111 := bstep (se 1 (by rfl) ⟨189083, by rfl⟩ : syracuseStep 252111 = 378167) B378167
theorem B383231 : Blo 251819 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B383303 : Blo 251819 383303 := bstep (se 1 (by rfl) ⟨287477, by rfl⟩ : syracuseStep 383303 = 574955) B574955
theorem B285151 : Blo 251819 285151 := bstep (se 1 (by rfl) ⟨213863, by rfl⟩ : syracuseStep 285151 = 427727) B427727
theorem B252911 : Blo 251819 252911 := bstep (se 1 (by rfl) ⟨189683, by rfl⟩ : syracuseStep 252911 = 379367) B379367
theorem B482431 : Blo 251819 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B253095 : Blo 251819 253095 := bstep (se 1 (by rfl) ⟨189821, by rfl⟩ : syracuseStep 253095 = 379643) B379643
theorem B1924559 : Blo 251819 1924559 := bstep (se 1 (by rfl) ⟨1443419, by rfl⟩ : syracuseStep 1924559 = 2886839) B2886839
theorem B253595 : Blo 251819 253595 := bstep (se 1 (by rfl) ⟨190196, by rfl⟩ : syracuseStep 253595 = 380393) B380393
theorem B253723 : Blo 251819 253723 := bstep (se 1 (by rfl) ⟨190292, by rfl⟩ : syracuseStep 253723 = 380585) B380585
theorem B253887 : Blo 251819 253887 := bstep (se 1 (by rfl) ⟨190415, by rfl⟩ : syracuseStep 253887 = 380831) B380831
theorem B254311 : Blo 251819 254311 := bstep (se 1 (by rfl) ⟨190733, by rfl⟩ : syracuseStep 254311 = 381467) B381467
theorem B1926017 : Blo 251819 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B1369001 : Blo 251819 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B254975 : Blo 251819 254975 := bstep (se 1 (by rfl) ⟨191231, by rfl⟩ : syracuseStep 254975 = 382463) B382463
theorem B255335 : Blo 251819 255335 := bstep (se 1 (by rfl) ⟨191501, by rfl⟩ : syracuseStep 255335 = 383003) B383003
theorem B484967 : Blo 251819 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B976799 : Blo 251819 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B2190239 : Blo 251819 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B486967 : Blo 251819 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B2158811 : Blo 251819 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B3273119 : Blo 251819 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B29652439 : Blo 251819 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1079081 : Blo 251819 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B1832827 : Blo 251819 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1079183 : Blo 251819 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1932335 : Blo 251819 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B1473913 : Blo 251819 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B851809 : Blo 251819 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B1933307 : Blo 251819 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B1214195 : Blo 251819 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B2623427 : Blo 251819 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B723431 : Blo 251819 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B429887 : Blo 251819 429887 := bstep (se 1 (by rfl) ⟨322415, by rfl⟩ : syracuseStep 429887 = 644831) B644831
theorem B1283039 : Blo 251819 1283039 := bstep (se 1 (by rfl) ⟨962279, by rfl⟩ : syracuseStep 1283039 = 1924559) B1924559
theorem B1447247 : Blo 251819 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B1284011 : Blo 251819 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B2889755 : Blo 251819 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B5577017 : Blo 251819 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B2726369 : Blo 251819 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B2728829 : Blo 251819 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B1288223 : Blo 251819 1288223 := bstep (se 1 (by rfl) ⟨966167, by rfl⟩ : syracuseStep 1288223 = 1932335) B1932335
theorem B1288871 : Blo 251819 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B568475 : Blo 251819 568475 := bstep (se 1 (by rfl) ⟨426356, by rfl⟩ : syracuseStep 568475 = 852713) B852713
theorem B21966227 : Blo 251819 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B568943 : Blo 251819 568943 := bstep (se 1 (by rfl) ⟨426707, by rfl⟩ : syracuseStep 568943 = 853415) B853415
theorem B766111 : Blo 251819 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B5551939 : Blo 251819 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B1293245 : Blo 251819 1293245 := bstep (se 3 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 1293245 = 484967) B484967
theorem B1817603 : Blo 251819 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B573767 : Blo 251819 573767 := bstep (se 1 (by rfl) ⟨430325, by rfl⟩ : syracuseStep 573767 = 860651) B860651
theorem B377951 : Blo 251819 377951 := bstep (se 1 (by rfl) ⟨283463, by rfl⟩ : syracuseStep 377951 = 566927) B566927
theorem B377993 : Blo 251819 377993 := bstep (se 2 (by rfl) ⟨141747, by rfl⟩ : syracuseStep 377993 = 283495) B283495
theorem B575207 : Blo 251819 575207 := bstep (se 1 (by rfl) ⟨431405, by rfl⟩ : syracuseStep 575207 = 862811) B862811
theorem B575387 : Blo 251819 575387 := bstep (se 1 (by rfl) ⟨431540, by rfl⟩ : syracuseStep 575387 = 863081) B863081
theorem B1460159 : Blo 251819 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B39536585 : Blo 251819 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B379055 : Blo 251819 379055 := bstep (se 1 (by rfl) ⟨284291, by rfl⟩ : syracuseStep 379055 = 568583) B568583
theorem B2443769 : Blo 251819 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B2182079 : Blo 251819 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B380135 : Blo 251819 380135 := bstep (se 1 (by rfl) ⟨285101, by rfl⟩ : syracuseStep 380135 = 570203) B570203
theorem B380201 : Blo 251819 380201 := bstep (se 2 (by rfl) ⟨142575, by rfl⟩ : syracuseStep 380201 = 285151) B285151
theorem B380207 : Blo 251819 380207 := bstep (se 1 (by rfl) ⟨285155, by rfl⟩ : syracuseStep 380207 = 570311) B570311
theorem B4312763 : Blo 251819 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B4968499 : Blo 251819 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B4870313 : Blo 251819 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B643241 : Blo 251819 643241 := bstep (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) B482431
theorem B381287 : Blo 251819 381287 := bstep (se 1 (by rfl) ⟨285965, by rfl⟩ : syracuseStep 381287 = 571931) B571931
theorem B774539 : Blo 251819 774539 := bstep (se 1 (by rfl) ⟨580904, by rfl⟩ : syracuseStep 774539 = 1161809) B1161809
theorem B382043 : Blo 251819 382043 := bstep (se 1 (by rfl) ⟨286532, by rfl⟩ : syracuseStep 382043 = 573065) B573065
theorem B1135745 : Blo 251819 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B382187 : Blo 251819 382187 := bstep (se 1 (by rfl) ⟨286640, by rfl⟩ : syracuseStep 382187 = 573281) B573281
theorem B382415 : Blo 251819 382415 := bstep (se 1 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 382415 = 573623) B573623
theorem B382955 : Blo 251819 382955 := bstep (se 1 (by rfl) ⟨287216, by rfl⟩ : syracuseStep 382955 = 574433) B574433
theorem B1857583 : Blo 251819 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B383723 : Blo 251819 383723 := bstep (se 1 (by rfl) ⟨287792, by rfl⟩ : syracuseStep 383723 = 575585) B575585
theorem B613241 : Blo 251819 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B646015 : Blo 251819 646015 := bstep (se 1 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 646015 = 969023) B969023
theorem B253031 : Blo 251819 253031 := bstep (se 1 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 253031 = 379547) B379547
theorem B253087 : Blo 251819 253087 := bstep (se 1 (by rfl) ⟨189815, by rfl⟩ : syracuseStep 253087 = 379631) B379631
theorem B253183 : Blo 251819 253183 := bstep (se 1 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 253183 = 379775) B379775
theorem B253599 : Blo 251819 253599 := bstep (se 1 (by rfl) ⟨190199, by rfl⟩ : syracuseStep 253599 = 380399) B380399
theorem B1925531 : Blo 251819 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B254715 : Blo 251819 254715 := bstep (se 1 (by rfl) ⟨191036, by rfl⟩ : syracuseStep 254715 = 382073) B382073
theorem B255259 : Blo 251819 255259 := bstep (se 1 (by rfl) ⟨191444, by rfl⟩ : syracuseStep 255259 = 382889) B382889
theorem B255487 : Blo 251819 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B255535 : Blo 251819 255535 := bstep (se 1 (by rfl) ⟨191651, by rfl⟩ : syracuseStep 255535 = 383303) B383303
theorem B649289 : Blo 251819 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B1076449 : Blo 251819 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B912667 : Blo 251819 912667 := bstep (se 1 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 912667 = 1369001) B1369001
theorem B651199 : Blo 251819 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B1077407 : Blo 251819 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B815359 : Blo 251819 815359 := bstep (se 1 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 815359 = 1223039) B1223039
theorem B1439207 : Blo 251819 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B719273 : Blo 251819 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B719387 : Blo 251819 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B719455 : Blo 251819 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B1965217 : Blo 251819 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B3246875 : Blo 251819 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B428827 : Blo 251819 428827 := bstep (se 1 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 428827 = 643241) B643241
theorem B855359 : Blo 251819 855359 := bstep (se 1 (by rfl) ⟨641519, by rfl⟩ : syracuseStep 855359 = 1283039) B1283039
theorem B856007 : Blo 251819 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B1216889 : Blo 251819 1216889 := bstep (se 2 (by rfl) ⟨456333, by rfl⟩ : syracuseStep 1216889 = 912667) B912667
theorem B6624665 : Blo 251819 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B1021481 : Blo 251819 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B1283687 : Blo 251819 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B1087145 : Blo 251819 1087145 := bstep (se 2 (by rfl) ⟨407679, by rfl⟩ : syracuseStep 1087145 = 815359) B815359
theorem B858815 : Blo 251819 858815 := bstep (se 1 (by rfl) ⟨644111, by rfl⟩ : syracuseStep 858815 = 1288223) B1288223
theorem B432859 : Blo 251819 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B859247 : Blo 251819 859247 := bstep (se 1 (by rfl) ⟨644435, by rfl⟩ : syracuseStep 859247 = 1288871) B1288871
theorem B959273 : Blo 251819 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B959471 : Blo 251819 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B861353 : Blo 251819 861353 := bstep (se 2 (by rfl) ⟨323007, by rfl⟩ : syracuseStep 861353 = 646015) B646015
theorem B862163 : Blo 251819 862163 := bstep (se 1 (by rfl) ⟨646622, by rfl⟩ : syracuseStep 862163 = 1293245) B1293245
theorem B1748951 : Blo 251819 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B26357723 : Blo 251819 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B1454719 : Blo 251819 1454719 := bstep (se 1 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 1454719 = 2182079) B2182079
theorem B964831 : Blo 251819 964831 := bstep (se 1 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 964831 = 1447247) B1447247
theorem B1817579 : Blo 251819 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B408827 : Blo 251819 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B868265 : Blo 251819 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B1819219 : Blo 251819 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B378983 : Blo 251819 378983 := bstep (se 1 (by rfl) ⟨284237, by rfl⟩ : syracuseStep 378983 = 568475) B568475
theorem B379295 : Blo 251819 379295 := bstep (se 1 (by rfl) ⟨284471, by rfl⟩ : syracuseStep 379295 = 568943) B568943
theorem B2476777 : Blo 251819 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B479515 : Blo 251819 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B479591 : Blo 251819 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B382511 : Blo 251819 382511 := bstep (se 1 (by rfl) ⟨286883, by rfl⟩ : syracuseStep 382511 = 573767) B573767
theorem B251967 : Blo 251819 251967 := bstep (se 1 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 251967 = 377951) B377951
theorem B251995 : Blo 251819 251995 := bstep (se 1 (by rfl) ⟨188996, by rfl⟩ : syracuseStep 251995 = 377993) B377993
theorem B383471 : Blo 251819 383471 := bstep (se 1 (by rfl) ⟨287603, by rfl⟩ : syracuseStep 383471 = 575207) B575207
theorem B383591 : Blo 251819 383591 := bstep (se 1 (by rfl) ⟨287693, by rfl⟩ : syracuseStep 383591 = 575387) B575387
theorem B973439 : Blo 251819 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B12114613 : Blo 251819 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B252703 : Blo 251819 252703 := bstep (se 1 (by rfl) ⟨189527, by rfl⟩ : syracuseStep 252703 = 379055) B379055
theorem B482287 : Blo 251819 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B1629179 : Blo 251819 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B253423 : Blo 251819 253423 := bstep (se 1 (by rfl) ⟨190067, by rfl⟩ : syracuseStep 253423 = 380135) B380135
theorem B253467 : Blo 251819 253467 := bstep (se 1 (by rfl) ⟨190100, by rfl⟩ : syracuseStep 253467 = 380201) B380201
theorem B253471 : Blo 251819 253471 := bstep (se 1 (by rfl) ⟨190103, by rfl⟩ : syracuseStep 253471 = 380207) B380207
theorem B2875175 : Blo 251819 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B286591 : Blo 251819 286591 := bstep (se 1 (by rfl) ⟨214943, by rfl⟩ : syracuseStep 286591 = 429887) B429887
theorem B254191 : Blo 251819 254191 := bstep (se 1 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 254191 = 381287) B381287
theorem B516359 : Blo 251819 516359 := bstep (se 1 (by rfl) ⟨387269, by rfl⟩ : syracuseStep 516359 = 774539) B774539
theorem B254695 : Blo 251819 254695 := bstep (se 1 (by rfl) ⟨191021, by rfl⟩ : syracuseStep 254695 = 382043) B382043
theorem B254791 : Blo 251819 254791 := bstep (se 1 (by rfl) ⟨191093, by rfl⟩ : syracuseStep 254791 = 382187) B382187
theorem B254943 : Blo 251819 254943 := bstep (se 1 (by rfl) ⟨191207, by rfl⟩ : syracuseStep 254943 = 382415) B382415
theorem B255303 : Blo 251819 255303 := bstep (se 1 (by rfl) ⟨191477, by rfl⟩ : syracuseStep 255303 = 382955) B382955
theorem B1926503 : Blo 251819 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B1435265 : Blo 251819 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B255815 : Blo 251819 255815 := bstep (se 1 (by rfl) ⟨191861, by rfl⟩ : syracuseStep 255815 = 383723) B383723
theorem B3237853 : Blo 251819 3237853 := bstep (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) B1214195
theorem B14872045 : Blo 251819 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B14644151 : Blo 251819 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B7402585 : Blo 251819 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B718271 : Blo 251819 718271 := bstep (se 1 (by rfl) ⟨538703, by rfl⟩ : syracuseStep 718271 = 1077407) B1077407
theorem B2620289 : Blo 251819 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1211735 : Blo 251819 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B2425625 : Blo 251819 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B2164583 : Blo 251819 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B855791 : Blo 251819 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B724763 : Blo 251819 724763 := bstep (se 1 (by rfl) ⟨543572, by rfl⟩ : syracuseStep 724763 = 1087145) B1087145
theorem B19829393 : Blo 251819 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1086119 : Blo 251819 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B1939625 : Blo 251819 1939625 := bstep (se 2 (by rfl) ⟨727359, by rfl⟩ : syracuseStep 1939625 = 1454719) B1454719
theorem B1284335 : Blo 251819 1284335 := bstep (se 1 (by rfl) ⟨963251, by rfl⟩ : syracuseStep 1284335 = 1926503) B1926503
theorem B956843 : Blo 251819 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B9870113 : Blo 251819 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B17571815 : Blo 251819 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B1286441 : Blo 251819 1286441 := bstep (se 2 (by rfl) ⟨482415, by rfl⟩ : syracuseStep 1286441 = 964831) B964831
theorem B1090205 : Blo 251819 1090205 := bstep (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) B408827
theorem B1746859 : Blo 251819 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B570239 : Blo 251819 570239 := bstep (se 1 (by rfl) ⟨427679, by rfl⟩ : syracuseStep 570239 = 855359) B855359
theorem B570671 : Blo 251819 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B571769 : Blo 251819 571769 := bstep (se 2 (by rfl) ⟨214413, by rfl⟩ : syracuseStep 571769 = 428827) B428827
theorem B572543 : Blo 251819 572543 := bstep (se 1 (by rfl) ⟨429407, by rfl⟩ : syracuseStep 572543 = 858815) B858815
theorem B572831 : Blo 251819 572831 := bstep (se 1 (by rfl) ⟨429623, by rfl⟩ : syracuseStep 572831 = 859247) B859247
theorem B1916783 : Blo 251819 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B344239 : Blo 251819 344239 := bstep (se 1 (by rfl) ⟨258179, by rfl⟩ : syracuseStep 344239 = 516359) B516359
theorem B639353 : Blo 251819 639353 := bstep (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) B479515
theorem B639515 : Blo 251819 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B639647 : Blo 251819 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B574235 : Blo 251819 574235 := bstep (se 1 (by rfl) ⟨430676, by rfl⟩ : syracuseStep 574235 = 861353) B861353
theorem B574775 : Blo 251819 574775 := bstep (se 1 (by rfl) ⟨431081, by rfl⟩ : syracuseStep 574775 = 862163) B862163
theorem B1165967 : Blo 251819 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B577145 : Blo 251819 577145 := bstep (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) B432859
theorem B478847 : Blo 251819 478847 := bstep (se 1 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 478847 = 718271) B718271
theorem B643049 : Blo 251819 643049 := bstep (se 2 (by rfl) ⟨241143, by rfl⟩ : syracuseStep 643049 = 482287) B482287
theorem B807823 : Blo 251819 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B382121 : Blo 251819 382121 := bstep (se 2 (by rfl) ⟨143295, by rfl⟩ : syracuseStep 382121 = 286591) B286591
theorem B578843 : Blo 251819 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B252655 : Blo 251819 252655 := bstep (se 1 (by rfl) ⟨189491, by rfl⟩ : syracuseStep 252655 = 378983) B378983
theorem B252863 : Blo 251819 252863 := bstep (se 1 (by rfl) ⟨189647, by rfl⟩ : syracuseStep 252863 = 379295) B379295
theorem B4317137 : Blo 251819 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B319727 : Blo 251819 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B811259 : Blo 251819 811259 := bstep (se 1 (by rfl) ⟨608444, by rfl⟩ : syracuseStep 811259 = 1216889) B1216889
theorem B4416443 : Blo 251819 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B3302369 : Blo 251819 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B680987 : Blo 251819 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B255007 : Blo 251819 255007 := bstep (se 1 (by rfl) ⟨191255, by rfl⟩ : syracuseStep 255007 = 382511) B382511
theorem B255647 : Blo 251819 255647 := bstep (se 1 (by rfl) ⟨191735, by rfl⟩ : syracuseStep 255647 = 383471) B383471
theorem B255727 : Blo 251819 255727 := bstep (se 1 (by rfl) ⟨191795, by rfl⟩ : syracuseStep 255727 = 383591) B383591
theorem B648959 : Blo 251819 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B9762767 : Blo 251819 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B16152817 : Blo 251819 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1211719 : Blo 251819 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B426235 : Blo 251819 426235 := bstep (se 1 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 426235 = 639353) B639353
theorem B426343 : Blo 251819 426343 := bstep (se 1 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 426343 = 639515) B639515
theorem B426431 : Blo 251819 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B852605 : Blo 251819 852605 := bstep (se 3 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 852605 = 319727) B319727
theorem B1835941 : Blo 251819 1835941 := bstep (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) B344239
theorem B1443055 : Blo 251819 1443055 := bstep (se 1 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 1443055 = 2164583) B2164583
theorem B2329145 : Blo 251819 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B428699 : Blo 251819 428699 := bstep (se 1 (by rfl) ⟨321524, by rfl⟩ : syracuseStep 428699 = 643049) B643049
theorem B724079 : Blo 251819 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B856223 : Blo 251819 856223 := bstep (se 1 (by rfl) ⟨642167, by rfl⟩ : syracuseStep 856223 = 1284335) B1284335
theorem B857627 : Blo 251819 857627 := bstep (se 1 (by rfl) ⟨643220, by rfl⟩ : syracuseStep 857627 = 1286441) B1286441
theorem B726803 : Blo 251819 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B2201579 : Blo 251819 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B21537089 : Blo 251819 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1615625 : Blo 251819 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B1617083 : Blo 251819 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B570527 : Blo 251819 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B13219595 : Blo 251819 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B1293083 : Blo 251819 1293083 := bstep (se 1 (by rfl) ⟨969812, by rfl⟩ : syracuseStep 1293083 = 1939625) B1939625
theorem B637895 : Blo 251819 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B4308389 : Blo 251819 4308389 := bstep (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) B807823
theorem B11714543 : Blo 251819 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B540839 : Blo 251819 540839 := bstep (se 1 (by rfl) ⟨405629, by rfl⟩ : syracuseStep 540839 = 811259) B811259
theorem B380159 : Blo 251819 380159 := bstep (se 1 (by rfl) ⟨285119, by rfl⟩ : syracuseStep 380159 = 570239) B570239
theorem B380447 : Blo 251819 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B6508511 : Blo 251819 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B381179 : Blo 251819 381179 := bstep (se 1 (by rfl) ⟨285884, by rfl⟩ : syracuseStep 381179 = 571769) B571769
theorem B381695 : Blo 251819 381695 := bstep (se 1 (by rfl) ⟨286271, by rfl⟩ : syracuseStep 381695 = 572543) B572543
theorem B381887 : Blo 251819 381887 := bstep (se 1 (by rfl) ⟨286415, by rfl⟩ : syracuseStep 381887 = 572831) B572831
theorem B382823 : Blo 251819 382823 := bstep (se 1 (by rfl) ⟨287117, by rfl⟩ : syracuseStep 382823 = 574235) B574235
theorem B383183 : Blo 251819 383183 := bstep (se 1 (by rfl) ⟨287387, by rfl⟩ : syracuseStep 383183 = 574775) B574775
theorem B777311 : Blo 251819 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B319231 : Blo 251819 319231 := bstep (se 1 (by rfl) ⟨239423, by rfl⟩ : syracuseStep 319231 = 478847) B478847
theorem B483175 : Blo 251819 483175 := bstep (se 1 (by rfl) ⟨362381, by rfl⟩ : syracuseStep 483175 = 724763) B724763
theorem B254747 : Blo 251819 254747 := bstep (se 1 (by rfl) ⟨191060, by rfl⟩ : syracuseStep 254747 = 382121) B382121
theorem B385895 : Blo 251819 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B6580075 : Blo 251819 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B1730557 : Blo 251819 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B2878091 : Blo 251819 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B2944295 : Blo 251819 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B453991 : Blo 251819 453991 := bstep (se 1 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 453991 = 680987) B680987
theorem B1539053 : Blo 251819 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B1277855 : Blo 251819 1277855 := bstep (se 1 (by rfl) ⟨958391, by rfl⟩ : syracuseStep 1277855 = 1916783) B1916783
theorem B360559 : Blo 251819 360559 := bstep (se 1 (by rfl) ⟨270419, by rfl⟩ : syracuseStep 360559 = 540839) B540839
theorem B14358059 : Blo 251819 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B862055 : Blo 251819 862055 := bstep (se 1 (by rfl) ⟨646541, by rfl⟩ : syracuseStep 862055 = 1293083) B1293083
theorem B1026035 : Blo 251819 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B7809695 : Blo 251819 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B568313 : Blo 251819 568313 := bstep (se 2 (by rfl) ⟨213117, by rfl⟩ : syracuseStep 568313 = 426235) B426235
theorem B568403 : Blo 251819 568403 := bstep (se 1 (by rfl) ⟨426302, by rfl⟩ : syracuseStep 568403 = 852605) B852605
theorem B568457 : Blo 251819 568457 := bstep (se 2 (by rfl) ⟨213171, by rfl⟩ : syracuseStep 568457 = 426343) B426343
theorem B1552763 : Blo 251819 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B4339007 : Blo 251819 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2307409 : Blo 251819 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B570815 : Blo 251819 570815 := bstep (se 1 (by rfl) ⟨428111, by rfl⟩ : syracuseStep 570815 = 856223) B856223
theorem B571751 : Blo 251819 571751 := bstep (se 1 (by rfl) ⟨428813, by rfl⟩ : syracuseStep 571751 = 857627) B857627
theorem B605321 : Blo 251819 605321 := bstep (se 2 (by rfl) ⟨226995, by rfl⟩ : syracuseStep 605321 = 453991) B453991
theorem B1918727 : Blo 251819 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B380351 : Blo 251819 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B2872259 : Blo 251819 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B644233 : Blo 251819 644233 := bstep (se 2 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 644233 = 483175) B483175
theorem B284287 : Blo 251819 284287 := bstep (se 1 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 284287 = 426431) B426431
theorem B2447921 : Blo 251819 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B1924073 : Blo 251819 1924073 := bstep (se 2 (by rfl) ⟨721527, by rfl⟩ : syracuseStep 1924073 = 1443055) B1443055
theorem B285799 : Blo 251819 285799 := bstep (se 1 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 285799 = 428699) B428699
theorem B253439 : Blo 251819 253439 := bstep (se 1 (by rfl) ⟨190079, by rfl⟩ : syracuseStep 253439 = 380159) B380159
theorem B253631 : Blo 251819 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B8773433 : Blo 251819 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B254119 : Blo 251819 254119 := bstep (se 1 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 254119 = 381179) B381179
theorem B254463 : Blo 251819 254463 := bstep (se 1 (by rfl) ⟨190847, by rfl⟩ : syracuseStep 254463 = 381695) B381695
theorem B254591 : Blo 251819 254591 := bstep (se 1 (by rfl) ⟨190943, by rfl⟩ : syracuseStep 254591 = 381887) B381887
theorem B484535 : Blo 251819 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B255215 : Blo 251819 255215 := bstep (se 1 (by rfl) ⟨191411, by rfl⟩ : syracuseStep 255215 = 382823) B382823
theorem B1467719 : Blo 251819 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B255455 : Blo 251819 255455 := bstep (se 1 (by rfl) ⟨191591, by rfl⟩ : syracuseStep 255455 = 383183) B383183
theorem B518207 : Blo 251819 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B257263 : Blo 251819 257263 := bstep (se 1 (by rfl) ⟨192947, by rfl⟩ : syracuseStep 257263 = 385895) B385895
theorem B1077083 : Blo 251819 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B1078055 : Blo 251819 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B1962863 : Blo 251819 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B1930877 : Blo 251819 1930877 := bstep (se 3 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 1930877 = 724079) B724079
theorem B8813063 : Blo 251819 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B425263 : Blo 251819 425263 := bstep (se 1 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 425263 = 637895) B637895
theorem B425641 : Blo 251819 425641 := bstep (se 2 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 425641 = 319231) B319231
theorem B851903 : Blo 251819 851903 := bstep (se 1 (by rfl) ⟨638927, by rfl⟩ : syracuseStep 851903 = 1277855) B1277855
theorem B1279151 : Blo 251819 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B9572039 : Blo 251819 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1282715 : Blo 251819 1282715 := bstep (se 1 (by rfl) ⟨962036, by rfl⟩ : syracuseStep 1282715 = 1924073) B1924073
theorem B23501501 : Blo 251819 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B858977 : Blo 251819 858977 := bstep (se 2 (by rfl) ⟨322116, by rfl⟩ : syracuseStep 858977 = 644233) B644233
theorem B2892671 : Blo 251819 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B1287251 : Blo 251819 1287251 := bstep (se 1 (by rfl) ⟨965438, by rfl⟩ : syracuseStep 1287251 = 1930877) B1930877
theorem B567017 : Blo 251819 567017 := bstep (se 2 (by rfl) ⟨212631, by rfl⟩ : syracuseStep 567017 = 425263) B425263
theorem B403547 : Blo 251819 403547 := bstep (se 1 (by rfl) ⟨302660, by rfl⟩ : syracuseStep 403547 = 605321) B605321
theorem B567521 : Blo 251819 567521 := bstep (se 2 (by rfl) ⟨212820, by rfl⟩ : syracuseStep 567521 = 425641) B425641
theorem B567935 : Blo 251819 567935 := bstep (se 1 (by rfl) ⟨425951, by rfl⟩ : syracuseStep 567935 = 851903) B851903
theorem B1914839 : Blo 251819 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B5848955 : Blo 251819 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B574703 : Blo 251819 574703 := bstep (se 1 (by rfl) ⟨431027, by rfl⟩ : syracuseStep 574703 = 862055) B862055
theorem B12306181 : Blo 251819 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B378875 : Blo 251819 378875 := bstep (se 1 (by rfl) ⟨284156, by rfl⟩ : syracuseStep 378875 = 568313) B568313
theorem B378935 : Blo 251819 378935 := bstep (se 1 (by rfl) ⟨284201, by rfl⟩ : syracuseStep 378935 = 568403) B568403
theorem B378971 : Blo 251819 378971 := bstep (se 1 (by rfl) ⟨284228, by rfl⟩ : syracuseStep 378971 = 568457) B568457
theorem B379049 : Blo 251819 379049 := bstep (se 2 (by rfl) ⟨142143, by rfl⟩ : syracuseStep 379049 = 284287) B284287
theorem B1035175 : Blo 251819 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B380543 : Blo 251819 380543 := bstep (se 1 (by rfl) ⟨285407, by rfl⟩ : syracuseStep 380543 = 570815) B570815
theorem B381065 : Blo 251819 381065 := bstep (se 2 (by rfl) ⟨142899, by rfl⟩ : syracuseStep 381065 = 285799) B285799
theorem B381167 : Blo 251819 381167 := bstep (se 1 (by rfl) ⟨285875, by rfl⟩ : syracuseStep 381167 = 571751) B571751
theorem B480745 : Blo 251819 480745 := bstep (se 2 (by rfl) ⟨180279, by rfl⟩ : syracuseStep 480745 = 360559) B360559
theorem B5527541 : Blo 251819 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B253567 : Blo 251819 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B1631947 : Blo 251819 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B323023 : Blo 251819 323023 := bstep (se 1 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 323023 = 484535) B484535
theorem B978479 : Blo 251819 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B1372069 : Blo 251819 1372069 := bstep (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) B257263
theorem B684023 : Blo 251819 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B5206463 : Blo 251819 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B718055 : Blo 251819 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B718703 : Blo 251819 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B1308575 : Blo 251819 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B852767 : Blo 251819 852767 := bstep (se 1 (by rfl) ⟨639575, by rfl⟩ : syracuseStep 852767 = 1279151) B1279151
theorem B855143 : Blo 251819 855143 := bstep (se 1 (by rfl) ⟨641357, by rfl⟩ : syracuseStep 855143 = 1282715) B1282715
theorem B1380233 : Blo 251819 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B15667667 : Blo 251819 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B430697 : Blo 251819 430697 := bstep (se 2 (by rfl) ⟨161511, by rfl⟩ : syracuseStep 430697 = 323023) B323023
theorem B858167 : Blo 251819 858167 := bstep (se 1 (by rfl) ⟨643625, by rfl⟩ : syracuseStep 858167 = 1287251) B1287251
theorem B7317701 : Blo 251819 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B2175929 : Blo 251819 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B3685027 : Blo 251819 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B572651 : Blo 251819 572651 := bstep (se 1 (by rfl) ⟨429488, by rfl⟩ : syracuseStep 572651 = 858977) B858977
theorem B378011 : Blo 251819 378011 := bstep (se 1 (by rfl) ⟨283508, by rfl⟩ : syracuseStep 378011 = 567017) B567017
theorem B378347 : Blo 251819 378347 := bstep (se 1 (by rfl) ⟨283760, by rfl⟩ : syracuseStep 378347 = 567521) B567521
theorem B378623 : Blo 251819 378623 := bstep (se 1 (by rfl) ⟨283967, by rfl⟩ : syracuseStep 378623 = 567935) B567935
theorem B640993 : Blo 251819 640993 := bstep (se 2 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 640993 = 480745) B480745
theorem B478703 : Blo 251819 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B479135 : Blo 251819 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B872383 : Blo 251819 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B1824061 : Blo 251819 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B383135 : Blo 251819 383135 := bstep (se 1 (by rfl) ⟨287351, by rfl⟩ : syracuseStep 383135 = 574703) B574703
theorem B252583 : Blo 251819 252583 := bstep (se 1 (by rfl) ⟨189437, by rfl⟩ : syracuseStep 252583 = 378875) B378875
theorem B252623 : Blo 251819 252623 := bstep (se 1 (by rfl) ⟨189467, by rfl⟩ : syracuseStep 252623 = 378935) B378935
theorem B252647 : Blo 251819 252647 := bstep (se 1 (by rfl) ⟨189485, by rfl⟩ : syracuseStep 252647 = 378971) B378971
theorem B252699 : Blo 251819 252699 := bstep (se 1 (by rfl) ⟨189524, by rfl⟩ : syracuseStep 252699 = 379049) B379049
theorem B16408241 : Blo 251819 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B253695 : Blo 251819 253695 := bstep (se 1 (by rfl) ⟨190271, by rfl⟩ : syracuseStep 253695 = 380543) B380543
theorem B6381359 : Blo 251819 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B254043 : Blo 251819 254043 := bstep (se 1 (by rfl) ⟨190532, by rfl⟩ : syracuseStep 254043 = 381065) B381065
theorem B254111 : Blo 251819 254111 := bstep (se 1 (by rfl) ⟨190583, by rfl⟩ : syracuseStep 254111 = 381167) B381167
theorem B1076125 : Blo 251819 1076125 := bstep (se 3 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 1076125 = 403547) B403547
theorem B1928447 : Blo 251819 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B652319 : Blo 251819 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B3470975 : Blo 251819 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B1276559 : Blo 251819 1276559 := bstep (se 1 (by rfl) ⟨957419, by rfl⟩ : syracuseStep 1276559 = 1914839) B1914839
theorem B3899303 : Blo 251819 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B920155 : Blo 251819 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B854657 : Blo 251819 854657 := bstep (se 2 (by rfl) ⟨320496, by rfl⟩ : syracuseStep 854657 = 640993) B640993
theorem B2432081 : Blo 251819 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B1285631 : Blo 251819 1285631 := bstep (se 1 (by rfl) ⟨964223, by rfl⟩ : syracuseStep 1285631 = 1928447) B1928447
theorem B1450619 : Blo 251819 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B434879 : Blo 251819 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B2599535 : Blo 251819 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B568511 : Blo 251819 568511 := bstep (se 1 (by rfl) ⟨426383, by rfl⟩ : syracuseStep 568511 = 852767) B852767
theorem B570095 : Blo 251819 570095 := bstep (se 1 (by rfl) ⟨427571, by rfl⟩ : syracuseStep 570095 = 855143) B855143
theorem B572111 : Blo 251819 572111 := bstep (se 1 (by rfl) ⟨429083, by rfl⟩ : syracuseStep 572111 = 858167) B858167
theorem B1163177 : Blo 251819 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B2313983 : Blo 251819 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B381767 : Blo 251819 381767 := bstep (se 1 (by rfl) ⟨286325, by rfl⟩ : syracuseStep 381767 = 572651) B572651
theorem B252007 : Blo 251819 252007 := bstep (se 1 (by rfl) ⟨189005, by rfl⟩ : syracuseStep 252007 = 378011) B378011
theorem B252231 : Blo 251819 252231 := bstep (se 1 (by rfl) ⟨189173, by rfl⟩ : syracuseStep 252231 = 378347) B378347
theorem B252415 : Blo 251819 252415 := bstep (se 1 (by rfl) ⟨189311, by rfl⟩ : syracuseStep 252415 = 378623) B378623
theorem B319135 : Blo 251819 319135 := bstep (se 1 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 319135 = 478703) B478703
theorem B10445111 : Blo 251819 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B287131 : Blo 251819 287131 := bstep (se 1 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 287131 = 430697) B430697
theorem B1434833 : Blo 251819 1434833 := bstep (se 2 (by rfl) ⟨538062, by rfl⟩ : syracuseStep 1434833 = 1076125) B1076125
theorem B255423 : Blo 251819 255423 := bstep (se 1 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 255423 = 383135) B383135
theorem B10938827 : Blo 251819 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B4254239 : Blo 251819 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B4878467 : Blo 251819 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B4913369 : Blo 251819 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B851039 : Blo 251819 851039 := bstep (se 1 (by rfl) ⟨638279, by rfl⟩ : syracuseStep 851039 = 1276559) B1276559
theorem B1277693 : Blo 251819 1277693 := bstep (se 3 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 1277693 = 479135) B479135
theorem B5376149 : Blo 251819 5376149 := bstep (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) B252007
theorem B1542655 : Blo 251819 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B857087 : Blo 251819 857087 := bstep (se 1 (by rfl) ⟨642815, by rfl⟩ : syracuseStep 857087 = 1285631) B1285631
theorem B956555 : Blo 251819 956555 := bstep (se 1 (by rfl) ⟨717416, by rfl⟩ : syracuseStep 956555 = 1434833) B1434833
theorem B11344637 : Blo 251819 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B3252311 : Blo 251819 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B567359 : Blo 251819 567359 := bstep (se 1 (by rfl) ⟨425519, by rfl⟩ : syracuseStep 567359 = 851039) B851039
theorem B569771 : Blo 251819 569771 := bstep (se 1 (by rfl) ⟨427328, by rfl⟩ : syracuseStep 569771 = 854657) B854657
theorem B1226873 : Blo 251819 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B1621387 : Blo 251819 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B6963407 : Blo 251819 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B967079 : Blo 251819 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B7292551 : Blo 251819 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B379007 : Blo 251819 379007 := bstep (se 1 (by rfl) ⟨284255, by rfl⟩ : syracuseStep 379007 = 568511) B568511
theorem B380063 : Blo 251819 380063 := bstep (se 1 (by rfl) ⟨285047, by rfl⟩ : syracuseStep 380063 = 570095) B570095
theorem B381407 : Blo 251819 381407 := bstep (se 1 (by rfl) ⟨286055, by rfl⟩ : syracuseStep 381407 = 572111) B572111
theorem B775451 : Blo 251819 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B382841 : Blo 251819 382841 := bstep (se 2 (by rfl) ⟨143565, by rfl⟩ : syracuseStep 382841 = 287131) B287131
theorem B254511 : Blo 251819 254511 := bstep (se 1 (by rfl) ⟨190883, by rfl⟩ : syracuseStep 254511 = 381767) B381767
theorem B289919 : Blo 251819 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B1733023 : Blo 251819 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B3275579 : Blo 251819 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B425513 : Blo 251819 425513 := bstep (se 2 (by rfl) ⟨159567, by rfl⟩ : syracuseStep 425513 = 319135) B319135
theorem B851795 : Blo 251819 851795 := bstep (se 1 (by rfl) ⟨638846, by rfl⟩ : syracuseStep 851795 = 1277693) B1277693
theorem B8227493 : Blo 251819 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B2067869 : Blo 251819 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B2168207 : Blo 251819 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B567863 : Blo 251819 567863 := bstep (se 1 (by rfl) ⟨425897, by rfl⟩ : syracuseStep 567863 = 851795) B851795
theorem B3584099 : Blo 251819 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B571391 : Blo 251819 571391 := bstep (se 1 (by rfl) ⟨428543, by rfl⟩ : syracuseStep 571391 = 857087) B857087
theorem B637703 : Blo 251819 637703 := bstep (se 1 (by rfl) ⟨478277, by rfl⟩ : syracuseStep 637703 = 956555) B956555
theorem B2310697 : Blo 251819 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B378239 : Blo 251819 378239 := bstep (se 1 (by rfl) ⟨283679, by rfl⟩ : syracuseStep 378239 = 567359) B567359
theorem B379847 : Blo 251819 379847 := bstep (se 1 (by rfl) ⟨284885, by rfl⟩ : syracuseStep 379847 = 569771) B569771
theorem B773117 : Blo 251819 773117 := bstep (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) B289919
theorem B2183719 : Blo 251819 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B283675 : Blo 251819 283675 := bstep (se 1 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 283675 = 425513) B425513
theorem B4642271 : Blo 251819 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B644719 : Blo 251819 644719 := bstep (se 1 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 644719 = 967079) B967079
theorem B252671 : Blo 251819 252671 := bstep (se 1 (by rfl) ⟨189503, by rfl⟩ : syracuseStep 252671 = 379007) B379007
theorem B253375 : Blo 251819 253375 := bstep (se 1 (by rfl) ⟨190031, by rfl⟩ : syracuseStep 253375 = 380063) B380063
theorem B9723401 : Blo 251819 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B254271 : Blo 251819 254271 := bstep (se 1 (by rfl) ⟨190703, by rfl⟩ : syracuseStep 254271 = 381407) B381407
theorem B255227 : Blo 251819 255227 := bstep (se 1 (by rfl) ⟨191420, by rfl⟩ : syracuseStep 255227 = 382841) B382841
theorem B7563091 : Blo 251819 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B3271661 : Blo 251819 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B2161849 : Blo 251819 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B3080929 : Blo 251819 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B1445471 : Blo 251819 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B859625 : Blo 251819 859625 := bstep (se 2 (by rfl) ⟨322359, by rfl⟩ : syracuseStep 859625 = 644719) B644719
theorem B5514317 : Blo 251819 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B5484995 : Blo 251819 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B3094847 : Blo 251819 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B378233 : Blo 251819 378233 := bstep (se 2 (by rfl) ⟨141837, by rfl⟩ : syracuseStep 378233 = 283675) B283675
theorem B378575 : Blo 251819 378575 := bstep (se 1 (by rfl) ⟨283931, by rfl⟩ : syracuseStep 378575 = 567863) B567863
theorem B2181107 : Blo 251819 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B380927 : Blo 251819 380927 := bstep (se 1 (by rfl) ⟨285695, by rfl⟩ : syracuseStep 380927 = 571391) B571391
theorem B9557597 : Blo 251819 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B252159 : Blo 251819 252159 := bstep (se 1 (by rfl) ⟨189119, by rfl⟩ : syracuseStep 252159 = 378239) B378239
theorem B253231 : Blo 251819 253231 := bstep (se 1 (by rfl) ⟨189923, by rfl⟩ : syracuseStep 253231 = 379847) B379847
theorem B515411 : Blo 251819 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B10084121 : Blo 251819 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B6482267 : Blo 251819 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B2911625 : Blo 251819 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B2882465 : Blo 251819 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B425135 : Blo 251819 425135 := bstep (se 1 (by rfl) ⟨318851, by rfl⟩ : syracuseStep 425135 = 637703) B637703
theorem B6722747 : Blo 251819 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B3676211 : Blo 251819 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B1941083 : Blo 251819 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B4107905 : Blo 251819 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B1454071 : Blo 251819 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B963647 : Blo 251819 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B6371731 : Blo 251819 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B343607 : Blo 251819 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B573083 : Blo 251819 573083 := bstep (se 1 (by rfl) ⟨429812, by rfl⟩ : syracuseStep 573083 = 859625) B859625
theorem B3656663 : Blo 251819 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B1921643 : Blo 251819 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B283423 : Blo 251819 283423 := bstep (se 1 (by rfl) ⟨212567, by rfl⟩ : syracuseStep 283423 = 425135) B425135
theorem B252155 : Blo 251819 252155 := bstep (se 1 (by rfl) ⟨189116, by rfl⟩ : syracuseStep 252155 = 378233) B378233
theorem B252383 : Blo 251819 252383 := bstep (se 1 (by rfl) ⟨189287, by rfl⟩ : syracuseStep 252383 = 378575) B378575
theorem B253951 : Blo 251819 253951 := bstep (se 1 (by rfl) ⟨190463, by rfl⟩ : syracuseStep 253951 = 380927) B380927
theorem B4321511 : Blo 251819 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B2063231 : Blo 251819 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B1281095 : Blo 251819 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B1938761 : Blo 251819 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B8495641 : Blo 251819 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B2437775 : Blo 251819 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B1294055 : Blo 251819 1294055 := bstep (se 1 (by rfl) ⟨970541, by rfl⟩ : syracuseStep 1294055 = 1941083) B1941083
theorem B377897 : Blo 251819 377897 := bstep (se 2 (by rfl) ⟨141711, by rfl⟩ : syracuseStep 377897 = 283423) B283423
theorem B2738603 : Blo 251819 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B642431 : Blo 251819 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B382055 : Blo 251819 382055 := bstep (se 1 (by rfl) ⟨286541, by rfl⟩ : syracuseStep 382055 = 573083) B573083
theorem B4481831 : Blo 251819 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B2450807 : Blo 251819 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B2881007 : Blo 251819 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B916285 : Blo 251819 916285 := bstep (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) B343607
theorem B1375487 : Blo 251819 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B854063 : Blo 251819 854063 := bstep (se 1 (by rfl) ⟨640547, by rfl⟩ : syracuseStep 854063 = 1281095) B1281095
theorem B428287 : Blo 251819 428287 := bstep (se 1 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 428287 = 642431) B642431
theorem B2987887 : Blo 251819 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B1221713 : Blo 251819 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B862703 : Blo 251819 862703 := bstep (se 1 (by rfl) ⟨647027, by rfl⟩ : syracuseStep 862703 = 1294055) B1294055
theorem B1292507 : Blo 251819 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B1625183 : Blo 251819 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B1920671 : Blo 251819 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B251931 : Blo 251819 251931 := bstep (se 1 (by rfl) ⟨188948, by rfl⟩ : syracuseStep 251931 = 377897) B377897
theorem B11327521 : Blo 251819 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B1825735 : Blo 251819 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B254703 : Blo 251819 254703 := bstep (se 1 (by rfl) ⟨191027, by rfl⟩ : syracuseStep 254703 = 382055) B382055
theorem B1633871 : Blo 251819 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B916991 : Blo 251819 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B1083455 : Blo 251819 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B1280447 : Blo 251819 1280447 := bstep (se 1 (by rfl) ⟨960335, by rfl⟩ : syracuseStep 1280447 = 1920671) B1920671
theorem B1089247 : Blo 251819 1089247 := bstep (se 1 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 1089247 = 1633871) B1633871
theorem B2434313 : Blo 251819 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B861671 : Blo 251819 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B569375 : Blo 251819 569375 := bstep (se 1 (by rfl) ⟨427031, by rfl⟩ : syracuseStep 569375 = 854063) B854063
theorem B571049 : Blo 251819 571049 := bstep (se 2 (by rfl) ⟨214143, by rfl⟩ : syracuseStep 571049 = 428287) B428287
theorem B575135 : Blo 251819 575135 := bstep (se 1 (by rfl) ⟨431351, by rfl⟩ : syracuseStep 575135 = 862703) B862703
theorem B3983849 : Blo 251819 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B611327 : Blo 251819 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B814475 : Blo 251819 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B15103361 : Blo 251819 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B722303 : Blo 251819 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B853631 : Blo 251819 853631 := bstep (se 1 (by rfl) ⟨640223, by rfl⟩ : syracuseStep 853631 = 1280447) B1280447
theorem B2655899 : Blo 251819 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B10068907 : Blo 251819 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B2171933 : Blo 251819 2171933 := bstep (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) B814475
theorem B1452329 : Blo 251819 1452329 := bstep (se 2 (by rfl) ⟨544623, by rfl⟩ : syracuseStep 1452329 = 1089247) B1089247
theorem B1622875 : Blo 251819 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B574447 : Blo 251819 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B379583 : Blo 251819 379583 := bstep (se 1 (by rfl) ⟨284687, by rfl⟩ : syracuseStep 379583 = 569375) B569375
theorem B380699 : Blo 251819 380699 := bstep (se 1 (by rfl) ⟨285524, by rfl⟩ : syracuseStep 380699 = 571049) B571049
theorem B383423 : Blo 251819 383423 := bstep (se 1 (by rfl) ⟨287567, by rfl⟩ : syracuseStep 383423 = 575135) B575135
theorem B1630205 : Blo 251819 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B1770599 : Blo 251819 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B2163833 : Blo 251819 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B1086803 : Blo 251819 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B1447955 : Blo 251819 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B569087 : Blo 251819 569087 := bstep (se 1 (by rfl) ⟨426815, by rfl⟩ : syracuseStep 569087 = 853631) B853631
theorem B765929 : Blo 251819 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B968219 : Blo 251819 968219 := bstep (se 1 (by rfl) ⟨726164, by rfl⟩ : syracuseStep 968219 = 1452329) B1452329
theorem B481535 : Blo 251819 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B13425209 : Blo 251819 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B253055 : Blo 251819 253055 := bstep (se 1 (by rfl) ⟨189791, by rfl⟩ : syracuseStep 253055 = 379583) B379583
theorem B253799 : Blo 251819 253799 := bstep (se 1 (by rfl) ⟨190349, by rfl⟩ : syracuseStep 253799 = 380699) B380699
theorem B255615 : Blo 251819 255615 := bstep (se 1 (by rfl) ⟨191711, by rfl⟩ : syracuseStep 255615 = 383423) B383423
theorem B1442555 : Blo 251819 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B4721597 : Blo 251819 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B724535 : Blo 251819 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B8950139 : Blo 251819 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B965303 : Blo 251819 965303 := bstep (se 1 (by rfl) ⟨723977, by rfl⟩ : syracuseStep 965303 = 1447955) B1447955
theorem B379391 : Blo 251819 379391 := bstep (se 1 (by rfl) ⟨284543, by rfl⟩ : syracuseStep 379391 = 569087) B569087
theorem B510619 : Blo 251819 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B645479 : Blo 251819 645479 := bstep (se 1 (by rfl) ⟨484109, by rfl⟩ : syracuseStep 645479 = 968219) B968219
theorem B321023 : Blo 251819 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B3147731 : Blo 251819 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B5966759 : Blo 251819 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B856061 : Blo 251819 856061 := bstep (se 3 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 856061 = 321023) B321023
theorem B430319 : Blo 251819 430319 := bstep (se 1 (by rfl) ⟨322739, by rfl⟩ : syracuseStep 430319 = 645479) B645479
theorem B961703 : Blo 251819 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B643535 : Blo 251819 643535 := bstep (se 1 (by rfl) ⟨482651, by rfl⟩ : syracuseStep 643535 = 965303) B965303
theorem B252927 : Blo 251819 252927 := bstep (se 1 (by rfl) ⟨189695, by rfl⟩ : syracuseStep 252927 = 379391) B379391
theorem B483023 : Blo 251819 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B680825 : Blo 251819 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B2098487 : Blo 251819 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B429023 : Blo 251819 429023 := bstep (se 1 (by rfl) ⟨321767, by rfl⟩ : syracuseStep 429023 = 643535) B643535
theorem B1288061 : Blo 251819 1288061 := bstep (se 3 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 1288061 = 483023) B483023
theorem B3977839 : Blo 251819 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B570707 : Blo 251819 570707 := bstep (se 1 (by rfl) ⟨428030, by rfl⟩ : syracuseStep 570707 = 856061) B856061
theorem B641135 : Blo 251819 641135 := bstep (se 1 (by rfl) ⟨480851, by rfl⟩ : syracuseStep 641135 = 961703) B961703
theorem B286879 : Blo 251819 286879 := bstep (se 1 (by rfl) ⟨215159, by rfl⟩ : syracuseStep 286879 = 430319) B430319
theorem B453883 : Blo 251819 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B427423 : Blo 251819 427423 := bstep (se 1 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 427423 = 641135) B641135
theorem B858707 : Blo 251819 858707 := bstep (se 1 (by rfl) ⟨644030, by rfl⟩ : syracuseStep 858707 = 1288061) B1288061
theorem B21215141 : Blo 251819 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B605177 : Blo 251819 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B380471 : Blo 251819 380471 := bstep (se 1 (by rfl) ⟨285353, by rfl⟩ : syracuseStep 380471 = 570707) B570707
theorem B382505 : Blo 251819 382505 := bstep (se 2 (by rfl) ⟨143439, by rfl⟩ : syracuseStep 382505 = 286879) B286879
theorem B286015 : Blo 251819 286015 := bstep (se 1 (by rfl) ⟨214511, by rfl⟩ : syracuseStep 286015 = 429023) B429023
theorem B5595965 : Blo 251819 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B403451 : Blo 251819 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B569897 : Blo 251819 569897 := bstep (se 2 (by rfl) ⟨213711, by rfl⟩ : syracuseStep 569897 = 427423) B427423
theorem B572471 : Blo 251819 572471 := bstep (se 1 (by rfl) ⟨429353, by rfl⟩ : syracuseStep 572471 = 858707) B858707
theorem B14143427 : Blo 251819 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B381353 : Blo 251819 381353 := bstep (se 2 (by rfl) ⟨143007, by rfl⟩ : syracuseStep 381353 = 286015) B286015
theorem B253647 : Blo 251819 253647 := bstep (se 1 (by rfl) ⟨190235, by rfl⟩ : syracuseStep 253647 = 380471) B380471
theorem B255003 : Blo 251819 255003 := bstep (se 1 (by rfl) ⟨191252, by rfl⟩ : syracuseStep 255003 = 382505) B382505
theorem B3730643 : Blo 251819 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B268967 : Blo 251819 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B379931 : Blo 251819 379931 := bstep (se 1 (by rfl) ⟨284948, by rfl⟩ : syracuseStep 379931 = 569897) B569897
theorem B381647 : Blo 251819 381647 := bstep (se 1 (by rfl) ⟨286235, by rfl⟩ : syracuseStep 381647 = 572471) B572471
theorem B9428951 : Blo 251819 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B254235 : Blo 251819 254235 := bstep (se 1 (by rfl) ⟨190676, by rfl⟩ : syracuseStep 254235 = 381353) B381353
theorem B2487095 : Blo 251819 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B1658063 : Blo 251819 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B253287 : Blo 251819 253287 := bstep (se 1 (by rfl) ⟨189965, by rfl⟩ : syracuseStep 253287 = 379931) B379931
theorem B254431 : Blo 251819 254431 := bstep (se 1 (by rfl) ⟨190823, by rfl⟩ : syracuseStep 254431 = 381647) B381647
theorem B6285967 : Blo 251819 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B717245 : Blo 251819 717245 := bstep (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) B268967
theorem B134100629 : Blo 251819 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B478163 : Blo 251819 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B1105375 : Blo 251819 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B89400419 : Blo 251819 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B1275101 : Blo 251819 1275101 := bstep (se 3 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 1275101 = 478163) B478163
theorem B1473833 : Blo 251819 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B59600279 : Blo 251819 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B3930221 : Blo 251819 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B850067 : Blo 251819 850067 := bstep (se 1 (by rfl) ⟨637550, by rfl⟩ : syracuseStep 850067 = 1275101) B1275101
theorem B566711 : Blo 251819 566711 := bstep (se 1 (by rfl) ⟨425033, by rfl⟩ : syracuseStep 566711 = 850067) B850067
theorem B39733519 : Blo 251819 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B2620147 : Blo 251819 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B377807 : Blo 251819 377807 := bstep (se 1 (by rfl) ⟨283355, by rfl⟩ : syracuseStep 377807 = 566711) B566711
theorem B3493529 : Blo 251819 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B52978025 : Blo 251819 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B2329019 : Blo 251819 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B251871 : Blo 251819 251871 := bstep (se 1 (by rfl) ⟨188903, by rfl⟩ : syracuseStep 251871 = 377807) B377807
theorem B35318683 : Blo 251819 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B47091577 : Blo 251819 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B1552679 : Blo 251819 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B62788769 : Blo 251819 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B1035119 : Blo 251819 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B690079 : Blo 251819 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B41859179 : Blo 251819 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B920105 : Blo 251819 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B27906119 : Blo 251819 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B613403 : Blo 251819 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B18604079 : Blo 251819 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B408935 : Blo 251819 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B12402719 : Blo 251819 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B1090493 : Blo 251819 1090493 := bstep (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) B408935
theorem B8268479 : Blo 251819 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B726995 : Blo 251819 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B5512319 : Blo 251819 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B3674879 : Blo 251819 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B1938653 : Blo 251819 1938653 := bstep (se 3 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 1938653 = 726995) B726995
theorem B1292435 : Blo 251819 1292435 := bstep (se 1 (by rfl) ⟨969326, by rfl⟩ : syracuseStep 1292435 = 1938653) B1938653
theorem B2449919 : Blo 251819 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B861623 : Blo 251819 861623 := bstep (se 1 (by rfl) ⟨646217, by rfl⟩ : syracuseStep 861623 = 1292435) B1292435
theorem B1633279 : Blo 251819 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B2177705 : Blo 251819 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B574415 : Blo 251819 574415 := bstep (se 1 (by rfl) ⟨430811, by rfl⟩ : syracuseStep 574415 = 861623) B861623
theorem B1451803 : Blo 251819 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B382943 : Blo 251819 382943 := bstep (se 1 (by rfl) ⟨287207, by rfl⟩ : syracuseStep 382943 = 574415) B574415
theorem B1935737 : Blo 251819 1935737 := bstep (se 2 (by rfl) ⟨725901, by rfl⟩ : syracuseStep 1935737 = 1451803) B1451803
theorem B255295 : Blo 251819 255295 := bstep (se 1 (by rfl) ⟨191471, by rfl⟩ : syracuseStep 255295 = 382943) B382943
theorem B1290491 : Blo 251819 1290491 := bstep (se 1 (by rfl) ⟨967868, by rfl⟩ : syracuseStep 1290491 = 1935737) B1935737
theorem B860327 : Blo 251819 860327 := bstep (se 1 (by rfl) ⟨645245, by rfl⟩ : syracuseStep 860327 = 1290491) B1290491
theorem B573551 : Blo 251819 573551 := bstep (se 1 (by rfl) ⟨430163, by rfl⟩ : syracuseStep 573551 = 860327) B860327
theorem B382367 : Blo 251819 382367 := bstep (se 1 (by rfl) ⟨286775, by rfl⟩ : syracuseStep 382367 = 573551) B573551
theorem B254911 : Blo 251819 254911 := bstep (se 1 (by rfl) ⟨191183, by rfl⟩ : syracuseStep 254911 = 382367) B382367

theorem C0 (j : ℕ) (h1 : 62954 ≤ j) (h2 : j ≤ 63653) : Blo 251819 (4 * j + 3) := by
  interval_cases j
  · exact B251819
  · exact B251823
  · exact B251827
  · exact B251831
  · exact B251835
  · exact B251839
  · exact B251843
  · exact B251847
  · exact B251851
  · exact B251855
  · exact B251859
  · exact B251863
  · exact B251867
  · exact B251871
  · exact B251875
  · exact B251879
  · exact B251883
  · exact B251887
  · exact B251891
  · exact B251895
  · exact B251899
  · exact B251903
  · exact B251907
  · exact B251911
  · exact B251915
  · exact B251919
  · exact B251923
  · exact B251927
  · exact B251931
  · exact B251935
  · exact B251939
  · exact B251943
  · exact B251947
  · exact B251951
  · exact B251955
  · exact B251959
  · exact B251963
  · exact B251967
  · exact B251971
  · exact B251975
  · exact B251979
  · exact B251983
  · exact B251987
  · exact B251991
  · exact B251995
  · exact B251999
  · exact B252003
  · exact B252007
  · exact B252011
  · exact B252015
  · exact B252019
  · exact B252023
  · exact B252027
  · exact B252031
  · exact B252035
  · exact B252039
  · exact B252043
  · exact B252047
  · exact B252051
  · exact B252055
  · exact B252059
  · exact B252063
  · exact B252067
  · exact B252071
  · exact B252075
  · exact B252079
  · exact B252083
  · exact B252087
  · exact B252091
  · exact B252095
  · exact B252099
  · exact B252103
  · exact B252107
  · exact B252111
  · exact B252115
  · exact B252119
  · exact B252123
  · exact B252127
  · exact B252131
  · exact B252135
  · exact B252139
  · exact B252143
  · exact B252147
  · exact B252151
  · exact B252155
  · exact B252159
  · exact B252163
  · exact B252167
  · exact B252171
  · exact B252175
  · exact B252179
  · exact B252183
  · exact B252187
  · exact B252191
  · exact B252195
  · exact B252199
  · exact B252203
  · exact B252207
  · exact B252211
  · exact B252215
  · exact B252219
  · exact B252223
  · exact B252227
  · exact B252231
  · exact B252235
  · exact B252239
  · exact B252243
  · exact B252247
  · exact B252251
  · exact B252255
  · exact B252259
  · exact B252263
  · exact B252267
  · exact B252271
  · exact B252275
  · exact B252279
  · exact B252283
  · exact B252287
  · exact B252291
  · exact B252295
  · exact B252299
  · exact B252303
  · exact B252307
  · exact B252311
  · exact B252315
  · exact B252319
  · exact B252323
  · exact B252327
  · exact B252331
  · exact B252335
  · exact B252339
  · exact B252343
  · exact B252347
  · exact B252351
  · exact B252355
  · exact B252359
  · exact B252363
  · exact B252367
  · exact B252371
  · exact B252375
  · exact B252379
  · exact B252383
  · exact B252387
  · exact B252391
  · exact B252395
  · exact B252399
  · exact B252403
  · exact B252407
  · exact B252411
  · exact B252415
  · exact B252419
  · exact B252423
  · exact B252427
  · exact B252431
  · exact B252435
  · exact B252439
  · exact B252443
  · exact B252447
  · exact B252451
  · exact B252455
  · exact B252459
  · exact B252463
  · exact B252467
  · exact B252471
  · exact B252475
  · exact B252479
  · exact B252483
  · exact B252487
  · exact B252491
  · exact B252495
  · exact B252499
  · exact B252503
  · exact B252507
  · exact B252511
  · exact B252515
  · exact B252519
  · exact B252523
  · exact B252527
  · exact B252531
  · exact B252535
  · exact B252539
  · exact B252543
  · exact B252547
  · exact B252551
  · exact B252555
  · exact B252559
  · exact B252563
  · exact B252567
  · exact B252571
  · exact B252575
  · exact B252579
  · exact B252583
  · exact B252587
  · exact B252591
  · exact B252595
  · exact B252599
  · exact B252603
  · exact B252607
  · exact B252611
  · exact B252615
  · exact B252619
  · exact B252623
  · exact B252627
  · exact B252631
  · exact B252635
  · exact B252639
  · exact B252643
  · exact B252647
  · exact B252651
  · exact B252655
  · exact B252659
  · exact B252663
  · exact B252667
  · exact B252671
  · exact B252675
  · exact B252679
  · exact B252683
  · exact B252687
  · exact B252691
  · exact B252695
  · exact B252699
  · exact B252703
  · exact B252707
  · exact B252711
  · exact B252715
  · exact B252719
  · exact B252723
  · exact B252727
  · exact B252731
  · exact B252735
  · exact B252739
  · exact B252743
  · exact B252747
  · exact B252751
  · exact B252755
  · exact B252759
  · exact B252763
  · exact B252767
  · exact B252771
  · exact B252775
  · exact B252779
  · exact B252783
  · exact B252787
  · exact B252791
  · exact B252795
  · exact B252799
  · exact B252803
  · exact B252807
  · exact B252811
  · exact B252815
  · exact B252819
  · exact B252823
  · exact B252827
  · exact B252831
  · exact B252835
  · exact B252839
  · exact B252843
  · exact B252847
  · exact B252851
  · exact B252855
  · exact B252859
  · exact B252863
  · exact B252867
  · exact B252871
  · exact B252875
  · exact B252879
  · exact B252883
  · exact B252887
  · exact B252891
  · exact B252895
  · exact B252899
  · exact B252903
  · exact B252907
  · exact B252911
  · exact B252915
  · exact B252919
  · exact B252923
  · exact B252927
  · exact B252931
  · exact B252935
  · exact B252939
  · exact B252943
  · exact B252947
  · exact B252951
  · exact B252955
  · exact B252959
  · exact B252963
  · exact B252967
  · exact B252971
  · exact B252975
  · exact B252979
  · exact B252983
  · exact B252987
  · exact B252991
  · exact B252995
  · exact B252999
  · exact B253003
  · exact B253007
  · exact B253011
  · exact B253015
  · exact B253019
  · exact B253023
  · exact B253027
  · exact B253031
  · exact B253035
  · exact B253039
  · exact B253043
  · exact B253047
  · exact B253051
  · exact B253055
  · exact B253059
  · exact B253063
  · exact B253067
  · exact B253071
  · exact B253075
  · exact B253079
  · exact B253083
  · exact B253087
  · exact B253091
  · exact B253095
  · exact B253099
  · exact B253103
  · exact B253107
  · exact B253111
  · exact B253115
  · exact B253119
  · exact B253123
  · exact B253127
  · exact B253131
  · exact B253135
  · exact B253139
  · exact B253143
  · exact B253147
  · exact B253151
  · exact B253155
  · exact B253159
  · exact B253163
  · exact B253167
  · exact B253171
  · exact B253175
  · exact B253179
  · exact B253183
  · exact B253187
  · exact B253191
  · exact B253195
  · exact B253199
  · exact B253203
  · exact B253207
  · exact B253211
  · exact B253215
  · exact B253219
  · exact B253223
  · exact B253227
  · exact B253231
  · exact B253235
  · exact B253239
  · exact B253243
  · exact B253247
  · exact B253251
  · exact B253255
  · exact B253259
  · exact B253263
  · exact B253267
  · exact B253271
  · exact B253275
  · exact B253279
  · exact B253283
  · exact B253287
  · exact B253291
  · exact B253295
  · exact B253299
  · exact B253303
  · exact B253307
  · exact B253311
  · exact B253315
  · exact B253319
  · exact B253323
  · exact B253327
  · exact B253331
  · exact B253335
  · exact B253339
  · exact B253343
  · exact B253347
  · exact B253351
  · exact B253355
  · exact B253359
  · exact B253363
  · exact B253367
  · exact B253371
  · exact B253375
  · exact B253379
  · exact B253383
  · exact B253387
  · exact B253391
  · exact B253395
  · exact B253399
  · exact B253403
  · exact B253407
  · exact B253411
  · exact B253415
  · exact B253419
  · exact B253423
  · exact B253427
  · exact B253431
  · exact B253435
  · exact B253439
  · exact B253443
  · exact B253447
  · exact B253451
  · exact B253455
  · exact B253459
  · exact B253463
  · exact B253467
  · exact B253471
  · exact B253475
  · exact B253479
  · exact B253483
  · exact B253487
  · exact B253491
  · exact B253495
  · exact B253499
  · exact B253503
  · exact B253507
  · exact B253511
  · exact B253515
  · exact B253519
  · exact B253523
  · exact B253527
  · exact B253531
  · exact B253535
  · exact B253539
  · exact B253543
  · exact B253547
  · exact B253551
  · exact B253555
  · exact B253559
  · exact B253563
  · exact B253567
  · exact B253571
  · exact B253575
  · exact B253579
  · exact B253583
  · exact B253587
  · exact B253591
  · exact B253595
  · exact B253599
  · exact B253603
  · exact B253607
  · exact B253611
  · exact B253615
  · exact B253619
  · exact B253623
  · exact B253627
  · exact B253631
  · exact B253635
  · exact B253639
  · exact B253643
  · exact B253647
  · exact B253651
  · exact B253655
  · exact B253659
  · exact B253663
  · exact B253667
  · exact B253671
  · exact B253675
  · exact B253679
  · exact B253683
  · exact B253687
  · exact B253691
  · exact B253695
  · exact B253699
  · exact B253703
  · exact B253707
  · exact B253711
  · exact B253715
  · exact B253719
  · exact B253723
  · exact B253727
  · exact B253731
  · exact B253735
  · exact B253739
  · exact B253743
  · exact B253747
  · exact B253751
  · exact B253755
  · exact B253759
  · exact B253763
  · exact B253767
  · exact B253771
  · exact B253775
  · exact B253779
  · exact B253783
  · exact B253787
  · exact B253791
  · exact B253795
  · exact B253799
  · exact B253803
  · exact B253807
  · exact B253811
  · exact B253815
  · exact B253819
  · exact B253823
  · exact B253827
  · exact B253831
  · exact B253835
  · exact B253839
  · exact B253843
  · exact B253847
  · exact B253851
  · exact B253855
  · exact B253859
  · exact B253863
  · exact B253867
  · exact B253871
  · exact B253875
  · exact B253879
  · exact B253883
  · exact B253887
  · exact B253891
  · exact B253895
  · exact B253899
  · exact B253903
  · exact B253907
  · exact B253911
  · exact B253915
  · exact B253919
  · exact B253923
  · exact B253927
  · exact B253931
  · exact B253935
  · exact B253939
  · exact B253943
  · exact B253947
  · exact B253951
  · exact B253955
  · exact B253959
  · exact B253963
  · exact B253967
  · exact B253971
  · exact B253975
  · exact B253979
  · exact B253983
  · exact B253987
  · exact B253991
  · exact B253995
  · exact B253999
  · exact B254003
  · exact B254007
  · exact B254011
  · exact B254015
  · exact B254019
  · exact B254023
  · exact B254027
  · exact B254031
  · exact B254035
  · exact B254039
  · exact B254043
  · exact B254047
  · exact B254051
  · exact B254055
  · exact B254059
  · exact B254063
  · exact B254067
  · exact B254071
  · exact B254075
  · exact B254079
  · exact B254083
  · exact B254087
  · exact B254091
  · exact B254095
  · exact B254099
  · exact B254103
  · exact B254107
  · exact B254111
  · exact B254115
  · exact B254119
  · exact B254123
  · exact B254127
  · exact B254131
  · exact B254135
  · exact B254139
  · exact B254143
  · exact B254147
  · exact B254151
  · exact B254155
  · exact B254159
  · exact B254163
  · exact B254167
  · exact B254171
  · exact B254175
  · exact B254179
  · exact B254183
  · exact B254187
  · exact B254191
  · exact B254195
  · exact B254199
  · exact B254203
  · exact B254207
  · exact B254211
  · exact B254215
  · exact B254219
  · exact B254223
  · exact B254227
  · exact B254231
  · exact B254235
  · exact B254239
  · exact B254243
  · exact B254247
  · exact B254251
  · exact B254255
  · exact B254259
  · exact B254263
  · exact B254267
  · exact B254271
  · exact B254275
  · exact B254279
  · exact B254283
  · exact B254287
  · exact B254291
  · exact B254295
  · exact B254299
  · exact B254303
  · exact B254307
  · exact B254311
  · exact B254315
  · exact B254319
  · exact B254323
  · exact B254327
  · exact B254331
  · exact B254335
  · exact B254339
  · exact B254343
  · exact B254347
  · exact B254351
  · exact B254355
  · exact B254359
  · exact B254363
  · exact B254367
  · exact B254371
  · exact B254375
  · exact B254379
  · exact B254383
  · exact B254387
  · exact B254391
  · exact B254395
  · exact B254399
  · exact B254403
  · exact B254407
  · exact B254411
  · exact B254415
  · exact B254419
  · exact B254423
  · exact B254427
  · exact B254431
  · exact B254435
  · exact B254439
  · exact B254443
  · exact B254447
  · exact B254451
  · exact B254455
  · exact B254459
  · exact B254463
  · exact B254467
  · exact B254471
  · exact B254475
  · exact B254479
  · exact B254483
  · exact B254487
  · exact B254491
  · exact B254495
  · exact B254499
  · exact B254503
  · exact B254507
  · exact B254511
  · exact B254515
  · exact B254519
  · exact B254523
  · exact B254527
  · exact B254531
  · exact B254535
  · exact B254539
  · exact B254543
  · exact B254547
  · exact B254551
  · exact B254555
  · exact B254559
  · exact B254563
  · exact B254567
  · exact B254571
  · exact B254575
  · exact B254579
  · exact B254583
  · exact B254587
  · exact B254591
  · exact B254595
  · exact B254599
  · exact B254603
  · exact B254607
  · exact B254611
  · exact B254615

theorem C1 (j : ℕ) (h1 : 63654 ≤ j) (h2 : j ≤ 63954) : Blo 251819 (4 * j + 3) := by
  interval_cases j
  · exact B254619
  · exact B254623
  · exact B254627
  · exact B254631
  · exact B254635
  · exact B254639
  · exact B254643
  · exact B254647
  · exact B254651
  · exact B254655
  · exact B254659
  · exact B254663
  · exact B254667
  · exact B254671
  · exact B254675
  · exact B254679
  · exact B254683
  · exact B254687
  · exact B254691
  · exact B254695
  · exact B254699
  · exact B254703
  · exact B254707
  · exact B254711
  · exact B254715
  · exact B254719
  · exact B254723
  · exact B254727
  · exact B254731
  · exact B254735
  · exact B254739
  · exact B254743
  · exact B254747
  · exact B254751
  · exact B254755
  · exact B254759
  · exact B254763
  · exact B254767
  · exact B254771
  · exact B254775
  · exact B254779
  · exact B254783
  · exact B254787
  · exact B254791
  · exact B254795
  · exact B254799
  · exact B254803
  · exact B254807
  · exact B254811
  · exact B254815
  · exact B254819
  · exact B254823
  · exact B254827
  · exact B254831
  · exact B254835
  · exact B254839
  · exact B254843
  · exact B254847
  · exact B254851
  · exact B254855
  · exact B254859
  · exact B254863
  · exact B254867
  · exact B254871
  · exact B254875
  · exact B254879
  · exact B254883
  · exact B254887
  · exact B254891
  · exact B254895
  · exact B254899
  · exact B254903
  · exact B254907
  · exact B254911
  · exact B254915
  · exact B254919
  · exact B254923
  · exact B254927
  · exact B254931
  · exact B254935
  · exact B254939
  · exact B254943
  · exact B254947
  · exact B254951
  · exact B254955
  · exact B254959
  · exact B254963
  · exact B254967
  · exact B254971
  · exact B254975
  · exact B254979
  · exact B254983
  · exact B254987
  · exact B254991
  · exact B254995
  · exact B254999
  · exact B255003
  · exact B255007
  · exact B255011
  · exact B255015
  · exact B255019
  · exact B255023
  · exact B255027
  · exact B255031
  · exact B255035
  · exact B255039
  · exact B255043
  · exact B255047
  · exact B255051
  · exact B255055
  · exact B255059
  · exact B255063
  · exact B255067
  · exact B255071
  · exact B255075
  · exact B255079
  · exact B255083
  · exact B255087
  · exact B255091
  · exact B255095
  · exact B255099
  · exact B255103
  · exact B255107
  · exact B255111
  · exact B255115
  · exact B255119
  · exact B255123
  · exact B255127
  · exact B255131
  · exact B255135
  · exact B255139
  · exact B255143
  · exact B255147
  · exact B255151
  · exact B255155
  · exact B255159
  · exact B255163
  · exact B255167
  · exact B255171
  · exact B255175
  · exact B255179
  · exact B255183
  · exact B255187
  · exact B255191
  · exact B255195
  · exact B255199
  · exact B255203
  · exact B255207
  · exact B255211
  · exact B255215
  · exact B255219
  · exact B255223
  · exact B255227
  · exact B255231
  · exact B255235
  · exact B255239
  · exact B255243
  · exact B255247
  · exact B255251
  · exact B255255
  · exact B255259
  · exact B255263
  · exact B255267
  · exact B255271
  · exact B255275
  · exact B255279
  · exact B255283
  · exact B255287
  · exact B255291
  · exact B255295
  · exact B255299
  · exact B255303
  · exact B255307
  · exact B255311
  · exact B255315
  · exact B255319
  · exact B255323
  · exact B255327
  · exact B255331
  · exact B255335
  · exact B255339
  · exact B255343
  · exact B255347
  · exact B255351
  · exact B255355
  · exact B255359
  · exact B255363
  · exact B255367
  · exact B255371
  · exact B255375
  · exact B255379
  · exact B255383
  · exact B255387
  · exact B255391
  · exact B255395
  · exact B255399
  · exact B255403
  · exact B255407
  · exact B255411
  · exact B255415
  · exact B255419
  · exact B255423
  · exact B255427
  · exact B255431
  · exact B255435
  · exact B255439
  · exact B255443
  · exact B255447
  · exact B255451
  · exact B255455
  · exact B255459
  · exact B255463
  · exact B255467
  · exact B255471
  · exact B255475
  · exact B255479
  · exact B255483
  · exact B255487
  · exact B255491
  · exact B255495
  · exact B255499
  · exact B255503
  · exact B255507
  · exact B255511
  · exact B255515
  · exact B255519
  · exact B255523
  · exact B255527
  · exact B255531
  · exact B255535
  · exact B255539
  · exact B255543
  · exact B255547
  · exact B255551
  · exact B255555
  · exact B255559
  · exact B255563
  · exact B255567
  · exact B255571
  · exact B255575
  · exact B255579
  · exact B255583
  · exact B255587
  · exact B255591
  · exact B255595
  · exact B255599
  · exact B255603
  · exact B255607
  · exact B255611
  · exact B255615
  · exact B255619
  · exact B255623
  · exact B255627
  · exact B255631
  · exact B255635
  · exact B255639
  · exact B255643
  · exact B255647
  · exact B255651
  · exact B255655
  · exact B255659
  · exact B255663
  · exact B255667
  · exact B255671
  · exact B255675
  · exact B255679
  · exact B255683
  · exact B255687
  · exact B255691
  · exact B255695
  · exact B255699
  · exact B255703
  · exact B255707
  · exact B255711
  · exact B255715
  · exact B255719
  · exact B255723
  · exact B255727
  · exact B255731
  · exact B255735
  · exact B255739
  · exact B255743
  · exact B255747
  · exact B255751
  · exact B255755
  · exact B255759
  · exact B255763
  · exact B255767
  · exact B255771
  · exact B255775
  · exact B255779
  · exact B255783
  · exact B255787
  · exact B255791
  · exact B255795
  · exact B255799
  · exact B255803
  · exact B255807
  · exact B255811
  · exact B255815
  · exact B255819

theorem solution (m : ℕ) (hlo : 251819 ≤ m) (hhi : m ≤ 255819) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 62954 ≤ j := by omega
    have hj2 : j ≤ 63954 := by omega
    have hb : Blo 251819 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 63654 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
