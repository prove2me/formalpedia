-- Prove2me | solution 1 for syracuse_descends_range_814346_818346
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:43.890198+00:00
-- url     : https://prove2.me/submissions/956d537f-cc36-4ae1-8d06-710a1b996cf3

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


theorem B917509 : Blo 814346 917509 := bbase (se 4 (by rfl) ⟨86016, by rfl⟩ : syracuseStep 917509 = 172033) (by norm_num)
theorem B1835045 : Blo 814346 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B917545 : Blo 814346 917545 := bbase (se 2 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 917545 = 688159) (by norm_num)
theorem B2064437 : Blo 814346 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B917581 : Blo 814346 917581 := bbase (se 3 (by rfl) ⟨172046, by rfl⟩ : syracuseStep 917581 = 344093) (by norm_num)
theorem B1572941 : Blo 814346 1572941 := bbase (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) (by norm_num)
theorem B2949221 : Blo 814346 2949221 := bbase (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) (by norm_num)
theorem B1835117 : Blo 814346 1835117 := bbase (se 3 (by rfl) ⟨344084, by rfl⟩ : syracuseStep 1835117 = 688169) (by norm_num)
theorem B1376365 : Blo 814346 1376365 := bbase (se 3 (by rfl) ⟨258068, by rfl⟩ : syracuseStep 1376365 = 516137) (by norm_num)
theorem B917617 : Blo 814346 917617 := bbase (se 2 (by rfl) ⟨344106, by rfl⟩ : syracuseStep 917617 = 688213) (by norm_num)
theorem B917653 : Blo 814346 917653 := bbase (se 6 (by rfl) ⟨21507, by rfl⟩ : syracuseStep 917653 = 43015) (by norm_num)
theorem B1835189 : Blo 814346 1835189 := bbase (se 5 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 1835189 = 172049) (by norm_num)
theorem B2621621 : Blo 814346 2621621 := bbase (se 5 (by rfl) ⟨122888, by rfl⟩ : syracuseStep 2621621 = 245777) (by norm_num)
theorem B917689 : Blo 814346 917689 := bbase (se 2 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 917689 = 688267) (by norm_num)
theorem B1376453 : Blo 814346 1376453 := bbase (se 4 (by rfl) ⟨129042, by rfl⟩ : syracuseStep 1376453 = 258085) (by norm_num)
theorem B917725 : Blo 814346 917725 := bbase (se 3 (by rfl) ⟨172073, by rfl⟩ : syracuseStep 917725 = 344147) (by norm_num)
theorem B2752757 : Blo 814346 2752757 := bbase (se 5 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 2752757 = 258071) (by norm_num)
theorem B2064629 : Blo 814346 2064629 := bbase (se 5 (by rfl) ⟨96779, by rfl⟩ : syracuseStep 2064629 = 193559) (by norm_num)
theorem B1835261 : Blo 814346 1835261 := bbase (se 3 (by rfl) ⟨344111, by rfl⟩ : syracuseStep 1835261 = 688223) (by norm_num)
theorem B917761 : Blo 814346 917761 := bbase (se 2 (by rfl) ⟨344160, by rfl⟩ : syracuseStep 917761 = 688321) (by norm_num)
theorem B917797 : Blo 814346 917797 := bbase (se 4 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 917797 = 172087) (by norm_num)
theorem B1835333 : Blo 814346 1835333 := bbase (se 4 (by rfl) ⟨172062, by rfl⟩ : syracuseStep 1835333 = 344125) (by norm_num)
theorem B1376581 : Blo 814346 1376581 := bbase (se 4 (by rfl) ⟨129054, by rfl⟩ : syracuseStep 1376581 = 258109) (by norm_num)
theorem B917833 : Blo 814346 917833 := bbase (se 2 (by rfl) ⟨344187, by rfl⟩ : syracuseStep 917833 = 688375) (by norm_num)
theorem B917869 : Blo 814346 917869 := bbase (se 3 (by rfl) ⟨172100, by rfl⟩ : syracuseStep 917869 = 344201) (by norm_num)
theorem B1835405 : Blo 814346 1835405 := bbase (se 3 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 1835405 = 688277) (by norm_num)
theorem B917905 : Blo 814346 917905 := bbase (se 2 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 917905 = 688429) (by norm_num)
theorem B1376669 : Blo 814346 1376669 := bbase (se 3 (by rfl) ⟨258125, by rfl⟩ : syracuseStep 1376669 = 516251) (by norm_num)
theorem B917941 : Blo 814346 917941 := bbase (se 5 (by rfl) ⟨43028, by rfl⟩ : syracuseStep 917941 = 86057) (by norm_num)
theorem B1769933 : Blo 814346 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1835477 : Blo 814346 1835477 := bbase (se 7 (by rfl) ⟨21509, by rfl⟩ : syracuseStep 1835477 = 43019) (by norm_num)
theorem B917977 : Blo 814346 917977 := bbase (se 2 (by rfl) ⟨344241, by rfl⟩ : syracuseStep 917977 = 688483) (by norm_num)
theorem B918013 : Blo 814346 918013 := bbase (se 3 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 918013 = 344255) (by norm_num)
theorem B1835549 : Blo 814346 1835549 := bbase (se 3 (by rfl) ⟨344165, by rfl⟩ : syracuseStep 1835549 = 688331) (by norm_num)
theorem B1376797 : Blo 814346 1376797 := bbase (se 3 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 1376797 = 516299) (by norm_num)
theorem B918049 : Blo 814346 918049 := bbase (se 2 (by rfl) ⟨344268, by rfl⟩ : syracuseStep 918049 = 688537) (by norm_num)
theorem B918085 : Blo 814346 918085 := bbase (se 4 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 918085 = 172141) (by norm_num)
theorem B2064973 : Blo 814346 2064973 := bbase (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) (by norm_num)
theorem B1835621 : Blo 814346 1835621 := bbase (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) (by norm_num)
theorem B4194917 : Blo 814346 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B918121 : Blo 814346 918121 := bbase (se 2 (by rfl) ⟨344295, by rfl⟩ : syracuseStep 918121 = 688591) (by norm_num)
theorem B1376885 : Blo 814346 1376885 := bbase (se 5 (by rfl) ⟨64541, by rfl⟩ : syracuseStep 1376885 = 129083) (by norm_num)
theorem B918157 : Blo 814346 918157 := bbase (se 3 (by rfl) ⟨172154, by rfl⟩ : syracuseStep 918157 = 344309) (by norm_num)
theorem B2753189 : Blo 814346 2753189 := bbase (se 4 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 2753189 = 516223) (by norm_num)
theorem B1835693 : Blo 814346 1835693 := bbase (se 3 (by rfl) ⟨344192, by rfl⟩ : syracuseStep 1835693 = 688385) (by norm_num)
theorem B918193 : Blo 814346 918193 := bbase (se 2 (by rfl) ⟨344322, by rfl⟩ : syracuseStep 918193 = 688645) (by norm_num)
theorem B2065085 : Blo 814346 2065085 := bbase (se 3 (by rfl) ⟨387203, by rfl⟩ : syracuseStep 2065085 = 774407) (by norm_num)
theorem B918229 : Blo 814346 918229 := bbase (se 7 (by rfl) ⟨10760, by rfl⟩ : syracuseStep 918229 = 21521) (by norm_num)
theorem B1835765 : Blo 814346 1835765 := bbase (se 5 (by rfl) ⟨86051, by rfl⟩ : syracuseStep 1835765 = 172103) (by norm_num)
theorem B1377013 : Blo 814346 1377013 := bbase (se 5 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 1377013 = 129095) (by norm_num)
theorem B918265 : Blo 814346 918265 := bbase (se 2 (by rfl) ⟨344349, by rfl⟩ : syracuseStep 918265 = 688699) (by norm_num)
theorem B4129541 : Blo 814346 4129541 := bbase (se 4 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 4129541 = 774289) (by norm_num)
theorem B4653845 : Blo 814346 4653845 := bbase (se 6 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 4653845 = 218149) (by norm_num)
theorem B918301 : Blo 814346 918301 := bbase (se 3 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 918301 = 344363) (by norm_num)
theorem B1835837 : Blo 814346 1835837 := bbase (se 3 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 1835837 = 688439) (by norm_num)
theorem B918337 : Blo 814346 918337 := bbase (se 2 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 918337 = 688753) (by norm_num)
theorem B1377101 : Blo 814346 1377101 := bbase (se 3 (by rfl) ⟨258206, by rfl⟩ : syracuseStep 1377101 = 516413) (by norm_num)
theorem B17662805 : Blo 814346 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B918373 : Blo 814346 918373 := bbase (se 4 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 918373 = 172195) (by norm_num)
theorem B2327413 : Blo 814346 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B2065277 : Blo 814346 2065277 := bbase (se 3 (by rfl) ⟨387239, by rfl⟩ : syracuseStep 2065277 = 774479) (by norm_num)
theorem B1835909 : Blo 814346 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B918409 : Blo 814346 918409 := bbase (se 2 (by rfl) ⟨344403, by rfl⟩ : syracuseStep 918409 = 688807) (by norm_num)
theorem B6194069 : Blo 814346 6194069 := bbase (se 6 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 6194069 = 290347) (by norm_num)
theorem B918445 : Blo 814346 918445 := bbase (se 3 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 918445 = 344417) (by norm_num)
theorem B1835981 : Blo 814346 1835981 := bbase (se 3 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 1835981 = 688493) (by norm_num)
theorem B1377229 : Blo 814346 1377229 := bbase (se 3 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 1377229 = 516461) (by norm_num)
theorem B918481 : Blo 814346 918481 := bbase (se 2 (by rfl) ⟨344430, by rfl⟩ : syracuseStep 918481 = 688861) (by norm_num)
theorem B918517 : Blo 814346 918517 := bbase (se 5 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 918517 = 86111) (by norm_num)
theorem B1836053 : Blo 814346 1836053 := bbase (se 6 (by rfl) ⟨43032, by rfl⟩ : syracuseStep 1836053 = 86065) (by norm_num)
theorem B918553 : Blo 814346 918553 := bbase (se 2 (by rfl) ⟨344457, by rfl⟩ : syracuseStep 918553 = 688915) (by norm_num)
theorem B1377317 : Blo 814346 1377317 := bbase (se 4 (by rfl) ⟨129123, by rfl⟩ : syracuseStep 1377317 = 258247) (by norm_num)
theorem B918589 : Blo 814346 918589 := bbase (se 3 (by rfl) ⟨172235, by rfl⟩ : syracuseStep 918589 = 344471) (by norm_num)
theorem B2753621 : Blo 814346 2753621 := bbase (se 8 (by rfl) ⟨16134, by rfl⟩ : syracuseStep 2753621 = 32269) (by norm_num)
theorem B1836125 : Blo 814346 1836125 := bbase (se 3 (by rfl) ⟨344273, by rfl⟩ : syracuseStep 1836125 = 688547) (by norm_num)
theorem B918625 : Blo 814346 918625 := bbase (se 2 (by rfl) ⟨344484, by rfl⟩ : syracuseStep 918625 = 688969) (by norm_num)
theorem B918661 : Blo 814346 918661 := bbase (se 4 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 918661 = 172249) (by norm_num)
theorem B1836197 : Blo 814346 1836197 := bbase (se 4 (by rfl) ⟨172143, by rfl⟩ : syracuseStep 1836197 = 344287) (by norm_num)
theorem B1377445 : Blo 814346 1377445 := bbase (se 4 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 1377445 = 258271) (by norm_num)
theorem B918697 : Blo 814346 918697 := bbase (se 2 (by rfl) ⟨344511, by rfl⟩ : syracuseStep 918697 = 689023) (by norm_num)
theorem B918733 : Blo 814346 918733 := bbase (se 3 (by rfl) ⟨172262, by rfl⟩ : syracuseStep 918733 = 344525) (by norm_num)
theorem B2065621 : Blo 814346 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B1836269 : Blo 814346 1836269 := bbase (se 3 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 1836269 = 688601) (by norm_num)
theorem B918769 : Blo 814346 918769 := bbase (se 2 (by rfl) ⟨344538, by rfl⟩ : syracuseStep 918769 = 689077) (by norm_num)
theorem B1377533 : Blo 814346 1377533 := bbase (se 3 (by rfl) ⟨258287, by rfl⟩ : syracuseStep 1377533 = 516575) (by norm_num)
theorem B918805 : Blo 814346 918805 := bbase (se 6 (by rfl) ⟨21534, by rfl⟩ : syracuseStep 918805 = 43069) (by norm_num)
theorem B1836341 : Blo 814346 1836341 := bbase (se 5 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 1836341 = 172157) (by norm_num)
theorem B918841 : Blo 814346 918841 := bbase (se 2 (by rfl) ⟨344565, by rfl⟩ : syracuseStep 918841 = 689131) (by norm_num)
theorem B2065733 : Blo 814346 2065733 := bbase (se 4 (by rfl) ⟨193662, by rfl⟩ : syracuseStep 2065733 = 387325) (by norm_num)
theorem B3540293 : Blo 814346 3540293 := bbase (se 4 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 3540293 = 663805) (by norm_num)
theorem B918877 : Blo 814346 918877 := bbase (se 3 (by rfl) ⟨172289, by rfl⟩ : syracuseStep 918877 = 344579) (by norm_num)
theorem B1836413 : Blo 814346 1836413 := bbase (se 3 (by rfl) ⟨344327, by rfl⟩ : syracuseStep 1836413 = 688655) (by norm_num)
theorem B1377661 : Blo 814346 1377661 := bbase (se 3 (by rfl) ⟨258311, by rfl⟩ : syracuseStep 1377661 = 516623) (by norm_num)
theorem B918913 : Blo 814346 918913 := bbase (se 2 (by rfl) ⟨344592, by rfl⟩ : syracuseStep 918913 = 689185) (by norm_num)
theorem B918949 : Blo 814346 918949 := bbase (se 4 (by rfl) ⟨86151, by rfl⟩ : syracuseStep 918949 = 172303) (by norm_num)
theorem B1836485 : Blo 814346 1836485 := bbase (se 4 (by rfl) ⟨172170, by rfl⟩ : syracuseStep 1836485 = 344341) (by norm_num)
theorem B918985 : Blo 814346 918985 := bbase (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) (by norm_num)
theorem B1377749 : Blo 814346 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B919021 : Blo 814346 919021 := bbase (se 3 (by rfl) ⟨172316, by rfl⟩ : syracuseStep 919021 = 344633) (by norm_num)
theorem B2754053 : Blo 814346 2754053 := bbase (se 4 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 2754053 = 516385) (by norm_num)
theorem B2065925 : Blo 814346 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B1836557 : Blo 814346 1836557 := bbase (se 3 (by rfl) ⟨344354, by rfl⟩ : syracuseStep 1836557 = 688709) (by norm_num)
theorem B919057 : Blo 814346 919057 := bbase (se 2 (by rfl) ⟨344646, by rfl⟩ : syracuseStep 919057 = 689293) (by norm_num)
theorem B919093 : Blo 814346 919093 := bbase (se 5 (by rfl) ⟨43082, by rfl⟩ : syracuseStep 919093 = 86165) (by norm_num)
theorem B1836629 : Blo 814346 1836629 := bbase (se 8 (by rfl) ⟨10761, by rfl⟩ : syracuseStep 1836629 = 21523) (by norm_num)
theorem B1377877 : Blo 814346 1377877 := bbase (se 8 (by rfl) ⟨8073, by rfl⟩ : syracuseStep 1377877 = 16147) (by norm_num)
theorem B919129 : Blo 814346 919129 := bbase (se 2 (by rfl) ⟨344673, by rfl⟩ : syracuseStep 919129 = 689347) (by norm_num)
theorem B919165 : Blo 814346 919165 := bbase (se 3 (by rfl) ⟨172343, by rfl⟩ : syracuseStep 919165 = 344687) (by norm_num)
theorem B1836701 : Blo 814346 1836701 := bbase (se 3 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 1836701 = 688763) (by norm_num)
theorem B919201 : Blo 814346 919201 := bbase (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) (by norm_num)
theorem B1377965 : Blo 814346 1377965 := bbase (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) (by norm_num)
theorem B919237 : Blo 814346 919237 := bbase (se 4 (by rfl) ⟨86178, by rfl⟩ : syracuseStep 919237 = 172357) (by norm_num)
theorem B1836773 : Blo 814346 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B919273 : Blo 814346 919273 := bbase (se 2 (by rfl) ⟨344727, by rfl⟩ : syracuseStep 919273 = 689455) (by norm_num)
theorem B919309 : Blo 814346 919309 := bbase (se 3 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 919309 = 344741) (by norm_num)
theorem B1836845 : Blo 814346 1836845 := bbase (se 3 (by rfl) ⟨344408, by rfl⟩ : syracuseStep 1836845 = 688817) (by norm_num)
theorem B1378093 : Blo 814346 1378093 := bbase (se 3 (by rfl) ⟨258392, by rfl⟩ : syracuseStep 1378093 = 516785) (by norm_num)
theorem B919345 : Blo 814346 919345 := bbase (se 2 (by rfl) ⟨344754, by rfl⟩ : syracuseStep 919345 = 689509) (by norm_num)
theorem B919381 : Blo 814346 919381 := bbase (se 9 (by rfl) ⟨2693, by rfl⟩ : syracuseStep 919381 = 5387) (by norm_num)
theorem B2066269 : Blo 814346 2066269 := bbase (se 3 (by rfl) ⟨387425, by rfl⟩ : syracuseStep 2066269 = 774851) (by norm_num)
theorem B1836917 : Blo 814346 1836917 := bbase (se 5 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 1836917 = 172211) (by norm_num)
theorem B919417 : Blo 814346 919417 := bbase (se 2 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 919417 = 689563) (by norm_num)
theorem B1378181 : Blo 814346 1378181 := bbase (se 4 (by rfl) ⟨129204, by rfl⟩ : syracuseStep 1378181 = 258409) (by norm_num)
theorem B919453 : Blo 814346 919453 := bbase (se 3 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 919453 = 344795) (by norm_num)
theorem B2754485 : Blo 814346 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B4655029 : Blo 814346 4655029 := bbase (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) (by norm_num)
theorem B1836989 : Blo 814346 1836989 := bbase (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) (by norm_num)
theorem B919489 : Blo 814346 919489 := bbase (se 2 (by rfl) ⟨344808, by rfl⟩ : syracuseStep 919489 = 689617) (by norm_num)
theorem B2328517 : Blo 814346 2328517 := bbase (se 4 (by rfl) ⟨218298, by rfl⟩ : syracuseStep 2328517 = 436597) (by norm_num)
theorem B2066381 : Blo 814346 2066381 := bbase (se 3 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 2066381 = 774893) (by norm_num)
theorem B919525 : Blo 814346 919525 := bbase (se 4 (by rfl) ⟨86205, by rfl⟩ : syracuseStep 919525 = 172411) (by norm_num)
theorem B1837061 : Blo 814346 1837061 := bbase (se 4 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 1837061 = 344449) (by norm_num)
theorem B1378309 : Blo 814346 1378309 := bbase (se 4 (by rfl) ⟨129216, by rfl⟩ : syracuseStep 1378309 = 258433) (by norm_num)
theorem B919561 : Blo 814346 919561 := bbase (se 2 (by rfl) ⟨344835, by rfl⟩ : syracuseStep 919561 = 689671) (by norm_num)
theorem B4130837 : Blo 814346 4130837 := bbase (se 6 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 4130837 = 193633) (by norm_num)
theorem B919597 : Blo 814346 919597 := bbase (se 3 (by rfl) ⟨172424, by rfl⟩ : syracuseStep 919597 = 344849) (by norm_num)
theorem B1837133 : Blo 814346 1837133 := bbase (se 3 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 1837133 = 688925) (by norm_num)
theorem B919633 : Blo 814346 919633 := bbase (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) (by norm_num)
theorem B1378397 : Blo 814346 1378397 := bbase (se 3 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 1378397 = 516899) (by norm_num)
theorem B919669 : Blo 814346 919669 := bbase (se 5 (by rfl) ⟨43109, by rfl⟩ : syracuseStep 919669 = 86219) (by norm_num)
theorem B2066573 : Blo 814346 2066573 := bbase (se 3 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 2066573 = 774965) (by norm_num)
theorem B1837205 : Blo 814346 1837205 := bbase (se 6 (by rfl) ⟨43059, by rfl⟩ : syracuseStep 1837205 = 86119) (by norm_num)
theorem B919705 : Blo 814346 919705 := bbase (se 2 (by rfl) ⟨344889, by rfl⟩ : syracuseStep 919705 = 689779) (by norm_num)
theorem B919741 : Blo 814346 919741 := bbase (se 3 (by rfl) ⟨172451, by rfl⟩ : syracuseStep 919741 = 344903) (by norm_num)
theorem B1837277 : Blo 814346 1837277 := bbase (se 3 (by rfl) ⟨344489, by rfl⟩ : syracuseStep 1837277 = 688979) (by norm_num)
theorem B1378525 : Blo 814346 1378525 := bbase (se 3 (by rfl) ⟨258473, by rfl⟩ : syracuseStep 1378525 = 516947) (by norm_num)
theorem B919777 : Blo 814346 919777 := bbase (se 2 (by rfl) ⟨344916, by rfl⟩ : syracuseStep 919777 = 689833) (by norm_num)
theorem B919813 : Blo 814346 919813 := bbase (se 4 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 919813 = 172465) (by norm_num)
theorem B10455317 : Blo 814346 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B1837349 : Blo 814346 1837349 := bbase (se 4 (by rfl) ⟨172251, by rfl⟩ : syracuseStep 1837349 = 344503) (by norm_num)
theorem B919849 : Blo 814346 919849 := bbase (se 2 (by rfl) ⟨344943, by rfl⟩ : syracuseStep 919849 = 689887) (by norm_num)
theorem B1378613 : Blo 814346 1378613 := bbase (se 5 (by rfl) ⟨64622, by rfl⟩ : syracuseStep 1378613 = 129245) (by norm_num)
theorem B919885 : Blo 814346 919885 := bbase (se 3 (by rfl) ⟨172478, by rfl⟩ : syracuseStep 919885 = 344957) (by norm_num)
theorem B2754917 : Blo 814346 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B1837421 : Blo 814346 1837421 := bbase (se 3 (by rfl) ⟨344516, by rfl⟩ : syracuseStep 1837421 = 689033) (by norm_num)
theorem B919921 : Blo 814346 919921 := bbase (se 2 (by rfl) ⟨344970, by rfl⟩ : syracuseStep 919921 = 689941) (by norm_num)
theorem B919957 : Blo 814346 919957 := bbase (se 6 (by rfl) ⟨21561, by rfl⟩ : syracuseStep 919957 = 43123) (by norm_num)
theorem B1837493 : Blo 814346 1837493 := bbase (se 5 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 1837493 = 172265) (by norm_num)
theorem B1378741 : Blo 814346 1378741 := bbase (se 5 (by rfl) ⟨64628, by rfl⟩ : syracuseStep 1378741 = 129257) (by norm_num)
theorem B919993 : Blo 814346 919993 := bbase (se 2 (by rfl) ⟨344997, by rfl⟩ : syracuseStep 919993 = 689995) (by norm_num)
theorem B920029 : Blo 814346 920029 := bbase (se 3 (by rfl) ⟨172505, by rfl⟩ : syracuseStep 920029 = 345011) (by norm_num)
theorem B2066917 : Blo 814346 2066917 := bbase (se 4 (by rfl) ⟨193773, by rfl⟩ : syracuseStep 2066917 = 387547) (by norm_num)
theorem B1837565 : Blo 814346 1837565 := bbase (se 3 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 1837565 = 689087) (by norm_num)
theorem B920065 : Blo 814346 920065 := bbase (se 2 (by rfl) ⟨345024, by rfl⟩ : syracuseStep 920065 = 690049) (by norm_num)
theorem B1378829 : Blo 814346 1378829 := bbase (se 3 (by rfl) ⟨258530, by rfl⟩ : syracuseStep 1378829 = 517061) (by norm_num)
theorem B920101 : Blo 814346 920101 := bbase (se 4 (by rfl) ⟨86259, by rfl⟩ : syracuseStep 920101 = 172519) (by norm_num)
theorem B1837637 : Blo 814346 1837637 := bbase (se 4 (by rfl) ⟨172278, by rfl⟩ : syracuseStep 1837637 = 344557) (by norm_num)
theorem B920137 : Blo 814346 920137 := bbase (se 2 (by rfl) ⟨345051, by rfl⟩ : syracuseStep 920137 = 690103) (by norm_num)
theorem B2067029 : Blo 814346 2067029 := bbase (se 8 (by rfl) ⟨12111, by rfl⟩ : syracuseStep 2067029 = 24223) (by norm_num)
theorem B920173 : Blo 814346 920173 := bbase (se 3 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 920173 = 345065) (by norm_num)
theorem B1837709 : Blo 814346 1837709 := bbase (se 3 (by rfl) ⟨344570, by rfl⟩ : syracuseStep 1837709 = 689141) (by norm_num)
theorem B1378957 : Blo 814346 1378957 := bbase (se 3 (by rfl) ⟨258554, by rfl⟩ : syracuseStep 1378957 = 517109) (by norm_num)
theorem B920209 : Blo 814346 920209 := bbase (se 2 (by rfl) ⟨345078, by rfl⟩ : syracuseStep 920209 = 690157) (by norm_num)
theorem B920245 : Blo 814346 920245 := bbase (se 5 (by rfl) ⟨43136, by rfl⟩ : syracuseStep 920245 = 86273) (by norm_num)
theorem B1837781 : Blo 814346 1837781 := bbase (se 7 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 1837781 = 43073) (by norm_num)
theorem B920281 : Blo 814346 920281 := bbase (se 2 (by rfl) ⟨345105, by rfl⟩ : syracuseStep 920281 = 690211) (by norm_num)
theorem B1739485 : Blo 814346 1739485 := bbase (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) (by norm_num)
theorem B1379045 : Blo 814346 1379045 := bbase (se 4 (by rfl) ⟨129285, by rfl⟩ : syracuseStep 1379045 = 258571) (by norm_num)
theorem B920317 : Blo 814346 920317 := bbase (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) (by norm_num)
theorem B2755349 : Blo 814346 2755349 := bbase (se 6 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 2755349 = 129157) (by norm_num)
theorem B2067221 : Blo 814346 2067221 := bbase (se 6 (by rfl) ⟨48450, by rfl⟩ : syracuseStep 2067221 = 96901) (by norm_num)
theorem B1837853 : Blo 814346 1837853 := bbase (se 3 (by rfl) ⟨344597, by rfl⟩ : syracuseStep 1837853 = 689195) (by norm_num)
theorem B920353 : Blo 814346 920353 := bbase (se 2 (by rfl) ⟨345132, by rfl⟩ : syracuseStep 920353 = 690265) (by norm_num)
theorem B920389 : Blo 814346 920389 := bbase (se 4 (by rfl) ⟨86286, by rfl⟩ : syracuseStep 920389 = 172573) (by norm_num)
theorem B1837925 : Blo 814346 1837925 := bbase (se 4 (by rfl) ⟨172305, by rfl⟩ : syracuseStep 1837925 = 344611) (by norm_num)
theorem B1379173 : Blo 814346 1379173 := bbase (se 4 (by rfl) ⟨129297, by rfl⟩ : syracuseStep 1379173 = 258595) (by norm_num)
theorem B920425 : Blo 814346 920425 := bbase (se 2 (by rfl) ⟨345159, by rfl⟩ : syracuseStep 920425 = 690319) (by norm_num)
theorem B920461 : Blo 814346 920461 := bbase (se 3 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 920461 = 345173) (by norm_num)
theorem B1837997 : Blo 814346 1837997 := bbase (se 3 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 1837997 = 689249) (by norm_num)
theorem B920497 : Blo 814346 920497 := bbase (se 2 (by rfl) ⟨345186, by rfl⟩ : syracuseStep 920497 = 690373) (by norm_num)
theorem B1379261 : Blo 814346 1379261 := bbase (se 3 (by rfl) ⟨258611, by rfl⟩ : syracuseStep 1379261 = 517223) (by norm_num)
theorem B920533 : Blo 814346 920533 := bbase (se 7 (by rfl) ⟨10787, by rfl⟩ : syracuseStep 920533 = 21575) (by norm_num)
theorem B1838069 : Blo 814346 1838069 := bbase (se 5 (by rfl) ⟨86159, by rfl⟩ : syracuseStep 1838069 = 172319) (by norm_num)
theorem B920569 : Blo 814346 920569 := bbase (se 2 (by rfl) ⟨345213, by rfl⟩ : syracuseStep 920569 = 690427) (by norm_num)
theorem B920605 : Blo 814346 920605 := bbase (se 3 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 920605 = 345227) (by norm_num)
theorem B1838141 : Blo 814346 1838141 := bbase (se 3 (by rfl) ⟨344651, by rfl⟩ : syracuseStep 1838141 = 689303) (by norm_num)
theorem B1379389 : Blo 814346 1379389 := bbase (se 3 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 1379389 = 517271) (by norm_num)
theorem B2067565 : Blo 814346 2067565 := bbase (se 3 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 2067565 = 775337) (by norm_num)
theorem B1838213 : Blo 814346 1838213 := bbase (se 4 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 1838213 = 344665) (by norm_num)
theorem B1379477 : Blo 814346 1379477 := bbase (se 6 (by rfl) ⟨32331, by rfl⟩ : syracuseStep 1379477 = 64663) (by norm_num)
theorem B1674437 : Blo 814346 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B2755781 : Blo 814346 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B1838285 : Blo 814346 1838285 := bbase (se 3 (by rfl) ⟨344678, by rfl⟩ : syracuseStep 1838285 = 689357) (by norm_num)
theorem B1739981 : Blo 814346 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B11144405 : Blo 814346 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B2067677 : Blo 814346 2067677 := bbase (se 3 (by rfl) ⟨387689, by rfl⟩ : syracuseStep 2067677 = 775379) (by norm_num)
theorem B1838357 : Blo 814346 1838357 := bbase (se 6 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 1838357 = 86173) (by norm_num)
theorem B1379605 : Blo 814346 1379605 := bbase (se 6 (by rfl) ⟨32334, by rfl⟩ : syracuseStep 1379605 = 64669) (by norm_num)
theorem B4132133 : Blo 814346 4132133 := bbase (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) (by norm_num)
theorem B1838429 : Blo 814346 1838429 := bbase (se 3 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 1838429 = 689411) (by norm_num)
theorem B1379693 : Blo 814346 1379693 := bbase (se 3 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 1379693 = 517385) (by norm_num)
theorem B2067869 : Blo 814346 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B1838501 : Blo 814346 1838501 := bbase (se 4 (by rfl) ⟨172359, by rfl⟩ : syracuseStep 1838501 = 344719) (by norm_num)
theorem B2330021 : Blo 814346 2330021 := bbase (se 4 (by rfl) ⟨218439, by rfl⟩ : syracuseStep 2330021 = 436879) (by norm_num)
theorem B1838573 : Blo 814346 1838573 := bbase (se 3 (by rfl) ⟨344732, by rfl⟩ : syracuseStep 1838573 = 689465) (by norm_num)
theorem B1379821 : Blo 814346 1379821 := bbase (se 3 (by rfl) ⟨258716, by rfl⟩ : syracuseStep 1379821 = 517433) (by norm_num)
theorem B1838645 : Blo 814346 1838645 := bbase (se 5 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 1838645 = 172373) (by norm_num)
theorem B1379909 : Blo 814346 1379909 := bbase (se 4 (by rfl) ⟨129366, by rfl⟩ : syracuseStep 1379909 = 258733) (by norm_num)
theorem B2756213 : Blo 814346 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B6295157 : Blo 814346 6295157 := bbase (se 5 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 6295157 = 590171) (by norm_num)
theorem B1838717 : Blo 814346 1838717 := bbase (se 3 (by rfl) ⟨344759, by rfl⟩ : syracuseStep 1838717 = 689519) (by norm_num)
theorem B1838789 : Blo 814346 1838789 := bbase (se 4 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 1838789 = 344773) (by norm_num)
theorem B1380037 : Blo 814346 1380037 := bbase (se 4 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 1380037 = 258757) (by norm_num)
theorem B2068213 : Blo 814346 2068213 := bbase (se 5 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 2068213 = 193895) (by norm_num)
theorem B1838861 : Blo 814346 1838861 := bbase (se 3 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 1838861 = 689573) (by norm_num)
theorem B1380125 : Blo 814346 1380125 := bbase (se 3 (by rfl) ⟨258773, by rfl⟩ : syracuseStep 1380125 = 517547) (by norm_num)
theorem B25431893 : Blo 814346 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1838933 : Blo 814346 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B2068325 : Blo 814346 2068325 := bbase (se 4 (by rfl) ⟨193905, by rfl⟩ : syracuseStep 2068325 = 387811) (by norm_num)
theorem B4657013 : Blo 814346 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B1839005 : Blo 814346 1839005 := bbase (se 3 (by rfl) ⟨344813, by rfl⟩ : syracuseStep 1839005 = 689627) (by norm_num)
theorem B1380253 : Blo 814346 1380253 := bbase (se 3 (by rfl) ⟨258797, by rfl⟩ : syracuseStep 1380253 = 517595) (by norm_num)
theorem B1839077 : Blo 814346 1839077 := bbase (se 4 (by rfl) ⟨172413, by rfl⟩ : syracuseStep 1839077 = 344827) (by norm_num)
theorem B1380341 : Blo 814346 1380341 := bbase (se 5 (by rfl) ⟨64703, by rfl⟩ : syracuseStep 1380341 = 129407) (by norm_num)
theorem B2756645 : Blo 814346 2756645 := bbase (se 4 (by rfl) ⟨258435, by rfl⟩ : syracuseStep 2756645 = 516871) (by norm_num)
theorem B2068517 : Blo 814346 2068517 := bbase (se 4 (by rfl) ⟨193923, by rfl⟩ : syracuseStep 2068517 = 387847) (by norm_num)
theorem B1740845 : Blo 814346 1740845 := bbase (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) (by norm_num)
theorem B1839149 : Blo 814346 1839149 := bbase (se 3 (by rfl) ⟨344840, by rfl⟩ : syracuseStep 1839149 = 689681) (by norm_num)
theorem B1839221 : Blo 814346 1839221 := bbase (se 5 (by rfl) ⟨86213, by rfl⟩ : syracuseStep 1839221 = 172427) (by norm_num)
theorem B1380469 : Blo 814346 1380469 := bbase (se 5 (by rfl) ⟨64709, by rfl⟩ : syracuseStep 1380469 = 129419) (by norm_num)
theorem B4198517 : Blo 814346 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B1740989 : Blo 814346 1740989 := bbase (se 3 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 1740989 = 652871) (by norm_num)
theorem B1839293 : Blo 814346 1839293 := bbase (se 3 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 1839293 = 689735) (by norm_num)
theorem B1380557 : Blo 814346 1380557 := bbase (se 3 (by rfl) ⟨258854, by rfl⟩ : syracuseStep 1380557 = 517709) (by norm_num)
theorem B1839365 : Blo 814346 1839365 := bbase (se 4 (by rfl) ⟨172440, by rfl⟩ : syracuseStep 1839365 = 344881) (by norm_num)
theorem B1839437 : Blo 814346 1839437 := bbase (se 3 (by rfl) ⟨344894, by rfl⟩ : syracuseStep 1839437 = 689789) (by norm_num)
theorem B1380685 : Blo 814346 1380685 := bbase (se 3 (by rfl) ⟨258878, by rfl⟩ : syracuseStep 1380685 = 517757) (by norm_num)
theorem B2068861 : Blo 814346 2068861 := bbase (se 3 (by rfl) ⟨387911, by rfl⟩ : syracuseStep 2068861 = 775823) (by norm_num)
theorem B1839509 : Blo 814346 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B1380773 : Blo 814346 1380773 := bbase (se 4 (by rfl) ⟨129447, by rfl⟩ : syracuseStep 1380773 = 258895) (by norm_num)
theorem B2757077 : Blo 814346 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B1839581 : Blo 814346 1839581 := bbase (se 3 (by rfl) ⟨344921, by rfl⟩ : syracuseStep 1839581 = 689843) (by norm_num)
theorem B2068973 : Blo 814346 2068973 := bbase (se 3 (by rfl) ⟨387932, by rfl⟩ : syracuseStep 2068973 = 775865) (by norm_num)
theorem B1839653 : Blo 814346 1839653 := bbase (se 4 (by rfl) ⟨172467, by rfl⟩ : syracuseStep 1839653 = 344935) (by norm_num)
theorem B1380901 : Blo 814346 1380901 := bbase (se 4 (by rfl) ⟨129459, by rfl⟩ : syracuseStep 1380901 = 258919) (by norm_num)
theorem B4133429 : Blo 814346 4133429 := bbase (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) (by norm_num)
theorem B1839725 : Blo 814346 1839725 := bbase (se 3 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 1839725 = 689897) (by norm_num)
theorem B2069165 : Blo 814346 2069165 := bbase (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) (by norm_num)
theorem B1839797 : Blo 814346 1839797 := bbase (se 5 (by rfl) ⟨86240, by rfl⟩ : syracuseStep 1839797 = 172481) (by norm_num)
theorem B1839869 : Blo 814346 1839869 := bbase (se 3 (by rfl) ⟨344975, by rfl⟩ : syracuseStep 1839869 = 689951) (by norm_num)
theorem B1839941 : Blo 814346 1839941 := bbase (se 4 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 1839941 = 344989) (by norm_num)
theorem B2757509 : Blo 814346 2757509 := bbase (se 4 (by rfl) ⟨258516, by rfl⟩ : syracuseStep 2757509 = 517033) (by norm_num)
theorem B1840013 : Blo 814346 1840013 := bbase (se 3 (by rfl) ⟨345002, by rfl⟩ : syracuseStep 1840013 = 690005) (by norm_num)
theorem B1741733 : Blo 814346 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B1840085 : Blo 814346 1840085 := bbase (se 7 (by rfl) ⟨21563, by rfl⟩ : syracuseStep 1840085 = 43127) (by norm_num)
theorem B2069509 : Blo 814346 2069509 := bbase (se 4 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 2069509 = 388033) (by norm_num)
theorem B1840157 : Blo 814346 1840157 := bbase (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) (by norm_num)
theorem B1840229 : Blo 814346 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B2069621 : Blo 814346 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B1840301 : Blo 814346 1840301 := bbase (se 3 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 1840301 = 690113) (by norm_num)
theorem B1840373 : Blo 814346 1840373 := bbase (se 5 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 1840373 = 172535) (by norm_num)
theorem B2757941 : Blo 814346 2757941 := bbase (se 5 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 2757941 = 258557) (by norm_num)
theorem B2069813 : Blo 814346 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B1840445 : Blo 814346 1840445 := bbase (se 3 (by rfl) ⟨345083, by rfl⟩ : syracuseStep 1840445 = 690167) (by norm_num)
theorem B1840517 : Blo 814346 1840517 := bbase (se 4 (by rfl) ⟨172548, by rfl⟩ : syracuseStep 1840517 = 345097) (by norm_num)
theorem B1840589 : Blo 814346 1840589 := bbase (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) (by norm_num)
theorem B1840661 : Blo 814346 1840661 := bbase (se 6 (by rfl) ⟨43140, by rfl⟩ : syracuseStep 1840661 = 86281) (by norm_num)
theorem B1840733 : Blo 814346 1840733 := bbase (se 3 (by rfl) ⟨345137, by rfl⟩ : syracuseStep 1840733 = 690275) (by norm_num)
theorem B2070157 : Blo 814346 2070157 := bbase (se 3 (by rfl) ⟨388154, by rfl⟩ : syracuseStep 2070157 = 776309) (by norm_num)
theorem B1742485 : Blo 814346 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B1840805 : Blo 814346 1840805 := bbase (se 4 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 1840805 = 345151) (by norm_num)
theorem B2758373 : Blo 814346 2758373 := bbase (se 4 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 2758373 = 517195) (by norm_num)
theorem B1840877 : Blo 814346 1840877 := bbase (se 3 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 1840877 = 690329) (by norm_num)
theorem B2070269 : Blo 814346 2070269 := bbase (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) (by norm_num)
theorem B1742629 : Blo 814346 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B1840949 : Blo 814346 1840949 := bbase (se 5 (by rfl) ⟨86294, by rfl⟩ : syracuseStep 1840949 = 172589) (by norm_num)
theorem B4134725 : Blo 814346 4134725 := bbase (se 4 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 4134725 = 775261) (by norm_num)
theorem B3479381 : Blo 814346 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1841021 : Blo 814346 1841021 := bbase (se 3 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 1841021 = 690383) (by norm_num)
theorem B1546141 : Blo 814346 1546141 := bbase (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) (by norm_num)
theorem B2070461 : Blo 814346 2070461 := bbase (se 3 (by rfl) ⟨388211, by rfl⟩ : syracuseStep 2070461 = 776423) (by norm_num)
theorem B1841093 : Blo 814346 1841093 := bbase (se 4 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 1841093 = 345205) (by norm_num)
theorem B9050069 : Blo 814346 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B1841165 : Blo 814346 1841165 := bbase (se 3 (by rfl) ⟨345218, by rfl⟩ : syracuseStep 1841165 = 690437) (by norm_num)
theorem B4659221 : Blo 814346 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B1546285 : Blo 814346 1546285 := bbase (se 3 (by rfl) ⟨289928, by rfl⟩ : syracuseStep 1546285 = 579857) (by norm_num)
theorem B1841237 : Blo 814346 1841237 := bbase (se 8 (by rfl) ⟨10788, by rfl⟩ : syracuseStep 1841237 = 21577) (by norm_num)
theorem B2758805 : Blo 814346 2758805 := bbase (se 6 (by rfl) ⟨64659, by rfl⟩ : syracuseStep 2758805 = 129319) (by norm_num)
theorem B1743005 : Blo 814346 1743005 := bbase (se 3 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 1743005 = 653627) (by norm_num)
theorem B3184805 : Blo 814346 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B1546445 : Blo 814346 1546445 := bbase (se 3 (by rfl) ⟨289958, by rfl⟩ : syracuseStep 1546445 = 579917) (by norm_num)
theorem B2070805 : Blo 814346 2070805 := bbase (se 6 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 2070805 = 97069) (by norm_num)
theorem B1546589 : Blo 814346 1546589 := bbase (se 3 (by rfl) ⟨289985, by rfl⟩ : syracuseStep 1546589 = 579971) (by norm_num)
theorem B2070917 : Blo 814346 2070917 := bbase (se 4 (by rfl) ⟨194148, by rfl⟩ : syracuseStep 2070917 = 388297) (by norm_num)
theorem B1743373 : Blo 814346 1743373 := bbase (se 3 (by rfl) ⟨326882, by rfl⟩ : syracuseStep 1743373 = 653765) (by norm_num)
theorem B2759237 : Blo 814346 2759237 := bbase (se 4 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 2759237 = 517357) (by norm_num)
theorem B2071109 : Blo 814346 2071109 := bbase (se 4 (by rfl) ⟨194166, by rfl⟩ : syracuseStep 2071109 = 388333) (by norm_num)
theorem B1546877 : Blo 814346 1546877 := bbase (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) (by norm_num)
theorem B1547029 : Blo 814346 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B6986645 : Blo 814346 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B2759669 : Blo 814346 2759669 := bbase (se 5 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 2759669 = 258719) (by norm_num)
theorem B1547333 : Blo 814346 1547333 := bbase (se 4 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 1547333 = 290125) (by norm_num)
theorem B826453 : Blo 814346 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B4136021 : Blo 814346 4136021 := bbase (se 8 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 4136021 = 48469) (by norm_num)
theorem B1023205 : Blo 814346 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B826777 : Blo 814346 826777 := bbase (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) (by norm_num)
theorem B2760101 : Blo 814346 2760101 := bbase (se 4 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 2760101 = 517519) (by norm_num)
theorem B3481157 : Blo 814346 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B4038437 : Blo 814346 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B1548085 : Blo 814346 1548085 := bbase (se 5 (by rfl) ⟨72566, by rfl⟩ : syracuseStep 1548085 = 145133) (by norm_num)
theorem B2760533 : Blo 814346 2760533 := bbase (se 9 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 2760533 = 16175) (by norm_num)
theorem B1548229 : Blo 814346 1548229 := bbase (se 4 (by rfl) ⟨145146, by rfl⟩ : syracuseStep 1548229 = 290293) (by norm_num)
theorem B1744877 : Blo 814346 1744877 := bbase (se 3 (by rfl) ⟨327164, by rfl⟩ : syracuseStep 1744877 = 654329) (by norm_num)
theorem B1679437 : Blo 814346 1679437 := bbase (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) (by norm_num)
theorem B1548389 : Blo 814346 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B1745021 : Blo 814346 1745021 := bbase (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) (by norm_num)
theorem B1548533 : Blo 814346 1548533 := bbase (se 5 (by rfl) ⟨72587, by rfl⟩ : syracuseStep 1548533 = 145175) (by norm_num)
theorem B2760965 : Blo 814346 2760965 := bbase (se 4 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 2760965 = 517681) (by norm_num)
theorem B4137317 : Blo 814346 4137317 := bbase (se 4 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 4137317 = 775747) (by norm_num)
theorem B1745381 : Blo 814346 1745381 := bbase (se 4 (by rfl) ⟨163629, by rfl⟩ : syracuseStep 1745381 = 327259) (by norm_num)
theorem B6201845 : Blo 814346 6201845 := bbase (se 5 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 6201845 = 581423) (by norm_num)
theorem B1548821 : Blo 814346 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B3482149 : Blo 814346 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B827977 : Blo 814346 827977 := bbase (se 2 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 827977 = 620983) (by norm_num)
theorem B4956821 : Blo 814346 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B1548973 : Blo 814346 1548973 := bbase (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) (by norm_num)
theorem B2761397 : Blo 814346 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B1221533 : Blo 814346 1221533 := bbase (se 3 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 1221533 = 458075) (by norm_num)
theorem B1221557 : Blo 814346 1221557 := bbase (se 5 (by rfl) ⟨57260, by rfl⟩ : syracuseStep 1221557 = 114521) (by norm_num)
theorem B1221581 : Blo 814346 1221581 := bbase (se 3 (by rfl) ⟨229046, by rfl⟩ : syracuseStep 1221581 = 458093) (by norm_num)
theorem B1549277 : Blo 814346 1549277 := bbase (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) (by norm_num)
theorem B1221605 : Blo 814346 1221605 := bbase (se 4 (by rfl) ⟨114525, by rfl⟩ : syracuseStep 1221605 = 229051) (by norm_num)
theorem B1221629 : Blo 814346 1221629 := bbase (se 3 (by rfl) ⟨229055, by rfl⟩ : syracuseStep 1221629 = 458111) (by norm_num)
theorem B1221653 : Blo 814346 1221653 := bbase (se 6 (by rfl) ⟨28632, by rfl⟩ : syracuseStep 1221653 = 57265) (by norm_num)
theorem B1221677 : Blo 814346 1221677 := bbase (se 3 (by rfl) ⟨229064, by rfl⟩ : syracuseStep 1221677 = 458129) (by norm_num)
theorem B1221701 : Blo 814346 1221701 := bbase (se 4 (by rfl) ⟨114534, by rfl⟩ : syracuseStep 1221701 = 229069) (by norm_num)
theorem B1221725 : Blo 814346 1221725 := bbase (se 3 (by rfl) ⟨229073, by rfl⟩ : syracuseStep 1221725 = 458147) (by norm_num)
theorem B2761829 : Blo 814346 2761829 := bbase (se 4 (by rfl) ⟨258921, by rfl⟩ : syracuseStep 2761829 = 517843) (by norm_num)
theorem B1221749 : Blo 814346 1221749 := bbase (se 5 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 1221749 = 114539) (by norm_num)
theorem B1221773 : Blo 814346 1221773 := bbase (se 3 (by rfl) ⟨229082, by rfl⟩ : syracuseStep 1221773 = 458165) (by norm_num)
theorem B1221797 : Blo 814346 1221797 := bbase (se 4 (by rfl) ⟨114543, by rfl⟩ : syracuseStep 1221797 = 229087) (by norm_num)
theorem B1221821 : Blo 814346 1221821 := bbase (se 3 (by rfl) ⟨229091, by rfl⟩ : syracuseStep 1221821 = 458183) (by norm_num)
theorem B1221845 : Blo 814346 1221845 := bbase (se 7 (by rfl) ⟨14318, by rfl⟩ : syracuseStep 1221845 = 28637) (by norm_num)
theorem B992473 : Blo 814346 992473 := bbase (se 2 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 992473 = 744355) (by norm_num)
theorem B1221869 : Blo 814346 1221869 := bbase (se 3 (by rfl) ⟨229100, by rfl⟩ : syracuseStep 1221869 = 458201) (by norm_num)
theorem B1221893 : Blo 814346 1221893 := bbase (se 4 (by rfl) ⟨114552, by rfl⟩ : syracuseStep 1221893 = 229105) (by norm_num)
theorem B1221917 : Blo 814346 1221917 := bbase (se 3 (by rfl) ⟨229109, by rfl⟩ : syracuseStep 1221917 = 458219) (by norm_num)
theorem B1221941 : Blo 814346 1221941 := bbase (se 5 (by rfl) ⟨57278, by rfl⟩ : syracuseStep 1221941 = 114557) (by norm_num)
theorem B5580085 : Blo 814346 5580085 := bbase (se 5 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 5580085 = 523133) (by norm_num)
theorem B1221965 : Blo 814346 1221965 := bbase (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) (by norm_num)
theorem B1746269 : Blo 814346 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B1680733 : Blo 814346 1680733 := bbase (se 3 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 1680733 = 630275) (by norm_num)
theorem B1221989 : Blo 814346 1221989 := bbase (se 4 (by rfl) ⟨114561, by rfl⟩ : syracuseStep 1221989 = 229123) (by norm_num)
theorem B1222013 : Blo 814346 1222013 := bbase (se 3 (by rfl) ⟨229127, by rfl⟩ : syracuseStep 1222013 = 458255) (by norm_num)
theorem B1222037 : Blo 814346 1222037 := bbase (se 6 (by rfl) ⟨28641, by rfl⟩ : syracuseStep 1222037 = 57283) (by norm_num)
theorem B1222061 : Blo 814346 1222061 := bbase (se 3 (by rfl) ⟨229136, by rfl⟩ : syracuseStep 1222061 = 458273) (by norm_num)
theorem B1222085 : Blo 814346 1222085 := bbase (se 4 (by rfl) ⟨114570, by rfl⟩ : syracuseStep 1222085 = 229141) (by norm_num)
theorem B8365525 : Blo 814346 8365525 := bbase (se 7 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 8365525 = 196067) (by norm_num)
theorem B1222109 : Blo 814346 1222109 := bbase (se 3 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 1222109 = 458291) (by norm_num)
theorem B1222133 : Blo 814346 1222133 := bbase (se 5 (by rfl) ⟨57287, by rfl⟩ : syracuseStep 1222133 = 114575) (by norm_num)
theorem B1222157 : Blo 814346 1222157 := bbase (se 3 (by rfl) ⟨229154, by rfl⟩ : syracuseStep 1222157 = 458309) (by norm_num)
theorem B1222181 : Blo 814346 1222181 := bbase (se 4 (by rfl) ⟨114579, by rfl⟩ : syracuseStep 1222181 = 229159) (by norm_num)
theorem B1222205 : Blo 814346 1222205 := bbase (se 3 (by rfl) ⟨229163, by rfl⟩ : syracuseStep 1222205 = 458327) (by norm_num)
theorem B1222229 : Blo 814346 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B1746517 : Blo 814346 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B1222253 : Blo 814346 1222253 := bbase (se 3 (by rfl) ⟨229172, by rfl⟩ : syracuseStep 1222253 = 458345) (by norm_num)
theorem B4138613 : Blo 814346 4138613 := bbase (se 5 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 4138613 = 387995) (by norm_num)
theorem B1222277 : Blo 814346 1222277 := bbase (se 4 (by rfl) ⟨114588, by rfl⟩ : syracuseStep 1222277 = 229177) (by norm_num)
theorem B1222301 : Blo 814346 1222301 := bbase (se 3 (by rfl) ⟨229181, by rfl⟩ : syracuseStep 1222301 = 458363) (by norm_num)
theorem B1222325 : Blo 814346 1222325 := bbase (se 5 (by rfl) ⟨57296, by rfl⟩ : syracuseStep 1222325 = 114593) (by norm_num)
theorem B1222349 : Blo 814346 1222349 := bbase (se 3 (by rfl) ⟨229190, by rfl⟩ : syracuseStep 1222349 = 458381) (by norm_num)
theorem B1550029 : Blo 814346 1550029 := bbase (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) (by norm_num)
theorem B1222373 : Blo 814346 1222373 := bbase (se 4 (by rfl) ⟨114597, by rfl⟩ : syracuseStep 1222373 = 229195) (by norm_num)
theorem B1222397 : Blo 814346 1222397 := bbase (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) (by norm_num)
theorem B1222421 : Blo 814346 1222421 := bbase (se 6 (by rfl) ⟨28650, by rfl⟩ : syracuseStep 1222421 = 57301) (by norm_num)
theorem B1222445 : Blo 814346 1222445 := bbase (se 3 (by rfl) ⟨229208, by rfl⟩ : syracuseStep 1222445 = 458417) (by norm_num)
theorem B1222469 : Blo 814346 1222469 := bbase (se 4 (by rfl) ⟨114606, by rfl⟩ : syracuseStep 1222469 = 229213) (by norm_num)
theorem B1222493 : Blo 814346 1222493 := bbase (se 3 (by rfl) ⟨229217, by rfl⟩ : syracuseStep 1222493 = 458435) (by norm_num)
theorem B1550173 : Blo 814346 1550173 := bbase (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) (by norm_num)
theorem B1222517 : Blo 814346 1222517 := bbase (se 5 (by rfl) ⟨57305, by rfl⟩ : syracuseStep 1222517 = 114611) (by norm_num)
theorem B1222541 : Blo 814346 1222541 := bbase (se 3 (by rfl) ⟨229226, by rfl⟩ : syracuseStep 1222541 = 458453) (by norm_num)
theorem B1222565 : Blo 814346 1222565 := bbase (se 4 (by rfl) ⟨114615, by rfl⟩ : syracuseStep 1222565 = 229231) (by norm_num)
theorem B1222589 : Blo 814346 1222589 := bbase (se 3 (by rfl) ⟨229235, by rfl⟩ : syracuseStep 1222589 = 458471) (by norm_num)
theorem B1222613 : Blo 814346 1222613 := bbase (se 7 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 1222613 = 28655) (by norm_num)
theorem B1222637 : Blo 814346 1222637 := bbase (se 3 (by rfl) ⟨229244, by rfl⟩ : syracuseStep 1222637 = 458489) (by norm_num)
theorem B1550333 : Blo 814346 1550333 := bbase (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) (by norm_num)
theorem B1222661 : Blo 814346 1222661 := bbase (se 4 (by rfl) ⟨114624, by rfl⟩ : syracuseStep 1222661 = 229249) (by norm_num)
theorem B1222685 : Blo 814346 1222685 := bbase (se 3 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 1222685 = 458507) (by norm_num)
theorem B1222709 : Blo 814346 1222709 := bbase (se 5 (by rfl) ⟨57314, by rfl⟩ : syracuseStep 1222709 = 114629) (by norm_num)
theorem B829501 : Blo 814346 829501 := bbase (se 3 (by rfl) ⟨155531, by rfl⟩ : syracuseStep 829501 = 311063) (by norm_num)
theorem B1222733 : Blo 814346 1222733 := bbase (se 3 (by rfl) ⟨229262, by rfl⟩ : syracuseStep 1222733 = 458525) (by norm_num)
theorem B1747021 : Blo 814346 1747021 := bbase (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) (by norm_num)
theorem B1222757 : Blo 814346 1222757 := bbase (se 4 (by rfl) ⟨114633, by rfl⟩ : syracuseStep 1222757 = 229267) (by norm_num)
theorem B1222781 : Blo 814346 1222781 := bbase (se 3 (by rfl) ⟨229271, by rfl⟩ : syracuseStep 1222781 = 458543) (by norm_num)
theorem B1550477 : Blo 814346 1550477 := bbase (se 3 (by rfl) ⟨290714, by rfl⟩ : syracuseStep 1550477 = 581429) (by norm_num)
theorem B1222805 : Blo 814346 1222805 := bbase (se 6 (by rfl) ⟨28659, by rfl⟩ : syracuseStep 1222805 = 57319) (by norm_num)
theorem B6629525 : Blo 814346 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B1222829 : Blo 814346 1222829 := bbase (se 3 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 1222829 = 458561) (by norm_num)
theorem B1222853 : Blo 814346 1222853 := bbase (se 4 (by rfl) ⟨114642, by rfl⟩ : syracuseStep 1222853 = 229285) (by norm_num)
theorem B1222877 : Blo 814346 1222877 := bbase (se 3 (by rfl) ⟨229289, by rfl⟩ : syracuseStep 1222877 = 458579) (by norm_num)
theorem B1222901 : Blo 814346 1222901 := bbase (se 5 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 1222901 = 114647) (by norm_num)
theorem B1222925 : Blo 814346 1222925 := bbase (se 3 (by rfl) ⟨229298, by rfl⟩ : syracuseStep 1222925 = 458597) (by norm_num)
theorem B1222949 : Blo 814346 1222949 := bbase (se 4 (by rfl) ⟨114651, by rfl⟩ : syracuseStep 1222949 = 229303) (by norm_num)
theorem B1222973 : Blo 814346 1222973 := bbase (se 3 (by rfl) ⟨229307, by rfl⟩ : syracuseStep 1222973 = 458615) (by norm_num)
theorem B44607829 : Blo 814346 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B1222997 : Blo 814346 1222997 := bbase (se 10 (by rfl) ⟨1791, by rfl⟩ : syracuseStep 1222997 = 3583) (by norm_num)
theorem B1223021 : Blo 814346 1223021 := bbase (se 3 (by rfl) ⟨229316, by rfl⟩ : syracuseStep 1223021 = 458633) (by norm_num)
theorem B1223045 : Blo 814346 1223045 := bbase (se 4 (by rfl) ⟨114660, by rfl⟩ : syracuseStep 1223045 = 229321) (by norm_num)
theorem B1223069 : Blo 814346 1223069 := bbase (se 3 (by rfl) ⟨229325, by rfl⟩ : syracuseStep 1223069 = 458651) (by norm_num)
theorem B1550765 : Blo 814346 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B1223093 : Blo 814346 1223093 := bbase (se 5 (by rfl) ⟨57332, by rfl⟩ : syracuseStep 1223093 = 114665) (by norm_num)
theorem B1223117 : Blo 814346 1223117 := bbase (se 3 (by rfl) ⟨229334, by rfl⟩ : syracuseStep 1223117 = 458669) (by norm_num)
theorem B1223141 : Blo 814346 1223141 := bbase (se 4 (by rfl) ⟨114669, by rfl⟩ : syracuseStep 1223141 = 229339) (by norm_num)
theorem B1223165 : Blo 814346 1223165 := bbase (se 3 (by rfl) ⟨229343, by rfl⟩ : syracuseStep 1223165 = 458687) (by norm_num)
theorem B1223189 : Blo 814346 1223189 := bbase (se 6 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 1223189 = 57337) (by norm_num)
theorem B1223213 : Blo 814346 1223213 := bbase (se 3 (by rfl) ⟨229352, by rfl⟩ : syracuseStep 1223213 = 458705) (by norm_num)
theorem B1223237 : Blo 814346 1223237 := bbase (se 4 (by rfl) ⟨114678, by rfl⟩ : syracuseStep 1223237 = 229357) (by norm_num)
theorem B1550917 : Blo 814346 1550917 := bbase (se 4 (by rfl) ⟨145398, by rfl⟩ : syracuseStep 1550917 = 290797) (by norm_num)
theorem B1223261 : Blo 814346 1223261 := bbase (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) (by norm_num)
theorem B1223285 : Blo 814346 1223285 := bbase (se 5 (by rfl) ⟨57341, by rfl⟩ : syracuseStep 1223285 = 114683) (by norm_num)
theorem B1223309 : Blo 814346 1223309 := bbase (se 3 (by rfl) ⟨229370, by rfl⟩ : syracuseStep 1223309 = 458741) (by norm_num)
theorem B1223333 : Blo 814346 1223333 := bbase (se 4 (by rfl) ⟨114687, by rfl⟩ : syracuseStep 1223333 = 229375) (by norm_num)
theorem B1223357 : Blo 814346 1223357 := bbase (se 3 (by rfl) ⟨229379, by rfl⟩ : syracuseStep 1223357 = 458759) (by norm_num)
theorem B1223381 : Blo 814346 1223381 := bbase (se 7 (by rfl) ⟨14336, by rfl⟩ : syracuseStep 1223381 = 28673) (by norm_num)
theorem B1223405 : Blo 814346 1223405 := bbase (se 3 (by rfl) ⟨229388, by rfl⟩ : syracuseStep 1223405 = 458777) (by norm_num)
theorem B1223429 : Blo 814346 1223429 := bbase (se 4 (by rfl) ⟨114696, by rfl⟩ : syracuseStep 1223429 = 229393) (by norm_num)
theorem B1223453 : Blo 814346 1223453 := bbase (se 3 (by rfl) ⟨229397, by rfl⟩ : syracuseStep 1223453 = 458795) (by norm_num)
theorem B1059625 : Blo 814346 1059625 := bbase (se 2 (by rfl) ⟨397359, by rfl⟩ : syracuseStep 1059625 = 794719) (by norm_num)
theorem B1223477 : Blo 814346 1223477 := bbase (se 5 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 1223477 = 114701) (by norm_num)
theorem B1223501 : Blo 814346 1223501 := bbase (se 3 (by rfl) ⟨229406, by rfl⟩ : syracuseStep 1223501 = 458813) (by norm_num)
theorem B1223525 : Blo 814346 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B1551221 : Blo 814346 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B1223549 : Blo 814346 1223549 := bbase (se 3 (by rfl) ⟨229415, by rfl⟩ : syracuseStep 1223549 = 458831) (by norm_num)
theorem B4139909 : Blo 814346 4139909 := bbase (se 4 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 4139909 = 776233) (by norm_num)
theorem B6269845 : Blo 814346 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B1223573 : Blo 814346 1223573 := bbase (se 6 (by rfl) ⟨28677, by rfl⟩ : syracuseStep 1223573 = 57355) (by norm_num)
theorem B1223597 : Blo 814346 1223597 := bbase (se 3 (by rfl) ⟨229424, by rfl⟩ : syracuseStep 1223597 = 458849) (by norm_num)
theorem B1223621 : Blo 814346 1223621 := bbase (se 4 (by rfl) ⟨114714, by rfl⟩ : syracuseStep 1223621 = 229429) (by norm_num)
theorem B1223645 : Blo 814346 1223645 := bbase (se 3 (by rfl) ⟨229433, by rfl⟩ : syracuseStep 1223645 = 458867) (by norm_num)
theorem B1223669 : Blo 814346 1223669 := bbase (se 5 (by rfl) ⟨57359, by rfl⟩ : syracuseStep 1223669 = 114719) (by norm_num)
theorem B1223693 : Blo 814346 1223693 := bbase (se 3 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 1223693 = 458885) (by norm_num)
theorem B1223717 : Blo 814346 1223717 := bbase (se 4 (by rfl) ⟨114723, by rfl⟩ : syracuseStep 1223717 = 229447) (by norm_num)
theorem B1223741 : Blo 814346 1223741 := bbase (se 3 (by rfl) ⟨229451, by rfl⟩ : syracuseStep 1223741 = 458903) (by norm_num)
theorem B1223765 : Blo 814346 1223765 := bbase (se 8 (by rfl) ⟨7170, by rfl⟩ : syracuseStep 1223765 = 14341) (by norm_num)
theorem B1223789 : Blo 814346 1223789 := bbase (se 3 (by rfl) ⟨229460, by rfl⟩ : syracuseStep 1223789 = 458921) (by norm_num)
theorem B1223813 : Blo 814346 1223813 := bbase (se 4 (by rfl) ⟨114732, by rfl⟩ : syracuseStep 1223813 = 229465) (by norm_num)
theorem B1223837 : Blo 814346 1223837 := bbase (se 3 (by rfl) ⟨229469, by rfl⟩ : syracuseStep 1223837 = 458939) (by norm_num)
theorem B1223861 : Blo 814346 1223861 := bbase (se 5 (by rfl) ⟨57368, by rfl⟩ : syracuseStep 1223861 = 114737) (by norm_num)
theorem B1223885 : Blo 814346 1223885 := bbase (se 3 (by rfl) ⟨229478, by rfl⟩ : syracuseStep 1223885 = 458957) (by norm_num)
theorem B1223909 : Blo 814346 1223909 := bbase (se 4 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 1223909 = 229483) (by norm_num)
theorem B7843061 : Blo 814346 7843061 := bbase (se 5 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 7843061 = 735287) (by norm_num)
theorem B1223933 : Blo 814346 1223933 := bbase (se 3 (by rfl) ⟨229487, by rfl⟩ : syracuseStep 1223933 = 458975) (by norm_num)
theorem B1223957 : Blo 814346 1223957 := bbase (se 6 (by rfl) ⟨28686, by rfl⟩ : syracuseStep 1223957 = 57373) (by norm_num)
theorem B1223981 : Blo 814346 1223981 := bbase (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) (by norm_num)
theorem B1224005 : Blo 814346 1224005 := bbase (se 4 (by rfl) ⟨114750, by rfl⟩ : syracuseStep 1224005 = 229501) (by norm_num)
theorem B1224029 : Blo 814346 1224029 := bbase (se 3 (by rfl) ⟨229505, by rfl⟩ : syracuseStep 1224029 = 459011) (by norm_num)
theorem B1224053 : Blo 814346 1224053 := bbase (se 5 (by rfl) ⟨57377, by rfl⟩ : syracuseStep 1224053 = 114755) (by norm_num)
theorem B1224077 : Blo 814346 1224077 := bbase (se 3 (by rfl) ⟨229514, by rfl⟩ : syracuseStep 1224077 = 459029) (by norm_num)
theorem B1224101 : Blo 814346 1224101 := bbase (se 4 (by rfl) ⟨114759, by rfl⟩ : syracuseStep 1224101 = 229519) (by norm_num)
theorem B1224125 : Blo 814346 1224125 := bbase (se 3 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 1224125 = 459047) (by norm_num)
theorem B1224149 : Blo 814346 1224149 := bbase (se 7 (by rfl) ⟨14345, by rfl⟩ : syracuseStep 1224149 = 28691) (by norm_num)
theorem B1224173 : Blo 814346 1224173 := bbase (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) (by norm_num)
theorem B1224197 : Blo 814346 1224197 := bbase (se 4 (by rfl) ⟨114768, by rfl⟩ : syracuseStep 1224197 = 229537) (by norm_num)
theorem B1224221 : Blo 814346 1224221 := bbase (se 3 (by rfl) ⟨229541, by rfl⟩ : syracuseStep 1224221 = 459083) (by norm_num)
theorem B1224245 : Blo 814346 1224245 := bbase (se 5 (by rfl) ⟨57386, by rfl⟩ : syracuseStep 1224245 = 114773) (by norm_num)
theorem B1224269 : Blo 814346 1224269 := bbase (se 3 (by rfl) ⟨229550, by rfl⟩ : syracuseStep 1224269 = 459101) (by norm_num)
theorem B3092053 : Blo 814346 3092053 := bbase (se 8 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 3092053 = 36235) (by norm_num)
theorem B1224293 : Blo 814346 1224293 := bbase (se 4 (by rfl) ⟨114777, by rfl⟩ : syracuseStep 1224293 = 229555) (by norm_num)
theorem B2207333 : Blo 814346 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B1551973 : Blo 814346 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B1224317 : Blo 814346 1224317 := bbase (se 3 (by rfl) ⟨229559, by rfl⟩ : syracuseStep 1224317 = 459119) (by norm_num)
theorem B1224341 : Blo 814346 1224341 := bbase (se 6 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 1224341 = 57391) (by norm_num)
theorem B2240165 : Blo 814346 2240165 := bbase (se 4 (by rfl) ⟨210015, by rfl⟩ : syracuseStep 2240165 = 420031) (by norm_num)
theorem B1224365 : Blo 814346 1224365 := bbase (se 3 (by rfl) ⟨229568, by rfl⟩ : syracuseStep 1224365 = 459137) (by norm_num)
theorem B1224389 : Blo 814346 1224389 := bbase (se 4 (by rfl) ⟨114786, by rfl⟩ : syracuseStep 1224389 = 229573) (by norm_num)
theorem B1224413 : Blo 814346 1224413 := bbase (se 3 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 1224413 = 459155) (by norm_num)
theorem B1224437 : Blo 814346 1224437 := bbase (se 5 (by rfl) ⟨57395, by rfl⟩ : syracuseStep 1224437 = 114791) (by norm_num)
theorem B1552117 : Blo 814346 1552117 := bbase (se 5 (by rfl) ⟨72755, by rfl⟩ : syracuseStep 1552117 = 145511) (by norm_num)
theorem B1224461 : Blo 814346 1224461 := bbase (se 3 (by rfl) ⟨229586, by rfl⟩ : syracuseStep 1224461 = 459173) (by norm_num)
theorem B1224485 : Blo 814346 1224485 := bbase (se 4 (by rfl) ⟨114795, by rfl⟩ : syracuseStep 1224485 = 229591) (by norm_num)
theorem B1224509 : Blo 814346 1224509 := bbase (se 3 (by rfl) ⟨229595, by rfl⟩ : syracuseStep 1224509 = 459191) (by norm_num)
theorem B1224533 : Blo 814346 1224533 := bbase (se 9 (by rfl) ⟨3587, by rfl⟩ : syracuseStep 1224533 = 7175) (by norm_num)
theorem B1224557 : Blo 814346 1224557 := bbase (se 3 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 1224557 = 459209) (by norm_num)
theorem B3092357 : Blo 814346 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B1224581 : Blo 814346 1224581 := bbase (se 4 (by rfl) ⟨114804, by rfl⟩ : syracuseStep 1224581 = 229609) (by norm_num)
theorem B1552277 : Blo 814346 1552277 := bbase (se 6 (by rfl) ⟨36381, by rfl⟩ : syracuseStep 1552277 = 72763) (by norm_num)
theorem B1224605 : Blo 814346 1224605 := bbase (se 3 (by rfl) ⟨229613, by rfl⟩ : syracuseStep 1224605 = 459227) (by norm_num)
theorem B1224629 : Blo 814346 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B1224653 : Blo 814346 1224653 := bbase (se 3 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 1224653 = 459245) (by norm_num)
theorem B1224677 : Blo 814346 1224677 := bbase (se 4 (by rfl) ⟨114813, by rfl⟩ : syracuseStep 1224677 = 229627) (by norm_num)
theorem B929777 : Blo 814346 929777 := bbase (se 2 (by rfl) ⟨348666, by rfl⟩ : syracuseStep 929777 = 697333) (by norm_num)
theorem B1224701 : Blo 814346 1224701 := bbase (se 3 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 1224701 = 459263) (by norm_num)
theorem B1224725 : Blo 814346 1224725 := bbase (se 6 (by rfl) ⟨28704, by rfl⟩ : syracuseStep 1224725 = 57409) (by norm_num)
theorem B1552421 : Blo 814346 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1224749 : Blo 814346 1224749 := bbase (se 3 (by rfl) ⟨229640, by rfl⟩ : syracuseStep 1224749 = 459281) (by norm_num)
theorem B1224773 : Blo 814346 1224773 := bbase (se 4 (by rfl) ⟨114822, by rfl⟩ : syracuseStep 1224773 = 229645) (by norm_num)
theorem B1224797 : Blo 814346 1224797 := bbase (se 3 (by rfl) ⟨229649, by rfl⟩ : syracuseStep 1224797 = 459299) (by norm_num)
theorem B1224821 : Blo 814346 1224821 := bbase (se 5 (by rfl) ⟨57413, by rfl⟩ : syracuseStep 1224821 = 114827) (by norm_num)
theorem B1224845 : Blo 814346 1224845 := bbase (se 3 (by rfl) ⟨229658, by rfl⟩ : syracuseStep 1224845 = 459317) (by norm_num)
theorem B4141205 : Blo 814346 4141205 := bbase (se 6 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 4141205 = 194119) (by norm_num)
theorem B1224869 : Blo 814346 1224869 := bbase (se 4 (by rfl) ⟨114831, by rfl⟩ : syracuseStep 1224869 = 229663) (by norm_num)
theorem B1224893 : Blo 814346 1224893 := bbase (se 3 (by rfl) ⟨229667, by rfl⟩ : syracuseStep 1224893 = 459335) (by norm_num)
theorem B1224917 : Blo 814346 1224917 := bbase (se 7 (by rfl) ⟨14354, by rfl⟩ : syracuseStep 1224917 = 28709) (by norm_num)
theorem B1224941 : Blo 814346 1224941 := bbase (se 3 (by rfl) ⟨229676, by rfl⟩ : syracuseStep 1224941 = 459353) (by norm_num)
theorem B1224965 : Blo 814346 1224965 := bbase (se 4 (by rfl) ⟨114840, by rfl⟩ : syracuseStep 1224965 = 229681) (by norm_num)
theorem B1224989 : Blo 814346 1224989 := bbase (se 3 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 1224989 = 459371) (by norm_num)
theorem B1225013 : Blo 814346 1225013 := bbase (se 5 (by rfl) ⟨57422, by rfl⟩ : syracuseStep 1225013 = 114845) (by norm_num)
theorem B1552709 : Blo 814346 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B1225037 : Blo 814346 1225037 := bbase (se 3 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 1225037 = 459389) (by norm_num)
theorem B1225061 : Blo 814346 1225061 := bbase (se 4 (by rfl) ⟨114849, by rfl⟩ : syracuseStep 1225061 = 229699) (by norm_num)
theorem B995689 : Blo 814346 995689 := bbase (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) (by norm_num)
theorem B1225085 : Blo 814346 1225085 := bbase (se 3 (by rfl) ⟨229703, by rfl⟩ : syracuseStep 1225085 = 459407) (by norm_num)
theorem B1225109 : Blo 814346 1225109 := bbase (se 6 (by rfl) ⟨28713, by rfl⟩ : syracuseStep 1225109 = 57427) (by norm_num)
theorem B1225133 : Blo 814346 1225133 := bbase (se 3 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 1225133 = 459425) (by norm_num)
theorem B1225157 : Blo 814346 1225157 := bbase (se 4 (by rfl) ⟨114858, by rfl⟩ : syracuseStep 1225157 = 229717) (by norm_num)
theorem B1225181 : Blo 814346 1225181 := bbase (se 3 (by rfl) ⟨229721, by rfl⟩ : syracuseStep 1225181 = 459443) (by norm_num)
theorem B1552861 : Blo 814346 1552861 := bbase (se 3 (by rfl) ⟨291161, by rfl⟩ : syracuseStep 1552861 = 582323) (by norm_num)
theorem B1225205 : Blo 814346 1225205 := bbase (se 5 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 1225205 = 114863) (by norm_num)
theorem B1225229 : Blo 814346 1225229 := bbase (se 3 (by rfl) ⟨229730, by rfl⟩ : syracuseStep 1225229 = 459461) (by norm_num)
theorem B1225253 : Blo 814346 1225253 := bbase (se 4 (by rfl) ⟨114867, by rfl⟩ : syracuseStep 1225253 = 229735) (by norm_num)
theorem B1225277 : Blo 814346 1225277 := bbase (se 3 (by rfl) ⟨229739, by rfl⟩ : syracuseStep 1225277 = 459479) (by norm_num)
theorem B1225301 : Blo 814346 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1225325 : Blo 814346 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B1159805 : Blo 814346 1159805 := bbase (se 3 (by rfl) ⟨217463, by rfl⟩ : syracuseStep 1159805 = 434927) (by norm_num)
theorem B1225349 : Blo 814346 1225349 := bbase (se 4 (by rfl) ⟨114876, by rfl⟩ : syracuseStep 1225349 = 229753) (by norm_num)
theorem B1225373 : Blo 814346 1225373 := bbase (se 3 (by rfl) ⟨229757, by rfl⟩ : syracuseStep 1225373 = 459515) (by norm_num)
theorem B1225397 : Blo 814346 1225397 := bbase (se 5 (by rfl) ⟨57440, by rfl⟩ : syracuseStep 1225397 = 114881) (by norm_num)
theorem B6632117 : Blo 814346 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B1225421 : Blo 814346 1225421 := bbase (se 3 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 1225421 = 459533) (by norm_num)
theorem B1225445 : Blo 814346 1225445 := bbase (se 4 (by rfl) ⟨114885, by rfl⟩ : syracuseStep 1225445 = 229771) (by norm_num)
theorem B1225469 : Blo 814346 1225469 := bbase (se 3 (by rfl) ⟨229775, by rfl⟩ : syracuseStep 1225469 = 459551) (by norm_num)
theorem B1553165 : Blo 814346 1553165 := bbase (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) (by norm_num)
theorem B1225493 : Blo 814346 1225493 := bbase (se 6 (by rfl) ⟨28722, by rfl⟩ : syracuseStep 1225493 = 57445) (by norm_num)
theorem B1225517 : Blo 814346 1225517 := bbase (se 3 (by rfl) ⟨229784, by rfl⟩ : syracuseStep 1225517 = 459569) (by norm_num)
theorem B1225541 : Blo 814346 1225541 := bbase (se 4 (by rfl) ⟨114894, by rfl⟩ : syracuseStep 1225541 = 229789) (by norm_num)
theorem B1225565 : Blo 814346 1225565 := bbase (se 3 (by rfl) ⟨229793, by rfl⟩ : syracuseStep 1225565 = 459587) (by norm_num)
theorem B1225589 : Blo 814346 1225589 := bbase (se 5 (by rfl) ⟨57449, by rfl⟩ : syracuseStep 1225589 = 114899) (by norm_num)
theorem B1225613 : Blo 814346 1225613 := bbase (se 3 (by rfl) ⟨229802, by rfl⟩ : syracuseStep 1225613 = 459605) (by norm_num)
theorem B1225637 : Blo 814346 1225637 := bbase (se 4 (by rfl) ⟨114903, by rfl⟩ : syracuseStep 1225637 = 229807) (by norm_num)
theorem B1225661 : Blo 814346 1225661 := bbase (se 3 (by rfl) ⟨229811, by rfl⟩ : syracuseStep 1225661 = 459623) (by norm_num)
theorem B1225685 : Blo 814346 1225685 := bbase (se 7 (by rfl) ⟨14363, by rfl⟩ : syracuseStep 1225685 = 28727) (by norm_num)
theorem B1225709 : Blo 814346 1225709 := bbase (se 3 (by rfl) ⟨229820, by rfl⟩ : syracuseStep 1225709 = 459641) (by norm_num)
theorem B1225733 : Blo 814346 1225733 := bbase (se 4 (by rfl) ⟨114912, by rfl⟩ : syracuseStep 1225733 = 229825) (by norm_num)
theorem B1225757 : Blo 814346 1225757 := bbase (se 3 (by rfl) ⟨229829, by rfl⟩ : syracuseStep 1225757 = 459659) (by norm_num)
theorem B1225781 : Blo 814346 1225781 := bbase (se 5 (by rfl) ⟨57458, by rfl⟩ : syracuseStep 1225781 = 114917) (by norm_num)
theorem B1225805 : Blo 814346 1225805 := bbase (se 3 (by rfl) ⟨229838, by rfl⟩ : syracuseStep 1225805 = 459677) (by norm_num)
theorem B1225829 : Blo 814346 1225829 := bbase (se 4 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 1225829 = 229843) (by norm_num)
theorem B1225853 : Blo 814346 1225853 := bbase (se 3 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 1225853 = 459695) (by norm_num)
theorem B1225877 : Blo 814346 1225877 := bbase (se 6 (by rfl) ⟨28731, by rfl⟩ : syracuseStep 1225877 = 57463) (by norm_num)
theorem B1225901 : Blo 814346 1225901 := bbase (se 3 (by rfl) ⟨229856, by rfl⟩ : syracuseStep 1225901 = 459713) (by norm_num)
theorem B1225925 : Blo 814346 1225925 := bbase (se 4 (by rfl) ⟨114930, by rfl⟩ : syracuseStep 1225925 = 229861) (by norm_num)
theorem B1225949 : Blo 814346 1225949 := bbase (se 3 (by rfl) ⟨229865, by rfl⟩ : syracuseStep 1225949 = 459731) (by norm_num)
theorem B1225973 : Blo 814346 1225973 := bbase (se 5 (by rfl) ⟨57467, by rfl⟩ : syracuseStep 1225973 = 114935) (by norm_num)
theorem B1225997 : Blo 814346 1225997 := bbase (se 3 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 1225997 = 459749) (by norm_num)
theorem B1226021 : Blo 814346 1226021 := bbase (se 4 (by rfl) ⟨114939, by rfl⟩ : syracuseStep 1226021 = 229879) (by norm_num)
theorem B1226045 : Blo 814346 1226045 := bbase (se 3 (by rfl) ⟨229883, by rfl⟩ : syracuseStep 1226045 = 459767) (by norm_num)
theorem B1226069 : Blo 814346 1226069 := bbase (se 13 (by rfl) ⟨224, by rfl⟩ : syracuseStep 1226069 = 449) (by norm_num)
theorem B1226093 : Blo 814346 1226093 := bbase (se 3 (by rfl) ⟨229892, by rfl⟩ : syracuseStep 1226093 = 459785) (by norm_num)
theorem B1226117 : Blo 814346 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B1226141 : Blo 814346 1226141 := bbase (se 3 (by rfl) ⟨229901, by rfl⟩ : syracuseStep 1226141 = 459803) (by norm_num)
theorem B4142501 : Blo 814346 4142501 := bbase (se 4 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 4142501 = 776719) (by norm_num)
theorem B3487157 : Blo 814346 3487157 := bbase (se 5 (by rfl) ⟨163460, by rfl⟩ : syracuseStep 3487157 = 326921) (by norm_num)
theorem B1226165 : Blo 814346 1226165 := bbase (se 5 (by rfl) ⟨57476, by rfl⟩ : syracuseStep 1226165 = 114953) (by norm_num)
theorem B1226189 : Blo 814346 1226189 := bbase (se 3 (by rfl) ⟨229910, by rfl⟩ : syracuseStep 1226189 = 459821) (by norm_num)
theorem B1258973 : Blo 814346 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B1226213 : Blo 814346 1226213 := bbase (se 4 (by rfl) ⟨114957, by rfl⟩ : syracuseStep 1226213 = 229915) (by norm_num)
theorem B1226237 : Blo 814346 1226237 := bbase (se 3 (by rfl) ⟨229919, by rfl⟩ : syracuseStep 1226237 = 459839) (by norm_num)
theorem B1226261 : Blo 814346 1226261 := bbase (se 6 (by rfl) ⟨28740, by rfl⟩ : syracuseStep 1226261 = 57481) (by norm_num)
theorem B1226285 : Blo 814346 1226285 := bbase (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) (by norm_num)
theorem B1226309 : Blo 814346 1226309 := bbase (se 4 (by rfl) ⟨114966, by rfl⟩ : syracuseStep 1226309 = 229933) (by norm_num)
theorem B1226333 : Blo 814346 1226333 := bbase (se 3 (by rfl) ⟨229937, by rfl⟩ : syracuseStep 1226333 = 459875) (by norm_num)
theorem B1226357 : Blo 814346 1226357 := bbase (se 5 (by rfl) ⟨57485, by rfl⟩ : syracuseStep 1226357 = 114971) (by norm_num)
theorem B1226381 : Blo 814346 1226381 := bbase (se 3 (by rfl) ⟨229946, by rfl⟩ : syracuseStep 1226381 = 459893) (by norm_num)
theorem B1226405 : Blo 814346 1226405 := bbase (se 4 (by rfl) ⟨114975, by rfl⟩ : syracuseStep 1226405 = 229951) (by norm_num)
theorem B1226429 : Blo 814346 1226429 := bbase (se 3 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 1226429 = 459911) (by norm_num)
theorem B1226453 : Blo 814346 1226453 := bbase (se 7 (by rfl) ⟨14372, by rfl⟩ : syracuseStep 1226453 = 28745) (by norm_num)
theorem B3487445 : Blo 814346 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B1226477 : Blo 814346 1226477 := bbase (se 3 (by rfl) ⟨229964, by rfl⟩ : syracuseStep 1226477 = 459929) (by norm_num)
theorem B1226501 : Blo 814346 1226501 := bbase (se 4 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 1226501 = 229969) (by norm_num)
theorem B1226525 : Blo 814346 1226525 := bbase (se 3 (by rfl) ⟨229973, by rfl⟩ : syracuseStep 1226525 = 459947) (by norm_num)
theorem B1226549 : Blo 814346 1226549 := bbase (se 5 (by rfl) ⟨57494, by rfl⟩ : syracuseStep 1226549 = 114989) (by norm_num)
theorem B1226573 : Blo 814346 1226573 := bbase (se 3 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 1226573 = 459965) (by norm_num)
theorem B1226597 : Blo 814346 1226597 := bbase (se 4 (by rfl) ⟨114993, by rfl⟩ : syracuseStep 1226597 = 229987) (by norm_num)
theorem B1226621 : Blo 814346 1226621 := bbase (se 3 (by rfl) ⟨229991, by rfl⟩ : syracuseStep 1226621 = 459983) (by norm_num)
theorem B1226645 : Blo 814346 1226645 := bbase (se 6 (by rfl) ⟨28749, by rfl⟩ : syracuseStep 1226645 = 57499) (by norm_num)
theorem B1226669 : Blo 814346 1226669 := bbase (se 3 (by rfl) ⟨230000, by rfl⟩ : syracuseStep 1226669 = 460001) (by norm_num)
theorem B3094469 : Blo 814346 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B1226693 : Blo 814346 1226693 := bbase (se 4 (by rfl) ⟨115002, by rfl⟩ : syracuseStep 1226693 = 230005) (by norm_num)
theorem B1226717 : Blo 814346 1226717 := bbase (se 3 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 1226717 = 460019) (by norm_num)
theorem B1226741 : Blo 814346 1226741 := bbase (se 5 (by rfl) ⟨57503, by rfl⟩ : syracuseStep 1226741 = 115007) (by norm_num)
theorem B1161229 : Blo 814346 1161229 := bbase (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) (by norm_num)
theorem B1226765 : Blo 814346 1226765 := bbase (se 3 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 1226765 = 460037) (by norm_num)
theorem B1226789 : Blo 814346 1226789 := bbase (se 4 (by rfl) ⟨115011, by rfl⟩ : syracuseStep 1226789 = 230023) (by norm_num)
theorem B1226813 : Blo 814346 1226813 := bbase (se 3 (by rfl) ⟨230027, by rfl⟩ : syracuseStep 1226813 = 460055) (by norm_num)
theorem B1226837 : Blo 814346 1226837 := bbase (se 8 (by rfl) ⟨7188, by rfl⟩ : syracuseStep 1226837 = 14377) (by norm_num)
theorem B1226861 : Blo 814346 1226861 := bbase (se 3 (by rfl) ⟨230036, by rfl⟩ : syracuseStep 1226861 = 460073) (by norm_num)
theorem B1226885 : Blo 814346 1226885 := bbase (se 4 (by rfl) ⟨115020, by rfl⟩ : syracuseStep 1226885 = 230041) (by norm_num)
theorem B1226909 : Blo 814346 1226909 := bbase (se 3 (by rfl) ⟨230045, by rfl⟩ : syracuseStep 1226909 = 460091) (by norm_num)
theorem B5879989 : Blo 814346 5879989 := bbase (se 5 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 5879989 = 551249) (by norm_num)
theorem B1226933 : Blo 814346 1226933 := bbase (se 5 (by rfl) ⟨57512, by rfl⟩ : syracuseStep 1226933 = 115025) (by norm_num)
theorem B1226957 : Blo 814346 1226957 := bbase (se 3 (by rfl) ⟨230054, by rfl⟩ : syracuseStep 1226957 = 460109) (by norm_num)
theorem B5224661 : Blo 814346 5224661 := bbase (se 7 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 5224661 = 122453) (by norm_num)
theorem B3094757 : Blo 814346 3094757 := bbase (se 4 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 3094757 = 580267) (by norm_num)
theorem B1226981 : Blo 814346 1226981 := bbase (se 4 (by rfl) ⟨115029, by rfl⟩ : syracuseStep 1226981 = 230059) (by norm_num)
theorem B932077 : Blo 814346 932077 := bbase (se 3 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 932077 = 349529) (by norm_num)
theorem B1227005 : Blo 814346 1227005 := bbase (se 3 (by rfl) ⟨230063, by rfl⟩ : syracuseStep 1227005 = 460127) (by norm_num)
theorem B1227029 : Blo 814346 1227029 := bbase (se 6 (by rfl) ⟨28758, by rfl⟩ : syracuseStep 1227029 = 57517) (by norm_num)
theorem B1554733 : Blo 814346 1554733 := bbase (se 3 (by rfl) ⟨291512, by rfl⟩ : syracuseStep 1554733 = 583025) (by norm_num)
theorem B1227053 : Blo 814346 1227053 := bbase (se 3 (by rfl) ⟨230072, by rfl⟩ : syracuseStep 1227053 = 460145) (by norm_num)
theorem B1227077 : Blo 814346 1227077 := bbase (se 4 (by rfl) ⟨115038, by rfl⟩ : syracuseStep 1227077 = 230077) (by norm_num)
theorem B1227101 : Blo 814346 1227101 := bbase (se 3 (by rfl) ⟨230081, by rfl⟩ : syracuseStep 1227101 = 460163) (by norm_num)
theorem B1227125 : Blo 814346 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1227149 : Blo 814346 1227149 := bbase (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) (by norm_num)
theorem B1227173 : Blo 814346 1227173 := bbase (se 4 (by rfl) ⟨115047, by rfl⟩ : syracuseStep 1227173 = 230095) (by norm_num)
theorem B1227197 : Blo 814346 1227197 := bbase (se 3 (by rfl) ⟨230099, by rfl⟩ : syracuseStep 1227197 = 460199) (by norm_num)
theorem B3488197 : Blo 814346 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B1227221 : Blo 814346 1227221 := bbase (se 7 (by rfl) ⟨14381, by rfl⟩ : syracuseStep 1227221 = 28763) (by norm_num)
theorem B1227245 : Blo 814346 1227245 := bbase (se 3 (by rfl) ⟨230108, by rfl⟩ : syracuseStep 1227245 = 460217) (by norm_num)
theorem B1227269 : Blo 814346 1227269 := bbase (se 4 (by rfl) ⟨115056, by rfl⟩ : syracuseStep 1227269 = 230113) (by norm_num)
theorem B1227293 : Blo 814346 1227293 := bbase (se 3 (by rfl) ⟨230117, by rfl⟩ : syracuseStep 1227293 = 460235) (by norm_num)
theorem B1227317 : Blo 814346 1227317 := bbase (se 5 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 1227317 = 115061) (by norm_num)
theorem B1227341 : Blo 814346 1227341 := bbase (se 3 (by rfl) ⟨230126, by rfl⟩ : syracuseStep 1227341 = 460253) (by norm_num)
theorem B1030745 : Blo 814346 1030745 := bbase (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) (by norm_num)
theorem B1161821 : Blo 814346 1161821 := bbase (se 3 (by rfl) ⟨217841, by rfl⟩ : syracuseStep 1161821 = 435683) (by norm_num)
theorem B1227365 : Blo 814346 1227365 := bbase (se 4 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 1227365 = 230131) (by norm_num)
theorem B1227389 : Blo 814346 1227389 := bbase (se 3 (by rfl) ⟨230135, by rfl⟩ : syracuseStep 1227389 = 460271) (by norm_num)
theorem B1030801 : Blo 814346 1030801 := bbase (se 2 (by rfl) ⟨386550, by rfl⟩ : syracuseStep 1030801 = 773101) (by norm_num)
theorem B1227413 : Blo 814346 1227413 := bbase (se 6 (by rfl) ⟨28767, by rfl⟩ : syracuseStep 1227413 = 57535) (by norm_num)
theorem B1161901 : Blo 814346 1161901 := bbase (se 3 (by rfl) ⟨217856, by rfl⟩ : syracuseStep 1161901 = 435713) (by norm_num)
theorem B1227437 : Blo 814346 1227437 := bbase (se 3 (by rfl) ⟨230144, by rfl⟩ : syracuseStep 1227437 = 460289) (by norm_num)
theorem B1227461 : Blo 814346 1227461 := bbase (se 4 (by rfl) ⟨115074, by rfl⟩ : syracuseStep 1227461 = 230149) (by norm_num)
theorem B1227485 : Blo 814346 1227485 := bbase (se 3 (by rfl) ⟨230153, by rfl⟩ : syracuseStep 1227485 = 460307) (by norm_num)
theorem B1030897 : Blo 814346 1030897 := bbase (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) (by norm_num)
theorem B1227509 : Blo 814346 1227509 := bbase (se 5 (by rfl) ⟨57539, by rfl⟩ : syracuseStep 1227509 = 115079) (by norm_num)
theorem B1162021 : Blo 814346 1162021 := bbase (se 4 (by rfl) ⟨108939, by rfl⟩ : syracuseStep 1162021 = 217879) (by norm_num)
theorem B1162117 : Blo 814346 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B1031069 : Blo 814346 1031069 := bbase (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) (by norm_num)
theorem B7650229 : Blo 814346 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1031125 : Blo 814346 1031125 := bbase (se 7 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 1031125 = 24167) (by norm_num)
theorem B1653805 : Blo 814346 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B1031221 : Blo 814346 1031221 := bbase (se 5 (by rfl) ⟨48338, by rfl⟩ : syracuseStep 1031221 = 96677) (by norm_num)
theorem B1653877 : Blo 814346 1653877 := bbase (se 5 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 1653877 = 155051) (by norm_num)
theorem B3488933 : Blo 814346 3488933 := bbase (se 4 (by rfl) ⟨327087, by rfl⟩ : syracuseStep 3488933 = 654175) (by norm_num)
theorem B9288917 : Blo 814346 9288917 := bbase (se 7 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 9288917 = 217709) (by norm_num)
theorem B1031393 : Blo 814346 1031393 := bbase (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) (by norm_num)
theorem B1031449 : Blo 814346 1031449 := bbase (se 2 (by rfl) ⟨386793, by rfl⟩ : syracuseStep 1031449 = 773587) (by norm_num)
theorem B1162613 : Blo 814346 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B1031545 : Blo 814346 1031545 := bbase (se 2 (by rfl) ⟨386829, by rfl⟩ : syracuseStep 1031545 = 773659) (by norm_num)
theorem B3095941 : Blo 814346 3095941 := bbase (se 4 (by rfl) ⟨290244, by rfl⟩ : syracuseStep 3095941 = 580489) (by norm_num)
theorem B1031717 : Blo 814346 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B1031773 : Blo 814346 1031773 := bbase (se 3 (by rfl) ⟨193457, by rfl⟩ : syracuseStep 1031773 = 386915) (by norm_num)
theorem B6274709 : Blo 814346 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B3096245 : Blo 814346 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B1031869 : Blo 814346 1031869 := bbase (se 3 (by rfl) ⟨193475, by rfl⟩ : syracuseStep 1031869 = 386951) (by norm_num)
theorem B1032041 : Blo 814346 1032041 := bbase (se 2 (by rfl) ⟨387015, by rfl⟩ : syracuseStep 1032041 = 774031) (by norm_num)
theorem B1163165 : Blo 814346 1163165 := bbase (se 3 (by rfl) ⟨218093, by rfl⟩ : syracuseStep 1163165 = 436187) (by norm_num)
theorem B1032097 : Blo 814346 1032097 := bbase (se 2 (by rfl) ⟨387036, by rfl⟩ : syracuseStep 1032097 = 774073) (by norm_num)
theorem B1032193 : Blo 814346 1032193 := bbase (se 2 (by rfl) ⟨387072, by rfl⟩ : syracuseStep 1032193 = 774145) (by norm_num)
theorem B6209621 : Blo 814346 6209621 := bbase (se 8 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 6209621 = 72769) (by norm_num)
theorem B1032365 : Blo 814346 1032365 := bbase (se 3 (by rfl) ⟨193568, by rfl⟩ : syracuseStep 1032365 = 387137) (by norm_num)
theorem B1654997 : Blo 814346 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B1032421 : Blo 814346 1032421 := bbase (se 4 (by rfl) ⟨96789, by rfl⟩ : syracuseStep 1032421 = 193579) (by norm_num)
theorem B1884437 : Blo 814346 1884437 := bbase (se 6 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 1884437 = 88333) (by norm_num)
theorem B1032517 : Blo 814346 1032517 := bbase (se 4 (by rfl) ⟨96798, by rfl⟩ : syracuseStep 1032517 = 193597) (by norm_num)
theorem B3916133 : Blo 814346 3916133 := bbase (se 4 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 3916133 = 734275) (by norm_num)
theorem B1032689 : Blo 814346 1032689 := bbase (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) (by norm_num)
theorem B1032745 : Blo 814346 1032745 := bbase (se 2 (by rfl) ⟨387279, by rfl⟩ : syracuseStep 1032745 = 774559) (by norm_num)
theorem B1032841 : Blo 814346 1032841 := bbase (se 2 (by rfl) ⟨387315, by rfl⟩ : syracuseStep 1032841 = 774631) (by norm_num)
theorem B1163917 : Blo 814346 1163917 := bbase (se 3 (by rfl) ⟨218234, by rfl⟩ : syracuseStep 1163917 = 436469) (by norm_num)
theorem B1491605 : Blo 814346 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1033013 : Blo 814346 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B1033069 : Blo 814346 1033069 := bbase (se 3 (by rfl) ⟨193700, by rfl⟩ : syracuseStep 1033069 = 387401) (by norm_num)
theorem B4408181 : Blo 814346 4408181 := bbase (se 5 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 4408181 = 413267) (by norm_num)
theorem B1033165 : Blo 814346 1033165 := bbase (se 3 (by rfl) ⟨193718, by rfl⟩ : syracuseStep 1033165 = 387437) (by norm_num)
theorem B1033337 : Blo 814346 1033337 := bbase (se 2 (by rfl) ⟨387501, by rfl⟩ : syracuseStep 1033337 = 775003) (by norm_num)
theorem B1033393 : Blo 814346 1033393 := bbase (se 2 (by rfl) ⟨387522, by rfl⟩ : syracuseStep 1033393 = 775045) (by norm_num)
theorem B1033489 : Blo 814346 1033489 := bbase (se 2 (by rfl) ⟨387558, by rfl⟩ : syracuseStep 1033489 = 775117) (by norm_num)
theorem B6964501 : Blo 814346 6964501 := bbase (se 6 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 6964501 = 326461) (by norm_num)
theorem B1885517 : Blo 814346 1885517 := bbase (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) (by norm_num)
theorem B869773 : Blo 814346 869773 := bbase (se 3 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 869773 = 326165) (by norm_num)
theorem B1164709 : Blo 814346 1164709 := bbase (se 4 (by rfl) ⟨109191, by rfl⟩ : syracuseStep 1164709 = 218383) (by norm_num)
theorem B1033661 : Blo 814346 1033661 := bbase (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) (by norm_num)
theorem B1033717 : Blo 814346 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B1033813 : Blo 814346 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B5883509 : Blo 814346 5883509 := bbase (se 5 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 5883509 = 551579) (by norm_num)
theorem B3098357 : Blo 814346 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B1165045 : Blo 814346 1165045 := bbase (se 5 (by rfl) ⟨54611, by rfl⟩ : syracuseStep 1165045 = 109223) (by norm_num)
theorem B1033985 : Blo 814346 1033985 := bbase (se 2 (by rfl) ⟨387744, by rfl⟩ : syracuseStep 1033985 = 775489) (by norm_num)
theorem B870149 : Blo 814346 870149 := bbase (se 4 (by rfl) ⟨81576, by rfl⟩ : syracuseStep 870149 = 163153) (by norm_num)
theorem B1034041 : Blo 814346 1034041 := bbase (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) (by norm_num)
theorem B870221 : Blo 814346 870221 := bbase (se 3 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 870221 = 326333) (by norm_num)
theorem B1034137 : Blo 814346 1034137 := bbase (se 2 (by rfl) ⟨387801, by rfl⟩ : syracuseStep 1034137 = 775603) (by norm_num)
theorem B1656733 : Blo 814346 1656733 := bbase (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) (by norm_num)
theorem B870409 : Blo 814346 870409 := bbase (se 2 (by rfl) ⟨326403, by rfl⟩ : syracuseStep 870409 = 652807) (by norm_num)
theorem B3098645 : Blo 814346 3098645 := bbase (se 6 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 3098645 = 145249) (by norm_num)
theorem B1034309 : Blo 814346 1034309 := bbase (se 4 (by rfl) ⟨96966, by rfl⟩ : syracuseStep 1034309 = 193933) (by norm_num)
theorem B1034365 : Blo 814346 1034365 := bbase (se 3 (by rfl) ⟨193943, by rfl⟩ : syracuseStep 1034365 = 387887) (by norm_num)
theorem B870593 : Blo 814346 870593 := bbase (se 2 (by rfl) ⟨326472, by rfl⟩ : syracuseStep 870593 = 652945) (by norm_num)
theorem B1034461 : Blo 814346 1034461 := bbase (se 3 (by rfl) ⟨193961, by rfl⟩ : syracuseStep 1034461 = 387923) (by norm_num)
theorem B3492229 : Blo 814346 3492229 := bbase (se 4 (by rfl) ⟨327396, by rfl⟩ : syracuseStep 3492229 = 654793) (by norm_num)
theorem B1034633 : Blo 814346 1034633 := bbase (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) (by norm_num)
theorem B1034689 : Blo 814346 1034689 := bbase (se 2 (by rfl) ⟨388008, by rfl⟩ : syracuseStep 1034689 = 776017) (by norm_num)
theorem B1395181 : Blo 814346 1395181 := bbase (se 3 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 1395181 = 523193) (by norm_num)
theorem B1034785 : Blo 814346 1034785 := bbase (se 2 (by rfl) ⟨388044, by rfl⟩ : syracuseStep 1034785 = 776089) (by norm_num)
theorem B4409909 : Blo 814346 4409909 := bbase (se 5 (by rfl) ⟨206714, by rfl⟩ : syracuseStep 4409909 = 413429) (by norm_num)
theorem B1034957 : Blo 814346 1034957 := bbase (se 3 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 1034957 = 388109) (by norm_num)
theorem B1035013 : Blo 814346 1035013 := bbase (se 4 (by rfl) ⟨97032, by rfl⟩ : syracuseStep 1035013 = 194065) (by norm_num)
theorem B1395541 : Blo 814346 1395541 := bbase (se 9 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 1395541 = 8177) (by norm_num)
theorem B1035109 : Blo 814346 1035109 := bbase (se 4 (by rfl) ⟨97041, by rfl⟩ : syracuseStep 1035109 = 194083) (by norm_num)
theorem B871345 : Blo 814346 871345 := bbase (se 2 (by rfl) ⟨326754, by rfl⟩ : syracuseStep 871345 = 653509) (by norm_num)
theorem B871417 : Blo 814346 871417 := bbase (se 2 (by rfl) ⟨326781, by rfl⟩ : syracuseStep 871417 = 653563) (by norm_num)
theorem B1035281 : Blo 814346 1035281 := bbase (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) (by norm_num)
theorem B3918917 : Blo 814346 3918917 := bbase (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) (by norm_num)
theorem B1035337 : Blo 814346 1035337 := bbase (se 2 (by rfl) ⟨388251, by rfl⟩ : syracuseStep 1035337 = 776503) (by norm_num)
theorem B1657957 : Blo 814346 1657957 := bbase (se 4 (by rfl) ⟨155433, by rfl⟩ : syracuseStep 1657957 = 310867) (by norm_num)
theorem B1100941 : Blo 814346 1100941 := bbase (se 3 (by rfl) ⟨206426, by rfl⟩ : syracuseStep 1100941 = 412853) (by norm_num)
theorem B1035433 : Blo 814346 1035433 := bbase (se 2 (by rfl) ⟨388287, by rfl⟩ : syracuseStep 1035433 = 776575) (by norm_num)
theorem B871597 : Blo 814346 871597 := bbase (se 3 (by rfl) ⟨163424, by rfl⟩ : syracuseStep 871597 = 326849) (by norm_num)
theorem B3099829 : Blo 814346 3099829 := bbase (se 5 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 3099829 = 290609) (by norm_num)
theorem B6966485 : Blo 814346 6966485 := bbase (se 7 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 6966485 = 163277) (by norm_num)
theorem B1035605 : Blo 814346 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B1035661 : Blo 814346 1035661 := bbase (se 3 (by rfl) ⟨194186, by rfl⟩ : syracuseStep 1035661 = 388373) (by norm_num)
theorem B2477461 : Blo 814346 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B1396165 : Blo 814346 1396165 := bbase (se 4 (by rfl) ⟨130890, by rfl⟩ : syracuseStep 1396165 = 261781) (by norm_num)
theorem B3100133 : Blo 814346 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B872041 : Blo 814346 872041 := bbase (se 2 (by rfl) ⟨327015, by rfl⟩ : syracuseStep 872041 = 654031) (by norm_num)
theorem B1658549 : Blo 814346 1658549 := bbase (se 5 (by rfl) ⟨77744, by rfl⟩ : syracuseStep 1658549 = 155489) (by norm_num)
theorem B1396445 : Blo 814346 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B872165 : Blo 814346 872165 := bbase (se 4 (by rfl) ⟨81765, by rfl⟩ : syracuseStep 872165 = 163531) (by norm_num)
theorem B1396493 : Blo 814346 1396493 := bbase (se 3 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 1396493 = 523685) (by norm_num)
theorem B872417 : Blo 814346 872417 := bbase (se 2 (by rfl) ⟨327156, by rfl⟩ : syracuseStep 872417 = 654313) (by norm_num)
theorem B3723413 : Blo 814346 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B872861 : Blo 814346 872861 := bbase (se 3 (by rfl) ⟨163661, by rfl⟩ : syracuseStep 872861 = 327323) (by norm_num)
theorem B1102325 : Blo 814346 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B873109 : Blo 814346 873109 := bbase (se 6 (by rfl) ⟨20463, by rfl⟩ : syracuseStep 873109 = 40927) (by norm_num)
theorem B840389 : Blo 814346 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B873553 : Blo 814346 873553 := bbase (se 2 (by rfl) ⟨327582, by rfl⟩ : syracuseStep 873553 = 655165) (by norm_num)
theorem B873613 : Blo 814346 873613 := bbase (se 3 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 873613 = 327605) (by norm_num)
theorem B3495221 : Blo 814346 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B3102245 : Blo 814346 3102245 := bbase (se 4 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 3102245 = 581671) (by norm_num)
theorem B1103429 : Blo 814346 1103429 := bbase (se 4 (by rfl) ⟨103446, by rfl⟩ : syracuseStep 1103429 = 206893) (by norm_num)
theorem B3102533 : Blo 814346 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B2611381 : Blo 814346 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B4413845 : Blo 814346 4413845 := bbase (se 6 (by rfl) ⟨103449, by rfl⟩ : syracuseStep 4413845 = 206899) (by norm_num)
theorem B3922453 : Blo 814346 3922453 := bbase (se 6 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 3922453 = 183865) (by norm_num)
theorem B1104445 : Blo 814346 1104445 := bbase (se 3 (by rfl) ⟨207083, by rfl⟩ : syracuseStep 1104445 = 414167) (by norm_num)
theorem B2120357 : Blo 814346 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B1399621 : Blo 814346 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B1104845 : Blo 814346 1104845 := bbase (se 3 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 1104845 = 414317) (by norm_num)
theorem B3103717 : Blo 814346 3103717 := bbase (se 4 (by rfl) ⟨290973, by rfl⟩ : syracuseStep 3103717 = 581947) (by norm_num)
theorem B3104021 : Blo 814346 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B1859117 : Blo 814346 1859117 := bbase (se 3 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 1859117 = 697169) (by norm_num)
theorem B1793669 : Blo 814346 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1957613 : Blo 814346 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B6610709 : Blo 814346 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B2383781 : Blo 814346 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B1433909 : Blo 814346 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B4251973 : Blo 814346 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B4416373 : Blo 814346 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B4645781 : Blo 814346 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B943193 : Blo 814346 943193 := bbase (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) (by norm_num)
theorem B1238213 : Blo 814346 1238213 := bbase (se 4 (by rfl) ⟨116082, by rfl⟩ : syracuseStep 1238213 = 232165) (by norm_num)
theorem B6186293 : Blo 814346 6186293 := bbase (se 5 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 6186293 = 579965) (by norm_num)
theorem B3106133 : Blo 814346 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B1795421 : Blo 814346 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B1467749 : Blo 814346 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B1467893 : Blo 814346 1467893 := bbase (se 5 (by rfl) ⟨68807, by rfl⟩ : syracuseStep 1467893 = 137615) (by norm_num)
theorem B1467973 : Blo 814346 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B2319941 : Blo 814346 2319941 := bbase (se 4 (by rfl) ⟨217494, by rfl⟩ : syracuseStep 2319941 = 434989) (by norm_num)
theorem B2090605 : Blo 814346 2090605 := bbase (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) (by norm_num)
theorem B3106421 : Blo 814346 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B15656597 : Blo 814346 15656597 := bbase (se 6 (by rfl) ⟨366951, by rfl⟩ : syracuseStep 15656597 = 733903) (by norm_num)
theorem B4187861 : Blo 814346 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B2942677 : Blo 814346 2942677 := bbase (se 7 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 2942677 = 68969) (by norm_num)
theorem B1238797 : Blo 814346 1238797 := bbase (se 3 (by rfl) ⟨232274, by rfl⟩ : syracuseStep 1238797 = 464549) (by norm_num)
theorem B1959805 : Blo 814346 1959805 := bbase (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) (by norm_num)
theorem B2516933 : Blo 814346 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B1304525 : Blo 814346 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B7858133 : Blo 814346 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B5236757 : Blo 814346 5236757 := bbase (se 6 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 5236757 = 245473) (by norm_num)
theorem B3926069 : Blo 814346 3926069 := bbase (se 5 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 3926069 = 368069) (by norm_num)
theorem B2091221 : Blo 814346 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B2320613 : Blo 814346 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B1010053 : Blo 814346 1010053 := bbase (se 4 (by rfl) ⟨94692, by rfl⟩ : syracuseStep 1010053 = 189385) (by norm_num)
theorem B4123061 : Blo 814346 4123061 := bbase (se 5 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 4123061 = 386537) (by norm_num)
theorem B1272349 : Blo 814346 1272349 := bbase (se 3 (by rfl) ⟨238565, by rfl⟩ : syracuseStep 1272349 = 477131) (by norm_num)
theorem B1239581 : Blo 814346 1239581 := bbase (se 3 (by rfl) ⟨232421, by rfl⟩ : syracuseStep 1239581 = 464843) (by norm_num)
theorem B2321045 : Blo 814346 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B2943685 : Blo 814346 2943685 := bbase (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) (by norm_num)
theorem B1469357 : Blo 814346 1469357 := bbase (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) (by norm_num)
theorem B3533765 : Blo 814346 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B1862621 : Blo 814346 1862621 := bbase (se 3 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 1862621 = 698483) (by norm_num)
theorem B2616533 : Blo 814346 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1961189 : Blo 814346 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B1240373 : Blo 814346 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B1305973 : Blo 814346 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B2321797 : Blo 814346 2321797 := bbase (se 4 (by rfl) ⟨217668, by rfl⟩ : syracuseStep 2321797 = 435337) (by norm_num)
theorem B1961381 : Blo 814346 1961381 := bbase (se 4 (by rfl) ⟨183879, by rfl⟩ : syracuseStep 1961381 = 367759) (by norm_num)
theorem B978365 : Blo 814346 978365 := bbase (se 3 (by rfl) ⟨183443, by rfl⟩ : syracuseStep 978365 = 366887) (by norm_num)
theorem B2092637 : Blo 814346 2092637 := bbase (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) (by norm_num)
theorem B4124357 : Blo 814346 4124357 := bbase (se 4 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 4124357 = 773317) (by norm_num)
theorem B978653 : Blo 814346 978653 := bbase (se 3 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 978653 = 366995) (by norm_num)
theorem B978817 : Blo 814346 978817 := bbase (se 2 (by rfl) ⟨367056, by rfl⟩ : syracuseStep 978817 = 734113) (by norm_num)
theorem B1699717 : Blo 814346 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B978845 : Blo 814346 978845 := bbase (se 3 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 978845 = 367067) (by norm_num)
theorem B3927973 : Blo 814346 3927973 := bbase (se 4 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 3927973 = 736495) (by norm_num)
theorem B3927989 : Blo 814346 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B1568717 : Blo 814346 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B1863677 : Blo 814346 1863677 := bbase (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) (by norm_num)
theorem B978961 : Blo 814346 978961 := bbase (se 2 (by rfl) ⟨367110, by rfl⟩ : syracuseStep 978961 = 734221) (by norm_num)
theorem B2748437 : Blo 814346 2748437 := bbase (se 6 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 2748437 = 128833) (by norm_num)
theorem B2617429 : Blo 814346 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B979057 : Blo 814346 979057 := bbase (se 2 (by rfl) ⟨367146, by rfl⟩ : syracuseStep 979057 = 734293) (by norm_num)
theorem B1568909 : Blo 814346 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1241237 : Blo 814346 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B1962149 : Blo 814346 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B2093293 : Blo 814346 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B1863917 : Blo 814346 1863917 := bbase (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) (by norm_num)
theorem B2748869 : Blo 814346 2748869 := bbase (se 4 (by rfl) ⟨257706, by rfl⟩ : syracuseStep 2748869 = 515413) (by norm_num)
theorem B2617829 : Blo 814346 2617829 := bbase (se 4 (by rfl) ⟨245421, by rfl⟩ : syracuseStep 2617829 = 490843) (by norm_num)
theorem B979537 : Blo 814346 979537 := bbase (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) (by norm_num)
theorem B1569461 : Blo 814346 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B1307357 : Blo 814346 1307357 := bbase (se 3 (by rfl) ⟨245129, by rfl⟩ : syracuseStep 1307357 = 490259) (by norm_num)
theorem B1766165 : Blo 814346 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1045333 : Blo 814346 1045333 := bbase (se 9 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 1045333 = 6125) (by norm_num)
theorem B2749301 : Blo 814346 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B1307549 : Blo 814346 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B1569701 : Blo 814346 1569701 := bbase (se 4 (by rfl) ⟨147159, by rfl⟩ : syracuseStep 1569701 = 294319) (by norm_num)
theorem B4125653 : Blo 814346 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B2061389 : Blo 814346 2061389 := bbase (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) (by norm_num)
theorem B1864957 : Blo 814346 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B2749733 : Blo 814346 2749733 := bbase (se 4 (by rfl) ⟨257787, by rfl⟩ : syracuseStep 2749733 = 515575) (by norm_num)
theorem B1832309 : Blo 814346 1832309 := bbase (se 5 (by rfl) ⟨85889, by rfl⟩ : syracuseStep 1832309 = 171779) (by norm_num)
theorem B2061733 : Blo 814346 2061733 := bbase (se 4 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 2061733 = 386575) (by norm_num)
theorem B1832381 : Blo 814346 1832381 := bbase (se 3 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 1832381 = 687143) (by norm_num)
theorem B1832453 : Blo 814346 1832453 := bbase (se 4 (by rfl) ⟨171792, by rfl⟩ : syracuseStep 1832453 = 343585) (by norm_num)
theorem B2061845 : Blo 814346 2061845 := bbase (se 6 (by rfl) ⟨48324, by rfl⟩ : syracuseStep 2061845 = 96649) (by norm_num)
theorem B1832525 : Blo 814346 1832525 := bbase (se 3 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 1832525 = 687197) (by norm_num)
theorem B1832597 : Blo 814346 1832597 := bbase (se 6 (by rfl) ⟨42951, by rfl⟩ : syracuseStep 1832597 = 85903) (by norm_num)
theorem B5732021 : Blo 814346 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B5961397 : Blo 814346 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B2062037 : Blo 814346 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B2750165 : Blo 814346 2750165 := bbase (se 7 (by rfl) ⟨32228, by rfl⟩ : syracuseStep 2750165 = 64457) (by norm_num)
theorem B1832669 : Blo 814346 1832669 := bbase (se 3 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 1832669 = 687251) (by norm_num)
theorem B1472261 : Blo 814346 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B1177373 : Blo 814346 1177373 := bbase (se 3 (by rfl) ⟨220757, by rfl⟩ : syracuseStep 1177373 = 441515) (by norm_num)
theorem B1832741 : Blo 814346 1832741 := bbase (se 4 (by rfl) ⟨171819, by rfl⟩ : syracuseStep 1832741 = 343639) (by norm_num)
theorem B1275685 : Blo 814346 1275685 := bbase (se 4 (by rfl) ⟨119595, by rfl⟩ : syracuseStep 1275685 = 239191) (by norm_num)
theorem B1832813 : Blo 814346 1832813 := bbase (se 3 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 1832813 = 687305) (by norm_num)
theorem B1832885 : Blo 814346 1832885 := bbase (se 5 (by rfl) ⟨85916, by rfl⟩ : syracuseStep 1832885 = 171833) (by norm_num)
theorem B980921 : Blo 814346 980921 := bbase (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) (by norm_num)
theorem B1832957 : Blo 814346 1832957 := bbase (se 3 (by rfl) ⟨343679, by rfl⟩ : syracuseStep 1832957 = 687359) (by norm_num)
theorem B2062381 : Blo 814346 2062381 := bbase (se 3 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 2062381 = 773393) (by norm_num)
theorem B1833029 : Blo 814346 1833029 := bbase (se 4 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 1833029 = 343693) (by norm_num)
theorem B1374293 : Blo 814346 1374293 := bbase (se 8 (by rfl) ⟨8052, by rfl⟩ : syracuseStep 1374293 = 16105) (by norm_num)
theorem B981109 : Blo 814346 981109 := bbase (se 5 (by rfl) ⟨45989, by rfl⟩ : syracuseStep 981109 = 91979) (by norm_num)
theorem B2750597 : Blo 814346 2750597 := bbase (se 4 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 2750597 = 515737) (by norm_num)
theorem B1833101 : Blo 814346 1833101 := bbase (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) (by norm_num)
theorem B2062493 : Blo 814346 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B2324645 : Blo 814346 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B1308869 : Blo 814346 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B1374421 : Blo 814346 1374421 := bbase (se 7 (by rfl) ⟨16106, by rfl⟩ : syracuseStep 1374421 = 32213) (by norm_num)
theorem B1833173 : Blo 814346 1833173 := bbase (se 7 (by rfl) ⟨21482, by rfl⟩ : syracuseStep 1833173 = 42965) (by norm_num)
theorem B1964245 : Blo 814346 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B4126949 : Blo 814346 4126949 := bbase (se 4 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 4126949 = 773803) (by norm_num)
theorem B3930373 : Blo 814346 3930373 := bbase (se 4 (by rfl) ⟨368472, by rfl⟩ : syracuseStep 3930373 = 736945) (by norm_num)
theorem B4421909 : Blo 814346 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B1833245 : Blo 814346 1833245 := bbase (se 3 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 1833245 = 687467) (by norm_num)
theorem B1308965 : Blo 814346 1308965 := bbase (se 4 (by rfl) ⟨122715, by rfl⟩ : syracuseStep 1308965 = 245431) (by norm_num)
theorem B1374509 : Blo 814346 1374509 := bbase (se 3 (by rfl) ⟨257720, by rfl⟩ : syracuseStep 1374509 = 515441) (by norm_num)
theorem B1308997 : Blo 814346 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B981325 : Blo 814346 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B2062685 : Blo 814346 2062685 := bbase (se 3 (by rfl) ⟨386753, by rfl⟩ : syracuseStep 2062685 = 773507) (by norm_num)
theorem B1833317 : Blo 814346 1833317 := bbase (se 4 (by rfl) ⟨171873, by rfl⟩ : syracuseStep 1833317 = 343747) (by norm_num)
theorem B5896597 : Blo 814346 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B1374637 : Blo 814346 1374637 := bbase (se 3 (by rfl) ⟨257744, by rfl⟩ : syracuseStep 1374637 = 515489) (by norm_num)
theorem B1833389 : Blo 814346 1833389 := bbase (se 3 (by rfl) ⟨343760, by rfl⟩ : syracuseStep 1833389 = 687521) (by norm_num)
theorem B1833461 : Blo 814346 1833461 := bbase (se 5 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 1833461 = 171887) (by norm_num)
theorem B1374725 : Blo 814346 1374725 := bbase (se 4 (by rfl) ⟨128880, by rfl⟩ : syracuseStep 1374725 = 257761) (by norm_num)
theorem B1243669 : Blo 814346 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1866269 : Blo 814346 1866269 := bbase (se 3 (by rfl) ⟨349925, by rfl⟩ : syracuseStep 1866269 = 699851) (by norm_num)
theorem B2751029 : Blo 814346 2751029 := bbase (se 5 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 2751029 = 257909) (by norm_num)
theorem B2652725 : Blo 814346 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B1833533 : Blo 814346 1833533 := bbase (se 3 (by rfl) ⟨343787, by rfl⟩ : syracuseStep 1833533 = 687575) (by norm_num)
theorem B1342037 : Blo 814346 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B981613 : Blo 814346 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B1374853 : Blo 814346 1374853 := bbase (se 4 (by rfl) ⟨128892, by rfl⟩ : syracuseStep 1374853 = 257785) (by norm_num)
theorem B1833605 : Blo 814346 1833605 := bbase (se 4 (by rfl) ⟨171900, by rfl⟩ : syracuseStep 1833605 = 343801) (by norm_num)
theorem B1866397 : Blo 814346 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B916141 : Blo 814346 916141 := bbase (se 3 (by rfl) ⟨171776, by rfl⟩ : syracuseStep 916141 = 343553) (by norm_num)
theorem B2063029 : Blo 814346 2063029 := bbase (se 5 (by rfl) ⟨96704, by rfl⟩ : syracuseStep 2063029 = 193409) (by norm_num)
theorem B1833677 : Blo 814346 1833677 := bbase (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) (by norm_num)
theorem B916177 : Blo 814346 916177 := bbase (se 2 (by rfl) ⟨343566, by rfl⟩ : syracuseStep 916177 = 687133) (by norm_num)
theorem B1374941 : Blo 814346 1374941 := bbase (se 3 (by rfl) ⟨257801, by rfl⟩ : syracuseStep 1374941 = 515603) (by norm_num)
theorem B1571557 : Blo 814346 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B916213 : Blo 814346 916213 := bbase (se 5 (by rfl) ⟨42947, by rfl⟩ : syracuseStep 916213 = 85895) (by norm_num)
theorem B1833749 : Blo 814346 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B3308309 : Blo 814346 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B916249 : Blo 814346 916249 := bbase (se 2 (by rfl) ⟨343593, by rfl⟩ : syracuseStep 916249 = 687187) (by norm_num)
theorem B2063141 : Blo 814346 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B3537701 : Blo 814346 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B916285 : Blo 814346 916285 := bbase (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) (by norm_num)
theorem B1964861 : Blo 814346 1964861 := bbase (se 3 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 1964861 = 736823) (by norm_num)
theorem B23886677 : Blo 814346 23886677 := bbase (se 9 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 23886677 = 139961) (by norm_num)
theorem B1375069 : Blo 814346 1375069 := bbase (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) (by norm_num)
theorem B1833821 : Blo 814346 1833821 := bbase (se 3 (by rfl) ⟨343841, by rfl⟩ : syracuseStep 1833821 = 687683) (by norm_num)
theorem B916321 : Blo 814346 916321 := bbase (se 2 (by rfl) ⟨343620, by rfl⟩ : syracuseStep 916321 = 687241) (by norm_num)
theorem B1964917 : Blo 814346 1964917 := bbase (se 5 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 1964917 = 184211) (by norm_num)
theorem B916357 : Blo 814346 916357 := bbase (se 4 (by rfl) ⟨85908, by rfl⟩ : syracuseStep 916357 = 171817) (by norm_num)
theorem B1833893 : Blo 814346 1833893 := bbase (se 4 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 1833893 = 343855) (by norm_num)
theorem B916393 : Blo 814346 916393 := bbase (se 2 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 916393 = 687295) (by norm_num)
theorem B1375157 : Blo 814346 1375157 := bbase (se 5 (by rfl) ⟨64460, by rfl⟩ : syracuseStep 1375157 = 128921) (by norm_num)
theorem B916429 : Blo 814346 916429 := bbase (se 3 (by rfl) ⟨171830, by rfl⟩ : syracuseStep 916429 = 343661) (by norm_num)
theorem B2063333 : Blo 814346 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B2751461 : Blo 814346 2751461 := bbase (se 4 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 2751461 = 515899) (by norm_num)
theorem B2948069 : Blo 814346 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B1833965 : Blo 814346 1833965 := bbase (se 3 (by rfl) ⟨343868, by rfl⟩ : syracuseStep 1833965 = 687737) (by norm_num)
theorem B916465 : Blo 814346 916465 := bbase (se 2 (by rfl) ⟨343674, by rfl⟩ : syracuseStep 916465 = 687349) (by norm_num)
theorem B916501 : Blo 814346 916501 := bbase (se 6 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 916501 = 42961) (by norm_num)
theorem B6978581 : Blo 814346 6978581 := bbase (se 6 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 6978581 = 327121) (by norm_num)
theorem B1375285 : Blo 814346 1375285 := bbase (se 5 (by rfl) ⟨64466, by rfl⟩ : syracuseStep 1375285 = 128933) (by norm_num)
theorem B1834037 : Blo 814346 1834037 := bbase (se 5 (by rfl) ⟨85970, by rfl⟩ : syracuseStep 1834037 = 171941) (by norm_num)
theorem B916537 : Blo 814346 916537 := bbase (se 2 (by rfl) ⟨343701, by rfl⟩ : syracuseStep 916537 = 687403) (by norm_num)
theorem B916573 : Blo 814346 916573 := bbase (se 3 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 916573 = 343715) (by norm_num)
theorem B2948213 : Blo 814346 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B1834109 : Blo 814346 1834109 := bbase (se 3 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 1834109 = 687791) (by norm_num)
theorem B916609 : Blo 814346 916609 := bbase (se 2 (by rfl) ⟨343728, by rfl⟩ : syracuseStep 916609 = 687457) (by norm_num)
theorem B1375373 : Blo 814346 1375373 := bbase (se 3 (by rfl) ⟨257882, by rfl⟩ : syracuseStep 1375373 = 515765) (by norm_num)
theorem B916645 : Blo 814346 916645 := bbase (se 4 (by rfl) ⟨85935, by rfl⟩ : syracuseStep 916645 = 171871) (by norm_num)
theorem B1834181 : Blo 814346 1834181 := bbase (se 4 (by rfl) ⟨171954, by rfl⟩ : syracuseStep 1834181 = 343909) (by norm_num)
theorem B916681 : Blo 814346 916681 := bbase (se 2 (by rfl) ⟨343755, by rfl⟩ : syracuseStep 916681 = 687511) (by norm_num)
theorem B916717 : Blo 814346 916717 := bbase (se 3 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 916717 = 343769) (by norm_num)
theorem B1375501 : Blo 814346 1375501 := bbase (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) (by norm_num)
theorem B1834253 : Blo 814346 1834253 := bbase (se 3 (by rfl) ⟨343922, by rfl⟩ : syracuseStep 1834253 = 687845) (by norm_num)
theorem B916753 : Blo 814346 916753 := bbase (se 2 (by rfl) ⟨343782, by rfl⟩ : syracuseStep 916753 = 687565) (by norm_num)
theorem B916789 : Blo 814346 916789 := bbase (se 5 (by rfl) ⟨42974, by rfl⟩ : syracuseStep 916789 = 85949) (by norm_num)
theorem B2063677 : Blo 814346 2063677 := bbase (se 3 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 2063677 = 773879) (by norm_num)
theorem B2325829 : Blo 814346 2325829 := bbase (se 4 (by rfl) ⟨218046, by rfl⟩ : syracuseStep 2325829 = 436093) (by norm_num)
theorem B1834325 : Blo 814346 1834325 := bbase (se 11 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1834325 = 2687) (by norm_num)
theorem B916825 : Blo 814346 916825 := bbase (se 2 (by rfl) ⟨343809, by rfl⟩ : syracuseStep 916825 = 687619) (by norm_num)
theorem B1375589 : Blo 814346 1375589 := bbase (se 4 (by rfl) ⟨128961, by rfl⟩ : syracuseStep 1375589 = 257923) (by norm_num)
theorem B916861 : Blo 814346 916861 := bbase (se 3 (by rfl) ⟨171911, by rfl⟩ : syracuseStep 916861 = 343823) (by norm_num)
theorem B2751893 : Blo 814346 2751893 := bbase (se 6 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 2751893 = 128995) (by norm_num)
theorem B1834397 : Blo 814346 1834397 := bbase (se 3 (by rfl) ⟨343949, by rfl⟩ : syracuseStep 1834397 = 687899) (by norm_num)
theorem B916897 : Blo 814346 916897 := bbase (se 2 (by rfl) ⟨343836, by rfl⟩ : syracuseStep 916897 = 687673) (by norm_num)
theorem B2063789 : Blo 814346 2063789 := bbase (se 3 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 2063789 = 773921) (by norm_num)
theorem B916933 : Blo 814346 916933 := bbase (se 4 (by rfl) ⟨85962, by rfl⟩ : syracuseStep 916933 = 171925) (by norm_num)
theorem B1375717 : Blo 814346 1375717 := bbase (se 4 (by rfl) ⟨128973, by rfl⟩ : syracuseStep 1375717 = 257947) (by norm_num)
theorem B1834469 : Blo 814346 1834469 := bbase (se 4 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 1834469 = 343963) (by norm_num)
theorem B2325989 : Blo 814346 2325989 := bbase (se 4 (by rfl) ⟨218061, by rfl⟩ : syracuseStep 2325989 = 436123) (by norm_num)
theorem B916969 : Blo 814346 916969 := bbase (se 2 (by rfl) ⟨343863, by rfl⟩ : syracuseStep 916969 = 687727) (by norm_num)
theorem B4128245 : Blo 814346 4128245 := bbase (se 5 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 4128245 = 387023) (by norm_num)
theorem B917005 : Blo 814346 917005 := bbase (se 3 (by rfl) ⟨171938, by rfl⟩ : syracuseStep 917005 = 343877) (by norm_num)
theorem B1834541 : Blo 814346 1834541 := bbase (se 3 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 1834541 = 687953) (by norm_num)
theorem B917041 : Blo 814346 917041 := bbase (se 2 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 917041 = 687781) (by norm_num)
theorem B5242421 : Blo 814346 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B1375805 : Blo 814346 1375805 := bbase (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) (by norm_num)
theorem B917077 : Blo 814346 917077 := bbase (se 8 (by rfl) ⟨5373, by rfl⟩ : syracuseStep 917077 = 10747) (by norm_num)
theorem B2063981 : Blo 814346 2063981 := bbase (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) (by norm_num)
theorem B1834613 : Blo 814346 1834613 := bbase (se 5 (by rfl) ⟨85997, by rfl⟩ : syracuseStep 1834613 = 171995) (by norm_num)
theorem B917113 : Blo 814346 917113 := bbase (se 2 (by rfl) ⟨343917, by rfl⟩ : syracuseStep 917113 = 687835) (by norm_num)
theorem B2981509 : Blo 814346 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B917149 : Blo 814346 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B1375933 : Blo 814346 1375933 := bbase (se 3 (by rfl) ⟨257987, by rfl⟩ : syracuseStep 1375933 = 515975) (by norm_num)
theorem B1834685 : Blo 814346 1834685 := bbase (se 3 (by rfl) ⟨344003, by rfl⟩ : syracuseStep 1834685 = 688007) (by norm_num)
theorem B917185 : Blo 814346 917185 := bbase (se 2 (by rfl) ⟨343944, by rfl⟩ : syracuseStep 917185 = 687889) (by norm_num)
theorem B2326229 : Blo 814346 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B917221 : Blo 814346 917221 := bbase (se 4 (by rfl) ⟨85989, by rfl⟩ : syracuseStep 917221 = 171979) (by norm_num)
theorem B1834757 : Blo 814346 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B917257 : Blo 814346 917257 := bbase (se 2 (by rfl) ⟨343971, by rfl⟩ : syracuseStep 917257 = 687943) (by norm_num)
theorem B1376021 : Blo 814346 1376021 := bbase (se 6 (by rfl) ⟨32250, by rfl⟩ : syracuseStep 1376021 = 64501) (by norm_num)
theorem B917293 : Blo 814346 917293 := bbase (se 3 (by rfl) ⟨171992, by rfl⟩ : syracuseStep 917293 = 343985) (by norm_num)
theorem B1310509 : Blo 814346 1310509 := bbase (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) (by norm_num)
theorem B2752325 : Blo 814346 2752325 := bbase (se 4 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 2752325 = 516061) (by norm_num)
theorem B1834829 : Blo 814346 1834829 := bbase (se 3 (by rfl) ⟨344030, by rfl⟩ : syracuseStep 1834829 = 688061) (by norm_num)
theorem B917329 : Blo 814346 917329 := bbase (se 2 (by rfl) ⟨343998, by rfl⟩ : syracuseStep 917329 = 687997) (by norm_num)
theorem B1965917 : Blo 814346 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B851809 : Blo 814346 851809 := bbase (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) (by norm_num)
theorem B917365 : Blo 814346 917365 := bbase (se 5 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 917365 = 86003) (by norm_num)
theorem B1572725 : Blo 814346 1572725 := bbase (se 5 (by rfl) ⟨73721, by rfl⟩ : syracuseStep 1572725 = 147443) (by norm_num)
theorem B982901 : Blo 814346 982901 := bbase (se 5 (by rfl) ⟨46073, by rfl⟩ : syracuseStep 982901 = 92147) (by norm_num)
theorem B1376149 : Blo 814346 1376149 := bbase (se 6 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 1376149 = 64507) (by norm_num)
theorem B1834901 : Blo 814346 1834901 := bbase (se 6 (by rfl) ⟨43005, by rfl⟩ : syracuseStep 1834901 = 86011) (by norm_num)
theorem B2326421 : Blo 814346 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B917401 : Blo 814346 917401 := bbase (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) (by norm_num)
theorem B917437 : Blo 814346 917437 := bbase (se 3 (by rfl) ⟨172019, by rfl⟩ : syracuseStep 917437 = 344039) (by norm_num)
theorem B2064325 : Blo 814346 2064325 := bbase (se 4 (by rfl) ⟨193530, by rfl⟩ : syracuseStep 2064325 = 387061) (by norm_num)
theorem B1834973 : Blo 814346 1834973 := bbase (se 3 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 1834973 = 688115) (by norm_num)
theorem B917473 : Blo 814346 917473 := bbase (se 2 (by rfl) ⟨344052, by rfl⟩ : syracuseStep 917473 = 688105) (by norm_num)
theorem B1376237 : Blo 814346 1376237 := bbase (se 3 (by rfl) ⟨258044, by rfl⟩ : syracuseStep 1376237 = 516089) (by norm_num)
theorem B1376257 : Blo 814346 1376257 := bstep (se 2 (by rfl) ⟨516096, by rfl⟩ : syracuseStep 1376257 = 1032193) B1032193
theorem B1376291 : Blo 814346 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B1048627 : Blo 814346 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B917635 : Blo 814346 917635 := bstep (se 1 (by rfl) ⟨688226, by rfl⟩ : syracuseStep 917635 = 1376453) B1376453
theorem B1835153 : Blo 814346 1835153 := bstep (se 2 (by rfl) ⟨688182, by rfl⟩ : syracuseStep 1835153 = 1376365) B1376365
theorem B1835171 : Blo 814346 1835171 := bstep (se 1 (by rfl) ⟨1376378, by rfl⟩ : syracuseStep 1835171 = 2752757) B2752757
theorem B1376419 : Blo 814346 1376419 := bstep (se 1 (by rfl) ⟨1032314, by rfl⟩ : syracuseStep 1376419 = 2064629) B2064629
theorem B7864589 : Blo 814346 7864589 := bstep (se 3 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 7864589 = 2949221) B2949221
theorem B917779 : Blo 814346 917779 := bstep (se 1 (by rfl) ⟨688334, by rfl⟩ : syracuseStep 917779 = 1376669) B1376669
theorem B1376561 : Blo 814346 1376561 := bstep (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) B1032421
theorem B1179955 : Blo 814346 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B4424005 : Blo 814346 4424005 := bstep (se 4 (by rfl) ⟨414750, by rfl⟩ : syracuseStep 4424005 = 829501) B829501
theorem B4653389 : Blo 814346 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B9929101 : Blo 814346 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B917923 : Blo 814346 917923 := bstep (se 1 (by rfl) ⟨688442, by rfl⟩ : syracuseStep 917923 = 1376885) B1376885
theorem B1835441 : Blo 814346 1835441 := bstep (se 2 (by rfl) ⟨688290, by rfl⟩ : syracuseStep 1835441 = 1376581) B1376581
theorem B1376689 : Blo 814346 1376689 := bstep (se 2 (by rfl) ⟨516258, by rfl⟩ : syracuseStep 1376689 = 1032517) B1032517
theorem B5669297 : Blo 814346 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B1835459 : Blo 814346 1835459 := bstep (se 1 (by rfl) ⟨1376594, by rfl⟩ : syracuseStep 1835459 = 2753189) B2753189
theorem B2752973 : Blo 814346 2752973 := bstep (se 3 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 2752973 = 1032365) B1032365
theorem B1376723 : Blo 814346 1376723 := bstep (se 1 (by rfl) ⟨1032542, by rfl⟩ : syracuseStep 1376723 = 2065085) B2065085
theorem B2753027 : Blo 814346 2753027 := bstep (se 1 (by rfl) ⟨2064770, by rfl⟩ : syracuseStep 2753027 = 4129541) B4129541
theorem B918067 : Blo 814346 918067 := bstep (se 1 (by rfl) ⟨688550, by rfl⟩ : syracuseStep 918067 = 1377101) B1377101
theorem B1376851 : Blo 814346 1376851 := bstep (se 1 (by rfl) ⟨1032638, by rfl⟩ : syracuseStep 1376851 = 2065277) B2065277
theorem B4129379 : Blo 814346 4129379 := bstep (se 1 (by rfl) ⟨3097034, by rfl⟩ : syracuseStep 4129379 = 6194069) B6194069
theorem B918211 : Blo 814346 918211 := bstep (se 1 (by rfl) ⟨688658, by rfl⟩ : syracuseStep 918211 = 1377317) B1377317
theorem B1835729 : Blo 814346 1835729 := bstep (se 2 (by rfl) ⟨688398, by rfl⟩ : syracuseStep 1835729 = 1376797) B1376797
theorem B1376993 : Blo 814346 1376993 := bstep (se 2 (by rfl) ⟨516372, by rfl⟩ : syracuseStep 1376993 = 1032745) B1032745
theorem B1835747 : Blo 814346 1835747 := bstep (se 1 (by rfl) ⟨1376810, by rfl⟩ : syracuseStep 1835747 = 2753621) B2753621
theorem B2753297 : Blo 814346 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B918355 : Blo 814346 918355 := bstep (se 1 (by rfl) ⟨688766, by rfl⟩ : syracuseStep 918355 = 1377533) B1377533
theorem B1377121 : Blo 814346 1377121 := bstep (se 2 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 1377121 = 1032841) B1032841
theorem B1377155 : Blo 814346 1377155 := bstep (se 1 (by rfl) ⟨1032866, by rfl⟩ : syracuseStep 1377155 = 2065733) B2065733
theorem B2360195 : Blo 814346 2360195 := bstep (se 1 (by rfl) ⟨1770146, by rfl⟩ : syracuseStep 2360195 = 3540293) B3540293
theorem B2065297 : Blo 814346 2065297 := bstep (se 2 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 2065297 = 1548973) B1548973
theorem B918499 : Blo 814346 918499 := bstep (se 1 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 918499 = 1377749) B1377749
theorem B1836017 : Blo 814346 1836017 := bstep (se 2 (by rfl) ⟨688506, by rfl⟩ : syracuseStep 1836017 = 1377013) B1377013
theorem B1836035 : Blo 814346 1836035 := bstep (se 1 (by rfl) ⟨1377026, by rfl⟩ : syracuseStep 1836035 = 2754053) B2754053
theorem B1377283 : Blo 814346 1377283 := bstep (se 1 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 1377283 = 2065925) B2065925
theorem B2327629 : Blo 814346 2327629 := bstep (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) B872861
theorem B918643 : Blo 814346 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B1377425 : Blo 814346 1377425 := bstep (se 2 (by rfl) ⟨516534, by rfl⟩ : syracuseStep 1377425 = 1033069) B1033069
theorem B2065571 : Blo 814346 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B918787 : Blo 814346 918787 := bstep (se 1 (by rfl) ⟨689090, by rfl⟩ : syracuseStep 918787 = 1378181) B1378181
theorem B1836305 : Blo 814346 1836305 := bstep (se 2 (by rfl) ⟨688614, by rfl⟩ : syracuseStep 1836305 = 1377229) B1377229
theorem B1377553 : Blo 814346 1377553 := bstep (se 2 (by rfl) ⟨516582, by rfl⟩ : syracuseStep 1377553 = 1033165) B1033165
theorem B1836323 : Blo 814346 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B2753837 : Blo 814346 2753837 := bstep (se 3 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 2753837 = 1032689) B1032689
theorem B1377587 : Blo 814346 1377587 := bstep (se 1 (by rfl) ⟨1033190, by rfl⟩ : syracuseStep 1377587 = 2066381) B2066381
theorem B2753891 : Blo 814346 2753891 := bstep (se 1 (by rfl) ⟨2065418, by rfl⟩ : syracuseStep 2753891 = 4130837) B4130837
theorem B2065763 : Blo 814346 2065763 := bstep (se 1 (by rfl) ⟨1549322, by rfl⟩ : syracuseStep 2065763 = 3098645) B3098645
theorem B4130189 : Blo 814346 4130189 := bstep (se 3 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 4130189 = 1548821) B1548821
theorem B918931 : Blo 814346 918931 := bstep (se 1 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 918931 = 1378397) B1378397
theorem B1377715 : Blo 814346 1377715 := bstep (se 1 (by rfl) ⟨1033286, by rfl⟩ : syracuseStep 1377715 = 2066573) B2066573
theorem B919075 : Blo 814346 919075 := bstep (se 1 (by rfl) ⟨689306, by rfl⟩ : syracuseStep 919075 = 1378613) B1378613
theorem B1836593 : Blo 814346 1836593 := bstep (se 2 (by rfl) ⟨688722, by rfl⟩ : syracuseStep 1836593 = 1377445) B1377445
theorem B1377857 : Blo 814346 1377857 := bstep (se 2 (by rfl) ⟨516696, by rfl⟩ : syracuseStep 1377857 = 1033393) B1033393
theorem B1836611 : Blo 814346 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B8291909 : Blo 814346 8291909 := bstep (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) B1554733
theorem B2754161 : Blo 814346 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B919219 : Blo 814346 919219 := bstep (se 1 (by rfl) ⟨689414, by rfl⟩ : syracuseStep 919219 = 1378829) B1378829
theorem B1377985 : Blo 814346 1377985 := bstep (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) B1033489
theorem B1378019 : Blo 814346 1378019 := bstep (se 1 (by rfl) ⟨1033514, by rfl⟩ : syracuseStep 1378019 = 2067029) B2067029
theorem B7440113 : Blo 814346 7440113 := bstep (se 2 (by rfl) ⟨2790042, by rfl⟩ : syracuseStep 7440113 = 5580085) B5580085
theorem B919363 : Blo 814346 919363 := bstep (se 1 (by rfl) ⟨689522, by rfl⟩ : syracuseStep 919363 = 1379045) B1379045
theorem B1836881 : Blo 814346 1836881 := bstep (se 2 (by rfl) ⟨688830, by rfl⟩ : syracuseStep 1836881 = 1377661) B1377661
theorem B1836899 : Blo 814346 1836899 := bstep (se 1 (by rfl) ⟨1377674, by rfl⟩ : syracuseStep 1836899 = 2755349) B2755349
theorem B1378147 : Blo 814346 1378147 := bstep (se 1 (by rfl) ⟨1033610, by rfl⟩ : syracuseStep 1378147 = 2067221) B2067221
theorem B919507 : Blo 814346 919507 := bstep (se 1 (by rfl) ⟨689630, by rfl⟩ : syracuseStep 919507 = 1379261) B1379261
theorem B1378289 : Blo 814346 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B17860661 : Blo 814346 17860661 := bstep (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) B1674437
theorem B919651 : Blo 814346 919651 := bstep (se 1 (by rfl) ⟨689738, by rfl⟩ : syracuseStep 919651 = 1379477) B1379477
theorem B1837169 : Blo 814346 1837169 := bstep (se 2 (by rfl) ⟨688938, by rfl⟩ : syracuseStep 1837169 = 1377877) B1377877
theorem B1378417 : Blo 814346 1378417 := bstep (se 2 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 1378417 = 1033813) B1033813
theorem B2328689 : Blo 814346 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B1837187 : Blo 814346 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B2754701 : Blo 814346 2754701 := bstep (se 3 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 2754701 = 1033013) B1033013
theorem B2787473 : Blo 814346 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B1378451 : Blo 814346 1378451 := bstep (se 1 (by rfl) ⟨1033838, by rfl⟩ : syracuseStep 1378451 = 2067677) B2067677
theorem B2754755 : Blo 814346 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B919795 : Blo 814346 919795 := bstep (se 1 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 919795 = 1379693) B1379693
theorem B2066705 : Blo 814346 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B1378579 : Blo 814346 1378579 := bstep (se 1 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 1378579 = 2067869) B2067869
theorem B2066755 : Blo 814346 2066755 := bstep (se 1 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 2066755 = 3100133) B3100133
theorem B919939 : Blo 814346 919939 := bstep (se 1 (by rfl) ⟨689954, by rfl⟩ : syracuseStep 919939 = 1379909) B1379909
theorem B1837457 : Blo 814346 1837457 := bstep (se 2 (by rfl) ⟨689046, by rfl⟩ : syracuseStep 1837457 = 1378093) B1378093
theorem B1378721 : Blo 814346 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B1837475 : Blo 814346 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B4196771 : Blo 814346 4196771 := bstep (se 1 (by rfl) ⟨3147578, by rfl⟩ : syracuseStep 4196771 = 6295157) B6295157
theorem B2755025 : Blo 814346 2755025 := bstep (se 2 (by rfl) ⟨1033134, by rfl⟩ : syracuseStep 2755025 = 2066269) B2066269
theorem B2066897 : Blo 814346 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B920083 : Blo 814346 920083 := bstep (se 1 (by rfl) ⟨690062, by rfl⟩ : syracuseStep 920083 = 1380125) B1380125
theorem B1378849 : Blo 814346 1378849 := bstep (se 2 (by rfl) ⟨517068, by rfl⟩ : syracuseStep 1378849 = 1034137) B1034137
theorem B1378883 : Blo 814346 1378883 := bstep (se 1 (by rfl) ⟨1034162, by rfl⟩ : syracuseStep 1378883 = 2068325) B2068325
theorem B920227 : Blo 814346 920227 := bstep (se 1 (by rfl) ⟨690170, by rfl⟩ : syracuseStep 920227 = 1380341) B1380341
theorem B1837745 : Blo 814346 1837745 := bstep (se 2 (by rfl) ⟨689154, by rfl⟩ : syracuseStep 1837745 = 1378309) B1378309
theorem B1837763 : Blo 814346 1837763 := bstep (se 1 (by rfl) ⟨1378322, by rfl⟩ : syracuseStep 1837763 = 2756645) B2756645
theorem B1379011 : Blo 814346 1379011 := bstep (se 1 (by rfl) ⟨1034258, by rfl⟩ : syracuseStep 1379011 = 2068517) B2068517
theorem B2329361 : Blo 814346 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B920371 : Blo 814346 920371 := bstep (se 1 (by rfl) ⟨690278, by rfl⟩ : syracuseStep 920371 = 1380557) B1380557
theorem B1379153 : Blo 814346 1379153 := bstep (se 2 (by rfl) ⟨517182, by rfl⟩ : syracuseStep 1379153 = 1034365) B1034365
theorem B920515 : Blo 814346 920515 := bstep (se 1 (by rfl) ⟨690386, by rfl⟩ : syracuseStep 920515 = 1380773) B1380773
theorem B1838033 : Blo 814346 1838033 := bstep (se 2 (by rfl) ⟨689262, by rfl⟩ : syracuseStep 1838033 = 1378525) B1378525
theorem B1379281 : Blo 814346 1379281 := bstep (se 2 (by rfl) ⟨517230, by rfl⟩ : syracuseStep 1379281 = 1034461) B1034461
theorem B1838051 : Blo 814346 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B2755565 : Blo 814346 2755565 := bstep (se 3 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 2755565 = 1033337) B1033337
theorem B1379315 : Blo 814346 1379315 := bstep (se 1 (by rfl) ⟨1034486, by rfl⟩ : syracuseStep 1379315 = 2068973) B2068973
theorem B2755619 : Blo 814346 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B59477105 : Blo 814346 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B1379443 : Blo 814346 1379443 := bstep (se 1 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 1379443 = 2069165) B2069165
theorem B4656305 : Blo 814346 4656305 := bstep (se 2 (by rfl) ⟨1746114, by rfl⟩ : syracuseStep 4656305 = 3492229) B3492229
theorem B1346737 : Blo 814346 1346737 := bstep (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) B1010053
theorem B1838321 : Blo 814346 1838321 := bstep (se 2 (by rfl) ⟨689370, by rfl⟩ : syracuseStep 1838321 = 1378741) B1378741
theorem B1379585 : Blo 814346 1379585 := bstep (se 2 (by rfl) ⟨517344, by rfl⟩ : syracuseStep 1379585 = 1034689) B1034689
theorem B1838339 : Blo 814346 1838339 := bstep (se 1 (by rfl) ⟨1378754, by rfl⟩ : syracuseStep 1838339 = 2757509) B2757509
theorem B2755889 : Blo 814346 2755889 := bstep (se 2 (by rfl) ⟨1033458, by rfl⟩ : syracuseStep 2755889 = 2066917) B2066917
theorem B1379713 : Blo 814346 1379713 := bstep (se 2 (by rfl) ⟨517392, by rfl⟩ : syracuseStep 1379713 = 1034785) B1034785
theorem B1379747 : Blo 814346 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B2067889 : Blo 814346 2067889 := bstep (se 2 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 2067889 = 1550917) B1550917
theorem B1838609 : Blo 814346 1838609 := bstep (se 2 (by rfl) ⟨689478, by rfl⟩ : syracuseStep 1838609 = 1378957) B1378957
theorem B1838627 : Blo 814346 1838627 := bstep (se 1 (by rfl) ⟨1378970, by rfl⟩ : syracuseStep 1838627 = 2757941) B2757941
theorem B1379875 : Blo 814346 1379875 := bstep (se 1 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 1379875 = 2069813) B2069813
theorem B2330147 : Blo 814346 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1380017 : Blo 814346 1380017 := bstep (se 2 (by rfl) ⟨517506, by rfl⟩ : syracuseStep 1380017 = 1035013) B1035013
theorem B2068163 : Blo 814346 2068163 := bstep (se 1 (by rfl) ⟨1551122, by rfl⟩ : syracuseStep 2068163 = 3102245) B3102245
theorem B15699653 : Blo 814346 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B1838897 : Blo 814346 1838897 := bstep (se 2 (by rfl) ⟨689586, by rfl⟩ : syracuseStep 1838897 = 1379173) B1379173
theorem B1380145 : Blo 814346 1380145 := bstep (se 2 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 1380145 = 1035109) B1035109
theorem B1838915 : Blo 814346 1838915 := bstep (se 1 (by rfl) ⟨1379186, by rfl⟩ : syracuseStep 1838915 = 2758373) B2758373
theorem B9277253 : Blo 814346 9277253 := bstep (se 4 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 9277253 = 1739485) B1739485
theorem B2756429 : Blo 814346 2756429 := bstep (se 3 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 2756429 = 1033661) B1033661
theorem B1380179 : Blo 814346 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B8359793 : Blo 814346 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B2068355 : Blo 814346 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B2756483 : Blo 814346 2756483 := bstep (se 1 (by rfl) ⟨2067362, by rfl⟩ : syracuseStep 2756483 = 4134725) B4134725
theorem B1380307 : Blo 814346 1380307 := bstep (se 1 (by rfl) ⟨1035230, by rfl⟩ : syracuseStep 1380307 = 2070461) B2070461
theorem B6033379 : Blo 814346 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B1839185 : Blo 814346 1839185 := bstep (se 2 (by rfl) ⟨689694, by rfl⟩ : syracuseStep 1839185 = 1379389) B1379389
theorem B1380449 : Blo 814346 1380449 := bstep (se 2 (by rfl) ⟨517668, by rfl⟩ : syracuseStep 1380449 = 1035337) B1035337
theorem B1839203 : Blo 814346 1839203 := bstep (se 1 (by rfl) ⟨1379402, by rfl⟩ : syracuseStep 1839203 = 2758805) B2758805
theorem B2756753 : Blo 814346 2756753 := bstep (se 2 (by rfl) ⟨1033782, by rfl⟩ : syracuseStep 2756753 = 2067565) B2067565
theorem B1380577 : Blo 814346 1380577 := bstep (se 2 (by rfl) ⟨517716, by rfl⟩ : syracuseStep 1380577 = 1035433) B1035433
theorem B4133105 : Blo 814346 4133105 := bstep (se 2 (by rfl) ⟨1549914, by rfl⟩ : syracuseStep 4133105 = 3099829) B3099829
theorem B1380611 : Blo 814346 1380611 := bstep (se 1 (by rfl) ⟨1035458, by rfl⟩ : syracuseStep 1380611 = 2070917) B2070917
theorem B1839473 : Blo 814346 1839473 := bstep (se 2 (by rfl) ⟨689802, by rfl⟩ : syracuseStep 1839473 = 1379605) B1379605
theorem B1839491 : Blo 814346 1839491 := bstep (se 1 (by rfl) ⟨1379618, by rfl⟩ : syracuseStep 1839491 = 2759237) B2759237
theorem B1380739 : Blo 814346 1380739 := bstep (se 1 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 1380739 = 2071109) B2071109
theorem B7442885 : Blo 814346 7442885 := bstep (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) B1395541
theorem B1741297 : Blo 814346 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B1380881 : Blo 814346 1380881 := bstep (se 2 (by rfl) ⟨517830, by rfl⟩ : syracuseStep 1380881 = 1035661) B1035661
theorem B21172757 : Blo 814346 21172757 := bstep (se 6 (by rfl) ⟨496236, by rfl⟩ : syracuseStep 21172757 = 992473) B992473
theorem B4657763 : Blo 814346 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B1839761 : Blo 814346 1839761 := bstep (se 2 (by rfl) ⟨689910, by rfl⟩ : syracuseStep 1839761 = 1379821) B1379821
theorem B1839779 : Blo 814346 1839779 := bstep (se 1 (by rfl) ⟨1379834, by rfl⟩ : syracuseStep 1839779 = 2759669) B2759669
theorem B2757293 : Blo 814346 2757293 := bstep (se 3 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 2757293 = 1033985) B1033985
theorem B6197957 : Blo 814346 6197957 := bstep (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) B1162117
theorem B2757347 : Blo 814346 2757347 := bstep (se 1 (by rfl) ⟨2068010, by rfl⟩ : syracuseStep 2757347 = 4136021) B4136021
theorem B2069297 : Blo 814346 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B2069347 : Blo 814346 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B1840049 : Blo 814346 1840049 := bstep (se 2 (by rfl) ⟨690018, by rfl⟩ : syracuseStep 1840049 = 1380037) B1380037
theorem B1840067 : Blo 814346 1840067 := bstep (se 1 (by rfl) ⟨1380050, by rfl⟩ : syracuseStep 1840067 = 2760101) B2760101
theorem B2757617 : Blo 814346 2757617 := bstep (se 2 (by rfl) ⟨1034106, by rfl⟩ : syracuseStep 2757617 = 2068213) B2068213
theorem B2069489 : Blo 814346 2069489 := bstep (se 2 (by rfl) ⟨776058, by rfl⟩ : syracuseStep 2069489 = 1552117) B1552117
theorem B2266289 : Blo 814346 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B3478733 : Blo 814346 3478733 := bstep (se 3 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 3478733 = 1304525) B1304525
theorem B1840337 : Blo 814346 1840337 := bstep (se 2 (by rfl) ⟨690126, by rfl⟩ : syracuseStep 1840337 = 1380253) B1380253
theorem B1840355 : Blo 814346 1840355 := bstep (se 1 (by rfl) ⟨1380266, by rfl⟩ : syracuseStep 1840355 = 2760533) B2760533
theorem B1840625 : Blo 814346 1840625 := bstep (se 2 (by rfl) ⟨690234, by rfl⟩ : syracuseStep 1840625 = 1380469) B1380469
theorem B1840643 : Blo 814346 1840643 := bstep (se 1 (by rfl) ⟨1380482, by rfl⟩ : syracuseStep 1840643 = 2760965) B2760965
theorem B2758157 : Blo 814346 2758157 := bstep (se 3 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 2758157 = 1034309) B1034309
theorem B955939 : Blo 814346 955939 := bstep (se 1 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 955939 = 1433909) B1433909
theorem B2758211 : Blo 814346 2758211 := bstep (se 1 (by rfl) ⟨2068658, by rfl⟩ : syracuseStep 2758211 = 4137317) B4137317
theorem B2791057 : Blo 814346 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B4134563 : Blo 814346 4134563 := bstep (se 1 (by rfl) ⟨3100922, by rfl⟩ : syracuseStep 4134563 = 6201845) B6201845
theorem B8492813 : Blo 814346 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B1840913 : Blo 814346 1840913 := bstep (se 2 (by rfl) ⟨690342, by rfl⟩ : syracuseStep 1840913 = 1380685) B1380685
theorem B1840931 : Blo 814346 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B2758481 : Blo 814346 2758481 := bstep (se 2 (by rfl) ⟨1034430, by rfl⟩ : syracuseStep 2758481 = 2068861) B2068861
theorem B8820677 : Blo 814346 8820677 := bstep (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) B1653877
theorem B2070481 : Blo 814346 2070481 := bstep (se 2 (by rfl) ⟨776430, by rfl⟩ : syracuseStep 2070481 = 1552861) B1552861
theorem B1841201 : Blo 814346 1841201 := bstep (se 2 (by rfl) ⟨690450, by rfl⟩ : syracuseStep 1841201 = 1380901) B1380901
theorem B1841219 : Blo 814346 1841219 := bstep (se 1 (by rfl) ⟨1380914, by rfl⟩ : syracuseStep 1841219 = 2761829) B2761829
theorem B5871685 : Blo 814346 5871685 := bstep (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) B1100941
theorem B2070755 : Blo 814346 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B2759021 : Blo 814346 2759021 := bstep (se 3 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 2759021 = 1034633) B1034633
theorem B1546627 : Blo 814346 1546627 := bstep (se 1 (by rfl) ⟨1159970, by rfl⟩ : syracuseStep 1546627 = 2319941) B2319941
theorem B2759075 : Blo 814346 2759075 := bstep (se 1 (by rfl) ⟨2069306, by rfl⟩ : syracuseStep 2759075 = 4138613) B4138613
theorem B2070947 : Blo 814346 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B4135373 : Blo 814346 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B2791907 : Blo 814346 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B2759345 : Blo 814346 2759345 := bstep (se 2 (by rfl) ⟨1034754, by rfl⟩ : syracuseStep 2759345 = 2069509) B2069509
theorem B1547075 : Blo 814346 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B826387 : Blo 814346 826387 := bstep (se 1 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 826387 = 1239581) B1239581
theorem B1547363 : Blo 814346 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B2759885 : Blo 814346 2759885 := bstep (se 3 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 2759885 = 1034957) B1034957
theorem B2759939 : Blo 814346 2759939 := bstep (se 1 (by rfl) ⟨2069954, by rfl⟩ : syracuseStep 2759939 = 4139909) B4139909
theorem B1744355 : Blo 814346 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B2760209 : Blo 814346 2760209 := bstep (se 2 (by rfl) ⟨1035078, by rfl⟩ : syracuseStep 2760209 = 2070157) B2070157
theorem B1548305 : Blo 814346 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B2760749 : Blo 814346 2760749 := bstep (se 3 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 2760749 = 1035281) B1035281
theorem B15704117 : Blo 814346 15704117 := bstep (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) B1472261
theorem B827491 : Blo 814346 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B2760803 : Blo 814346 2760803 := bstep (se 1 (by rfl) ⟨2070602, by rfl⟩ : syracuseStep 2760803 = 4141205) B4141205
theorem B3481841 : Blo 814346 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B7839985 : Blo 814346 7839985 := bstep (se 2 (by rfl) ⟨2939994, by rfl⟩ : syracuseStep 7839985 = 5879989) B5879989
theorem B1745219 : Blo 814346 1745219 := bstep (se 1 (by rfl) ⟨1308914, by rfl⟩ : syracuseStep 1745219 = 2617829) B2617829
theorem B2761073 : Blo 814346 2761073 := bstep (se 2 (by rfl) ⟨1035402, by rfl⟩ : syracuseStep 2761073 = 2070805) B2070805
theorem B1745329 : Blo 814346 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B15901381 : Blo 814346 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B2761613 : Blo 814346 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B1221521 : Blo 814346 1221521 := bstep (se 2 (by rfl) ⟨458070, by rfl⟩ : syracuseStep 1221521 = 916141) B916141
theorem B1549201 : Blo 814346 1549201 := bstep (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) B1161901
theorem B1221539 : Blo 814346 1221539 := bstep (se 1 (by rfl) ⟨916154, by rfl⟩ : syracuseStep 1221539 = 1832309) B1832309
theorem B1221569 : Blo 814346 1221569 := bstep (se 2 (by rfl) ⟨458088, by rfl⟩ : syracuseStep 1221569 = 916177) B916177
theorem B2761667 : Blo 814346 2761667 := bstep (se 1 (by rfl) ⟨2071250, by rfl⟩ : syracuseStep 2761667 = 4142501) B4142501
theorem B1221587 : Blo 814346 1221587 := bstep (se 1 (by rfl) ⟨916190, by rfl⟩ : syracuseStep 1221587 = 1832381) B1832381
theorem B1221617 : Blo 814346 1221617 := bstep (se 2 (by rfl) ⟨458106, by rfl⟩ : syracuseStep 1221617 = 916213) B916213
theorem B1221635 : Blo 814346 1221635 := bstep (se 1 (by rfl) ⟨916226, by rfl⟩ : syracuseStep 1221635 = 1832453) B1832453
theorem B1221665 : Blo 814346 1221665 := bstep (se 2 (by rfl) ⟨458124, by rfl⟩ : syracuseStep 1221665 = 916249) B916249
theorem B1549361 : Blo 814346 1549361 := bstep (se 2 (by rfl) ⟨581010, by rfl⟩ : syracuseStep 1549361 = 1162021) B1162021
theorem B1221683 : Blo 814346 1221683 := bstep (se 1 (by rfl) ⟨916262, by rfl⟩ : syracuseStep 1221683 = 1832525) B1832525
theorem B1221713 : Blo 814346 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B1221731 : Blo 814346 1221731 := bstep (se 1 (by rfl) ⟨916298, by rfl⟩ : syracuseStep 1221731 = 1832597) B1832597
theorem B1221761 : Blo 814346 1221761 := bstep (se 2 (by rfl) ⟨458160, by rfl⟩ : syracuseStep 1221761 = 916321) B916321
theorem B1221779 : Blo 814346 1221779 := bstep (se 1 (by rfl) ⟨916334, by rfl⟩ : syracuseStep 1221779 = 1832669) B1832669
theorem B1221809 : Blo 814346 1221809 := bstep (se 2 (by rfl) ⟨458178, by rfl⟩ : syracuseStep 1221809 = 916357) B916357
theorem B1221827 : Blo 814346 1221827 := bstep (se 1 (by rfl) ⟨916370, by rfl⟩ : syracuseStep 1221827 = 1832741) B1832741
theorem B1221857 : Blo 814346 1221857 := bstep (se 2 (by rfl) ⟨458196, by rfl⟩ : syracuseStep 1221857 = 916393) B916393
theorem B10200305 : Blo 814346 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1221875 : Blo 814346 1221875 := bstep (se 1 (by rfl) ⟨916406, by rfl⟩ : syracuseStep 1221875 = 1832813) B1832813
theorem B1221905 : Blo 814346 1221905 := bstep (se 2 (by rfl) ⟨458214, by rfl⟩ : syracuseStep 1221905 = 916429) B916429
theorem B1221923 : Blo 814346 1221923 := bstep (se 1 (by rfl) ⟨916442, by rfl⟩ : syracuseStep 1221923 = 1832885) B1832885
theorem B4138289 : Blo 814346 4138289 := bstep (se 2 (by rfl) ⟨1551858, by rfl⟩ : syracuseStep 4138289 = 3103717) B3103717
theorem B1221953 : Blo 814346 1221953 := bstep (se 2 (by rfl) ⟨458232, by rfl⟩ : syracuseStep 1221953 = 916465) B916465
theorem B1221971 : Blo 814346 1221971 := bstep (se 1 (by rfl) ⟨916478, by rfl⟩ : syracuseStep 1221971 = 1832957) B1832957
theorem B1222001 : Blo 814346 1222001 := bstep (se 2 (by rfl) ⟨458250, by rfl⟩ : syracuseStep 1222001 = 916501) B916501
theorem B1222019 : Blo 814346 1222019 := bstep (se 1 (by rfl) ⟨916514, by rfl⟩ : syracuseStep 1222019 = 1833029) B1833029
theorem B2205073 : Blo 814346 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B1222049 : Blo 814346 1222049 := bstep (se 2 (by rfl) ⟨458268, by rfl⟩ : syracuseStep 1222049 = 916537) B916537
theorem B1222067 : Blo 814346 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B1549763 : Blo 814346 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B4957645 : Blo 814346 4957645 := bstep (se 3 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 4957645 = 1859117) B1859117
theorem B1222097 : Blo 814346 1222097 := bstep (se 2 (by rfl) ⟨458286, by rfl⟩ : syracuseStep 1222097 = 916573) B916573
theorem B1222115 : Blo 814346 1222115 := bstep (se 1 (by rfl) ⟨916586, by rfl⟩ : syracuseStep 1222115 = 1833173) B1833173
theorem B3483107 : Blo 814346 3483107 := bstep (se 1 (by rfl) ⟨2612330, by rfl⟩ : syracuseStep 3483107 = 5224661) B5224661
theorem B1222145 : Blo 814346 1222145 := bstep (se 2 (by rfl) ⟨458304, by rfl⟩ : syracuseStep 1222145 = 916609) B916609
theorem B9283085 : Blo 814346 9283085 := bstep (se 3 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 9283085 = 3481157) B3481157
theorem B1222163 : Blo 814346 1222163 := bstep (se 1 (by rfl) ⟨916622, by rfl⟩ : syracuseStep 1222163 = 1833245) B1833245
theorem B1222193 : Blo 814346 1222193 := bstep (se 2 (by rfl) ⟨458322, by rfl⟩ : syracuseStep 1222193 = 916645) B916645
theorem B1222211 : Blo 814346 1222211 := bstep (se 1 (by rfl) ⟨916658, by rfl⟩ : syracuseStep 1222211 = 1833317) B1833317
theorem B1222241 : Blo 814346 1222241 := bstep (se 2 (by rfl) ⟨458340, by rfl⟩ : syracuseStep 1222241 = 916681) B916681
theorem B1222259 : Blo 814346 1222259 := bstep (se 1 (by rfl) ⟨916694, by rfl⟩ : syracuseStep 1222259 = 1833389) B1833389
theorem B1222289 : Blo 814346 1222289 := bstep (se 2 (by rfl) ⟨458358, by rfl⟩ : syracuseStep 1222289 = 916717) B916717
theorem B1222307 : Blo 814346 1222307 := bstep (se 1 (by rfl) ⟨916730, by rfl⟩ : syracuseStep 1222307 = 1833461) B1833461
theorem B1222337 : Blo 814346 1222337 := bstep (se 2 (by rfl) ⟨458376, by rfl⟩ : syracuseStep 1222337 = 916753) B916753
theorem B1222355 : Blo 814346 1222355 := bstep (se 1 (by rfl) ⟨916766, by rfl⟩ : syracuseStep 1222355 = 1833533) B1833533
theorem B894691 : Blo 814346 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B1222385 : Blo 814346 1222385 := bstep (se 2 (by rfl) ⟨458394, by rfl⟩ : syracuseStep 1222385 = 916789) B916789
theorem B1222403 : Blo 814346 1222403 := bstep (se 1 (by rfl) ⟨916802, by rfl⟩ : syracuseStep 1222403 = 1833605) B1833605
theorem B5973773 : Blo 814346 5973773 := bstep (se 3 (by rfl) ⟨1120082, by rfl⟩ : syracuseStep 5973773 = 2240165) B2240165
theorem B1222433 : Blo 814346 1222433 := bstep (se 2 (by rfl) ⟨458412, by rfl⟩ : syracuseStep 1222433 = 916825) B916825
theorem B1222451 : Blo 814346 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B1222481 : Blo 814346 1222481 := bstep (se 2 (by rfl) ⟨458430, by rfl⟩ : syracuseStep 1222481 = 916861) B916861
theorem B1222499 : Blo 814346 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B2205539 : Blo 814346 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B1222529 : Blo 814346 1222529 := bstep (se 2 (by rfl) ⟨458448, by rfl⟩ : syracuseStep 1222529 = 916897) B916897
theorem B1222547 : Blo 814346 1222547 := bstep (se 1 (by rfl) ⟨916910, by rfl⟩ : syracuseStep 1222547 = 1833821) B1833821
theorem B1222577 : Blo 814346 1222577 := bstep (se 2 (by rfl) ⟨458466, by rfl⟩ : syracuseStep 1222577 = 916933) B916933
theorem B1222595 : Blo 814346 1222595 := bstep (se 1 (by rfl) ⟨916946, by rfl⟩ : syracuseStep 1222595 = 1833893) B1833893
theorem B5220301 : Blo 814346 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B1222625 : Blo 814346 1222625 := bstep (se 2 (by rfl) ⟨458484, by rfl⟩ : syracuseStep 1222625 = 916969) B916969
theorem B1222643 : Blo 814346 1222643 := bstep (se 1 (by rfl) ⟨916982, by rfl⟩ : syracuseStep 1222643 = 1833965) B1833965
theorem B1222673 : Blo 814346 1222673 := bstep (se 2 (by rfl) ⟨458502, by rfl⟩ : syracuseStep 1222673 = 917005) B917005
theorem B1222691 : Blo 814346 1222691 := bstep (se 1 (by rfl) ⟨917018, by rfl⟩ : syracuseStep 1222691 = 1834037) B1834037
theorem B1222721 : Blo 814346 1222721 := bstep (se 2 (by rfl) ⟨458520, by rfl⟩ : syracuseStep 1222721 = 917041) B917041
theorem B1222739 : Blo 814346 1222739 := bstep (se 1 (by rfl) ⟨917054, by rfl⟩ : syracuseStep 1222739 = 1834109) B1834109
theorem B1222769 : Blo 814346 1222769 := bstep (se 2 (by rfl) ⟨458538, by rfl⟩ : syracuseStep 1222769 = 917077) B917077
theorem B1222787 : Blo 814346 1222787 := bstep (se 1 (by rfl) ⟨917090, by rfl⟩ : syracuseStep 1222787 = 1834181) B1834181
theorem B1222817 : Blo 814346 1222817 := bstep (se 2 (by rfl) ⟨458556, by rfl⟩ : syracuseStep 1222817 = 917113) B917113
theorem B1222835 : Blo 814346 1222835 := bstep (se 1 (by rfl) ⟨917126, by rfl⟩ : syracuseStep 1222835 = 1834253) B1834253
theorem B1222865 : Blo 814346 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B1222883 : Blo 814346 1222883 := bstep (se 1 (by rfl) ⟨917162, by rfl⟩ : syracuseStep 1222883 = 1834325) B1834325
theorem B1222913 : Blo 814346 1222913 := bstep (se 2 (by rfl) ⟨458592, by rfl⟩ : syracuseStep 1222913 = 917185) B917185
theorem B1222931 : Blo 814346 1222931 := bstep (se 1 (by rfl) ⟨917198, by rfl⟩ : syracuseStep 1222931 = 1834397) B1834397
theorem B1222961 : Blo 814346 1222961 := bstep (se 2 (by rfl) ⟨458610, by rfl⟩ : syracuseStep 1222961 = 917221) B917221
theorem B1222979 : Blo 814346 1222979 := bstep (se 1 (by rfl) ⟨917234, by rfl⟩ : syracuseStep 1222979 = 1834469) B1834469
theorem B1550659 : Blo 814346 1550659 := bstep (se 1 (by rfl) ⟨1162994, by rfl⟩ : syracuseStep 1550659 = 2325989) B2325989
theorem B1223009 : Blo 814346 1223009 := bstep (se 2 (by rfl) ⟨458628, by rfl⟩ : syracuseStep 1223009 = 917257) B917257
theorem B1223027 : Blo 814346 1223027 := bstep (se 1 (by rfl) ⟨917270, by rfl⟩ : syracuseStep 1223027 = 1834541) B1834541
theorem B6203789 : Blo 814346 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B1223057 : Blo 814346 1223057 := bstep (se 2 (by rfl) ⟨458646, by rfl⟩ : syracuseStep 1223057 = 917293) B917293
theorem B1747345 : Blo 814346 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1223075 : Blo 814346 1223075 := bstep (se 1 (by rfl) ⟨917306, by rfl⟩ : syracuseStep 1223075 = 1834613) B1834613
theorem B1223105 : Blo 814346 1223105 := bstep (se 2 (by rfl) ⟨458664, by rfl⟩ : syracuseStep 1223105 = 917329) B917329
theorem B1223123 : Blo 814346 1223123 := bstep (se 1 (by rfl) ⟨917342, by rfl⟩ : syracuseStep 1223123 = 1834685) B1834685
theorem B1550819 : Blo 814346 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1223153 : Blo 814346 1223153 := bstep (se 2 (by rfl) ⟨458682, by rfl⟩ : syracuseStep 1223153 = 917365) B917365
theorem B1223171 : Blo 814346 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B1223201 : Blo 814346 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B1223219 : Blo 814346 1223219 := bstep (se 1 (by rfl) ⟨917414, by rfl⟩ : syracuseStep 1223219 = 1834829) B1834829
theorem B1223249 : Blo 814346 1223249 := bstep (se 2 (by rfl) ⟨458718, by rfl⟩ : syracuseStep 1223249 = 917437) B917437
theorem B1223267 : Blo 814346 1223267 := bstep (se 1 (by rfl) ⟨917450, by rfl⟩ : syracuseStep 1223267 = 1834901) B1834901
theorem B1223297 : Blo 814346 1223297 := bstep (se 2 (by rfl) ⟨458736, by rfl⟩ : syracuseStep 1223297 = 917473) B917473
theorem B1223315 : Blo 814346 1223315 := bstep (se 1 (by rfl) ⟨917486, by rfl⟩ : syracuseStep 1223315 = 1834973) B1834973
theorem B1223345 : Blo 814346 1223345 := bstep (se 2 (by rfl) ⟨458754, by rfl⟩ : syracuseStep 1223345 = 917509) B917509
theorem B1223363 : Blo 814346 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B1223393 : Blo 814346 1223393 := bstep (se 2 (by rfl) ⟨458772, by rfl⟩ : syracuseStep 1223393 = 917545) B917545
theorem B4139747 : Blo 814346 4139747 := bstep (se 1 (by rfl) ⟨3104810, by rfl⟩ : syracuseStep 4139747 = 6209621) B6209621
theorem B1223411 : Blo 814346 1223411 := bstep (se 1 (by rfl) ⟨917558, by rfl⟩ : syracuseStep 1223411 = 1835117) B1835117
theorem B1223441 : Blo 814346 1223441 := bstep (se 2 (by rfl) ⟨458790, by rfl⟩ : syracuseStep 1223441 = 917581) B917581
theorem B2239249 : Blo 814346 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B1223459 : Blo 814346 1223459 := bstep (se 1 (by rfl) ⟨917594, by rfl⟩ : syracuseStep 1223459 = 1835189) B1835189
theorem B1747747 : Blo 814346 1747747 := bstep (se 1 (by rfl) ⟨1310810, by rfl⟩ : syracuseStep 1747747 = 2621621) B2621621
theorem B1223489 : Blo 814346 1223489 := bstep (se 2 (by rfl) ⟨458808, by rfl⟩ : syracuseStep 1223489 = 917617) B917617
theorem B1223507 : Blo 814346 1223507 := bstep (se 1 (by rfl) ⟨917630, by rfl⟩ : syracuseStep 1223507 = 1835261) B1835261
theorem B1256291 : Blo 814346 1256291 := bstep (se 1 (by rfl) ⟨942218, by rfl⟩ : syracuseStep 1256291 = 1884437) B1884437
theorem B1223537 : Blo 814346 1223537 := bstep (se 2 (by rfl) ⟨458826, by rfl⟩ : syracuseStep 1223537 = 917653) B917653
theorem B1223555 : Blo 814346 1223555 := bstep (se 1 (by rfl) ⟨917666, by rfl⟩ : syracuseStep 1223555 = 1835333) B1835333
theorem B1223585 : Blo 814346 1223585 := bstep (se 2 (by rfl) ⟨458844, by rfl⟩ : syracuseStep 1223585 = 917689) B917689
theorem B1223603 : Blo 814346 1223603 := bstep (se 1 (by rfl) ⟨917702, by rfl⟩ : syracuseStep 1223603 = 1835405) B1835405
theorem B1223633 : Blo 814346 1223633 := bstep (se 2 (by rfl) ⟨458862, by rfl⟩ : syracuseStep 1223633 = 917725) B917725
theorem B1223651 : Blo 814346 1223651 := bstep (se 1 (by rfl) ⟨917738, by rfl⟩ : syracuseStep 1223651 = 1835477) B1835477
theorem B1223681 : Blo 814346 1223681 := bstep (se 2 (by rfl) ⟨458880, by rfl⟩ : syracuseStep 1223681 = 917761) B917761
theorem B1223699 : Blo 814346 1223699 := bstep (se 1 (by rfl) ⟨917774, by rfl⟩ : syracuseStep 1223699 = 1835549) B1835549
theorem B1223729 : Blo 814346 1223729 := bstep (se 2 (by rfl) ⟨458898, by rfl⟩ : syracuseStep 1223729 = 917797) B917797
theorem B1223747 : Blo 814346 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B2796611 : Blo 814346 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1223777 : Blo 814346 1223777 := bstep (se 2 (by rfl) ⟨458916, by rfl⟩ : syracuseStep 1223777 = 917833) B917833
theorem B994403 : Blo 814346 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B1223795 : Blo 814346 1223795 := bstep (se 1 (by rfl) ⟨917846, by rfl⟩ : syracuseStep 1223795 = 1835693) B1835693
theorem B1223825 : Blo 814346 1223825 := bstep (se 2 (by rfl) ⟨458934, by rfl⟩ : syracuseStep 1223825 = 917869) B917869
theorem B1223843 : Blo 814346 1223843 := bstep (se 1 (by rfl) ⟨917882, by rfl⟩ : syracuseStep 1223843 = 1835765) B1835765
theorem B1223873 : Blo 814346 1223873 := bstep (se 2 (by rfl) ⟨458952, by rfl⟩ : syracuseStep 1223873 = 917905) B917905
theorem B1223891 : Blo 814346 1223891 := bstep (se 1 (by rfl) ⟨917918, by rfl⟩ : syracuseStep 1223891 = 1835837) B1835837
theorem B11775203 : Blo 814346 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B1223921 : Blo 814346 1223921 := bstep (se 2 (by rfl) ⟨458970, by rfl⟩ : syracuseStep 1223921 = 917941) B917941
theorem B1223939 : Blo 814346 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B1223969 : Blo 814346 1223969 := bstep (se 2 (by rfl) ⟨458988, by rfl⟩ : syracuseStep 1223969 = 917977) B917977
theorem B1223987 : Blo 814346 1223987 := bstep (se 1 (by rfl) ⟨917990, by rfl⟩ : syracuseStep 1223987 = 1835981) B1835981
theorem B1224017 : Blo 814346 1224017 := bstep (se 2 (by rfl) ⟨459006, by rfl⟩ : syracuseStep 1224017 = 918013) B918013
theorem B1224035 : Blo 814346 1224035 := bstep (se 1 (by rfl) ⟨918026, by rfl⟩ : syracuseStep 1224035 = 1836053) B1836053
theorem B1224065 : Blo 814346 1224065 := bstep (se 2 (by rfl) ⟨459024, by rfl⟩ : syracuseStep 1224065 = 918049) B918049
theorem B1224083 : Blo 814346 1224083 := bstep (se 1 (by rfl) ⟨918062, by rfl⟩ : syracuseStep 1224083 = 1836125) B1836125
theorem B1224113 : Blo 814346 1224113 := bstep (se 2 (by rfl) ⟨459042, by rfl⟩ : syracuseStep 1224113 = 918085) B918085
theorem B1224131 : Blo 814346 1224131 := bstep (se 1 (by rfl) ⟨918098, by rfl⟩ : syracuseStep 1224131 = 1836197) B1836197
theorem B1224161 : Blo 814346 1224161 := bstep (se 2 (by rfl) ⟨459060, by rfl⟩ : syracuseStep 1224161 = 918121) B918121
theorem B1224179 : Blo 814346 1224179 := bstep (se 1 (by rfl) ⟨918134, by rfl⟩ : syracuseStep 1224179 = 1836269) B1836269
theorem B4140557 : Blo 814346 4140557 := bstep (se 3 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 4140557 = 1552709) B1552709
theorem B1224209 : Blo 814346 1224209 := bstep (se 2 (by rfl) ⟨459078, by rfl⟩ : syracuseStep 1224209 = 918157) B918157
theorem B1551889 : Blo 814346 1551889 := bstep (se 2 (by rfl) ⟨581958, by rfl⟩ : syracuseStep 1551889 = 1163917) B1163917
theorem B1224227 : Blo 814346 1224227 := bstep (se 1 (by rfl) ⟨918170, by rfl⟩ : syracuseStep 1224227 = 1836341) B1836341
theorem B1257011 : Blo 814346 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B1224257 : Blo 814346 1224257 := bstep (se 2 (by rfl) ⟨459096, by rfl⟩ : syracuseStep 1224257 = 918193) B918193
theorem B1224275 : Blo 814346 1224275 := bstep (se 1 (by rfl) ⟨918206, by rfl⟩ : syracuseStep 1224275 = 1836413) B1836413
theorem B1224305 : Blo 814346 1224305 := bstep (se 2 (by rfl) ⟨459114, by rfl⟩ : syracuseStep 1224305 = 918229) B918229
theorem B1224323 : Blo 814346 1224323 := bstep (se 1 (by rfl) ⟨918242, by rfl⟩ : syracuseStep 1224323 = 1836485) B1836485
theorem B1224353 : Blo 814346 1224353 := bstep (se 2 (by rfl) ⟨459132, by rfl⟩ : syracuseStep 1224353 = 918265) B918265
theorem B1224371 : Blo 814346 1224371 := bstep (se 1 (by rfl) ⟨918278, by rfl⟩ : syracuseStep 1224371 = 1836557) B1836557
theorem B1224401 : Blo 814346 1224401 := bstep (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) B918301
theorem B1224419 : Blo 814346 1224419 := bstep (se 1 (by rfl) ⟨918314, by rfl⟩ : syracuseStep 1224419 = 1836629) B1836629
theorem B1224449 : Blo 814346 1224449 := bstep (se 2 (by rfl) ⟨459168, by rfl⟩ : syracuseStep 1224449 = 918337) B918337
theorem B1224467 : Blo 814346 1224467 := bstep (se 1 (by rfl) ⟨918350, by rfl⟩ : syracuseStep 1224467 = 1836701) B1836701
theorem B1224497 : Blo 814346 1224497 := bstep (se 2 (by rfl) ⟨459186, by rfl⟩ : syracuseStep 1224497 = 918373) B918373
theorem B1224515 : Blo 814346 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B1224545 : Blo 814346 1224545 := bstep (se 2 (by rfl) ⟨459204, by rfl⟩ : syracuseStep 1224545 = 918409) B918409
theorem B1224563 : Blo 814346 1224563 := bstep (se 1 (by rfl) ⟨918422, by rfl⟩ : syracuseStep 1224563 = 1836845) B1836845
theorem B1224593 : Blo 814346 1224593 := bstep (se 2 (by rfl) ⟨459222, by rfl⟩ : syracuseStep 1224593 = 918445) B918445
theorem B1224611 : Blo 814346 1224611 := bstep (se 1 (by rfl) ⟨918458, by rfl⟩ : syracuseStep 1224611 = 1836917) B1836917
theorem B1224641 : Blo 814346 1224641 := bstep (se 2 (by rfl) ⟨459240, by rfl⟩ : syracuseStep 1224641 = 918481) B918481
theorem B1224659 : Blo 814346 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B1224689 : Blo 814346 1224689 := bstep (se 2 (by rfl) ⟨459258, by rfl⟩ : syracuseStep 1224689 = 918517) B918517
theorem B1224707 : Blo 814346 1224707 := bstep (se 1 (by rfl) ⟨918530, by rfl⟩ : syracuseStep 1224707 = 1837061) B1837061
theorem B1224737 : Blo 814346 1224737 := bstep (se 2 (by rfl) ⟨459276, by rfl⟩ : syracuseStep 1224737 = 918553) B918553
theorem B1224755 : Blo 814346 1224755 := bstep (se 1 (by rfl) ⟨918566, by rfl⟩ : syracuseStep 1224755 = 1837133) B1837133
theorem B1224785 : Blo 814346 1224785 := bstep (se 2 (by rfl) ⟨459294, by rfl⟩ : syracuseStep 1224785 = 918589) B918589
theorem B1224803 : Blo 814346 1224803 := bstep (se 1 (by rfl) ⟨918602, by rfl⟩ : syracuseStep 1224803 = 1837205) B1837205
theorem B1224833 : Blo 814346 1224833 := bstep (se 2 (by rfl) ⟨459312, by rfl⟩ : syracuseStep 1224833 = 918625) B918625
theorem B1224851 : Blo 814346 1224851 := bstep (se 1 (by rfl) ⟨918638, by rfl⟩ : syracuseStep 1224851 = 1837277) B1837277
theorem B1224881 : Blo 814346 1224881 := bstep (se 2 (by rfl) ⟨459330, by rfl⟩ : syracuseStep 1224881 = 918661) B918661
theorem B1224899 : Blo 814346 1224899 := bstep (se 1 (by rfl) ⟨918674, by rfl⟩ : syracuseStep 1224899 = 1837349) B1837349
theorem B1224929 : Blo 814346 1224929 := bstep (se 2 (by rfl) ⟨459348, by rfl⟩ : syracuseStep 1224929 = 918697) B918697
theorem B1224947 : Blo 814346 1224947 := bstep (se 1 (by rfl) ⟨918710, by rfl⟩ : syracuseStep 1224947 = 1837421) B1837421
theorem B1224977 : Blo 814346 1224977 := bstep (se 2 (by rfl) ⟨459366, by rfl⟩ : syracuseStep 1224977 = 918733) B918733
theorem B1224995 : Blo 814346 1224995 := bstep (se 1 (by rfl) ⟨918746, by rfl⟩ : syracuseStep 1224995 = 1837493) B1837493
theorem B1225025 : Blo 814346 1225025 := bstep (se 2 (by rfl) ⟨459384, by rfl⟩ : syracuseStep 1225025 = 918769) B918769
theorem B3092813 : Blo 814346 3092813 := bstep (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) B1159805
theorem B1225043 : Blo 814346 1225043 := bstep (se 1 (by rfl) ⟨918782, by rfl⟩ : syracuseStep 1225043 = 1837565) B1837565
theorem B9286001 : Blo 814346 9286001 := bstep (se 2 (by rfl) ⟨3482250, by rfl⟩ : syracuseStep 9286001 = 6964501) B6964501
theorem B1225073 : Blo 814346 1225073 := bstep (se 2 (by rfl) ⟨459402, by rfl⟩ : syracuseStep 1225073 = 918805) B918805
theorem B1225091 : Blo 814346 1225091 := bstep (se 1 (by rfl) ⟨918818, by rfl⟩ : syracuseStep 1225091 = 1837637) B1837637
theorem B1225121 : Blo 814346 1225121 := bstep (se 2 (by rfl) ⟨459420, by rfl⟩ : syracuseStep 1225121 = 918841) B918841
theorem B1225139 : Blo 814346 1225139 := bstep (se 1 (by rfl) ⟨918854, by rfl⟩ : syracuseStep 1225139 = 1837709) B1837709
theorem B1225169 : Blo 814346 1225169 := bstep (se 2 (by rfl) ⟨459438, by rfl⟩ : syracuseStep 1225169 = 918877) B918877
theorem B1225187 : Blo 814346 1225187 := bstep (se 1 (by rfl) ⟨918890, by rfl⟩ : syracuseStep 1225187 = 1837781) B1837781
theorem B1225217 : Blo 814346 1225217 := bstep (se 2 (by rfl) ⟨459456, by rfl⟩ : syracuseStep 1225217 = 918913) B918913
theorem B2241037 : Blo 814346 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B1159697 : Blo 814346 1159697 := bstep (se 2 (by rfl) ⟨434886, by rfl⟩ : syracuseStep 1159697 = 869773) B869773
theorem B1225235 : Blo 814346 1225235 := bstep (se 1 (by rfl) ⟨918926, by rfl⟩ : syracuseStep 1225235 = 1837853) B1837853
theorem B1225265 : Blo 814346 1225265 := bstep (se 2 (by rfl) ⟨459474, by rfl⟩ : syracuseStep 1225265 = 918949) B918949
theorem B1552945 : Blo 814346 1552945 := bstep (se 2 (by rfl) ⟨582354, by rfl⟩ : syracuseStep 1552945 = 1164709) B1164709
theorem B1225283 : Blo 814346 1225283 := bstep (se 1 (by rfl) ⟨918962, by rfl⟩ : syracuseStep 1225283 = 1837925) B1837925
theorem B1225313 : Blo 814346 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B1225331 : Blo 814346 1225331 := bstep (se 1 (by rfl) ⟨918998, by rfl⟩ : syracuseStep 1225331 = 1837997) B1837997
theorem B1225361 : Blo 814346 1225361 := bstep (se 2 (by rfl) ⟨459510, by rfl⟩ : syracuseStep 1225361 = 919021) B919021
theorem B1225379 : Blo 814346 1225379 := bstep (se 1 (by rfl) ⟨919034, by rfl⟩ : syracuseStep 1225379 = 1838069) B1838069
theorem B1225409 : Blo 814346 1225409 := bstep (se 2 (by rfl) ⟨459528, by rfl⟩ : syracuseStep 1225409 = 919057) B919057
theorem B1225427 : Blo 814346 1225427 := bstep (se 1 (by rfl) ⟨919070, by rfl⟩ : syracuseStep 1225427 = 1838141) B1838141
theorem B1225457 : Blo 814346 1225457 := bstep (se 2 (by rfl) ⟨459546, by rfl⟩ : syracuseStep 1225457 = 919093) B919093
theorem B1225475 : Blo 814346 1225475 := bstep (se 1 (by rfl) ⟨919106, by rfl⟩ : syracuseStep 1225475 = 1838213) B1838213
theorem B1225505 : Blo 814346 1225505 := bstep (se 2 (by rfl) ⟨459564, by rfl⟩ : syracuseStep 1225505 = 919129) B919129
theorem B1225523 : Blo 814346 1225523 := bstep (se 1 (by rfl) ⟨919142, by rfl⟩ : syracuseStep 1225523 = 1838285) B1838285
theorem B1225553 : Blo 814346 1225553 := bstep (se 2 (by rfl) ⟨459582, by rfl⟩ : syracuseStep 1225553 = 919165) B919165
theorem B1225571 : Blo 814346 1225571 := bstep (se 1 (by rfl) ⟨919178, by rfl⟩ : syracuseStep 1225571 = 1838357) B1838357
theorem B1225601 : Blo 814346 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B1225619 : Blo 814346 1225619 := bstep (se 1 (by rfl) ⟨919214, by rfl⟩ : syracuseStep 1225619 = 1838429) B1838429
theorem B1225649 : Blo 814346 1225649 := bstep (se 2 (by rfl) ⟨459618, by rfl⟩ : syracuseStep 1225649 = 919237) B919237
theorem B1225667 : Blo 814346 1225667 := bstep (se 1 (by rfl) ⟨919250, by rfl⟩ : syracuseStep 1225667 = 1838501) B1838501
theorem B1553347 : Blo 814346 1553347 := bstep (se 1 (by rfl) ⟨1165010, by rfl⟩ : syracuseStep 1553347 = 2330021) B2330021
theorem B1225697 : Blo 814346 1225697 := bstep (se 2 (by rfl) ⟨459636, by rfl⟩ : syracuseStep 1225697 = 919273) B919273
theorem B1553393 : Blo 814346 1553393 := bstep (se 2 (by rfl) ⟨582522, by rfl⟩ : syracuseStep 1553393 = 1165045) B1165045
theorem B1225715 : Blo 814346 1225715 := bstep (se 1 (by rfl) ⟨919286, by rfl⟩ : syracuseStep 1225715 = 1838573) B1838573
theorem B1225745 : Blo 814346 1225745 := bstep (se 2 (by rfl) ⟨459654, by rfl⟩ : syracuseStep 1225745 = 919309) B919309
theorem B1225763 : Blo 814346 1225763 := bstep (se 1 (by rfl) ⟨919322, by rfl⟩ : syracuseStep 1225763 = 1838645) B1838645
theorem B1225793 : Blo 814346 1225793 := bstep (se 2 (by rfl) ⟨459672, by rfl⟩ : syracuseStep 1225793 = 919345) B919345
theorem B3486797 : Blo 814346 3486797 := bstep (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) B1307549
theorem B1225811 : Blo 814346 1225811 := bstep (se 1 (by rfl) ⟨919358, by rfl⟩ : syracuseStep 1225811 = 1838717) B1838717
theorem B1225841 : Blo 814346 1225841 := bstep (se 2 (by rfl) ⟨459690, by rfl⟩ : syracuseStep 1225841 = 919381) B919381
theorem B1225859 : Blo 814346 1225859 := bstep (se 1 (by rfl) ⟨919394, by rfl⟩ : syracuseStep 1225859 = 1838789) B1838789
theorem B1225889 : Blo 814346 1225889 := bstep (se 2 (by rfl) ⟨459708, by rfl⟩ : syracuseStep 1225889 = 919417) B919417
theorem B930995 : Blo 814346 930995 := bstep (se 1 (by rfl) ⟨698246, by rfl⟩ : syracuseStep 930995 = 1396493) B1396493
theorem B1225907 : Blo 814346 1225907 := bstep (se 1 (by rfl) ⟨919430, by rfl⟩ : syracuseStep 1225907 = 1838861) B1838861
theorem B2208977 : Blo 814346 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B1225937 : Blo 814346 1225937 := bstep (se 2 (by rfl) ⟨459726, by rfl⟩ : syracuseStep 1225937 = 919453) B919453
theorem B16954595 : Blo 814346 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B1225955 : Blo 814346 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B6206705 : Blo 814346 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B1225985 : Blo 814346 1225985 := bstep (se 2 (by rfl) ⟨459744, by rfl⟩ : syracuseStep 1225985 = 919489) B919489
theorem B1226003 : Blo 814346 1226003 := bstep (se 1 (by rfl) ⟨919502, by rfl⟩ : syracuseStep 1226003 = 1839005) B1839005
theorem B1226033 : Blo 814346 1226033 := bstep (se 2 (by rfl) ⟨459762, by rfl⟩ : syracuseStep 1226033 = 919525) B919525
theorem B1226051 : Blo 814346 1226051 := bstep (se 1 (by rfl) ⟨919538, by rfl⟩ : syracuseStep 1226051 = 1839077) B1839077
theorem B1226081 : Blo 814346 1226081 := bstep (se 2 (by rfl) ⟨459780, by rfl⟩ : syracuseStep 1226081 = 919561) B919561
theorem B1160563 : Blo 814346 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B1226099 : Blo 814346 1226099 := bstep (se 1 (by rfl) ⟨919574, by rfl⟩ : syracuseStep 1226099 = 1839149) B1839149
theorem B1226129 : Blo 814346 1226129 := bstep (se 2 (by rfl) ⟨459798, by rfl⟩ : syracuseStep 1226129 = 919597) B919597
theorem B1226147 : Blo 814346 1226147 := bstep (se 1 (by rfl) ⟨919610, by rfl⟩ : syracuseStep 1226147 = 1839221) B1839221
theorem B2799011 : Blo 814346 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B1226177 : Blo 814346 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B1160659 : Blo 814346 1160659 := bstep (se 1 (by rfl) ⟨870494, by rfl⟩ : syracuseStep 1160659 = 1740989) B1740989
theorem B1226195 : Blo 814346 1226195 := bstep (se 1 (by rfl) ⟨919646, by rfl⟩ : syracuseStep 1226195 = 1839293) B1839293
theorem B1226225 : Blo 814346 1226225 := bstep (se 2 (by rfl) ⟨459834, by rfl⟩ : syracuseStep 1226225 = 919669) B919669
theorem B1226243 : Blo 814346 1226243 := bstep (se 1 (by rfl) ⟨919682, by rfl⟩ : syracuseStep 1226243 = 1839365) B1839365
theorem B1226273 : Blo 814346 1226273 := bstep (se 2 (by rfl) ⟨459852, by rfl⟩ : syracuseStep 1226273 = 919705) B919705
theorem B1226291 : Blo 814346 1226291 := bstep (se 1 (by rfl) ⟨919718, by rfl⟩ : syracuseStep 1226291 = 1839437) B1839437
theorem B1226321 : Blo 814346 1226321 := bstep (se 2 (by rfl) ⟨459870, by rfl⟩ : syracuseStep 1226321 = 919741) B919741
theorem B1226339 : Blo 814346 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B1226369 : Blo 814346 1226369 := bstep (se 2 (by rfl) ⟨459888, by rfl⟩ : syracuseStep 1226369 = 919777) B919777
theorem B1226387 : Blo 814346 1226387 := bstep (se 1 (by rfl) ⟨919790, by rfl⟩ : syracuseStep 1226387 = 1839581) B1839581
theorem B1226417 : Blo 814346 1226417 := bstep (se 2 (by rfl) ⟨459906, by rfl⟩ : syracuseStep 1226417 = 919813) B919813
theorem B1226435 : Blo 814346 1226435 := bstep (se 1 (by rfl) ⟨919826, by rfl⟩ : syracuseStep 1226435 = 1839653) B1839653
theorem B1226465 : Blo 814346 1226465 := bstep (se 2 (by rfl) ⟨459924, by rfl⟩ : syracuseStep 1226465 = 919849) B919849
theorem B1226483 : Blo 814346 1226483 := bstep (se 1 (by rfl) ⟨919862, by rfl⟩ : syracuseStep 1226483 = 1839725) B1839725
theorem B1226513 : Blo 814346 1226513 := bstep (se 2 (by rfl) ⟨459942, by rfl⟩ : syracuseStep 1226513 = 919885) B919885
theorem B1226531 : Blo 814346 1226531 := bstep (se 1 (by rfl) ⟨919898, by rfl⟩ : syracuseStep 1226531 = 1839797) B1839797
theorem B1226561 : Blo 814346 1226561 := bstep (se 2 (by rfl) ⟨459960, by rfl⟩ : syracuseStep 1226561 = 919921) B919921
theorem B1226579 : Blo 814346 1226579 := bstep (se 1 (by rfl) ⟨919934, by rfl⟩ : syracuseStep 1226579 = 1839869) B1839869
theorem B1226609 : Blo 814346 1226609 := bstep (se 2 (by rfl) ⟨459978, by rfl⟩ : syracuseStep 1226609 = 919957) B919957
theorem B1226627 : Blo 814346 1226627 := bstep (se 1 (by rfl) ⟨919970, by rfl⟩ : syracuseStep 1226627 = 1839941) B1839941
theorem B1226657 : Blo 814346 1226657 := bstep (se 2 (by rfl) ⟨459996, by rfl⟩ : syracuseStep 1226657 = 919993) B919993
theorem B1226675 : Blo 814346 1226675 := bstep (se 1 (by rfl) ⟨920006, by rfl⟩ : syracuseStep 1226675 = 1840013) B1840013
theorem B1161155 : Blo 814346 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B1226705 : Blo 814346 1226705 := bstep (se 2 (by rfl) ⟨460014, by rfl⟩ : syracuseStep 1226705 = 920029) B920029
theorem B1226723 : Blo 814346 1226723 := bstep (se 1 (by rfl) ⟨920042, by rfl⟩ : syracuseStep 1226723 = 1840085) B1840085
theorem B1226753 : Blo 814346 1226753 := bstep (se 2 (by rfl) ⟨460032, by rfl⟩ : syracuseStep 1226753 = 920065) B920065
theorem B1226771 : Blo 814346 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1226801 : Blo 814346 1226801 := bstep (se 2 (by rfl) ⟨460050, by rfl⟩ : syracuseStep 1226801 = 920101) B920101
theorem B1226819 : Blo 814346 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B1226849 : Blo 814346 1226849 := bstep (se 2 (by rfl) ⟨460068, by rfl⟩ : syracuseStep 1226849 = 920137) B920137
theorem B1226867 : Blo 814346 1226867 := bstep (se 1 (by rfl) ⟨920150, by rfl⟩ : syracuseStep 1226867 = 1840301) B1840301
theorem B1226897 : Blo 814346 1226897 := bstep (se 2 (by rfl) ⟨460086, by rfl⟩ : syracuseStep 1226897 = 920173) B920173
theorem B1226915 : Blo 814346 1226915 := bstep (se 1 (by rfl) ⟨920186, by rfl⟩ : syracuseStep 1226915 = 1840373) B1840373
theorem B1226945 : Blo 814346 1226945 := bstep (se 2 (by rfl) ⟨460104, by rfl⟩ : syracuseStep 1226945 = 920209) B920209
theorem B1226963 : Blo 814346 1226963 := bstep (se 1 (by rfl) ⟨920222, by rfl⟩ : syracuseStep 1226963 = 1840445) B1840445
theorem B1226993 : Blo 814346 1226993 := bstep (se 2 (by rfl) ⟨460122, by rfl⟩ : syracuseStep 1226993 = 920245) B920245
theorem B1227011 : Blo 814346 1227011 := bstep (se 1 (by rfl) ⟨920258, by rfl⟩ : syracuseStep 1227011 = 1840517) B1840517
theorem B1227041 : Blo 814346 1227041 := bstep (se 2 (by rfl) ⟨460140, by rfl⟩ : syracuseStep 1227041 = 920281) B920281
theorem B1227059 : Blo 814346 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B1227089 : Blo 814346 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B1227107 : Blo 814346 1227107 := bstep (se 1 (by rfl) ⟨920330, by rfl⟩ : syracuseStep 1227107 = 1840661) B1840661
theorem B1227137 : Blo 814346 1227137 := bstep (se 2 (by rfl) ⟨460176, by rfl⟩ : syracuseStep 1227137 = 920353) B920353
theorem B1227155 : Blo 814346 1227155 := bstep (se 1 (by rfl) ⟨920366, by rfl⟩ : syracuseStep 1227155 = 1840733) B1840733
theorem B1227185 : Blo 814346 1227185 := bstep (se 2 (by rfl) ⟨460194, by rfl⟩ : syracuseStep 1227185 = 920389) B920389
theorem B1227203 : Blo 814346 1227203 := bstep (se 1 (by rfl) ⟨920402, by rfl⟩ : syracuseStep 1227203 = 1840805) B1840805
theorem B1227233 : Blo 814346 1227233 := bstep (se 2 (by rfl) ⟨460212, by rfl⟩ : syracuseStep 1227233 = 920425) B920425
theorem B1227251 : Blo 814346 1227251 := bstep (se 1 (by rfl) ⟨920438, by rfl⟩ : syracuseStep 1227251 = 1840877) B1840877
theorem B1227281 : Blo 814346 1227281 := bstep (se 2 (by rfl) ⟨460230, by rfl⟩ : syracuseStep 1227281 = 920461) B920461
theorem B1227299 : Blo 814346 1227299 := bstep (se 1 (by rfl) ⟨920474, by rfl⟩ : syracuseStep 1227299 = 1840949) B1840949
theorem B1161793 : Blo 814346 1161793 := bstep (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) B871345
theorem B1227329 : Blo 814346 1227329 := bstep (se 2 (by rfl) ⟨460248, by rfl⟩ : syracuseStep 1227329 = 920497) B920497
theorem B1227347 : Blo 814346 1227347 := bstep (se 1 (by rfl) ⟨920510, by rfl⟩ : syracuseStep 1227347 = 1841021) B1841021
theorem B1227377 : Blo 814346 1227377 := bstep (se 2 (by rfl) ⟨460266, by rfl⟩ : syracuseStep 1227377 = 920533) B920533
theorem B1227395 : Blo 814346 1227395 := bstep (se 1 (by rfl) ⟨920546, by rfl⟩ : syracuseStep 1227395 = 1841093) B1841093
theorem B3914381 : Blo 814346 3914381 := bstep (se 3 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 3914381 = 1467893) B1467893
theorem B1227425 : Blo 814346 1227425 := bstep (se 2 (by rfl) ⟨460284, by rfl⟩ : syracuseStep 1227425 = 920569) B920569
theorem B1227443 : Blo 814346 1227443 := bstep (se 1 (by rfl) ⟨920582, by rfl⟩ : syracuseStep 1227443 = 1841165) B1841165
theorem B1227473 : Blo 814346 1227473 := bstep (se 2 (by rfl) ⟨460302, by rfl⟩ : syracuseStep 1227473 = 920605) B920605
theorem B1227491 : Blo 814346 1227491 := bstep (se 1 (by rfl) ⟨920618, by rfl⟩ : syracuseStep 1227491 = 1841237) B1841237
theorem B2210609 : Blo 814346 2210609 := bstep (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) B1657957
theorem B1030963 : Blo 814346 1030963 := bstep (se 1 (by rfl) ⟨773222, by rfl⟩ : syracuseStep 1030963 = 1546445) B1546445
theorem B5651333 : Blo 814346 5651333 := bstep (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) B1059625
theorem B1162129 : Blo 814346 1162129 := bstep (se 2 (by rfl) ⟨435798, by rfl⟩ : syracuseStep 1162129 = 871597) B871597
theorem B1031059 : Blo 814346 1031059 := bstep (se 1 (by rfl) ⟨773294, by rfl⟩ : syracuseStep 1031059 = 1546589) B1546589
theorem B3095729 : Blo 814346 3095729 := bstep (se 2 (by rfl) ⟨1160898, by rfl⟩ : syracuseStep 3095729 = 2321797) B2321797
theorem B1031555 : Blo 814346 1031555 := bstep (se 1 (by rfl) ⟨773666, by rfl⟩ : syracuseStep 1031555 = 1547333) B1547333
theorem B1162721 : Blo 814346 1162721 := bstep (se 2 (by rfl) ⟨436020, by rfl⟩ : syracuseStep 1162721 = 872041) B872041
theorem B4407139 : Blo 814346 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B1163251 : Blo 814346 1163251 := bstep (se 1 (by rfl) ⟨872438, by rfl⟩ : syracuseStep 1163251 = 1744877) B1744877
theorem B1032259 : Blo 814346 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B3489905 : Blo 814346 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B1032355 : Blo 814346 1032355 := bstep (se 1 (by rfl) ⟨774266, by rfl⟩ : syracuseStep 1032355 = 1548533) B1548533
theorem B1163587 : Blo 814346 1163587 := bstep (se 1 (by rfl) ⟨872690, by rfl⟩ : syracuseStep 1163587 = 1745381) B1745381
theorem B1327585 : Blo 814346 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B3097187 : Blo 814346 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B1032851 : Blo 814346 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B3490573 : Blo 814346 3490573 := bstep (se 3 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 3490573 = 1308965) B1308965
theorem B27214613 : Blo 814346 27214613 := bstep (se 6 (by rfl) ⟨637842, by rfl⟩ : syracuseStep 27214613 = 1275685) B1275685
theorem B1164145 : Blo 814346 1164145 := bstep (se 2 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 1164145 = 873109) B873109
theorem B1164179 : Blo 814346 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B1196947 : Blo 814346 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B10437731 : Blo 814346 10437731 := bstep (se 1 (by rfl) ⟨7828298, by rfl⟩ : syracuseStep 10437731 = 15656597) B15656597
theorem B1393777 : Blo 814346 1393777 := bstep (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) B1045333
theorem B1033555 : Blo 814346 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B3491171 : Blo 814346 3491171 := bstep (se 1 (by rfl) ⟨2618378, by rfl⟩ : syracuseStep 3491171 = 5236757) B5236757
theorem B1033651 : Blo 814346 1033651 := bstep (se 1 (by rfl) ⟨775238, by rfl⟩ : syracuseStep 1033651 = 1550477) B1550477
theorem B1164737 : Blo 814346 1164737 := bstep (se 2 (by rfl) ⟨436776, by rfl⟩ : syracuseStep 1164737 = 873553) B873553
theorem B1394147 : Blo 814346 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B1164817 : Blo 814346 1164817 := bstep (se 2 (by rfl) ⟨436806, by rfl⟩ : syracuseStep 1164817 = 873613) B873613
theorem B3098189 : Blo 814346 3098189 := bstep (se 3 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 3098189 = 1161821) B1161821
theorem B5654285 : Blo 814346 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B8963909 : Blo 814346 8963909 := bstep (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) B1680733
theorem B1034147 : Blo 814346 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B4409477 : Blo 814346 4409477 := bstep (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) B826777
theorem B5228707 : Blo 814346 5228707 := bstep (se 1 (by rfl) ⟨3921530, by rfl⟩ : syracuseStep 5228707 = 7843061) B7843061
theorem B7948529 : Blo 814346 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B1395091 : Blo 814346 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B44616133 : Blo 814346 44616133 := bstep (se 4 (by rfl) ⟨4182762, by rfl⟩ : syracuseStep 44616133 = 8365525) B8365525
theorem B9423373 : Blo 814346 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B1034851 : Blo 814346 1034851 := bstep (se 1 (by rfl) ⟨776138, by rfl⟩ : syracuseStep 1034851 = 1552277) B1552277
theorem B1034947 : Blo 814346 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B871571 : Blo 814346 871571 := bstep (se 1 (by rfl) ⟨653678, by rfl⟩ : syracuseStep 871571 = 1307357) B1307357
theorem B1035443 : Blo 814346 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B4639949 : Blo 814346 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B5229937 : Blo 814346 5229937 := bstep (se 2 (by rfl) ⟨1961226, by rfl⟩ : syracuseStep 5229937 = 3922453) B3922453
theorem B1658225 : Blo 814346 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B3100301 : Blo 814346 3100301 := bstep (se 3 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 3100301 = 1162613) B1162613
theorem B839315 : Blo 814346 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B3821347 : Blo 814346 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2608973 : Blo 814346 2608973 := bstep (se 3 (by rfl) ⟨489182, by rfl⟩ : syracuseStep 2608973 = 978365) B978365
theorem B6606917 : Blo 814346 6606917 := bstep (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) B1238797
theorem B1101937 : Blo 814346 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B872579 : Blo 814346 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B1364273 : Blo 814346 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B3101105 : Blo 814346 3101105 := bstep (se 2 (by rfl) ⟨1162914, by rfl⟩ : syracuseStep 3101105 = 2325829) B2325829
theorem B2609741 : Blo 814346 2609741 := bstep (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) B978653
theorem B3723853 : Blo 814346 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B10769165 : Blo 814346 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B11785013 : Blo 814346 11785013 := bstep (se 5 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 11785013 = 1104845) B1104845
theorem B3494947 : Blo 814346 3494947 := bstep (se 1 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 3494947 = 5242421) B5242421
theorem B2610253 : Blo 814346 2610253 := bstep (se 3 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 2610253 = 978845) B978845
theorem B3101773 : Blo 814346 3101773 := bstep (se 3 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 3101773 = 1163165) B1163165
theorem B4183139 : Blo 814346 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1135745 : Blo 814346 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B2479405 : Blo 814346 2479405 := bstep (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) B929777
theorem B4642181 : Blo 814346 4642181 := bstep (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) B870409
theorem B2610755 : Blo 814346 2610755 := bstep (se 1 (by rfl) ⟨1958066, by rfl⟩ : syracuseStep 2610755 = 3916133) B3916133
theorem B3102563 : Blo 814346 3102563 := bstep (se 1 (by rfl) ⟨2326922, by rfl⟩ : syracuseStep 3102563 = 4653845) B4653845
theorem B4413325 : Blo 814346 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B2938787 : Blo 814346 2938787 := bstep (se 1 (by rfl) ⟨2204090, by rfl⟩ : syracuseStep 2938787 = 4408181) B4408181
theorem B4642865 : Blo 814346 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B1103969 : Blo 814346 1103969 := bstep (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) B827977
theorem B3922339 : Blo 814346 3922339 := bstep (se 1 (by rfl) ⟨2941754, by rfl⟩ : syracuseStep 3922339 = 5883509) B5883509
theorem B3103217 : Blo 814346 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B2939533 : Blo 814346 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B6970211 : Blo 814346 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B2939939 : Blo 814346 2939939 := bstep (se 1 (by rfl) ⟨2204954, by rfl⟩ : syracuseStep 2939939 = 4409909) B4409909
theorem B20929589 : Blo 814346 20929589 := bstep (se 5 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 20929589 = 1962149) B1962149
theorem B5233733 : Blo 814346 5233733 := bstep (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) B981325
theorem B2612611 : Blo 814346 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B4709773 : Blo 814346 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B1957297 : Blo 814346 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B4644323 : Blo 814346 4644323 := bstep (se 1 (by rfl) ⟨3483242, by rfl⟩ : syracuseStep 4644323 = 6966485) B6966485
theorem B3923569 : Blo 814346 3923569 := bstep (se 2 (by rfl) ⟨1471338, by rfl⟩ : syracuseStep 3923569 = 2942677) B2942677
theorem B1105699 : Blo 814346 1105699 := bstep (se 1 (by rfl) ⟨829274, by rfl⟩ : syracuseStep 1105699 = 1658549) B1658549
theorem B2613073 : Blo 814346 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B3104675 : Blo 814346 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B3104689 : Blo 814346 3104689 := bstep (se 2 (by rfl) ⟨1164258, by rfl⟩ : syracuseStep 3104689 = 2328517) B2328517
theorem B2515181 : Blo 814346 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B3301901 : Blo 814346 3301901 := bstep (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) B1238213
theorem B1860241 : Blo 814346 1860241 := bstep (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) B1395181
theorem B1696465 : Blo 814346 1696465 := bstep (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) B1272349
theorem B2319587 : Blo 814346 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B3106147 : Blo 814346 3106147 := bstep (se 1 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 3106147 = 4659221) B4659221
theorem B2942477 : Blo 814346 2942477 := bstep (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) B1103429
theorem B2942563 : Blo 814346 2942563 := bstep (se 1 (by rfl) ⟨2206922, by rfl⟩ : syracuseStep 2942563 = 4413845) B4413845
theorem B3303281 : Blo 814346 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1861553 : Blo 814346 1861553 := bstep (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) B1396165
theorem B23553989 : Blo 814346 23553989 := bstep (se 4 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 23553989 = 4416373) B4416373
theorem B10479557 : Blo 814346 10479557 := bstep (se 4 (by rfl) ⟨982458, by rfl⟩ : syracuseStep 10479557 = 1964917) B1964917
theorem B2320397 : Blo 814346 2320397 := bstep (se 3 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 2320397 = 870149) B870149
theorem B3139661 : Blo 814346 3139661 := bstep (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) B1177373
theorem B4122737 : Blo 814346 4122737 := bstep (se 2 (by rfl) ⟨1546026, by rfl⟩ : syracuseStep 4122737 = 3092053) B3092053
theorem B2320589 : Blo 814346 2320589 := bstep (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) B870221
theorem B2615789 : Blo 814346 2615789 := bstep (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) B980921
theorem B1305089 : Blo 814346 1305089 := bstep (se 2 (by rfl) ⟨489408, by rfl⟩ : syracuseStep 1305089 = 978817) B978817
theorem B6711821 : Blo 814346 6711821 := bstep (se 3 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 6711821 = 2516933) B2516933
theorem B5237297 : Blo 814346 5237297 := bstep (se 2 (by rfl) ⟨1963986, by rfl⟩ : syracuseStep 5237297 = 3927973) B3927973
theorem B4647557 : Blo 814346 4647557 := bstep (se 4 (by rfl) ⟨435708, by rfl⟩ : syracuseStep 4647557 = 871417) B871417
theorem B1305281 : Blo 814346 1305281 := bstep (se 2 (by rfl) ⟨489480, by rfl⟩ : syracuseStep 1305281 = 978961) B978961
theorem B1305409 : Blo 814346 1305409 := bstep (se 2 (by rfl) ⟨489528, by rfl⟩ : syracuseStep 1305409 = 979057) B979057
theorem B4648013 : Blo 814346 4648013 := bstep (se 3 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 4648013 = 1743005) B1743005
theorem B3304547 : Blo 814346 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B2321581 : Blo 814346 2321581 := bstep (se 3 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 2321581 = 870593) B870593
theorem B814355 : Blo 814346 814355 := bstep (se 1 (by rfl) ⟨610766, by rfl⟩ : syracuseStep 814355 = 1221533) B1221533
theorem B814371 : Blo 814346 814371 := bstep (se 1 (by rfl) ⟨610778, by rfl⟩ : syracuseStep 814371 = 1221557) B1221557
theorem B814387 : Blo 814346 814387 := bstep (se 1 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 814387 = 1221581) B1221581
theorem B814403 : Blo 814346 814403 := bstep (se 1 (by rfl) ⟨610802, by rfl⟩ : syracuseStep 814403 = 1221605) B1221605
theorem B814419 : Blo 814346 814419 := bstep (se 1 (by rfl) ⟨610814, by rfl⟩ : syracuseStep 814419 = 1221629) B1221629
theorem B814435 : Blo 814346 814435 := bstep (se 1 (by rfl) ⟨610826, by rfl⟩ : syracuseStep 814435 = 1221653) B1221653
theorem B814451 : Blo 814346 814451 := bstep (se 1 (by rfl) ⟨610838, by rfl⟩ : syracuseStep 814451 = 1221677) B1221677
theorem B814467 : Blo 814346 814467 := bstep (se 1 (by rfl) ⟨610850, by rfl⟩ : syracuseStep 814467 = 1221701) B1221701
theorem B11791757 : Blo 814346 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B814483 : Blo 814346 814483 := bstep (se 1 (by rfl) ⟨610862, by rfl⟩ : syracuseStep 814483 = 1221725) B1221725
theorem B814499 : Blo 814346 814499 := bstep (se 1 (by rfl) ⟨610874, by rfl⟩ : syracuseStep 814499 = 1221749) B1221749
theorem B814515 : Blo 814346 814515 := bstep (se 1 (by rfl) ⟨610886, by rfl⟩ : syracuseStep 814515 = 1221773) B1221773
theorem B1306049 : Blo 814346 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B814531 : Blo 814346 814531 := bstep (se 1 (by rfl) ⟨610898, by rfl⟩ : syracuseStep 814531 = 1221797) B1221797
theorem B814547 : Blo 814346 814547 := bstep (se 1 (by rfl) ⟨610910, by rfl⟩ : syracuseStep 814547 = 1221821) B1221821
theorem B814563 : Blo 814346 814563 := bstep (se 1 (by rfl) ⟨610922, by rfl⟩ : syracuseStep 814563 = 1221845) B1221845
theorem B814579 : Blo 814346 814579 := bstep (se 1 (by rfl) ⟨610934, by rfl⟩ : syracuseStep 814579 = 1221869) B1221869
theorem B814595 : Blo 814346 814595 := bstep (se 1 (by rfl) ⟨610946, by rfl⟩ : syracuseStep 814595 = 1221893) B1221893
theorem B814611 : Blo 814346 814611 := bstep (se 1 (by rfl) ⟨610958, by rfl⟩ : syracuseStep 814611 = 1221917) B1221917
theorem B814627 : Blo 814346 814627 := bstep (se 1 (by rfl) ⟨610970, by rfl⟩ : syracuseStep 814627 = 1221941) B1221941
theorem B4124195 : Blo 814346 4124195 := bstep (se 1 (by rfl) ⟨3093146, by rfl⟩ : syracuseStep 4124195 = 6186293) B6186293
theorem B814643 : Blo 814346 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B978499 : Blo 814346 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B814659 : Blo 814346 814659 := bstep (se 1 (by rfl) ⟨610994, by rfl⟩ : syracuseStep 814659 = 1221989) B1221989
theorem B814675 : Blo 814346 814675 := bstep (se 1 (by rfl) ⟨611006, by rfl⟩ : syracuseStep 814675 = 1222013) B1222013
theorem B814691 : Blo 814346 814691 := bstep (se 1 (by rfl) ⟨611018, by rfl⟩ : syracuseStep 814691 = 1222037) B1222037
theorem B814707 : Blo 814346 814707 := bstep (se 1 (by rfl) ⟨611030, by rfl⟩ : syracuseStep 814707 = 1222061) B1222061
theorem B814723 : Blo 814346 814723 := bstep (se 1 (by rfl) ⟨611042, by rfl⟩ : syracuseStep 814723 = 1222085) B1222085
theorem B814739 : Blo 814346 814739 := bstep (se 1 (by rfl) ⟨611054, by rfl⟩ : syracuseStep 814739 = 1222109) B1222109
theorem B814755 : Blo 814346 814755 := bstep (se 1 (by rfl) ⟨611066, by rfl⟩ : syracuseStep 814755 = 1222133) B1222133
theorem B814771 : Blo 814346 814771 := bstep (se 1 (by rfl) ⟨611078, by rfl⟩ : syracuseStep 814771 = 1222157) B1222157
theorem B814787 : Blo 814346 814787 := bstep (se 1 (by rfl) ⟨611090, by rfl⟩ : syracuseStep 814787 = 1222181) B1222181
theorem B814803 : Blo 814346 814803 := bstep (se 1 (by rfl) ⟨611102, by rfl⟩ : syracuseStep 814803 = 1222205) B1222205
theorem B814819 : Blo 814346 814819 := bstep (se 1 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 814819 = 1222229) B1222229
theorem B814835 : Blo 814346 814835 := bstep (se 1 (by rfl) ⟨611126, by rfl⟩ : syracuseStep 814835 = 1222253) B1222253
theorem B814851 : Blo 814346 814851 := bstep (se 1 (by rfl) ⟨611138, by rfl⟩ : syracuseStep 814851 = 1222277) B1222277
theorem B814867 : Blo 814346 814867 := bstep (se 1 (by rfl) ⟨611150, by rfl⟩ : syracuseStep 814867 = 1222301) B1222301
theorem B814883 : Blo 814346 814883 := bstep (se 1 (by rfl) ⟨611162, by rfl⟩ : syracuseStep 814883 = 1222325) B1222325
theorem B814899 : Blo 814346 814899 := bstep (se 1 (by rfl) ⟨611174, by rfl⟩ : syracuseStep 814899 = 1222349) B1222349
theorem B814915 : Blo 814346 814915 := bstep (se 1 (by rfl) ⟨611186, by rfl⟩ : syracuseStep 814915 = 1222373) B1222373
theorem B814931 : Blo 814346 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B814947 : Blo 814346 814947 := bstep (se 1 (by rfl) ⟨611210, by rfl⟩ : syracuseStep 814947 = 1222421) B1222421
theorem B814963 : Blo 814346 814963 := bstep (se 1 (by rfl) ⟨611222, by rfl⟩ : syracuseStep 814963 = 1222445) B1222445
theorem B814979 : Blo 814346 814979 := bstep (se 1 (by rfl) ⟨611234, by rfl⟩ : syracuseStep 814979 = 1222469) B1222469
theorem B814995 : Blo 814346 814995 := bstep (se 1 (by rfl) ⟨611246, by rfl⟩ : syracuseStep 814995 = 1222493) B1222493
theorem B815011 : Blo 814346 815011 := bstep (se 1 (by rfl) ⟨611258, by rfl⟩ : syracuseStep 815011 = 1222517) B1222517
theorem B815027 : Blo 814346 815027 := bstep (se 1 (by rfl) ⟨611270, by rfl⟩ : syracuseStep 815027 = 1222541) B1222541
theorem B815043 : Blo 814346 815043 := bstep (se 1 (by rfl) ⟨611282, by rfl⟩ : syracuseStep 815043 = 1222565) B1222565
theorem B815059 : Blo 814346 815059 := bstep (se 1 (by rfl) ⟨611294, by rfl⟩ : syracuseStep 815059 = 1222589) B1222589
theorem B815075 : Blo 814346 815075 := bstep (se 1 (by rfl) ⟨611306, by rfl⟩ : syracuseStep 815075 = 1222613) B1222613
theorem B5238755 : Blo 814346 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B815091 : Blo 814346 815091 := bstep (se 1 (by rfl) ⟨611318, by rfl⟩ : syracuseStep 815091 = 1222637) B1222637
theorem B815107 : Blo 814346 815107 := bstep (se 1 (by rfl) ⟨611330, by rfl⟩ : syracuseStep 815107 = 1222661) B1222661
theorem B815123 : Blo 814346 815123 := bstep (se 1 (by rfl) ⟨611342, by rfl⟩ : syracuseStep 815123 = 1222685) B1222685
theorem B815139 : Blo 814346 815139 := bstep (se 1 (by rfl) ⟨611354, by rfl⟩ : syracuseStep 815139 = 1222709) B1222709
theorem B2617379 : Blo 814346 2617379 := bstep (se 1 (by rfl) ⟨1963034, by rfl⟩ : syracuseStep 2617379 = 3926069) B3926069
theorem B815155 : Blo 814346 815155 := bstep (se 1 (by rfl) ⟨611366, by rfl⟩ : syracuseStep 815155 = 1222733) B1222733
theorem B19132469 : Blo 814346 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B815171 : Blo 814346 815171 := bstep (se 1 (by rfl) ⟨611378, by rfl⟩ : syracuseStep 815171 = 1222757) B1222757
theorem B815187 : Blo 814346 815187 := bstep (se 1 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 815187 = 1222781) B1222781
theorem B815203 : Blo 814346 815203 := bstep (se 1 (by rfl) ⟨611402, by rfl⟩ : syracuseStep 815203 = 1222805) B1222805
theorem B4419683 : Blo 814346 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B815219 : Blo 814346 815219 := bstep (se 1 (by rfl) ⟨611414, by rfl⟩ : syracuseStep 815219 = 1222829) B1222829
theorem B815235 : Blo 814346 815235 := bstep (se 1 (by rfl) ⟨611426, by rfl⟩ : syracuseStep 815235 = 1222853) B1222853
theorem B815251 : Blo 814346 815251 := bstep (se 1 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 815251 = 1222877) B1222877
theorem B815267 : Blo 814346 815267 := bstep (se 1 (by rfl) ⟨611450, by rfl⟩ : syracuseStep 815267 = 1222901) B1222901
theorem B815283 : Blo 814346 815283 := bstep (se 1 (by rfl) ⟨611462, by rfl⟩ : syracuseStep 815283 = 1222925) B1222925
theorem B815299 : Blo 814346 815299 := bstep (se 1 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 815299 = 1222949) B1222949
theorem B815315 : Blo 814346 815315 := bstep (se 1 (by rfl) ⟨611486, by rfl⟩ : syracuseStep 815315 = 1222973) B1222973
theorem B815331 : Blo 814346 815331 := bstep (se 1 (by rfl) ⟨611498, by rfl⟩ : syracuseStep 815331 = 1222997) B1222997
theorem B2748653 : Blo 814346 2748653 := bstep (se 3 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 2748653 = 1030745) B1030745
theorem B815347 : Blo 814346 815347 := bstep (se 1 (by rfl) ⟨611510, by rfl⟩ : syracuseStep 815347 = 1223021) B1223021
theorem B815363 : Blo 814346 815363 := bstep (se 1 (by rfl) ⟨611522, by rfl⟩ : syracuseStep 815363 = 1223045) B1223045
theorem B815379 : Blo 814346 815379 := bstep (se 1 (by rfl) ⟨611534, by rfl⟩ : syracuseStep 815379 = 1223069) B1223069
theorem B2748707 : Blo 814346 2748707 := bstep (se 1 (by rfl) ⟨2061530, by rfl⟩ : syracuseStep 2748707 = 4123061) B4123061
theorem B815395 : Blo 814346 815395 := bstep (se 1 (by rfl) ⟨611546, by rfl⟩ : syracuseStep 815395 = 1223093) B1223093
theorem B815411 : Blo 814346 815411 := bstep (se 1 (by rfl) ⟨611558, by rfl⟩ : syracuseStep 815411 = 1223117) B1223117
theorem B815427 : Blo 814346 815427 := bstep (se 1 (by rfl) ⟨611570, by rfl⟩ : syracuseStep 815427 = 1223141) B1223141
theorem B4125005 : Blo 814346 4125005 := bstep (se 3 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 4125005 = 1546877) B1546877
theorem B2486609 : Blo 814346 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B815443 : Blo 814346 815443 := bstep (se 1 (by rfl) ⟨611582, by rfl⟩ : syracuseStep 815443 = 1223165) B1223165
theorem B815459 : Blo 814346 815459 := bstep (se 1 (by rfl) ⟨611594, by rfl⟩ : syracuseStep 815459 = 1223189) B1223189
theorem B815475 : Blo 814346 815475 := bstep (se 1 (by rfl) ⟨611606, by rfl⟩ : syracuseStep 815475 = 1223213) B1223213
theorem B815491 : Blo 814346 815491 := bstep (se 1 (by rfl) ⟨611618, by rfl⟩ : syracuseStep 815491 = 1223237) B1223237
theorem B815507 : Blo 814346 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B815523 : Blo 814346 815523 := bstep (se 1 (by rfl) ⟨611642, by rfl⟩ : syracuseStep 815523 = 1223285) B1223285
theorem B815539 : Blo 814346 815539 := bstep (se 1 (by rfl) ⟨611654, by rfl⟩ : syracuseStep 815539 = 1223309) B1223309
theorem B815555 : Blo 814346 815555 := bstep (se 1 (by rfl) ⟨611666, by rfl⟩ : syracuseStep 815555 = 1223333) B1223333
theorem B815571 : Blo 814346 815571 := bstep (se 1 (by rfl) ⟨611678, by rfl⟩ : syracuseStep 815571 = 1223357) B1223357
theorem B815587 : Blo 814346 815587 := bstep (se 1 (by rfl) ⟨611690, by rfl⟩ : syracuseStep 815587 = 1223381) B1223381
theorem B815603 : Blo 814346 815603 := bstep (se 1 (by rfl) ⟨611702, by rfl⟩ : syracuseStep 815603 = 1223405) B1223405
theorem B815619 : Blo 814346 815619 := bstep (se 1 (by rfl) ⟨611714, by rfl⟩ : syracuseStep 815619 = 1223429) B1223429
theorem B815635 : Blo 814346 815635 := bstep (se 1 (by rfl) ⟨611726, by rfl⟩ : syracuseStep 815635 = 1223453) B1223453
theorem B815651 : Blo 814346 815651 := bstep (se 1 (by rfl) ⟨611738, by rfl⟩ : syracuseStep 815651 = 1223477) B1223477
theorem B2748977 : Blo 814346 2748977 := bstep (se 2 (by rfl) ⟨1030866, by rfl⟩ : syracuseStep 2748977 = 2061733) B2061733
theorem B815667 : Blo 814346 815667 := bstep (se 1 (by rfl) ⟨611750, by rfl⟩ : syracuseStep 815667 = 1223501) B1223501
theorem B16740917 : Blo 814346 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B815683 : Blo 814346 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B815699 : Blo 814346 815699 := bstep (se 1 (by rfl) ⟨611774, by rfl⟩ : syracuseStep 815699 = 1223549) B1223549
theorem B815715 : Blo 814346 815715 := bstep (se 1 (by rfl) ⟨611786, by rfl⟩ : syracuseStep 815715 = 1223573) B1223573
theorem B979571 : Blo 814346 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B815731 : Blo 814346 815731 := bstep (se 1 (by rfl) ⟨611798, by rfl⟩ : syracuseStep 815731 = 1223597) B1223597
theorem B815747 : Blo 814346 815747 := bstep (se 1 (by rfl) ⟨611810, by rfl⟩ : syracuseStep 815747 = 1223621) B1223621
theorem B815763 : Blo 814346 815763 := bstep (se 1 (by rfl) ⟨611822, by rfl⟩ : syracuseStep 815763 = 1223645) B1223645
theorem B1241747 : Blo 814346 1241747 := bstep (se 1 (by rfl) ⟨931310, by rfl⟩ : syracuseStep 1241747 = 1862621) B1862621
theorem B815779 : Blo 814346 815779 := bstep (se 1 (by rfl) ⟨611834, by rfl⟩ : syracuseStep 815779 = 1223669) B1223669
theorem B815795 : Blo 814346 815795 := bstep (se 1 (by rfl) ⟨611846, by rfl⟩ : syracuseStep 815795 = 1223693) B1223693
theorem B815811 : Blo 814346 815811 := bstep (se 1 (by rfl) ⟨611858, by rfl⟩ : syracuseStep 815811 = 1223717) B1223717
theorem B815827 : Blo 814346 815827 := bstep (se 1 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 815827 = 1223741) B1223741
theorem B815843 : Blo 814346 815843 := bstep (se 1 (by rfl) ⟨611882, by rfl⟩ : syracuseStep 815843 = 1223765) B1223765
theorem B815859 : Blo 814346 815859 := bstep (se 1 (by rfl) ⟨611894, by rfl⟩ : syracuseStep 815859 = 1223789) B1223789
theorem B815875 : Blo 814346 815875 := bstep (se 1 (by rfl) ⟨611906, by rfl⟩ : syracuseStep 815875 = 1223813) B1223813
theorem B815891 : Blo 814346 815891 := bstep (se 1 (by rfl) ⟨611918, by rfl⟩ : syracuseStep 815891 = 1223837) B1223837
theorem B815907 : Blo 814346 815907 := bstep (se 1 (by rfl) ⟨611930, by rfl⟩ : syracuseStep 815907 = 1223861) B1223861
theorem B815923 : Blo 814346 815923 := bstep (se 1 (by rfl) ⟨611942, by rfl⟩ : syracuseStep 815923 = 1223885) B1223885
theorem B815939 : Blo 814346 815939 := bstep (se 1 (by rfl) ⟨611954, by rfl⟩ : syracuseStep 815939 = 1223909) B1223909
theorem B1307459 : Blo 814346 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B815955 : Blo 814346 815955 := bstep (se 1 (by rfl) ⟨611966, by rfl⟩ : syracuseStep 815955 = 1223933) B1223933
theorem B815971 : Blo 814346 815971 := bstep (se 1 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 815971 = 1223957) B1223957
theorem B2323313 : Blo 814346 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B815987 : Blo 814346 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B816003 : Blo 814346 816003 := bstep (se 1 (by rfl) ⟨612002, by rfl⟩ : syracuseStep 816003 = 1224005) B1224005
theorem B816019 : Blo 814346 816019 := bstep (se 1 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 816019 = 1224029) B1224029
theorem B816035 : Blo 814346 816035 := bstep (se 1 (by rfl) ⟨612026, by rfl⟩ : syracuseStep 816035 = 1224053) B1224053
theorem B816051 : Blo 814346 816051 := bstep (se 1 (by rfl) ⟨612038, by rfl⟩ : syracuseStep 816051 = 1224077) B1224077
theorem B816067 : Blo 814346 816067 := bstep (se 1 (by rfl) ⟨612050, by rfl⟩ : syracuseStep 816067 = 1224101) B1224101
theorem B1307587 : Blo 814346 1307587 := bstep (se 1 (by rfl) ⟨980690, by rfl⟩ : syracuseStep 1307587 = 1961381) B1961381
theorem B816083 : Blo 814346 816083 := bstep (se 1 (by rfl) ⟨612062, by rfl⟩ : syracuseStep 816083 = 1224125) B1224125
theorem B816099 : Blo 814346 816099 := bstep (se 1 (by rfl) ⟨612074, by rfl⟩ : syracuseStep 816099 = 1224149) B1224149
theorem B816115 : Blo 814346 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B816131 : Blo 814346 816131 := bstep (se 1 (by rfl) ⟨612098, by rfl⟩ : syracuseStep 816131 = 1224197) B1224197
theorem B816147 : Blo 814346 816147 := bstep (se 1 (by rfl) ⟨612110, by rfl⟩ : syracuseStep 816147 = 1224221) B1224221
theorem B816163 : Blo 814346 816163 := bstep (se 1 (by rfl) ⟨612122, by rfl⟩ : syracuseStep 816163 = 1224245) B1224245
theorem B2323505 : Blo 814346 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B816179 : Blo 814346 816179 := bstep (se 1 (by rfl) ⟨612134, by rfl⟩ : syracuseStep 816179 = 1224269) B1224269
theorem B816195 : Blo 814346 816195 := bstep (se 1 (by rfl) ⟨612146, by rfl⟩ : syracuseStep 816195 = 1224293) B1224293
theorem B1471555 : Blo 814346 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B2749517 : Blo 814346 2749517 := bstep (se 3 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 2749517 = 1031069) B1031069
theorem B816211 : Blo 814346 816211 := bstep (se 1 (by rfl) ⟨612158, by rfl⟩ : syracuseStep 816211 = 1224317) B1224317
theorem B816227 : Blo 814346 816227 := bstep (se 1 (by rfl) ⟨612170, by rfl⟩ : syracuseStep 816227 = 1224341) B1224341
theorem B816243 : Blo 814346 816243 := bstep (se 1 (by rfl) ⟨612182, by rfl⟩ : syracuseStep 816243 = 1224365) B1224365
theorem B2749571 : Blo 814346 2749571 := bstep (se 1 (by rfl) ⟨2062178, by rfl⟩ : syracuseStep 2749571 = 4124357) B4124357
theorem B816259 : Blo 814346 816259 := bstep (se 1 (by rfl) ⟨612194, by rfl⟩ : syracuseStep 816259 = 1224389) B1224389
theorem B816275 : Blo 814346 816275 := bstep (se 1 (by rfl) ⟨612206, by rfl⟩ : syracuseStep 816275 = 1224413) B1224413
theorem B816291 : Blo 814346 816291 := bstep (se 1 (by rfl) ⟨612218, by rfl⟩ : syracuseStep 816291 = 1224437) B1224437
theorem B816307 : Blo 814346 816307 := bstep (se 1 (by rfl) ⟨612230, by rfl⟩ : syracuseStep 816307 = 1224461) B1224461
theorem B816323 : Blo 814346 816323 := bstep (se 1 (by rfl) ⟨612242, by rfl⟩ : syracuseStep 816323 = 1224485) B1224485
theorem B2061521 : Blo 814346 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B816339 : Blo 814346 816339 := bstep (se 1 (by rfl) ⟨612254, by rfl⟩ : syracuseStep 816339 = 1224509) B1224509
theorem B816355 : Blo 814346 816355 := bstep (se 1 (by rfl) ⟨612266, by rfl⟩ : syracuseStep 816355 = 1224533) B1224533
theorem B816371 : Blo 814346 816371 := bstep (se 1 (by rfl) ⟨612278, by rfl⟩ : syracuseStep 816371 = 1224557) B1224557
theorem B2061571 : Blo 814346 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B816387 : Blo 814346 816387 := bstep (se 1 (by rfl) ⟨612290, by rfl⟩ : syracuseStep 816387 = 1224581) B1224581
theorem B816403 : Blo 814346 816403 := bstep (se 1 (by rfl) ⟨612302, by rfl⟩ : syracuseStep 816403 = 1224605) B1224605
theorem B816419 : Blo 814346 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B2618659 : Blo 814346 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B1045811 : Blo 814346 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B816435 : Blo 814346 816435 := bstep (se 1 (by rfl) ⟨612326, by rfl⟩ : syracuseStep 816435 = 1224653) B1224653
theorem B816451 : Blo 814346 816451 := bstep (se 1 (by rfl) ⟨612338, by rfl⟩ : syracuseStep 816451 = 1224677) B1224677
theorem B816467 : Blo 814346 816467 := bstep (se 1 (by rfl) ⟨612350, by rfl⟩ : syracuseStep 816467 = 1224701) B1224701
theorem B1242451 : Blo 814346 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B1832291 : Blo 814346 1832291 := bstep (se 1 (by rfl) ⟨1374218, by rfl⟩ : syracuseStep 1832291 = 2748437) B2748437
theorem B816483 : Blo 814346 816483 := bstep (se 1 (by rfl) ⟨612362, by rfl⟩ : syracuseStep 816483 = 1224725) B1224725
theorem B816499 : Blo 814346 816499 := bstep (se 1 (by rfl) ⟨612374, by rfl⟩ : syracuseStep 816499 = 1224749) B1224749
theorem B816515 : Blo 814346 816515 := bstep (se 1 (by rfl) ⟨612386, by rfl⟩ : syracuseStep 816515 = 1224773) B1224773
theorem B2061713 : Blo 814346 2061713 := bstep (se 2 (by rfl) ⟨773142, by rfl⟩ : syracuseStep 2061713 = 1546285) B1546285
theorem B2749841 : Blo 814346 2749841 := bstep (se 2 (by rfl) ⟨1031190, by rfl⟩ : syracuseStep 2749841 = 2062381) B2062381
theorem B816531 : Blo 814346 816531 := bstep (se 1 (by rfl) ⟨612398, by rfl⟩ : syracuseStep 816531 = 1224797) B1224797
theorem B816547 : Blo 814346 816547 := bstep (se 1 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 816547 = 1224821) B1224821
theorem B1045939 : Blo 814346 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B816563 : Blo 814346 816563 := bstep (se 1 (by rfl) ⟨612422, by rfl⟩ : syracuseStep 816563 = 1224845) B1224845
theorem B816579 : Blo 814346 816579 := bstep (se 1 (by rfl) ⟨612434, by rfl⟩ : syracuseStep 816579 = 1224869) B1224869
theorem B816595 : Blo 814346 816595 := bstep (se 1 (by rfl) ⟨612446, by rfl⟩ : syracuseStep 816595 = 1224893) B1224893
theorem B816611 : Blo 814346 816611 := bstep (se 1 (by rfl) ⟨612458, by rfl⟩ : syracuseStep 816611 = 1224917) B1224917
theorem B1308145 : Blo 814346 1308145 := bstep (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) B981109
theorem B816627 : Blo 814346 816627 := bstep (se 1 (by rfl) ⟨612470, by rfl⟩ : syracuseStep 816627 = 1224941) B1224941
theorem B1242611 : Blo 814346 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B816643 : Blo 814346 816643 := bstep (se 1 (by rfl) ⟨612482, by rfl⟩ : syracuseStep 816643 = 1224965) B1224965
theorem B816659 : Blo 814346 816659 := bstep (se 1 (by rfl) ⟨612494, by rfl⟩ : syracuseStep 816659 = 1224989) B1224989
theorem B816675 : Blo 814346 816675 := bstep (se 1 (by rfl) ⟨612506, by rfl⟩ : syracuseStep 816675 = 1225013) B1225013
theorem B816691 : Blo 814346 816691 := bstep (se 1 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 816691 = 1225037) B1225037
theorem B816707 : Blo 814346 816707 := bstep (se 1 (by rfl) ⟨612530, by rfl⟩ : syracuseStep 816707 = 1225061) B1225061
theorem B816723 : Blo 814346 816723 := bstep (se 1 (by rfl) ⟨612542, by rfl⟩ : syracuseStep 816723 = 1225085) B1225085
theorem B816739 : Blo 814346 816739 := bstep (se 1 (by rfl) ⟨612554, by rfl⟩ : syracuseStep 816739 = 1225109) B1225109
theorem B1832561 : Blo 814346 1832561 := bstep (se 2 (by rfl) ⟨687210, by rfl⟩ : syracuseStep 1832561 = 1374421) B1374421
theorem B2618993 : Blo 814346 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B816755 : Blo 814346 816755 := bstep (se 1 (by rfl) ⟨612566, by rfl⟩ : syracuseStep 816755 = 1225133) B1225133
theorem B1832579 : Blo 814346 1832579 := bstep (se 1 (by rfl) ⟨1374434, by rfl⟩ : syracuseStep 1832579 = 2748869) B2748869
theorem B816771 : Blo 814346 816771 := bstep (se 1 (by rfl) ⟨612578, by rfl⟩ : syracuseStep 816771 = 1225157) B1225157
theorem B1242769 : Blo 814346 1242769 := bstep (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) B932077
theorem B816787 : Blo 814346 816787 := bstep (se 1 (by rfl) ⟨612590, by rfl⟩ : syracuseStep 816787 = 1225181) B1225181
theorem B816803 : Blo 814346 816803 := bstep (se 1 (by rfl) ⟨612602, by rfl⟩ : syracuseStep 816803 = 1225205) B1225205
theorem B5240497 : Blo 814346 5240497 := bstep (se 2 (by rfl) ⟨1965186, by rfl⟩ : syracuseStep 5240497 = 3930373) B3930373
theorem B816819 : Blo 814346 816819 := bstep (se 1 (by rfl) ⟨612614, by rfl⟩ : syracuseStep 816819 = 1225229) B1225229
theorem B816835 : Blo 814346 816835 := bstep (se 1 (by rfl) ⟨612626, by rfl⟩ : syracuseStep 816835 = 1225253) B1225253
theorem B816851 : Blo 814346 816851 := bstep (se 1 (by rfl) ⟨612638, by rfl⟩ : syracuseStep 816851 = 1225277) B1225277
theorem B816867 : Blo 814346 816867 := bstep (se 1 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 816867 = 1225301) B1225301
theorem B816883 : Blo 814346 816883 := bstep (se 1 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 816883 = 1225325) B1225325
theorem B816899 : Blo 814346 816899 := bstep (se 1 (by rfl) ⟨612674, by rfl⟩ : syracuseStep 816899 = 1225349) B1225349
theorem B816915 : Blo 814346 816915 := bstep (se 1 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 816915 = 1225373) B1225373
theorem B816931 : Blo 814346 816931 := bstep (se 1 (by rfl) ⟨612698, by rfl⟩ : syracuseStep 816931 = 1225397) B1225397
theorem B4421411 : Blo 814346 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B816947 : Blo 814346 816947 := bstep (se 1 (by rfl) ⟨612710, by rfl⟩ : syracuseStep 816947 = 1225421) B1225421
theorem B816963 : Blo 814346 816963 := bstep (se 1 (by rfl) ⟨612722, by rfl⟩ : syracuseStep 816963 = 1225445) B1225445
theorem B816979 : Blo 814346 816979 := bstep (se 1 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 816979 = 1225469) B1225469
theorem B816995 : Blo 814346 816995 := bstep (se 1 (by rfl) ⟨612746, by rfl⟩ : syracuseStep 816995 = 1225493) B1225493
theorem B7862129 : Blo 814346 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B817011 : Blo 814346 817011 := bstep (se 1 (by rfl) ⟨612758, by rfl⟩ : syracuseStep 817011 = 1225517) B1225517
theorem B817027 : Blo 814346 817027 := bstep (se 1 (by rfl) ⟨612770, by rfl⟩ : syracuseStep 817027 = 1225541) B1225541
theorem B29718413 : Blo 814346 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B1832849 : Blo 814346 1832849 := bstep (se 2 (by rfl) ⟨687318, by rfl⟩ : syracuseStep 1832849 = 1374637) B1374637
theorem B817043 : Blo 814346 817043 := bstep (se 1 (by rfl) ⟨612782, by rfl⟩ : syracuseStep 817043 = 1225565) B1225565
theorem B1832867 : Blo 814346 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B817059 : Blo 814346 817059 := bstep (se 1 (by rfl) ⟨612794, by rfl⟩ : syracuseStep 817059 = 1225589) B1225589
theorem B2750381 : Blo 814346 2750381 := bstep (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) B1031393
theorem B4650929 : Blo 814346 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B817075 : Blo 814346 817075 := bstep (se 1 (by rfl) ⟨612806, by rfl⟩ : syracuseStep 817075 = 1225613) B1225613
theorem B1046467 : Blo 814346 1046467 := bstep (se 1 (by rfl) ⟨784850, by rfl⟩ : syracuseStep 1046467 = 1569701) B1569701
theorem B817091 : Blo 814346 817091 := bstep (se 1 (by rfl) ⟨612818, by rfl⟩ : syracuseStep 817091 = 1225637) B1225637
theorem B817107 : Blo 814346 817107 := bstep (se 1 (by rfl) ⟨612830, by rfl⟩ : syracuseStep 817107 = 1225661) B1225661
theorem B2750435 : Blo 814346 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B817123 : Blo 814346 817123 := bstep (se 1 (by rfl) ⟨612842, by rfl⟩ : syracuseStep 817123 = 1225685) B1225685
theorem B817139 : Blo 814346 817139 := bstep (se 1 (by rfl) ⟨612854, by rfl⟩ : syracuseStep 817139 = 1225709) B1225709
theorem B817155 : Blo 814346 817155 := bstep (se 1 (by rfl) ⟨612866, by rfl⟩ : syracuseStep 817155 = 1225733) B1225733
theorem B2324497 : Blo 814346 2324497 := bstep (se 2 (by rfl) ⟨871686, by rfl⟩ : syracuseStep 2324497 = 1743373) B1743373
theorem B817171 : Blo 814346 817171 := bstep (se 1 (by rfl) ⟨612878, by rfl⟩ : syracuseStep 817171 = 1225757) B1225757
theorem B817187 : Blo 814346 817187 := bstep (se 1 (by rfl) ⟨612890, by rfl⟩ : syracuseStep 817187 = 1225781) B1225781
theorem B1374259 : Blo 814346 1374259 := bstep (se 1 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 1374259 = 2061389) B2061389
theorem B817203 : Blo 814346 817203 := bstep (se 1 (by rfl) ⟨612902, by rfl⟩ : syracuseStep 817203 = 1225805) B1225805
theorem B817219 : Blo 814346 817219 := bstep (se 1 (by rfl) ⟨612914, by rfl⟩ : syracuseStep 817219 = 1225829) B1225829
theorem B1472593 : Blo 814346 1472593 := bstep (se 2 (by rfl) ⟨552222, by rfl⟩ : syracuseStep 1472593 = 1104445) B1104445
theorem B817235 : Blo 814346 817235 := bstep (se 1 (by rfl) ⟨612926, by rfl⟩ : syracuseStep 817235 = 1225853) B1225853
theorem B817251 : Blo 814346 817251 := bstep (se 1 (by rfl) ⟨612938, by rfl⟩ : syracuseStep 817251 = 1225877) B1225877
theorem B817267 : Blo 814346 817267 := bstep (se 1 (by rfl) ⟨612950, by rfl⟩ : syracuseStep 817267 = 1225901) B1225901
theorem B817283 : Blo 814346 817283 := bstep (se 1 (by rfl) ⟨612962, by rfl⟩ : syracuseStep 817283 = 1225925) B1225925
theorem B3307661 : Blo 814346 3307661 := bstep (se 3 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 3307661 = 1240373) B1240373
theorem B1308817 : Blo 814346 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B817299 : Blo 814346 817299 := bstep (se 1 (by rfl) ⟨612974, by rfl⟩ : syracuseStep 817299 = 1225949) B1225949
theorem B817315 : Blo 814346 817315 := bstep (se 1 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 817315 = 1225973) B1225973
theorem B1833137 : Blo 814346 1833137 := bstep (se 2 (by rfl) ⟨687426, by rfl⟩ : syracuseStep 1833137 = 1374853) B1374853
theorem B817331 : Blo 814346 817331 := bstep (se 1 (by rfl) ⟨612998, by rfl⟩ : syracuseStep 817331 = 1225997) B1225997
theorem B1374401 : Blo 814346 1374401 := bstep (se 2 (by rfl) ⟨515400, by rfl⟩ : syracuseStep 1374401 = 1030801) B1030801
theorem B1833155 : Blo 814346 1833155 := bstep (se 1 (by rfl) ⟨1374866, by rfl⟩ : syracuseStep 1833155 = 2749733) B2749733
theorem B817347 : Blo 814346 817347 := bstep (se 1 (by rfl) ⟨613010, by rfl⟩ : syracuseStep 817347 = 1226021) B1226021
theorem B2488529 : Blo 814346 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B817363 : Blo 814346 817363 := bstep (se 1 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 817363 = 1226045) B1226045
theorem B817379 : Blo 814346 817379 := bstep (se 1 (by rfl) ⟨613034, by rfl⟩ : syracuseStep 817379 = 1226069) B1226069
theorem B2750705 : Blo 814346 2750705 := bstep (se 2 (by rfl) ⟨1031514, by rfl⟩ : syracuseStep 2750705 = 2063029) B2063029
theorem B817395 : Blo 814346 817395 := bstep (se 1 (by rfl) ⟨613046, by rfl⟩ : syracuseStep 817395 = 1226093) B1226093
theorem B817411 : Blo 814346 817411 := bstep (se 1 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 817411 = 1226117) B1226117
theorem B817427 : Blo 814346 817427 := bstep (se 1 (by rfl) ⟨613070, by rfl⟩ : syracuseStep 817427 = 1226141) B1226141
theorem B2324771 : Blo 814346 2324771 := bstep (se 1 (by rfl) ⟨1743578, by rfl⟩ : syracuseStep 2324771 = 3487157) B3487157
theorem B817443 : Blo 814346 817443 := bstep (se 1 (by rfl) ⟨613082, by rfl⟩ : syracuseStep 817443 = 1226165) B1226165
theorem B2095409 : Blo 814346 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B817459 : Blo 814346 817459 := bstep (se 1 (by rfl) ⟨613094, by rfl⟩ : syracuseStep 817459 = 1226189) B1226189
theorem B1374529 : Blo 814346 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B817475 : Blo 814346 817475 := bstep (se 1 (by rfl) ⟨613106, by rfl⟩ : syracuseStep 817475 = 1226213) B1226213
theorem B817491 : Blo 814346 817491 := bstep (se 1 (by rfl) ⟨613118, by rfl⟩ : syracuseStep 817491 = 1226237) B1226237
theorem B1374563 : Blo 814346 1374563 := bstep (se 1 (by rfl) ⟨1030922, by rfl⟩ : syracuseStep 1374563 = 2061845) B2061845
theorem B817507 : Blo 814346 817507 := bstep (se 1 (by rfl) ⟨613130, by rfl⟩ : syracuseStep 817507 = 1226261) B1226261
theorem B2062705 : Blo 814346 2062705 := bstep (se 2 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 2062705 = 1547029) B1547029
theorem B817523 : Blo 814346 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B817539 : Blo 814346 817539 := bstep (se 1 (by rfl) ⟨613154, by rfl⟩ : syracuseStep 817539 = 1226309) B1226309
theorem B817555 : Blo 814346 817555 := bstep (se 1 (by rfl) ⟨613166, by rfl⟩ : syracuseStep 817555 = 1226333) B1226333
theorem B817571 : Blo 814346 817571 := bstep (se 1 (by rfl) ⟨613178, by rfl⟩ : syracuseStep 817571 = 1226357) B1226357
theorem B1866161 : Blo 814346 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B817587 : Blo 814346 817587 := bstep (se 1 (by rfl) ⟨613190, by rfl⟩ : syracuseStep 817587 = 1226381) B1226381
theorem B817603 : Blo 814346 817603 := bstep (se 1 (by rfl) ⟨613202, by rfl⟩ : syracuseStep 817603 = 1226405) B1226405
theorem B1833425 : Blo 814346 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B817619 : Blo 814346 817619 := bstep (se 1 (by rfl) ⟨613214, by rfl⟩ : syracuseStep 817619 = 1226429) B1226429
theorem B1374691 : Blo 814346 1374691 := bstep (se 1 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 1374691 = 2062037) B2062037
theorem B1833443 : Blo 814346 1833443 := bstep (se 1 (by rfl) ⟨1375082, by rfl⟩ : syracuseStep 1833443 = 2750165) B2750165
theorem B2324963 : Blo 814346 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B817635 : Blo 814346 817635 := bstep (se 1 (by rfl) ⟨613226, by rfl⟩ : syracuseStep 817635 = 1226453) B1226453
theorem B817651 : Blo 814346 817651 := bstep (se 1 (by rfl) ⟨613238, by rfl⟩ : syracuseStep 817651 = 1226477) B1226477
theorem B817667 : Blo 814346 817667 := bstep (se 1 (by rfl) ⟨613250, by rfl⟩ : syracuseStep 817667 = 1226501) B1226501
theorem B817683 : Blo 814346 817683 := bstep (se 1 (by rfl) ⟨613262, by rfl⟩ : syracuseStep 817683 = 1226525) B1226525
theorem B817699 : Blo 814346 817699 := bstep (se 1 (by rfl) ⟨613274, by rfl⟩ : syracuseStep 817699 = 1226549) B1226549
theorem B817715 : Blo 814346 817715 := bstep (se 1 (by rfl) ⟨613286, by rfl⟩ : syracuseStep 817715 = 1226573) B1226573
theorem B817731 : Blo 814346 817731 := bstep (se 1 (by rfl) ⟨613298, by rfl⟩ : syracuseStep 817731 = 1226597) B1226597
theorem B817747 : Blo 814346 817747 := bstep (se 1 (by rfl) ⟨613310, by rfl⟩ : syracuseStep 817747 = 1226621) B1226621
theorem B817763 : Blo 814346 817763 := bstep (se 1 (by rfl) ⟨613322, by rfl⟩ : syracuseStep 817763 = 1226645) B1226645
theorem B1374833 : Blo 814346 1374833 := bstep (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) B1031125
theorem B817779 : Blo 814346 817779 := bstep (se 1 (by rfl) ⟨613334, by rfl⟩ : syracuseStep 817779 = 1226669) B1226669
theorem B2062979 : Blo 814346 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B817795 : Blo 814346 817795 := bstep (se 1 (by rfl) ⟨613346, by rfl⟩ : syracuseStep 817795 = 1226693) B1226693
theorem B817811 : Blo 814346 817811 := bstep (se 1 (by rfl) ⟨613358, by rfl⟩ : syracuseStep 817811 = 1226717) B1226717
theorem B817827 : Blo 814346 817827 := bstep (se 1 (by rfl) ⟨613370, by rfl⟩ : syracuseStep 817827 = 1226741) B1226741
theorem B817843 : Blo 814346 817843 := bstep (se 1 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 817843 = 1226765) B1226765
theorem B817859 : Blo 814346 817859 := bstep (se 1 (by rfl) ⟨613394, by rfl⟩ : syracuseStep 817859 = 1226789) B1226789
theorem B817875 : Blo 814346 817875 := bstep (se 1 (by rfl) ⟨613406, by rfl⟩ : syracuseStep 817875 = 1226813) B1226813
theorem B916195 : Blo 814346 916195 := bstep (se 1 (by rfl) ⟨687146, by rfl⟩ : syracuseStep 916195 = 1374293) B1374293
theorem B817891 : Blo 814346 817891 := bstep (se 1 (by rfl) ⟨613418, by rfl⟩ : syracuseStep 817891 = 1226837) B1226837
theorem B1374961 : Blo 814346 1374961 := bstep (se 2 (by rfl) ⟨515610, by rfl⟩ : syracuseStep 1374961 = 1031221) B1031221
theorem B1833713 : Blo 814346 1833713 := bstep (se 2 (by rfl) ⟨687642, by rfl⟩ : syracuseStep 1833713 = 1375285) B1375285
theorem B817907 : Blo 814346 817907 := bstep (se 1 (by rfl) ⟨613430, by rfl⟩ : syracuseStep 817907 = 1226861) B1226861
theorem B1833731 : Blo 814346 1833731 := bstep (se 1 (by rfl) ⟨1375298, by rfl⟩ : syracuseStep 1833731 = 2750597) B2750597
theorem B817923 : Blo 814346 817923 := bstep (se 1 (by rfl) ⟨613442, by rfl⟩ : syracuseStep 817923 = 1226885) B1226885
theorem B2751245 : Blo 814346 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B1374995 : Blo 814346 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B817939 : Blo 814346 817939 := bstep (se 1 (by rfl) ⟨613454, by rfl⟩ : syracuseStep 817939 = 1226909) B1226909
theorem B817955 : Blo 814346 817955 := bstep (se 1 (by rfl) ⟨613466, by rfl⟩ : syracuseStep 817955 = 1226933) B1226933
theorem B817971 : Blo 814346 817971 := bstep (se 1 (by rfl) ⟨613478, by rfl⟩ : syracuseStep 817971 = 1226957) B1226957
theorem B2063171 : Blo 814346 2063171 := bstep (se 1 (by rfl) ⟨1547378, by rfl⟩ : syracuseStep 2063171 = 3094757) B3094757
theorem B2751299 : Blo 814346 2751299 := bstep (se 1 (by rfl) ⟨2063474, by rfl⟩ : syracuseStep 2751299 = 4126949) B4126949
theorem B817987 : Blo 814346 817987 := bstep (se 1 (by rfl) ⟨613490, by rfl⟩ : syracuseStep 817987 = 1226981) B1226981
theorem B818003 : Blo 814346 818003 := bstep (se 1 (by rfl) ⟨613502, by rfl⟩ : syracuseStep 818003 = 1227005) B1227005
theorem B818019 : Blo 814346 818019 := bstep (se 1 (by rfl) ⟨613514, by rfl⟩ : syracuseStep 818019 = 1227029) B1227029
theorem B916339 : Blo 814346 916339 := bstep (se 1 (by rfl) ⟨687254, by rfl⟩ : syracuseStep 916339 = 1374509) B1374509
theorem B818035 : Blo 814346 818035 := bstep (se 1 (by rfl) ⟨613526, by rfl⟩ : syracuseStep 818035 = 1227053) B1227053
theorem B818051 : Blo 814346 818051 := bstep (se 1 (by rfl) ⟨613538, by rfl⟩ : syracuseStep 818051 = 1227077) B1227077
theorem B1375123 : Blo 814346 1375123 := bstep (se 1 (by rfl) ⟨1031342, by rfl⟩ : syracuseStep 1375123 = 2062685) B2062685
theorem B818067 : Blo 814346 818067 := bstep (se 1 (by rfl) ⟨613550, by rfl⟩ : syracuseStep 818067 = 1227101) B1227101
theorem B818083 : Blo 814346 818083 := bstep (se 1 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 818083 = 1227125) B1227125
theorem B818099 : Blo 814346 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B818115 : Blo 814346 818115 := bstep (se 1 (by rfl) ⟨613586, by rfl⟩ : syracuseStep 818115 = 1227173) B1227173
theorem B818131 : Blo 814346 818131 := bstep (se 1 (by rfl) ⟨613598, by rfl⟩ : syracuseStep 818131 = 1227197) B1227197
theorem B818147 : Blo 814346 818147 := bstep (se 1 (by rfl) ⟨613610, by rfl⟩ : syracuseStep 818147 = 1227221) B1227221
theorem B818163 : Blo 814346 818163 := bstep (se 1 (by rfl) ⟨613622, by rfl⟩ : syracuseStep 818163 = 1227245) B1227245
theorem B916483 : Blo 814346 916483 := bstep (se 1 (by rfl) ⟨687362, by rfl⟩ : syracuseStep 916483 = 1374725) B1374725
theorem B818179 : Blo 814346 818179 := bstep (se 1 (by rfl) ⟨613634, by rfl⟩ : syracuseStep 818179 = 1227269) B1227269
theorem B1834001 : Blo 814346 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B818195 : Blo 814346 818195 := bstep (se 1 (by rfl) ⟨613646, by rfl⟩ : syracuseStep 818195 = 1227293) B1227293
theorem B1244179 : Blo 814346 1244179 := bstep (se 1 (by rfl) ⟨933134, by rfl⟩ : syracuseStep 1244179 = 1866269) B1866269
theorem B1375265 : Blo 814346 1375265 := bstep (se 2 (by rfl) ⟨515724, by rfl⟩ : syracuseStep 1375265 = 1031449) B1031449
theorem B1834019 : Blo 814346 1834019 := bstep (se 1 (by rfl) ⟨1375514, by rfl⟩ : syracuseStep 1834019 = 2751029) B2751029
theorem B1768483 : Blo 814346 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B818211 : Blo 814346 818211 := bstep (se 1 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 818211 = 1227317) B1227317
theorem B818227 : Blo 814346 818227 := bstep (se 1 (by rfl) ⟨613670, by rfl⟩ : syracuseStep 818227 = 1227341) B1227341
theorem B25426997 : Blo 814346 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B818243 : Blo 814346 818243 := bstep (se 1 (by rfl) ⟨613682, by rfl⟩ : syracuseStep 818243 = 1227365) B1227365
theorem B2751569 : Blo 814346 2751569 := bstep (se 2 (by rfl) ⟨1031838, by rfl⟩ : syracuseStep 2751569 = 2063677) B2063677
theorem B818259 : Blo 814346 818259 := bstep (se 1 (by rfl) ⟨613694, by rfl⟩ : syracuseStep 818259 = 1227389) B1227389
theorem B818275 : Blo 814346 818275 := bstep (se 1 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 818275 = 1227413) B1227413
theorem B818291 : Blo 814346 818291 := bstep (se 1 (by rfl) ⟨613718, by rfl⟩ : syracuseStep 818291 = 1227437) B1227437
theorem B818307 : Blo 814346 818307 := bstep (se 1 (by rfl) ⟨613730, by rfl⟩ : syracuseStep 818307 = 1227461) B1227461
theorem B916627 : Blo 814346 916627 := bstep (se 1 (by rfl) ⟨687470, by rfl⟩ : syracuseStep 916627 = 1374941) B1374941
theorem B818323 : Blo 814346 818323 := bstep (se 1 (by rfl) ⟨613742, by rfl⟩ : syracuseStep 818323 = 1227485) B1227485
theorem B1375393 : Blo 814346 1375393 := bstep (se 2 (by rfl) ⟨515772, by rfl⟩ : syracuseStep 1375393 = 1031545) B1031545
theorem B818339 : Blo 814346 818339 := bstep (se 1 (by rfl) ⟨613754, by rfl⟩ : syracuseStep 818339 = 1227509) B1227509
theorem B4127921 : Blo 814346 4127921 := bstep (se 2 (by rfl) ⟨1547970, by rfl⟩ : syracuseStep 4127921 = 3095941) B3095941
theorem B1375427 : Blo 814346 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B2358467 : Blo 814346 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B1309907 : Blo 814346 1309907 := bstep (se 1 (by rfl) ⟨982430, by rfl⟩ : syracuseStep 1309907 = 1964861) B1964861
theorem B15924451 : Blo 814346 15924451 := bstep (se 1 (by rfl) ⟨11943338, by rfl⟩ : syracuseStep 15924451 = 23886677) B23886677
theorem B2325773 : Blo 814346 2325773 := bstep (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) B872165
theorem B916771 : Blo 814346 916771 := bstep (se 1 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 916771 = 1375157) B1375157
theorem B1834289 : Blo 814346 1834289 := bstep (se 2 (by rfl) ⟨687858, by rfl⟩ : syracuseStep 1834289 = 1375717) B1375717
theorem B1375555 : Blo 814346 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B1834307 : Blo 814346 1834307 := bstep (se 1 (by rfl) ⟨1375730, by rfl⟩ : syracuseStep 1834307 = 2751461) B2751461
theorem B1965379 : Blo 814346 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B4652387 : Blo 814346 4652387 := bstep (se 1 (by rfl) ⟨3489290, by rfl⟩ : syracuseStep 4652387 = 6978581) B6978581
theorem B1965475 : Blo 814346 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B916915 : Blo 814346 916915 := bstep (se 1 (by rfl) ⟨687686, by rfl⟩ : syracuseStep 916915 = 1375373) B1375373
theorem B2325955 : Blo 814346 2325955 := bstep (se 1 (by rfl) ⟨1744466, by rfl⟩ : syracuseStep 2325955 = 3488933) B3488933
theorem B1375697 : Blo 814346 1375697 := bstep (se 2 (by rfl) ⟨515886, by rfl⟩ : syracuseStep 1375697 = 1031773) B1031773
theorem B6192611 : Blo 814346 6192611 := bstep (se 1 (by rfl) ⟨4644458, by rfl⟩ : syracuseStep 6192611 = 9288917) B9288917
theorem B917059 : Blo 814346 917059 := bstep (se 1 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 917059 = 1375589) B1375589
theorem B5242445 : Blo 814346 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B1375825 : Blo 814346 1375825 := bstep (se 2 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 1375825 = 1031869) B1031869
theorem B1834577 : Blo 814346 1834577 := bstep (se 2 (by rfl) ⟨687966, by rfl⟩ : syracuseStep 1834577 = 1375933) B1375933
theorem B1834595 : Blo 814346 1834595 := bstep (se 1 (by rfl) ⟨1375946, by rfl⟩ : syracuseStep 1834595 = 2751893) B2751893
theorem B2752109 : Blo 814346 2752109 := bstep (se 3 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 2752109 = 1032041) B1032041
theorem B1375859 : Blo 814346 1375859 := bstep (se 1 (by rfl) ⟨1031894, by rfl⟩ : syracuseStep 1375859 = 2063789) B2063789
theorem B2621069 : Blo 814346 2621069 := bstep (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) B982901
theorem B2752163 : Blo 814346 2752163 := bstep (se 1 (by rfl) ⟨2064122, by rfl⟩ : syracuseStep 2752163 = 4128245) B4128245
theorem B917203 : Blo 814346 917203 := bstep (se 1 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 917203 = 1375805) B1375805
theorem B2064113 : Blo 814346 2064113 := bstep (se 2 (by rfl) ⟨774042, by rfl⟩ : syracuseStep 2064113 = 1548085) B1548085
theorem B1375987 : Blo 814346 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B2064163 : Blo 814346 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B917347 : Blo 814346 917347 := bstep (se 1 (by rfl) ⟨688010, by rfl⟩ : syracuseStep 917347 = 1376021) B1376021
theorem B1834865 : Blo 814346 1834865 := bstep (se 2 (by rfl) ⟨688074, by rfl⟩ : syracuseStep 1834865 = 1376149) B1376149
theorem B1376129 : Blo 814346 1376129 := bstep (se 2 (by rfl) ⟨516048, by rfl⟩ : syracuseStep 1376129 = 1032097) B1032097
theorem B1834883 : Blo 814346 1834883 := bstep (se 1 (by rfl) ⟨1376162, by rfl⟩ : syracuseStep 1834883 = 2752325) B2752325
theorem B1048483 : Blo 814346 1048483 := bstep (se 1 (by rfl) ⟨786362, by rfl⟩ : syracuseStep 1048483 = 1572725) B1572725
theorem B2326445 : Blo 814346 2326445 := bstep (se 3 (by rfl) ⟨436208, by rfl⟩ : syracuseStep 2326445 = 872417) B872417
theorem B2064305 : Blo 814346 2064305 := bstep (se 2 (by rfl) ⟨774114, by rfl⟩ : syracuseStep 2064305 = 1548229) B1548229
theorem B2752433 : Blo 814346 2752433 := bstep (se 2 (by rfl) ⟨1032162, by rfl⟩ : syracuseStep 2752433 = 2064325) B2064325
theorem B917491 : Blo 814346 917491 := bstep (se 1 (by rfl) ⟨688118, by rfl⟩ : syracuseStep 917491 = 1376237) B1376237
theorem B1835009 : Blo 814346 1835009 := bstep (se 2 (by rfl) ⟨688128, by rfl⟩ : syracuseStep 1835009 = 1376257) B1376257
theorem B917527 : Blo 814346 917527 := bstep (se 1 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 917527 = 1376291) B1376291
theorem B1376345 : Blo 814346 1376345 := bstep (se 2 (by rfl) ⟨516129, by rfl⟩ : syracuseStep 1376345 = 1032259) B1032259
theorem B5243059 : Blo 814346 5243059 := bstep (se 1 (by rfl) ⟨3932294, by rfl⟩ : syracuseStep 5243059 = 7864589) B7864589
theorem B917707 : Blo 814346 917707 := bstep (se 1 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 917707 = 1376561) B1376561
theorem B1835225 : Blo 814346 1835225 := bstep (se 2 (by rfl) ⟨688209, by rfl⟩ : syracuseStep 1835225 = 1376419) B1376419
theorem B1376473 : Blo 814346 1376473 := bstep (se 2 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 1376473 = 1032355) B1032355
theorem B9306413 : Blo 814346 9306413 := bstep (se 3 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 9306413 = 3489905) B3489905
theorem B1835315 : Blo 814346 1835315 := bstep (se 1 (by rfl) ⟨1376486, by rfl⟩ : syracuseStep 1835315 = 2752973) B2752973
theorem B917815 : Blo 814346 917815 := bstep (se 1 (by rfl) ⟨688361, by rfl⟩ : syracuseStep 917815 = 1376723) B1376723
theorem B10453313 : Blo 814346 10453313 := bstep (se 2 (by rfl) ⟨3919992, by rfl⟩ : syracuseStep 10453313 = 7839985) B7839985
theorem B1835351 : Blo 814346 1835351 := bstep (se 1 (by rfl) ⟨1376513, by rfl⟩ : syracuseStep 1835351 = 2753027) B2753027
theorem B2326877 : Blo 814346 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B17629589 : Blo 814346 17629589 := bstep (se 6 (by rfl) ⟨413193, by rfl⟩ : syracuseStep 17629589 = 826387) B826387
theorem B2752919 : Blo 814346 2752919 := bstep (se 1 (by rfl) ⟨2064689, by rfl⟩ : syracuseStep 2752919 = 4129379) B4129379
theorem B2064791 : Blo 814346 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B1573273 : Blo 814346 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B5898673 : Blo 814346 5898673 := bstep (se 2 (by rfl) ⟨2212002, by rfl⟩ : syracuseStep 5898673 = 4424005) B4424005
theorem B917995 : Blo 814346 917995 := bstep (se 1 (by rfl) ⟨688496, by rfl⟩ : syracuseStep 917995 = 1376993) B1376993
theorem B1835531 : Blo 814346 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B13238801 : Blo 814346 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B1835585 : Blo 814346 1835585 := bstep (se 2 (by rfl) ⟨688344, by rfl⟩ : syracuseStep 1835585 = 1376689) B1376689
theorem B2327105 : Blo 814346 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B918103 : Blo 814346 918103 := bstep (se 1 (by rfl) ⟨688577, by rfl⟩ : syracuseStep 918103 = 1377155) B1377155
theorem B1573463 : Blo 814346 1573463 := bstep (se 1 (by rfl) ⟨1180097, by rfl⟩ : syracuseStep 1573463 = 2360195) B2360195
theorem B1770113 : Blo 814346 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B6980357 : Blo 814346 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B918283 : Blo 814346 918283 := bstep (se 1 (by rfl) ⟨688712, by rfl⟩ : syracuseStep 918283 = 1377425) B1377425
theorem B1377047 : Blo 814346 1377047 := bstep (se 1 (by rfl) ⟨1032785, by rfl⟩ : syracuseStep 1377047 = 2065571) B2065571
theorem B1835801 : Blo 814346 1835801 := bstep (se 2 (by rfl) ⟨688425, by rfl⟩ : syracuseStep 1835801 = 1376851) B1376851
theorem B1835891 : Blo 814346 1835891 := bstep (se 1 (by rfl) ⟨1376918, by rfl⟩ : syracuseStep 1835891 = 2753837) B2753837
theorem B918391 : Blo 814346 918391 := bstep (se 1 (by rfl) ⟨688793, by rfl⟩ : syracuseStep 918391 = 1377587) B1377587
theorem B1835927 : Blo 814346 1835927 := bstep (se 1 (by rfl) ⟨1376945, by rfl⟩ : syracuseStep 1835927 = 2753891) B2753891
theorem B1377175 : Blo 814346 1377175 := bstep (se 1 (by rfl) ⟨1032881, by rfl⟩ : syracuseStep 1377175 = 2065763) B2065763
theorem B2327447 : Blo 814346 2327447 := bstep (se 1 (by rfl) ⟨1745585, by rfl⟩ : syracuseStep 2327447 = 3491171) B3491171
theorem B21201841 : Blo 814346 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B2753459 : Blo 814346 2753459 := bstep (se 1 (by rfl) ⟨2065094, by rfl⟩ : syracuseStep 2753459 = 4130189) B4130189
theorem B2261953 : Blo 814346 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B4654097 : Blo 814346 4654097 := bstep (se 2 (by rfl) ⟨1745286, by rfl⟩ : syracuseStep 4654097 = 3490573) B3490573
theorem B918571 : Blo 814346 918571 := bstep (se 1 (by rfl) ⟨688928, by rfl⟩ : syracuseStep 918571 = 1377857) B1377857
theorem B2065459 : Blo 814346 2065459 := bstep (se 1 (by rfl) ⟨1549094, by rfl⟩ : syracuseStep 2065459 = 3098189) B3098189
theorem B1836107 : Blo 814346 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B1836161 : Blo 814346 1836161 := bstep (se 2 (by rfl) ⟨688560, by rfl⟩ : syracuseStep 1836161 = 1377121) B1377121
theorem B918679 : Blo 814346 918679 := bstep (se 1 (by rfl) ⟨689009, by rfl⟩ : syracuseStep 918679 = 1378019) B1378019
theorem B3769523 : Blo 814346 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B2753729 : Blo 814346 2753729 := bstep (se 2 (by rfl) ⟨1032648, by rfl⟩ : syracuseStep 2753729 = 2065297) B2065297
theorem B2065601 : Blo 814346 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B918859 : Blo 814346 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B1836377 : Blo 814346 1836377 := bstep (se 2 (by rfl) ⟨688641, by rfl⟩ : syracuseStep 1836377 = 1377283) B1377283
theorem B56460685 : Blo 814346 56460685 := bstep (se 3 (by rfl) ⟨10586378, by rfl⟩ : syracuseStep 56460685 = 21172757) B21172757
theorem B1836467 : Blo 814346 1836467 := bstep (se 1 (by rfl) ⟨1377350, by rfl⟩ : syracuseStep 1836467 = 2754701) B2754701
theorem B918967 : Blo 814346 918967 := bstep (se 1 (by rfl) ⟨689225, by rfl⟩ : syracuseStep 918967 = 1378451) B1378451
theorem B1836503 : Blo 814346 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B1377803 : Blo 814346 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B919147 : Blo 814346 919147 := bstep (se 1 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 919147 = 1378721) B1378721
theorem B1836683 : Blo 814346 1836683 := bstep (se 1 (by rfl) ⟨1377512, by rfl⟩ : syracuseStep 1836683 = 2755025) B2755025
theorem B1377931 : Blo 814346 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B1836737 : Blo 814346 1836737 := bstep (se 2 (by rfl) ⟨688776, by rfl⟩ : syracuseStep 1836737 = 1377553) B1377553
theorem B919255 : Blo 814346 919255 := bstep (se 1 (by rfl) ⟨689441, by rfl⟩ : syracuseStep 919255 = 1378883) B1378883
theorem B2754269 : Blo 814346 2754269 := bstep (se 3 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 2754269 = 1032851) B1032851
theorem B1378073 : Blo 814346 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B9930613 : Blo 814346 9930613 := bstep (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) B930995
theorem B919435 : Blo 814346 919435 := bstep (se 1 (by rfl) ⟨689576, by rfl⟩ : syracuseStep 919435 = 1379153) B1379153
theorem B1836953 : Blo 814346 1836953 := bstep (se 2 (by rfl) ⟨688857, by rfl⟩ : syracuseStep 1836953 = 1377715) B1377715
theorem B1378201 : Blo 814346 1378201 := bstep (se 2 (by rfl) ⟨516825, by rfl⟩ : syracuseStep 1378201 = 1033651) B1033651
theorem B1837043 : Blo 814346 1837043 := bstep (se 1 (by rfl) ⟨1377782, by rfl⟩ : syracuseStep 1837043 = 2755565) B2755565
theorem B919543 : Blo 814346 919543 := bstep (se 1 (by rfl) ⟨689657, by rfl⟩ : syracuseStep 919543 = 1379315) B1379315
theorem B1837079 : Blo 814346 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B39651403 : Blo 814346 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B919723 : Blo 814346 919723 := bstep (se 1 (by rfl) ⟨689792, by rfl⟩ : syracuseStep 919723 = 1379585) B1379585
theorem B1837259 : Blo 814346 1837259 := bstep (se 1 (by rfl) ⟨1377944, by rfl⟩ : syracuseStep 1837259 = 2755889) B2755889
theorem B1837313 : Blo 814346 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B919831 : Blo 814346 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B2066867 : Blo 814346 2066867 := bstep (se 1 (by rfl) ⟨1550150, by rfl⟩ : syracuseStep 2066867 = 3100301) B3100301
theorem B920011 : Blo 814346 920011 := bstep (se 1 (by rfl) ⟨690008, by rfl⟩ : syracuseStep 920011 = 1380017) B1380017
theorem B1378775 : Blo 814346 1378775 := bstep (se 1 (by rfl) ⟨1034081, by rfl⟩ : syracuseStep 1378775 = 2068163) B2068163
theorem B1837529 : Blo 814346 1837529 := bstep (se 2 (by rfl) ⟨689073, by rfl⟩ : syracuseStep 1837529 = 1378147) B1378147
theorem B1739315 : Blo 814346 1739315 := bstep (se 1 (by rfl) ⟨1304486, by rfl⟩ : syracuseStep 1739315 = 2608973) B2608973
theorem B1837619 : Blo 814346 1837619 := bstep (se 1 (by rfl) ⟨1378214, by rfl⟩ : syracuseStep 1837619 = 2756429) B2756429
theorem B920119 : Blo 814346 920119 := bstep (se 1 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 920119 = 1380179) B1380179
theorem B5573195 : Blo 814346 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B1837655 : Blo 814346 1837655 := bstep (se 1 (by rfl) ⟨1378241, by rfl⟩ : syracuseStep 1837655 = 2756483) B2756483
theorem B1378903 : Blo 814346 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B920299 : Blo 814346 920299 := bstep (se 1 (by rfl) ⟨690224, by rfl⟩ : syracuseStep 920299 = 1380449) B1380449
theorem B1837835 : Blo 814346 1837835 := bstep (se 1 (by rfl) ⟨1378376, by rfl⟩ : syracuseStep 1837835 = 2756753) B2756753
theorem B6196013 : Blo 814346 6196013 := bstep (se 3 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 6196013 = 2323505) B2323505
theorem B1837889 : Blo 814346 1837889 := bstep (se 2 (by rfl) ⟨689208, by rfl⟩ : syracuseStep 1837889 = 1378417) B1378417
theorem B2755403 : Blo 814346 2755403 := bstep (se 1 (by rfl) ⟨2066552, by rfl⟩ : syracuseStep 2755403 = 4133105) B4133105
theorem B920407 : Blo 814346 920407 := bstep (se 1 (by rfl) ⟨690305, by rfl⟩ : syracuseStep 920407 = 1380611) B1380611
theorem B2067403 : Blo 814346 2067403 := bstep (se 1 (by rfl) ⟨1550552, by rfl⟩ : syracuseStep 2067403 = 3101105) B3101105
theorem B920587 : Blo 814346 920587 := bstep (se 1 (by rfl) ⟨690440, by rfl⟩ : syracuseStep 920587 = 1380881) B1380881
theorem B1838105 : Blo 814346 1838105 := bstep (se 2 (by rfl) ⟨689289, by rfl⟩ : syracuseStep 1838105 = 1378579) B1378579
theorem B1739827 : Blo 814346 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B2755673 : Blo 814346 2755673 := bstep (se 2 (by rfl) ⟨1033377, by rfl⟩ : syracuseStep 2755673 = 2066755) B2066755
theorem B2067545 : Blo 814346 2067545 := bstep (se 2 (by rfl) ⟨775329, by rfl⟩ : syracuseStep 2067545 = 1550659) B1550659
theorem B1838195 : Blo 814346 1838195 := bstep (se 1 (by rfl) ⟨1378646, by rfl⟩ : syracuseStep 1838195 = 2757293) B2757293
theorem B4131971 : Blo 814346 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B1838231 : Blo 814346 1838231 := bstep (se 1 (by rfl) ⟨1378673, by rfl⟩ : syracuseStep 1838231 = 2757347) B2757347
theorem B7179443 : Blo 814346 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B2329793 : Blo 814346 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B1379531 : Blo 814346 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1838411 : Blo 814346 1838411 := bstep (se 1 (by rfl) ⟨1378808, by rfl⟩ : syracuseStep 1838411 = 2757617) B2757617
theorem B1379659 : Blo 814346 1379659 := bstep (se 1 (by rfl) ⟨1034744, by rfl⟩ : syracuseStep 1379659 = 2069489) B2069489
theorem B1838465 : Blo 814346 1838465 := bstep (se 2 (by rfl) ⟨689424, by rfl⟩ : syracuseStep 1838465 = 1378849) B1378849
theorem B2788759 : Blo 814346 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B1510859 : Blo 814346 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1379801 : Blo 814346 1379801 := bstep (se 2 (by rfl) ⟨517425, by rfl⟩ : syracuseStep 1379801 = 1034851) B1034851
theorem B2788829 : Blo 814346 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B1838681 : Blo 814346 1838681 := bstep (se 2 (by rfl) ⟨689505, by rfl⟩ : syracuseStep 1838681 = 1379011) B1379011
theorem B1379929 : Blo 814346 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B1838771 : Blo 814346 1838771 := bstep (se 1 (by rfl) ⟨1379078, by rfl⟩ : syracuseStep 1838771 = 2758157) B2758157
theorem B2985665 : Blo 814346 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B1740503 : Blo 814346 1740503 := bstep (se 1 (by rfl) ⟨1305377, by rfl⟩ : syracuseStep 1740503 = 2610755) B2610755
theorem B1838807 : Blo 814346 1838807 := bstep (se 1 (by rfl) ⟨1379105, by rfl⟩ : syracuseStep 1838807 = 2758211) B2758211
theorem B2330329 : Blo 814346 2330329 := bstep (se 2 (by rfl) ⟨873873, by rfl⟩ : syracuseStep 2330329 = 1747747) B1747747
theorem B1740545 : Blo 814346 1740545 := bstep (se 2 (by rfl) ⟨652704, by rfl⟩ : syracuseStep 1740545 = 1305409) B1305409
theorem B2756375 : Blo 814346 2756375 := bstep (se 1 (by rfl) ⟨2067281, by rfl⟩ : syracuseStep 2756375 = 4134563) B4134563
theorem B1838987 : Blo 814346 1838987 := bstep (se 1 (by rfl) ⟨1379240, by rfl⟩ : syracuseStep 1838987 = 2758481) B2758481
theorem B2068375 : Blo 814346 2068375 := bstep (se 1 (by rfl) ⟨1551281, by rfl⟩ : syracuseStep 2068375 = 3102563) B3102563
theorem B1839041 : Blo 814346 1839041 := bstep (se 2 (by rfl) ⟨689640, by rfl⟩ : syracuseStep 1839041 = 1379281) B1379281
theorem B1380503 : Blo 814346 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B1839257 : Blo 814346 1839257 := bstep (se 2 (by rfl) ⟨689721, by rfl⟩ : syracuseStep 1839257 = 1379443) B1379443
theorem B1839347 : Blo 814346 1839347 := bstep (se 1 (by rfl) ⟨1379510, by rfl⟩ : syracuseStep 1839347 = 2759021) B2759021
theorem B1839383 : Blo 814346 1839383 := bstep (se 1 (by rfl) ⟨1379537, by rfl⟩ : syracuseStep 1839383 = 2759075) B2759075
theorem B1380631 : Blo 814346 1380631 := bstep (se 1 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 1380631 = 2070947) B2070947
theorem B6983981 : Blo 814346 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B2756915 : Blo 814346 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B2068811 : Blo 814346 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B1839563 : Blo 814346 1839563 := bstep (se 1 (by rfl) ⟨1379672, by rfl⟩ : syracuseStep 1839563 = 2759345) B2759345
theorem B1839617 : Blo 814346 1839617 := bstep (se 2 (by rfl) ⟨689856, by rfl⟩ : syracuseStep 1839617 = 1379713) B1379713
theorem B2757185 : Blo 814346 2757185 := bstep (se 2 (by rfl) ⟨1033944, by rfl⟩ : syracuseStep 2757185 = 2067889) B2067889
theorem B13931189 : Blo 814346 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B2069185 : Blo 814346 2069185 := bstep (se 2 (by rfl) ⟨775944, by rfl⟩ : syracuseStep 2069185 = 1551889) B1551889
theorem B1839833 : Blo 814346 1839833 := bstep (se 2 (by rfl) ⟨689937, by rfl⟩ : syracuseStep 1839833 = 1379875) B1379875
theorem B1839923 : Blo 814346 1839923 := bstep (se 1 (by rfl) ⟨1379942, by rfl⟩ : syracuseStep 1839923 = 2759885) B2759885
theorem B1839959 : Blo 814346 1839959 := bstep (se 1 (by rfl) ⟨1379969, by rfl⟩ : syracuseStep 1839959 = 2759939) B2759939
theorem B1840139 : Blo 814346 1840139 := bstep (se 1 (by rfl) ⟨1380104, by rfl⟩ : syracuseStep 1840139 = 2760209) B2760209
theorem B1840193 : Blo 814346 1840193 := bstep (se 2 (by rfl) ⟨690072, by rfl⟩ : syracuseStep 1840193 = 1380145) B1380145
theorem B2757725 : Blo 814346 2757725 := bstep (se 3 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 2757725 = 1034147) B1034147
theorem B2069783 : Blo 814346 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B1840409 : Blo 814346 1840409 := bstep (se 2 (by rfl) ⟨690153, by rfl⟩ : syracuseStep 1840409 = 1380307) B1380307
theorem B1840499 : Blo 814346 1840499 := bstep (se 1 (by rfl) ⟨1380374, by rfl⟩ : syracuseStep 1840499 = 2760749) B2760749
theorem B1840535 : Blo 814346 1840535 := bstep (se 1 (by rfl) ⟨1380401, by rfl⟩ : syracuseStep 1840535 = 2760803) B2760803
theorem B1840715 : Blo 814346 1840715 := bstep (se 1 (by rfl) ⟨1380536, by rfl⟩ : syracuseStep 1840715 = 2761073) B2761073
theorem B1840769 : Blo 814346 1840769 := bstep (se 2 (by rfl) ⟨690288, by rfl⟩ : syracuseStep 1840769 = 1380577) B1380577
theorem B2201267 : Blo 814346 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B1840985 : Blo 814346 1840985 := bstep (se 2 (by rfl) ⟨690369, by rfl⟩ : syracuseStep 1840985 = 1380739) B1380739
theorem B1841075 : Blo 814346 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1841111 : Blo 814346 1841111 := bstep (se 1 (by rfl) ⟨1380833, by rfl⟩ : syracuseStep 1841111 = 2761667) B2761667
theorem B2070593 : Blo 814346 2070593 := bstep (se 2 (by rfl) ⟨776472, by rfl⟩ : syracuseStep 2070593 = 1552945) B1552945
theorem B1546391 : Blo 814346 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B2758859 : Blo 814346 2758859 := bstep (se 1 (by rfl) ⟨2069144, by rfl⟩ : syracuseStep 2758859 = 4138289) B4138289
theorem B2759129 : Blo 814346 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B2202187 : Blo 814346 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B1743449 : Blo 814346 1743449 := bstep (se 2 (by rfl) ⟨653793, by rfl⟩ : syracuseStep 1743449 = 1307587) B1307587
theorem B2071129 : Blo 814346 2071129 := bstep (se 2 (by rfl) ⟨776673, by rfl⟩ : syracuseStep 2071129 = 1553347) B1553347
theorem B6199901 : Blo 814346 6199901 := bstep (se 3 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 6199901 = 2324963) B2324963
theorem B15702659 : Blo 814346 15702659 := bstep (se 1 (by rfl) ⟨11776994, by rfl⟩ : syracuseStep 15702659 = 23553989) B23553989
theorem B6986371 : Blo 814346 6986371 := bstep (se 1 (by rfl) ⟨5239778, by rfl⟩ : syracuseStep 6986371 = 10479557) B10479557
theorem B1546931 : Blo 814346 1546931 := bstep (se 1 (by rfl) ⟨1160198, by rfl⟩ : syracuseStep 1546931 = 2320397) B2320397
theorem B4659929 : Blo 814346 4659929 := bstep (se 2 (by rfl) ⟨1747473, by rfl⟩ : syracuseStep 4659929 = 3494947) B3494947
theorem B3480337 : Blo 814346 3480337 := bstep (se 2 (by rfl) ⟨1305126, by rfl⟩ : syracuseStep 3480337 = 2610253) B2610253
theorem B4135697 : Blo 814346 4135697 := bstep (se 2 (by rfl) ⟨1550886, by rfl⟩ : syracuseStep 4135697 = 3101773) B3101773
theorem B13966181 : Blo 814346 13966181 := bstep (se 4 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 13966181 = 2618659) B2618659
theorem B4135859 : Blo 814346 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B1743859 : Blo 814346 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B6626405 : Blo 814346 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B2759831 : Blo 814346 2759831 := bstep (se 1 (by rfl) ⟨2069873, by rfl⟩ : syracuseStep 2759831 = 4139747) B4139747
theorem B1547417 : Blo 814346 1547417 := bstep (se 2 (by rfl) ⟨580281, by rfl⟩ : syracuseStep 1547417 = 1160563) B1160563
theorem B1744193 : Blo 814346 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B2203031 : Blo 814346 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B6987329 : Blo 814346 6987329 := bstep (se 2 (by rfl) ⟨2620248, by rfl⟩ : syracuseStep 6987329 = 5240497) B5240497
theorem B2760371 : Blo 814346 2760371 := bstep (se 1 (by rfl) ⟨2070278, by rfl⟩ : syracuseStep 2760371 = 4140557) B4140557
theorem B2760641 : Blo 814346 2760641 := bstep (se 2 (by rfl) ⟨1035240, by rfl⟩ : syracuseStep 2760641 = 2070481) B2070481
theorem B1744919 : Blo 814346 1744919 := bstep (se 1 (by rfl) ⟨1308689, by rfl⟩ : syracuseStep 1744919 = 2617379) B2617379
theorem B12754979 : Blo 814346 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B5218661 : Blo 814346 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B827831 : Blo 814346 827831 := bstep (se 1 (by rfl) ⟨620873, by rfl⟩ : syracuseStep 827831 = 1241747) B1241747
theorem B2761181 : Blo 814346 2761181 := bstep (se 3 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 2761181 = 1035443) B1035443
theorem B1548875 : Blo 814346 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B1549057 : Blo 814346 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B4137803 : Blo 814346 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B1221527 : Blo 814346 1221527 := bstep (se 1 (by rfl) ⟨916145, by rfl⟩ : syracuseStep 1221527 = 1832291) B1832291
theorem B1221593 : Blo 814346 1221593 := bstep (se 2 (by rfl) ⟨458097, by rfl⟩ : syracuseStep 1221593 = 916195) B916195
theorem B828407 : Blo 814346 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B1221707 : Blo 814346 1221707 := bstep (se 1 (by rfl) ⟨916280, by rfl⟩ : syracuseStep 1221707 = 1832561) B1832561
theorem B1221719 : Blo 814346 1221719 := bstep (se 1 (by rfl) ⟨916289, by rfl⟩ : syracuseStep 1221719 = 1832579) B1832579
theorem B1221785 : Blo 814346 1221785 := bstep (se 2 (by rfl) ⟨458169, by rfl⟩ : syracuseStep 1221785 = 916339) B916339
theorem B1549505 : Blo 814346 1549505 := bstep (se 2 (by rfl) ⟨581064, by rfl⟩ : syracuseStep 1549505 = 1162129) B1162129
theorem B1221899 : Blo 814346 1221899 := bstep (se 1 (by rfl) ⟨916424, by rfl⟩ : syracuseStep 1221899 = 1832849) B1832849
theorem B1221911 : Blo 814346 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B1221977 : Blo 814346 1221977 := bstep (se 2 (by rfl) ⟨458241, by rfl⟩ : syracuseStep 1221977 = 916483) B916483
theorem B2205107 : Blo 814346 2205107 := bstep (se 1 (by rfl) ⟨1653830, by rfl⟩ : syracuseStep 2205107 = 3307661) B3307661
theorem B1222091 : Blo 814346 1222091 := bstep (se 1 (by rfl) ⟨916568, by rfl⟩ : syracuseStep 1222091 = 1833137) B1833137
theorem B1222103 : Blo 814346 1222103 := bstep (se 1 (by rfl) ⟨916577, by rfl⟩ : syracuseStep 1222103 = 1833155) B1833155
theorem B1549847 : Blo 814346 1549847 := bstep (se 1 (by rfl) ⟨1162385, by rfl⟩ : syracuseStep 1549847 = 2324771) B2324771
theorem B1222169 : Blo 814346 1222169 := bstep (se 2 (by rfl) ⟨458313, by rfl⟩ : syracuseStep 1222169 = 916627) B916627
theorem B1222283 : Blo 814346 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B1222295 : Blo 814346 1222295 := bstep (se 1 (by rfl) ⟨916721, by rfl⟩ : syracuseStep 1222295 = 1833443) B1833443
theorem B1222361 : Blo 814346 1222361 := bstep (se 2 (by rfl) ⟨458385, by rfl⟩ : syracuseStep 1222361 = 916771) B916771
theorem B2238173 : Blo 814346 2238173 := bstep (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) B839315
theorem B1222475 : Blo 814346 1222475 := bstep (se 1 (by rfl) ⟨916856, by rfl⟩ : syracuseStep 1222475 = 1833713) B1833713
theorem B1222487 : Blo 814346 1222487 := bstep (se 1 (by rfl) ⟨916865, by rfl⟩ : syracuseStep 1222487 = 1833731) B1833731
theorem B3483481 : Blo 814346 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B1222553 : Blo 814346 1222553 := bstep (se 2 (by rfl) ⟨458457, by rfl⟩ : syracuseStep 1222553 = 916915) B916915
theorem B1222667 : Blo 814346 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B1222679 : Blo 814346 1222679 := bstep (se 1 (by rfl) ⟨917009, by rfl⟩ : syracuseStep 1222679 = 1834019) B1834019
theorem B16951331 : Blo 814346 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B1222745 : Blo 814346 1222745 := bstep (se 2 (by rfl) ⟨458529, by rfl⟩ : syracuseStep 1222745 = 917059) B917059
theorem B1550515 : Blo 814346 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B1222859 : Blo 814346 1222859 := bstep (se 1 (by rfl) ⟨917144, by rfl⟩ : syracuseStep 1222859 = 1834289) B1834289
theorem B1222871 : Blo 814346 1222871 := bstep (se 1 (by rfl) ⟨917153, by rfl⟩ : syracuseStep 1222871 = 1834307) B1834307
theorem B1222937 : Blo 814346 1222937 := bstep (se 2 (by rfl) ⟨458601, by rfl⟩ : syracuseStep 1222937 = 917203) B917203
theorem B1223051 : Blo 814346 1223051 := bstep (se 1 (by rfl) ⟨917288, by rfl⟩ : syracuseStep 1223051 = 1834577) B1834577
theorem B1223063 : Blo 814346 1223063 := bstep (se 1 (by rfl) ⟨917297, by rfl⟩ : syracuseStep 1223063 = 1834595) B1834595
theorem B1747379 : Blo 814346 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B3484097 : Blo 814346 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B5876185 : Blo 814346 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B1223129 : Blo 814346 1223129 := bstep (se 2 (by rfl) ⟨458673, by rfl⟩ : syracuseStep 1223129 = 917347) B917347
theorem B4139585 : Blo 814346 4139585 := bstep (se 2 (by rfl) ⟨1552344, by rfl⟩ : syracuseStep 4139585 = 3104689) B3104689
theorem B1223243 : Blo 814346 1223243 := bstep (se 1 (by rfl) ⟨917432, by rfl⟩ : syracuseStep 1223243 = 1834865) B1834865
theorem B1223255 : Blo 814346 1223255 := bstep (se 1 (by rfl) ⟨917441, by rfl⟩ : syracuseStep 1223255 = 1834883) B1834883
theorem B1550963 : Blo 814346 1550963 := bstep (se 1 (by rfl) ⟨1163222, by rfl⟩ : syracuseStep 1550963 = 2326445) B2326445
theorem B1223321 : Blo 814346 1223321 := bstep (se 2 (by rfl) ⟨458745, by rfl⟩ : syracuseStep 1223321 = 917491) B917491
theorem B1551001 : Blo 814346 1551001 := bstep (se 2 (by rfl) ⟨581625, by rfl⟩ : syracuseStep 1551001 = 1163251) B1163251
theorem B1223435 : Blo 814346 1223435 := bstep (se 1 (by rfl) ⟨917576, by rfl⟩ : syracuseStep 1223435 = 1835153) B1835153
theorem B1223447 : Blo 814346 1223447 := bstep (se 1 (by rfl) ⟨917585, by rfl⟩ : syracuseStep 1223447 = 1835171) B1835171
theorem B1223513 : Blo 814346 1223513 := bstep (se 2 (by rfl) ⟨458817, by rfl⟩ : syracuseStep 1223513 = 917635) B917635
theorem B1223627 : Blo 814346 1223627 := bstep (se 1 (by rfl) ⟨917720, by rfl⟩ : syracuseStep 1223627 = 1835441) B1835441
theorem B3779531 : Blo 814346 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B1223639 : Blo 814346 1223639 := bstep (se 1 (by rfl) ⟨917729, by rfl⟩ : syracuseStep 1223639 = 1835459) B1835459
theorem B1223705 : Blo 814346 1223705 := bstep (se 2 (by rfl) ⟨458889, by rfl⟩ : syracuseStep 1223705 = 917779) B917779
theorem B1551449 : Blo 814346 1551449 := bstep (se 2 (by rfl) ⟨581793, by rfl⟩ : syracuseStep 1551449 = 1163587) B1163587
theorem B1223819 : Blo 814346 1223819 := bstep (se 1 (by rfl) ⟨917864, by rfl⟩ : syracuseStep 1223819 = 1835729) B1835729
theorem B1223831 : Blo 814346 1223831 := bstep (se 1 (by rfl) ⟨917873, by rfl⟩ : syracuseStep 1223831 = 1835747) B1835747
theorem B1223897 : Blo 814346 1223897 := bstep (se 2 (by rfl) ⟨458961, by rfl⟩ : syracuseStep 1223897 = 917923) B917923
theorem B1224011 : Blo 814346 1224011 := bstep (se 1 (by rfl) ⟨918008, by rfl⟩ : syracuseStep 1224011 = 1836017) B1836017
theorem B1224023 : Blo 814346 1224023 := bstep (se 1 (by rfl) ⟨918017, by rfl⟩ : syracuseStep 1224023 = 1836035) B1836035
theorem B6958487 : Blo 814346 6958487 := bstep (se 1 (by rfl) ⟨5218865, by rfl⟩ : syracuseStep 6958487 = 10437731) B10437731
theorem B1224089 : Blo 814346 1224089 := bstep (se 2 (by rfl) ⟨459033, by rfl⟩ : syracuseStep 1224089 = 918067) B918067
theorem B1224203 : Blo 814346 1224203 := bstep (se 1 (by rfl) ⟨918152, by rfl⟩ : syracuseStep 1224203 = 1836305) B1836305
theorem B1224215 : Blo 814346 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B1224281 : Blo 814346 1224281 := bstep (se 2 (by rfl) ⟨459105, by rfl⟩ : syracuseStep 1224281 = 918211) B918211
theorem B929431 : Blo 814346 929431 := bstep (se 1 (by rfl) ⟨697073, by rfl⟩ : syracuseStep 929431 = 1394147) B1394147
theorem B1224395 : Blo 814346 1224395 := bstep (se 1 (by rfl) ⟨918296, by rfl⟩ : syracuseStep 1224395 = 1836593) B1836593
theorem B1224407 : Blo 814346 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B1224473 : Blo 814346 1224473 := bstep (se 2 (by rfl) ⟨459177, by rfl⟩ : syracuseStep 1224473 = 918355) B918355
theorem B1552193 : Blo 814346 1552193 := bstep (se 2 (by rfl) ⟨582072, by rfl⟩ : syracuseStep 1552193 = 1164145) B1164145
theorem B4960075 : Blo 814346 4960075 := bstep (se 1 (by rfl) ⟨3720056, by rfl⟩ : syracuseStep 4960075 = 7440113) B7440113
theorem B5975939 : Blo 814346 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B1224587 : Blo 814346 1224587 := bstep (se 1 (by rfl) ⟨918440, by rfl⟩ : syracuseStep 1224587 = 1836881) B1836881
theorem B1224599 : Blo 814346 1224599 := bstep (se 1 (by rfl) ⟨918449, by rfl⟩ : syracuseStep 1224599 = 1836899) B1836899
theorem B1224665 : Blo 814346 1224665 := bstep (se 2 (by rfl) ⟨459249, by rfl⟩ : syracuseStep 1224665 = 918499) B918499
theorem B11907107 : Blo 814346 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B3092525 : Blo 814346 3092525 := bstep (se 3 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 3092525 = 1159697) B1159697
theorem B1224779 : Blo 814346 1224779 := bstep (se 1 (by rfl) ⟨918584, by rfl⟩ : syracuseStep 1224779 = 1837169) B1837169
theorem B1552459 : Blo 814346 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1224791 : Blo 814346 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B1224857 : Blo 814346 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B1224971 : Blo 814346 1224971 := bstep (se 1 (by rfl) ⟨918728, by rfl⟩ : syracuseStep 1224971 = 1837457) B1837457
theorem B1224983 : Blo 814346 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B2797847 : Blo 814346 2797847 := bstep (se 1 (by rfl) ⟨2098385, by rfl⟩ : syracuseStep 2797847 = 4196771) B4196771
theorem B1225049 : Blo 814346 1225049 := bstep (se 2 (by rfl) ⟨459393, by rfl⟩ : syracuseStep 1225049 = 918787) B918787
theorem B1225163 : Blo 814346 1225163 := bstep (se 1 (by rfl) ⟨918872, by rfl⟩ : syracuseStep 1225163 = 1837745) B1837745
theorem B1225175 : Blo 814346 1225175 := bstep (se 1 (by rfl) ⟨918881, by rfl⟩ : syracuseStep 1225175 = 1837763) B1837763
theorem B4141529 : Blo 814346 4141529 := bstep (se 2 (by rfl) ⟨1553073, by rfl⟩ : syracuseStep 4141529 = 3106147) B3106147
theorem B1552907 : Blo 814346 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1225241 : Blo 814346 1225241 := bstep (se 2 (by rfl) ⟨459465, by rfl⟩ : syracuseStep 1225241 = 918931) B918931
theorem B1225355 : Blo 814346 1225355 := bstep (se 1 (by rfl) ⟨919016, by rfl⟩ : syracuseStep 1225355 = 1838033) B1838033
theorem B1225367 : Blo 814346 1225367 := bstep (se 1 (by rfl) ⟨919025, by rfl⟩ : syracuseStep 1225367 = 1838051) B1838051
theorem B1553089 : Blo 814346 1553089 := bstep (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) B1164817
theorem B1225433 : Blo 814346 1225433 := bstep (se 2 (by rfl) ⟨459537, by rfl⟩ : syracuseStep 1225433 = 919075) B919075
theorem B3093299 : Blo 814346 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B1225547 : Blo 814346 1225547 := bstep (se 1 (by rfl) ⟨919160, by rfl⟩ : syracuseStep 1225547 = 1838321) B1838321
theorem B1225559 : Blo 814346 1225559 := bstep (se 1 (by rfl) ⟨919169, by rfl⟩ : syracuseStep 1225559 = 1838339) B1838339
theorem B3486557 : Blo 814346 3486557 := bstep (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) B1307459
theorem B1225625 : Blo 814346 1225625 := bstep (se 2 (by rfl) ⟨459609, by rfl⟩ : syracuseStep 1225625 = 919219) B919219
theorem B1225739 : Blo 814346 1225739 := bstep (se 1 (by rfl) ⟨919304, by rfl⟩ : syracuseStep 1225739 = 1838609) B1838609
theorem B1225751 : Blo 814346 1225751 := bstep (se 1 (by rfl) ⟨919313, by rfl⟩ : syracuseStep 1225751 = 1838627) B1838627
theorem B1553431 : Blo 814346 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B1225817 : Blo 814346 1225817 := bstep (se 2 (by rfl) ⟨459681, by rfl⟩ : syracuseStep 1225817 = 919363) B919363
theorem B10466435 : Blo 814346 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B1225931 : Blo 814346 1225931 := bstep (se 1 (by rfl) ⟨919448, by rfl⟩ : syracuseStep 1225931 = 1838897) B1838897
theorem B1225943 : Blo 814346 1225943 := bstep (se 1 (by rfl) ⟨919457, by rfl⟩ : syracuseStep 1225943 = 1838915) B1838915
theorem B6960401 : Blo 814346 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1226009 : Blo 814346 1226009 := bstep (se 2 (by rfl) ⟨459753, by rfl⟩ : syracuseStep 1226009 = 919507) B919507
theorem B4404611 : Blo 814346 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B1226123 : Blo 814346 1226123 := bstep (se 1 (by rfl) ⟨919592, by rfl⟩ : syracuseStep 1226123 = 1839185) B1839185
theorem B1226135 : Blo 814346 1226135 := bstep (se 1 (by rfl) ⟨919601, by rfl⟩ : syracuseStep 1226135 = 1839203) B1839203
theorem B1226201 : Blo 814346 1226201 := bstep (se 2 (by rfl) ⟨459825, by rfl⟩ : syracuseStep 1226201 = 919651) B919651
theorem B1226315 : Blo 814346 1226315 := bstep (se 1 (by rfl) ⟨919736, by rfl⟩ : syracuseStep 1226315 = 1839473) B1839473
theorem B1226327 : Blo 814346 1226327 := bstep (se 1 (by rfl) ⟨919745, by rfl⟩ : syracuseStep 1226327 = 1839491) B1839491
theorem B1226393 : Blo 814346 1226393 := bstep (se 2 (by rfl) ⟨459897, by rfl⟩ : syracuseStep 1226393 = 919795) B919795
theorem B1226507 : Blo 814346 1226507 := bstep (se 1 (by rfl) ⟨919880, by rfl⟩ : syracuseStep 1226507 = 1839761) B1839761
theorem B1226519 : Blo 814346 1226519 := bstep (se 1 (by rfl) ⟨919889, by rfl⟩ : syracuseStep 1226519 = 1839779) B1839779
theorem B1226585 : Blo 814346 1226585 := bstep (se 2 (by rfl) ⟨459969, by rfl⟩ : syracuseStep 1226585 = 919939) B919939
theorem B59488177 : Blo 814346 59488177 := bstep (se 2 (by rfl) ⟨22308066, by rfl⟩ : syracuseStep 59488177 = 44616133) B44616133
theorem B1226699 : Blo 814346 1226699 := bstep (se 1 (by rfl) ⟨920024, by rfl⟩ : syracuseStep 1226699 = 1840049) B1840049
theorem B1226711 : Blo 814346 1226711 := bstep (se 1 (by rfl) ⟨920033, by rfl⟩ : syracuseStep 1226711 = 1840067) B1840067
theorem B12564497 : Blo 814346 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B1226777 : Blo 814346 1226777 := bstep (se 2 (by rfl) ⟨460041, by rfl⟩ : syracuseStep 1226777 = 920083) B920083
theorem B15677509 : Blo 814346 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B1226891 : Blo 814346 1226891 := bstep (se 1 (by rfl) ⟨920168, by rfl⟩ : syracuseStep 1226891 = 1840337) B1840337
theorem B1226903 : Blo 814346 1226903 := bstep (se 1 (by rfl) ⟨920177, by rfl⟩ : syracuseStep 1226903 = 1840355) B1840355
theorem B1226969 : Blo 814346 1226969 := bstep (se 2 (by rfl) ⟨460113, by rfl⟩ : syracuseStep 1226969 = 920227) B920227
theorem B3094787 : Blo 814346 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B1227083 : Blo 814346 1227083 := bstep (se 1 (by rfl) ⟨920312, by rfl⟩ : syracuseStep 1227083 = 1840625) B1840625
theorem B1227095 : Blo 814346 1227095 := bstep (se 1 (by rfl) ⟨920321, by rfl⟩ : syracuseStep 1227095 = 1840643) B1840643
theorem B1227161 : Blo 814346 1227161 := bstep (se 2 (by rfl) ⟨460185, by rfl⟩ : syracuseStep 1227161 = 920371) B920371
theorem B1227275 : Blo 814346 1227275 := bstep (se 1 (by rfl) ⟨920456, by rfl⟩ : syracuseStep 1227275 = 1840913) B1840913
theorem B1227287 : Blo 814346 1227287 := bstep (se 1 (by rfl) ⟨920465, by rfl⟩ : syracuseStep 1227287 = 1840931) B1840931
theorem B1227353 : Blo 814346 1227353 := bstep (se 2 (by rfl) ⟨460257, by rfl⟩ : syracuseStep 1227353 = 920515) B920515
theorem B5880451 : Blo 814346 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B3095243 : Blo 814346 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B1227467 : Blo 814346 1227467 := bstep (se 1 (by rfl) ⟨920600, by rfl⟩ : syracuseStep 1227467 = 1841201) B1841201
theorem B1227479 : Blo 814346 1227479 := bstep (se 1 (by rfl) ⟨920609, by rfl⟩ : syracuseStep 1227479 = 1841219) B1841219
theorem B3095441 : Blo 814346 3095441 := bstep (se 2 (by rfl) ⟨1160790, by rfl⟩ : syracuseStep 3095441 = 2321581) B2321581
theorem B1031383 : Blo 814346 1031383 := bstep (se 1 (by rfl) ⟨773537, by rfl⟩ : syracuseStep 1031383 = 1547075) B1547075
theorem B3489155 : Blo 814346 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B3096215 : Blo 814346 3096215 := bstep (se 1 (by rfl) ⟨2322161, by rfl⟩ : syracuseStep 3096215 = 4644323) B4644323
theorem B4964141 : Blo 814346 4964141 := bstep (se 3 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 4964141 = 1861553) B1861553
theorem B3096413 : Blo 814346 3096413 := bstep (se 3 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 3096413 = 1161155) B1161155
theorem B8044505 : Blo 814346 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B1032203 : Blo 814346 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B10469411 : Blo 814346 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B6635621 : Blo 814346 6635621 := bstep (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) B1244179
theorem B8372429 : Blo 814346 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B1163479 : Blo 814346 1163479 := bstep (se 1 (by rfl) ⟨872609, by rfl⟩ : syracuseStep 1163479 = 1745219) B1745219
theorem B6636077 : Blo 814346 6636077 := bstep (se 3 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 6636077 = 2488529) B2488529
theorem B1032907 : Blo 814346 1032907 := bstep (se 1 (by rfl) ⟨774680, by rfl⟩ : syracuseStep 1032907 = 1549361) B1549361
theorem B4965137 : Blo 814346 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B6800203 : Blo 814346 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B1033175 : Blo 814346 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B1033879 : Blo 814346 1033879 := bstep (se 1 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 1033879 = 1550819) B1550819
theorem B870059 : Blo 814346 870059 := bstep (se 1 (by rfl) ⟨652544, by rfl⟩ : syracuseStep 870059 = 1305089) B1305089
theorem B4474547 : Blo 814346 4474547 := bstep (se 1 (by rfl) ⟨3355910, by rfl⟩ : syracuseStep 4474547 = 6711821) B6711821
theorem B3491531 : Blo 814346 3491531 := bstep (se 1 (by rfl) ⟨2618648, by rfl⟩ : syracuseStep 3491531 = 5237297) B5237297
theorem B3098371 : Blo 814346 3098371 := bstep (se 1 (by rfl) ⟨2323778, by rfl⟩ : syracuseStep 3098371 = 4647557) B4647557
theorem B870187 : Blo 814346 870187 := bstep (se 1 (by rfl) ⟨652640, by rfl⟩ : syracuseStep 870187 = 1305281) B1305281
theorem B837527 : Blo 814346 837527 := bstep (se 1 (by rfl) ⟨628145, by rfl⟩ : syracuseStep 837527 = 1256291) B1256291
theorem B1394585 : Blo 814346 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B3098675 : Blo 814346 3098675 := bstep (se 1 (by rfl) ⟨2324006, by rfl⟩ : syracuseStep 3098675 = 4648013) B4648013
theorem B7850135 : Blo 814346 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B3721409 : Blo 814346 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1657025 : Blo 814346 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B5884433 : Blo 814346 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B1395289 : Blo 814346 1395289 := bstep (se 2 (by rfl) ⟨523233, by rfl⟩ : syracuseStep 1395289 = 1046467) B1046467
theorem B3492503 : Blo 814346 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B3099329 : Blo 814346 3099329 := bstep (se 2 (by rfl) ⟨1162248, by rfl⟩ : syracuseStep 3099329 = 2324497) B2324497
theorem B63720245 : Blo 814346 63720245 := bstep (se 5 (by rfl) ⟨2986886, by rfl⟩ : syracuseStep 63720245 = 5973773) B5973773
theorem B7457629 : Blo 814346 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B1657739 : Blo 814346 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B11160611 : Blo 814346 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B5229785 : Blo 814346 5229785 := bstep (se 2 (by rfl) ⟨1961169, by rfl⟩ : syracuseStep 5229785 = 3922339) B3922339
theorem B1035595 : Blo 814346 1035595 := bstep (se 1 (by rfl) ⟨776696, by rfl⟩ : syracuseStep 1035595 = 1553393) B1553393
theorem B4771685 : Blo 814346 4771685 := bstep (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) B894691
theorem B3100589 : Blo 814346 3100589 := bstep (se 3 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 3100589 = 1162721) B1162721
theorem B19812275 : Blo 814346 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B3100619 : Blo 814346 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B1396939 : Blo 814346 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B2609587 : Blo 814346 2609587 := bstep (se 1 (by rfl) ⟨1957190, by rfl⟩ : syracuseStep 2609587 = 3914381) B3914381
theorem B6279697 : Blo 814346 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B2609729 : Blo 814346 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B3101273 : Blo 814346 3101273 := bstep (se 2 (by rfl) ⟨1162977, by rfl⟩ : syracuseStep 3101273 = 2325955) B2325955
theorem B873271 : Blo 814346 873271 := bstep (se 1 (by rfl) ⟨654953, by rfl⟩ : syracuseStep 873271 = 1309907) B1309907
theorem B5231425 : Blo 814346 5231425 := bstep (se 2 (by rfl) ⟨1961784, by rfl⟩ : syracuseStep 5231425 = 3923569) B3923569
theorem B5591909 : Blo 814346 5591909 := bstep (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) B1048483
theorem B3101591 : Blo 814346 3101591 := bstep (se 1 (by rfl) ⟨2326193, by rfl⟩ : syracuseStep 3101591 = 4652387) B4652387
theorem B3494963 : Blo 814346 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B1398169 : Blo 814346 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B1103321 : Blo 814346 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B3102259 : Blo 814346 3102259 := bstep (se 1 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 3102259 = 4653389) B4653389
theorem B18143075 : Blo 814346 18143075 := bstep (se 1 (by rfl) ⟨13607306, by rfl⟩ : syracuseStep 18143075 = 27214613) B27214613
theorem B2480321 : Blo 814346 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B5527939 : Blo 814346 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B19847693 : Blo 814346 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B12114613 : Blo 814346 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B2939651 : Blo 814346 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B1858315 : Blo 814346 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B3103505 : Blo 814346 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B5299019 : Blo 814346 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B2612189 : Blo 814346 2612189 := bstep (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) B979571
theorem B6610193 : Blo 814346 6610193 := bstep (se 2 (by rfl) ⟨2478822, by rfl⟩ : syracuseStep 6610193 = 4957645) B4957645
theorem B3104203 : Blo 814346 3104203 := bstep (se 1 (by rfl) ⟨2328152, by rfl⟩ : syracuseStep 3104203 = 4656305) B4656305
theorem B53632469 : Blo 814346 53632469 := bstep (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) B1257011
theorem B3923417 : Blo 814346 3923417 := bstep (se 2 (by rfl) ⟨1471281, by rfl⟩ : syracuseStep 3923417 = 2942563) B2942563
theorem B1105483 : Blo 814346 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B3104477 : Blo 814346 3104477 := bstep (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) B1164179
theorem B26828597 : Blo 814346 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B6184835 : Blo 814346 6184835 := bstep (se 1 (by rfl) ⟨4638626, by rfl⟩ : syracuseStep 6184835 = 9277253) B9277253
theorem B11952197 : Blo 814346 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B909515 : Blo 814346 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B6971609 : Blo 814346 6971609 := bstep (se 2 (by rfl) ⟨2614353, by rfl⟩ : syracuseStep 6971609 = 5228707) B5228707
theorem B3105175 : Blo 814346 3105175 := bstep (se 1 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 3105175 = 4657763) B4657763
theorem B1860121 : Blo 814346 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B7856675 : Blo 814346 7856675 := bstep (se 1 (by rfl) ⟨5892506, by rfl⟩ : syracuseStep 7856675 = 11785013) B11785013
theorem B2319155 : Blo 814346 2319155 := bstep (se 1 (by rfl) ⟨1739366, by rfl⟩ : syracuseStep 2319155 = 3478733) B3478733
theorem B3105965 : Blo 814346 3105965 := bstep (se 3 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 3105965 = 1164737) B1164737
theorem B5661875 : Blo 814346 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B1959191 : Blo 814346 1959191 := bstep (se 1 (by rfl) ⟨1469393, by rfl⟩ : syracuseStep 1959191 = 2938787) B2938787
theorem B1795649 : Blo 814346 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B1861271 : Blo 814346 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B6973249 : Blo 814346 6973249 := bstep (se 2 (by rfl) ⟨2614968, by rfl⟩ : syracuseStep 6973249 = 5229937) B5229937
theorem B4646807 : Blo 814346 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B1959959 : Blo 814346 1959959 := bstep (se 1 (by rfl) ⟨1469969, by rfl⟩ : syracuseStep 1959959 = 2939939) B2939939
theorem B13953059 : Blo 814346 13953059 := bstep (se 1 (by rfl) ⟨10464794, by rfl⟩ : syracuseStep 13953059 = 20929589) B20929589
theorem B6383717 : Blo 814346 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B1469249 : Blo 814346 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B2321227 : Blo 814346 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B9431909 : Blo 814346 9431909 := bstep (se 4 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 9431909 = 1768483) B1768483
theorem B2943917 : Blo 814346 2943917 := bstep (se 3 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 2943917 = 1103969) B1103969
theorem B6188237 : Blo 814346 6188237 := bstep (se 3 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 6188237 = 2320589) B2320589
theorem B7433477 : Blo 814346 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B814347 : Blo 814346 814347 := bstep (se 1 (by rfl) ⟨610760, by rfl⟩ : syracuseStep 814347 = 1221521) B1221521
theorem B814359 : Blo 814346 814359 := bstep (se 1 (by rfl) ⟨610769, by rfl⟩ : syracuseStep 814359 = 1221539) B1221539
theorem B814379 : Blo 814346 814379 := bstep (se 1 (by rfl) ⟨610784, by rfl⟩ : syracuseStep 814379 = 1221569) B1221569
theorem B814391 : Blo 814346 814391 := bstep (se 1 (by rfl) ⟨610793, by rfl⟩ : syracuseStep 814391 = 1221587) B1221587
theorem B2321729 : Blo 814346 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B814411 : Blo 814346 814411 := bstep (se 1 (by rfl) ⟨610808, by rfl⟩ : syracuseStep 814411 = 1221617) B1221617
theorem B814423 : Blo 814346 814423 := bstep (se 1 (by rfl) ⟨610817, by rfl⟩ : syracuseStep 814423 = 1221635) B1221635
theorem B814443 : Blo 814346 814443 := bstep (se 1 (by rfl) ⟨610832, by rfl⟩ : syracuseStep 814443 = 1221665) B1221665
theorem B814455 : Blo 814346 814455 := bstep (se 1 (by rfl) ⟨610841, by rfl⟩ : syracuseStep 814455 = 1221683) B1221683
theorem B814475 : Blo 814346 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B814487 : Blo 814346 814487 := bstep (se 1 (by rfl) ⟨610865, by rfl⟩ : syracuseStep 814487 = 1221731) B1221731
theorem B814507 : Blo 814346 814507 := bstep (se 1 (by rfl) ⟨610880, by rfl⟩ : syracuseStep 814507 = 1221761) B1221761
theorem B814519 : Blo 814346 814519 := bstep (se 1 (by rfl) ⟨610889, by rfl⟩ : syracuseStep 814519 = 1221779) B1221779
theorem B814539 : Blo 814346 814539 := bstep (se 1 (by rfl) ⟨610904, by rfl⟩ : syracuseStep 814539 = 1221809) B1221809
theorem B814551 : Blo 814346 814551 := bstep (se 1 (by rfl) ⟨610913, by rfl⟩ : syracuseStep 814551 = 1221827) B1221827
theorem B814571 : Blo 814346 814571 := bstep (se 1 (by rfl) ⟨610928, by rfl⟩ : syracuseStep 814571 = 1221857) B1221857
theorem B814583 : Blo 814346 814583 := bstep (se 1 (by rfl) ⟨610937, by rfl⟩ : syracuseStep 814583 = 1221875) B1221875
theorem B814603 : Blo 814346 814603 := bstep (se 1 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 814603 = 1221905) B1221905
theorem B814615 : Blo 814346 814615 := bstep (se 1 (by rfl) ⟨610961, by rfl⟩ : syracuseStep 814615 = 1221923) B1221923
theorem B814635 : Blo 814346 814635 := bstep (se 1 (by rfl) ⟨610976, by rfl⟩ : syracuseStep 814635 = 1221953) B1221953
theorem B814647 : Blo 814346 814647 := bstep (se 1 (by rfl) ⟨610985, by rfl⟩ : syracuseStep 814647 = 1221971) B1221971
theorem B814667 : Blo 814346 814667 := bstep (se 1 (by rfl) ⟨611000, by rfl⟩ : syracuseStep 814667 = 1222001) B1222001
theorem B814679 : Blo 814346 814679 := bstep (se 1 (by rfl) ⟨611009, by rfl⟩ : syracuseStep 814679 = 1222019) B1222019
theorem B814699 : Blo 814346 814699 := bstep (se 1 (by rfl) ⟨611024, by rfl⟩ : syracuseStep 814699 = 1222049) B1222049
theorem B814711 : Blo 814346 814711 := bstep (se 1 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 814711 = 1222067) B1222067
theorem B814731 : Blo 814346 814731 := bstep (se 1 (by rfl) ⟨611048, by rfl⟩ : syracuseStep 814731 = 1222097) B1222097
theorem B814743 : Blo 814346 814743 := bstep (se 1 (by rfl) ⟨611057, by rfl⟩ : syracuseStep 814743 = 1222115) B1222115
theorem B2322071 : Blo 814346 2322071 := bstep (se 1 (by rfl) ⟨1741553, by rfl⟩ : syracuseStep 2322071 = 3483107) B3483107
theorem B814763 : Blo 814346 814763 := bstep (se 1 (by rfl) ⟨611072, by rfl⟩ : syracuseStep 814763 = 1222145) B1222145
theorem B6188723 : Blo 814346 6188723 := bstep (se 1 (by rfl) ⟨4641542, by rfl⟩ : syracuseStep 6188723 = 9283085) B9283085
theorem B1961651 : Blo 814346 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B814775 : Blo 814346 814775 := bstep (se 1 (by rfl) ⟨611081, by rfl⟩ : syracuseStep 814775 = 1222163) B1222163
theorem B814795 : Blo 814346 814795 := bstep (se 1 (by rfl) ⟨611096, by rfl⟩ : syracuseStep 814795 = 1222193) B1222193
theorem B814807 : Blo 814346 814807 := bstep (se 1 (by rfl) ⟨611105, by rfl⟩ : syracuseStep 814807 = 1222211) B1222211
theorem B814827 : Blo 814346 814827 := bstep (se 1 (by rfl) ⟨611120, by rfl⟩ : syracuseStep 814827 = 1222241) B1222241
theorem B814839 : Blo 814346 814839 := bstep (se 1 (by rfl) ⟨611129, by rfl⟩ : syracuseStep 814839 = 1222259) B1222259
theorem B814859 : Blo 814346 814859 := bstep (se 1 (by rfl) ⟨611144, by rfl⟩ : syracuseStep 814859 = 1222289) B1222289
theorem B814871 : Blo 814346 814871 := bstep (se 1 (by rfl) ⟨611153, by rfl⟩ : syracuseStep 814871 = 1222307) B1222307
theorem B814891 : Blo 814346 814891 := bstep (se 1 (by rfl) ⟨611168, by rfl⟩ : syracuseStep 814891 = 1222337) B1222337
theorem B814903 : Blo 814346 814903 := bstep (se 1 (by rfl) ⟨611177, by rfl⟩ : syracuseStep 814903 = 1222355) B1222355
theorem B814923 : Blo 814346 814923 := bstep (se 1 (by rfl) ⟨611192, by rfl⟩ : syracuseStep 814923 = 1222385) B1222385
theorem B814935 : Blo 814346 814935 := bstep (se 1 (by rfl) ⟨611201, by rfl⟩ : syracuseStep 814935 = 1222403) B1222403
theorem B814955 : Blo 814346 814955 := bstep (se 1 (by rfl) ⟨611216, by rfl⟩ : syracuseStep 814955 = 1222433) B1222433
theorem B814967 : Blo 814346 814967 := bstep (se 1 (by rfl) ⟨611225, by rfl⟩ : syracuseStep 814967 = 1222451) B1222451
theorem B814987 : Blo 814346 814987 := bstep (se 1 (by rfl) ⟨611240, by rfl⟩ : syracuseStep 814987 = 1222481) B1222481
theorem B814999 : Blo 814346 814999 := bstep (se 1 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 814999 = 1222499) B1222499
theorem B1470359 : Blo 814346 1470359 := bstep (se 1 (by rfl) ⟨1102769, by rfl⟩ : syracuseStep 1470359 = 2205539) B2205539
theorem B815019 : Blo 814346 815019 := bstep (se 1 (by rfl) ⟨611264, by rfl⟩ : syracuseStep 815019 = 1222529) B1222529
theorem B815031 : Blo 814346 815031 := bstep (se 1 (by rfl) ⟨611273, by rfl⟩ : syracuseStep 815031 = 1222547) B1222547
theorem B815051 : Blo 814346 815051 := bstep (se 1 (by rfl) ⟨611288, by rfl⟩ : syracuseStep 815051 = 1222577) B1222577
theorem B815063 : Blo 814346 815063 := bstep (se 1 (by rfl) ⟨611297, by rfl⟩ : syracuseStep 815063 = 1222595) B1222595
theorem B815083 : Blo 814346 815083 := bstep (se 1 (by rfl) ⟨611312, by rfl⟩ : syracuseStep 815083 = 1222625) B1222625
theorem B815095 : Blo 814346 815095 := bstep (se 1 (by rfl) ⟨611321, by rfl⟩ : syracuseStep 815095 = 1222643) B1222643
theorem B815115 : Blo 814346 815115 := bstep (se 1 (by rfl) ⟨611336, by rfl⟩ : syracuseStep 815115 = 1222673) B1222673
theorem B815127 : Blo 814346 815127 := bstep (se 1 (by rfl) ⟨611345, by rfl⟩ : syracuseStep 815127 = 1222691) B1222691
theorem B815147 : Blo 814346 815147 := bstep (se 1 (by rfl) ⟨611360, by rfl⟩ : syracuseStep 815147 = 1222721) B1222721
theorem B815159 : Blo 814346 815159 := bstep (se 1 (by rfl) ⟨611369, by rfl⟩ : syracuseStep 815159 = 1222739) B1222739
theorem B2748491 : Blo 814346 2748491 := bstep (se 1 (by rfl) ⟨2061368, by rfl⟩ : syracuseStep 2748491 = 4122737) B4122737
theorem B815179 : Blo 814346 815179 := bstep (se 1 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 815179 = 1222769) B1222769
theorem B815191 : Blo 814346 815191 := bstep (se 1 (by rfl) ⟨611393, by rfl⟩ : syracuseStep 815191 = 1222787) B1222787
theorem B1962073 : Blo 814346 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B815211 : Blo 814346 815211 := bstep (se 1 (by rfl) ⟨611408, by rfl⟩ : syracuseStep 815211 = 1222817) B1222817
theorem B815223 : Blo 814346 815223 := bstep (se 1 (by rfl) ⟨611417, by rfl⟩ : syracuseStep 815223 = 1222835) B1222835
theorem B815243 : Blo 814346 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B815255 : Blo 814346 815255 := bstep (se 1 (by rfl) ⟨611441, by rfl⟩ : syracuseStep 815255 = 1222883) B1222883
theorem B815275 : Blo 814346 815275 := bstep (se 1 (by rfl) ⟨611456, by rfl⟩ : syracuseStep 815275 = 1222913) B1222913
theorem B815287 : Blo 814346 815287 := bstep (se 1 (by rfl) ⟨611465, by rfl⟩ : syracuseStep 815287 = 1222931) B1222931
theorem B815307 : Blo 814346 815307 := bstep (se 1 (by rfl) ⟨611480, by rfl⟩ : syracuseStep 815307 = 1222961) B1222961
theorem B815319 : Blo 814346 815319 := bstep (se 1 (by rfl) ⟨611489, by rfl⟩ : syracuseStep 815319 = 1222979) B1222979
theorem B815339 : Blo 814346 815339 := bstep (se 1 (by rfl) ⟨611504, by rfl⟩ : syracuseStep 815339 = 1223009) B1223009
theorem B815351 : Blo 814346 815351 := bstep (se 1 (by rfl) ⟨611513, by rfl⟩ : syracuseStep 815351 = 1223027) B1223027
theorem B815371 : Blo 814346 815371 := bstep (se 1 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 815371 = 1223057) B1223057
theorem B815383 : Blo 814346 815383 := bstep (se 1 (by rfl) ⟨611537, by rfl⟩ : syracuseStep 815383 = 1223075) B1223075
theorem B815403 : Blo 814346 815403 := bstep (se 1 (by rfl) ⟨611552, by rfl⟩ : syracuseStep 815403 = 1223105) B1223105
theorem B815415 : Blo 814346 815415 := bstep (se 1 (by rfl) ⟨611561, by rfl⟩ : syracuseStep 815415 = 1223123) B1223123
theorem B815435 : Blo 814346 815435 := bstep (se 1 (by rfl) ⟨611576, by rfl⟩ : syracuseStep 815435 = 1223153) B1223153
theorem B815447 : Blo 814346 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B2748761 : Blo 814346 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B815467 : Blo 814346 815467 := bstep (se 1 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 815467 = 1223201) B1223201
theorem B815479 : Blo 814346 815479 := bstep (se 1 (by rfl) ⟨611609, by rfl⟩ : syracuseStep 815479 = 1223219) B1223219
theorem B815499 : Blo 814346 815499 := bstep (se 1 (by rfl) ⟨611624, by rfl⟩ : syracuseStep 815499 = 1223249) B1223249
theorem B3305873 : Blo 814346 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B815511 : Blo 814346 815511 := bstep (se 1 (by rfl) ⟨611633, by rfl⟩ : syracuseStep 815511 = 1223267) B1223267
theorem B815531 : Blo 814346 815531 := bstep (se 1 (by rfl) ⟨611648, by rfl⟩ : syracuseStep 815531 = 1223297) B1223297
theorem B815543 : Blo 814346 815543 := bstep (se 1 (by rfl) ⟨611657, by rfl⟩ : syracuseStep 815543 = 1223315) B1223315
theorem B815563 : Blo 814346 815563 := bstep (se 1 (by rfl) ⟨611672, by rfl⟩ : syracuseStep 815563 = 1223345) B1223345
theorem B815575 : Blo 814346 815575 := bstep (se 1 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 815575 = 1223363) B1223363
theorem B815595 : Blo 814346 815595 := bstep (se 1 (by rfl) ⟨611696, by rfl⟩ : syracuseStep 815595 = 1223393) B1223393
theorem B815607 : Blo 814346 815607 := bstep (se 1 (by rfl) ⟨611705, by rfl⟩ : syracuseStep 815607 = 1223411) B1223411
theorem B815627 : Blo 814346 815627 := bstep (se 1 (by rfl) ⟨611720, by rfl⟩ : syracuseStep 815627 = 1223441) B1223441
theorem B815639 : Blo 814346 815639 := bstep (se 1 (by rfl) ⟨611729, by rfl⟩ : syracuseStep 815639 = 1223459) B1223459
theorem B815659 : Blo 814346 815659 := bstep (se 1 (by rfl) ⟨611744, by rfl⟩ : syracuseStep 815659 = 1223489) B1223489
theorem B815671 : Blo 814346 815671 := bstep (se 1 (by rfl) ⟨611753, by rfl⟩ : syracuseStep 815671 = 1223507) B1223507
theorem B815691 : Blo 814346 815691 := bstep (se 1 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 815691 = 1223537) B1223537
theorem B815703 : Blo 814346 815703 := bstep (se 1 (by rfl) ⟨611777, by rfl⟩ : syracuseStep 815703 = 1223555) B1223555
theorem B815723 : Blo 814346 815723 := bstep (se 1 (by rfl) ⟨611792, by rfl⟩ : syracuseStep 815723 = 1223585) B1223585
theorem B815735 : Blo 814346 815735 := bstep (se 1 (by rfl) ⟨611801, by rfl⟩ : syracuseStep 815735 = 1223603) B1223603
theorem B815755 : Blo 814346 815755 := bstep (se 1 (by rfl) ⟨611816, by rfl⟩ : syracuseStep 815755 = 1223633) B1223633
theorem B815767 : Blo 814346 815767 := bstep (se 1 (by rfl) ⟨611825, by rfl⟩ : syracuseStep 815767 = 1223651) B1223651
theorem B815787 : Blo 814346 815787 := bstep (se 1 (by rfl) ⟨611840, by rfl⟩ : syracuseStep 815787 = 1223681) B1223681
theorem B815799 : Blo 814346 815799 := bstep (se 1 (by rfl) ⟨611849, by rfl⟩ : syracuseStep 815799 = 1223699) B1223699
theorem B815819 : Blo 814346 815819 := bstep (se 1 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 815819 = 1223729) B1223729
theorem B815831 : Blo 814346 815831 := bstep (se 1 (by rfl) ⟨611873, by rfl⟩ : syracuseStep 815831 = 1223747) B1223747
theorem B1274585 : Blo 814346 1274585 := bstep (se 2 (by rfl) ⟨477969, by rfl⟩ : syracuseStep 1274585 = 955939) B955939
theorem B815851 : Blo 814346 815851 := bstep (se 1 (by rfl) ⟨611888, by rfl⟩ : syracuseStep 815851 = 1223777) B1223777
theorem B815863 : Blo 814346 815863 := bstep (se 1 (by rfl) ⟨611897, by rfl⟩ : syracuseStep 815863 = 1223795) B1223795
theorem B11760389 : Blo 814346 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B815883 : Blo 814346 815883 := bstep (se 1 (by rfl) ⟨611912, by rfl⟩ : syracuseStep 815883 = 1223825) B1223825
theorem B815895 : Blo 814346 815895 := bstep (se 1 (by rfl) ⟨611921, by rfl⟩ : syracuseStep 815895 = 1223843) B1223843
theorem B815915 : Blo 814346 815915 := bstep (se 1 (by rfl) ⟨611936, by rfl⟩ : syracuseStep 815915 = 1223873) B1223873
theorem B5894957 : Blo 814346 5894957 := bstep (se 3 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 5894957 = 2210609) B2210609
theorem B815927 : Blo 814346 815927 := bstep (se 1 (by rfl) ⟨611945, by rfl⟩ : syracuseStep 815927 = 1223891) B1223891
theorem B815947 : Blo 814346 815947 := bstep (se 1 (by rfl) ⟨611960, by rfl⟩ : syracuseStep 815947 = 1223921) B1223921
theorem B815959 : Blo 814346 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B10482533 : Blo 814346 10482533 := bstep (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) B1965475
theorem B815979 : Blo 814346 815979 := bstep (se 1 (by rfl) ⟨611984, by rfl⟩ : syracuseStep 815979 = 1223969) B1223969
theorem B815991 : Blo 814346 815991 := bstep (se 1 (by rfl) ⟨611993, by rfl⟩ : syracuseStep 815991 = 1223987) B1223987
theorem B816011 : Blo 814346 816011 := bstep (se 1 (by rfl) ⟨612008, by rfl⟩ : syracuseStep 816011 = 1224017) B1224017
theorem B816023 : Blo 814346 816023 := bstep (se 1 (by rfl) ⟨612017, by rfl⟩ : syracuseStep 816023 = 1224035) B1224035
theorem B816043 : Blo 814346 816043 := bstep (se 1 (by rfl) ⟨612032, by rfl⟩ : syracuseStep 816043 = 1224065) B1224065
theorem B7861171 : Blo 814346 7861171 := bstep (se 1 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 7861171 = 11791757) B11791757
theorem B816055 : Blo 814346 816055 := bstep (se 1 (by rfl) ⟨612041, by rfl⟩ : syracuseStep 816055 = 1224083) B1224083
theorem B816075 : Blo 814346 816075 := bstep (se 1 (by rfl) ⟨612056, by rfl⟩ : syracuseStep 816075 = 1224113) B1224113
theorem B816087 : Blo 814346 816087 := bstep (se 1 (by rfl) ⟨612065, by rfl⟩ : syracuseStep 816087 = 1224131) B1224131
theorem B816107 : Blo 814346 816107 := bstep (se 1 (by rfl) ⟨612080, by rfl⟩ : syracuseStep 816107 = 1224161) B1224161
theorem B816119 : Blo 814346 816119 := bstep (se 1 (by rfl) ⟨612089, by rfl⟩ : syracuseStep 816119 = 1224179) B1224179
theorem B816139 : Blo 814346 816139 := bstep (se 1 (by rfl) ⟨612104, by rfl⟩ : syracuseStep 816139 = 1224209) B1224209
theorem B2749463 : Blo 814346 2749463 := bstep (se 1 (by rfl) ⟨2062097, by rfl⟩ : syracuseStep 2749463 = 4124195) B4124195
theorem B816151 : Blo 814346 816151 := bstep (se 1 (by rfl) ⟨612113, by rfl⟩ : syracuseStep 816151 = 1224227) B1224227
theorem B816171 : Blo 814346 816171 := bstep (se 1 (by rfl) ⟨612128, by rfl⟩ : syracuseStep 816171 = 1224257) B1224257
theorem B816183 : Blo 814346 816183 := bstep (se 1 (by rfl) ⟨612137, by rfl⟩ : syracuseStep 816183 = 1224275) B1224275
theorem B816203 : Blo 814346 816203 := bstep (se 1 (by rfl) ⟨612152, by rfl⟩ : syracuseStep 816203 = 1224305) B1224305
theorem B816215 : Blo 814346 816215 := bstep (se 1 (by rfl) ⟨612161, by rfl⟩ : syracuseStep 816215 = 1224323) B1224323
theorem B6190181 : Blo 814346 6190181 := bstep (se 4 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 6190181 = 1160659) B1160659
theorem B816235 : Blo 814346 816235 := bstep (se 1 (by rfl) ⟨612176, by rfl⟩ : syracuseStep 816235 = 1224353) B1224353
theorem B816247 : Blo 814346 816247 := bstep (se 1 (by rfl) ⟨612185, by rfl⟩ : syracuseStep 816247 = 1224371) B1224371
theorem B816267 : Blo 814346 816267 := bstep (se 1 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 816267 = 1224401) B1224401
theorem B816279 : Blo 814346 816279 := bstep (se 1 (by rfl) ⟨612209, by rfl⟩ : syracuseStep 816279 = 1224419) B1224419
theorem B816299 : Blo 814346 816299 := bstep (se 1 (by rfl) ⟨612224, by rfl⟩ : syracuseStep 816299 = 1224449) B1224449
theorem B816311 : Blo 814346 816311 := bstep (se 1 (by rfl) ⟨612233, by rfl⟩ : syracuseStep 816311 = 1224467) B1224467
theorem B816331 : Blo 814346 816331 := bstep (se 1 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 816331 = 1224497) B1224497
theorem B816343 : Blo 814346 816343 := bstep (se 1 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 816343 = 1224515) B1224515
theorem B816363 : Blo 814346 816363 := bstep (se 1 (by rfl) ⟨612272, by rfl⟩ : syracuseStep 816363 = 1224545) B1224545
theorem B816375 : Blo 814346 816375 := bstep (se 1 (by rfl) ⟨612281, by rfl⟩ : syracuseStep 816375 = 1224563) B1224563
theorem B816395 : Blo 814346 816395 := bstep (se 1 (by rfl) ⟨612296, by rfl⟩ : syracuseStep 816395 = 1224593) B1224593
theorem B816407 : Blo 814346 816407 := bstep (se 1 (by rfl) ⟨612305, by rfl⟩ : syracuseStep 816407 = 1224611) B1224611
theorem B816427 : Blo 814346 816427 := bstep (se 1 (by rfl) ⟨612320, by rfl⟩ : syracuseStep 816427 = 1224641) B1224641
theorem B816439 : Blo 814346 816439 := bstep (se 1 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 816439 = 1224659) B1224659
theorem B816459 : Blo 814346 816459 := bstep (se 1 (by rfl) ⟨612344, by rfl⟩ : syracuseStep 816459 = 1224689) B1224689
theorem B816471 : Blo 814346 816471 := bstep (se 1 (by rfl) ⟨612353, by rfl⟩ : syracuseStep 816471 = 1224707) B1224707
theorem B816491 : Blo 814346 816491 := bstep (se 1 (by rfl) ⟨612368, by rfl⟩ : syracuseStep 816491 = 1224737) B1224737
theorem B816503 : Blo 814346 816503 := bstep (se 1 (by rfl) ⟨612377, by rfl⟩ : syracuseStep 816503 = 1224755) B1224755
theorem B816523 : Blo 814346 816523 := bstep (se 1 (by rfl) ⟨612392, by rfl⟩ : syracuseStep 816523 = 1224785) B1224785
theorem B816535 : Blo 814346 816535 := bstep (se 1 (by rfl) ⟨612401, by rfl⟩ : syracuseStep 816535 = 1224803) B1224803
theorem B2946455 : Blo 814346 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B1832345 : Blo 814346 1832345 := bstep (se 2 (by rfl) ⟨687129, by rfl⟩ : syracuseStep 1832345 = 1374259) B1374259
theorem B816555 : Blo 814346 816555 := bstep (se 1 (by rfl) ⟨612416, by rfl⟩ : syracuseStep 816555 = 1224833) B1224833
theorem B7828913 : Blo 814346 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B816567 : Blo 814346 816567 := bstep (se 1 (by rfl) ⟨612425, by rfl⟩ : syracuseStep 816567 = 1224851) B1224851
theorem B1963457 : Blo 814346 1963457 := bstep (se 2 (by rfl) ⟨736296, by rfl⟩ : syracuseStep 1963457 = 1472593) B1472593
theorem B816587 : Blo 814346 816587 := bstep (se 1 (by rfl) ⟨612440, by rfl⟩ : syracuseStep 816587 = 1224881) B1224881
theorem B816599 : Blo 814346 816599 := bstep (se 1 (by rfl) ⟨612449, by rfl⟩ : syracuseStep 816599 = 1224899) B1224899
theorem B816619 : Blo 814346 816619 := bstep (se 1 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 816619 = 1224929) B1224929
theorem B1832435 : Blo 814346 1832435 := bstep (se 1 (by rfl) ⟨1374326, by rfl⟩ : syracuseStep 1832435 = 2748653) B2748653
theorem B816631 : Blo 814346 816631 := bstep (se 1 (by rfl) ⟨612473, by rfl⟩ : syracuseStep 816631 = 1224947) B1224947
theorem B816651 : Blo 814346 816651 := bstep (se 1 (by rfl) ⟨612488, by rfl⟩ : syracuseStep 816651 = 1224977) B1224977
theorem B1832471 : Blo 814346 1832471 := bstep (se 1 (by rfl) ⟨1374353, by rfl⟩ : syracuseStep 1832471 = 2748707) B2748707
theorem B816663 : Blo 814346 816663 := bstep (se 1 (by rfl) ⟨612497, by rfl⟩ : syracuseStep 816663 = 1224995) B1224995
theorem B816683 : Blo 814346 816683 := bstep (se 1 (by rfl) ⟨612512, by rfl⟩ : syracuseStep 816683 = 1225025) B1225025
theorem B2061875 : Blo 814346 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B2750003 : Blo 814346 2750003 := bstep (se 1 (by rfl) ⟨2062502, by rfl⟩ : syracuseStep 2750003 = 4125005) B4125005
theorem B816695 : Blo 814346 816695 := bstep (se 1 (by rfl) ⟨612521, by rfl⟩ : syracuseStep 816695 = 1225043) B1225043
theorem B6190667 : Blo 814346 6190667 := bstep (se 1 (by rfl) ⟨4643000, by rfl⟩ : syracuseStep 6190667 = 9286001) B9286001
theorem B816715 : Blo 814346 816715 := bstep (se 1 (by rfl) ⟨612536, by rfl⟩ : syracuseStep 816715 = 1225073) B1225073
theorem B816727 : Blo 814346 816727 := bstep (se 1 (by rfl) ⟨612545, by rfl⟩ : syracuseStep 816727 = 1225091) B1225091
theorem B4126301 : Blo 814346 4126301 := bstep (se 3 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 4126301 = 1547363) B1547363
theorem B2651741 : Blo 814346 2651741 := bstep (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) B994403
theorem B816747 : Blo 814346 816747 := bstep (se 1 (by rfl) ⟨612560, by rfl⟩ : syracuseStep 816747 = 1225121) B1225121
theorem B816759 : Blo 814346 816759 := bstep (se 1 (by rfl) ⟨612569, by rfl⟩ : syracuseStep 816759 = 1225139) B1225139
theorem B816779 : Blo 814346 816779 := bstep (se 1 (by rfl) ⟨612584, by rfl⟩ : syracuseStep 816779 = 1225169) B1225169
theorem B816791 : Blo 814346 816791 := bstep (se 1 (by rfl) ⟨612593, by rfl⟩ : syracuseStep 816791 = 1225187) B1225187
theorem B816811 : Blo 814346 816811 := bstep (se 1 (by rfl) ⟨612608, by rfl⟩ : syracuseStep 816811 = 1225217) B1225217
theorem B816823 : Blo 814346 816823 := bstep (se 1 (by rfl) ⟨612617, by rfl⟩ : syracuseStep 816823 = 1225235) B1225235
theorem B1832651 : Blo 814346 1832651 := bstep (se 1 (by rfl) ⟨1374488, by rfl⟩ : syracuseStep 1832651 = 2748977) B2748977
theorem B816843 : Blo 814346 816843 := bstep (se 1 (by rfl) ⟨612632, by rfl⟩ : syracuseStep 816843 = 1225265) B1225265
theorem B816855 : Blo 814346 816855 := bstep (se 1 (by rfl) ⟨612641, by rfl⟩ : syracuseStep 816855 = 1225283) B1225283
theorem B2324189 : Blo 814346 2324189 := bstep (se 3 (by rfl) ⟨435785, by rfl⟩ : syracuseStep 2324189 = 871571) B871571
theorem B816875 : Blo 814346 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B816887 : Blo 814346 816887 := bstep (se 1 (by rfl) ⟨612665, by rfl⟩ : syracuseStep 816887 = 1225331) B1225331
theorem B1832705 : Blo 814346 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B816907 : Blo 814346 816907 := bstep (se 1 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 816907 = 1225361) B1225361
theorem B816919 : Blo 814346 816919 := bstep (se 1 (by rfl) ⟨612689, by rfl⟩ : syracuseStep 816919 = 1225379) B1225379
theorem B816939 : Blo 814346 816939 := bstep (se 1 (by rfl) ⟨612704, by rfl⟩ : syracuseStep 816939 = 1225409) B1225409
theorem B816951 : Blo 814346 816951 := bstep (se 1 (by rfl) ⟨612713, by rfl⟩ : syracuseStep 816951 = 1225427) B1225427
theorem B2750273 : Blo 814346 2750273 := bstep (se 2 (by rfl) ⟨1031352, by rfl⟩ : syracuseStep 2750273 = 2062705) B2062705
theorem B816971 : Blo 814346 816971 := bstep (se 1 (by rfl) ⟨612728, by rfl⟩ : syracuseStep 816971 = 1225457) B1225457
theorem B816983 : Blo 814346 816983 := bstep (se 1 (by rfl) ⟨612737, by rfl⟩ : syracuseStep 816983 = 1225475) B1225475
theorem B2062169 : Blo 814346 2062169 := bstep (se 2 (by rfl) ⟨773313, by rfl⟩ : syracuseStep 2062169 = 1546627) B1546627
theorem B817003 : Blo 814346 817003 := bstep (se 1 (by rfl) ⟨612752, by rfl⟩ : syracuseStep 817003 = 1225505) B1225505
theorem B817015 : Blo 814346 817015 := bstep (se 1 (by rfl) ⟨612761, by rfl⟩ : syracuseStep 817015 = 1225523) B1225523
theorem B817035 : Blo 814346 817035 := bstep (se 1 (by rfl) ⟨612776, by rfl⟩ : syracuseStep 817035 = 1225553) B1225553
theorem B817047 : Blo 814346 817047 := bstep (se 1 (by rfl) ⟨612785, by rfl⟩ : syracuseStep 817047 = 1225571) B1225571
theorem B817067 : Blo 814346 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B817079 : Blo 814346 817079 := bstep (se 1 (by rfl) ⟨612809, by rfl⟩ : syracuseStep 817079 = 1225619) B1225619
theorem B817099 : Blo 814346 817099 := bstep (se 1 (by rfl) ⟨612824, by rfl⟩ : syracuseStep 817099 = 1225649) B1225649
theorem B817111 : Blo 814346 817111 := bstep (se 1 (by rfl) ⟨612833, by rfl⟩ : syracuseStep 817111 = 1225667) B1225667
theorem B1832921 : Blo 814346 1832921 := bstep (se 2 (by rfl) ⟨687345, by rfl⟩ : syracuseStep 1832921 = 1374691) B1374691
theorem B817131 : Blo 814346 817131 := bstep (se 1 (by rfl) ⟨612848, by rfl⟩ : syracuseStep 817131 = 1225697) B1225697
theorem B817143 : Blo 814346 817143 := bstep (se 1 (by rfl) ⟨612857, by rfl⟩ : syracuseStep 817143 = 1225715) B1225715
theorem B817163 : Blo 814346 817163 := bstep (se 1 (by rfl) ⟨612872, by rfl⟩ : syracuseStep 817163 = 1225745) B1225745
theorem B817175 : Blo 814346 817175 := bstep (se 1 (by rfl) ⟨612881, by rfl⟩ : syracuseStep 817175 = 1225763) B1225763
theorem B817195 : Blo 814346 817195 := bstep (se 1 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 817195 = 1225793) B1225793
theorem B1833011 : Blo 814346 1833011 := bstep (se 1 (by rfl) ⟨1374758, by rfl⟩ : syracuseStep 1833011 = 2749517) B2749517
theorem B2324531 : Blo 814346 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B817207 : Blo 814346 817207 := bstep (se 1 (by rfl) ⟨612905, by rfl⟩ : syracuseStep 817207 = 1225811) B1225811
theorem B817227 : Blo 814346 817227 := bstep (se 1 (by rfl) ⟨612920, by rfl⟩ : syracuseStep 817227 = 1225841) B1225841
theorem B1833047 : Blo 814346 1833047 := bstep (se 1 (by rfl) ⟨1374785, by rfl⟩ : syracuseStep 1833047 = 2749571) B2749571
theorem B817239 : Blo 814346 817239 := bstep (se 1 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 817239 = 1225859) B1225859
theorem B817259 : Blo 814346 817259 := bstep (se 1 (by rfl) ⟨612944, by rfl⟩ : syracuseStep 817259 = 1225889) B1225889
theorem B817271 : Blo 814346 817271 := bstep (se 1 (by rfl) ⟨612953, by rfl⟩ : syracuseStep 817271 = 1225907) B1225907
theorem B1374347 : Blo 814346 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B1472651 : Blo 814346 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B817291 : Blo 814346 817291 := bstep (se 1 (by rfl) ⟨612968, by rfl⟩ : syracuseStep 817291 = 1225937) B1225937
theorem B11303063 : Blo 814346 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B817303 : Blo 814346 817303 := bstep (se 1 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 817303 = 1225955) B1225955
theorem B817323 : Blo 814346 817323 := bstep (se 1 (by rfl) ⟨612992, by rfl⟩ : syracuseStep 817323 = 1225985) B1225985
theorem B817335 : Blo 814346 817335 := bstep (se 1 (by rfl) ⟨613001, by rfl⟩ : syracuseStep 817335 = 1226003) B1226003
theorem B817355 : Blo 814346 817355 := bstep (se 1 (by rfl) ⟨613016, by rfl⟩ : syracuseStep 817355 = 1226033) B1226033
theorem B817367 : Blo 814346 817367 := bstep (se 1 (by rfl) ⟨613025, by rfl⟩ : syracuseStep 817367 = 1226051) B1226051
theorem B817387 : Blo 814346 817387 := bstep (se 1 (by rfl) ⟨613040, by rfl⟩ : syracuseStep 817387 = 1226081) B1226081
theorem B817399 : Blo 814346 817399 := bstep (se 1 (by rfl) ⟨613049, by rfl⟩ : syracuseStep 817399 = 1226099) B1226099
theorem B1374475 : Blo 814346 1374475 := bstep (se 1 (by rfl) ⟨1030856, by rfl⟩ : syracuseStep 1374475 = 2061713) B2061713
theorem B1833227 : Blo 814346 1833227 := bstep (se 1 (by rfl) ⟨1374920, by rfl⟩ : syracuseStep 1833227 = 2749841) B2749841
theorem B817419 : Blo 814346 817419 := bstep (se 1 (by rfl) ⟨613064, by rfl⟩ : syracuseStep 817419 = 1226129) B1226129
theorem B817431 : Blo 814346 817431 := bstep (se 1 (by rfl) ⟨613073, by rfl⟩ : syracuseStep 817431 = 1226147) B1226147
theorem B1866007 : Blo 814346 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B817451 : Blo 814346 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B817463 : Blo 814346 817463 := bstep (se 1 (by rfl) ⟨613097, by rfl⟩ : syracuseStep 817463 = 1226195) B1226195
theorem B1833281 : Blo 814346 1833281 := bstep (se 2 (by rfl) ⟨687480, by rfl⟩ : syracuseStep 1833281 = 1374961) B1374961
theorem B817483 : Blo 814346 817483 := bstep (se 1 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 817483 = 1226225) B1226225
theorem B817495 : Blo 814346 817495 := bstep (se 1 (by rfl) ⟨613121, by rfl⟩ : syracuseStep 817495 = 1226243) B1226243
theorem B2750813 : Blo 814346 2750813 := bstep (se 3 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 2750813 = 1031555) B1031555
theorem B817515 : Blo 814346 817515 := bstep (se 1 (by rfl) ⟨613136, by rfl⟩ : syracuseStep 817515 = 1226273) B1226273
theorem B817527 : Blo 814346 817527 := bstep (se 1 (by rfl) ⟨613145, by rfl⟩ : syracuseStep 817527 = 1226291) B1226291
theorem B817547 : Blo 814346 817547 := bstep (se 1 (by rfl) ⟨613160, by rfl⟩ : syracuseStep 817547 = 1226321) B1226321
theorem B817559 : Blo 814346 817559 := bstep (se 1 (by rfl) ⟨613169, by rfl⟩ : syracuseStep 817559 = 1226339) B1226339
theorem B1374617 : Blo 814346 1374617 := bstep (se 2 (by rfl) ⟨515481, by rfl⟩ : syracuseStep 1374617 = 1030963) B1030963
theorem B817579 : Blo 814346 817579 := bstep (se 1 (by rfl) ⟨613184, by rfl⟩ : syracuseStep 817579 = 1226369) B1226369
theorem B817591 : Blo 814346 817591 := bstep (se 1 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 817591 = 1226387) B1226387
theorem B817611 : Blo 814346 817611 := bstep (se 1 (by rfl) ⟨613208, by rfl⟩ : syracuseStep 817611 = 1226417) B1226417
theorem B817623 : Blo 814346 817623 := bstep (se 1 (by rfl) ⟨613217, by rfl⟩ : syracuseStep 817623 = 1226435) B1226435
theorem B817643 : Blo 814346 817643 := bstep (se 1 (by rfl) ⟨613232, by rfl⟩ : syracuseStep 817643 = 1226465) B1226465
theorem B817655 : Blo 814346 817655 := bstep (se 1 (by rfl) ⟨613241, by rfl⟩ : syracuseStep 817655 = 1226483) B1226483
theorem B817675 : Blo 814346 817675 := bstep (se 1 (by rfl) ⟨613256, by rfl⟩ : syracuseStep 817675 = 1226513) B1226513
theorem B1374745 : Blo 814346 1374745 := bstep (se 2 (by rfl) ⟨515529, by rfl⟩ : syracuseStep 1374745 = 1031059) B1031059
theorem B1833497 : Blo 814346 1833497 := bstep (se 2 (by rfl) ⟨687561, by rfl⟩ : syracuseStep 1833497 = 1375123) B1375123
theorem B817687 : Blo 814346 817687 := bstep (se 1 (by rfl) ⟨613265, by rfl⟩ : syracuseStep 817687 = 1226531) B1226531
theorem B2947607 : Blo 814346 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B817707 : Blo 814346 817707 := bstep (se 1 (by rfl) ⟨613280, by rfl⟩ : syracuseStep 817707 = 1226561) B1226561
theorem B817719 : Blo 814346 817719 := bstep (se 1 (by rfl) ⟨613289, by rfl⟩ : syracuseStep 817719 = 1226579) B1226579
theorem B817739 : Blo 814346 817739 := bstep (se 1 (by rfl) ⟨613304, by rfl⟩ : syracuseStep 817739 = 1226609) B1226609
theorem B5241419 : Blo 814346 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B817751 : Blo 814346 817751 := bstep (se 1 (by rfl) ⟨613313, by rfl⟩ : syracuseStep 817751 = 1226627) B1226627
theorem B4651613 : Blo 814346 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B817771 : Blo 814346 817771 := bstep (se 1 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 817771 = 1226657) B1226657
theorem B1833587 : Blo 814346 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B817783 : Blo 814346 817783 := bstep (se 1 (by rfl) ⟨613337, by rfl⟩ : syracuseStep 817783 = 1226675) B1226675
theorem B817803 : Blo 814346 817803 := bstep (se 1 (by rfl) ⟨613352, by rfl⟩ : syracuseStep 817803 = 1226705) B1226705
theorem B1833623 : Blo 814346 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B817815 : Blo 814346 817815 := bstep (se 1 (by rfl) ⟨613361, by rfl⟩ : syracuseStep 817815 = 1226723) B1226723
theorem B817835 : Blo 814346 817835 := bstep (se 1 (by rfl) ⟨613376, by rfl⟩ : syracuseStep 817835 = 1226753) B1226753
theorem B817847 : Blo 814346 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B817867 : Blo 814346 817867 := bstep (se 1 (by rfl) ⟨613400, by rfl⟩ : syracuseStep 817867 = 1226801) B1226801
theorem B817879 : Blo 814346 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B817899 : Blo 814346 817899 := bstep (se 1 (by rfl) ⟨613424, by rfl⟩ : syracuseStep 817899 = 1226849) B1226849
theorem B817911 : Blo 814346 817911 := bstep (se 1 (by rfl) ⟨613433, by rfl⟩ : syracuseStep 817911 = 1226867) B1226867
theorem B817931 : Blo 814346 817931 := bstep (se 1 (by rfl) ⟨613448, by rfl⟩ : syracuseStep 817931 = 1226897) B1226897
theorem B817943 : Blo 814346 817943 := bstep (se 1 (by rfl) ⟨613457, by rfl⟩ : syracuseStep 817943 = 1226915) B1226915
theorem B916267 : Blo 814346 916267 := bstep (se 1 (by rfl) ⟨687200, by rfl⟩ : syracuseStep 916267 = 1374401) B1374401
theorem B817963 : Blo 814346 817963 := bstep (se 1 (by rfl) ⟨613472, by rfl⟩ : syracuseStep 817963 = 1226945) B1226945
theorem B817975 : Blo 814346 817975 := bstep (se 1 (by rfl) ⟨613481, by rfl⟩ : syracuseStep 817975 = 1226963) B1226963
theorem B1833803 : Blo 814346 1833803 := bstep (se 1 (by rfl) ⟨1375352, by rfl⟩ : syracuseStep 1833803 = 2750705) B2750705
theorem B817995 : Blo 814346 817995 := bstep (se 1 (by rfl) ⟨613496, by rfl⟩ : syracuseStep 817995 = 1226993) B1226993
theorem B818007 : Blo 814346 818007 := bstep (se 1 (by rfl) ⟨613505, by rfl⟩ : syracuseStep 818007 = 1227011) B1227011
theorem B20380517 : Blo 814346 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B818027 : Blo 814346 818027 := bstep (se 1 (by rfl) ⟨613520, by rfl⟩ : syracuseStep 818027 = 1227041) B1227041
theorem B818039 : Blo 814346 818039 := bstep (se 1 (by rfl) ⟨613529, by rfl⟩ : syracuseStep 818039 = 1227059) B1227059
theorem B1833857 : Blo 814346 1833857 := bstep (se 2 (by rfl) ⟨687696, by rfl⟩ : syracuseStep 1833857 = 1375393) B1375393
theorem B818059 : Blo 814346 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B916375 : Blo 814346 916375 := bstep (se 1 (by rfl) ⟨687281, by rfl⟩ : syracuseStep 916375 = 1374563) B1374563
theorem B818071 : Blo 814346 818071 := bstep (se 1 (by rfl) ⟨613553, by rfl⟩ : syracuseStep 818071 = 1227107) B1227107
theorem B818091 : Blo 814346 818091 := bstep (se 1 (by rfl) ⟨613568, by rfl⟩ : syracuseStep 818091 = 1227137) B1227137
theorem B818103 : Blo 814346 818103 := bstep (se 1 (by rfl) ⟨613577, by rfl⟩ : syracuseStep 818103 = 1227155) B1227155
theorem B818123 : Blo 814346 818123 := bstep (se 1 (by rfl) ⟨613592, by rfl⟩ : syracuseStep 818123 = 1227185) B1227185
theorem B1244107 : Blo 814346 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B818135 : Blo 814346 818135 := bstep (se 1 (by rfl) ⟨613601, by rfl⟩ : syracuseStep 818135 = 1227203) B1227203
theorem B21232601 : Blo 814346 21232601 := bstep (se 2 (by rfl) ⟨7962225, by rfl⟩ : syracuseStep 21232601 = 15924451) B15924451
theorem B818155 : Blo 814346 818155 := bstep (se 1 (by rfl) ⟨613616, by rfl⟩ : syracuseStep 818155 = 1227233) B1227233
theorem B818167 : Blo 814346 818167 := bstep (se 1 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 818167 = 1227251) B1227251
theorem B818187 : Blo 814346 818187 := bstep (se 1 (by rfl) ⟨613640, by rfl⟩ : syracuseStep 818187 = 1227281) B1227281
theorem B818199 : Blo 814346 818199 := bstep (se 1 (by rfl) ⟨613649, by rfl⟩ : syracuseStep 818199 = 1227299) B1227299
theorem B818219 : Blo 814346 818219 := bstep (se 1 (by rfl) ⟨613664, by rfl⟩ : syracuseStep 818219 = 1227329) B1227329
theorem B818231 : Blo 814346 818231 := bstep (se 1 (by rfl) ⟨613673, by rfl⟩ : syracuseStep 818231 = 1227347) B1227347
theorem B916555 : Blo 814346 916555 := bstep (se 1 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 916555 = 1374833) B1374833
theorem B818251 : Blo 814346 818251 := bstep (se 1 (by rfl) ⟨613688, by rfl⟩ : syracuseStep 818251 = 1227377) B1227377
theorem B1375319 : Blo 814346 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B818263 : Blo 814346 818263 := bstep (se 1 (by rfl) ⟨613697, by rfl⟩ : syracuseStep 818263 = 1227395) B1227395
theorem B1834073 : Blo 814346 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B2620505 : Blo 814346 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B818283 : Blo 814346 818283 := bstep (se 1 (by rfl) ⟨613712, by rfl⟩ : syracuseStep 818283 = 1227425) B1227425
theorem B818295 : Blo 814346 818295 := bstep (se 1 (by rfl) ⟨613721, by rfl⟩ : syracuseStep 818295 = 1227443) B1227443
theorem B818315 : Blo 814346 818315 := bstep (se 1 (by rfl) ⟨613736, by rfl⟩ : syracuseStep 818315 = 1227473) B1227473
theorem B818327 : Blo 814346 818327 := bstep (se 1 (by rfl) ⟨613745, by rfl⟩ : syracuseStep 818327 = 1227491) B1227491
theorem B1834163 : Blo 814346 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B916663 : Blo 814346 916663 := bstep (se 1 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 916663 = 1374995) B1374995
theorem B1375447 : Blo 814346 1375447 := bstep (se 1 (by rfl) ⟨1031585, by rfl⟩ : syracuseStep 1375447 = 2063171) B2063171
theorem B1834199 : Blo 814346 1834199 := bstep (se 1 (by rfl) ⟨1375649, by rfl⟩ : syracuseStep 1834199 = 2751299) B2751299
theorem B3767555 : Blo 814346 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B916843 : Blo 814346 916843 := bstep (se 1 (by rfl) ⟨687632, by rfl⟩ : syracuseStep 916843 = 1375265) B1375265
theorem B1834379 : Blo 814346 1834379 := bstep (se 1 (by rfl) ⟨1375784, by rfl⟩ : syracuseStep 1834379 = 2751569) B2751569
theorem B1834433 : Blo 814346 1834433 := bstep (se 2 (by rfl) ⟨687912, by rfl⟩ : syracuseStep 1834433 = 1375825) B1375825
theorem B2063819 : Blo 814346 2063819 := bstep (se 1 (by rfl) ⟨1547864, by rfl⟩ : syracuseStep 2063819 = 3095729) B3095729
theorem B2751947 : Blo 814346 2751947 := bstep (se 1 (by rfl) ⟨2063960, by rfl⟩ : syracuseStep 2751947 = 4127921) B4127921
theorem B916951 : Blo 814346 916951 := bstep (se 1 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 916951 = 1375427) B1375427
theorem B1572311 : Blo 814346 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B917131 : Blo 814346 917131 := bstep (se 1 (by rfl) ⟨687848, by rfl⟩ : syracuseStep 917131 = 1375697) B1375697
theorem B4128407 : Blo 814346 4128407 := bstep (se 1 (by rfl) ⟨3096305, by rfl⟩ : syracuseStep 4128407 = 6192611) B6192611
theorem B1834649 : Blo 814346 1834649 := bstep (se 2 (by rfl) ⟨687993, by rfl⟩ : syracuseStep 1834649 = 1375987) B1375987
theorem B2752217 : Blo 814346 2752217 := bstep (se 2 (by rfl) ⟨1032081, by rfl⟩ : syracuseStep 2752217 = 2064163) B2064163
theorem B1474265 : Blo 814346 1474265 := bstep (se 2 (by rfl) ⟨552849, by rfl⟩ : syracuseStep 1474265 = 1105699) B1105699
theorem B1834739 : Blo 814346 1834739 := bstep (se 1 (by rfl) ⟨1376054, by rfl⟩ : syracuseStep 1834739 = 2752109) B2752109
theorem B917239 : Blo 814346 917239 := bstep (se 1 (by rfl) ⟨687929, by rfl⟩ : syracuseStep 917239 = 1375859) B1375859
theorem B1834775 : Blo 814346 1834775 := bstep (se 1 (by rfl) ⟨1376081, by rfl⟩ : syracuseStep 1834775 = 2752163) B2752163
theorem B1376075 : Blo 814346 1376075 := bstep (se 1 (by rfl) ⟨1032056, by rfl⟩ : syracuseStep 1376075 = 2064113) B2064113
theorem B917419 : Blo 814346 917419 := bstep (se 1 (by rfl) ⟨688064, by rfl⟩ : syracuseStep 917419 = 1376129) B1376129
theorem B1376203 : Blo 814346 1376203 := bstep (se 1 (by rfl) ⟨1032152, by rfl⟩ : syracuseStep 1376203 = 2064305) B2064305
theorem B1834955 : Blo 814346 1834955 := bstep (se 1 (by rfl) ⟨1376216, by rfl⟩ : syracuseStep 1834955 = 2752433) B2752433
theorem B6979607 : Blo 814346 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B2752541 : Blo 814346 2752541 := bstep (se 3 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 2752541 = 1032203) B1032203
theorem B917563 : Blo 814346 917563 := bstep (se 1 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 917563 = 1376345) B1376345
theorem B4423747 : Blo 814346 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B1835279 : Blo 814346 1835279 := bstep (se 1 (by rfl) ⟨1376459, by rfl⟩ : syracuseStep 1835279 = 2752919) B2752919
theorem B1376527 : Blo 814346 1376527 := bstep (se 1 (by rfl) ⟨1032395, by rfl⟩ : syracuseStep 1376527 = 2064791) B2064791
theorem B1835297 : Blo 814346 1835297 := bstep (se 2 (by rfl) ⟨688236, by rfl⟩ : syracuseStep 1835297 = 1376473) B1376473
theorem B4424051 : Blo 814346 4424051 := bstep (se 1 (by rfl) ⟨3318038, by rfl⟩ : syracuseStep 4424051 = 6636077) B6636077
theorem B1180075 : Blo 814346 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B4653571 : Blo 814346 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B3310091 : Blo 814346 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B918031 : Blo 814346 918031 := bstep (se 1 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 918031 = 1377047) B1377047
theorem B2425373 : Blo 814346 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B7864897 : Blo 814346 7864897 := bstep (se 2 (by rfl) ⟨2949336, by rfl⟩ : syracuseStep 7864897 = 5898673) B5898673
theorem B1835639 : Blo 814346 1835639 := bstep (se 1 (by rfl) ⟨1376729, by rfl⟩ : syracuseStep 1835639 = 2753459) B2753459
theorem B1835819 : Blo 814346 1835819 := bstep (se 1 (by rfl) ⟨1376864, by rfl⟩ : syracuseStep 1835819 = 2753729) B2753729
theorem B1377067 : Blo 814346 1377067 := bstep (se 1 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 1377067 = 2065601) B2065601
theorem B1377209 : Blo 814346 1377209 := bstep (se 2 (by rfl) ⟨516453, by rfl⟩ : syracuseStep 1377209 = 1032907) B1032907
theorem B2065409 : Blo 814346 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B918535 : Blo 814346 918535 := bstep (se 1 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 918535 = 1377803) B1377803
theorem B8815661 : Blo 814346 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B2983031 : Blo 814346 2983031 := bstep (se 1 (by rfl) ⟨2237273, by rfl⟩ : syracuseStep 2983031 = 4474547) B4474547
theorem B2327687 : Blo 814346 2327687 := bstep (se 1 (by rfl) ⟨1745765, by rfl⟩ : syracuseStep 2327687 = 3491531) B3491531
theorem B1836179 : Blo 814346 1836179 := bstep (se 1 (by rfl) ⟨1377134, by rfl⟩ : syracuseStep 1836179 = 2754269) B2754269
theorem B918715 : Blo 814346 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B1836233 : Blo 814346 1836233 := bstep (se 2 (by rfl) ⟨688587, by rfl⟩ : syracuseStep 1836233 = 1377175) B1377175
theorem B3015937 : Blo 814346 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B2065783 : Blo 814346 2065783 := bstep (se 1 (by rfl) ⟨1549337, by rfl⟩ : syracuseStep 2065783 = 3098675) B3098675
theorem B2753945 : Blo 814346 2753945 := bstep (se 2 (by rfl) ⟨1032729, by rfl⟩ : syracuseStep 2753945 = 2065459) B2065459
theorem B4195901 : Blo 814346 4195901 := bstep (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) B1573463
theorem B1377911 : Blo 814346 1377911 := bstep (se 1 (by rfl) ⟨1033433, by rfl⟩ : syracuseStep 1377911 = 2066867) B2066867
theorem B919183 : Blo 814346 919183 := bstep (se 1 (by rfl) ⟨689387, by rfl⟩ : syracuseStep 919183 = 1378775) B1378775
theorem B2328335 : Blo 814346 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B2066219 : Blo 814346 2066219 := bstep (se 1 (by rfl) ⟨1549664, by rfl⟩ : syracuseStep 2066219 = 3099329) B3099329
theorem B4130675 : Blo 814346 4130675 := bstep (se 1 (by rfl) ⟨3098006, by rfl⟩ : syracuseStep 4130675 = 6196013) B6196013
theorem B1836935 : Blo 814346 1836935 := bstep (se 1 (by rfl) ⟨1377701, by rfl⟩ : syracuseStep 1836935 = 2755403) B2755403
theorem B7440407 : Blo 814346 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B1837115 : Blo 814346 1837115 := bstep (se 1 (by rfl) ⟨1377836, by rfl⟩ : syracuseStep 1837115 = 2755673) B2755673
theorem B1378363 : Blo 814346 1378363 := bstep (se 1 (by rfl) ⟨1033772, by rfl⟩ : syracuseStep 1378363 = 2067545) B2067545
theorem B2754647 : Blo 814346 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B4786295 : Blo 814346 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B8390789 : Blo 814346 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B919687 : Blo 814346 919687 := bstep (se 1 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 919687 = 1379531) B1379531
theorem B1837241 : Blo 814346 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B1378505 : Blo 814346 1378505 := bstep (se 2 (by rfl) ⟨516939, by rfl⟩ : syracuseStep 1378505 = 1033879) B1033879
theorem B919867 : Blo 814346 919867 := bstep (se 1 (by rfl) ⟨689900, by rfl⟩ : syracuseStep 919867 = 1379801) B1379801
theorem B4131161 : Blo 814346 4131161 := bstep (se 2 (by rfl) ⟨1549185, by rfl⟩ : syracuseStep 4131161 = 3098371) B3098371
theorem B13240817 : Blo 814346 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B1837583 : Blo 814346 1837583 := bstep (se 1 (by rfl) ⟨1378187, by rfl⟩ : syracuseStep 1837583 = 2756375) B2756375
theorem B1837601 : Blo 814346 1837601 := bstep (se 2 (by rfl) ⟨689100, by rfl⟩ : syracuseStep 1837601 = 1378201) B1378201
theorem B2755133 : Blo 814346 2755133 := bstep (se 3 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 2755133 = 1033175) B1033175
theorem B3181123 : Blo 814346 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B2067059 : Blo 814346 2067059 := bstep (se 1 (by rfl) ⟨1550294, by rfl⟩ : syracuseStep 2067059 = 3100589) B3100589
theorem B13208183 : Blo 814346 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B2067079 : Blo 814346 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B920335 : Blo 814346 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B4655987 : Blo 814346 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1837943 : Blo 814346 1837943 := bstep (se 1 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 1837943 = 2756915) B2756915
theorem B1379207 : Blo 814346 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B2067353 : Blo 814346 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B1739819 : Blo 814346 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B1838123 : Blo 814346 1838123 := bstep (se 1 (by rfl) ⟨1378592, by rfl⟩ : syracuseStep 1838123 = 2757185) B2757185
theorem B2067515 : Blo 814346 2067515 := bstep (se 1 (by rfl) ⟨1550636, by rfl⟩ : syracuseStep 2067515 = 3101273) B3101273
theorem B7441541 : Blo 814346 7441541 := bstep (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) B1395289
theorem B2067727 : Blo 814346 2067727 := bstep (se 1 (by rfl) ⟨1550795, by rfl⟩ : syracuseStep 2067727 = 3101591) B3101591
theorem B7834913 : Blo 814346 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B2329975 : Blo 814346 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B1838483 : Blo 814346 1838483 := bstep (se 1 (by rfl) ⟨1378862, by rfl⟩ : syracuseStep 1838483 = 2757725) B2757725
theorem B1838537 : Blo 814346 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B1379855 : Blo 814346 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B2068001 : Blo 814346 2068001 := bstep (se 2 (by rfl) ⟨775500, by rfl⟩ : syracuseStep 2068001 = 1551001) B1551001
theorem B20877101 : Blo 814346 20877101 := bstep (se 3 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 20877101 = 7828913) B7828913
theorem B2756537 : Blo 814346 2756537 := bstep (se 2 (by rfl) ⟨1033701, by rfl⟩ : syracuseStep 2756537 = 2067403) B2067403
theorem B1380395 : Blo 814346 1380395 := bstep (se 1 (by rfl) ⟨1035296, by rfl⟩ : syracuseStep 1380395 = 2070593) B2070593
theorem B1839239 : Blo 814346 1839239 := bstep (se 1 (by rfl) ⟨1379429, by rfl⟩ : syracuseStep 1839239 = 2758859) B2758859
theorem B4788397 : Blo 814346 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B4657445 : Blo 814346 4657445 := bstep (se 4 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 4657445 = 873271) B873271
theorem B1839419 : Blo 814346 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B4133267 : Blo 814346 4133267 := bstep (se 1 (by rfl) ⟨3099950, by rfl⟩ : syracuseStep 4133267 = 6199901) B6199901
theorem B1839545 : Blo 814346 1839545 := bstep (se 2 (by rfl) ⟨689829, by rfl⟩ : syracuseStep 1839545 = 1379659) B1379659
theorem B1380793 : Blo 814346 1380793 := bstep (se 2 (by rfl) ⟨517797, by rfl⟩ : syracuseStep 1380793 = 1035595) B1035595
theorem B5870045 : Blo 814346 5870045 := bstep (se 3 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 5870045 = 2201267) B2201267
theorem B2757131 : Blo 814346 2757131 := bstep (se 1 (by rfl) ⟨2067848, by rfl⟩ : syracuseStep 2757131 = 4135697) B4135697
theorem B2069003 : Blo 814346 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B9310787 : Blo 814346 9310787 := bstep (se 1 (by rfl) ⟨6983090, by rfl⟩ : syracuseStep 9310787 = 13966181) B13966181
theorem B2757239 : Blo 814346 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B1839887 : Blo 814346 1839887 := bstep (se 1 (by rfl) ⟨1379915, by rfl⟩ : syracuseStep 1839887 = 2759831) B2759831
theorem B1839905 : Blo 814346 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B35754979 : Blo 814346 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B4658219 : Blo 814346 4658219 := bstep (se 1 (by rfl) ⟨3493664, by rfl⟩ : syracuseStep 4658219 = 6987329) B6987329
theorem B2233405 : Blo 814346 2233405 := bstep (se 3 (by rfl) ⟨418763, by rfl⟩ : syracuseStep 2233405 = 837527) B837527
theorem B1840247 : Blo 814346 1840247 := bstep (se 1 (by rfl) ⟨1380185, by rfl⟩ : syracuseStep 1840247 = 2760371) B2760371
theorem B2069651 : Blo 814346 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B2757833 : Blo 814346 2757833 := bstep (se 2 (by rfl) ⟨1034187, by rfl⟩ : syracuseStep 2757833 = 2068375) B2068375
theorem B1840427 : Blo 814346 1840427 := bstep (se 1 (by rfl) ⟨1380320, by rfl⟩ : syracuseStep 1840427 = 2760641) B2760641
theorem B7968131 : Blo 814346 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B2069945 : Blo 814346 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B3479107 : Blo 814346 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B1840787 : Blo 814346 1840787 := bstep (se 1 (by rfl) ⟨1380590, by rfl⟩ : syracuseStep 1840787 = 2761181) B2761181
theorem B1840841 : Blo 814346 1840841 := bstep (se 2 (by rfl) ⟨690315, by rfl⟩ : syracuseStep 1840841 = 1380631) B1380631
theorem B1546103 : Blo 814346 1546103 := bstep (se 1 (by rfl) ⟨1159577, by rfl⟩ : syracuseStep 1546103 = 2319155) B2319155
theorem B2758535 : Blo 814346 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B3479449 : Blo 814346 3479449 := bstep (se 2 (by rfl) ⟨1304793, by rfl⟩ : syracuseStep 3479449 = 2609587) B2609587
theorem B2070643 : Blo 814346 2070643 := bstep (se 1 (by rfl) ⟨1552982, by rfl⟩ : syracuseStep 2070643 = 3105965) B3105965
theorem B3774583 : Blo 814346 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B2758913 : Blo 814346 2758913 := bstep (se 2 (by rfl) ⟨1034592, by rfl⟩ : syracuseStep 2758913 = 2069185) B2069185
theorem B2070785 : Blo 814346 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B4659677 : Blo 814346 4659677 := bstep (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) B1747379
theorem B2071241 : Blo 814346 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B2759723 : Blo 814346 2759723 := bstep (se 1 (by rfl) ⟨2069792, by rfl⟩ : syracuseStep 2759723 = 4139585) B4139585
theorem B4136345 : Blo 814346 4136345 := bstep (se 2 (by rfl) ⟨1551129, by rfl⟩ : syracuseStep 4136345 = 3102259) B3102259
theorem B4955651 : Blo 814346 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B1547819 : Blo 814346 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B1548047 : Blo 814346 1548047 := bstep (se 1 (by rfl) ⟨1161035, by rfl⟩ : syracuseStep 1548047 = 2322071) B2322071
theorem B7938071 : Blo 814346 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B17670413 : Blo 814346 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B2761019 : Blo 814346 2761019 := bstep (se 1 (by rfl) ⟨2070764, by rfl⟩ : syracuseStep 2761019 = 4141529) B4141529
theorem B7840259 : Blo 814346 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B6988355 : Blo 814346 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B2761505 : Blo 814346 2761505 := bstep (se 2 (by rfl) ⟨1035564, by rfl⟩ : syracuseStep 2761505 = 2071129) B2071129
theorem B7840601 : Blo 814346 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B9315161 : Blo 814346 9315161 := bstep (se 2 (by rfl) ⟨3493185, by rfl⟩ : syracuseStep 9315161 = 6986371) B6986371
theorem B1221563 : Blo 814346 1221563 := bstep (se 1 (by rfl) ⟨916172, by rfl⟩ : syracuseStep 1221563 = 1832345) B1832345
theorem B1221623 : Blo 814346 1221623 := bstep (se 1 (by rfl) ⟨916217, by rfl⟩ : syracuseStep 1221623 = 1832435) B1832435
theorem B1221647 : Blo 814346 1221647 := bstep (se 1 (by rfl) ⟨916235, by rfl⟩ : syracuseStep 1221647 = 1832471) B1832471
theorem B1221689 : Blo 814346 1221689 := bstep (se 2 (by rfl) ⟨458133, by rfl⟩ : syracuseStep 1221689 = 916267) B916267
theorem B1221767 : Blo 814346 1221767 := bstep (se 1 (by rfl) ⟨916325, by rfl⟩ : syracuseStep 1221767 = 1832651) B1832651
theorem B1549459 : Blo 814346 1549459 := bstep (se 1 (by rfl) ⟨1162094, by rfl⟩ : syracuseStep 1549459 = 2324189) B2324189
theorem B1221803 : Blo 814346 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B1221833 : Blo 814346 1221833 := bstep (se 2 (by rfl) ⟨458187, by rfl⟩ : syracuseStep 1221833 = 916375) B916375
theorem B1221947 : Blo 814346 1221947 := bstep (se 1 (by rfl) ⟨916460, by rfl⟩ : syracuseStep 1221947 = 1832921) B1832921
theorem B1222007 : Blo 814346 1222007 := bstep (se 1 (by rfl) ⟨916505, by rfl⟩ : syracuseStep 1222007 = 1833011) B1833011
theorem B1549687 : Blo 814346 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B1222031 : Blo 814346 1222031 := bstep (se 1 (by rfl) ⟨916523, by rfl⟩ : syracuseStep 1222031 = 1833047) B1833047
theorem B1222073 : Blo 814346 1222073 := bstep (se 2 (by rfl) ⟨458277, by rfl⟩ : syracuseStep 1222073 = 916555) B916555
theorem B1222151 : Blo 814346 1222151 := bstep (se 1 (by rfl) ⟨916613, by rfl⟩ : syracuseStep 1222151 = 1833227) B1833227
theorem B1222187 : Blo 814346 1222187 := bstep (se 1 (by rfl) ⟨916640, by rfl⟩ : syracuseStep 1222187 = 1833281) B1833281
theorem B1222217 : Blo 814346 1222217 := bstep (se 2 (by rfl) ⟨458331, by rfl⟩ : syracuseStep 1222217 = 916663) B916663
theorem B1222331 : Blo 814346 1222331 := bstep (se 1 (by rfl) ⟨916748, by rfl⟩ : syracuseStep 1222331 = 1833497) B1833497
theorem B1222391 : Blo 814346 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B1222415 : Blo 814346 1222415 := bstep (se 1 (by rfl) ⟨916811, by rfl⟩ : syracuseStep 1222415 = 1833623) B1833623
theorem B1222457 : Blo 814346 1222457 := bstep (se 2 (by rfl) ⟨458421, by rfl⟩ : syracuseStep 1222457 = 916843) B916843
theorem B1222535 : Blo 814346 1222535 := bstep (se 1 (by rfl) ⟨916901, by rfl⟩ : syracuseStep 1222535 = 1833803) B1833803
theorem B1222571 : Blo 814346 1222571 := bstep (se 1 (by rfl) ⟨916928, by rfl⟩ : syracuseStep 1222571 = 1833857) B1833857
theorem B4138937 : Blo 814346 4138937 := bstep (se 2 (by rfl) ⟨1552101, by rfl⟩ : syracuseStep 4138937 = 3104203) B3104203
theorem B1222601 : Blo 814346 1222601 := bstep (se 2 (by rfl) ⟨458475, by rfl⟩ : syracuseStep 1222601 = 916951) B916951
theorem B1222715 : Blo 814346 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1747003 : Blo 814346 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1222775 : Blo 814346 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B1222799 : Blo 814346 1222799 := bstep (se 1 (by rfl) ⟨917099, by rfl⟩ : syracuseStep 1222799 = 1834199) B1834199
theorem B1222841 : Blo 814346 1222841 := bstep (se 2 (by rfl) ⟨458565, by rfl⟩ : syracuseStep 1222841 = 917131) B917131
theorem B1222919 : Blo 814346 1222919 := bstep (se 1 (by rfl) ⟨917189, by rfl⟩ : syracuseStep 1222919 = 1834379) B1834379
theorem B1222955 : Blo 814346 1222955 := bstep (se 1 (by rfl) ⟨917216, by rfl⟩ : syracuseStep 1222955 = 1834433) B1834433
theorem B1222985 : Blo 814346 1222985 := bstep (se 2 (by rfl) ⟨458619, by rfl⟩ : syracuseStep 1222985 = 917239) B917239
theorem B1223099 : Blo 814346 1223099 := bstep (se 1 (by rfl) ⟨917324, by rfl⟩ : syracuseStep 1223099 = 1834649) B1834649
theorem B1223159 : Blo 814346 1223159 := bstep (se 1 (by rfl) ⟨917369, by rfl⟩ : syracuseStep 1223159 = 1834739) B1834739
theorem B1223183 : Blo 814346 1223183 := bstep (se 1 (by rfl) ⟨917387, by rfl⟩ : syracuseStep 1223183 = 1834775) B1834775
theorem B1223225 : Blo 814346 1223225 := bstep (se 2 (by rfl) ⟨458709, by rfl⟩ : syracuseStep 1223225 = 917419) B917419
theorem B1223303 : Blo 814346 1223303 := bstep (se 1 (by rfl) ⟨917477, by rfl⟩ : syracuseStep 1223303 = 1834955) B1834955
theorem B1223339 : Blo 814346 1223339 := bstep (se 1 (by rfl) ⟨917504, by rfl⟩ : syracuseStep 1223339 = 1835009) B1835009
theorem B1223369 : Blo 814346 1223369 := bstep (se 2 (by rfl) ⟨458763, by rfl⟩ : syracuseStep 1223369 = 917527) B917527
theorem B5581619 : Blo 814346 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B1223483 : Blo 814346 1223483 := bstep (se 1 (by rfl) ⟨917612, by rfl⟩ : syracuseStep 1223483 = 1835225) B1835225
theorem B6204275 : Blo 814346 6204275 := bstep (se 1 (by rfl) ⟨4653206, by rfl⟩ : syracuseStep 6204275 = 9306413) B9306413
theorem B1223543 : Blo 814346 1223543 := bstep (se 1 (by rfl) ⟨917657, by rfl⟩ : syracuseStep 1223543 = 1835315) B1835315
theorem B1223567 : Blo 814346 1223567 := bstep (se 1 (by rfl) ⟨917675, by rfl⟩ : syracuseStep 1223567 = 1835351) B1835351
theorem B1551251 : Blo 814346 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B6990745 : Blo 814346 6990745 := bstep (se 2 (by rfl) ⟨2621529, by rfl⟩ : syracuseStep 6990745 = 5243059) B5243059
theorem B1223609 : Blo 814346 1223609 := bstep (se 2 (by rfl) ⟨458853, by rfl⟩ : syracuseStep 1223609 = 917707) B917707
theorem B1551305 : Blo 814346 1551305 := bstep (se 2 (by rfl) ⟨581739, by rfl⟩ : syracuseStep 1551305 = 1163479) B1163479
theorem B1223687 : Blo 814346 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B8825867 : Blo 814346 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1223723 : Blo 814346 1223723 := bstep (se 1 (by rfl) ⟨917792, by rfl⟩ : syracuseStep 1223723 = 1835585) B1835585
theorem B1551403 : Blo 814346 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B1223753 : Blo 814346 1223753 := bstep (se 2 (by rfl) ⟨458907, by rfl⟩ : syracuseStep 1223753 = 917815) B917815
theorem B1223867 : Blo 814346 1223867 := bstep (se 1 (by rfl) ⟨917900, by rfl⟩ : syracuseStep 1223867 = 1835801) B1835801
theorem B4140233 : Blo 814346 4140233 := bstep (se 2 (by rfl) ⟨1552587, by rfl⟩ : syracuseStep 4140233 = 3105175) B3105175
theorem B1223927 : Blo 814346 1223927 := bstep (se 1 (by rfl) ⟨917945, by rfl⟩ : syracuseStep 1223927 = 1835891) B1835891
theorem B1223951 : Blo 814346 1223951 := bstep (se 1 (by rfl) ⟨917963, by rfl⟩ : syracuseStep 1223951 = 1835927) B1835927
theorem B1551631 : Blo 814346 1551631 := bstep (se 1 (by rfl) ⟨1163723, by rfl⟩ : syracuseStep 1551631 = 2327447) B2327447
theorem B1223993 : Blo 814346 1223993 := bstep (se 2 (by rfl) ⟨458997, by rfl⟩ : syracuseStep 1223993 = 917995) B917995
theorem B1224071 : Blo 814346 1224071 := bstep (se 1 (by rfl) ⟨918053, by rfl⟩ : syracuseStep 1224071 = 1836107) B1836107
theorem B1224107 : Blo 814346 1224107 := bstep (se 1 (by rfl) ⟨918080, by rfl⟩ : syracuseStep 1224107 = 1836161) B1836161
theorem B1224137 : Blo 814346 1224137 := bstep (se 2 (by rfl) ⟨459051, by rfl⟩ : syracuseStep 1224137 = 918103) B918103
theorem B1224251 : Blo 814346 1224251 := bstep (se 1 (by rfl) ⟨918188, by rfl⟩ : syracuseStep 1224251 = 1836377) B1836377
theorem B1224311 : Blo 814346 1224311 := bstep (se 1 (by rfl) ⟨918233, by rfl⟩ : syracuseStep 1224311 = 1836467) B1836467
theorem B1224335 : Blo 814346 1224335 := bstep (se 1 (by rfl) ⟨918251, by rfl⟩ : syracuseStep 1224335 = 1836503) B1836503
theorem B1224377 : Blo 814346 1224377 := bstep (se 2 (by rfl) ⟨459141, by rfl⟩ : syracuseStep 1224377 = 918283) B918283
theorem B1224455 : Blo 814346 1224455 := bstep (se 1 (by rfl) ⟨918341, by rfl⟩ : syracuseStep 1224455 = 1836683) B1836683
theorem B1224491 : Blo 814346 1224491 := bstep (se 1 (by rfl) ⟨918368, by rfl⟩ : syracuseStep 1224491 = 1836737) B1836737
theorem B2207549 : Blo 814346 2207549 := bstep (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) B827831
theorem B1224521 : Blo 814346 1224521 := bstep (se 2 (by rfl) ⟨459195, by rfl⟩ : syracuseStep 1224521 = 918391) B918391
theorem B929723 : Blo 814346 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B1224635 : Blo 814346 1224635 := bstep (se 1 (by rfl) ⟨918476, by rfl⟩ : syracuseStep 1224635 = 1836953) B1836953
theorem B1224695 : Blo 814346 1224695 := bstep (se 1 (by rfl) ⟨918521, by rfl⟩ : syracuseStep 1224695 = 1837043) B1837043
theorem B1224719 : Blo 814346 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B1224761 : Blo 814346 1224761 := bstep (se 2 (by rfl) ⟨459285, by rfl⟩ : syracuseStep 1224761 = 918571) B918571
theorem B1224839 : Blo 814346 1224839 := bstep (se 1 (by rfl) ⟨918629, by rfl⟩ : syracuseStep 1224839 = 1837259) B1837259
theorem B1224875 : Blo 814346 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B1224905 : Blo 814346 1224905 := bstep (se 2 (by rfl) ⟨459339, by rfl⟩ : syracuseStep 1224905 = 918679) B918679
theorem B1225019 : Blo 814346 1225019 := bstep (se 1 (by rfl) ⟨918764, by rfl⟩ : syracuseStep 1225019 = 1837529) B1837529
theorem B1159543 : Blo 814346 1159543 := bstep (se 1 (by rfl) ⟨869657, by rfl⟩ : syracuseStep 1159543 = 1739315) B1739315
theorem B1225079 : Blo 814346 1225079 := bstep (se 1 (by rfl) ⟨918809, by rfl⟩ : syracuseStep 1225079 = 1837619) B1837619
theorem B3715463 : Blo 814346 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B1225103 : Blo 814346 1225103 := bstep (se 1 (by rfl) ⟨918827, by rfl⟩ : syracuseStep 1225103 = 1837655) B1837655
theorem B1225145 : Blo 814346 1225145 := bstep (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) B918859
theorem B1225223 : Blo 814346 1225223 := bstep (se 1 (by rfl) ⟨918917, by rfl⟩ : syracuseStep 1225223 = 1837835) B1837835
theorem B75280913 : Blo 814346 75280913 := bstep (se 2 (by rfl) ⟨28230342, by rfl⟩ : syracuseStep 75280913 = 56460685) B56460685
theorem B42480163 : Blo 814346 42480163 := bstep (se 1 (by rfl) ⟨31860122, by rfl⟩ : syracuseStep 42480163 = 63720245) B63720245
theorem B1225259 : Blo 814346 1225259 := bstep (se 1 (by rfl) ⟨918944, by rfl⟩ : syracuseStep 1225259 = 1837889) B1837889
theorem B1225289 : Blo 814346 1225289 := bstep (se 2 (by rfl) ⟨459483, by rfl⟩ : syracuseStep 1225289 = 918967) B918967
theorem B1225403 : Blo 814346 1225403 := bstep (se 1 (by rfl) ⟨919052, by rfl⟩ : syracuseStep 1225403 = 1838105) B1838105
theorem B1225463 : Blo 814346 1225463 := bstep (se 1 (by rfl) ⟨919097, by rfl⟩ : syracuseStep 1225463 = 1838195) B1838195
theorem B1225487 : Blo 814346 1225487 := bstep (se 1 (by rfl) ⟨919115, by rfl⟩ : syracuseStep 1225487 = 1838231) B1838231
theorem B1553195 : Blo 814346 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B1225529 : Blo 814346 1225529 := bstep (se 2 (by rfl) ⟨459573, by rfl⟩ : syracuseStep 1225529 = 919147) B919147
theorem B3486523 : Blo 814346 3486523 := bstep (se 1 (by rfl) ⟨2614892, by rfl⟩ : syracuseStep 3486523 = 5229785) B5229785
theorem B1225607 : Blo 814346 1225607 := bstep (se 1 (by rfl) ⟨919205, by rfl⟩ : syracuseStep 1225607 = 1838411) B1838411
theorem B1225643 : Blo 814346 1225643 := bstep (se 1 (by rfl) ⟨919232, by rfl⟩ : syracuseStep 1225643 = 1838465) B1838465
theorem B1225673 : Blo 814346 1225673 := bstep (se 2 (by rfl) ⟨459627, by rfl⟩ : syracuseStep 1225673 = 919255) B919255
theorem B1160249 : Blo 814346 1160249 := bstep (se 2 (by rfl) ⟨435093, by rfl⟩ : syracuseStep 1160249 = 870187) B870187
theorem B1225787 : Blo 814346 1225787 := bstep (se 1 (by rfl) ⟨919340, by rfl⟩ : syracuseStep 1225787 = 1838681) B1838681
theorem B1225847 : Blo 814346 1225847 := bstep (se 1 (by rfl) ⟨919385, by rfl⟩ : syracuseStep 1225847 = 1838771) B1838771
theorem B1160335 : Blo 814346 1160335 := bstep (se 1 (by rfl) ⟨870251, by rfl⟩ : syracuseStep 1160335 = 1740503) B1740503
theorem B1225871 : Blo 814346 1225871 := bstep (se 1 (by rfl) ⟨919403, by rfl⟩ : syracuseStep 1225871 = 1838807) B1838807
theorem B1160363 : Blo 814346 1160363 := bstep (se 1 (by rfl) ⟨870272, by rfl⟩ : syracuseStep 1160363 = 1740545) B1740545
theorem B1225913 : Blo 814346 1225913 := bstep (se 2 (by rfl) ⟨459717, by rfl⟩ : syracuseStep 1225913 = 919435) B919435
theorem B1225991 : Blo 814346 1225991 := bstep (se 1 (by rfl) ⟨919493, by rfl⟩ : syracuseStep 1225991 = 1838987) B1838987
theorem B1226027 : Blo 814346 1226027 := bstep (se 1 (by rfl) ⟨919520, by rfl⟩ : syracuseStep 1226027 = 1839041) B1839041
theorem B2209085 : Blo 814346 2209085 := bstep (se 3 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 2209085 = 828407) B828407
theorem B1226057 : Blo 814346 1226057 := bstep (se 2 (by rfl) ⟨459771, by rfl⟩ : syracuseStep 1226057 = 919543) B919543
theorem B52868537 : Blo 814346 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B1226171 : Blo 814346 1226171 := bstep (se 1 (by rfl) ⟨919628, by rfl⟩ : syracuseStep 1226171 = 1839257) B1839257
theorem B1226231 : Blo 814346 1226231 := bstep (se 1 (by rfl) ⟨919673, by rfl⟩ : syracuseStep 1226231 = 1839347) B1839347
theorem B1226255 : Blo 814346 1226255 := bstep (se 1 (by rfl) ⟨919691, by rfl⟩ : syracuseStep 1226255 = 1839383) B1839383
theorem B1226297 : Blo 814346 1226297 := bstep (se 2 (by rfl) ⟨459861, by rfl⟩ : syracuseStep 1226297 = 919723) B919723
theorem B1226375 : Blo 814346 1226375 := bstep (se 1 (by rfl) ⟨919781, by rfl⟩ : syracuseStep 1226375 = 1839563) B1839563
theorem B1226411 : Blo 814346 1226411 := bstep (se 1 (by rfl) ⟨919808, by rfl⟩ : syracuseStep 1226411 = 1839617) B1839617
theorem B1226441 : Blo 814346 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B9287459 : Blo 814346 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B1226555 : Blo 814346 1226555 := bstep (se 1 (by rfl) ⟨919916, by rfl⟩ : syracuseStep 1226555 = 1839833) B1839833
theorem B1226615 : Blo 814346 1226615 := bstep (se 1 (by rfl) ⟨919961, by rfl⟩ : syracuseStep 1226615 = 1839923) B1839923
theorem B1226639 : Blo 814346 1226639 := bstep (se 1 (by rfl) ⟨919979, by rfl⟩ : syracuseStep 1226639 = 1839959) B1839959
theorem B1226681 : Blo 814346 1226681 := bstep (se 2 (by rfl) ⟨460005, by rfl⟩ : syracuseStep 1226681 = 920011) B920011
theorem B1226759 : Blo 814346 1226759 := bstep (se 1 (by rfl) ⟨920069, by rfl⟩ : syracuseStep 1226759 = 1840139) B1840139
theorem B1226795 : Blo 814346 1226795 := bstep (se 1 (by rfl) ⟨920096, by rfl⟩ : syracuseStep 1226795 = 1840193) B1840193
theorem B1226825 : Blo 814346 1226825 := bstep (se 2 (by rfl) ⟨460059, by rfl⟩ : syracuseStep 1226825 = 920119) B920119
theorem B1226939 : Blo 814346 1226939 := bstep (se 1 (by rfl) ⟨920204, by rfl⟩ : syracuseStep 1226939 = 1840409) B1840409
theorem B1226999 : Blo 814346 1226999 := bstep (se 1 (by rfl) ⟨920249, by rfl⟩ : syracuseStep 1226999 = 1840499) B1840499
theorem B1227023 : Blo 814346 1227023 := bstep (se 1 (by rfl) ⟨920267, by rfl⟩ : syracuseStep 1227023 = 1840535) B1840535
theorem B1227065 : Blo 814346 1227065 := bstep (se 2 (by rfl) ⟨460149, by rfl⟩ : syracuseStep 1227065 = 920299) B920299
theorem B1227143 : Blo 814346 1227143 := bstep (se 1 (by rfl) ⟨920357, by rfl⟩ : syracuseStep 1227143 = 1840715) B1840715
theorem B1227179 : Blo 814346 1227179 := bstep (se 1 (by rfl) ⟨920384, by rfl⟩ : syracuseStep 1227179 = 1840769) B1840769
theorem B3094969 : Blo 814346 3094969 := bstep (se 2 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 3094969 = 2321227) B2321227
theorem B1227209 : Blo 814346 1227209 := bstep (se 2 (by rfl) ⟨460203, by rfl⟩ : syracuseStep 1227209 = 920407) B920407
theorem B9943505 : Blo 814346 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B1227323 : Blo 814346 1227323 := bstep (se 1 (by rfl) ⟨920492, by rfl⟩ : syracuseStep 1227323 = 1840985) B1840985
theorem B1227383 : Blo 814346 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B1227407 : Blo 814346 1227407 := bstep (se 1 (by rfl) ⟨920555, by rfl⟩ : syracuseStep 1227407 = 1841111) B1841111
theorem B1227449 : Blo 814346 1227449 := bstep (se 2 (by rfl) ⟨460293, by rfl⟩ : syracuseStep 1227449 = 920587) B920587
theorem B1653547 : Blo 814346 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B10468439 : Blo 814346 10468439 := bstep (se 1 (by rfl) ⟨7851329, by rfl⟩ : syracuseStep 10468439 = 15702659) B15702659
theorem B1031287 : Blo 814346 1031287 := bstep (se 1 (by rfl) ⟨773465, by rfl⟩ : syracuseStep 1031287 = 1546931) B1546931
theorem B3718345 : Blo 814346 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B1031611 : Blo 814346 1031611 := bstep (se 1 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 1031611 = 1547417) B1547417
theorem B4406795 : Blo 814346 4406795 := bstep (se 1 (by rfl) ⟨3305096, by rfl⟩ : syracuseStep 4406795 = 6610193) B6610193
theorem B48381533 : Blo 814346 48381533 := bstep (se 3 (by rfl) ⟨9071537, by rfl⟩ : syracuseStep 48381533 = 18143075) B18143075
theorem B1163279 : Blo 814346 1163279 := bstep (se 1 (by rfl) ⟨872459, by rfl⟩ : syracuseStep 1163279 = 1744919) B1744919
theorem B8503319 : Blo 814346 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B1032583 : Blo 814346 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B8372929 : Blo 814346 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B1033003 : Blo 814346 1033003 := bstep (se 1 (by rfl) ⟨774752, by rfl⟩ : syracuseStep 1033003 = 1549505) B1549505
theorem B1033231 : Blo 814346 1033231 := bstep (se 1 (by rfl) ⟨774923, by rfl⟩ : syracuseStep 1033231 = 1549847) B1549847
theorem B1492115 : Blo 814346 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B3097871 : Blo 814346 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B1033975 : Blo 814346 1033975 := bstep (se 1 (by rfl) ⟨775481, by rfl⟩ : syracuseStep 1033975 = 1550963) B1550963
theorem B1034299 : Blo 814346 1034299 := bstep (se 1 (by rfl) ⟨775724, by rfl⟩ : syracuseStep 1034299 = 1551449) B1551449
theorem B4638991 : Blo 814346 4638991 := bstep (se 1 (by rfl) ⟨3479243, by rfl⟩ : syracuseStep 4638991 = 6958487) B6958487
theorem B1034795 : Blo 814346 1034795 := bstep (se 1 (by rfl) ⟨776096, by rfl⟩ : syracuseStep 1034795 = 1552193) B1552193
theorem B79317569 : Blo 814346 79317569 := bstep (se 2 (by rfl) ⟨29744088, by rfl⟩ : syracuseStep 79317569 = 59488177) B59488177
theorem B6965837 : Blo 814346 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B3983959 : Blo 814346 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B1035271 : Blo 814346 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B2936249 : Blo 814346 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B4640267 : Blo 814346 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B2936407 : Blo 814346 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B2477753 : Blo 814346 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B4640449 : Blo 814346 4640449 := bstep (se 2 (by rfl) ⟨1740168, by rfl⟩ : syracuseStep 4640449 = 3480337) B3480337
theorem B1658809 : Blo 814346 1658809 := bstep (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) B1244107
theorem B8376331 : Blo 814346 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B3494279 : Blo 814346 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B3101075 : Blo 814346 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B13587011 : Blo 814346 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B2511703 : Blo 814346 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B3920957 : Blo 814346 3920957 := bstep (se 3 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 3920957 = 1470359) B1470359
theorem B5363003 : Blo 814346 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B6968875 : Blo 814346 6968875 := bstep (se 1 (by rfl) ⟨5226656, by rfl⟩ : syracuseStep 6968875 = 10453313) B10453313
theorem B11753059 : Blo 814346 11753059 := bstep (se 1 (by rfl) ⟨8814794, by rfl⟩ : syracuseStep 11753059 = 17629589) B17629589
theorem B3102731 : Blo 814346 3102731 := bstep (se 1 (by rfl) ⟨2327048, by rfl⟩ : syracuseStep 3102731 = 4654097) B4654097
theorem B2480161 : Blo 814346 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B2513015 : Blo 814346 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B9066937 : Blo 814346 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B28269121 : Blo 814346 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B5233423 : Blo 814346 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B2480939 : Blo 814346 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B1104683 : Blo 814346 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B3922955 : Blo 814346 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B1105159 : Blo 814346 1105159 := bstep (se 1 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 1105159 = 1657739) B1657739
theorem B1007239 : Blo 814346 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B1859219 : Blo 814346 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B9297665 : Blo 814346 9297665 := bstep (se 2 (by rfl) ⟨3486624, by rfl⟩ : syracuseStep 9297665 = 6973249) B6973249
theorem B4644641 : Blo 814346 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B3727939 : Blo 814346 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B2942189 : Blo 814346 2942189 := bstep (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) B1103321
theorem B2319769 : Blo 814346 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B13231795 : Blo 814346 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B2320157 : Blo 814346 2320157 := bstep (se 3 (by rfl) ⟨435029, by rfl⟩ : syracuseStep 2320157 = 870059) B870059
theorem B3106619 : Blo 814346 3106619 := bstep (se 1 (by rfl) ⟨2329964, by rfl⟩ : syracuseStep 3106619 = 4659929) B4659929
theorem B1959767 : Blo 814346 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B3532679 : Blo 814346 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B1239241 : Blo 814346 1239241 := bstep (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) B929431
theorem B1468687 : Blo 814346 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B3107105 : Blo 814346 3107105 := bstep (se 2 (by rfl) ⟨1165164, by rfl⟩ : syracuseStep 3107105 = 2330329) B2330329
theorem B2615611 : Blo 814346 2615611 := bstep (se 1 (by rfl) ⟨1961708, by rfl⟩ : syracuseStep 2615611 = 3923417) B3923417
theorem B6613433 : Blo 814346 6613433 := bstep (se 2 (by rfl) ⟨2480037, by rfl⟩ : syracuseStep 6613433 = 4960075) B4960075
theorem B17885731 : Blo 814346 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B4123223 : Blo 814346 4123223 := bstep (se 1 (by rfl) ⟨3092417, by rfl⟩ : syracuseStep 4123223 = 6184835) B6184835
theorem B9300581 : Blo 814346 9300581 := bstep (se 4 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 9300581 = 1743859) B1743859
theorem B2616097 : Blo 814346 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B4647739 : Blo 814346 4647739 := bstep (se 1 (by rfl) ⟨3485804, by rfl⟩ : syracuseStep 4647739 = 6971609) B6971609
theorem B1862585 : Blo 814346 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B5237783 : Blo 814346 5237783 := bstep (se 1 (by rfl) ⟨3928337, by rfl⟩ : syracuseStep 5237783 = 7856675) B7856675
theorem B4123709 : Blo 814346 4123709 := bstep (se 3 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 4123709 = 1546391) B1546391
theorem B814351 : Blo 814346 814351 := bstep (se 1 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 814351 = 1221527) B1221527
theorem B814395 : Blo 814346 814395 := bstep (se 1 (by rfl) ⟨610796, by rfl⟩ : syracuseStep 814395 = 1221593) B1221593
theorem B814471 : Blo 814346 814471 := bstep (se 1 (by rfl) ⟨610853, by rfl⟩ : syracuseStep 814471 = 1221707) B1221707
theorem B814479 : Blo 814346 814479 := bstep (se 1 (by rfl) ⟨610859, by rfl⟩ : syracuseStep 814479 = 1221719) B1221719
theorem B814523 : Blo 814346 814523 := bstep (se 1 (by rfl) ⟨610892, by rfl⟩ : syracuseStep 814523 = 1221785) B1221785
theorem B814599 : Blo 814346 814599 := bstep (se 1 (by rfl) ⟨610949, by rfl⟩ : syracuseStep 814599 = 1221899) B1221899
theorem B814607 : Blo 814346 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B1306127 : Blo 814346 1306127 := bstep (se 1 (by rfl) ⟨979595, by rfl⟩ : syracuseStep 1306127 = 1959191) B1959191
theorem B814651 : Blo 814346 814651 := bstep (se 1 (by rfl) ⟨610988, by rfl⟩ : syracuseStep 814651 = 1221977) B1221977
theorem B1470071 : Blo 814346 1470071 := bstep (se 1 (by rfl) ⟨1102553, by rfl⟩ : syracuseStep 1470071 = 2205107) B2205107
theorem B814727 : Blo 814346 814727 := bstep (se 1 (by rfl) ⟨611045, by rfl⟩ : syracuseStep 814727 = 1222091) B1222091
theorem B814735 : Blo 814346 814735 := bstep (se 1 (by rfl) ⟨611051, by rfl⟩ : syracuseStep 814735 = 1222103) B1222103
theorem B814779 : Blo 814346 814779 := bstep (se 1 (by rfl) ⟨611084, by rfl⟩ : syracuseStep 814779 = 1222169) B1222169
theorem B6975233 : Blo 814346 6975233 := bstep (se 2 (by rfl) ⟨2615712, by rfl⟩ : syracuseStep 6975233 = 5231425) B5231425
theorem B814855 : Blo 814346 814855 := bstep (se 1 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 814855 = 1222283) B1222283
theorem B814863 : Blo 814346 814863 := bstep (se 1 (by rfl) ⟨611147, by rfl⟩ : syracuseStep 814863 = 1222295) B1222295
theorem B1240847 : Blo 814346 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B814907 : Blo 814346 814907 := bstep (se 1 (by rfl) ⟨611180, by rfl⟩ : syracuseStep 814907 = 1222361) B1222361
theorem B814983 : Blo 814346 814983 := bstep (se 1 (by rfl) ⟨611237, by rfl⟩ : syracuseStep 814983 = 1222475) B1222475
theorem B814991 : Blo 814346 814991 := bstep (se 1 (by rfl) ⟨611243, by rfl⟩ : syracuseStep 814991 = 1222487) B1222487
theorem B10481561 : Blo 814346 10481561 := bstep (se 2 (by rfl) ⟨3930585, by rfl⟩ : syracuseStep 10481561 = 7861171) B7861171
theorem B815035 : Blo 814346 815035 := bstep (se 1 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 815035 = 1222553) B1222553
theorem B815111 : Blo 814346 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B815119 : Blo 814346 815119 := bstep (se 1 (by rfl) ⟨611339, by rfl⟩ : syracuseStep 815119 = 1222679) B1222679
theorem B1306639 : Blo 814346 1306639 := bstep (se 1 (by rfl) ⟨979979, by rfl⟩ : syracuseStep 1306639 = 1959959) B1959959
theorem B11300887 : Blo 814346 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B9302039 : Blo 814346 9302039 := bstep (se 1 (by rfl) ⟨6976529, by rfl⟩ : syracuseStep 9302039 = 13953059) B13953059
theorem B815163 : Blo 814346 815163 := bstep (se 1 (by rfl) ⟨611372, by rfl⟩ : syracuseStep 815163 = 1222745) B1222745
theorem B4255811 : Blo 814346 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B815239 : Blo 814346 815239 := bstep (se 1 (by rfl) ⟨611429, by rfl⟩ : syracuseStep 815239 = 1222859) B1222859
theorem B815247 : Blo 814346 815247 := bstep (se 1 (by rfl) ⟨611435, by rfl⟩ : syracuseStep 815247 = 1222871) B1222871
theorem B815291 : Blo 814346 815291 := bstep (se 1 (by rfl) ⟨611468, by rfl⟩ : syracuseStep 815291 = 1222937) B1222937
theorem B4649197 : Blo 814346 4649197 := bstep (se 3 (by rfl) ⟨871724, by rfl⟩ : syracuseStep 4649197 = 1743449) B1743449
theorem B815367 : Blo 814346 815367 := bstep (se 1 (by rfl) ⟨611525, by rfl⟩ : syracuseStep 815367 = 1223051) B1223051
theorem B815375 : Blo 814346 815375 := bstep (se 1 (by rfl) ⟨611531, by rfl⟩ : syracuseStep 815375 = 1223063) B1223063
theorem B2322731 : Blo 814346 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B815419 : Blo 814346 815419 := bstep (se 1 (by rfl) ⟨611564, by rfl⟩ : syracuseStep 815419 = 1223129) B1223129
theorem B815495 : Blo 814346 815495 := bstep (se 1 (by rfl) ⟨611621, by rfl⟩ : syracuseStep 815495 = 1223243) B1223243
theorem B815503 : Blo 814346 815503 := bstep (se 1 (by rfl) ⟨611627, by rfl⟩ : syracuseStep 815503 = 1223255) B1223255
theorem B815547 : Blo 814346 815547 := bstep (se 1 (by rfl) ⟨611660, by rfl⟩ : syracuseStep 815547 = 1223321) B1223321
theorem B815623 : Blo 814346 815623 := bstep (se 1 (by rfl) ⟨611717, by rfl⟩ : syracuseStep 815623 = 1223435) B1223435
theorem B815631 : Blo 814346 815631 := bstep (se 1 (by rfl) ⟨611723, by rfl⟩ : syracuseStep 815631 = 1223447) B1223447
theorem B1864225 : Blo 814346 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B979499 : Blo 814346 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B815675 : Blo 814346 815675 := bstep (se 1 (by rfl) ⟨611756, by rfl⟩ : syracuseStep 815675 = 1223513) B1223513
theorem B6287939 : Blo 814346 6287939 := bstep (se 1 (by rfl) ⟨4715954, by rfl⟩ : syracuseStep 6287939 = 9431909) B9431909
theorem B1962611 : Blo 814346 1962611 := bstep (se 1 (by rfl) ⟨1471958, by rfl⟩ : syracuseStep 1962611 = 2943917) B2943917
theorem B815751 : Blo 814346 815751 := bstep (se 1 (by rfl) ⟨611813, by rfl⟩ : syracuseStep 815751 = 1223627) B1223627
theorem B2519687 : Blo 814346 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B815759 : Blo 814346 815759 := bstep (se 1 (by rfl) ⟨611819, by rfl⟩ : syracuseStep 815759 = 1223639) B1223639
theorem B31847093 : Blo 814346 31847093 := bstep (se 5 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 31847093 = 2985665) B2985665
theorem B815803 : Blo 814346 815803 := bstep (se 1 (by rfl) ⟨611852, by rfl⟩ : syracuseStep 815803 = 1223705) B1223705
theorem B815879 : Blo 814346 815879 := bstep (se 1 (by rfl) ⟨611909, by rfl⟩ : syracuseStep 815879 = 1223819) B1223819
theorem B815887 : Blo 814346 815887 := bstep (se 1 (by rfl) ⟨611915, by rfl⟩ : syracuseStep 815887 = 1223831) B1223831
theorem B4125491 : Blo 814346 4125491 := bstep (se 1 (by rfl) ⟨3094118, by rfl⟩ : syracuseStep 4125491 = 6188237) B6188237
theorem B815931 : Blo 814346 815931 := bstep (se 1 (by rfl) ⟨611948, by rfl⟩ : syracuseStep 815931 = 1223897) B1223897
theorem B816007 : Blo 814346 816007 := bstep (se 1 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 816007 = 1224011) B1224011
theorem B816015 : Blo 814346 816015 := bstep (se 1 (by rfl) ⟨612011, by rfl⟩ : syracuseStep 816015 = 1224023) B1224023
theorem B13595573 : Blo 814346 13595573 := bstep (se 5 (by rfl) ⟨637292, by rfl⟩ : syracuseStep 13595573 = 1274585) B1274585
theorem B816059 : Blo 814346 816059 := bstep (se 1 (by rfl) ⟨612044, by rfl⟩ : syracuseStep 816059 = 1224089) B1224089
theorem B816135 : Blo 814346 816135 := bstep (se 1 (by rfl) ⟨612101, by rfl⟩ : syracuseStep 816135 = 1224203) B1224203
theorem B816143 : Blo 814346 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B816187 : Blo 814346 816187 := bstep (se 1 (by rfl) ⟨612140, by rfl⟩ : syracuseStep 816187 = 1224281) B1224281
theorem B4125815 : Blo 814346 4125815 := bstep (se 1 (by rfl) ⟨3094361, by rfl⟩ : syracuseStep 4125815 = 6188723) B6188723
theorem B1307767 : Blo 814346 1307767 := bstep (se 1 (by rfl) ⟨980825, by rfl⟩ : syracuseStep 1307767 = 1961651) B1961651
theorem B816263 : Blo 814346 816263 := bstep (se 1 (by rfl) ⟨612197, by rfl⟩ : syracuseStep 816263 = 1224395) B1224395
theorem B816271 : Blo 814346 816271 := bstep (se 1 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 816271 = 1224407) B1224407
theorem B816315 : Blo 814346 816315 := bstep (se 1 (by rfl) ⟨612236, by rfl⟩ : syracuseStep 816315 = 1224473) B1224473
theorem B816391 : Blo 814346 816391 := bstep (se 1 (by rfl) ⟨612293, by rfl⟩ : syracuseStep 816391 = 1224587) B1224587
theorem B816399 : Blo 814346 816399 := bstep (se 1 (by rfl) ⟨612299, by rfl⟩ : syracuseStep 816399 = 1224599) B1224599
theorem B816443 : Blo 814346 816443 := bstep (se 1 (by rfl) ⟨612332, by rfl⟩ : syracuseStep 816443 = 1224665) B1224665
theorem B2061683 : Blo 814346 2061683 := bstep (se 1 (by rfl) ⟨1546262, by rfl⟩ : syracuseStep 2061683 = 3092525) B3092525
theorem B1832327 : Blo 814346 1832327 := bstep (se 1 (by rfl) ⟨1374245, by rfl⟩ : syracuseStep 1832327 = 2748491) B2748491
theorem B816519 : Blo 814346 816519 := bstep (se 1 (by rfl) ⟨612389, by rfl⟩ : syracuseStep 816519 = 1224779) B1224779
theorem B816527 : Blo 814346 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B20903345 : Blo 814346 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B816571 : Blo 814346 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B816647 : Blo 814346 816647 := bstep (se 1 (by rfl) ⟨612485, by rfl⟩ : syracuseStep 816647 = 1224971) B1224971
theorem B816655 : Blo 814346 816655 := bstep (se 1 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 816655 = 1224983) B1224983
theorem B1865231 : Blo 814346 1865231 := bstep (se 1 (by rfl) ⟨1398923, by rfl⟩ : syracuseStep 1865231 = 2797847) B2797847
theorem B1832507 : Blo 814346 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B816699 : Blo 814346 816699 := bstep (se 1 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 816699 = 1225049) B1225049
theorem B816775 : Blo 814346 816775 := bstep (se 1 (by rfl) ⟨612581, by rfl⟩ : syracuseStep 816775 = 1225163) B1225163
theorem B816783 : Blo 814346 816783 := bstep (se 1 (by rfl) ⟨612587, by rfl⟩ : syracuseStep 816783 = 1225175) B1225175
theorem B1832633 : Blo 814346 1832633 := bstep (se 2 (by rfl) ⟨687237, by rfl⟩ : syracuseStep 1832633 = 1374475) B1374475
theorem B816827 : Blo 814346 816827 := bstep (se 1 (by rfl) ⟨612620, by rfl⟩ : syracuseStep 816827 = 1225241) B1225241
theorem B2488009 : Blo 814346 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B816903 : Blo 814346 816903 := bstep (se 1 (by rfl) ⟨612677, by rfl⟩ : syracuseStep 816903 = 1225355) B1225355
theorem B816911 : Blo 814346 816911 := bstep (se 1 (by rfl) ⟨612683, by rfl⟩ : syracuseStep 816911 = 1225367) B1225367
theorem B816955 : Blo 814346 816955 := bstep (se 1 (by rfl) ⟨612716, by rfl⟩ : syracuseStep 816955 = 1225433) B1225433
theorem B7370585 : Blo 814346 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B3929971 : Blo 814346 3929971 := bstep (se 1 (by rfl) ⟨2947478, by rfl⟩ : syracuseStep 3929971 = 5894957) B5894957
theorem B2062199 : Blo 814346 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B817031 : Blo 814346 817031 := bstep (se 1 (by rfl) ⟨612773, by rfl⟩ : syracuseStep 817031 = 1225547) B1225547
theorem B817039 : Blo 814346 817039 := bstep (se 1 (by rfl) ⟨612779, by rfl⟩ : syracuseStep 817039 = 1225559) B1225559
theorem B2324371 : Blo 814346 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B817083 : Blo 814346 817083 := bstep (se 1 (by rfl) ⟨612812, by rfl⟩ : syracuseStep 817083 = 1225625) B1225625
theorem B817159 : Blo 814346 817159 := bstep (se 1 (by rfl) ⟨612869, by rfl⟩ : syracuseStep 817159 = 1225739) B1225739
theorem B1832975 : Blo 814346 1832975 := bstep (se 1 (by rfl) ⟨1374731, by rfl⟩ : syracuseStep 1832975 = 2749463) B2749463
theorem B817167 : Blo 814346 817167 := bstep (se 1 (by rfl) ⟨612875, by rfl⟩ : syracuseStep 817167 = 1225751) B1225751
theorem B1832993 : Blo 814346 1832993 := bstep (se 2 (by rfl) ⟨687372, by rfl⟩ : syracuseStep 1832993 = 1374745) B1374745
theorem B817211 : Blo 814346 817211 := bstep (se 1 (by rfl) ⟨612908, by rfl⟩ : syracuseStep 817211 = 1225817) B1225817
theorem B4126787 : Blo 814346 4126787 := bstep (se 1 (by rfl) ⟨3095090, by rfl⟩ : syracuseStep 4126787 = 6190181) B6190181
theorem B6977623 : Blo 814346 6977623 := bstep (se 1 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 6977623 = 10466435) B10466435
theorem B817287 : Blo 814346 817287 := bstep (se 1 (by rfl) ⟨612965, by rfl⟩ : syracuseStep 817287 = 1225931) B1225931
theorem B817295 : Blo 814346 817295 := bstep (se 1 (by rfl) ⟨612971, by rfl⟩ : syracuseStep 817295 = 1225943) B1225943
theorem B4651181 : Blo 814346 4651181 := bstep (se 3 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 4651181 = 1744193) B1744193
theorem B817339 : Blo 814346 817339 := bstep (se 1 (by rfl) ⟨613004, by rfl⟩ : syracuseStep 817339 = 1226009) B1226009
theorem B16152817 : Blo 814346 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B817415 : Blo 814346 817415 := bstep (se 1 (by rfl) ⟨613061, by rfl⟩ : syracuseStep 817415 = 1226123) B1226123
theorem B817423 : Blo 814346 817423 := bstep (se 1 (by rfl) ⟨613067, by rfl⟩ : syracuseStep 817423 = 1226135) B1226135
theorem B1964303 : Blo 814346 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1308971 : Blo 814346 1308971 := bstep (se 1 (by rfl) ⟨981728, by rfl⟩ : syracuseStep 1308971 = 1963457) B1963457
theorem B817467 : Blo 814346 817467 := bstep (se 1 (by rfl) ⟨613100, by rfl⟩ : syracuseStep 817467 = 1226201) B1226201
theorem B1374583 : Blo 814346 1374583 := bstep (se 1 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 1374583 = 2061875) B2061875
theorem B1833335 : Blo 814346 1833335 := bstep (se 1 (by rfl) ⟨1375001, by rfl⟩ : syracuseStep 1833335 = 2750003) B2750003
theorem B4127111 : Blo 814346 4127111 := bstep (se 1 (by rfl) ⟨3095333, by rfl⟩ : syracuseStep 4127111 = 6190667) B6190667
theorem B817543 : Blo 814346 817543 := bstep (se 1 (by rfl) ⟨613157, by rfl⟩ : syracuseStep 817543 = 1226315) B1226315
theorem B817551 : Blo 814346 817551 := bstep (se 1 (by rfl) ⟨613163, by rfl⟩ : syracuseStep 817551 = 1226327) B1226327
theorem B2750867 : Blo 814346 2750867 := bstep (se 1 (by rfl) ⟨2063150, by rfl⟩ : syracuseStep 2750867 = 4126301) B4126301
theorem B1767827 : Blo 814346 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B817595 : Blo 814346 817595 := bstep (se 1 (by rfl) ⟨613196, by rfl⟩ : syracuseStep 817595 = 1226393) B1226393
theorem B817671 : Blo 814346 817671 := bstep (se 1 (by rfl) ⟨613253, by rfl⟩ : syracuseStep 817671 = 1226507) B1226507
theorem B817679 : Blo 814346 817679 := bstep (se 1 (by rfl) ⟨613259, by rfl⟩ : syracuseStep 817679 = 1226519) B1226519
theorem B1833515 : Blo 814346 1833515 := bstep (se 1 (by rfl) ⟨1375136, by rfl⟩ : syracuseStep 1833515 = 2750273) B2750273
theorem B1374779 : Blo 814346 1374779 := bstep (se 1 (by rfl) ⟨1031084, by rfl⟩ : syracuseStep 1374779 = 2062169) B2062169
theorem B4192829 : Blo 814346 4192829 := bstep (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) B1572311
theorem B817723 : Blo 814346 817723 := bstep (se 1 (by rfl) ⟨613292, by rfl⟩ : syracuseStep 817723 = 1226585) B1226585
theorem B817799 : Blo 814346 817799 := bstep (se 1 (by rfl) ⟨613349, by rfl⟩ : syracuseStep 817799 = 1226699) B1226699
theorem B817807 : Blo 814346 817807 := bstep (se 1 (by rfl) ⟨613355, by rfl⟩ : syracuseStep 817807 = 1226711) B1226711
theorem B817851 : Blo 814346 817851 := bstep (se 1 (by rfl) ⟨613388, by rfl⟩ : syracuseStep 817851 = 1226777) B1226777
theorem B916231 : Blo 814346 916231 := bstep (se 1 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 916231 = 1374347) B1374347
theorem B981767 : Blo 814346 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B817927 : Blo 814346 817927 := bstep (se 1 (by rfl) ⟨613445, by rfl⟩ : syracuseStep 817927 = 1226891) B1226891
theorem B7535375 : Blo 814346 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B817935 : Blo 814346 817935 := bstep (se 1 (by rfl) ⟨613451, by rfl⟩ : syracuseStep 817935 = 1226903) B1226903
theorem B817979 : Blo 814346 817979 := bstep (se 1 (by rfl) ⟨613484, by rfl⟩ : syracuseStep 817979 = 1226969) B1226969
theorem B2063191 : Blo 814346 2063191 := bstep (se 1 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 2063191 = 3094787) B3094787
theorem B818055 : Blo 814346 818055 := bstep (se 1 (by rfl) ⟨613541, by rfl⟩ : syracuseStep 818055 = 1227083) B1227083
theorem B818063 : Blo 814346 818063 := bstep (se 1 (by rfl) ⟨613547, by rfl⟩ : syracuseStep 818063 = 1227095) B1227095
theorem B1833875 : Blo 814346 1833875 := bstep (se 1 (by rfl) ⟨1375406, by rfl⟩ : syracuseStep 1833875 = 2750813) B2750813
theorem B916411 : Blo 814346 916411 := bstep (se 1 (by rfl) ⟨687308, by rfl⟩ : syracuseStep 916411 = 1374617) B1374617
theorem B818107 : Blo 814346 818107 := bstep (se 1 (by rfl) ⟨613580, by rfl⟩ : syracuseStep 818107 = 1227161) B1227161
theorem B1375177 : Blo 814346 1375177 := bstep (se 2 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 1375177 = 1031383) B1031383
theorem B1833929 : Blo 814346 1833929 := bstep (se 2 (by rfl) ⟨687723, by rfl⟩ : syracuseStep 1833929 = 1375447) B1375447
theorem B818183 : Blo 814346 818183 := bstep (se 1 (by rfl) ⟨613637, by rfl⟩ : syracuseStep 818183 = 1227275) B1227275
theorem B1965071 : Blo 814346 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B818191 : Blo 814346 818191 := bstep (se 1 (by rfl) ⟨613643, by rfl⟩ : syracuseStep 818191 = 1227287) B1227287
theorem B818235 : Blo 814346 818235 := bstep (se 1 (by rfl) ⟨613676, by rfl⟩ : syracuseStep 818235 = 1227353) B1227353
theorem B2063495 : Blo 814346 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B818311 : Blo 814346 818311 := bstep (se 1 (by rfl) ⟨613733, by rfl⟩ : syracuseStep 818311 = 1227467) B1227467
theorem B818319 : Blo 814346 818319 := bstep (se 1 (by rfl) ⟨613739, by rfl⟩ : syracuseStep 818319 = 1227479) B1227479
theorem B2063627 : Blo 814346 2063627 := bstep (se 1 (by rfl) ⟨1547720, by rfl⟩ : syracuseStep 2063627 = 3095441) B3095441
theorem B14155067 : Blo 814346 14155067 := bstep (se 1 (by rfl) ⟨10616300, by rfl⟩ : syracuseStep 14155067 = 21232601) B21232601
theorem B916879 : Blo 814346 916879 := bstep (se 1 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 916879 = 1375319) B1375319
theorem B1473977 : Blo 814346 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B2326103 : Blo 814346 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B1375879 : Blo 814346 1375879 := bstep (se 1 (by rfl) ⟨1031909, by rfl⟩ : syracuseStep 1375879 = 2063819) B2063819
theorem B1834631 : Blo 814346 1834631 := bstep (se 1 (by rfl) ⟨1375973, by rfl⟩ : syracuseStep 1834631 = 2751947) B2751947
theorem B2064143 : Blo 814346 2064143 := bstep (se 1 (by rfl) ⟨1548107, by rfl⟩ : syracuseStep 2064143 = 3096215) B3096215
theorem B2752271 : Blo 814346 2752271 := bstep (se 1 (by rfl) ⟨2064203, by rfl⟩ : syracuseStep 2752271 = 4128407) B4128407
theorem B1834811 : Blo 814346 1834811 := bstep (se 1 (by rfl) ⟨1376108, by rfl⟩ : syracuseStep 1834811 = 2752217) B2752217
theorem B982843 : Blo 814346 982843 := bstep (se 1 (by rfl) ⟨737132, by rfl⟩ : syracuseStep 982843 = 1474265) B1474265
theorem B3309427 : Blo 814346 3309427 := bstep (se 1 (by rfl) ⟨2482070, by rfl⟩ : syracuseStep 3309427 = 4964141) B4964141
theorem B917383 : Blo 814346 917383 := bstep (se 1 (by rfl) ⟨688037, by rfl⟩ : syracuseStep 917383 = 1376075) B1376075
theorem B2064275 : Blo 814346 2064275 := bstep (se 1 (by rfl) ⟨1548206, by rfl⟩ : syracuseStep 2064275 = 3096413) B3096413
theorem B1834937 : Blo 814346 1834937 := bstep (se 2 (by rfl) ⟨688101, by rfl⟩ : syracuseStep 1834937 = 1376203) B1376203
theorem B4653071 : Blo 814346 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B5668879 : Blo 814346 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B1835027 : Blo 814346 1835027 := bstep (se 1 (by rfl) ⟨1376270, by rfl⟩ : syracuseStep 1835027 = 2752541) B2752541
theorem B5898329 : Blo 814346 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B2949367 : Blo 814346 2949367 := bstep (se 1 (by rfl) ⟨2212025, by rfl⟩ : syracuseStep 2949367 = 4424051) B4424051
theorem B1835369 : Blo 814346 1835369 := bstep (se 2 (by rfl) ⟨688263, by rfl⟩ : syracuseStep 1835369 = 1376527) B1376527
theorem B1376777 : Blo 814346 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B1573433 : Blo 814346 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B918139 : Blo 814346 918139 := bstep (se 1 (by rfl) ⟨688604, by rfl⟩ : syracuseStep 918139 = 1377209) B1377209
theorem B1376939 : Blo 814346 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B47121101 : Blo 814346 47121101 := bstep (se 3 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 47121101 = 17670413) B17670413
theorem B10486529 : Blo 814346 10486529 := bstep (se 2 (by rfl) ⟨3932448, by rfl⟩ : syracuseStep 10486529 = 7864897) B7864897
theorem B2065247 : Blo 814346 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1835963 : Blo 814346 1835963 := bstep (se 1 (by rfl) ⟨1376972, by rfl⟩ : syracuseStep 1835963 = 2753945) B2753945
theorem B1836089 : Blo 814346 1836089 := bstep (se 2 (by rfl) ⟨688533, by rfl⟩ : syracuseStep 1836089 = 1377067) B1377067
theorem B1377337 : Blo 814346 1377337 := bstep (se 2 (by rfl) ⟨516501, by rfl⟩ : syracuseStep 1377337 = 1033003) B1033003
theorem B918607 : Blo 814346 918607 := bstep (se 1 (by rfl) ⟨688955, by rfl⟩ : syracuseStep 918607 = 1377911) B1377911
theorem B1377479 : Blo 814346 1377479 := bstep (se 1 (by rfl) ⟨1033109, by rfl⟩ : syracuseStep 1377479 = 2066219) B2066219
theorem B2753783 : Blo 814346 2753783 := bstep (se 1 (by rfl) ⟨2065337, by rfl⟩ : syracuseStep 2753783 = 4130675) B4130675
theorem B1377641 : Blo 814346 1377641 := bstep (se 2 (by rfl) ⟨516615, by rfl⟩ : syracuseStep 1377641 = 1033231) B1033231
theorem B1836431 : Blo 814346 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B919003 : Blo 814346 919003 := bstep (se 1 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 919003 = 1378505) B1378505
theorem B2065945 : Blo 814346 2065945 := bstep (se 2 (by rfl) ⟨774729, by rfl⟩ : syracuseStep 2065945 = 1549459) B1549459
theorem B2754107 : Blo 814346 2754107 := bstep (se 1 (by rfl) ⟨2065580, by rfl⟩ : syracuseStep 2754107 = 4131161) B4131161
theorem B1836755 : Blo 814346 1836755 := bstep (se 1 (by rfl) ⟨1377566, by rfl⟩ : syracuseStep 1836755 = 2755133) B2755133
theorem B1378039 : Blo 814346 1378039 := bstep (se 1 (by rfl) ⟨1033529, by rfl⟩ : syracuseStep 1378039 = 2067059) B2067059
theorem B2754377 : Blo 814346 2754377 := bstep (se 2 (by rfl) ⟨1032891, by rfl⟩ : syracuseStep 2754377 = 2065783) B2065783
theorem B2066249 : Blo 814346 2066249 := bstep (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) B1549687
theorem B919471 : Blo 814346 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1378235 : Blo 814346 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B1378343 : Blo 814346 1378343 := bstep (se 1 (by rfl) ⟨1033757, by rfl⟩ : syracuseStep 1378343 = 2067515) B2067515
theorem B1378633 : Blo 814346 1378633 := bstep (se 2 (by rfl) ⟨516987, by rfl⟩ : syracuseStep 1378633 = 1033975) B1033975
theorem B919903 : Blo 814346 919903 := bstep (se 1 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 919903 = 1379855) B1379855
theorem B1378667 : Blo 814346 1378667 := bstep (se 1 (by rfl) ⟨1034000, by rfl⟩ : syracuseStep 1378667 = 2068001) B2068001
theorem B1837691 : Blo 814346 1837691 := bstep (se 1 (by rfl) ⟨1378268, by rfl⟩ : syracuseStep 1837691 = 2756537) B2756537
theorem B920263 : Blo 814346 920263 := bstep (se 1 (by rfl) ⟨690197, by rfl⟩ : syracuseStep 920263 = 1380395) B1380395
theorem B1837817 : Blo 814346 1837817 := bstep (se 2 (by rfl) ⟨689181, by rfl⟩ : syracuseStep 1837817 = 1378363) B1378363
theorem B1379065 : Blo 814346 1379065 := bstep (se 2 (by rfl) ⟨517149, by rfl⟩ : syracuseStep 1379065 = 1034299) B1034299
theorem B2329337 : Blo 814346 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2755511 : Blo 814346 2755511 := bstep (se 1 (by rfl) ⟨2066633, by rfl⟩ : syracuseStep 2755511 = 4133267) B4133267
theorem B2067383 : Blo 814346 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1838087 : Blo 814346 1838087 := bstep (se 1 (by rfl) ⟨1378565, by rfl⟩ : syracuseStep 1838087 = 2757131) B2757131
theorem B1379335 : Blo 814346 1379335 := bstep (se 1 (by rfl) ⟨1034501, by rfl⟩ : syracuseStep 1379335 = 2069003) B2069003
theorem B1838159 : Blo 814346 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B1379767 : Blo 814346 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B5311945 : Blo 814346 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B1838555 : Blo 814346 1838555 := bstep (se 1 (by rfl) ⟨1378916, by rfl⟩ : syracuseStep 1838555 = 2757833) B2757833
theorem B2756105 : Blo 814346 2756105 := bstep (se 2 (by rfl) ⟨1033539, by rfl⟩ : syracuseStep 2756105 = 2067079) B2067079
theorem B3575335 : Blo 814346 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B5312087 : Blo 814346 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B1379963 : Blo 814346 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B6196985 : Blo 814346 6196985 := bstep (se 2 (by rfl) ⟨2323869, by rfl⟩ : syracuseStep 6196985 = 4647739) B4647739
theorem B1839023 : Blo 814346 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B2068487 : Blo 814346 2068487 := bstep (se 1 (by rfl) ⟨1551365, by rfl⟩ : syracuseStep 2068487 = 3102731) B3102731
theorem B1380361 : Blo 814346 1380361 := bstep (se 2 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 1380361 = 1035271) B1035271
theorem B2068537 : Blo 814346 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B1675343 : Blo 814346 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1839275 : Blo 814346 1839275 := bstep (se 1 (by rfl) ⟨1379456, by rfl⟩ : syracuseStep 1839275 = 2758913) B2758913
theorem B1380523 : Blo 814346 1380523 := bstep (se 1 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 1380523 = 2070785) B2070785
theorem B2756969 : Blo 814346 2756969 := bstep (se 2 (by rfl) ⟨1033863, by rfl⟩ : syracuseStep 2756969 = 2067727) B2067727
theorem B2068841 : Blo 814346 2068841 := bstep (se 2 (by rfl) ⟨775815, by rfl⟩ : syracuseStep 2068841 = 1551631) B1551631
theorem B1380827 : Blo 814346 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1839815 : Blo 814346 1839815 := bstep (se 1 (by rfl) ⟨1379861, by rfl⟩ : syracuseStep 1839815 = 2759723) B2759723
theorem B2757563 : Blo 814346 2757563 := bstep (se 1 (by rfl) ⟨2068172, by rfl⟩ : syracuseStep 2757563 = 4136345) B4136345
theorem B6198443 : Blo 814346 6198443 := bstep (se 1 (by rfl) ⟨4648832, by rfl⟩ : syracuseStep 6198443 = 9297665) B9297665
theorem B1742185 : Blo 814346 1742185 := bstep (se 2 (by rfl) ⟨653319, by rfl⟩ : syracuseStep 1742185 = 1306639) B1306639
theorem B1840679 : Blo 814346 1840679 := bstep (se 1 (by rfl) ⟨1380509, by rfl⟩ : syracuseStep 1840679 = 2761019) B2761019
theorem B6198929 : Blo 814346 6198929 := bstep (se 2 (by rfl) ⟨2324598, by rfl⟩ : syracuseStep 6198929 = 4649197) B4649197
theorem B4658903 : Blo 814346 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B1546057 : Blo 814346 1546057 := bstep (se 2 (by rfl) ⟨579771, by rfl⟩ : syracuseStep 1546057 = 1159543) B1159543
theorem B1841003 : Blo 814346 1841003 := bstep (se 1 (by rfl) ⟨1380752, by rfl⟩ : syracuseStep 1841003 = 2761505) B2761505
theorem B1841057 : Blo 814346 1841057 := bstep (se 2 (by rfl) ⟨690396, by rfl⟩ : syracuseStep 1841057 = 1380793) B1380793
theorem B3348937 : Blo 814346 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B1546771 : Blo 814346 1546771 := bstep (se 1 (by rfl) ⟨1160078, by rfl⟩ : syracuseStep 1546771 = 2320157) B2320157
theorem B2071079 : Blo 814346 2071079 := bstep (se 1 (by rfl) ⟨1553309, by rfl⟩ : syracuseStep 2071079 = 3106619) B3106619
theorem B2759291 : Blo 814346 2759291 := bstep (se 1 (by rfl) ⟨2069468, by rfl⟩ : syracuseStep 2759291 = 4138937) B4138937
theorem B2759453 : Blo 814346 2759453 := bstep (se 3 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 2759453 = 1034795) B1034795
theorem B1743689 : Blo 814346 1743689 := bstep (se 2 (by rfl) ⟨653883, by rfl⟩ : syracuseStep 1743689 = 1307767) B1307767
theorem B1547113 : Blo 814346 1547113 := bstep (se 2 (by rfl) ⟨580167, by rfl⟩ : syracuseStep 1547113 = 1160335) B1160335
theorem B2071403 : Blo 814346 2071403 := bstep (se 1 (by rfl) ⟨1553552, by rfl⟩ : syracuseStep 2071403 = 3107105) B3107105
theorem B6200387 : Blo 814346 6200387 := bstep (se 1 (by rfl) ⟨4650290, by rfl⟩ : syracuseStep 6200387 = 9300581) B9300581
theorem B4136183 : Blo 814346 4136183 := bstep (se 1 (by rfl) ⟨3102137, by rfl⟩ : syracuseStep 4136183 = 6204275) B6204275
theorem B15670745 : Blo 814346 15670745 := bstep (se 2 (by rfl) ⟨5876529, by rfl⟩ : syracuseStep 15670745 = 11753059) B11753059
theorem B2760155 : Blo 814346 2760155 := bstep (se 1 (by rfl) ⟨2070116, by rfl⟩ : syracuseStep 2760155 = 4140233) B4140233
theorem B3317345 : Blo 814346 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B4136669 : Blo 814346 4136669 := bstep (se 3 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 4136669 = 1551251) B1551251
theorem B827231 : Blo 814346 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B6987707 : Blo 814346 6987707 := bstep (se 1 (by rfl) ⟨5240780, by rfl⟩ : syracuseStep 6987707 = 10481561) B10481561
theorem B6201359 : Blo 814346 6201359 := bstep (se 1 (by rfl) ⟨4651019, by rfl⟩ : syracuseStep 6201359 = 9302039) B9302039
theorem B2760857 : Blo 814346 2760857 := bstep (se 2 (by rfl) ⟨1035321, by rfl⟩ : syracuseStep 2760857 = 2070643) B2070643
theorem B1548487 : Blo 814346 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B21537089 : Blo 814346 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1679791 : Blo 814346 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B37692161 : Blo 814346 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B1221551 : Blo 814346 1221551 := bstep (se 1 (by rfl) ⟨916163, by rfl⟩ : syracuseStep 1221551 = 1832327) B1832327
theorem B13935563 : Blo 814346 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B1221641 : Blo 814346 1221641 := bstep (se 2 (by rfl) ⟨458115, by rfl⟩ : syracuseStep 1221641 = 916231) B916231
theorem B1221671 : Blo 814346 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B2204729 : Blo 814346 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B1221755 : Blo 814346 1221755 := bstep (se 1 (by rfl) ⟨916316, by rfl⟩ : syracuseStep 1221755 = 1832633) B1832633
theorem B1221881 : Blo 814346 1221881 := bstep (se 2 (by rfl) ⟨458205, by rfl⟩ : syracuseStep 1221881 = 916411) B916411
theorem B1221983 : Blo 814346 1221983 := bstep (se 1 (by rfl) ⟨916487, by rfl⟩ : syracuseStep 1221983 = 1832975) B1832975
theorem B1221995 : Blo 814346 1221995 := bstep (se 1 (by rfl) ⟨916496, by rfl⟩ : syracuseStep 1221995 = 1832993) B1832993
theorem B1222223 : Blo 814346 1222223 := bstep (se 1 (by rfl) ⟨916667, by rfl⟩ : syracuseStep 1222223 = 1833335) B1833335
theorem B4957793 : Blo 814346 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B6629003 : Blo 814346 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B1222343 : Blo 814346 1222343 := bstep (se 1 (by rfl) ⟨916757, by rfl⟩ : syracuseStep 1222343 = 1833515) B1833515
theorem B2795219 : Blo 814346 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B5023583 : Blo 814346 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B1222505 : Blo 814346 1222505 := bstep (se 2 (by rfl) ⟨458439, by rfl⟩ : syracuseStep 1222505 = 916879) B916879
theorem B1222583 : Blo 814346 1222583 := bstep (se 1 (by rfl) ⟨916937, by rfl⟩ : syracuseStep 1222583 = 1833875) B1833875
theorem B1222619 : Blo 814346 1222619 := bstep (se 1 (by rfl) ⟨916964, by rfl⟩ : syracuseStep 1222619 = 1833929) B1833929
theorem B1550735 : Blo 814346 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B32254355 : Blo 814346 32254355 := bstep (se 1 (by rfl) ⟨24190766, by rfl⟩ : syracuseStep 32254355 = 48381533) B48381533
theorem B1223087 : Blo 814346 1223087 := bstep (se 1 (by rfl) ⟨917315, by rfl⟩ : syracuseStep 1223087 = 1834631) B1834631
theorem B1223177 : Blo 814346 1223177 := bstep (se 2 (by rfl) ⟨458691, by rfl⟩ : syracuseStep 1223177 = 917383) B917383
theorem B1223207 : Blo 814346 1223207 := bstep (se 1 (by rfl) ⟨917405, by rfl⟩ : syracuseStep 1223207 = 1834811) B1834811
theorem B1223291 : Blo 814346 1223291 := bstep (se 1 (by rfl) ⟨917468, by rfl⟩ : syracuseStep 1223291 = 1834937) B1834937
theorem B1223417 : Blo 814346 1223417 := bstep (se 2 (by rfl) ⟨458781, by rfl⟩ : syracuseStep 1223417 = 917563) B917563
theorem B60271397 : Blo 814346 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B1223519 : Blo 814346 1223519 := bstep (se 1 (by rfl) ⟨917639, by rfl⟩ : syracuseStep 1223519 = 1835279) B1835279
theorem B1223531 : Blo 814346 1223531 := bstep (se 1 (by rfl) ⟨917648, by rfl⟩ : syracuseStep 1223531 = 1835297) B1835297
theorem B2206727 : Blo 814346 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B1616915 : Blo 814346 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1223759 : Blo 814346 1223759 := bstep (se 1 (by rfl) ⟨917819, by rfl⟩ : syracuseStep 1223759 = 1835639) B1835639
theorem B1223879 : Blo 814346 1223879 := bstep (se 1 (by rfl) ⟨917909, by rfl⟩ : syracuseStep 1223879 = 1835819) B1835819
theorem B6204761 : Blo 814346 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1224041 : Blo 814346 1224041 := bstep (se 2 (by rfl) ⟨459015, by rfl⟩ : syracuseStep 1224041 = 918031) B918031
theorem B5877107 : Blo 814346 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B1551791 : Blo 814346 1551791 := bstep (se 1 (by rfl) ⟨1163843, by rfl⟩ : syracuseStep 1551791 = 2327687) B2327687
theorem B1224119 : Blo 814346 1224119 := bstep (se 1 (by rfl) ⟨918089, by rfl⟩ : syracuseStep 1224119 = 1836179) B1836179
theorem B1224155 : Blo 814346 1224155 := bstep (se 1 (by rfl) ⟨918116, by rfl⟩ : syracuseStep 1224155 = 1836233) B1836233
theorem B9318077 : Blo 814346 9318077 := bstep (se 3 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 9318077 = 3494279) B3494279
theorem B2797267 : Blo 814346 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B1552223 : Blo 814346 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1224623 : Blo 814346 1224623 := bstep (se 1 (by rfl) ⟨918467, by rfl⟩ : syracuseStep 1224623 = 1836935) B1836935
theorem B1224713 : Blo 814346 1224713 := bstep (se 2 (by rfl) ⟨459267, by rfl⟩ : syracuseStep 1224713 = 918535) B918535
theorem B4960271 : Blo 814346 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B1224743 : Blo 814346 1224743 := bstep (se 1 (by rfl) ⟨918557, by rfl⟩ : syracuseStep 1224743 = 1837115) B1837115
theorem B1224827 : Blo 814346 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B1224953 : Blo 814346 1224953 := bstep (se 2 (by rfl) ⟨459357, by rfl⟩ : syracuseStep 1224953 = 918715) B918715
theorem B8827211 : Blo 814346 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B1225055 : Blo 814346 1225055 := bstep (se 1 (by rfl) ⟨918791, by rfl⟩ : syracuseStep 1225055 = 1837583) B1837583
theorem B1225067 : Blo 814346 1225067 := bstep (se 1 (by rfl) ⟨918800, by rfl⟩ : syracuseStep 1225067 = 1837601) B1837601
theorem B3093025 : Blo 814346 3093025 := bstep (se 2 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 3093025 = 2319769) B2319769
theorem B1225295 : Blo 814346 1225295 := bstep (se 1 (by rfl) ⟨918971, by rfl⟩ : syracuseStep 1225295 = 1837943) B1837943
theorem B1225415 : Blo 814346 1225415 := bstep (se 1 (by rfl) ⟨919061, by rfl⟩ : syracuseStep 1225415 = 1838123) B1838123
theorem B4961027 : Blo 814346 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B4141853 : Blo 814346 4141853 := bstep (se 3 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 4141853 = 1553195) B1553195
theorem B1225577 : Blo 814346 1225577 := bstep (se 2 (by rfl) ⟨459591, by rfl⟩ : syracuseStep 1225577 = 919183) B919183
theorem B5223275 : Blo 814346 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B17642393 : Blo 814346 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B1225655 : Blo 814346 1225655 := bstep (se 1 (by rfl) ⟨919241, by rfl⟩ : syracuseStep 1225655 = 1838483) B1838483
theorem B1225691 : Blo 814346 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B3093511 : Blo 814346 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B1651835 : Blo 814346 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B36254861 : Blo 814346 36254861 := bstep (se 3 (by rfl) ⟨6797786, by rfl⟩ : syracuseStep 36254861 = 13595573) B13595573
theorem B1226159 : Blo 814346 1226159 := bstep (se 1 (by rfl) ⟨919619, by rfl⟩ : syracuseStep 1226159 = 1839239) B1839239
theorem B3093997 : Blo 814346 3093997 := bstep (se 3 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 3093997 = 1160249) B1160249
theorem B1226249 : Blo 814346 1226249 := bstep (se 2 (by rfl) ⟨459843, by rfl⟩ : syracuseStep 1226249 = 919687) B919687
theorem B1226279 : Blo 814346 1226279 := bstep (se 1 (by rfl) ⟨919709, by rfl⟩ : syracuseStep 1226279 = 1839419) B1839419
theorem B1652321 : Blo 814346 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B1226363 : Blo 814346 1226363 := bstep (se 1 (by rfl) ⟨919772, by rfl⟩ : syracuseStep 1226363 = 1839545) B1839545
theorem B3913363 : Blo 814346 3913363 := bstep (se 1 (by rfl) ⟨2935022, by rfl⟩ : syracuseStep 3913363 = 5870045) B5870045
theorem B6207191 : Blo 814346 6207191 := bstep (se 1 (by rfl) ⟨4655393, by rfl⟩ : syracuseStep 6207191 = 9310787) B9310787
theorem B9058007 : Blo 814346 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B3978973 : Blo 814346 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B3487481 : Blo 814346 3487481 := bstep (se 2 (by rfl) ⟨1307805, by rfl⟩ : syracuseStep 3487481 = 2615611) B2615611
theorem B1226489 : Blo 814346 1226489 := bstep (se 2 (by rfl) ⟨459933, by rfl⟩ : syracuseStep 1226489 = 919867) B919867
theorem B3094301 : Blo 814346 3094301 := bstep (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) B1160363
theorem B1226591 : Blo 814346 1226591 := bstep (se 1 (by rfl) ⟨919943, by rfl⟩ : syracuseStep 1226591 = 1839887) B1839887
theorem B1226603 : Blo 814346 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1226831 : Blo 814346 1226831 := bstep (se 1 (by rfl) ⟨920123, by rfl⟩ : syracuseStep 1226831 = 1840247) B1840247
theorem B4241497 : Blo 814346 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B1226951 : Blo 814346 1226951 := bstep (se 1 (by rfl) ⟨920213, by rfl⟩ : syracuseStep 1226951 = 1840427) B1840427
theorem B1227113 : Blo 814346 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B3488129 : Blo 814346 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B1227191 : Blo 814346 1227191 := bstep (se 1 (by rfl) ⟨920393, by rfl⟩ : syracuseStep 1227191 = 1840787) B1840787
theorem B1227227 : Blo 814346 1227227 := bstep (se 1 (by rfl) ⟨920420, by rfl⟩ : syracuseStep 1227227 = 1840841) B1840841
theorem B9320993 : Blo 814346 9320993 := bstep (se 2 (by rfl) ⟨3495372, by rfl⟩ : syracuseStep 9320993 = 6990745) B6990745
theorem B1030735 : Blo 814346 1030735 := bstep (se 1 (by rfl) ⟨773051, by rfl⟩ : syracuseStep 1030735 = 1546103) B1546103
theorem B1653959 : Blo 814346 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B3915209 : Blo 814346 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B1031879 : Blo 814346 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B1032031 : Blo 814346 1032031 := bstep (se 1 (by rfl) ⟨774023, by rfl⟩ : syracuseStep 1032031 = 1548047) B1548047
theorem B3096427 : Blo 814346 3096427 := bstep (se 1 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 3096427 = 4644641) B4644641
theorem B2211745 : Blo 814346 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B5292047 : Blo 814346 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B12763453 : Blo 814346 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B11911493 : Blo 814346 11911493 := bstep (se 4 (by rfl) ⟨1116702, by rfl⟩ : syracuseStep 11911493 = 2233405) B2233405
theorem B5226839 : Blo 814346 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B5227067 : Blo 814346 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B6210107 : Blo 814346 6210107 := bstep (se 1 (by rfl) ⟨4657580, by rfl⟩ : syracuseStep 6210107 = 9315161) B9315161
theorem B56640217 : Blo 814346 56640217 := bstep (se 2 (by rfl) ⟨21240081, by rfl⟩ : syracuseStep 56640217 = 42480163) B42480163
theorem B3490589 : Blo 814346 3490589 := bstep (se 3 (by rfl) ⟨654485, by rfl⟩ : syracuseStep 3490589 = 1308971) B1308971
theorem B4408955 : Blo 814346 4408955 := bstep (se 1 (by rfl) ⟨3306716, by rfl⟩ : syracuseStep 4408955 = 6613433) B6613433
theorem B3721079 : Blo 814346 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B1034203 : Blo 814346 1034203 := bstep (se 1 (by rfl) ⟨775652, by rfl⟩ : syracuseStep 1034203 = 1551305) B1551305
theorem B5883911 : Blo 814346 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B3491855 : Blo 814346 3491855 := bstep (se 1 (by rfl) ⟨2618891, by rfl⟩ : syracuseStep 3491855 = 5237783) B5237783
theorem B9291833 : Blo 814346 9291833 := bstep (se 2 (by rfl) ⟨3484437, by rfl⟩ : syracuseStep 9291833 = 6968875) B6968875
theorem B4638809 : Blo 814346 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B870751 : Blo 814346 870751 := bstep (se 1 (by rfl) ⟨653063, by rfl⟩ : syracuseStep 870751 = 1306127) B1306127
theorem B3099161 : Blo 814346 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B4639265 : Blo 814346 4639265 := bstep (se 2 (by rfl) ⟨1739724, by rfl⟩ : syracuseStep 4639265 = 3479449) B3479449
theorem B2837207 : Blo 814346 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B4639517 : Blo 814346 4639517 := bstep (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) B1739819
theorem B5032777 : Blo 814346 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B2476975 : Blo 814346 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B50187275 : Blo 814346 50187275 := bstep (se 1 (by rfl) ⟨37640456, by rfl⟩ : syracuseStep 50187275 = 75280913) B75280913
theorem B35245691 : Blo 814346 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B3100787 : Blo 814346 3100787 := bstep (se 1 (by rfl) ⟨2325590, by rfl⟩ : syracuseStep 3100787 = 4651181) B4651181
theorem B2937863 : Blo 814346 2937863 := bstep (se 1 (by rfl) ⟨2203397, by rfl⟩ : syracuseStep 2937863 = 4406795) B4406795
theorem B4412569 : Blo 814346 4412569 := bstep (se 2 (by rfl) ⟨1654713, by rfl⟩ : syracuseStep 4412569 = 3309427) B3309427
theorem B2479261 : Blo 814346 2479261 := bstep (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) B929723
theorem B3102077 : Blo 814346 3102077 := bstep (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) B1163279
theorem B1988687 : Blo 814346 1988687 := bstep (se 1 (by rfl) ⟨1491515, by rfl⟩ : syracuseStep 1988687 = 2983031) B2983031
theorem B4970585 : Blo 814346 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B11163905 : Blo 814346 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B5593859 : Blo 814346 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B2611997 : Blo 814346 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B4021249 : Blo 814346 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B52878379 : Blo 814346 52878379 := bstep (se 1 (by rfl) ⟨39658784, by rfl⟩ : syracuseStep 52878379 = 79317569) B79317569
theorem B4643891 : Blo 814346 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B8805455 : Blo 814346 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B3103991 : Blo 814346 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B1957499 : Blo 814346 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B13918067 : Blo 814346 13918067 := bstep (se 1 (by rfl) ⟨10438550, by rfl⟩ : syracuseStep 13918067 = 20877101) B20877101
theorem B3104963 : Blo 814346 3104963 := bstep (se 1 (by rfl) ⟨2328722, by rfl⟩ : syracuseStep 3104963 = 4657445) B4657445
theorem B6185321 : Blo 814346 6185321 := bstep (se 2 (by rfl) ⟨2319495, by rfl⟩ : syracuseStep 6185321 = 4638991) B4638991
theorem B1958249 : Blo 814346 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B3105479 : Blo 814346 3105479 := bstep (se 1 (by rfl) ⟨2329109, by rfl⟩ : syracuseStep 3105479 = 4658219) B4658219
theorem B2613971 : Blo 814346 2613971 := bstep (se 1 (by rfl) ⟨1960478, by rfl⟩ : syracuseStep 2613971 = 3920957) B3920957
theorem B23847641 : Blo 814346 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B3106451 : Blo 814346 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B3106633 : Blo 814346 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B2615303 : Blo 814346 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B6187265 : Blo 814346 6187265 := bstep (se 2 (by rfl) ⟨2320224, by rfl⟩ : syracuseStep 6187265 = 4640449) B4640449
theorem B3303767 : Blo 814346 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B1239479 : Blo 814346 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B11168441 : Blo 814346 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B6384529 : Blo 814346 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B814375 : Blo 814346 814375 := bstep (se 1 (by rfl) ⟨610781, by rfl⟩ : syracuseStep 814375 = 1221563) B1221563
theorem B814415 : Blo 814346 814415 := bstep (se 1 (by rfl) ⟨610811, by rfl⟩ : syracuseStep 814415 = 1221623) B1221623
theorem B814431 : Blo 814346 814431 := bstep (se 1 (by rfl) ⟨610823, by rfl⟩ : syracuseStep 814431 = 1221647) B1221647
theorem B814459 : Blo 814346 814459 := bstep (se 1 (by rfl) ⟨610844, by rfl⟩ : syracuseStep 814459 = 1221689) B1221689
theorem B2485633 : Blo 814346 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B814511 : Blo 814346 814511 := bstep (se 1 (by rfl) ⟨610883, by rfl⟩ : syracuseStep 814511 = 1221767) B1221767
theorem B814535 : Blo 814346 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B814555 : Blo 814346 814555 := bstep (se 1 (by rfl) ⟨610916, by rfl⟩ : syracuseStep 814555 = 1221833) B1221833
theorem B1961459 : Blo 814346 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B814631 : Blo 814346 814631 := bstep (se 1 (by rfl) ⟨610973, by rfl⟩ : syracuseStep 814631 = 1221947) B1221947
theorem B814671 : Blo 814346 814671 := bstep (se 1 (by rfl) ⟨611003, by rfl⟩ : syracuseStep 814671 = 1222007) B1222007
theorem B814687 : Blo 814346 814687 := bstep (se 1 (by rfl) ⟨611015, by rfl⟩ : syracuseStep 814687 = 1222031) B1222031
theorem B814715 : Blo 814346 814715 := bstep (se 1 (by rfl) ⟨611036, by rfl⟩ : syracuseStep 814715 = 1222073) B1222073
theorem B814767 : Blo 814346 814767 := bstep (se 1 (by rfl) ⟨611075, by rfl⟩ : syracuseStep 814767 = 1222151) B1222151
theorem B814791 : Blo 814346 814791 := bstep (se 1 (by rfl) ⟨611093, by rfl⟩ : syracuseStep 814791 = 1222187) B1222187
theorem B814811 : Blo 814346 814811 := bstep (se 1 (by rfl) ⟨611108, by rfl⟩ : syracuseStep 814811 = 1222217) B1222217
theorem B4648697 : Blo 814346 4648697 := bstep (se 2 (by rfl) ⟨1743261, by rfl⟩ : syracuseStep 4648697 = 3486523) B3486523
theorem B814887 : Blo 814346 814887 := bstep (se 1 (by rfl) ⟨611165, by rfl⟩ : syracuseStep 814887 = 1222331) B1222331
theorem B814927 : Blo 814346 814927 := bstep (se 1 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 814927 = 1222391) B1222391
theorem B814943 : Blo 814346 814943 := bstep (se 1 (by rfl) ⟨611207, by rfl⟩ : syracuseStep 814943 = 1222415) B1222415
theorem B814971 : Blo 814346 814971 := bstep (se 1 (by rfl) ⟨611228, by rfl⟩ : syracuseStep 814971 = 1222457) B1222457
theorem B1306511 : Blo 814346 1306511 := bstep (se 1 (by rfl) ⟨979883, by rfl⟩ : syracuseStep 1306511 = 1959767) B1959767
theorem B815023 : Blo 814346 815023 := bstep (se 1 (by rfl) ⟨611267, by rfl⟩ : syracuseStep 815023 = 1222535) B1222535
theorem B2355119 : Blo 814346 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B815047 : Blo 814346 815047 := bstep (se 1 (by rfl) ⟨611285, by rfl⟩ : syracuseStep 815047 = 1222571) B1222571
theorem B47673305 : Blo 814346 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B815067 : Blo 814346 815067 := bstep (se 1 (by rfl) ⟨611300, by rfl⟩ : syracuseStep 815067 = 1222601) B1222601
theorem B815143 : Blo 814346 815143 := bstep (se 1 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 815143 = 1222715) B1222715
theorem B815183 : Blo 814346 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B815199 : Blo 814346 815199 := bstep (se 1 (by rfl) ⟨611399, by rfl⟩ : syracuseStep 815199 = 1222799) B1222799
theorem B815227 : Blo 814346 815227 := bstep (se 1 (by rfl) ⟨611420, by rfl⟩ : syracuseStep 815227 = 1222841) B1222841
theorem B815279 : Blo 814346 815279 := bstep (se 1 (by rfl) ⟨611459, by rfl⟩ : syracuseStep 815279 = 1222919) B1222919
theorem B815303 : Blo 814346 815303 := bstep (se 1 (by rfl) ⟨611477, by rfl⟩ : syracuseStep 815303 = 1222955) B1222955
theorem B815323 : Blo 814346 815323 := bstep (se 1 (by rfl) ⟨611492, by rfl⟩ : syracuseStep 815323 = 1222985) B1222985
theorem B815399 : Blo 814346 815399 := bstep (se 1 (by rfl) ⟨611549, by rfl⟩ : syracuseStep 815399 = 1223099) B1223099
theorem B815439 : Blo 814346 815439 := bstep (se 1 (by rfl) ⟨611579, by rfl⟩ : syracuseStep 815439 = 1223159) B1223159
theorem B815455 : Blo 814346 815455 := bstep (se 1 (by rfl) ⟨611591, by rfl⟩ : syracuseStep 815455 = 1223183) B1223183
theorem B815483 : Blo 814346 815483 := bstep (se 1 (by rfl) ⟨611612, by rfl⟩ : syracuseStep 815483 = 1223225) B1223225
theorem B2748815 : Blo 814346 2748815 := bstep (se 1 (by rfl) ⟨2061611, by rfl⟩ : syracuseStep 2748815 = 4123223) B4123223
theorem B815535 : Blo 814346 815535 := bstep (se 1 (by rfl) ⟨611651, by rfl⟩ : syracuseStep 815535 = 1223303) B1223303
theorem B815559 : Blo 814346 815559 := bstep (se 1 (by rfl) ⟨611669, by rfl⟩ : syracuseStep 815559 = 1223339) B1223339
theorem B815579 : Blo 814346 815579 := bstep (se 1 (by rfl) ⟨611684, by rfl⟩ : syracuseStep 815579 = 1223369) B1223369
theorem B815655 : Blo 814346 815655 := bstep (se 1 (by rfl) ⟨611741, by rfl⟩ : syracuseStep 815655 = 1223483) B1223483
theorem B815695 : Blo 814346 815695 := bstep (se 1 (by rfl) ⟨611771, by rfl⟩ : syracuseStep 815695 = 1223543) B1223543
theorem B815711 : Blo 814346 815711 := bstep (se 1 (by rfl) ⟨611783, by rfl⟩ : syracuseStep 815711 = 1223567) B1223567
theorem B815739 : Blo 814346 815739 := bstep (se 1 (by rfl) ⟨611804, by rfl⟩ : syracuseStep 815739 = 1223609) B1223609
theorem B1241723 : Blo 814346 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B815791 : Blo 814346 815791 := bstep (se 1 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 815791 = 1223687) B1223687
theorem B2618045 : Blo 814346 2618045 := bstep (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) B981767
theorem B815815 : Blo 814346 815815 := bstep (se 1 (by rfl) ⟨611861, by rfl⟩ : syracuseStep 815815 = 1223723) B1223723
theorem B2749139 : Blo 814346 2749139 := bstep (se 1 (by rfl) ⟨2061854, by rfl⟩ : syracuseStep 2749139 = 4123709) B4123709
theorem B815835 : Blo 814346 815835 := bstep (se 1 (by rfl) ⟨611876, by rfl⟩ : syracuseStep 815835 = 1223753) B1223753
theorem B2945821 : Blo 814346 2945821 := bstep (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) B1104683
theorem B815911 : Blo 814346 815911 := bstep (se 1 (by rfl) ⟨611933, by rfl⟩ : syracuseStep 815911 = 1223867) B1223867
theorem B815951 : Blo 814346 815951 := bstep (se 1 (by rfl) ⟨611963, by rfl⟩ : syracuseStep 815951 = 1223927) B1223927
theorem B815967 : Blo 814346 815967 := bstep (se 1 (by rfl) ⟨611975, by rfl⟩ : syracuseStep 815967 = 1223951) B1223951
theorem B815995 : Blo 814346 815995 := bstep (se 1 (by rfl) ⟨611996, by rfl⟩ : syracuseStep 815995 = 1223993) B1223993
theorem B816047 : Blo 814346 816047 := bstep (se 1 (by rfl) ⟨612035, by rfl⟩ : syracuseStep 816047 = 1224071) B1224071
theorem B816071 : Blo 814346 816071 := bstep (se 1 (by rfl) ⟨612053, by rfl⟩ : syracuseStep 816071 = 1224107) B1224107
theorem B816091 : Blo 814346 816091 := bstep (se 1 (by rfl) ⟨612068, by rfl⟩ : syracuseStep 816091 = 1224137) B1224137
theorem B816167 : Blo 814346 816167 := bstep (se 1 (by rfl) ⟨612125, by rfl⟩ : syracuseStep 816167 = 1224251) B1224251
theorem B980047 : Blo 814346 980047 := bstep (se 1 (by rfl) ⟨735035, by rfl⟩ : syracuseStep 980047 = 1470071) B1470071
theorem B816207 : Blo 814346 816207 := bstep (se 1 (by rfl) ⟨612155, by rfl⟩ : syracuseStep 816207 = 1224311) B1224311
theorem B816223 : Blo 814346 816223 := bstep (se 1 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 816223 = 1224335) B1224335
theorem B816251 : Blo 814346 816251 := bstep (se 1 (by rfl) ⟨612188, by rfl⟩ : syracuseStep 816251 = 1224377) B1224377
theorem B5239961 : Blo 814346 5239961 := bstep (se 2 (by rfl) ⟨1964985, by rfl⟩ : syracuseStep 5239961 = 3929971) B3929971
theorem B4650155 : Blo 814346 4650155 := bstep (se 1 (by rfl) ⟨3487616, by rfl⟩ : syracuseStep 4650155 = 6975233) B6975233
theorem B816303 : Blo 814346 816303 := bstep (se 1 (by rfl) ⟨612227, by rfl⟩ : syracuseStep 816303 = 1224455) B1224455
theorem B816327 : Blo 814346 816327 := bstep (se 1 (by rfl) ⟨612245, by rfl⟩ : syracuseStep 816327 = 1224491) B1224491
theorem B1471699 : Blo 814346 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B816347 : Blo 814346 816347 := bstep (se 1 (by rfl) ⟨612260, by rfl⟩ : syracuseStep 816347 = 1224521) B1224521
theorem B816423 : Blo 814346 816423 := bstep (se 1 (by rfl) ⟨612317, by rfl⟩ : syracuseStep 816423 = 1224635) B1224635
theorem B816463 : Blo 814346 816463 := bstep (se 1 (by rfl) ⟨612347, by rfl⟩ : syracuseStep 816463 = 1224695) B1224695
theorem B816479 : Blo 814346 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B816507 : Blo 814346 816507 := bstep (se 1 (by rfl) ⟨612380, by rfl⟩ : syracuseStep 816507 = 1224761) B1224761
theorem B5240189 : Blo 814346 5240189 := bstep (se 3 (by rfl) ⟨982535, by rfl⟩ : syracuseStep 5240189 = 1965071) B1965071
theorem B3306881 : Blo 814346 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B816559 : Blo 814346 816559 := bstep (se 1 (by rfl) ⟨612419, by rfl⟩ : syracuseStep 816559 = 1224839) B1224839
theorem B816583 : Blo 814346 816583 := bstep (se 1 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 816583 = 1224875) B1224875
theorem B9303497 : Blo 814346 9303497 := bstep (se 2 (by rfl) ⟨3488811, by rfl⟩ : syracuseStep 9303497 = 6977623) B6977623
theorem B816603 : Blo 814346 816603 := bstep (se 1 (by rfl) ⟨612452, by rfl⟩ : syracuseStep 816603 = 1224905) B1224905
theorem B816679 : Blo 814346 816679 := bstep (se 1 (by rfl) ⟨612509, by rfl⟩ : syracuseStep 816679 = 1225019) B1225019
theorem B816719 : Blo 814346 816719 := bstep (se 1 (by rfl) ⟨612539, by rfl⟩ : syracuseStep 816719 = 1225079) B1225079
theorem B816735 : Blo 814346 816735 := bstep (se 1 (by rfl) ⟨612551, by rfl⟩ : syracuseStep 816735 = 1225103) B1225103
theorem B816763 : Blo 814346 816763 := bstep (se 1 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 816763 = 1225145) B1225145
theorem B816815 : Blo 814346 816815 := bstep (se 1 (by rfl) ⟨612611, by rfl⟩ : syracuseStep 816815 = 1225223) B1225223
theorem B816839 : Blo 814346 816839 := bstep (se 1 (by rfl) ⟨612629, by rfl⟩ : syracuseStep 816839 = 1225259) B1225259
theorem B4191959 : Blo 814346 4191959 := bstep (se 1 (by rfl) ⟨3143969, by rfl⟩ : syracuseStep 4191959 = 6287939) B6287939
theorem B816859 : Blo 814346 816859 := bstep (se 1 (by rfl) ⟨612644, by rfl⟩ : syracuseStep 816859 = 1225289) B1225289
theorem B1308407 : Blo 814346 1308407 := bstep (se 1 (by rfl) ⟨981305, by rfl⟩ : syracuseStep 1308407 = 1962611) B1962611
theorem B21231395 : Blo 814346 21231395 := bstep (se 1 (by rfl) ⟨15923546, by rfl⟩ : syracuseStep 21231395 = 31847093) B31847093
theorem B816935 : Blo 814346 816935 := bstep (se 1 (by rfl) ⟨612701, by rfl⟩ : syracuseStep 816935 = 1225403) B1225403
theorem B1832777 : Blo 814346 1832777 := bstep (se 2 (by rfl) ⟨687291, by rfl⟩ : syracuseStep 1832777 = 1374583) B1374583
theorem B816975 : Blo 814346 816975 := bstep (se 1 (by rfl) ⟨612731, by rfl⟩ : syracuseStep 816975 = 1225463) B1225463
theorem B816991 : Blo 814346 816991 := bstep (se 1 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 816991 = 1225487) B1225487
theorem B2750327 : Blo 814346 2750327 := bstep (se 1 (by rfl) ⟨2062745, by rfl⟩ : syracuseStep 2750327 = 4125491) B4125491
theorem B817019 : Blo 814346 817019 := bstep (se 1 (by rfl) ⟨612764, by rfl⟩ : syracuseStep 817019 = 1225529) B1225529
theorem B4126625 : Blo 814346 4126625 := bstep (se 2 (by rfl) ⟨1547484, by rfl⟩ : syracuseStep 4126625 = 3094969) B3094969
theorem B12089249 : Blo 814346 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B817071 : Blo 814346 817071 := bstep (se 1 (by rfl) ⟨612803, by rfl⟩ : syracuseStep 817071 = 1225607) B1225607
theorem B817095 : Blo 814346 817095 := bstep (se 1 (by rfl) ⟨612821, by rfl⟩ : syracuseStep 817095 = 1225643) B1225643
theorem B817115 : Blo 814346 817115 := bstep (se 1 (by rfl) ⟨612836, by rfl⟩ : syracuseStep 817115 = 1225673) B1225673
theorem B817191 : Blo 814346 817191 := bstep (se 1 (by rfl) ⟨612893, by rfl⟩ : syracuseStep 817191 = 1225787) B1225787
theorem B2750543 : Blo 814346 2750543 := bstep (se 1 (by rfl) ⟨2062907, by rfl⟩ : syracuseStep 2750543 = 4125815) B4125815
theorem B817231 : Blo 814346 817231 := bstep (se 1 (by rfl) ⟨612923, by rfl⟩ : syracuseStep 817231 = 1225847) B1225847
theorem B817247 : Blo 814346 817247 := bstep (se 1 (by rfl) ⟨612935, by rfl⟩ : syracuseStep 817247 = 1225871) B1225871
theorem B817275 : Blo 814346 817275 := bstep (se 1 (by rfl) ⟨612956, by rfl⟩ : syracuseStep 817275 = 1225913) B1225913
theorem B817327 : Blo 814346 817327 := bstep (se 1 (by rfl) ⟨612995, by rfl⟩ : syracuseStep 817327 = 1225991) B1225991
theorem B817351 : Blo 814346 817351 := bstep (se 1 (by rfl) ⟨613013, by rfl⟩ : syracuseStep 817351 = 1226027) B1226027
theorem B1472723 : Blo 814346 1472723 := bstep (se 1 (by rfl) ⟨1104542, by rfl⟩ : syracuseStep 1472723 = 2209085) B2209085
theorem B817371 : Blo 814346 817371 := bstep (se 1 (by rfl) ⟨613028, by rfl⟩ : syracuseStep 817371 = 1226057) B1226057
theorem B1374455 : Blo 814346 1374455 := bstep (se 1 (by rfl) ⟨1030841, by rfl⟩ : syracuseStep 1374455 = 2061683) B2061683
theorem B817447 : Blo 814346 817447 := bstep (se 1 (by rfl) ⟨613085, by rfl⟩ : syracuseStep 817447 = 1226171) B1226171
theorem B817487 : Blo 814346 817487 := bstep (se 1 (by rfl) ⟨613115, by rfl⟩ : syracuseStep 817487 = 1226231) B1226231
theorem B817503 : Blo 814346 817503 := bstep (se 1 (by rfl) ⟨613127, by rfl⟩ : syracuseStep 817503 = 1226255) B1226255
theorem B1243487 : Blo 814346 1243487 := bstep (se 1 (by rfl) ⟨932615, by rfl⟩ : syracuseStep 1243487 = 1865231) B1865231
theorem B6977897 : Blo 814346 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B817531 : Blo 814346 817531 := bstep (se 1 (by rfl) ⟨613148, by rfl⟩ : syracuseStep 817531 = 1226297) B1226297
theorem B817583 : Blo 814346 817583 := bstep (se 1 (by rfl) ⟨613187, by rfl⟩ : syracuseStep 817583 = 1226375) B1226375
theorem B817607 : Blo 814346 817607 := bstep (se 1 (by rfl) ⟨613205, by rfl⟩ : syracuseStep 817607 = 1226411) B1226411
theorem B2750921 : Blo 814346 2750921 := bstep (se 2 (by rfl) ⟨1031595, by rfl⟩ : syracuseStep 2750921 = 2063191) B2063191
theorem B817627 : Blo 814346 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B3930605 : Blo 814346 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B6191639 : Blo 814346 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B817703 : Blo 814346 817703 := bstep (se 1 (by rfl) ⟨613277, by rfl⟩ : syracuseStep 817703 = 1226555) B1226555
theorem B4913723 : Blo 814346 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B1374799 : Blo 814346 1374799 := bstep (se 1 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 1374799 = 2062199) B2062199
theorem B817743 : Blo 814346 817743 := bstep (se 1 (by rfl) ⟨613307, by rfl⟩ : syracuseStep 817743 = 1226615) B1226615
theorem B817759 : Blo 814346 817759 := bstep (se 1 (by rfl) ⟨613319, by rfl⟩ : syracuseStep 817759 = 1226639) B1226639
theorem B1833569 : Blo 814346 1833569 := bstep (se 2 (by rfl) ⟨687588, by rfl⟩ : syracuseStep 1833569 = 1375177) B1375177
theorem B817787 : Blo 814346 817787 := bstep (se 1 (by rfl) ⟨613340, by rfl⟩ : syracuseStep 817787 = 1226681) B1226681
theorem B817839 : Blo 814346 817839 := bstep (se 1 (by rfl) ⟨613379, by rfl⟩ : syracuseStep 817839 = 1226759) B1226759
theorem B817863 : Blo 814346 817863 := bstep (se 1 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 817863 = 1226795) B1226795
theorem B2751191 : Blo 814346 2751191 := bstep (se 1 (by rfl) ⟨2063393, by rfl⟩ : syracuseStep 2751191 = 4126787) B4126787
theorem B817883 : Blo 814346 817883 := bstep (se 1 (by rfl) ⟨613412, by rfl⟩ : syracuseStep 817883 = 1226825) B1226825
theorem B817959 : Blo 814346 817959 := bstep (se 1 (by rfl) ⟨613469, by rfl⟩ : syracuseStep 817959 = 1226939) B1226939
theorem B1375049 : Blo 814346 1375049 := bstep (se 2 (by rfl) ⟨515643, by rfl⟩ : syracuseStep 1375049 = 1031287) B1031287
theorem B817999 : Blo 814346 817999 := bstep (se 1 (by rfl) ⟨613499, by rfl⟩ : syracuseStep 817999 = 1226999) B1226999
theorem B1309535 : Blo 814346 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B818015 : Blo 814346 818015 := bstep (se 1 (by rfl) ⟨613511, by rfl⟩ : syracuseStep 818015 = 1227023) B1227023
theorem B818043 : Blo 814346 818043 := bstep (se 1 (by rfl) ⟨613532, by rfl⟩ : syracuseStep 818043 = 1227065) B1227065
theorem B2751407 : Blo 814346 2751407 := bstep (se 1 (by rfl) ⟨2063555, by rfl⟩ : syracuseStep 2751407 = 4127111) B4127111
theorem B818095 : Blo 814346 818095 := bstep (se 1 (by rfl) ⟨613571, by rfl⟩ : syracuseStep 818095 = 1227143) B1227143
theorem B1833911 : Blo 814346 1833911 := bstep (se 1 (by rfl) ⟨1375433, by rfl⟩ : syracuseStep 1833911 = 2750867) B2750867
theorem B1178551 : Blo 814346 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B818119 : Blo 814346 818119 := bstep (se 1 (by rfl) ⟨613589, by rfl⟩ : syracuseStep 818119 = 1227179) B1227179
theorem B818139 : Blo 814346 818139 := bstep (se 1 (by rfl) ⟨613604, by rfl⟩ : syracuseStep 818139 = 1227209) B1227209
theorem B5241829 : Blo 814346 5241829 := bstep (se 4 (by rfl) ⟨491421, by rfl⟩ : syracuseStep 5241829 = 982843) B982843
theorem B1473545 : Blo 814346 1473545 := bstep (se 2 (by rfl) ⟨552579, by rfl⟩ : syracuseStep 1473545 = 1105159) B1105159
theorem B916519 : Blo 814346 916519 := bstep (se 1 (by rfl) ⟨687389, by rfl⟩ : syracuseStep 916519 = 1374779) B1374779
theorem B818215 : Blo 814346 818215 := bstep (se 1 (by rfl) ⟨613661, by rfl⟩ : syracuseStep 818215 = 1227323) B1227323
theorem B818255 : Blo 814346 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B818271 : Blo 814346 818271 := bstep (se 1 (by rfl) ⟨613703, by rfl⟩ : syracuseStep 818271 = 1227407) B1227407
theorem B818299 : Blo 814346 818299 := bstep (se 1 (by rfl) ⟨613724, by rfl⟩ : syracuseStep 818299 = 1227449) B1227449
theorem B1375481 : Blo 814346 1375481 := bstep (se 2 (by rfl) ⟨515805, by rfl⟩ : syracuseStep 1375481 = 1031611) B1031611
theorem B6978959 : Blo 814346 6978959 := bstep (se 1 (by rfl) ⟨5234219, by rfl⟩ : syracuseStep 6978959 = 10468439) B10468439
theorem B1375663 : Blo 814346 1375663 := bstep (se 1 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 1375663 = 2063495) B2063495
theorem B1375751 : Blo 814346 1375751 := bstep (se 1 (by rfl) ⟨1031813, by rfl⟩ : syracuseStep 1375751 = 2063627) B2063627
theorem B1834505 : Blo 814346 1834505 := bstep (se 2 (by rfl) ⟨687939, by rfl⟩ : syracuseStep 1834505 = 1375879) B1375879
theorem B1342985 : Blo 814346 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B9436711 : Blo 814346 9436711 := bstep (se 1 (by rfl) ⟨7077533, by rfl⟩ : syracuseStep 9436711 = 14155067) B14155067
theorem B1376095 : Blo 814346 1376095 := bstep (se 1 (by rfl) ⟨1032071, by rfl⟩ : syracuseStep 1376095 = 2064143) B2064143
theorem B1834847 : Blo 814346 1834847 := bstep (se 1 (by rfl) ⟨1376135, by rfl⟩ : syracuseStep 1834847 = 2752271) B2752271
theorem B1376183 : Blo 814346 1376183 := bstep (se 1 (by rfl) ⟨1032137, by rfl⟩ : syracuseStep 1376183 = 2064275) B2064275
theorem B3932219 : Blo 814346 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B2064649 : Blo 814346 2064649 := bstep (se 2 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 2064649 = 1548487) B1548487
theorem B3932489 : Blo 814346 3932489 := bstep (se 2 (by rfl) ⟨1474683, by rfl⟩ : syracuseStep 3932489 = 2949367) B2949367
theorem B917851 : Blo 814346 917851 := bstep (se 1 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 917851 = 1376777) B1376777
theorem B1048955 : Blo 814346 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B917959 : Blo 814346 917959 := bstep (se 1 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 917959 = 1376939) B1376939
theorem B2327059 : Blo 814346 2327059 := bstep (se 1 (by rfl) ⟨1745294, by rfl⟩ : syracuseStep 2327059 = 3490589) B3490589
theorem B1376831 : Blo 814346 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B918319 : Blo 814346 918319 := bstep (se 1 (by rfl) ⟨688739, by rfl⟩ : syracuseStep 918319 = 1377479) B1377479
theorem B1835855 : Blo 814346 1835855 := bstep (se 1 (by rfl) ⟨1376891, by rfl⟩ : syracuseStep 1835855 = 2753783) B2753783
theorem B918427 : Blo 814346 918427 := bstep (se 1 (by rfl) ⟨688820, by rfl⟩ : syracuseStep 918427 = 1377641) B1377641
theorem B1836071 : Blo 814346 1836071 := bstep (se 1 (by rfl) ⟨1377053, by rfl⟩ : syracuseStep 1836071 = 2754107) B2754107
theorem B1836251 : Blo 814346 1836251 := bstep (se 1 (by rfl) ⟨1377188, by rfl⟩ : syracuseStep 1836251 = 2754377) B2754377
theorem B1377499 : Blo 814346 1377499 := bstep (se 1 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 1377499 = 2066249) B2066249
theorem B918823 : Blo 814346 918823 := bstep (se 1 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 918823 = 1378235) B1378235
theorem B2327903 : Blo 814346 2327903 := bstep (se 1 (by rfl) ⟨1745927, by rfl⟩ : syracuseStep 2327903 = 3491855) B3491855
theorem B918895 : Blo 814346 918895 := bstep (se 1 (by rfl) ⟨689171, by rfl⟩ : syracuseStep 918895 = 1378343) B1378343
theorem B6194555 : Blo 814346 6194555 := bstep (se 1 (by rfl) ⟨4645916, by rfl⟩ : syracuseStep 6194555 = 9291833) B9291833
theorem B1836449 : Blo 814346 1836449 := bstep (se 2 (by rfl) ⟨688668, by rfl⟩ : syracuseStep 1836449 = 1377337) B1377337
theorem B919111 : Blo 814346 919111 := bstep (se 1 (by rfl) ⟨689333, by rfl⟩ : syracuseStep 919111 = 1378667) B1378667
theorem B2066107 : Blo 814346 2066107 := bstep (se 1 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 2066107 = 3099161) B3099161
theorem B1837007 : Blo 814346 1837007 := bstep (se 1 (by rfl) ⟨1377755, by rfl⟩ : syracuseStep 1837007 = 2755511) B2755511
theorem B1378255 : Blo 814346 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B33458183 : Blo 814346 33458183 := bstep (se 1 (by rfl) ⟨25093637, by rfl⟩ : syracuseStep 33458183 = 50187275) B50187275
theorem B2754593 : Blo 814346 2754593 := bstep (se 2 (by rfl) ⟨1032972, by rfl⟩ : syracuseStep 2754593 = 2065945) B2065945
theorem B1837385 : Blo 814346 1837385 := bstep (se 2 (by rfl) ⟨689019, by rfl⟩ : syracuseStep 1837385 = 1378039) B1378039
theorem B1837403 : Blo 814346 1837403 := bstep (se 1 (by rfl) ⟨1378052, by rfl⟩ : syracuseStep 1837403 = 2756105) B2756105
theorem B3541391 : Blo 814346 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B23497127 : Blo 814346 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B919975 : Blo 814346 919975 := bstep (se 1 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 919975 = 1379963) B1379963
theorem B4131323 : Blo 814346 4131323 := bstep (se 1 (by rfl) ⟨3098492, by rfl⟩ : syracuseStep 4131323 = 6196985) B6196985
theorem B1378937 : Blo 814346 1378937 := bstep (se 2 (by rfl) ⟨517101, by rfl⟩ : syracuseStep 1378937 = 1034203) B1034203
theorem B1378991 : Blo 814346 1378991 := bstep (se 1 (by rfl) ⟨1034243, by rfl⟩ : syracuseStep 1378991 = 2068487) B2068487
theorem B2067191 : Blo 814346 2067191 := bstep (se 1 (by rfl) ⟨1550393, by rfl⟩ : syracuseStep 2067191 = 3100787) B3100787
theorem B1837979 : Blo 814346 1837979 := bstep (se 1 (by rfl) ⟨1378484, by rfl⟩ : syracuseStep 1837979 = 2756969) B2756969
theorem B1379227 : Blo 814346 1379227 := bstep (se 1 (by rfl) ⟨1034420, by rfl⟩ : syracuseStep 1379227 = 2068841) B2068841
theorem B920551 : Blo 814346 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B1838177 : Blo 814346 1838177 := bstep (se 2 (by rfl) ⟨689316, by rfl⟩ : syracuseStep 1838177 = 1378633) B1378633
theorem B1838375 : Blo 814346 1838375 := bstep (se 1 (by rfl) ⟨1378781, by rfl⟩ : syracuseStep 1838375 = 2757563) B2757563
theorem B4132295 : Blo 814346 4132295 := bstep (se 1 (by rfl) ⟨3099221, by rfl⟩ : syracuseStep 4132295 = 6198443) B6198443
theorem B2068051 : Blo 814346 2068051 := bstep (se 1 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 2068051 = 3102077) B3102077
theorem B1838753 : Blo 814346 1838753 := bstep (se 2 (by rfl) ⟨689532, by rfl⟩ : syracuseStep 1838753 = 1379065) B1379065
theorem B4132619 : Blo 814346 4132619 := bstep (se 1 (by rfl) ⟨3099464, by rfl⟩ : syracuseStep 4132619 = 6198929) B6198929
theorem B1839113 : Blo 814346 1839113 := bstep (se 2 (by rfl) ⟨689667, by rfl⟩ : syracuseStep 1839113 = 1379335) B1379335
theorem B3313723 : Blo 814346 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B7442603 : Blo 814346 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B1380719 : Blo 814346 1380719 := bstep (se 1 (by rfl) ⟨1035539, by rfl⟩ : syracuseStep 1380719 = 2071079) B2071079
theorem B1839527 : Blo 814346 1839527 := bstep (se 1 (by rfl) ⟨1379645, by rfl⟩ : syracuseStep 1839527 = 2759291) B2759291
theorem B3314177 : Blo 814346 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B1741331 : Blo 814346 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B1839635 : Blo 814346 1839635 := bstep (se 1 (by rfl) ⟨1379726, by rfl⟩ : syracuseStep 1839635 = 2759453) B2759453
theorem B24154685 : Blo 814346 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B11178557 : Blo 814346 11178557 := bstep (se 3 (by rfl) ⟨2095979, by rfl⟩ : syracuseStep 11178557 = 4191959) B4191959
theorem B1380935 : Blo 814346 1380935 := bstep (se 1 (by rfl) ⟨1035701, by rfl⟩ : syracuseStep 1380935 = 2071403) B2071403
theorem B1839689 : Blo 814346 1839689 := bstep (se 2 (by rfl) ⟨689883, by rfl⟩ : syracuseStep 1839689 = 1379767) B1379767
theorem B4133591 : Blo 814346 4133591 := bstep (se 1 (by rfl) ⟨3100193, by rfl⟩ : syracuseStep 4133591 = 6200387) B6200387
theorem B5870303 : Blo 814346 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B2757455 : Blo 814346 2757455 := bstep (se 1 (by rfl) ⟨2068091, by rfl⟩ : syracuseStep 2757455 = 4136183) B4136183
theorem B2069327 : Blo 814346 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B1840103 : Blo 814346 1840103 := bstep (se 1 (by rfl) ⟨1380077, by rfl⟩ : syracuseStep 1840103 = 2760155) B2760155
theorem B2757779 : Blo 814346 2757779 := bstep (se 1 (by rfl) ⟨2068334, by rfl⟩ : syracuseStep 2757779 = 4136669) B4136669
theorem B9278711 : Blo 814346 9278711 := bstep (se 1 (by rfl) ⟨6959033, by rfl⟩ : syracuseStep 9278711 = 13918067) B13918067
theorem B4658471 : Blo 814346 4658471 := bstep (se 1 (by rfl) ⟨3493853, by rfl⟩ : syracuseStep 4658471 = 6987707) B6987707
theorem B4134239 : Blo 814346 4134239 := bstep (se 1 (by rfl) ⟨3100679, by rfl⟩ : syracuseStep 4134239 = 6201359) B6201359
theorem B1840481 : Blo 814346 1840481 := bstep (se 2 (by rfl) ⟨690180, by rfl⟩ : syracuseStep 1840481 = 1380361) B1380361
theorem B2758049 : Blo 814346 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B1840571 : Blo 814346 1840571 := bstep (se 1 (by rfl) ⟨1380428, by rfl⟩ : syracuseStep 1840571 = 2760857) B2760857
theorem B2069975 : Blo 814346 2069975 := bstep (se 1 (by rfl) ⟨1552481, by rfl⟩ : syracuseStep 2069975 = 3104963) B3104963
theorem B14358059 : Blo 814346 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1840697 : Blo 814346 1840697 := bstep (se 2 (by rfl) ⟨690261, by rfl⟩ : syracuseStep 1840697 = 1380523) B1380523
theorem B2070319 : Blo 814346 2070319 := bstep (se 1 (by rfl) ⟨1552739, by rfl⟩ : syracuseStep 2070319 = 3105479) B3105479
theorem B1742647 : Blo 814346 1742647 := bstep (se 1 (by rfl) ⟨1306985, by rfl⟩ : syracuseStep 1742647 = 2613971) B2613971
theorem B15898427 : Blo 814346 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B2070967 : Blo 814346 2070967 := bstep (se 1 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 2070967 = 3106451) B3106451
theorem B3349055 : Blo 814346 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B1743535 : Blo 814346 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B2202511 : Blo 814346 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B21502903 : Blo 814346 21502903 := bstep (se 1 (by rfl) ⟨16127177, by rfl⟩ : syracuseStep 21502903 = 32254355) B32254355
theorem B826319 : Blo 814346 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B7445627 : Blo 814346 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B40180931 : Blo 814346 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B5217817 : Blo 814346 5217817 := bstep (se 2 (by rfl) ⟨1956681, by rfl⟩ : syracuseStep 5217817 = 3913363) B3913363
theorem B4136507 : Blo 814346 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B827815 : Blo 814346 827815 := bstep (se 1 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 827815 = 1241723) B1241723
theorem B1745363 : Blo 814346 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B2761235 : Blo 814346 2761235 := bstep (se 1 (by rfl) ⟨2070926, by rfl⟩ : syracuseStep 2761235 = 4141853) B4141853
theorem B3482183 : Blo 814346 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B4465249 : Blo 814346 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B2204587 : Blo 814346 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B6202331 : Blo 814346 6202331 := bstep (se 1 (by rfl) ⟨4651748, by rfl⟩ : syracuseStep 6202331 = 9303497) B9303497
theorem B4138127 : Blo 814346 4138127 := bstep (se 1 (by rfl) ⟨3103595, by rfl⟩ : syracuseStep 4138127 = 6207191) B6207191
theorem B1221851 : Blo 814346 1221851 := bstep (se 1 (by rfl) ⟨916388, by rfl⟩ : syracuseStep 1221851 = 1832777) B1832777
theorem B6989105 : Blo 814346 6989105 := bstep (se 2 (by rfl) ⟨2620914, by rfl⟩ : syracuseStep 6989105 = 5241829) B5241829
theorem B3581293 : Blo 814346 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1222025 : Blo 814346 1222025 := bstep (se 2 (by rfl) ⟨458259, by rfl⟩ : syracuseStep 1222025 = 916519) B916519
theorem B828991 : Blo 814346 828991 := bstep (se 1 (by rfl) ⟨621743, by rfl⟩ : syracuseStep 828991 = 1243487) B1243487
theorem B1222379 : Blo 814346 1222379 := bstep (se 1 (by rfl) ⟨916784, by rfl⟩ : syracuseStep 1222379 = 1833569) B1833569
theorem B1222607 : Blo 814346 1222607 := bstep (se 1 (by rfl) ⟨916955, by rfl⟩ : syracuseStep 1222607 = 1833911) B1833911
theorem B2205949 : Blo 814346 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B4139261 : Blo 814346 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B1223003 : Blo 814346 1223003 := bstep (se 1 (by rfl) ⟨917252, by rfl⟩ : syracuseStep 1223003 = 1834505) B1834505
theorem B1223231 : Blo 814346 1223231 := bstep (se 1 (by rfl) ⟨917423, by rfl⟩ : syracuseStep 1223231 = 1834847) B1834847
theorem B1223351 : Blo 814346 1223351 := bstep (se 1 (by rfl) ⟨917513, by rfl⟩ : syracuseStep 1223351 = 1835027) B1835027
theorem B4467581 : Blo 814346 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B3484559 : Blo 814346 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B1223579 : Blo 814346 1223579 := bstep (se 1 (by rfl) ⟨917684, by rfl⟩ : syracuseStep 1223579 = 1835369) B1835369
theorem B3484711 : Blo 814346 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B4140071 : Blo 814346 4140071 := bstep (se 1 (by rfl) ⟨3105053, by rfl⟩ : syracuseStep 4140071 = 6210107) B6210107
theorem B17017937 : Blo 814346 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B6991019 : Blo 814346 6991019 := bstep (se 1 (by rfl) ⟨5243264, by rfl⟩ : syracuseStep 6991019 = 10486529) B10486529
theorem B2239721 : Blo 814346 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B1223975 : Blo 814346 1223975 := bstep (se 1 (by rfl) ⟨917981, by rfl⟩ : syracuseStep 1223975 = 1835963) B1835963
theorem B1224059 : Blo 814346 1224059 := bstep (se 1 (by rfl) ⟨918044, by rfl⟩ : syracuseStep 1224059 = 1836089) B1836089
theorem B1224185 : Blo 814346 1224185 := bstep (se 2 (by rfl) ⟨459069, by rfl⟩ : syracuseStep 1224185 = 918139) B918139
theorem B31763981 : Blo 814346 31763981 := bstep (se 3 (by rfl) ⟨5955746, by rfl⟩ : syracuseStep 31763981 = 11911493) B11911493
theorem B1224287 : Blo 814346 1224287 := bstep (se 1 (by rfl) ⟨918215, by rfl⟩ : syracuseStep 1224287 = 1836431) B1836431
theorem B1224503 : Blo 814346 1224503 := bstep (se 1 (by rfl) ⟨918377, by rfl⟩ : syracuseStep 1224503 = 1836755) B1836755
theorem B3092539 : Blo 814346 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B1224809 : Blo 814346 1224809 := bstep (se 2 (by rfl) ⟨459303, by rfl⟩ : syracuseStep 1224809 = 918607) B918607
theorem B3092843 : Blo 814346 3092843 := bstep (se 1 (by rfl) ⟨2319632, by rfl⟩ : syracuseStep 3092843 = 4639265) B4639265
theorem B1225127 : Blo 814346 1225127 := bstep (se 1 (by rfl) ⟨918845, by rfl⟩ : syracuseStep 1225127 = 1837691) B1837691
theorem B1225211 : Blo 814346 1225211 := bstep (se 1 (by rfl) ⟨918908, by rfl⟩ : syracuseStep 1225211 = 1837817) B1837817
theorem B3093011 : Blo 814346 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B1225337 : Blo 814346 1225337 := bstep (se 2 (by rfl) ⟨459501, by rfl⟩ : syracuseStep 1225337 = 919003) B919003
theorem B1225391 : Blo 814346 1225391 := bstep (se 1 (by rfl) ⟨919043, by rfl⟩ : syracuseStep 1225391 = 1838087) B1838087
theorem B1225439 : Blo 814346 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B1225703 : Blo 814346 1225703 := bstep (se 1 (by rfl) ⟨919277, by rfl⟩ : syracuseStep 1225703 = 1838555) B1838555
theorem B4142177 : Blo 814346 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B1225961 : Blo 814346 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B1226015 : Blo 814346 1226015 := bstep (se 1 (by rfl) ⟨919511, by rfl⟩ : syracuseStep 1226015 = 1839023) B1839023
theorem B1226183 : Blo 814346 1226183 := bstep (se 1 (by rfl) ⟨919637, by rfl⟩ : syracuseStep 1226183 = 1839275) B1839275
theorem B1161001 : Blo 814346 1161001 := bstep (se 2 (by rfl) ⟨435375, by rfl⟩ : syracuseStep 1161001 = 870751) B870751
theorem B1226537 : Blo 814346 1226537 := bstep (se 2 (by rfl) ⟨459951, by rfl⟩ : syracuseStep 1226537 = 919903) B919903
theorem B1226543 : Blo 814346 1226543 := bstep (se 1 (by rfl) ⟨919907, by rfl⟩ : syracuseStep 1226543 = 1839815) B1839815
theorem B1227017 : Blo 814346 1227017 := bstep (se 2 (by rfl) ⟨460131, by rfl⟩ : syracuseStep 1227017 = 920263) B920263
theorem B1227119 : Blo 814346 1227119 := bstep (se 1 (by rfl) ⟨920339, by rfl⟩ : syracuseStep 1227119 = 1840679) B1840679
theorem B1227335 : Blo 814346 1227335 := bstep (se 1 (by rfl) ⟨920501, by rfl⟩ : syracuseStep 1227335 = 1841003) B1841003
theorem B1227371 : Blo 814346 1227371 := bstep (se 1 (by rfl) ⟨920528, by rfl⟩ : syracuseStep 1227371 = 1841057) B1841057
theorem B1325791 : Blo 814346 1325791 := bstep (se 1 (by rfl) ⟨994343, by rfl⟩ : syracuseStep 1325791 = 1988687) B1988687
theorem B1162459 : Blo 814346 1162459 := bstep (se 1 (by rfl) ⟨871844, by rfl⟩ : syracuseStep 1162459 = 1743689) B1743689
theorem B3489085 : Blo 814346 3489085 := bstep (se 3 (by rfl) ⟨654203, by rfl⟩ : syracuseStep 3489085 = 1308407) B1308407
theorem B3095927 : Blo 814346 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B4767113 : Blo 814346 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B2211563 : Blo 814346 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B9290375 : Blo 814346 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B7849061 : Blo 814346 7849061 := bstep (se 4 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 7849061 = 1471699) B1471699
theorem B5883425 : Blo 814346 5883425 := bstep (se 2 (by rfl) ⟨2206284, by rfl⟩ : syracuseStep 5883425 = 4412569) B4412569
theorem B1033823 : Blo 814346 1033823 := bstep (se 1 (by rfl) ⟨775367, by rfl⟩ : syracuseStep 1033823 = 1550735) B1550735
theorem B6211565 : Blo 814346 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B3918071 : Blo 814346 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B1034527 : Blo 814346 1034527 := bstep (se 1 (by rfl) ⟨775895, by rfl⟩ : syracuseStep 1034527 = 1551791) B1551791
theorem B28330373 : Blo 814346 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B6212051 : Blo 814346 6212051 := bstep (se 1 (by rfl) ⟨4659038, by rfl⟩ : syracuseStep 6212051 = 9318077) B9318077
theorem B3099131 : Blo 814346 3099131 := bstep (se 1 (by rfl) ⟨2324348, by rfl⟩ : syracuseStep 3099131 = 4648697) B4648697
theorem B871007 : Blo 814346 871007 := bstep (se 1 (by rfl) ⟨653255, by rfl⟩ : syracuseStep 871007 = 1306511) B1306511
theorem B5655329 : Blo 814346 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B5884807 : Blo 814346 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B4410557 : Blo 814346 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B1101223 : Blo 814346 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B24169907 : Blo 814346 24169907 := bstep (se 1 (by rfl) ⟨18127430, by rfl⟩ : syracuseStep 24169907 = 36254861) B36254861
theorem B3493307 : Blo 814346 3493307 := bstep (se 1 (by rfl) ⟨2619980, by rfl⟩ : syracuseStep 3493307 = 5239961) B5239961
theorem B3100103 : Blo 814346 3100103 := bstep (se 1 (by rfl) ⟨2325077, by rfl⟩ : syracuseStep 3100103 = 4650155) B4650155
theorem B3493459 : Blo 814346 3493459 := bstep (se 1 (by rfl) ⟨2620094, by rfl⟩ : syracuseStep 3493459 = 5240189) B5240189
theorem B1101547 : Blo 814346 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B21221189 : Blo 814346 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B5361665 : Blo 814346 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B70504505 : Blo 814346 70504505 := bstep (se 2 (by rfl) ⟨26439189, by rfl⟩ : syracuseStep 70504505 = 52878379) B52878379
theorem B6213995 : Blo 814346 6213995 := bstep (se 1 (by rfl) ⟨4660496, by rfl⟩ : syracuseStep 6213995 = 9320993) B9320993
theorem B873023 : Blo 814346 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B2610139 : Blo 814346 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B3528031 : Blo 814346 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B3102047 : Blo 814346 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B7558505 : Blo 814346 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B31414067 : Blo 814346 31414067 := bstep (se 1 (by rfl) ⟨23560550, by rfl⟩ : syracuseStep 31414067 = 47121101) B47121101
theorem B75520289 : Blo 814346 75520289 := bstep (se 2 (by rfl) ⟨28320108, by rfl⟩ : syracuseStep 75520289 = 56640217) B56640217
theorem B2939303 : Blo 814346 2939303 := bstep (se 1 (by rfl) ⟨2204477, by rfl⟩ : syracuseStep 2939303 = 4408955) B4408955
theorem B2480719 : Blo 814346 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B3922607 : Blo 814346 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B13229405 : Blo 814346 13229405 := bstep (se 3 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 13229405 = 4961027) B4961027
theorem B1958575 : Blo 814346 1958575 := bstep (se 1 (by rfl) ⟨1468931, by rfl⟩ : syracuseStep 1958575 = 2937863) B2937863
theorem B6710369 : Blo 814346 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B3105935 : Blo 814346 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B8512705 : Blo 814346 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B3302633 : Blo 814346 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B3729239 : Blo 814346 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B3729689 : Blo 814346 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B6285605 : Blo 814346 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B10447163 : Blo 814346 10447163 := bstep (se 1 (by rfl) ⟨7835372, by rfl⟩ : syracuseStep 10447163 = 15670745) B15670745
theorem B1304999 : Blo 814346 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B4123547 : Blo 814346 4123547 := bstep (se 1 (by rfl) ⟨3092660, by rfl⟩ : syracuseStep 4123547 = 6185321) B6185321
theorem B1305499 : Blo 814346 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B25128107 : Blo 814346 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B814367 : Blo 814346 814367 := bstep (se 1 (by rfl) ⟨610775, by rfl⟩ : syracuseStep 814367 = 1221551) B1221551
theorem B814427 : Blo 814346 814427 := bstep (se 1 (by rfl) ⟨610820, by rfl⟩ : syracuseStep 814427 = 1221641) B1221641
theorem B814447 : Blo 814346 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B1469819 : Blo 814346 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B4124033 : Blo 814346 4124033 := bstep (se 2 (by rfl) ⟨1546512, by rfl⟩ : syracuseStep 4124033 = 3093025) B3093025
theorem B814503 : Blo 814346 814503 := bstep (se 1 (by rfl) ⟨610877, by rfl⟩ : syracuseStep 814503 = 1221755) B1221755
theorem B814587 : Blo 814346 814587 := bstep (se 1 (by rfl) ⟨610940, by rfl⟩ : syracuseStep 814587 = 1221881) B1221881
theorem B814655 : Blo 814346 814655 := bstep (se 1 (by rfl) ⟨610991, by rfl⟩ : syracuseStep 814655 = 1221983) B1221983
theorem B814663 : Blo 814346 814663 := bstep (se 1 (by rfl) ⟨610997, by rfl⟩ : syracuseStep 814663 = 1221995) B1221995
theorem B3927761 : Blo 814346 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B814815 : Blo 814346 814815 := bstep (se 1 (by rfl) ⟨611111, by rfl⟩ : syracuseStep 814815 = 1222223) B1222223
theorem B3305195 : Blo 814346 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B4419335 : Blo 814346 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B814895 : Blo 814346 814895 := bstep (se 1 (by rfl) ⟨611171, by rfl⟩ : syracuseStep 814895 = 1222343) B1222343
theorem B1863479 : Blo 814346 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B815003 : Blo 814346 815003 := bstep (se 1 (by rfl) ⟨611252, by rfl⟩ : syracuseStep 815003 = 1222505) B1222505
theorem B815055 : Blo 814346 815055 := bstep (se 1 (by rfl) ⟨611291, by rfl⟩ : syracuseStep 815055 = 1222583) B1222583
theorem B815079 : Blo 814346 815079 := bstep (se 1 (by rfl) ⟨611309, by rfl⟩ : syracuseStep 815079 = 1222619) B1222619
theorem B4124681 : Blo 814346 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B1306729 : Blo 814346 1306729 := bstep (se 2 (by rfl) ⟨490023, by rfl⟩ : syracuseStep 1306729 = 980047) B980047
theorem B4124843 : Blo 814346 4124843 := bstep (se 1 (by rfl) ⟨3093632, by rfl⟩ : syracuseStep 4124843 = 6187265) B6187265
theorem B3305681 : Blo 814346 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B815391 : Blo 814346 815391 := bstep (se 1 (by rfl) ⟨611543, by rfl⟩ : syracuseStep 815391 = 1223087) B1223087
theorem B815451 : Blo 814346 815451 := bstep (se 1 (by rfl) ⟨611588, by rfl⟩ : syracuseStep 815451 = 1223177) B1223177
theorem B815471 : Blo 814346 815471 := bstep (se 1 (by rfl) ⟨611603, by rfl⟩ : syracuseStep 815471 = 1223207) B1223207
theorem B815527 : Blo 814346 815527 := bstep (se 1 (by rfl) ⟨611645, by rfl⟩ : syracuseStep 815527 = 1223291) B1223291
theorem B2322913 : Blo 814346 2322913 := bstep (se 2 (by rfl) ⟨871092, by rfl⟩ : syracuseStep 2322913 = 1742185) B1742185
theorem B815611 : Blo 814346 815611 := bstep (se 1 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 815611 = 1223417) B1223417
theorem B7565885 : Blo 814346 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B815679 : Blo 814346 815679 := bstep (se 1 (by rfl) ⟨611759, by rfl⟩ : syracuseStep 815679 = 1223519) B1223519
theorem B815687 : Blo 814346 815687 := bstep (se 1 (by rfl) ⟨611765, by rfl⟩ : syracuseStep 815687 = 1223531) B1223531
theorem B4125329 : Blo 814346 4125329 := bstep (se 2 (by rfl) ⟨1546998, by rfl⟩ : syracuseStep 4125329 = 3093997) B3093997
theorem B1471151 : Blo 814346 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B1077943 : Blo 814346 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B815839 : Blo 814346 815839 := bstep (se 1 (by rfl) ⟨611879, by rfl⟩ : syracuseStep 815839 = 1223759) B1223759
theorem B815919 : Blo 814346 815919 := bstep (se 1 (by rfl) ⟨611939, by rfl⟩ : syracuseStep 815919 = 1223879) B1223879
theorem B816027 : Blo 814346 816027 := bstep (se 1 (by rfl) ⟨612020, by rfl⟩ : syracuseStep 816027 = 1224041) B1224041
theorem B816079 : Blo 814346 816079 := bstep (se 1 (by rfl) ⟨612059, by rfl⟩ : syracuseStep 816079 = 1224119) B1224119
theorem B816103 : Blo 814346 816103 := bstep (se 1 (by rfl) ⟨612077, by rfl⟩ : syracuseStep 816103 = 1224155) B1224155
theorem B1307639 : Blo 814346 1307639 := bstep (se 1 (by rfl) ⟨980729, by rfl⟩ : syracuseStep 1307639 = 1961459) B1961459
theorem B2061409 : Blo 814346 2061409 := bstep (se 2 (by rfl) ⟨773028, by rfl⟩ : syracuseStep 2061409 = 1546057) B1546057
theorem B1570079 : Blo 814346 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B816415 : Blo 814346 816415 := bstep (se 1 (by rfl) ⟨612311, by rfl⟩ : syracuseStep 816415 = 1224623) B1224623
theorem B31782203 : Blo 814346 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B816475 : Blo 814346 816475 := bstep (se 1 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 816475 = 1224713) B1224713
theorem B3306847 : Blo 814346 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B816495 : Blo 814346 816495 := bstep (se 1 (by rfl) ⟨612371, by rfl⟩ : syracuseStep 816495 = 1224743) B1224743
theorem B816551 : Blo 814346 816551 := bstep (se 1 (by rfl) ⟨612413, by rfl⟩ : syracuseStep 816551 = 1224827) B1224827
theorem B816635 : Blo 814346 816635 := bstep (se 1 (by rfl) ⟨612476, by rfl⟩ : syracuseStep 816635 = 1224953) B1224953
theorem B816703 : Blo 814346 816703 := bstep (se 1 (by rfl) ⟨612527, by rfl⟩ : syracuseStep 816703 = 1225055) B1225055
theorem B816711 : Blo 814346 816711 := bstep (se 1 (by rfl) ⟨612533, by rfl⟩ : syracuseStep 816711 = 1225067) B1225067
theorem B1832543 : Blo 814346 1832543 := bstep (se 1 (by rfl) ⟨1374407, by rfl⟩ : syracuseStep 1832543 = 2748815) B2748815
theorem B816863 : Blo 814346 816863 := bstep (se 1 (by rfl) ⟨612647, by rfl⟩ : syracuseStep 816863 = 1225295) B1225295
theorem B816943 : Blo 814346 816943 := bstep (se 1 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 816943 = 1225415) B1225415
theorem B1832759 : Blo 814346 1832759 := bstep (se 1 (by rfl) ⟨1374569, by rfl⟩ : syracuseStep 1832759 = 2749139) B2749139
theorem B817051 : Blo 814346 817051 := bstep (se 1 (by rfl) ⟨612788, by rfl⟩ : syracuseStep 817051 = 1225577) B1225577
theorem B11761595 : Blo 814346 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B817103 : Blo 814346 817103 := bstep (se 1 (by rfl) ⟨612827, by rfl⟩ : syracuseStep 817103 = 1225655) B1225655
theorem B817127 : Blo 814346 817127 := bstep (se 1 (by rfl) ⟨612845, by rfl⟩ : syracuseStep 817127 = 1225691) B1225691
theorem B2062361 : Blo 814346 2062361 := bstep (se 2 (by rfl) ⟨773385, by rfl⟩ : syracuseStep 2062361 = 1546771) B1546771
theorem B1374313 : Blo 814346 1374313 := bstep (se 2 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 1374313 = 1030735) B1030735
theorem B1833065 : Blo 814346 1833065 := bstep (se 2 (by rfl) ⟨687399, by rfl⟩ : syracuseStep 1833065 = 1374799) B1374799
theorem B817439 : Blo 814346 817439 := bstep (se 1 (by rfl) ⟨613079, by rfl⟩ : syracuseStep 817439 = 1226159) B1226159
theorem B817499 : Blo 814346 817499 := bstep (se 1 (by rfl) ⟨613124, by rfl⟩ : syracuseStep 817499 = 1226249) B1226249
theorem B817519 : Blo 814346 817519 := bstep (se 1 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 817519 = 1226279) B1226279
theorem B817575 : Blo 814346 817575 := bstep (se 1 (by rfl) ⟨613181, by rfl⟩ : syracuseStep 817575 = 1226363) B1226363
theorem B2062817 : Blo 814346 2062817 := bstep (se 2 (by rfl) ⟨773556, by rfl⟩ : syracuseStep 2062817 = 1547113) B1547113
theorem B2324987 : Blo 814346 2324987 := bstep (se 1 (by rfl) ⟨1743740, by rfl⟩ : syracuseStep 2324987 = 3487481) B3487481
theorem B817659 : Blo 814346 817659 := bstep (se 1 (by rfl) ⟨613244, by rfl⟩ : syracuseStep 817659 = 1226489) B1226489
theorem B2062867 : Blo 814346 2062867 := bstep (se 1 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 2062867 = 3094301) B3094301
theorem B14154263 : Blo 814346 14154263 := bstep (se 1 (by rfl) ⟨10615697, by rfl⟩ : syracuseStep 14154263 = 21231395) B21231395
theorem B817727 : Blo 814346 817727 := bstep (se 1 (by rfl) ⟨613295, by rfl⟩ : syracuseStep 817727 = 1226591) B1226591
theorem B817735 : Blo 814346 817735 := bstep (se 1 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 817735 = 1226603) B1226603
theorem B1833551 : Blo 814346 1833551 := bstep (se 1 (by rfl) ⟨1375163, by rfl⟩ : syracuseStep 1833551 = 2750327) B2750327
theorem B2751083 : Blo 814346 2751083 := bstep (se 1 (by rfl) ⟨2063312, by rfl⟩ : syracuseStep 2751083 = 4126625) B4126625
theorem B8059499 : Blo 814346 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1833695 : Blo 814346 1833695 := bstep (se 1 (by rfl) ⟨1375271, by rfl⟩ : syracuseStep 1833695 = 2750543) B2750543
theorem B817887 : Blo 814346 817887 := bstep (se 1 (by rfl) ⟨613415, by rfl⟩ : syracuseStep 817887 = 1226831) B1226831
theorem B817967 : Blo 814346 817967 := bstep (se 1 (by rfl) ⟨613475, by rfl⟩ : syracuseStep 817967 = 1226951) B1226951
theorem B981815 : Blo 814346 981815 := bstep (se 1 (by rfl) ⟨736361, by rfl⟩ : syracuseStep 981815 = 1472723) B1472723
theorem B916303 : Blo 814346 916303 := bstep (se 1 (by rfl) ⟨687227, by rfl⟩ : syracuseStep 916303 = 1374455) B1374455
theorem B4651931 : Blo 814346 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B818075 : Blo 814346 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B2325419 : Blo 814346 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B818127 : Blo 814346 818127 := bstep (se 1 (by rfl) ⟨613595, by rfl⟩ : syracuseStep 818127 = 1227191) B1227191
theorem B1833947 : Blo 814346 1833947 := bstep (se 1 (by rfl) ⟨1375460, by rfl⟩ : syracuseStep 1833947 = 2750921) B2750921
theorem B818151 : Blo 814346 818151 := bstep (se 1 (by rfl) ⟨613613, by rfl⟩ : syracuseStep 818151 = 1227227) B1227227
theorem B2620403 : Blo 814346 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B4127759 : Blo 814346 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B3275815 : Blo 814346 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B1834127 : Blo 814346 1834127 := bstep (se 1 (by rfl) ⟨1375595, by rfl⟩ : syracuseStep 1834127 = 2751191) B2751191
theorem B2751677 : Blo 814346 2751677 := bstep (se 3 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 2751677 = 1031879) B1031879
theorem B916699 : Blo 814346 916699 := bstep (se 1 (by rfl) ⟨687524, by rfl⟩ : syracuseStep 916699 = 1375049) B1375049
theorem B1834217 : Blo 814346 1834217 := bstep (se 2 (by rfl) ⟨687831, by rfl⟩ : syracuseStep 1834217 = 1375663) B1375663
theorem B1834271 : Blo 814346 1834271 := bstep (se 1 (by rfl) ⟨1375703, by rfl⟩ : syracuseStep 1834271 = 2751407) B2751407
theorem B982363 : Blo 814346 982363 := bstep (se 1 (by rfl) ⟨736772, by rfl⟩ : syracuseStep 982363 = 1473545) B1473545
theorem B12582281 : Blo 814346 12582281 := bstep (se 2 (by rfl) ⟨4718355, by rfl⟩ : syracuseStep 12582281 = 9436711) B9436711
theorem B916987 : Blo 814346 916987 := bstep (se 1 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 916987 = 1375481) B1375481
theorem B4652639 : Blo 814346 4652639 := bstep (se 1 (by rfl) ⟨3489479, by rfl⟩ : syracuseStep 4652639 = 6978959) B6978959
theorem B917167 : Blo 814346 917167 := bstep (se 1 (by rfl) ⟨687875, by rfl⟩ : syracuseStep 917167 = 1375751) B1375751
theorem B1376041 : Blo 814346 1376041 := bstep (se 2 (by rfl) ⟨516015, by rfl⟩ : syracuseStep 1376041 = 1032031) B1032031
theorem B1834793 : Blo 814346 1834793 := bstep (se 2 (by rfl) ⟨688047, by rfl⟩ : syracuseStep 1834793 = 1376095) B1376095
theorem B4128569 : Blo 814346 4128569 := bstep (se 2 (by rfl) ⟨1548213, by rfl⟩ : syracuseStep 4128569 = 3096427) B3096427
theorem B2948993 : Blo 814346 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B917455 : Blo 814346 917455 := bstep (se 1 (by rfl) ⟨688091, by rfl⟩ : syracuseStep 917455 = 1376183) B1376183
theorem B2621479 : Blo 814346 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B2621659 : Blo 814346 2621659 := bstep (se 1 (by rfl) ⟨1966244, by rfl⟩ : syracuseStep 2621659 = 3932489) B3932489
theorem B2752865 : Blo 814346 2752865 := bstep (se 2 (by rfl) ⟨1032324, by rfl⟩ : syracuseStep 2752865 = 2064649) B2064649
theorem B917887 : Blo 814346 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B6193583 : Blo 814346 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B4129703 : Blo 814346 4129703 := bstep (se 1 (by rfl) ⟨3097277, by rfl⟩ : syracuseStep 4129703 = 6194555) B6194555
theorem B1836395 : Blo 814346 1836395 := bstep (se 1 (by rfl) ⟨1377296, by rfl⟩ : syracuseStep 1836395 = 2754593) B2754593
theorem B2360927 : Blo 814346 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B15664751 : Blo 814346 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B1836665 : Blo 814346 1836665 := bstep (se 2 (by rfl) ⟨688749, by rfl⟩ : syracuseStep 1836665 = 1377499) B1377499
theorem B2754215 : Blo 814346 2754215 := bstep (se 1 (by rfl) ⟨2065661, by rfl⟩ : syracuseStep 2754215 = 4131323) B4131323
theorem B2066087 : Blo 814346 2066087 := bstep (se 1 (by rfl) ⟨1549565, by rfl⟩ : syracuseStep 2066087 = 3099131) B3099131
theorem B919291 : Blo 814346 919291 := bstep (se 1 (by rfl) ⟨689468, by rfl⟩ : syracuseStep 919291 = 1378937) B1378937
theorem B919327 : Blo 814346 919327 := bstep (se 1 (by rfl) ⟨689495, by rfl⟩ : syracuseStep 919327 = 1378991) B1378991
theorem B1378127 : Blo 814346 1378127 := bstep (se 1 (by rfl) ⟨1033595, by rfl⟩ : syracuseStep 1378127 = 2067191) B2067191
theorem B3770219 : Blo 814346 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B2754809 : Blo 814346 2754809 := bstep (se 2 (by rfl) ⟨1033053, by rfl⟩ : syracuseStep 2754809 = 2066107) B2066107
theorem B2328871 : Blo 814346 2328871 := bstep (se 1 (by rfl) ⟨1746653, by rfl⟩ : syracuseStep 2328871 = 3493307) B3493307
theorem B2754863 : Blo 814346 2754863 := bstep (se 1 (by rfl) ⟨2066147, by rfl⟩ : syracuseStep 2754863 = 4132295) B4132295
theorem B2066735 : Blo 814346 2066735 := bstep (se 1 (by rfl) ⟨1550051, by rfl⟩ : syracuseStep 2066735 = 3100103) B3100103
theorem B2755079 : Blo 814346 2755079 := bstep (se 1 (by rfl) ⟨2066309, by rfl⟩ : syracuseStep 2755079 = 4132619) B4132619
theorem B1837673 : Blo 814346 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B920479 : Blo 814346 920479 := bstep (se 1 (by rfl) ⟨690359, by rfl⟩ : syracuseStep 920479 = 1380719) B1380719
theorem B17894317 : Blo 814346 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B1379369 : Blo 814346 1379369 := bstep (se 2 (by rfl) ⟨517263, by rfl⟩ : syracuseStep 1379369 = 1034527) B1034527
theorem B920623 : Blo 814346 920623 := bstep (se 1 (by rfl) ⟨690467, by rfl⟩ : syracuseStep 920623 = 1380935) B1380935
theorem B2755727 : Blo 814346 2755727 := bstep (se 1 (by rfl) ⟨2066795, by rfl⟩ : syracuseStep 2755727 = 4133591) B4133591
theorem B1838303 : Blo 814346 1838303 := bstep (se 1 (by rfl) ⟨1378727, by rfl⟩ : syracuseStep 1838303 = 2757455) B2757455
theorem B1379551 : Blo 814346 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B1838519 : Blo 814346 1838519 := bstep (se 1 (by rfl) ⟨1378889, by rfl⟩ : syracuseStep 1838519 = 2757779) B2757779
theorem B2756159 : Blo 814346 2756159 := bstep (se 1 (by rfl) ⟨2067119, by rfl⟩ : syracuseStep 2756159 = 4134239) B4134239
theorem B2068031 : Blo 814346 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B1838699 : Blo 814346 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B1379983 : Blo 814346 1379983 := bstep (se 1 (by rfl) ⟨1034987, by rfl⟩ : syracuseStep 1379983 = 2069975) B2069975
theorem B9572039 : Blo 814346 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B20942711 : Blo 814346 20942711 := bstep (se 1 (by rfl) ⟨15707033, by rfl⟩ : syracuseStep 20942711 = 31414067) B31414067
theorem B1740665 : Blo 814346 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B1838969 : Blo 814346 1838969 := bstep (se 2 (by rfl) ⟨689613, by rfl⟩ : syracuseStep 1838969 = 1379227) B1379227
theorem B2756861 : Blo 814346 2756861 := bstep (se 3 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 2756861 = 1033823) B1033823
theorem B2232703 : Blo 814346 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B2757401 : Blo 814346 2757401 := bstep (se 2 (by rfl) ⟨1034025, by rfl⟩ : syracuseStep 2757401 = 2068051) B2068051
theorem B4657945 : Blo 814346 4657945 := bstep (se 2 (by rfl) ⟨1746729, by rfl⟩ : syracuseStep 4657945 = 3493459) B3493459
theorem B8819603 : Blo 814346 8819603 := bstep (se 1 (by rfl) ⟨6614702, by rfl⟩ : syracuseStep 8819603 = 13229405) B13229405
theorem B2757671 : Blo 814346 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B1742305 : Blo 814346 1742305 := bstep (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) B1306729
theorem B1840823 : Blo 814346 1840823 := bstep (se 1 (by rfl) ⟨1380617, by rfl⟩ : syracuseStep 1840823 = 2761235) B2761235
theorem B4134887 : Blo 814346 4134887 := bstep (se 1 (by rfl) ⟨3101165, by rfl⟩ : syracuseStep 4134887 = 6202331) B6202331
theorem B9312245 : Blo 814346 9312245 := bstep (se 5 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 9312245 = 873023) B873023
theorem B2758751 : Blo 814346 2758751 := bstep (se 1 (by rfl) ⟨2069063, by rfl⟩ : syracuseStep 2758751 = 4138127) B4138127
theorem B2070623 : Blo 814346 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B2201755 : Blo 814346 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B4659403 : Blo 814346 4659403 := bstep (se 1 (by rfl) ⟨3494552, by rfl⟩ : syracuseStep 4659403 = 6989105) B6989105
theorem B3480185 : Blo 814346 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B2759507 : Blo 814346 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B10460285 : Blo 814346 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B2760047 : Blo 814346 2760047 := bstep (se 1 (by rfl) ⟨2070035, by rfl⟩ : syracuseStep 2760047 = 4140071) B4140071
theorem B11345291 : Blo 814346 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B16752071 : Blo 814346 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B4660679 : Blo 814346 4660679 := bstep (se 1 (by rfl) ⟨3495509, by rfl⟩ : syracuseStep 4660679 = 6991019) B6991019
theorem B21175987 : Blo 814346 21175987 := bstep (se 1 (by rfl) ⟨15881990, by rfl⟩ : syracuseStep 21175987 = 31763981) B31763981
theorem B1548001 : Blo 814346 1548001 := bstep (se 2 (by rfl) ⟨580500, by rfl⟩ : syracuseStep 1548001 = 1161001) B1161001
theorem B2760425 : Blo 814346 2760425 := bstep (se 2 (by rfl) ⟨1035159, by rfl⟩ : syracuseStep 2760425 = 2070319) B2070319
theorem B2203463 : Blo 814346 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B2203517 : Blo 814346 2203517 := bstep (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) B826319
theorem B2203787 : Blo 814346 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B2761289 : Blo 814346 2761289 := bstep (se 2 (by rfl) ⟨1035483, by rfl⟩ : syracuseStep 2761289 = 2070967) B2070967
theorem B2761451 : Blo 814346 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B1221695 : Blo 814346 1221695 := bstep (se 1 (by rfl) ⟨916271, by rfl⟩ : syracuseStep 1221695 = 1832543) B1832543
theorem B1221737 : Blo 814346 1221737 := bstep (se 2 (by rfl) ⟨458151, by rfl⟩ : syracuseStep 1221737 = 916303) B916303
theorem B1221839 : Blo 814346 1221839 := bstep (se 1 (by rfl) ⟨916379, by rfl⟩ : syracuseStep 1221839 = 1832759) B1832759
theorem B7841063 : Blo 814346 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B4367753 : Blo 814346 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B1222043 : Blo 814346 1222043 := bstep (se 1 (by rfl) ⟨916532, by rfl⟩ : syracuseStep 1222043 = 1833065) B1833065
theorem B1222265 : Blo 814346 1222265 := bstep (se 2 (by rfl) ⟨458349, by rfl⟩ : syracuseStep 1222265 = 916699) B916699
theorem B1549945 : Blo 814346 1549945 := bstep (se 2 (by rfl) ⟨581229, by rfl⟩ : syracuseStep 1549945 = 1162459) B1162459
theorem B1549991 : Blo 814346 1549991 := bstep (se 1 (by rfl) ⟨1162493, by rfl⟩ : syracuseStep 1549991 = 2324987) B2324987
theorem B1222367 : Blo 814346 1222367 := bstep (se 1 (by rfl) ⟨916775, by rfl⟩ : syracuseStep 1222367 = 1833551) B1833551
theorem B1222463 : Blo 814346 1222463 := bstep (se 1 (by rfl) ⟨916847, by rfl⟩ : syracuseStep 1222463 = 1833695) B1833695
theorem B1550279 : Blo 814346 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B1222631 : Blo 814346 1222631 := bstep (se 1 (by rfl) ⟨916973, by rfl⟩ : syracuseStep 1222631 = 1833947) B1833947
theorem B1746935 : Blo 814346 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B1222649 : Blo 814346 1222649 := bstep (se 2 (by rfl) ⟨458493, by rfl⟩ : syracuseStep 1222649 = 916987) B916987
theorem B6957089 : Blo 814346 6957089 := bstep (se 2 (by rfl) ⟨2608908, by rfl⟩ : syracuseStep 6957089 = 5217817) B5217817
theorem B1222751 : Blo 814346 1222751 := bstep (se 1 (by rfl) ⟨917063, by rfl⟩ : syracuseStep 1222751 = 1834127) B1834127
theorem B1222811 : Blo 814346 1222811 := bstep (se 1 (by rfl) ⟨917108, by rfl⟩ : syracuseStep 1222811 = 1834217) B1834217
theorem B1222847 : Blo 814346 1222847 := bstep (se 1 (by rfl) ⟨917135, by rfl⟩ : syracuseStep 1222847 = 1834271) B1834271
theorem B1222889 : Blo 814346 1222889 := bstep (se 2 (by rfl) ⟨458583, by rfl⟩ : syracuseStep 1222889 = 917167) B917167
theorem B1223195 : Blo 814346 1223195 := bstep (se 1 (by rfl) ⟨917396, by rfl⟩ : syracuseStep 1223195 = 1834793) B1834793
theorem B1223273 : Blo 814346 1223273 := bstep (se 2 (by rfl) ⟨458727, by rfl⟩ : syracuseStep 1223273 = 917455) B917455
theorem B57191093 : Blo 814346 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B1223801 : Blo 814346 1223801 := bstep (se 2 (by rfl) ⟨458925, by rfl⟩ : syracuseStep 1223801 = 917851) B917851
theorem B1223903 : Blo 814346 1223903 := bstep (se 1 (by rfl) ⟨917927, by rfl⟩ : syracuseStep 1223903 = 1835855) B1835855
theorem B1223945 : Blo 814346 1223945 := bstep (se 2 (by rfl) ⟨458979, by rfl⟩ : syracuseStep 1223945 = 917959) B917959
theorem B1224047 : Blo 814346 1224047 := bstep (se 1 (by rfl) ⟨918035, by rfl⟩ : syracuseStep 1224047 = 1836071) B1836071
theorem B1224167 : Blo 814346 1224167 := bstep (se 1 (by rfl) ⟨918125, by rfl⟩ : syracuseStep 1224167 = 1836251) B1836251
theorem B1551935 : Blo 814346 1551935 := bstep (se 1 (by rfl) ⟨1163951, by rfl⟩ : syracuseStep 1551935 = 2327903) B2327903
theorem B1224299 : Blo 814346 1224299 := bstep (se 1 (by rfl) ⟨918224, by rfl⟩ : syracuseStep 1224299 = 1836449) B1836449
theorem B1224425 : Blo 814346 1224425 := bstep (se 2 (by rfl) ⟨459159, by rfl⟩ : syracuseStep 1224425 = 918319) B918319
theorem B1224569 : Blo 814346 1224569 := bstep (se 2 (by rfl) ⟨459213, by rfl⟩ : syracuseStep 1224569 = 918427) B918427
theorem B1224671 : Blo 814346 1224671 := bstep (se 1 (by rfl) ⟨918503, by rfl⟩ : syracuseStep 1224671 = 1837007) B1837007
theorem B4141043 : Blo 814346 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B1224923 : Blo 814346 1224923 := bstep (se 1 (by rfl) ⟨918692, by rfl⟩ : syracuseStep 1224923 = 1837385) B1837385
theorem B1224935 : Blo 814346 1224935 := bstep (se 1 (by rfl) ⟨918701, by rfl⟩ : syracuseStep 1224935 = 1837403) B1837403
theorem B11350273 : Blo 814346 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B18886915 : Blo 814346 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B4141367 : Blo 814346 4141367 := bstep (se 1 (by rfl) ⟨3106025, by rfl⟩ : syracuseStep 4141367 = 6212051) B6212051
theorem B1225097 : Blo 814346 1225097 := bstep (se 2 (by rfl) ⟨459411, by rfl⟩ : syracuseStep 1225097 = 918823) B918823
theorem B1225193 : Blo 814346 1225193 := bstep (se 2 (by rfl) ⟨459447, by rfl⟩ : syracuseStep 1225193 = 918895) B918895
theorem B1225319 : Blo 814346 1225319 := bstep (se 1 (by rfl) ⟨918989, by rfl⟩ : syracuseStep 1225319 = 1837979) B1837979
theorem B1225451 : Blo 814346 1225451 := bstep (se 1 (by rfl) ⟨919088, by rfl⟩ : syracuseStep 1225451 = 1838177) B1838177
theorem B1225481 : Blo 814346 1225481 := bstep (se 2 (by rfl) ⟨459555, by rfl⟩ : syracuseStep 1225481 = 919111) B919111
theorem B1225583 : Blo 814346 1225583 := bstep (se 1 (by rfl) ⟨919187, by rfl⟩ : syracuseStep 1225583 = 1838375) B1838375
theorem B1225835 : Blo 814346 1225835 := bstep (se 1 (by rfl) ⟨919376, by rfl⟩ : syracuseStep 1225835 = 1838753) B1838753
theorem B1226075 : Blo 814346 1226075 := bstep (se 1 (by rfl) ⟨919556, by rfl⟩ : syracuseStep 1226075 = 1839113) B1839113
theorem B47003003 : Blo 814346 47003003 := bstep (se 1 (by rfl) ⟨35252252, by rfl⟩ : syracuseStep 47003003 = 70504505) B70504505
theorem B4961735 : Blo 814346 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B4142663 : Blo 814346 4142663 := bstep (se 1 (by rfl) ⟨3106997, by rfl⟩ : syracuseStep 4142663 = 6213995) B6213995
theorem B1226351 : Blo 814346 1226351 := bstep (se 1 (by rfl) ⟨919763, by rfl⟩ : syracuseStep 1226351 = 1839527) B1839527
theorem B2209451 : Blo 814346 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1160887 : Blo 814346 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B1226423 : Blo 814346 1226423 := bstep (se 1 (by rfl) ⟨919817, by rfl⟩ : syracuseStep 1226423 = 1839635) B1839635
theorem B16103123 : Blo 814346 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B7452371 : Blo 814346 7452371 := bstep (se 1 (by rfl) ⟨5589278, by rfl⟩ : syracuseStep 7452371 = 11178557) B11178557
theorem B1226459 : Blo 814346 1226459 := bstep (se 1 (by rfl) ⟨919844, by rfl⟩ : syracuseStep 1226459 = 1839689) B1839689
theorem B3913535 : Blo 814346 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B1226633 : Blo 814346 1226633 := bstep (se 2 (by rfl) ⟨459987, by rfl⟩ : syracuseStep 1226633 = 919975) B919975
theorem B1226735 : Blo 814346 1226735 := bstep (se 1 (by rfl) ⟨920051, by rfl⟩ : syracuseStep 1226735 = 1840103) B1840103
theorem B1226987 : Blo 814346 1226987 := bstep (se 1 (by rfl) ⟨920240, by rfl⟩ : syracuseStep 1226987 = 1840481) B1840481
theorem B1227047 : Blo 814346 1227047 := bstep (se 1 (by rfl) ⟨920285, by rfl⟩ : syracuseStep 1227047 = 1840571) B1840571
theorem B1227131 : Blo 814346 1227131 := bstep (se 1 (by rfl) ⟨920348, by rfl⟩ : syracuseStep 1227131 = 1840697) B1840697
theorem B7846409 : Blo 814346 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B10598951 : Blo 814346 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B11188853 : Blo 814346 11188853 := bstep (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) B1048955
theorem B1227401 : Blo 814346 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B50346859 : Blo 814346 50346859 := bstep (se 1 (by rfl) ⟨37760144, by rfl⟩ : syracuseStep 50346859 = 75520289) B75520289
theorem B4963751 : Blo 814346 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B26787287 : Blo 814346 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B1163575 : Blo 814346 1163575 := bstep (se 1 (by rfl) ⟨872681, by rfl⟩ : syracuseStep 1163575 = 1745363) B1745363
theorem B3097217 : Blo 814346 3097217 := bstep (se 2 (by rfl) ⟨1161456, by rfl⟩ : syracuseStep 3097217 = 2322913) B2322913
theorem B16761613 : Blo 814346 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B6964775 : Blo 814346 6964775 := bstep (se 1 (by rfl) ⟨5223581, by rfl⟩ : syracuseStep 6964775 = 10447163) B10447163
theorem B869999 : Blo 814346 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B4704041 : Blo 814346 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B4409129 : Blo 814346 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B1493147 : Blo 814346 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B871759 : Blo 814346 871759 := bstep (se 1 (by rfl) ⟨653819, by rfl⟩ : syracuseStep 871759 = 1307639) B1307639
theorem B21188135 : Blo 814346 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B2936681 : Blo 814346 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B3101287 : Blo 814346 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B3101759 : Blo 814346 3101759 := bstep (se 1 (by rfl) ⟨2326319, by rfl⟩ : syracuseStep 3101759 = 4652639) B4652639
theorem B1103753 : Blo 814346 1103753 := bstep (se 2 (by rfl) ⟨413907, by rfl⟩ : syracuseStep 1103753 = 827815) B827815
theorem B3102745 : Blo 814346 3102745 := bstep (se 2 (by rfl) ⟨1163529, by rfl⟩ : syracuseStep 3102745 = 2327059) B2327059
theorem B5232707 : Blo 814346 5232707 := bstep (se 1 (by rfl) ⟨3924530, by rfl⟩ : syracuseStep 5232707 = 7849061) B7849061
theorem B2611433 : Blo 814346 2611433 := bstep (se 2 (by rfl) ⟨979287, by rfl⟩ : syracuseStep 2611433 = 1958575) B1958575
theorem B3922283 : Blo 814346 3922283 := bstep (se 1 (by rfl) ⟨2941712, by rfl⟩ : syracuseStep 3922283 = 5883425) B5883425
theorem B2939449 : Blo 814346 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B22305455 : Blo 814346 22305455 := bstep (se 1 (by rfl) ⟨16729091, by rfl⟩ : syracuseStep 22305455 = 33458183) B33458183
theorem B4775057 : Blo 814346 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B1105321 : Blo 814346 1105321 := bstep (se 2 (by rfl) ⟨414495, by rfl⟩ : syracuseStep 1105321 = 828991) B828991
theorem B2940371 : Blo 814346 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B16113271 : Blo 814346 16113271 := bstep (se 1 (by rfl) ⟨12084953, by rfl⟩ : syracuseStep 16113271 = 24169907) B24169907
theorem B14147459 : Blo 814346 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B2941265 : Blo 814346 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B23814661 : Blo 814346 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B6185807 : Blo 814346 6185807 := bstep (se 1 (by rfl) ⟨4639355, by rfl⟩ : syracuseStep 6185807 = 9278711) B9278711
theorem B3105647 : Blo 814346 3105647 := bstep (se 1 (by rfl) ⟨2329235, by rfl⟩ : syracuseStep 3105647 = 4658471) B4658471
theorem B5039003 : Blo 814346 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B7070885 : Blo 814346 7070885 := bstep (se 4 (by rfl) ⟨662895, by rfl⟩ : syracuseStep 7070885 = 1325791) B1325791
theorem B4646281 : Blo 814346 4646281 := bstep (se 2 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 4646281 = 3484711) B3484711
theorem B1959535 : Blo 814346 1959535 := bstep (se 1 (by rfl) ⟨1469651, by rfl⟩ : syracuseStep 1959535 = 2939303) B2939303
theorem B1468297 : Blo 814346 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B1468729 : Blo 814346 1468729 := bstep (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) B1101547
theorem B4123385 : Blo 814346 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B4418297 : Blo 814346 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B2321455 : Blo 814346 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B10448189 : Blo 814346 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B814567 : Blo 814346 814567 := bstep (se 1 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 814567 = 1221851) B1221851
theorem B1437257 : Blo 814346 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B814683 : Blo 814346 814683 := bstep (se 1 (by rfl) ⟨611012, by rfl⟩ : syracuseStep 814683 = 1222025) B1222025
theorem B814919 : Blo 814346 814919 := bstep (se 1 (by rfl) ⟨611189, by rfl⟩ : syracuseStep 814919 = 1222379) B1222379
theorem B2486159 : Blo 814346 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B815071 : Blo 814346 815071 := bstep (se 1 (by rfl) ⟨611303, by rfl⟩ : syracuseStep 815071 = 1222607) B1222607
theorem B2748545 : Blo 814346 2748545 := bstep (se 2 (by rfl) ⟨1030704, by rfl⟩ : syracuseStep 2748545 = 2061409) B2061409
theorem B2486459 : Blo 814346 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B815335 : Blo 814346 815335 := bstep (se 1 (by rfl) ⟨611501, by rfl⟩ : syracuseStep 815335 = 1223003) B1223003
theorem B2322685 : Blo 814346 2322685 := bstep (se 3 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 2322685 = 871007) B871007
theorem B815487 : Blo 814346 815487 := bstep (se 1 (by rfl) ⟨611615, by rfl⟩ : syracuseStep 815487 = 1223231) B1223231
theorem B815567 : Blo 814346 815567 := bstep (se 1 (by rfl) ⟨611675, by rfl⟩ : syracuseStep 815567 = 1223351) B1223351
theorem B2978387 : Blo 814346 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B2323039 : Blo 814346 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B2749031 : Blo 814346 2749031 := bstep (se 1 (by rfl) ⟨2061773, by rfl⟩ : syracuseStep 2749031 = 4123547) B4123547
theorem B815719 : Blo 814346 815719 := bstep (se 1 (by rfl) ⟨611789, by rfl⟩ : syracuseStep 815719 = 1223579) B1223579
theorem B2618173 : Blo 814346 2618173 := bstep (se 3 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 2618173 = 981815) B981815
theorem B815983 : Blo 814346 815983 := bstep (se 1 (by rfl) ⟨611987, by rfl⟩ : syracuseStep 815983 = 1223975) B1223975
theorem B979879 : Blo 814346 979879 := bstep (se 1 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 979879 = 1469819) B1469819
theorem B816039 : Blo 814346 816039 := bstep (se 1 (by rfl) ⟨612029, by rfl⟩ : syracuseStep 816039 = 1224059) B1224059
theorem B2749355 : Blo 814346 2749355 := bstep (se 1 (by rfl) ⟨2062016, by rfl⟩ : syracuseStep 2749355 = 4124033) B4124033
theorem B816123 : Blo 814346 816123 := bstep (se 1 (by rfl) ⟨612092, by rfl⟩ : syracuseStep 816123 = 1224185) B1224185
theorem B816191 : Blo 814346 816191 := bstep (se 1 (by rfl) ⟨612143, by rfl⟩ : syracuseStep 816191 = 1224287) B1224287
theorem B2323529 : Blo 814346 2323529 := bstep (se 2 (by rfl) ⟨871323, by rfl⟩ : syracuseStep 2323529 = 1742647) B1742647
theorem B2618507 : Blo 814346 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B2946223 : Blo 814346 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B816335 : Blo 814346 816335 := bstep (se 1 (by rfl) ⟨612251, by rfl⟩ : syracuseStep 816335 = 1224503) B1224503
theorem B1242319 : Blo 814346 1242319 := bstep (se 1 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 1242319 = 1863479) B1863479
theorem B2749787 : Blo 814346 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B816539 : Blo 814346 816539 := bstep (se 1 (by rfl) ⟨612404, by rfl⟩ : syracuseStep 816539 = 1224809) B1224809
theorem B2749895 : Blo 814346 2749895 := bstep (se 1 (by rfl) ⟨2062421, by rfl⟩ : syracuseStep 2749895 = 4124843) B4124843
theorem B1832417 : Blo 814346 1832417 := bstep (se 2 (by rfl) ⟨687156, by rfl⟩ : syracuseStep 1832417 = 1374313) B1374313
theorem B2061895 : Blo 814346 2061895 := bstep (se 1 (by rfl) ⟨1546421, by rfl⟩ : syracuseStep 2061895 = 3092843) B3092843
theorem B816751 : Blo 814346 816751 := bstep (se 1 (by rfl) ⟨612563, by rfl⟩ : syracuseStep 816751 = 1225127) B1225127
theorem B816807 : Blo 814346 816807 := bstep (se 1 (by rfl) ⟨612605, by rfl⟩ : syracuseStep 816807 = 1225211) B1225211
theorem B2062007 : Blo 814346 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B5043923 : Blo 814346 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B816891 : Blo 814346 816891 := bstep (se 1 (by rfl) ⟨612668, by rfl⟩ : syracuseStep 816891 = 1225337) B1225337
theorem B2750219 : Blo 814346 2750219 := bstep (se 1 (by rfl) ⟨2062664, by rfl⟩ : syracuseStep 2750219 = 4125329) B4125329
theorem B980767 : Blo 814346 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B816927 : Blo 814346 816927 := bstep (se 1 (by rfl) ⟨612695, by rfl⟩ : syracuseStep 816927 = 1225391) B1225391
theorem B816959 : Blo 814346 816959 := bstep (se 1 (by rfl) ⟨612719, by rfl⟩ : syracuseStep 816959 = 1225439) B1225439
theorem B817135 : Blo 814346 817135 := bstep (se 1 (by rfl) ⟨612851, by rfl⟩ : syracuseStep 817135 = 1225703) B1225703
theorem B2750489 : Blo 814346 2750489 := bstep (se 2 (by rfl) ⟨1031433, by rfl⟩ : syracuseStep 2750489 = 2062867) B2062867
theorem B3307625 : Blo 814346 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B817307 : Blo 814346 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B1046719 : Blo 814346 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B817343 : Blo 814346 817343 := bstep (se 1 (by rfl) ⟨613007, by rfl⟩ : syracuseStep 817343 = 1226015) B1226015
theorem B2324713 : Blo 814346 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B817455 : Blo 814346 817455 := bstep (se 1 (by rfl) ⟨613091, by rfl⟩ : syracuseStep 817455 = 1226183) B1226183
theorem B12712301 : Blo 814346 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B33552749 : Blo 814346 33552749 := bstep (se 3 (by rfl) ⟨6291140, by rfl⟩ : syracuseStep 33552749 = 12582281) B12582281
theorem B817691 : Blo 814346 817691 := bstep (se 1 (by rfl) ⟨613268, by rfl⟩ : syracuseStep 817691 = 1226537) B1226537
theorem B817695 : Blo 814346 817695 := bstep (se 1 (by rfl) ⟨613271, by rfl⟩ : syracuseStep 817695 = 1226543) B1226543
theorem B28670537 : Blo 814346 28670537 := bstep (se 2 (by rfl) ⟨10751451, by rfl⟩ : syracuseStep 28670537 = 21502903) B21502903
theorem B1374907 : Blo 814346 1374907 := bstep (se 1 (by rfl) ⟨1031180, by rfl⟩ : syracuseStep 1374907 = 2062361) B2062361
theorem B818011 : Blo 814346 818011 := bstep (se 1 (by rfl) ⟨613508, by rfl⟩ : syracuseStep 818011 = 1227017) B1227017
theorem B818079 : Blo 814346 818079 := bstep (se 1 (by rfl) ⟨613559, by rfl⟩ : syracuseStep 818079 = 1227119) B1227119
theorem B1375211 : Blo 814346 1375211 := bstep (se 1 (by rfl) ⟨1031408, by rfl⟩ : syracuseStep 1375211 = 2062817) B2062817
theorem B9436175 : Blo 814346 9436175 := bstep (se 1 (by rfl) ⟨7077131, by rfl⟩ : syracuseStep 9436175 = 14154263) B14154263
theorem B818223 : Blo 814346 818223 := bstep (se 1 (by rfl) ⟨613667, by rfl⟩ : syracuseStep 818223 = 1227335) B1227335
theorem B1834055 : Blo 814346 1834055 := bstep (se 1 (by rfl) ⟨1375541, by rfl⟩ : syracuseStep 1834055 = 2751083) B2751083
theorem B5372999 : Blo 814346 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B818247 : Blo 814346 818247 := bstep (se 1 (by rfl) ⟨613685, by rfl⟩ : syracuseStep 818247 = 1227371) B1227371
theorem B4652113 : Blo 814346 4652113 := bstep (se 2 (by rfl) ⟨1744542, by rfl⟩ : syracuseStep 4652113 = 3489085) B3489085
theorem B1309817 : Blo 814346 1309817 := bstep (se 2 (by rfl) ⟨491181, by rfl⟩ : syracuseStep 1309817 = 982363) B982363
theorem B2751839 : Blo 814346 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B1834451 : Blo 814346 1834451 := bstep (se 1 (by rfl) ⟨1375838, by rfl⟩ : syracuseStep 1834451 = 2751677) B2751677
theorem B2063951 : Blo 814346 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B1834721 : Blo 814346 1834721 := bstep (se 2 (by rfl) ⟨688020, by rfl⟩ : syracuseStep 1834721 = 1376041) B1376041
theorem B1474375 : Blo 814346 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B2752379 : Blo 814346 2752379 := bstep (se 1 (by rfl) ⟨2064284, by rfl⟩ : syracuseStep 2752379 = 4128569) B4128569
theorem B1965995 : Blo 814346 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B1835243 : Blo 814346 1835243 := bstep (se 1 (by rfl) ⟨1376432, by rfl⟩ : syracuseStep 1835243 = 2752865) B2752865
theorem B4129055 : Blo 814346 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B2064811 : Blo 814346 2064811 := bstep (se 1 (by rfl) ⟨1548608, by rfl⟩ : syracuseStep 2064811 = 3097217) B3097217
theorem B2753135 : Blo 814346 2753135 := bstep (se 1 (by rfl) ⟨2064851, by rfl⟩ : syracuseStep 2753135 = 4129703) B4129703
theorem B31752881 : Blo 814346 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B22348817 : Blo 814346 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B1836143 : Blo 814346 1836143 := bstep (se 1 (by rfl) ⟨1377107, by rfl⟩ : syracuseStep 1836143 = 2754215) B2754215
theorem B1377391 : Blo 814346 1377391 := bstep (se 1 (by rfl) ⟨1033043, by rfl⟩ : syracuseStep 1377391 = 2066087) B2066087
theorem B918751 : Blo 814346 918751 := bstep (se 1 (by rfl) ⟨689063, by rfl⟩ : syracuseStep 918751 = 1378127) B1378127
theorem B100730213 : Blo 814346 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B1836539 : Blo 814346 1836539 := bstep (se 1 (by rfl) ⟨1377404, by rfl⟩ : syracuseStep 1836539 = 2754809) B2754809
theorem B1836575 : Blo 814346 1836575 := bstep (se 1 (by rfl) ⟨1377431, by rfl⟩ : syracuseStep 1836575 = 2754863) B2754863
theorem B1377823 : Blo 814346 1377823 := bstep (se 1 (by rfl) ⟨1033367, by rfl⟩ : syracuseStep 1377823 = 2066735) B2066735
theorem B1836719 : Blo 814346 1836719 := bstep (se 1 (by rfl) ⟨1377539, by rfl⟩ : syracuseStep 1836719 = 2755079) B2755079
theorem B6195041 : Blo 814346 6195041 := bstep (se 2 (by rfl) ⟨2323140, by rfl⟩ : syracuseStep 6195041 = 4646281) B4646281
theorem B919579 : Blo 814346 919579 := bstep (se 1 (by rfl) ⟨689684, by rfl⟩ : syracuseStep 919579 = 1379369) B1379369
theorem B1837151 : Blo 814346 1837151 := bstep (se 1 (by rfl) ⟨1377863, by rfl⟩ : syracuseStep 1837151 = 2755727) B2755727
theorem B2066593 : Blo 814346 2066593 := bstep (se 2 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 2066593 = 1549945) B1549945
theorem B14125423 : Blo 814346 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B1837439 : Blo 814346 1837439 := bstep (se 1 (by rfl) ⟨1378079, by rfl⟩ : syracuseStep 1837439 = 2756159) B2756159
theorem B1378687 : Blo 814346 1378687 := bstep (se 1 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 1378687 = 2068031) B2068031
theorem B13961807 : Blo 814346 13961807 := bstep (se 1 (by rfl) ⟨10471355, by rfl⟩ : syracuseStep 13961807 = 20942711) B20942711
theorem B1837907 : Blo 814346 1837907 := bstep (se 1 (by rfl) ⟨1378430, by rfl⟩ : syracuseStep 1837907 = 2756861) B2756861
theorem B1838267 : Blo 814346 1838267 := bstep (se 1 (by rfl) ⟨1378700, by rfl⟩ : syracuseStep 1838267 = 2757401) B2757401
theorem B1838447 : Blo 814346 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B2067839 : Blo 814346 2067839 := bstep (se 1 (by rfl) ⟨1550879, by rfl⟩ : syracuseStep 2067839 = 3101759) B3101759
theorem B23859089 : Blo 814346 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B2756591 : Blo 814346 2756591 := bstep (se 1 (by rfl) ⟨2067443, by rfl⟩ : syracuseStep 2756591 = 4134887) B4134887
theorem B1839167 : Blo 814346 1839167 := bstep (se 1 (by rfl) ⟨1379375, by rfl⟩ : syracuseStep 1839167 = 2758751) B2758751
theorem B1380415 : Blo 814346 1380415 := bstep (se 1 (by rfl) ⟨1035311, by rfl⟩ : syracuseStep 1380415 = 2070623) B2070623
theorem B1740955 : Blo 814346 1740955 := bstep (se 1 (by rfl) ⟨1305716, by rfl⟩ : syracuseStep 1740955 = 2611433) B2611433
theorem B6295805 : Blo 814346 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B1839401 : Blo 814346 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B1839671 : Blo 814346 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B3183371 : Blo 814346 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B1839977 : Blo 814346 1839977 := bstep (se 2 (by rfl) ⟨689991, by rfl⟩ : syracuseStep 1839977 = 1379983) B1379983
theorem B1840031 : Blo 814346 1840031 := bstep (se 1 (by rfl) ⟨1380023, by rfl⟩ : syracuseStep 1840031 = 2760047) B2760047
theorem B1840283 : Blo 814346 1840283 := bstep (se 1 (by rfl) ⟨1380212, by rfl⟩ : syracuseStep 1840283 = 2760425) B2760425
theorem B4134077 : Blo 814346 4134077 := bstep (se 3 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 4134077 = 1550279) B1550279
theorem B1840859 : Blo 814346 1840859 := bstep (se 1 (by rfl) ⟨1380644, by rfl⟩ : syracuseStep 1840859 = 2761289) B2761289
theorem B1840967 : Blo 814346 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B2070431 : Blo 814346 2070431 := bstep (se 1 (by rfl) ⟨1552823, by rfl⟩ : syracuseStep 2070431 = 3105647) B3105647
theorem B4135049 : Blo 814346 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B76454765 : Blo 814346 76454765 := bstep (se 3 (by rfl) ⟨14335268, by rfl⟩ : syracuseStep 76454765 = 28670537) B28670537
theorem B1547849 : Blo 814346 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B958171 : Blo 814346 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B2760695 : Blo 814346 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B4136993 : Blo 814346 4136993 := bstep (se 2 (by rfl) ⟨1551372, by rfl⟩ : syracuseStep 4136993 = 3102745) B3102745
theorem B2760911 : Blo 814346 2760911 := bstep (se 1 (by rfl) ⟨2070683, by rfl⟩ : syracuseStep 2760911 = 4141367) B4141367
theorem B1549019 : Blo 814346 1549019 := bstep (se 1 (by rfl) ⟨1161764, by rfl⟩ : syracuseStep 1549019 = 2323529) B2323529
theorem B1745671 : Blo 814346 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B31335335 : Blo 814346 31335335 := bstep (se 1 (by rfl) ⟨23501501, by rfl⟩ : syracuseStep 31335335 = 47003003) B47003003
theorem B1221611 : Blo 814346 1221611 := bstep (se 1 (by rfl) ⟨916208, by rfl⟩ : syracuseStep 1221611 = 1832417) B1832417
theorem B2761775 : Blo 814346 2761775 := bstep (se 1 (by rfl) ⟨2071331, by rfl⟩ : syracuseStep 2761775 = 4142663) B4142663
theorem B2205083 : Blo 814346 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B6202817 : Blo 814346 6202817 := bstep (se 2 (by rfl) ⟨2326056, by rfl⟩ : syracuseStep 6202817 = 4652113) B4652113
theorem B1222703 : Blo 814346 1222703 := bstep (se 1 (by rfl) ⟨917027, by rfl⟩ : syracuseStep 1222703 = 1834055) B1834055
theorem B3581999 : Blo 814346 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B5875901 : Blo 814346 5875901 := bstep (se 3 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 5875901 = 2203463) B2203463
theorem B1222967 : Blo 814346 1222967 := bstep (se 1 (by rfl) ⟨917225, by rfl⟩ : syracuseStep 1222967 = 1834451) B1834451
theorem B1223147 : Blo 814346 1223147 := bstep (se 1 (by rfl) ⟨917360, by rfl⟩ : syracuseStep 1223147 = 1834721) B1834721
theorem B6630557 : Blo 814346 6630557 := bstep (se 3 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 6630557 = 2486459) B2486459
theorem B1223849 : Blo 814346 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B1224263 : Blo 814346 1224263 := bstep (se 1 (by rfl) ⟨918197, by rfl⟩ : syracuseStep 1224263 = 1836395) B1836395
theorem B1224443 : Blo 814346 1224443 := bstep (se 1 (by rfl) ⟨918332, by rfl⟩ : syracuseStep 1224443 = 1836665) B1836665
theorem B995431 : Blo 814346 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B6205733 : Blo 814346 6205733 := bstep (se 4 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 6205733 = 1163575) B1163575
theorem B1225115 : Blo 814346 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B11907749 : Blo 814346 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B1225535 : Blo 814346 1225535 := bstep (se 1 (by rfl) ⟨919151, by rfl⟩ : syracuseStep 1225535 = 1838303) B1838303
theorem B1225679 : Blo 814346 1225679 := bstep (se 1 (by rfl) ⟨919259, by rfl⟩ : syracuseStep 1225679 = 1838519) B1838519
theorem B1225721 : Blo 814346 1225721 := bstep (se 2 (by rfl) ⟨459645, by rfl⟩ : syracuseStep 1225721 = 919291) B919291
theorem B1225769 : Blo 814346 1225769 := bstep (se 2 (by rfl) ⟨459663, by rfl⟩ : syracuseStep 1225769 = 919327) B919327
theorem B1225799 : Blo 814346 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B1160443 : Blo 814346 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B1225979 : Blo 814346 1225979 := bstep (se 1 (by rfl) ⟨919484, by rfl⟩ : syracuseStep 1225979 = 1838969) B1838969
theorem B5879735 : Blo 814346 5879735 := bstep (se 1 (by rfl) ⟨4409801, by rfl⟩ : syracuseStep 5879735 = 8819603) B8819603
theorem B1227215 : Blo 814346 1227215 := bstep (se 1 (by rfl) ⟨920411, by rfl⟩ : syracuseStep 1227215 = 1840823) B1840823
theorem B1227305 : Blo 814346 1227305 := bstep (se 2 (by rfl) ⟨460239, by rfl⟩ : syracuseStep 1227305 = 920479) B920479
theorem B6208163 : Blo 814346 6208163 := bstep (se 1 (by rfl) ⟨4656122, by rfl⟩ : syracuseStep 6208163 = 9312245) B9312245
theorem B3488471 : Blo 814346 3488471 := bstep (se 1 (by rfl) ⟨2616353, by rfl⟩ : syracuseStep 3488471 = 5232707) B5232707
theorem B3095273 : Blo 814346 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B1227497 : Blo 814346 1227497 := bstep (se 2 (by rfl) ⟨460311, by rfl⟩ : syracuseStep 1227497 = 920623) B920623
theorem B1162345 : Blo 814346 1162345 := bstep (se 2 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 1162345 = 871759) B871759
theorem B19872989 : Blo 814346 19872989 := bstep (se 3 (by rfl) ⟨3726185, by rfl⟩ : syracuseStep 19872989 = 7452371) B7452371
theorem B3096913 : Blo 814346 3096913 := bstep (se 2 (by rfl) ⟨1161342, by rfl⟩ : syracuseStep 3096913 = 2322685) B2322685
theorem B3359335 : Blo 814346 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B3097385 : Blo 814346 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B5227375 : Blo 814346 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B89473997 : Blo 814346 89473997 := bstep (se 3 (by rfl) ⟨16776374, by rfl⟩ : syracuseStep 89473997 = 33552749) B33552749
theorem B6210593 : Blo 814346 6210593 := bstep (se 2 (by rfl) ⟨2328972, by rfl⟩ : syracuseStep 6210593 = 4657945) B4657945
theorem B3490897 : Blo 814346 3490897 := bstep (se 2 (by rfl) ⟨1309086, by rfl⟩ : syracuseStep 3490897 = 2618173) B2618173
theorem B1033327 : Blo 814346 1033327 := bstep (se 1 (by rfl) ⟨774995, by rfl⟩ : syracuseStep 1033327 = 1549991) B1549991
theorem B1164623 : Blo 814346 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B4638059 : Blo 814346 4638059 := bstep (se 1 (by rfl) ⟨3478544, by rfl⟩ : syracuseStep 4638059 = 6957089) B6957089
theorem B1656425 : Blo 814346 1656425 := bstep (se 2 (by rfl) ⟨621159, by rfl⟩ : syracuseStep 1656425 = 1242319) B1242319
theorem B38127395 : Blo 814346 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B6965459 : Blo 814346 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B1034623 : Blo 814346 1034623 := bstep (se 1 (by rfl) ⟨775967, by rfl⟩ : syracuseStep 1034623 = 1551935) B1551935
theorem B1657439 : Blo 814346 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B2935673 : Blo 814346 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B1395625 : Blo 814346 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B6212537 : Blo 814346 6212537 := bstep (se 2 (by rfl) ⟨2329701, by rfl⟩ : syracuseStep 6212537 = 4659403) B4659403
theorem B3099617 : Blo 814346 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B3492845 : Blo 814346 3492845 := bstep (se 3 (by rfl) ⟨654908, by rfl⟩ : syracuseStep 3492845 = 1309817) B1309817
theorem B1985591 : Blo 814346 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B3919265 : Blo 814346 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B10735415 : Blo 814346 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B3362615 : Blo 814346 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B67129145 : Blo 814346 67129145 := bstep (se 2 (by rfl) ⟨25173429, by rfl⟩ : syracuseStep 67129145 = 50346859) B50346859
theorem B2609023 : Blo 814346 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B5230757 : Blo 814346 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B8474867 : Blo 814346 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B5230939 : Blo 814346 5230939 := bstep (se 1 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 5230939 = 7846409) B7846409
theorem B7065967 : Blo 814346 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B7459235 : Blo 814346 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B21484361 : Blo 814346 21484361 := bstep (se 2 (by rfl) ⟨8056635, by rfl⟩ : syracuseStep 21484361 = 16113271) B16113271
theorem B28234649 : Blo 814346 28234649 := bstep (se 2 (by rfl) ⟨10587993, by rfl⟩ : syracuseStep 28234649 = 21175987) B21175987
theorem B3495305 : Blo 814346 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B3495545 : Blo 814346 3495545 := bstep (se 2 (by rfl) ⟨1310829, by rfl⟩ : syracuseStep 3495545 = 2621659) B2621659
theorem B4643183 : Blo 814346 4643183 := bstep (se 1 (by rfl) ⟨3482387, by rfl⟩ : syracuseStep 4643183 = 6964775) B6964775
theorem B10443167 : Blo 814346 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B2939419 : Blo 814346 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B2513479 : Blo 814346 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B6381359 : Blo 814346 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B1957787 : Blo 814346 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B3105161 : Blo 814346 3105161 := bstep (se 2 (by rfl) ⟨1164435, by rfl⟩ : syracuseStep 3105161 = 2328871) B2328871
theorem B1958305 : Blo 814346 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B2614855 : Blo 814346 2614855 := bstep (se 1 (by rfl) ⟨1961141, by rfl⟩ : syracuseStep 2614855 = 3922283) B3922283
theorem B2319997 : Blo 814346 2319997 := bstep (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) B869999
theorem B2320123 : Blo 814346 2320123 := bstep (se 1 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 2320123 = 3480185) B3480185
theorem B5891869 : Blo 814346 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B14870303 : Blo 814346 14870303 := bstep (se 1 (by rfl) ⟨11152727, by rfl⟩ : syracuseStep 14870303 = 22305455) B22305455
theorem B6973523 : Blo 814346 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B12544109 : Blo 814346 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B7563527 : Blo 814346 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B11168047 : Blo 814346 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B3107119 : Blo 814346 3107119 := bstep (se 1 (by rfl) ⟨2330339, by rfl⟩ : syracuseStep 3107119 = 4660679) B4660679
theorem B1960247 : Blo 814346 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B2943341 : Blo 814346 2943341 := bstep (se 3 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 2943341 = 1103753) B1103753
theorem B1469011 : Blo 814346 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B9431639 : Blo 814346 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B1469191 : Blo 814346 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B1960843 : Blo 814346 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B15133697 : Blo 814346 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B4123871 : Blo 814346 4123871 := bstep (se 1 (by rfl) ⟨3092903, by rfl⟩ : syracuseStep 4123871 = 6185807) B6185807
theorem B814463 : Blo 814346 814463 := bstep (se 1 (by rfl) ⟨610847, by rfl⟩ : syracuseStep 814463 = 1221695) B1221695
theorem B814491 : Blo 814346 814491 := bstep (se 1 (by rfl) ⟨610868, by rfl⟩ : syracuseStep 814491 = 1221737) B1221737
theorem B4713923 : Blo 814346 4713923 := bstep (se 1 (by rfl) ⟨3535442, by rfl⟩ : syracuseStep 4713923 = 7070885) B7070885
theorem B814559 : Blo 814346 814559 := bstep (se 1 (by rfl) ⟨610919, by rfl⟩ : syracuseStep 814559 = 1221839) B1221839
theorem B2911835 : Blo 814346 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B814695 : Blo 814346 814695 := bstep (se 1 (by rfl) ⟨611021, by rfl⟩ : syracuseStep 814695 = 1222043) B1222043
theorem B814843 : Blo 814346 814843 := bstep (se 1 (by rfl) ⟨611132, by rfl⟩ : syracuseStep 814843 = 1222265) B1222265
theorem B814911 : Blo 814346 814911 := bstep (se 1 (by rfl) ⟨611183, by rfl⟩ : syracuseStep 814911 = 1222367) B1222367
theorem B814975 : Blo 814346 814975 := bstep (se 1 (by rfl) ⟨611231, by rfl⟩ : syracuseStep 814975 = 1222463) B1222463
theorem B1306505 : Blo 814346 1306505 := bstep (se 2 (by rfl) ⟨489939, by rfl⟩ : syracuseStep 1306505 = 979879) B979879
theorem B815087 : Blo 814346 815087 := bstep (se 1 (by rfl) ⟨611315, by rfl⟩ : syracuseStep 815087 = 1222631) B1222631
theorem B815099 : Blo 814346 815099 := bstep (se 1 (by rfl) ⟨611324, by rfl⟩ : syracuseStep 815099 = 1222649) B1222649
theorem B815167 : Blo 814346 815167 := bstep (se 1 (by rfl) ⟨611375, by rfl⟩ : syracuseStep 815167 = 1222751) B1222751
theorem B815207 : Blo 814346 815207 := bstep (se 1 (by rfl) ⟨611405, by rfl⟩ : syracuseStep 815207 = 1222811) B1222811
theorem B815231 : Blo 814346 815231 := bstep (se 1 (by rfl) ⟨611423, by rfl⟩ : syracuseStep 815231 = 1222847) B1222847
theorem B815259 : Blo 814346 815259 := bstep (se 1 (by rfl) ⟨611444, by rfl⟩ : syracuseStep 815259 = 1222889) B1222889
theorem B3928297 : Blo 814346 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B815463 : Blo 814346 815463 := bstep (se 1 (by rfl) ⟨611597, by rfl⟩ : syracuseStep 815463 = 1223195) B1223195
theorem B815515 : Blo 814346 815515 := bstep (se 1 (by rfl) ⟨611636, by rfl⟩ : syracuseStep 815515 = 1223273) B1223273
theorem B2748923 : Blo 814346 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B2945531 : Blo 814346 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B2323073 : Blo 814346 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B815867 : Blo 814346 815867 := bstep (se 1 (by rfl) ⟨611900, by rfl⟩ : syracuseStep 815867 = 1223801) B1223801
theorem B2749193 : Blo 814346 2749193 := bstep (se 2 (by rfl) ⟨1030947, by rfl⟩ : syracuseStep 2749193 = 2061895) B2061895
theorem B815935 : Blo 814346 815935 := bstep (se 1 (by rfl) ⟨611951, by rfl⟩ : syracuseStep 815935 = 1223903) B1223903
theorem B815963 : Blo 814346 815963 := bstep (se 1 (by rfl) ⟨611972, by rfl⟩ : syracuseStep 815963 = 1223945) B1223945
theorem B816031 : Blo 814346 816031 := bstep (se 1 (by rfl) ⟨612023, by rfl⟩ : syracuseStep 816031 = 1224047) B1224047
theorem B816111 : Blo 814346 816111 := bstep (se 1 (by rfl) ⟨612083, by rfl⟩ : syracuseStep 816111 = 1224167) B1224167
theorem B816199 : Blo 814346 816199 := bstep (se 1 (by rfl) ⟨612149, by rfl⟩ : syracuseStep 816199 = 1224299) B1224299
theorem B816283 : Blo 814346 816283 := bstep (se 1 (by rfl) ⟨612212, by rfl⟩ : syracuseStep 816283 = 1224425) B1224425
theorem B816379 : Blo 814346 816379 := bstep (se 1 (by rfl) ⟨612284, by rfl⟩ : syracuseStep 816379 = 1224569) B1224569
theorem B816447 : Blo 814346 816447 := bstep (se 1 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 816447 = 1224671) B1224671
theorem B1832363 : Blo 814346 1832363 := bstep (se 1 (by rfl) ⟨1374272, by rfl⟩ : syracuseStep 1832363 = 2748545) B2748545
theorem B816615 : Blo 814346 816615 := bstep (se 1 (by rfl) ⟨612461, by rfl⟩ : syracuseStep 816615 = 1224923) B1224923
theorem B816623 : Blo 814346 816623 := bstep (se 1 (by rfl) ⟨612467, by rfl⟩ : syracuseStep 816623 = 1224935) B1224935
theorem B816731 : Blo 814346 816731 := bstep (se 1 (by rfl) ⟨612548, by rfl⟩ : syracuseStep 816731 = 1225097) B1225097
theorem B816795 : Blo 814346 816795 := bstep (se 1 (by rfl) ⟨612596, by rfl⟩ : syracuseStep 816795 = 1225193) B1225193
theorem B1832687 : Blo 814346 1832687 := bstep (se 1 (by rfl) ⟨1374515, by rfl⟩ : syracuseStep 1832687 = 2749031) B2749031
theorem B816879 : Blo 814346 816879 := bstep (se 1 (by rfl) ⟨612659, by rfl⟩ : syracuseStep 816879 = 1225319) B1225319
theorem B816967 : Blo 814346 816967 := bstep (se 1 (by rfl) ⟨612725, by rfl⟩ : syracuseStep 816967 = 1225451) B1225451
theorem B816987 : Blo 814346 816987 := bstep (se 1 (by rfl) ⟨612740, by rfl⟩ : syracuseStep 816987 = 1225481) B1225481
theorem B817055 : Blo 814346 817055 := bstep (se 1 (by rfl) ⟨612791, by rfl⟩ : syracuseStep 817055 = 1225583) B1225583
theorem B10450853 : Blo 814346 10450853 := bstep (se 4 (by rfl) ⟨979767, by rfl⟩ : syracuseStep 10450853 = 1959535) B1959535
theorem B1832903 : Blo 814346 1832903 := bstep (se 1 (by rfl) ⟨1374677, by rfl⟩ : syracuseStep 1832903 = 2749355) B2749355
theorem B817223 : Blo 814346 817223 := bstep (se 1 (by rfl) ⟨612917, by rfl⟩ : syracuseStep 817223 = 1225835) B1225835
theorem B1833191 : Blo 814346 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B817383 : Blo 814346 817383 := bstep (se 1 (by rfl) ⟨613037, by rfl⟩ : syracuseStep 817383 = 1226075) B1226075
theorem B1833209 : Blo 814346 1833209 := bstep (se 2 (by rfl) ⟨687453, by rfl⟩ : syracuseStep 1833209 = 1374907) B1374907
theorem B1833263 : Blo 814346 1833263 := bstep (se 1 (by rfl) ⟨1374947, by rfl⟩ : syracuseStep 1833263 = 2749895) B2749895
theorem B3307823 : Blo 814346 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B817567 : Blo 814346 817567 := bstep (se 1 (by rfl) ⟨613175, by rfl⟩ : syracuseStep 817567 = 1226351) B1226351
theorem B1374671 : Blo 814346 1374671 := bstep (se 1 (by rfl) ⟨1031003, by rfl⟩ : syracuseStep 1374671 = 2062007) B2062007
theorem B817615 : Blo 814346 817615 := bstep (se 1 (by rfl) ⟨613211, by rfl⟩ : syracuseStep 817615 = 1226423) B1226423
theorem B817639 : Blo 814346 817639 := bstep (se 1 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 817639 = 1226459) B1226459
theorem B1833479 : Blo 814346 1833479 := bstep (se 1 (by rfl) ⟨1375109, by rfl⟩ : syracuseStep 1833479 = 2750219) B2750219
theorem B817755 : Blo 814346 817755 := bstep (se 1 (by rfl) ⟨613316, by rfl⟩ : syracuseStep 817755 = 1226633) B1226633
theorem B817823 : Blo 814346 817823 := bstep (se 1 (by rfl) ⟨613367, by rfl⟩ : syracuseStep 817823 = 1226735) B1226735
theorem B1833659 : Blo 814346 1833659 := bstep (se 1 (by rfl) ⟨1375244, by rfl⟩ : syracuseStep 1833659 = 2750489) B2750489
theorem B817991 : Blo 814346 817991 := bstep (se 1 (by rfl) ⟨613493, by rfl⟩ : syracuseStep 817991 = 1226987) B1226987
theorem B818031 : Blo 814346 818031 := bstep (se 1 (by rfl) ⟨613523, by rfl⟩ : syracuseStep 818031 = 1227047) B1227047
theorem B818087 : Blo 814346 818087 := bstep (se 1 (by rfl) ⟨613565, by rfl⟩ : syracuseStep 818087 = 1227131) B1227131
theorem B818267 : Blo 814346 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B1473761 : Blo 814346 1473761 := bstep (se 2 (by rfl) ⟨552660, by rfl⟩ : syracuseStep 1473761 = 1105321) B1105321
theorem B916807 : Blo 814346 916807 := bstep (se 1 (by rfl) ⟨687605, by rfl⟩ : syracuseStep 916807 = 1375211) B1375211
theorem B6290783 : Blo 814346 6290783 := bstep (se 1 (by rfl) ⟨4718087, by rfl⟩ : syracuseStep 6290783 = 9436175) B9436175
theorem B7830917 : Blo 814346 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B1834559 : Blo 814346 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B3309167 : Blo 814346 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B2064001 : Blo 814346 2064001 := bstep (se 2 (by rfl) ⟨774000, by rfl⟩ : syracuseStep 2064001 = 1548001) B1548001
theorem B17858191 : Blo 814346 17858191 := bstep (se 1 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 17858191 = 26787287) B26787287
theorem B1375967 : Blo 814346 1375967 := bstep (se 1 (by rfl) ⟨1031975, by rfl⟩ : syracuseStep 1375967 = 2063951) B2063951
theorem B1965833 : Blo 814346 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B1834919 : Blo 814346 1834919 := bstep (se 1 (by rfl) ⟨1376189, by rfl⟩ : syracuseStep 1834919 = 2752379) B2752379
theorem B1310663 : Blo 814346 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B2752703 : Blo 814346 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B1835423 : Blo 814346 1835423 := bstep (se 1 (by rfl) ⟨1376567, by rfl⟩ : syracuseStep 1835423 = 2753135) B2753135
theorem B4129217 : Blo 814346 4129217 := bstep (se 2 (by rfl) ⟨1548456, by rfl⟩ : syracuseStep 4129217 = 3096913) B3096913
theorem B21168587 : Blo 814346 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B2064923 : Blo 814346 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B2753081 : Blo 814346 2753081 := bstep (se 2 (by rfl) ⟨1032405, by rfl⟩ : syracuseStep 2753081 = 2064811) B2064811
theorem B2327561 : Blo 814346 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B4130027 : Blo 814346 4130027 := bstep (se 1 (by rfl) ⟨3097520, by rfl⟩ : syracuseStep 4130027 = 6195041) B6195041
theorem B4654529 : Blo 814346 4654529 := bstep (se 2 (by rfl) ⟨1745448, by rfl⟩ : syracuseStep 4654529 = 3490897) B3490897
theorem B1836521 : Blo 814346 1836521 := bstep (se 2 (by rfl) ⟨688695, by rfl⟩ : syracuseStep 1836521 = 1377391) B1377391
theorem B1377769 : Blo 814346 1377769 := bstep (se 2 (by rfl) ⟨516663, by rfl⟩ : syracuseStep 1377769 = 1033327) B1033327
theorem B9307871 : Blo 814346 9307871 := bstep (se 1 (by rfl) ⟨6980903, by rfl⟩ : syracuseStep 9307871 = 13961807) B13961807
theorem B2066411 : Blo 814346 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B2328563 : Blo 814346 2328563 := bstep (se 1 (by rfl) ⟨1746422, by rfl⟩ : syracuseStep 2328563 = 3492845) B3492845
theorem B1837097 : Blo 814346 1837097 := bstep (se 2 (by rfl) ⟨688911, by rfl⟩ : syracuseStep 1837097 = 1377823) B1377823
theorem B1378559 : Blo 814346 1378559 := bstep (se 1 (by rfl) ⟨1033919, by rfl⟩ : syracuseStep 1378559 = 2067839) B2067839
theorem B1837727 : Blo 814346 1837727 := bstep (se 1 (by rfl) ⟨1378295, by rfl⟩ : syracuseStep 1837727 = 2756591) B2756591
theorem B4197203 : Blo 814346 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B2755457 : Blo 814346 2755457 := bstep (se 2 (by rfl) ⟨1033296, by rfl⟩ : syracuseStep 2755457 = 2066593) B2066593
theorem B1838249 : Blo 814346 1838249 := bstep (se 2 (by rfl) ⟨689343, by rfl⟩ : syracuseStep 1838249 = 1378687) B1378687
theorem B1379497 : Blo 814346 1379497 := bstep (se 2 (by rfl) ⟨517311, by rfl⟩ : syracuseStep 1379497 = 1034623) B1034623
theorem B2756051 : Blo 814346 2756051 := bstep (se 1 (by rfl) ⟨2067038, by rfl⟩ : syracuseStep 2756051 = 4134077) B4134077
theorem B2330203 : Blo 814346 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B2330363 : Blo 814346 2330363 := bstep (se 1 (by rfl) ⟨1747772, by rfl⟩ : syracuseStep 2330363 = 3495545) B3495545
theorem B1380287 : Blo 814346 1380287 := bstep (se 1 (by rfl) ⟨1035215, by rfl⟩ : syracuseStep 1380287 = 2070431) B2070431
theorem B2756699 : Blo 814346 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B3478697 : Blo 814346 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B1840463 : Blo 814346 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B2757995 : Blo 814346 2757995 := bstep (se 1 (by rfl) ⟨2068496, by rfl⟩ : syracuseStep 2757995 = 4136993) B4136993
theorem B1840553 : Blo 814346 1840553 := bstep (se 2 (by rfl) ⟨690207, by rfl⟩ : syracuseStep 1840553 = 1380415) B1380415
theorem B1840607 : Blo 814346 1840607 := bstep (se 1 (by rfl) ⟨1380455, by rfl⟩ : syracuseStep 1840607 = 2760911) B2760911
theorem B2070107 : Blo 814346 2070107 := bstep (se 1 (by rfl) ⟨1552580, by rfl⟩ : syracuseStep 2070107 = 3105161) B3105161
theorem B1841183 : Blo 814346 1841183 := bstep (se 1 (by rfl) ⟨1380887, by rfl⟩ : syracuseStep 1841183 = 2761775) B2761775
theorem B4135211 : Blo 814346 4135211 := bstep (se 1 (by rfl) ⟨3101408, by rfl⟩ : syracuseStep 4135211 = 6202817) B6202817
theorem B8362739 : Blo 814346 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B1547257 : Blo 814346 1547257 := bstep (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) B1160443
theorem B1941223 : Blo 814346 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B4137155 : Blo 814346 4137155 := bstep (se 1 (by rfl) ⟨3102866, by rfl⟩ : syracuseStep 4137155 = 6205733) B6205733
theorem B1548715 : Blo 814346 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B7938499 : Blo 814346 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B3351305 : Blo 814346 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B1221575 : Blo 814346 1221575 := bstep (se 1 (by rfl) ⟨916181, by rfl⟩ : syracuseStep 1221575 = 1832363) B1832363
theorem B1221791 : Blo 814346 1221791 := bstep (se 1 (by rfl) ⟨916343, by rfl⟩ : syracuseStep 1221791 = 1832687) B1832687
theorem B1221935 : Blo 814346 1221935 := bstep (se 1 (by rfl) ⟨916451, by rfl⟩ : syracuseStep 1221935 = 1832903) B1832903
theorem B1549793 : Blo 814346 1549793 := bstep (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) B1162345
theorem B1222127 : Blo 814346 1222127 := bstep (se 1 (by rfl) ⟨916595, by rfl⟩ : syracuseStep 1222127 = 1833191) B1833191
theorem B1222139 : Blo 814346 1222139 := bstep (se 1 (by rfl) ⟨916604, by rfl⟩ : syracuseStep 1222139 = 1833209) B1833209
theorem B1222175 : Blo 814346 1222175 := bstep (se 1 (by rfl) ⟨916631, by rfl⟩ : syracuseStep 1222175 = 1833263) B1833263
theorem B2205215 : Blo 814346 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B1222319 : Blo 814346 1222319 := bstep (se 1 (by rfl) ⟨916739, by rfl⟩ : syracuseStep 1222319 = 1833479) B1833479
theorem B1222409 : Blo 814346 1222409 := bstep (se 2 (by rfl) ⟨458403, by rfl⟩ : syracuseStep 1222409 = 916807) B916807
theorem B4138775 : Blo 814346 4138775 := bstep (se 1 (by rfl) ⟨3104081, by rfl⟩ : syracuseStep 4138775 = 6208163) B6208163
theorem B1222439 : Blo 814346 1222439 := bstep (se 1 (by rfl) ⟨916829, by rfl⟩ : syracuseStep 1222439 = 1833659) B1833659
theorem B13248659 : Blo 814346 13248659 := bstep (se 1 (by rfl) ⟨9936494, by rfl⟩ : syracuseStep 13248659 = 19872989) B19872989
theorem B5220611 : Blo 814346 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B1223039 : Blo 814346 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B2206111 : Blo 814346 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B1223279 : Blo 814346 1223279 := bstep (se 1 (by rfl) ⟨917459, by rfl⟩ : syracuseStep 1223279 = 1834919) B1834919
theorem B1223495 : Blo 814346 1223495 := bstep (se 1 (by rfl) ⟨917621, by rfl⟩ : syracuseStep 1223495 = 1835243) B1835243
theorem B59649331 : Blo 814346 59649331 := bstep (se 1 (by rfl) ⟨44736998, by rfl⟩ : syracuseStep 59649331 = 89473997) B89473997
theorem B4140395 : Blo 814346 4140395 := bstep (se 1 (by rfl) ⟨3105296, by rfl⟩ : syracuseStep 4140395 = 6210593) B6210593
theorem B1224095 : Blo 814346 1224095 := bstep (se 1 (by rfl) ⟨918071, by rfl⟩ : syracuseStep 1224095 = 1836143) B1836143
theorem B67153475 : Blo 814346 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B3092039 : Blo 814346 3092039 := bstep (se 1 (by rfl) ⟨2319029, by rfl⟩ : syracuseStep 3092039 = 4638059) B4638059
theorem B1224359 : Blo 814346 1224359 := bstep (se 1 (by rfl) ⟨918269, by rfl⟩ : syracuseStep 1224359 = 1836539) B1836539
theorem B1224383 : Blo 814346 1224383 := bstep (se 1 (by rfl) ⟨918287, by rfl⟩ : syracuseStep 1224383 = 1836575) B1836575
theorem B1224479 : Blo 814346 1224479 := bstep (se 1 (by rfl) ⟨918359, by rfl⟩ : syracuseStep 1224479 = 1836719) B1836719
theorem B1224767 : Blo 814346 1224767 := bstep (se 1 (by rfl) ⟨918575, by rfl⟩ : syracuseStep 1224767 = 1837151) B1837151
theorem B1224959 : Blo 814346 1224959 := bstep (se 1 (by rfl) ⟨918719, by rfl⟩ : syracuseStep 1224959 = 1837439) B1837439
theorem B1225001 : Blo 814346 1225001 := bstep (se 2 (by rfl) ⟨459375, by rfl⟩ : syracuseStep 1225001 = 918751) B918751
theorem B1225271 : Blo 814346 1225271 := bstep (se 1 (by rfl) ⟨918953, by rfl⟩ : syracuseStep 1225271 = 1837907) B1837907
theorem B4141691 : Blo 814346 4141691 := bstep (se 1 (by rfl) ⟨3106268, by rfl⟩ : syracuseStep 4141691 = 6212537) B6212537
theorem B3486473 : Blo 814346 3486473 := bstep (se 2 (by rfl) ⟨1307427, by rfl⟩ : syracuseStep 3486473 = 2614855) B2614855
theorem B1225511 : Blo 814346 1225511 := bstep (se 1 (by rfl) ⟨919133, by rfl⟩ : syracuseStep 1225511 = 1838267) B1838267
theorem B3093329 : Blo 814346 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B57291629 : Blo 814346 57291629 := bstep (se 3 (by rfl) ⟨10742180, by rfl⟩ : syracuseStep 57291629 = 21484361) B21484361
theorem B1225631 : Blo 814346 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B3093497 : Blo 814346 3093497 := bstep (se 2 (by rfl) ⟨1160061, by rfl⟩ : syracuseStep 3093497 = 2320123) B2320123
theorem B7156943 : Blo 814346 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B2241743 : Blo 814346 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B15906059 : Blo 814346 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B1226105 : Blo 814346 1226105 := bstep (se 2 (by rfl) ⟨459789, by rfl⟩ : syracuseStep 1226105 = 919579) B919579
theorem B1226111 : Blo 814346 1226111 := bstep (se 1 (by rfl) ⟨919583, by rfl⟩ : syracuseStep 1226111 = 1839167) B1839167
theorem B5649911 : Blo 814346 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1226267 : Blo 814346 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B1226447 : Blo 814346 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B14890729 : Blo 814346 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B4142825 : Blo 814346 4142825 := bstep (se 2 (by rfl) ⟨1553559, by rfl⟩ : syracuseStep 4142825 = 3107119) B3107119
theorem B1226651 : Blo 814346 1226651 := bstep (se 1 (by rfl) ⟨919988, by rfl⟩ : syracuseStep 1226651 = 1839977) B1839977
theorem B18823099 : Blo 814346 18823099 := bstep (se 1 (by rfl) ⟨14117324, by rfl⟩ : syracuseStep 18823099 = 28234649) B28234649
theorem B1226687 : Blo 814346 1226687 := bstep (se 1 (by rfl) ⟨920015, by rfl⟩ : syracuseStep 1226687 = 1840031) B1840031
theorem B1226855 : Blo 814346 1226855 := bstep (se 1 (by rfl) ⟨920141, by rfl⟩ : syracuseStep 1226855 = 1840283) B1840283
theorem B5880221 : Blo 814346 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B1227239 : Blo 814346 1227239 := bstep (se 1 (by rfl) ⟨920429, by rfl⟩ : syracuseStep 1227239 = 1840859) B1840859
theorem B1227311 : Blo 814346 1227311 := bstep (se 1 (by rfl) ⟨920483, by rfl⟩ : syracuseStep 1227311 = 1840967) B1840967
theorem B3095455 : Blo 814346 3095455 := bstep (se 1 (by rfl) ⟨2321591, by rfl⟩ : syracuseStep 3095455 = 4643183) B4643183
theorem B6962111 : Blo 814346 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B50969843 : Blo 814346 50969843 := bstep (se 1 (by rfl) ⟨38227382, by rfl⟩ : syracuseStep 50969843 = 76454765) B76454765
theorem B1327241 : Blo 814346 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B1032679 : Blo 814346 1032679 := bstep (se 1 (by rfl) ⟨774509, by rfl⟩ : syracuseStep 1032679 = 1549019) B1549019
theorem B9421289 : Blo 814346 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B20890223 : Blo 814346 20890223 := bstep (se 1 (by rfl) ⟨15667667, by rfl⟩ : syracuseStep 20890223 = 31335335) B31335335
theorem B5227325 : Blo 814346 5227325 := bstep (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) B1960247
theorem B9913535 : Blo 814346 9913535 := bstep (se 1 (by rfl) ⟨7435151, by rfl⟩ : syracuseStep 9913535 = 14870303) B14870303
theorem B3917267 : Blo 814346 3917267 := bstep (se 1 (by rfl) ⟨2937950, by rfl⟩ : syracuseStep 3917267 = 5875901) B5875901
theorem B871003 : Blo 814346 871003 := bstep (se 1 (by rfl) ⟨653252, by rfl⟩ : syracuseStep 871003 = 1306505) B1306505
theorem B5294909 : Blo 814346 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B17681485 : Blo 814346 17681485 := bstep (se 3 (by rfl) ⟨3315278, by rfl⟩ : syracuseStep 17681485 = 6630557) B6630557
theorem B3919225 : Blo 814346 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B12570461 : Blo 814346 12570461 := bstep (se 3 (by rfl) ⟨2356961, by rfl⟩ : syracuseStep 12570461 = 4713923) B4713923
theorem B6967235 : Blo 814346 6967235 := bstep (se 1 (by rfl) ⟨5225426, by rfl⟩ : syracuseStep 6967235 = 10450853) B10450853
theorem B3919823 : Blo 814346 3919823 := bstep (se 1 (by rfl) ⟨2939867, by rfl⟩ : syracuseStep 3919823 = 5879735) B5879735
theorem B23810921 : Blo 814346 23810921 := bstep (se 2 (by rfl) ⟨8929095, by rfl⟩ : syracuseStep 23810921 = 17858191) B17858191
theorem B873775 : Blo 814346 873775 := bstep (se 1 (by rfl) ⟨655331, by rfl⟩ : syracuseStep 873775 = 1310663) B1310663
theorem B13948685 : Blo 814346 13948685 := bstep (se 3 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 13948685 = 5230757) B5230757
theorem B2611073 : Blo 814346 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B14899211 : Blo 814346 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B4479113 : Blo 814346 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B1104283 : Blo 814346 1104283 := bstep (se 1 (by rfl) ⟨828212, by rfl⟩ : syracuseStep 1104283 = 1656425) B1656425
theorem B6969833 : Blo 814346 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B4643639 : Blo 814346 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B1104959 : Blo 814346 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B1957115 : Blo 814346 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B2612843 : Blo 814346 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B7855825 : Blo 814346 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B44752763 : Blo 814346 44752763 := bstep (se 1 (by rfl) ⟨33564572, by rfl⟩ : syracuseStep 44752763 = 67129145) B67129145
theorem B4972823 : Blo 814346 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B18833897 : Blo 814346 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B2122247 : Blo 814346 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B1958681 : Blo 814346 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B3105661 : Blo 814346 3105661 := bstep (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) B1164623
theorem B1958921 : Blo 814346 1958921 := bstep (se 2 (by rfl) ⟨734595, by rfl⟩ : syracuseStep 1958921 = 1469191) B1469191
theorem B2614457 : Blo 814346 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B1860833 : Blo 814346 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B101673053 : Blo 814346 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B4254239 : Blo 814346 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1305191 : Blo 814346 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B2321273 : Blo 814346 2321273 := bstep (se 2 (by rfl) ⟨870477, by rfl⟩ : syracuseStep 2321273 = 1740955) B1740955
theorem B5237729 : Blo 814346 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B6974585 : Blo 814346 6974585 := bstep (se 2 (by rfl) ⟨2615469, by rfl⟩ : syracuseStep 6974585 = 5230939) B5230939
theorem B814407 : Blo 814346 814407 := bstep (se 1 (by rfl) ⟨610805, by rfl⟩ : syracuseStep 814407 = 1221611) B1221611
theorem B815135 : Blo 814346 815135 := bstep (se 1 (by rfl) ⟨611351, by rfl⟩ : syracuseStep 815135 = 1222703) B1222703
theorem B2387999 : Blo 814346 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B4649015 : Blo 814346 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B5042351 : Blo 814346 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B815311 : Blo 814346 815311 := bstep (se 1 (by rfl) ⟨611483, by rfl⟩ : syracuseStep 815311 = 1222967) B1222967
theorem B1962227 : Blo 814346 1962227 := bstep (se 1 (by rfl) ⟨1471670, by rfl⟩ : syracuseStep 1962227 = 2943341) B2943341
theorem B815431 : Blo 814346 815431 := bstep (se 1 (by rfl) ⟨611573, by rfl⟩ : syracuseStep 815431 = 1223147) B1223147
theorem B6287759 : Blo 814346 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B10089131 : Blo 814346 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B815899 : Blo 814346 815899 := bstep (se 1 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 815899 = 1223849) B1223849
theorem B2749247 : Blo 814346 2749247 := bstep (se 1 (by rfl) ⟨2061935, by rfl⟩ : syracuseStep 2749247 = 4123871) B4123871
theorem B816175 : Blo 814346 816175 := bstep (se 1 (by rfl) ⟨612131, by rfl⟩ : syracuseStep 816175 = 1224263) B1224263
theorem B816295 : Blo 814346 816295 := bstep (se 1 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 816295 = 1224443) B1224443
theorem B816743 : Blo 814346 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1832615 : Blo 814346 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B1963687 : Blo 814346 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B1832795 : Blo 814346 1832795 := bstep (se 1 (by rfl) ⟨1374596, by rfl⟩ : syracuseStep 1832795 = 2749193) B2749193
theorem B817023 : Blo 814346 817023 := bstep (se 1 (by rfl) ⟨612767, by rfl⟩ : syracuseStep 817023 = 1225535) B1225535
theorem B3930029 : Blo 814346 3930029 := bstep (se 3 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 3930029 = 1473761) B1473761
theorem B817119 : Blo 814346 817119 := bstep (se 1 (by rfl) ⟨612839, by rfl⟩ : syracuseStep 817119 = 1225679) B1225679
theorem B817147 : Blo 814346 817147 := bstep (se 1 (by rfl) ⟨612860, by rfl⟩ : syracuseStep 817147 = 1225721) B1225721
theorem B817179 : Blo 814346 817179 := bstep (se 1 (by rfl) ⟨612884, by rfl⟩ : syracuseStep 817179 = 1225769) B1225769
theorem B817199 : Blo 814346 817199 := bstep (se 1 (by rfl) ⟨612899, by rfl⟩ : syracuseStep 817199 = 1225799) B1225799
theorem B817319 : Blo 814346 817319 := bstep (se 1 (by rfl) ⟨612989, by rfl⟩ : syracuseStep 817319 = 1225979) B1225979
theorem B4127597 : Blo 814346 4127597 := bstep (se 3 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 4127597 = 1547849) B1547849
theorem B916447 : Blo 814346 916447 := bstep (se 1 (by rfl) ⟨687335, by rfl⟩ : syracuseStep 916447 = 1374671) B1374671
theorem B818143 : Blo 814346 818143 := bstep (se 1 (by rfl) ⟨613607, by rfl⟩ : syracuseStep 818143 = 1227215) B1227215
theorem B818203 : Blo 814346 818203 := bstep (se 1 (by rfl) ⟨613652, by rfl⟩ : syracuseStep 818203 = 1227305) B1227305
theorem B2325647 : Blo 814346 2325647 := bstep (se 1 (by rfl) ⟨1744235, by rfl⟩ : syracuseStep 2325647 = 3488471) B3488471
theorem B2063515 : Blo 814346 2063515 := bstep (se 1 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 2063515 = 3095273) B3095273
theorem B818331 : Blo 814346 818331 := bstep (se 1 (by rfl) ⟨613748, by rfl⟩ : syracuseStep 818331 = 1227497) B1227497
theorem B2752001 : Blo 814346 2752001 := bstep (se 2 (by rfl) ⟨1032000, by rfl⟩ : syracuseStep 2752001 = 2064001) B2064001
theorem B4193855 : Blo 814346 4193855 := bstep (se 1 (by rfl) ⟨3145391, by rfl⟩ : syracuseStep 4193855 = 6290783) B6290783
theorem B1277561 : Blo 814346 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B917311 : Blo 814346 917311 := bstep (se 1 (by rfl) ⟨687983, by rfl⟩ : syracuseStep 917311 = 1375967) B1375967
theorem B1310555 : Blo 814346 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B884827 : Blo 814346 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B1835135 : Blo 814346 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B2752811 : Blo 814346 2752811 := bstep (se 1 (by rfl) ⟨2064608, by rfl⟩ : syracuseStep 2752811 = 4129217) B4129217
theorem B1376615 : Blo 814346 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B1835387 : Blo 814346 1835387 := bstep (se 1 (by rfl) ⟨1376540, by rfl⟩ : syracuseStep 1835387 = 2753081) B2753081
theorem B13926815 : Blo 814346 13926815 := bstep (se 1 (by rfl) ⟨10445111, by rfl⟩ : syracuseStep 13926815 = 20890223) B20890223
theorem B2064953 : Blo 814346 2064953 := bstep (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) B1548715
theorem B10584665 : Blo 814346 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B1376905 : Blo 814346 1376905 := bstep (se 2 (by rfl) ⟨516339, by rfl⟩ : syracuseStep 1376905 = 1032679) B1032679
theorem B2753351 : Blo 814346 2753351 := bstep (se 1 (by rfl) ⟨2065013, by rfl⟩ : syracuseStep 2753351 = 4130027) B4130027
theorem B1377607 : Blo 814346 1377607 := bstep (se 1 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 1377607 = 2066411) B2066411
theorem B919039 : Blo 814346 919039 := bstep (se 1 (by rfl) ⟨689279, by rfl⟩ : syracuseStep 919039 = 1378559) B1378559
theorem B26904349 : Blo 814346 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B1836971 : Blo 814346 1836971 := bstep (se 1 (by rfl) ⟨1377728, by rfl⟩ : syracuseStep 1836971 = 2755457) B2755457
theorem B1837025 : Blo 814346 1837025 := bstep (se 2 (by rfl) ⟨688884, by rfl⟩ : syracuseStep 1837025 = 1377769) B1377769
theorem B1837367 : Blo 814346 1837367 := bstep (se 1 (by rfl) ⟨1378025, by rfl⟩ : syracuseStep 1837367 = 2756051) B2756051
theorem B920191 : Blo 814346 920191 := bstep (se 1 (by rfl) ⟨690143, by rfl⟩ : syracuseStep 920191 = 1380287) B1380287
theorem B1837799 : Blo 814346 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B1838663 : Blo 814346 1838663 := bstep (se 1 (by rfl) ⟨1378997, by rfl⟩ : syracuseStep 1838663 = 2757995) B2757995
theorem B1380071 : Blo 814346 1380071 := bstep (se 1 (by rfl) ⟨1035053, by rfl⟩ : syracuseStep 1380071 = 2070107) B2070107
theorem B4132781 : Blo 814346 4132781 := bstep (se 3 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 4132781 = 1549793) B1549793
theorem B9932807 : Blo 814346 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B2986075 : Blo 814346 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B2756807 : Blo 814346 2756807 := bstep (se 1 (by rfl) ⟨2067605, by rfl⟩ : syracuseStep 2756807 = 4135211) B4135211
theorem B1839329 : Blo 814346 1839329 := bstep (se 2 (by rfl) ⟨689748, by rfl⟩ : syracuseStep 1839329 = 1379497) B1379497
theorem B79532441 : Blo 814346 79532441 := bstep (se 2 (by rfl) ⟨29824665, by rfl⟩ : syracuseStep 79532441 = 59649331) B59649331
theorem B5575159 : Blo 814346 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B1741895 : Blo 814346 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B2758103 : Blo 814346 2758103 := bstep (se 1 (by rfl) ⟨2068577, by rfl⟩ : syracuseStep 2758103 = 4137155) B4137155
theorem B3315215 : Blo 814346 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B12555931 : Blo 814346 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B1414831 : Blo 814346 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1742971 : Blo 814346 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B2759183 : Blo 814346 2759183 := bstep (se 1 (by rfl) ⟨2069387, by rfl⟩ : syracuseStep 2759183 = 4138775) B4138775
theorem B11344637 : Blo 814346 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B3480407 : Blo 814346 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B3480509 : Blo 814346 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B1547515 : Blo 814346 1547515 := bstep (se 1 (by rfl) ⟨1160636, by rfl⟩ : syracuseStep 1547515 = 2321273) B2321273
theorem B2760263 : Blo 814346 2760263 := bstep (se 1 (by rfl) ⟨2070197, by rfl⟩ : syracuseStep 2760263 = 4140395) B4140395
theorem B44768983 : Blo 814346 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B2761127 : Blo 814346 2761127 := bstep (se 1 (by rfl) ⟨2070845, by rfl⟩ : syracuseStep 2761127 = 4141691) B4141691
theorem B1221743 : Blo 814346 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B2761883 : Blo 814346 2761883 := bstep (se 1 (by rfl) ⟨2071412, by rfl⟩ : syracuseStep 2761883 = 4142825) B4142825
theorem B1221863 : Blo 814346 1221863 := bstep (se 1 (by rfl) ⟨916397, by rfl⟩ : syracuseStep 1221863 = 1832795) B1832795
theorem B1221929 : Blo 814346 1221929 := bstep (se 2 (by rfl) ⟨458223, by rfl⟩ : syracuseStep 1221929 = 916447) B916447
theorem B1550431 : Blo 814346 1550431 := bstep (se 1 (by rfl) ⟨1162823, by rfl⟩ : syracuseStep 1550431 = 2325647) B2325647
theorem B2795903 : Blo 814346 2795903 := bstep (se 1 (by rfl) ⟨2096927, by rfl⟩ : syracuseStep 2795903 = 4193855) B4193855
theorem B1223081 : Blo 814346 1223081 := bstep (se 2 (by rfl) ⟨458655, by rfl⟩ : syracuseStep 1223081 = 917311) B917311
theorem B6367997 : Blo 814346 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1223615 : Blo 814346 1223615 := bstep (se 1 (by rfl) ⟨917711, by rfl⟩ : syracuseStep 1223615 = 1835423) B1835423
theorem B13446269 : Blo 814346 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B3484883 : Blo 814346 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B1551707 : Blo 814346 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B1224347 : Blo 814346 1224347 := bstep (se 1 (by rfl) ⟨918260, by rfl⟩ : syracuseStep 1224347 = 1836521) B1836521
theorem B6205247 : Blo 814346 6205247 := bstep (se 1 (by rfl) ⟨4653935, by rfl⟩ : syracuseStep 6205247 = 9307871) B9307871
theorem B4140881 : Blo 814346 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B1552375 : Blo 814346 1552375 := bstep (se 1 (by rfl) ⟨1164281, by rfl⟩ : syracuseStep 1552375 = 2328563) B2328563
theorem B1224731 : Blo 814346 1224731 := bstep (se 1 (by rfl) ⟨918548, by rfl⟩ : syracuseStep 1224731 = 1837097) B1837097
theorem B1225151 : Blo 814346 1225151 := bstep (se 1 (by rfl) ⟨918863, by rfl⟩ : syracuseStep 1225151 = 1837727) B1837727
theorem B2798135 : Blo 814346 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B5223149 : Blo 814346 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B1225499 : Blo 814346 1225499 := bstep (se 1 (by rfl) ⟨919124, by rfl⟩ : syracuseStep 1225499 = 1838249) B1838249
theorem B152777677 : Blo 814346 152777677 := bstep (se 3 (by rfl) ⟨28645814, by rfl⟩ : syracuseStep 152777677 = 57291629) B57291629
theorem B1553575 : Blo 814346 1553575 := bstep (se 1 (by rfl) ⟨1165181, by rfl⟩ : syracuseStep 1553575 = 2330363) B2330363
theorem B5977981 : Blo 814346 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B15873947 : Blo 814346 15873947 := bstep (se 1 (by rfl) ⟨11905460, by rfl⟩ : syracuseStep 15873947 = 23810921) B23810921
theorem B4962221 : Blo 814346 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B1226975 : Blo 814346 1226975 := bstep (se 1 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 1226975 = 1840463) B1840463
theorem B1227035 : Blo 814346 1227035 := bstep (se 1 (by rfl) ⟨920276, by rfl⟩ : syracuseStep 1227035 = 1840553) B1840553
theorem B1227071 : Blo 814346 1227071 := bstep (se 1 (by rfl) ⟨920303, by rfl⟩ : syracuseStep 1227071 = 1840607) B1840607
theorem B1227455 : Blo 814346 1227455 := bstep (se 1 (by rfl) ⟨920591, by rfl⟩ : syracuseStep 1227455 = 1841183) B1841183
theorem B23575313 : Blo 814346 23575313 := bstep (se 2 (by rfl) ⟨8840742, by rfl⟩ : syracuseStep 23575313 = 17681485) B17681485
theorem B5225633 : Blo 814346 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B3095759 : Blo 814346 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B6962861 : Blo 814346 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B29835175 : Blo 814346 29835175 := bstep (se 1 (by rfl) ⟨22376381, by rfl⟩ : syracuseStep 29835175 = 44752763) B44752763
theorem B67782035 : Blo 814346 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B8832439 : Blo 814346 8832439 := bstep (se 1 (by rfl) ⟨6624329, by rfl⟩ : syracuseStep 8832439 = 13248659) B13248659
theorem B1165033 : Blo 814346 1165033 := bstep (se 2 (by rfl) ⟨436887, by rfl⟩ : syracuseStep 1165033 = 873775) B873775
theorem B3491819 : Blo 814346 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B3099343 : Blo 814346 3099343 := bstep (se 1 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 3099343 = 4649015) B4649015
theorem B4771295 : Blo 814346 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B10604039 : Blo 814346 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B3920147 : Blo 814346 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B4641407 : Blo 814346 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B10474433 : Blo 814346 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B873703 : Blo 814346 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B14112391 : Blo 814346 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B6280859 : Blo 814346 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B6609023 : Blo 814346 6609023 := bstep (se 1 (by rfl) ⟨4956767, by rfl⟩ : syracuseStep 6609023 = 9913535) B9913535
theorem B3103019 : Blo 814346 3103019 := bstep (se 1 (by rfl) ⟨2327264, by rfl⟩ : syracuseStep 3103019 = 4654529) B4654529
theorem B2611511 : Blo 814346 2611511 := bstep (se 1 (by rfl) ⟨1958633, by rfl⟩ : syracuseStep 2611511 = 3917267) B3917267
theorem B3529939 : Blo 814346 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B8936813 : Blo 814346 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B5889509 : Blo 814346 5889509 := bstep (se 4 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 5889509 = 1104283) B1104283
theorem B8380307 : Blo 814346 8380307 := bstep (se 1 (by rfl) ⟨6285230, by rfl⟩ : syracuseStep 8380307 = 12570461) B12570461
theorem B4644823 : Blo 814346 4644823 := bstep (se 1 (by rfl) ⟨3483617, by rfl⟩ : syracuseStep 4644823 = 6967235) B6967235
theorem B2613215 : Blo 814346 2613215 := bstep (se 1 (by rfl) ⟨1959911, by rfl⟩ : syracuseStep 2613215 = 3919823) B3919823
theorem B4645349 : Blo 814346 4645349 := bstep (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) B871003
theorem B2941481 : Blo 814346 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B2319131 : Blo 814346 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B9299123 : Blo 814346 9299123 := bstep (se 1 (by rfl) ⟨6974342, by rfl⟩ : syracuseStep 9299123 = 13948685) B13948685
theorem B4646555 : Blo 814346 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B3106937 : Blo 814346 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B1304743 : Blo 814346 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B814383 : Blo 814346 814383 := bstep (se 1 (by rfl) ⟨610787, by rfl⟩ : syracuseStep 814383 = 1221575) B1221575
theorem B1305947 : Blo 814346 1305947 := bstep (se 1 (by rfl) ⟨979460, by rfl⟩ : syracuseStep 1305947 = 1958921) B1958921
theorem B814527 : Blo 814346 814527 := bstep (se 1 (by rfl) ⟨610895, by rfl⟩ : syracuseStep 814527 = 1221791) B1221791
theorem B814623 : Blo 814346 814623 := bstep (se 1 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 814623 = 1221935) B1221935
theorem B814751 : Blo 814346 814751 := bstep (se 1 (by rfl) ⟨611063, by rfl⟩ : syracuseStep 814751 = 1222127) B1222127
theorem B814759 : Blo 814346 814759 := bstep (se 1 (by rfl) ⟨611069, by rfl⟩ : syracuseStep 814759 = 1222139) B1222139
theorem B814783 : Blo 814346 814783 := bstep (se 1 (by rfl) ⟨611087, by rfl⟩ : syracuseStep 814783 = 1222175) B1222175
theorem B1470143 : Blo 814346 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B814879 : Blo 814346 814879 := bstep (se 1 (by rfl) ⟨611159, by rfl⟩ : syracuseStep 814879 = 1222319) B1222319
theorem B814939 : Blo 814346 814939 := bstep (se 1 (by rfl) ⟨611204, by rfl⟩ : syracuseStep 814939 = 1222409) B1222409
theorem B814959 : Blo 814346 814959 := bstep (se 1 (by rfl) ⟨611219, by rfl⟩ : syracuseStep 814959 = 1222439) B1222439
theorem B815359 : Blo 814346 815359 := bstep (se 1 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 815359 = 1223039) B1223039
theorem B815519 : Blo 814346 815519 := bstep (se 1 (by rfl) ⟨611639, by rfl⟩ : syracuseStep 815519 = 1223279) B1223279
theorem B815663 : Blo 814346 815663 := bstep (se 1 (by rfl) ⟨611747, by rfl⟩ : syracuseStep 815663 = 1223495) B1223495
theorem B4649723 : Blo 814346 4649723 := bstep (se 1 (by rfl) ⟨3487292, by rfl⟩ : syracuseStep 4649723 = 6974585) B6974585
theorem B2618249 : Blo 814346 2618249 := bstep (se 2 (by rfl) ⟨981843, by rfl⟩ : syracuseStep 2618249 = 1963687) B1963687
theorem B816063 : Blo 814346 816063 := bstep (se 1 (by rfl) ⟨612047, by rfl⟩ : syracuseStep 816063 = 1224095) B1224095
theorem B19854305 : Blo 814346 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B2061359 : Blo 814346 2061359 := bstep (se 1 (by rfl) ⟨1546019, by rfl⟩ : syracuseStep 2061359 = 3092039) B3092039
theorem B816239 : Blo 814346 816239 := bstep (se 1 (by rfl) ⟨612179, by rfl⟩ : syracuseStep 816239 = 1224359) B1224359
theorem B816255 : Blo 814346 816255 := bstep (se 1 (by rfl) ⟨612191, by rfl⟩ : syracuseStep 816255 = 1224383) B1224383
theorem B816319 : Blo 814346 816319 := bstep (se 1 (by rfl) ⟨612239, by rfl⟩ : syracuseStep 816319 = 1224479) B1224479
theorem B25097465 : Blo 814346 25097465 := bstep (se 2 (by rfl) ⟨9411549, by rfl⟩ : syracuseStep 25097465 = 18823099) B18823099
theorem B816511 : Blo 814346 816511 := bstep (se 1 (by rfl) ⟨612383, by rfl⟩ : syracuseStep 816511 = 1224767) B1224767
theorem B1308151 : Blo 814346 1308151 := bstep (se 1 (by rfl) ⟨981113, by rfl⟩ : syracuseStep 1308151 = 1962227) B1962227
theorem B2946557 : Blo 814346 2946557 := bstep (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) B1104959
theorem B816639 : Blo 814346 816639 := bstep (se 1 (by rfl) ⟨612479, by rfl⟩ : syracuseStep 816639 = 1224959) B1224959
theorem B816667 : Blo 814346 816667 := bstep (se 1 (by rfl) ⟨612500, by rfl⟩ : syracuseStep 816667 = 1225001) B1225001
theorem B4191839 : Blo 814346 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B816847 : Blo 814346 816847 := bstep (se 1 (by rfl) ⟨612635, by rfl⟩ : syracuseStep 816847 = 1225271) B1225271
theorem B2324315 : Blo 814346 2324315 := bstep (se 1 (by rfl) ⟨1743236, by rfl⟩ : syracuseStep 2324315 = 3486473) B3486473
theorem B817007 : Blo 814346 817007 := bstep (se 1 (by rfl) ⟨612755, by rfl⟩ : syracuseStep 817007 = 1225511) B1225511
theorem B1832831 : Blo 814346 1832831 := bstep (se 1 (by rfl) ⟨1374623, by rfl⟩ : syracuseStep 1832831 = 2749247) B2749247
theorem B2062219 : Blo 814346 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B817087 : Blo 814346 817087 := bstep (se 1 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 817087 = 1225631) B1225631
theorem B2062331 : Blo 814346 2062331 := bstep (se 1 (by rfl) ⟨1546748, by rfl⟩ : syracuseStep 2062331 = 3093497) B3093497
theorem B817403 : Blo 814346 817403 := bstep (se 1 (by rfl) ⟨613052, by rfl⟩ : syracuseStep 817403 = 1226105) B1226105
theorem B817407 : Blo 814346 817407 := bstep (se 1 (by rfl) ⟨613055, by rfl⟩ : syracuseStep 817407 = 1226111) B1226111
theorem B3766607 : Blo 814346 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B817511 : Blo 814346 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B817631 : Blo 814346 817631 := bstep (se 1 (by rfl) ⟨613223, by rfl⟩ : syracuseStep 817631 = 1226447) B1226447
theorem B4127273 : Blo 814346 4127273 := bstep (se 2 (by rfl) ⟨1547727, by rfl⟩ : syracuseStep 4127273 = 3095455) B3095455
theorem B817767 : Blo 814346 817767 := bstep (se 1 (by rfl) ⟨613325, by rfl⟩ : syracuseStep 817767 = 1226651) B1226651
theorem B2620019 : Blo 814346 2620019 := bstep (se 1 (by rfl) ⟨1965014, by rfl⟩ : syracuseStep 2620019 = 3930029) B3930029
theorem B817791 : Blo 814346 817791 := bstep (se 1 (by rfl) ⟨613343, by rfl⟩ : syracuseStep 817791 = 1226687) B1226687
theorem B2063009 : Blo 814346 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B817903 : Blo 814346 817903 := bstep (se 1 (by rfl) ⟨613427, by rfl⟩ : syracuseStep 817903 = 1226855) B1226855
theorem B2751353 : Blo 814346 2751353 := bstep (se 2 (by rfl) ⟨1031757, by rfl⟩ : syracuseStep 2751353 = 2063515) B2063515
theorem B818159 : Blo 814346 818159 := bstep (se 1 (by rfl) ⟨613619, by rfl⟩ : syracuseStep 818159 = 1227239) B1227239
theorem B818207 : Blo 814346 818207 := bstep (se 1 (by rfl) ⟨613655, by rfl⟩ : syracuseStep 818207 = 1227311) B1227311
theorem B2751731 : Blo 814346 2751731 := bstep (se 1 (by rfl) ⟨2063798, by rfl⟩ : syracuseStep 2751731 = 4127597) B4127597
theorem B33979895 : Blo 814346 33979895 := bstep (se 1 (by rfl) ⟨25484921, by rfl⟩ : syracuseStep 33979895 = 50969843) B50969843
theorem B2588297 : Blo 814346 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B1834667 : Blo 814346 1834667 := bstep (se 1 (by rfl) ⟨1376000, by rfl⟩ : syracuseStep 1834667 = 2752001) B2752001
theorem B851707 : Blo 814346 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B1835207 : Blo 814346 1835207 := bstep (se 1 (by rfl) ⟨1376405, by rfl⟩ : syracuseStep 1835207 = 2752811) B2752811
theorem B917743 : Blo 814346 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B1376635 : Blo 814346 1376635 := bstep (se 1 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 1376635 = 2064953) B2064953
theorem B15925733 : Blo 814346 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B4719077 : Blo 814346 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B1835567 : Blo 814346 1835567 := bstep (se 1 (by rfl) ⟨1376675, by rfl⟩ : syracuseStep 1835567 = 2753351) B2753351
theorem B1835873 : Blo 814346 1835873 := bstep (se 2 (by rfl) ⟨688452, by rfl⟩ : syracuseStep 1835873 = 1376905) B1376905
theorem B45188023 : Blo 814346 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B2327879 : Blo 814346 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1836809 : Blo 814346 1836809 := bstep (se 2 (by rfl) ⟨688803, by rfl⟩ : syracuseStep 1836809 = 1377607) B1377607
theorem B3180863 : Blo 814346 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B6981997 : Blo 814346 6981997 := bstep (se 3 (by rfl) ⟨1309124, by rfl⟩ : syracuseStep 6981997 = 2618249) B2618249
theorem B920047 : Blo 814346 920047 := bstep (se 1 (by rfl) ⟨690035, by rfl⟩ : syracuseStep 920047 = 1380071) B1380071
theorem B2755187 : Blo 814346 2755187 := bstep (se 1 (by rfl) ⟨2066390, by rfl⟩ : syracuseStep 2755187 = 4132781) B4132781
theorem B6621871 : Blo 814346 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B2067241 : Blo 814346 2067241 := bstep (se 2 (by rfl) ⟨775215, by rfl⟩ : syracuseStep 2067241 = 1550431) B1550431
theorem B1837871 : Blo 814346 1837871 := bstep (se 1 (by rfl) ⟨1378403, by rfl⟩ : syracuseStep 1837871 = 2756807) B2756807
theorem B1739657 : Blo 814346 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B53021627 : Blo 814346 53021627 := bstep (se 1 (by rfl) ⟨39766220, by rfl⟩ : syracuseStep 53021627 = 79532441) B79532441
theorem B6982955 : Blo 814346 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B4132457 : Blo 814346 4132457 := bstep (se 2 (by rfl) ⟨1549671, by rfl⟩ : syracuseStep 4132457 = 3099343) B3099343
theorem B1838735 : Blo 814346 1838735 := bstep (se 1 (by rfl) ⟨1379051, by rfl⟩ : syracuseStep 1838735 = 2758103) B2758103
theorem B2068679 : Blo 814346 2068679 := bstep (se 1 (by rfl) ⟨1551509, by rfl⟩ : syracuseStep 2068679 = 3103019) B3103019
theorem B1741007 : Blo 814346 1741007 := bstep (se 1 (by rfl) ⟨1305755, by rfl⟩ : syracuseStep 1741007 = 2611511) B2611511
theorem B1839455 : Blo 814346 1839455 := bstep (se 1 (by rfl) ⟨1379591, by rfl⟩ : syracuseStep 1839455 = 2759183) B2759183
theorem B16748957 : Blo 814346 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B1840175 : Blo 814346 1840175 := bstep (se 1 (by rfl) ⟨1380131, by rfl⟩ : syracuseStep 1840175 = 2760263) B2760263
theorem B1742143 : Blo 814346 1742143 := bstep (se 1 (by rfl) ⟨1306607, by rfl⟩ : syracuseStep 1742143 = 2613215) B2613215
theorem B2069833 : Blo 814346 2069833 := bstep (se 2 (by rfl) ⟨776187, by rfl⟩ : syracuseStep 2069833 = 1552375) B1552375
theorem B1840751 : Blo 814346 1840751 := bstep (se 1 (by rfl) ⟨1380563, by rfl⟩ : syracuseStep 1840751 = 2761127) B2761127
theorem B1841255 : Blo 814346 1841255 := bstep (se 1 (by rfl) ⟨1380941, by rfl⟩ : syracuseStep 1841255 = 2761883) B2761883
theorem B6199415 : Blo 814346 6199415 := bstep (se 1 (by rfl) ⟨4649561, by rfl⟩ : syracuseStep 6199415 = 9299123) B9299123
theorem B2071291 : Blo 814346 2071291 := bstep (se 1 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 2071291 = 3106937) B3106937
theorem B2071433 : Blo 814346 2071433 := bstep (se 2 (by rfl) ⟨776787, by rfl⟩ : syracuseStep 2071433 = 1553575) B1553575
theorem B1744201 : Blo 814346 1744201 := bstep (se 2 (by rfl) ⟨654075, by rfl⟩ : syracuseStep 1744201 = 1308151) B1308151
theorem B16981325 : Blo 814346 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B18816521 : Blo 814346 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B4136831 : Blo 814346 4136831 := bstep (se 1 (by rfl) ⟨3102623, by rfl⟩ : syracuseStep 4136831 = 6205247) B6205247
theorem B2760587 : Blo 814346 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B3482099 : Blo 814346 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B2794559 : Blo 814346 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B1549543 : Blo 814346 1549543 := bstep (se 1 (by rfl) ⟨1162157, by rfl⟩ : syracuseStep 1549543 = 2324315) B2324315
theorem B1221887 : Blo 814346 1221887 := bstep (se 1 (by rfl) ⟨916415, by rfl⟩ : syracuseStep 1221887 = 1832831) B1832831
theorem B1746679 : Blo 814346 1746679 := bstep (se 1 (by rfl) ⟨1310009, by rfl⟩ : syracuseStep 1746679 = 2620019) B2620019
theorem B3483755 : Blo 814346 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B22653263 : Blo 814346 22653263 := bstep (se 1 (by rfl) ⟨16989947, by rfl⟩ : syracuseStep 22653263 = 33979895) B33979895
theorem B1223111 : Blo 814346 1223111 := bstep (se 1 (by rfl) ⟨917333, by rfl⟩ : syracuseStep 1223111 = 1834667) B1834667
theorem B1223423 : Blo 814346 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B1223591 : Blo 814346 1223591 := bstep (se 1 (by rfl) ⟨917693, by rfl⟩ : syracuseStep 1223591 = 1835387) B1835387
theorem B9284543 : Blo 814346 9284543 := bstep (se 1 (by rfl) ⟨6963407, by rfl⟩ : syracuseStep 9284543 = 13926815) B13926815
theorem B7056443 : Blo 814346 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B1224647 : Blo 814346 1224647 := bstep (se 1 (by rfl) ⟨918485, by rfl⟩ : syracuseStep 1224647 = 1836971) B1836971
theorem B1224683 : Blo 814346 1224683 := bstep (se 1 (by rfl) ⟨918512, by rfl⟩ : syracuseStep 1224683 = 1837025) B1837025
theorem B7843949 : Blo 814346 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B1224911 : Blo 814346 1224911 := bstep (se 1 (by rfl) ⟨918683, by rfl⟩ : syracuseStep 1224911 = 1837367) B1837367
theorem B1225199 : Blo 814346 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B11776585 : Blo 814346 11776585 := bstep (se 2 (by rfl) ⟨4416219, by rfl⟩ : syracuseStep 11776585 = 8832439) B8832439
theorem B1225385 : Blo 814346 1225385 := bstep (se 2 (by rfl) ⟨459519, by rfl⟩ : syracuseStep 1225385 = 919039) B919039
theorem B1225775 : Blo 814346 1225775 := bstep (se 1 (by rfl) ⟨919331, by rfl⟩ : syracuseStep 1225775 = 1838663) B1838663
theorem B1226219 : Blo 814346 1226219 := bstep (se 1 (by rfl) ⟨919664, by rfl⟩ : syracuseStep 1226219 = 1839329) B1839329
theorem B3094271 : Blo 814346 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B1161263 : Blo 814346 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B1226921 : Blo 814346 1226921 := bstep (se 2 (by rfl) ⟨460095, by rfl⟩ : syracuseStep 1226921 = 920191) B920191
theorem B4406015 : Blo 814346 4406015 := bstep (se 1 (by rfl) ⟨3304511, by rfl⟩ : syracuseStep 4406015 = 6609023) B6609023
theorem B3096899 : Blo 814346 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B3097703 : Blo 814346 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B203703569 : Blo 814346 203703569 := bstep (se 2 (by rfl) ⟨76388838, by rfl⟩ : syracuseStep 203703569 = 152777677) B152777677
theorem B27608501 : Blo 814346 27608501 := bstep (se 5 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 27608501 = 2588297) B2588297
theorem B1164937 : Blo 814346 1164937 := bstep (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) B873703
theorem B8964179 : Blo 814346 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B870631 : Blo 814346 870631 := bstep (se 1 (by rfl) ⟨652973, by rfl⟩ : syracuseStep 870631 = 1305947) B1305947
theorem B1034471 : Blo 814346 1034471 := bstep (se 1 (by rfl) ⟨775853, by rfl⟩ : syracuseStep 1034471 = 1551707) B1551707
theorem B1886441 : Blo 814346 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B3099815 : Blo 814346 3099815 := bstep (se 1 (by rfl) ⟨2324861, by rfl⟩ : syracuseStep 3099815 = 4649723) B4649723
theorem B16731643 : Blo 814346 16731643 := bstep (se 1 (by rfl) ⟨12548732, by rfl⟩ : syracuseStep 16731643 = 25097465) B25097465
theorem B6213509 : Blo 814346 6213509 := bstep (se 4 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 6213509 = 1165033) B1165033
theorem B4542437 : Blo 814346 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B2511071 : Blo 814346 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B4706585 : Blo 814346 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B15716875 : Blo 814346 15716875 := bstep (se 1 (by rfl) ⟨11787656, by rfl⟩ : syracuseStep 15716875 = 23575313) B23575313
theorem B59691977 : Blo 814346 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B4641907 : Blo 814346 4641907 := bstep (se 1 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 4641907 = 6962861) B6962861
theorem B6184349 : Blo 814346 6184349 := bstep (se 3 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 6184349 = 2319131) B2319131
theorem B35872465 : Blo 814346 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B2613431 : Blo 814346 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B8840573 : Blo 814346 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B7563091 : Blo 814346 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B2320271 : Blo 814346 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B2320339 : Blo 814346 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B5957875 : Blo 814346 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B3926339 : Blo 814346 3926339 := bstep (se 1 (by rfl) ⟨2944754, by rfl⟩ : syracuseStep 3926339 = 5889509) B5889509
theorem B7433545 : Blo 814346 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B814495 : Blo 814346 814495 := bstep (se 1 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 814495 = 1221743) B1221743
theorem B814575 : Blo 814346 814575 := bstep (se 1 (by rfl) ⟨610931, by rfl⟩ : syracuseStep 814575 = 1221863) B1221863
theorem B814619 : Blo 814346 814619 := bstep (se 1 (by rfl) ⟨610964, by rfl⟩ : syracuseStep 814619 = 1221929) B1221929
theorem B1863935 : Blo 814346 1863935 := bstep (se 1 (by rfl) ⟨1397951, by rfl⟩ : syracuseStep 1863935 = 2795903) B2795903
theorem B815387 : Blo 814346 815387 := bstep (se 1 (by rfl) ⟨611540, by rfl⟩ : syracuseStep 815387 = 1223081) B1223081
theorem B815743 : Blo 814346 815743 := bstep (se 1 (by rfl) ⟨611807, by rfl⟩ : syracuseStep 815743 = 1223615) B1223615
theorem B2323255 : Blo 814346 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B16741241 : Blo 814346 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B816231 : Blo 814346 816231 := bstep (se 1 (by rfl) ⟨612173, by rfl⟩ : syracuseStep 816231 = 1224347) B1224347
theorem B980095 : Blo 814346 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B2749625 : Blo 814346 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B816487 : Blo 814346 816487 := bstep (se 1 (by rfl) ⟨612365, by rfl⟩ : syracuseStep 816487 = 1224731) B1224731
theorem B2323961 : Blo 814346 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B816767 : Blo 814346 816767 := bstep (se 1 (by rfl) ⟨612575, by rfl⟩ : syracuseStep 816767 = 1225151) B1225151
theorem B1865423 : Blo 814346 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B816999 : Blo 814346 816999 := bstep (se 1 (by rfl) ⟨612749, by rfl⟩ : syracuseStep 816999 = 1225499) B1225499
theorem B13236203 : Blo 814346 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B1374239 : Blo 814346 1374239 := bstep (se 1 (by rfl) ⟨1030679, by rfl⟩ : syracuseStep 1374239 = 2061359) B2061359
theorem B1964371 : Blo 814346 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B10582631 : Blo 814346 10582631 := bstep (se 1 (by rfl) ⟨7936973, by rfl⟩ : syracuseStep 10582631 = 15873947) B15873947
theorem B3308147 : Blo 814346 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B1374887 : Blo 814346 1374887 := bstep (se 1 (by rfl) ⟨1031165, by rfl⟩ : syracuseStep 1374887 = 2062331) B2062331
theorem B28277437 : Blo 814346 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B817983 : Blo 814346 817983 := bstep (se 1 (by rfl) ⟨613487, by rfl⟩ : syracuseStep 817983 = 1226975) B1226975
theorem B818023 : Blo 814346 818023 := bstep (se 1 (by rfl) ⟨613517, by rfl⟩ : syracuseStep 818023 = 1227035) B1227035
theorem B818047 : Blo 814346 818047 := bstep (se 1 (by rfl) ⟨613535, by rfl⟩ : syracuseStep 818047 = 1227071) B1227071
theorem B2063353 : Blo 814346 2063353 := bstep (se 2 (by rfl) ⟨773757, by rfl⟩ : syracuseStep 2063353 = 1547515) B1547515
theorem B2751515 : Blo 814346 2751515 := bstep (se 1 (by rfl) ⟨2063636, by rfl⟩ : syracuseStep 2751515 = 4127273) B4127273
theorem B1375339 : Blo 814346 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B818303 : Blo 814346 818303 := bstep (se 1 (by rfl) ⟨613727, by rfl⟩ : syracuseStep 818303 = 1227455) B1227455
theorem B1834235 : Blo 814346 1834235 := bstep (se 1 (by rfl) ⟨1375676, by rfl⟩ : syracuseStep 1834235 = 2751353) B2751353
theorem B31882565 : Blo 814346 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B2063839 : Blo 814346 2063839 := bstep (se 1 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 2063839 = 3095759) B3095759
theorem B1834487 : Blo 814346 1834487 := bstep (se 1 (by rfl) ⟨1375865, by rfl⟩ : syracuseStep 1834487 = 2751731) B2751731
theorem B22347485 : Blo 814346 22347485 := bstep (se 3 (by rfl) ⟨4190153, by rfl⟩ : syracuseStep 22347485 = 8380307) B8380307
theorem B39780233 : Blo 814346 39780233 := bstep (se 2 (by rfl) ⟨14917587, by rfl⟩ : syracuseStep 39780233 = 29835175) B29835175
theorem B6193097 : Blo 814346 6193097 := bstep (se 2 (by rfl) ⟨2322411, by rfl⟩ : syracuseStep 6193097 = 4644823) B4644823
theorem B2064599 : Blo 814346 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B10617155 : Blo 814346 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B3146051 : Blo 814346 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B1835513 : Blo 814346 1835513 := bstep (se 2 (by rfl) ⟨688317, by rfl⟩ : syracuseStep 1835513 = 1376635) B1376635
theorem B2065135 : Blo 814346 2065135 := bstep (se 1 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 2065135 = 3097703) B3097703
theorem B44663885 : Blo 814346 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B2066057 : Blo 814346 2066057 := bstep (se 2 (by rfl) ⟨774771, by rfl⟩ : syracuseStep 2066057 = 1549543) B1549543
theorem B1836791 : Blo 814346 1836791 := bstep (se 1 (by rfl) ⟨1377593, by rfl⟩ : syracuseStep 1836791 = 2755187) B2755187
theorem B2066543 : Blo 814346 2066543 := bstep (se 1 (by rfl) ⟨1549907, by rfl⟩ : syracuseStep 2066543 = 3099815) B3099815
theorem B4655303 : Blo 814346 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B2328905 : Blo 814346 2328905 := bstep (se 2 (by rfl) ⟨873339, by rfl⟩ : syracuseStep 2328905 = 1746679) B1746679
theorem B2754971 : Blo 814346 2754971 := bstep (se 1 (by rfl) ⟨2066228, by rfl⟩ : syracuseStep 2754971 = 4132457) B4132457
theorem B20122037 : Blo 814346 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B1379119 : Blo 814346 1379119 := bstep (se 1 (by rfl) ⟨1034339, by rfl⟩ : syracuseStep 1379119 = 2068679) B2068679
theorem B1674047 : Blo 814346 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B9309329 : Blo 814346 9309329 := bstep (se 2 (by rfl) ⟨3490998, by rfl⟩ : syracuseStep 9309329 = 6981997) B6981997
theorem B2756321 : Blo 814346 2756321 := bstep (se 2 (by rfl) ⟨1033620, by rfl⟩ : syracuseStep 2756321 = 2067241) B2067241
theorem B4132943 : Blo 814346 4132943 := bstep (se 1 (by rfl) ⟨3099707, by rfl⟩ : syracuseStep 4132943 = 6199415) B6199415
theorem B1380955 : Blo 814346 1380955 := bstep (se 1 (by rfl) ⟨1035716, by rfl⟩ : syracuseStep 1380955 = 2071433) B2071433
theorem B2757887 : Blo 814346 2757887 := bstep (se 1 (by rfl) ⟨2068415, by rfl⟩ : syracuseStep 2757887 = 4136831) B4136831
theorem B1840391 : Blo 814346 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B2758589 : Blo 814346 2758589 := bstep (se 3 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 2758589 = 1034471) B1034471
theorem B15702113 : Blo 814346 15702113 := bstep (se 2 (by rfl) ⟨5888292, by rfl⟩ : syracuseStep 15702113 = 11776585) B11776585
theorem B1546847 : Blo 814346 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B2759777 : Blo 814346 2759777 := bstep (se 2 (by rfl) ⟨1034916, by rfl⟩ : syracuseStep 2759777 = 2069833) B2069833
theorem B18817181 : Blo 814346 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B2761721 : Blo 814346 2761721 := bstep (se 2 (by rfl) ⟨1035645, by rfl⟩ : syracuseStep 2761721 = 2071291) B2071291
theorem B1549307 : Blo 814346 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B8824135 : Blo 814346 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B50177389 : Blo 814346 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B7055087 : Blo 814346 7055087 := bstep (se 1 (by rfl) ⟨5291315, by rfl⟩ : syracuseStep 7055087 = 10582631) B10582631
theorem B2205431 : Blo 814346 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1222823 : Blo 814346 1222823 := bstep (se 1 (by rfl) ⟨917117, by rfl⟩ : syracuseStep 1222823 = 1834235) B1834235
theorem B1222991 : Blo 814346 1222991 := bstep (se 1 (by rfl) ⟨917243, by rfl⟩ : syracuseStep 1222991 = 1834487) B1834487
theorem B26520155 : Blo 814346 26520155 := bstep (se 1 (by rfl) ⟨19890116, by rfl⟩ : syracuseStep 26520155 = 39780233) B39780233
theorem B1223471 : Blo 814346 1223471 := bstep (se 1 (by rfl) ⟨917603, by rfl⟩ : syracuseStep 1223471 = 1835207) B1835207
theorem B1223657 : Blo 814346 1223657 := bstep (se 2 (by rfl) ⟨458871, by rfl⟩ : syracuseStep 1223657 = 917743) B917743
theorem B1223711 : Blo 814346 1223711 := bstep (se 1 (by rfl) ⟨917783, by rfl⟩ : syracuseStep 1223711 = 1835567) B1835567
theorem B1223915 : Blo 814346 1223915 := bstep (se 1 (by rfl) ⟨917936, by rfl⟩ : syracuseStep 1223915 = 1835873) B1835873
theorem B135802379 : Blo 814346 135802379 := bstep (se 1 (by rfl) ⟨101851784, by rfl⟩ : syracuseStep 135802379 = 203703569) B203703569
theorem B1224539 : Blo 814346 1224539 := bstep (se 1 (by rfl) ⟨918404, by rfl⟩ : syracuseStep 1224539 = 1836809) B1836809
theorem B5976119 : Blo 814346 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B1225247 : Blo 814346 1225247 := bstep (se 1 (by rfl) ⟨918935, by rfl⟩ : syracuseStep 1225247 = 1837871) B1837871
theorem B1159771 : Blo 814346 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B1553249 : Blo 814346 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B1225823 : Blo 814346 1225823 := bstep (se 1 (by rfl) ⟨919367, by rfl⟩ : syracuseStep 1225823 = 1838735) B1838735
theorem B4142339 : Blo 814346 4142339 := bstep (se 1 (by rfl) ⟨3106754, by rfl⟩ : syracuseStep 4142339 = 6213509) B6213509
theorem B3093785 : Blo 814346 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B3028291 : Blo 814346 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1160671 : Blo 814346 1160671 := bstep (se 1 (by rfl) ⟨870503, by rfl⟩ : syracuseStep 1160671 = 1741007) B1741007
theorem B7452157 : Blo 814346 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B1226303 : Blo 814346 1226303 := bstep (se 1 (by rfl) ⟨919727, by rfl⟩ : syracuseStep 1226303 = 1839455) B1839455
theorem B39794651 : Blo 814346 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B1226729 : Blo 814346 1226729 := bstep (se 2 (by rfl) ⟨460023, by rfl⟩ : syracuseStep 1226729 = 920047) B920047
theorem B1226783 : Blo 814346 1226783 := bstep (se 1 (by rfl) ⟨920087, by rfl⟩ : syracuseStep 1226783 = 1840175) B1840175
theorem B6207677 : Blo 814346 6207677 := bstep (se 3 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 6207677 = 2327879) B2327879
theorem B8829161 : Blo 814346 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B1227167 : Blo 814346 1227167 := bstep (se 1 (by rfl) ⟨920375, by rfl⟩ : syracuseStep 1227167 = 1840751) B1840751
theorem B1227503 : Blo 814346 1227503 := bstep (se 1 (by rfl) ⟨920627, by rfl⟩ : syracuseStep 1227503 = 1841255) B1841255
theorem B9911393 : Blo 814346 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B11320883 : Blo 814346 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B3096701 : Blo 814346 3096701 := bstep (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) B1161263
theorem B20955833 : Blo 814346 20955833 := bstep (se 2 (by rfl) ⟨7858437, by rfl⟩ : syracuseStep 20955833 = 15716875) B15716875
theorem B3097673 : Blo 814346 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B5229299 : Blo 814346 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B11160827 : Blo 814346 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B37703249 : Blo 814346 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B2937343 : Blo 814346 2937343 := bstep (se 1 (by rfl) ⟨2203007, by rfl⟩ : syracuseStep 2937343 = 4406015) B4406015
theorem B21255043 : Blo 814346 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B47829953 : Blo 814346 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B14898323 : Blo 814346 14898323 := bstep (se 1 (by rfl) ⟨11173742, by rfl⟩ : syracuseStep 14898323 = 22347485) B22347485
theorem B6969149 : Blo 814346 6969149 := bstep (se 3 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 6969149 = 2613431) B2613431
theorem B18405667 : Blo 814346 18405667 := bstep (se 1 (by rfl) ⟨13804250, by rfl⟩ : syracuseStep 18405667 = 27608501) B27608501
theorem B4643365 : Blo 814346 4643365 := bstep (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) B870631
theorem B60250697 : Blo 814346 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B31775333 : Blo 814346 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B2120575 : Blo 814346 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B35347751 : Blo 814346 35347751 := bstep (se 1 (by rfl) ⟨26510813, by rfl⟩ : syracuseStep 35347751 = 53021627) B53021627
theorem B10084121 : Blo 814346 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B3137723 : Blo 814346 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B22308857 : Blo 814346 22308857 := bstep (se 2 (by rfl) ⟨8365821, by rfl⟩ : syracuseStep 22308857 = 16731643) B16731643
theorem B4122899 : Blo 814346 4122899 := bstep (se 1 (by rfl) ⟨3092174, by rfl⟩ : syracuseStep 4122899 = 6184349) B6184349
theorem B2321399 : Blo 814346 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B814591 : Blo 814346 814591 := bstep (se 1 (by rfl) ⟨610943, by rfl⟩ : syracuseStep 814591 = 1221887) B1221887
theorem B5893715 : Blo 814346 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B2322503 : Blo 814346 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B6189209 : Blo 814346 6189209 := bstep (se 2 (by rfl) ⟨2320953, by rfl⟩ : syracuseStep 6189209 = 4641907) B4641907
theorem B1306793 : Blo 814346 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B2617559 : Blo 814346 2617559 := bstep (se 1 (by rfl) ⟨1963169, by rfl⟩ : syracuseStep 2617559 = 3926339) B3926339
theorem B15102175 : Blo 814346 15102175 := bstep (se 1 (by rfl) ⟨11326631, by rfl⟩ : syracuseStep 15102175 = 22653263) B22653263
theorem B815407 : Blo 814346 815407 := bstep (se 1 (by rfl) ⟨611555, by rfl⟩ : syracuseStep 815407 = 1223111) B1223111
theorem B2322857 : Blo 814346 2322857 := bstep (se 2 (by rfl) ⟨871071, by rfl⟩ : syracuseStep 2322857 = 1742143) B1742143
theorem B815615 : Blo 814346 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B815727 : Blo 814346 815727 := bstep (se 1 (by rfl) ⟨611795, by rfl⟩ : syracuseStep 815727 = 1223591) B1223591
theorem B6189695 : Blo 814346 6189695 := bstep (se 1 (by rfl) ⟨4642271, by rfl⟩ : syracuseStep 6189695 = 9284543) B9284543
theorem B816431 : Blo 814346 816431 := bstep (se 1 (by rfl) ⟨612323, by rfl⟩ : syracuseStep 816431 = 1224647) B1224647
theorem B816455 : Blo 814346 816455 := bstep (se 1 (by rfl) ⟨612341, by rfl⟩ : syracuseStep 816455 = 1224683) B1224683
theorem B816607 : Blo 814346 816607 := bstep (se 1 (by rfl) ⟨612455, by rfl⟩ : syracuseStep 816607 = 1224911) B1224911
theorem B1242623 : Blo 814346 1242623 := bstep (se 1 (by rfl) ⟨931967, by rfl⟩ : syracuseStep 1242623 = 1863935) B1863935
theorem B816799 : Blo 814346 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B2619161 : Blo 814346 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B816923 : Blo 814346 816923 := bstep (se 1 (by rfl) ⟨612692, by rfl⟩ : syracuseStep 816923 = 1225385) B1225385
theorem B817183 : Blo 814346 817183 := bstep (se 1 (by rfl) ⟨612887, by rfl⟩ : syracuseStep 817183 = 1225775) B1225775
theorem B1833083 : Blo 814346 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B817479 : Blo 814346 817479 := bstep (se 1 (by rfl) ⟨613109, by rfl⟩ : syracuseStep 817479 = 1226219) B1226219
theorem B1243615 : Blo 814346 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B2062847 : Blo 814346 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B2751137 : Blo 814346 2751137 := bstep (se 2 (by rfl) ⟨1031676, by rfl⟩ : syracuseStep 2751137 = 2063353) B2063353
theorem B916159 : Blo 814346 916159 := bstep (se 1 (by rfl) ⟨687119, by rfl⟩ : syracuseStep 916159 = 1374239) B1374239
theorem B817947 : Blo 814346 817947 := bstep (se 1 (by rfl) ⟨613460, by rfl⟩ : syracuseStep 817947 = 1226921) B1226921
theorem B1833785 : Blo 814346 1833785 := bstep (se 2 (by rfl) ⟨687669, by rfl⟩ : syracuseStep 1833785 = 1375339) B1375339
theorem B2325601 : Blo 814346 2325601 := bstep (se 2 (by rfl) ⟨872100, by rfl⟩ : syracuseStep 2325601 = 1744201) B1744201
theorem B916591 : Blo 814346 916591 := bstep (se 1 (by rfl) ⟨687443, by rfl⟩ : syracuseStep 916591 = 1374887) B1374887
theorem B2751785 : Blo 814346 2751785 := bstep (se 2 (by rfl) ⟨1031919, by rfl⟩ : syracuseStep 2751785 = 2063839) B2063839
theorem B1834343 : Blo 814346 1834343 := bstep (se 1 (by rfl) ⟨1375757, by rfl⟩ : syracuseStep 1834343 = 2751515) B2751515
theorem B4128731 : Blo 814346 4128731 := bstep (se 1 (by rfl) ⟨3096548, by rfl⟩ : syracuseStep 4128731 = 6193097) B6193097
theorem B2064467 : Blo 814346 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B1376399 : Blo 814346 1376399 := bstep (se 1 (by rfl) ⟨1032299, by rfl⟩ : syracuseStep 1376399 = 2064599) B2064599
theorem B7078103 : Blo 814346 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B2065115 : Blo 814346 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B8389469 : Blo 814346 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B2753513 : Blo 814346 2753513 := bstep (se 2 (by rfl) ⟨1032567, by rfl⟩ : syracuseStep 2753513 = 2065135) B2065135
theorem B1377371 : Blo 814346 1377371 := bstep (se 1 (by rfl) ⟨1033028, by rfl⟩ : syracuseStep 1377371 = 2066057) B2066057
theorem B1377695 : Blo 814346 1377695 := bstep (se 1 (by rfl) ⟨1033271, by rfl⟩ : syracuseStep 1377695 = 2066543) B2066543
theorem B1836647 : Blo 814346 1836647 := bstep (se 1 (by rfl) ⟨1377485, by rfl⟩ : syracuseStep 1836647 = 2754971) B2754971
theorem B11765513 : Blo 814346 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B1116031 : Blo 814346 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B7440551 : Blo 814346 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B25135499 : Blo 814346 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B1837547 : Blo 814346 1837547 := bstep (se 1 (by rfl) ⟨1378160, by rfl⟩ : syracuseStep 1837547 = 2756321) B2756321
theorem B4131485 : Blo 814346 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B2755295 : Blo 814346 2755295 := bstep (se 1 (by rfl) ⟨2066471, by rfl⟩ : syracuseStep 2755295 = 4132943) B4132943
theorem B31886635 : Blo 814346 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B9932215 : Blo 814346 9932215 := bstep (se 1 (by rfl) ⟨7449161, by rfl⟩ : syracuseStep 9932215 = 14898323) B14898323
theorem B1838591 : Blo 814346 1838591 := bstep (se 1 (by rfl) ⟨1378943, by rfl⟩ : syracuseStep 1838591 = 2757887) B2757887
theorem B1838825 : Blo 814346 1838825 := bstep (se 2 (by rfl) ⟨689559, by rfl⟩ : syracuseStep 1838825 = 1379119) B1379119
theorem B1839059 : Blo 814346 1839059 := bstep (se 1 (by rfl) ⟨1379294, by rfl⟩ : syracuseStep 1839059 = 2758589) B2758589
theorem B18813565 : Blo 814346 18813565 := bstep (se 3 (by rfl) ⟨3527543, by rfl⟩ : syracuseStep 18813565 = 7055087) B7055087
theorem B1839851 : Blo 814346 1839851 := bstep (se 1 (by rfl) ⟨1379888, by rfl⟩ : syracuseStep 1839851 = 2759777) B2759777
theorem B23565167 : Blo 814346 23565167 := bstep (se 1 (by rfl) ⟨17673875, by rfl⟩ : syracuseStep 23565167 = 35347751) B35347751
theorem B6722747 : Blo 814346 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1841147 : Blo 814346 1841147 := bstep (se 1 (by rfl) ⟨1380860, by rfl⟩ : syracuseStep 1841147 = 2761721) B2761721
theorem B1546361 : Blo 814346 1546361 := bstep (se 2 (by rfl) ⟨579885, by rfl⟩ : syracuseStep 1546361 = 1159771) B1159771
theorem B1841273 : Blo 814346 1841273 := bstep (se 2 (by rfl) ⟨690477, by rfl⟩ : syracuseStep 1841273 = 1380955) B1380955
theorem B1547561 : Blo 814346 1547561 := bstep (se 2 (by rfl) ⟨580335, by rfl⟩ : syracuseStep 1547561 = 1160671) B1160671
theorem B1547599 : Blo 814346 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B9936209 : Blo 814346 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B1548335 : Blo 814346 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B1745039 : Blo 814346 1745039 := bstep (se 1 (by rfl) ⟨1308779, by rfl⟩ : syracuseStep 1745039 = 2617559) B2617559
theorem B1548571 : Blo 814346 1548571 := bstep (se 1 (by rfl) ⟨1161428, by rfl⟩ : syracuseStep 1548571 = 2322857) B2322857
theorem B2761559 : Blo 814346 2761559 := bstep (se 1 (by rfl) ⟨2071169, by rfl⟩ : syracuseStep 2761559 = 4142339) B4142339
theorem B1221545 : Blo 814346 1221545 := bstep (se 2 (by rfl) ⟨458079, by rfl⟩ : syracuseStep 1221545 = 916159) B916159
theorem B828415 : Blo 814346 828415 := bstep (se 1 (by rfl) ⟨621311, by rfl⟩ : syracuseStep 828415 = 1242623) B1242623
theorem B2827433 : Blo 814346 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B1746107 : Blo 814346 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B1222055 : Blo 814346 1222055 := bstep (se 1 (by rfl) ⟨916541, by rfl⟩ : syracuseStep 1222055 = 1833083) B1833083
theorem B4138451 : Blo 814346 4138451 := bstep (se 1 (by rfl) ⟨3103838, by rfl⟩ : syracuseStep 4138451 = 6207677) B6207677
theorem B1222121 : Blo 814346 1222121 := bstep (se 2 (by rfl) ⟨458295, by rfl⟩ : syracuseStep 1222121 = 916591) B916591
theorem B1222523 : Blo 814346 1222523 := bstep (se 1 (by rfl) ⟨916892, by rfl⟩ : syracuseStep 1222523 = 1833785) B1833785
theorem B1222895 : Blo 814346 1222895 := bstep (se 1 (by rfl) ⟨917171, by rfl⟩ : syracuseStep 1222895 = 1834343) B1834343
theorem B7547255 : Blo 814346 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B1223675 : Blo 814346 1223675 := bstep (se 1 (by rfl) ⟨917756, by rfl⟩ : syracuseStep 1223675 = 1835513) B1835513
theorem B3484781 : Blo 814346 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B13970555 : Blo 814346 13970555 := bstep (se 1 (by rfl) ⟨10477916, by rfl⟩ : syracuseStep 13970555 = 20955833) B20955833
theorem B1224527 : Blo 814346 1224527 := bstep (se 1 (by rfl) ⟨918395, by rfl⟩ : syracuseStep 1224527 = 1836791) B1836791
theorem B1552603 : Blo 814346 1552603 := bstep (se 1 (by rfl) ⟨1164452, by rfl⟩ : syracuseStep 1552603 = 2328905) B2328905
theorem B13414691 : Blo 814346 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B3486199 : Blo 814346 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B6206219 : Blo 814346 6206219 := bstep (se 1 (by rfl) ⟨4654664, by rfl⟩ : syracuseStep 6206219 = 9309329) B9309329
theorem B1226927 : Blo 814346 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B10468075 : Blo 814346 10468075 := bstep (se 1 (by rfl) ⟨7851056, by rfl⟩ : syracuseStep 10468075 = 15702113) B15702113
theorem B1031231 : Blo 814346 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B20136233 : Blo 814346 20136233 := bstep (se 2 (by rfl) ⟨7551087, by rfl⟩ : syracuseStep 20136233 = 15102175) B15102175
theorem B3916457 : Blo 814346 3916457 := bstep (se 2 (by rfl) ⟨1468671, by rfl⟩ : syracuseStep 3916457 = 2937343) B2937343
theorem B338936885 : Blo 814346 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B64603541 : Blo 814346 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B17680103 : Blo 814346 17680103 := bstep (se 1 (by rfl) ⟨13260077, by rfl⟩ : syracuseStep 17680103 = 26520155) B26520155
theorem B3984079 : Blo 814346 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B1035499 : Blo 814346 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B1658153 : Blo 814346 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B26529767 : Blo 814346 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B3100801 : Blo 814346 3100801 := bstep (se 2 (by rfl) ⟨1162800, by rfl⟩ : syracuseStep 3100801 = 2325601) B2325601
theorem B5886107 : Blo 814346 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B6607595 : Blo 814346 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B29775923 : Blo 814346 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B3103535 : Blo 814346 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B66903185 : Blo 814346 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B4646099 : Blo 814346 4646099 := bstep (se 1 (by rfl) ⟨3484574, by rfl⟩ : syracuseStep 4646099 = 6969149) B6969149
theorem B40167131 : Blo 814346 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B12544787 : Blo 814346 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B2091815 : Blo 814346 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B1470287 : Blo 814346 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B28340057 : Blo 814346 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B14872571 : Blo 814346 14872571 := bstep (se 1 (by rfl) ⟨11154428, by rfl⟩ : syracuseStep 14872571 = 22308857) B22308857
theorem B815215 : Blo 814346 815215 := bstep (se 1 (by rfl) ⟨611411, by rfl⟩ : syracuseStep 815215 = 1222823) B1222823
theorem B2748599 : Blo 814346 2748599 := bstep (se 1 (by rfl) ⟨2061449, by rfl⟩ : syracuseStep 2748599 = 4122899) B4122899
theorem B815327 : Blo 814346 815327 := bstep (se 1 (by rfl) ⟨611495, by rfl⟩ : syracuseStep 815327 = 1222991) B1222991
theorem B815647 : Blo 814346 815647 := bstep (se 1 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 815647 = 1223471) B1223471
theorem B815771 : Blo 814346 815771 := bstep (se 1 (by rfl) ⟨611828, by rfl⟩ : syracuseStep 815771 = 1223657) B1223657
theorem B815807 : Blo 814346 815807 := bstep (se 1 (by rfl) ⟨611855, by rfl⟩ : syracuseStep 815807 = 1223711) B1223711
theorem B815943 : Blo 814346 815943 := bstep (se 1 (by rfl) ⟨611957, by rfl⟩ : syracuseStep 815943 = 1223915) B1223915
theorem B90534919 : Blo 814346 90534919 := bstep (se 1 (by rfl) ⟨67901189, by rfl⟩ : syracuseStep 90534919 = 135802379) B135802379
theorem B3929143 : Blo 814346 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B816359 : Blo 814346 816359 := bstep (se 1 (by rfl) ⟨612269, by rfl⟩ : syracuseStep 816359 = 1224539) B1224539
theorem B4126139 : Blo 814346 4126139 := bstep (se 1 (by rfl) ⟨3094604, by rfl⟩ : syracuseStep 4126139 = 6189209) B6189209
theorem B816831 : Blo 814346 816831 := bstep (se 1 (by rfl) ⟨612623, by rfl⟩ : syracuseStep 816831 = 1225247) B1225247
theorem B24540889 : Blo 814346 24540889 := bstep (se 2 (by rfl) ⟨9202833, by rfl⟩ : syracuseStep 24540889 = 18405667) B18405667
theorem B4126463 : Blo 814346 4126463 := bstep (se 1 (by rfl) ⟨3094847, by rfl⟩ : syracuseStep 4126463 = 6189695) B6189695
theorem B6191153 : Blo 814346 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B817215 : Blo 814346 817215 := bstep (se 1 (by rfl) ⟨612911, by rfl⟩ : syracuseStep 817215 = 1225823) B1225823
theorem B2062523 : Blo 814346 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B817535 : Blo 814346 817535 := bstep (se 1 (by rfl) ⟨613151, by rfl⟩ : syracuseStep 817535 = 1226303) B1226303
theorem B817819 : Blo 814346 817819 := bstep (se 1 (by rfl) ⟨613364, by rfl⟩ : syracuseStep 817819 = 1226729) B1226729
theorem B817855 : Blo 814346 817855 := bstep (se 1 (by rfl) ⟨613391, by rfl⟩ : syracuseStep 817855 = 1226783) B1226783
theorem B818111 : Blo 814346 818111 := bstep (se 1 (by rfl) ⟨613583, by rfl⟩ : syracuseStep 818111 = 1227167) B1227167
theorem B1375231 : Blo 814346 1375231 := bstep (se 1 (by rfl) ⟨1031423, by rfl⟩ : syracuseStep 1375231 = 2062847) B2062847
theorem B1834091 : Blo 814346 1834091 := bstep (se 1 (by rfl) ⟨1375568, by rfl⟩ : syracuseStep 1834091 = 2751137) B2751137
theorem B818335 : Blo 814346 818335 := bstep (se 1 (by rfl) ⟨613751, by rfl⟩ : syracuseStep 818335 = 1227503) B1227503
theorem B1834523 : Blo 814346 1834523 := bstep (se 1 (by rfl) ⟨1375892, by rfl⟩ : syracuseStep 1834523 = 2751785) B2751785
theorem B2752487 : Blo 814346 2752487 := bstep (se 1 (by rfl) ⟨2064365, by rfl⟩ : syracuseStep 2752487 = 4128731) B4128731
theorem B1376311 : Blo 814346 1376311 := bstep (se 1 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 1376311 = 2064467) B2064467
theorem B917599 : Blo 814346 917599 := bstep (se 1 (by rfl) ⟨688199, by rfl⟩ : syracuseStep 917599 = 1376399) B1376399
theorem B4128893 : Blo 814346 4128893 := bstep (se 3 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 4128893 = 1548335) B1548335
theorem B4718735 : Blo 814346 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B2064761 : Blo 814346 2064761 := bstep (se 2 (by rfl) ⟨774285, by rfl⟩ : syracuseStep 2064761 = 1548571) B1548571
theorem B1376743 : Blo 814346 1376743 := bstep (se 1 (by rfl) ⟨1032557, by rfl⟩ : syracuseStep 1376743 = 2065115) B2065115
theorem B1835675 : Blo 814346 1835675 := bstep (se 1 (by rfl) ⟨1376756, by rfl⟩ : syracuseStep 1835675 = 2753513) B2753513
theorem B918247 : Blo 814346 918247 := bstep (se 1 (by rfl) ⟨688685, by rfl⟩ : syracuseStep 918247 = 1377371) B1377371
theorem B918463 : Blo 814346 918463 := bstep (se 1 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 918463 = 1377695) B1377695
theorem B2754323 : Blo 814346 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B1836863 : Blo 814346 1836863 := bstep (se 1 (by rfl) ⟨1377647, by rfl⟩ : syracuseStep 1836863 = 2755295) B2755295
theorem B100339013 : Blo 814346 100339013 := bstep (se 4 (by rfl) ⟨9406782, by rfl⟩ : syracuseStep 100339013 = 18813565) B18813565
theorem B5312105 : Blo 814346 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B1380665 : Blo 814346 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B2069023 : Blo 814346 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B13242953 : Blo 814346 13242953 := bstep (se 2 (by rfl) ⟨4966107, by rfl⟩ : syracuseStep 13242953 = 9932215) B9932215
theorem B44602123 : Blo 814346 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B6624139 : Blo 814346 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B4134401 : Blo 814346 4134401 := bstep (se 2 (by rfl) ⟨1550400, by rfl⟩ : syracuseStep 4134401 = 3100801) B3100801
theorem B2070137 : Blo 814346 2070137 := bstep (se 2 (by rfl) ⟨776301, by rfl⟩ : syracuseStep 2070137 = 1552603) B1552603
theorem B1841039 : Blo 814346 1841039 := bstep (se 1 (by rfl) ⟨1380779, by rfl⟩ : syracuseStep 1841039 = 2761559) B2761559
theorem B2758967 : Blo 814346 2758967 := bstep (se 1 (by rfl) ⟨2069225, by rfl⟩ : syracuseStep 2758967 = 4138451) B4138451
theorem B8363191 : Blo 814346 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B9313703 : Blo 814346 9313703 := bstep (se 1 (by rfl) ⟨6985277, by rfl⟩ : syracuseStep 9313703 = 13970555) B13970555
theorem B4137479 : Blo 814346 4137479 := bstep (se 1 (by rfl) ⟨3103109, by rfl⟩ : syracuseStep 4137479 = 6206219) B6206219
theorem B1222727 : Blo 814346 1222727 := bstep (se 1 (by rfl) ⟨917045, by rfl⟩ : syracuseStep 1222727 = 1834091) B1834091
theorem B75573485 : Blo 814346 75573485 := bstep (se 3 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 75573485 = 28340057) B28340057
theorem B1223015 : Blo 814346 1223015 := bstep (se 1 (by rfl) ⟨917261, by rfl⟩ : syracuseStep 1223015 = 1834523) B1834523
theorem B43069027 : Blo 814346 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B1224431 : Blo 814346 1224431 := bstep (se 1 (by rfl) ⟨918323, by rfl⟩ : syracuseStep 1224431 = 1836647) B1836647
theorem B4960367 : Blo 814346 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B16756999 : Blo 814346 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B1225031 : Blo 814346 1225031 := bstep (se 1 (by rfl) ⟨918773, by rfl⟩ : syracuseStep 1225031 = 1837547) B1837547
theorem B1225727 : Blo 814346 1225727 := bstep (se 1 (by rfl) ⟨919295, by rfl⟩ : syracuseStep 1225727 = 1838591) B1838591
theorem B1225883 : Blo 814346 1225883 := bstep (se 1 (by rfl) ⟨919412, by rfl⟩ : syracuseStep 1225883 = 1838825) B1838825
theorem B1488041 : Blo 814346 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1226039 : Blo 814346 1226039 := bstep (se 1 (by rfl) ⟨919529, by rfl⟩ : syracuseStep 1226039 = 1839059) B1839059
theorem B4405063 : Blo 814346 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B1226567 : Blo 814346 1226567 := bstep (se 1 (by rfl) ⟨919925, by rfl⟩ : syracuseStep 1226567 = 1839851) B1839851
theorem B15710111 : Blo 814346 15710111 := bstep (se 1 (by rfl) ⟨11782583, by rfl⟩ : syracuseStep 15710111 = 23565167) B23565167
theorem B1227431 : Blo 814346 1227431 := bstep (se 1 (by rfl) ⟨920573, by rfl⟩ : syracuseStep 1227431 = 1841147) B1841147
theorem B1030907 : Blo 814346 1030907 := bstep (se 1 (by rfl) ⟨773180, by rfl⟩ : syracuseStep 1030907 = 1546361) B1546361
theorem B1227515 : Blo 814346 1227515 := bstep (se 1 (by rfl) ⟨920636, by rfl⟩ : syracuseStep 1227515 = 1841273) B1841273
theorem B42515513 : Blo 814346 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B31374701 : Blo 814346 31374701 := bstep (se 3 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 31374701 = 11765513) B11765513
theorem B1031707 : Blo 814346 1031707 := bstep (se 1 (by rfl) ⟨773780, by rfl⟩ : syracuseStep 1031707 = 1547561) B1547561
theorem B1163359 : Blo 814346 1163359 := bstep (se 1 (by rfl) ⟨872519, by rfl⟩ : syracuseStep 1163359 = 1745039) B1745039
theorem B1884955 : Blo 814346 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B1164071 : Blo 814346 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B3097399 : Blo 814346 3097399 := bstep (se 1 (by rfl) ⟨2323049, by rfl⟩ : syracuseStep 3097399 = 4646099) B4646099
theorem B5031503 : Blo 814346 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B1394543 : Blo 814346 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B32721185 : Blo 814346 32721185 := bstep (se 2 (by rfl) ⟨12270444, by rfl⟩ : syracuseStep 32721185 = 24540889) B24540889
theorem B9915047 : Blo 814346 9915047 := bstep (se 1 (by rfl) ⟨7436285, by rfl⟩ : syracuseStep 9915047 = 14872571) B14872571
theorem B2610971 : Blo 814346 2610971 := bstep (se 1 (by rfl) ⟨1958228, by rfl⟩ : syracuseStep 2610971 = 3916457) B3916457
theorem B5592979 : Blo 814346 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B225957923 : Blo 814346 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B35772509 : Blo 814346 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B53696621 : Blo 814346 53696621 := bstep (se 3 (by rfl) ⟨10068116, by rfl⟩ : syracuseStep 53696621 = 20136233) B20136233
theorem B11786735 : Blo 814346 11786735 := bstep (se 1 (by rfl) ⟨8840051, by rfl⟩ : syracuseStep 11786735 = 17680103) B17680103
theorem B1104553 : Blo 814346 1104553 := bstep (se 2 (by rfl) ⟨414207, by rfl⟩ : syracuseStep 1104553 = 828415) B828415
theorem B1105435 : Blo 814346 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B17686511 : Blo 814346 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B3924071 : Blo 814346 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B4481831 : Blo 814346 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B19850615 : Blo 814346 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B107112349 : Blo 814346 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B814363 : Blo 814346 814363 := bstep (se 1 (by rfl) ⟨610772, by rfl⟩ : syracuseStep 814363 = 1221545) B1221545
theorem B4648265 : Blo 814346 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B814703 : Blo 814346 814703 := bstep (se 1 (by rfl) ⟨611027, by rfl⟩ : syracuseStep 814703 = 1222055) B1222055
theorem B814747 : Blo 814346 814747 := bstep (se 1 (by rfl) ⟨611060, by rfl⟩ : syracuseStep 814747 = 1222121) B1222121
theorem B815015 : Blo 814346 815015 := bstep (se 1 (by rfl) ⟨611261, by rfl⟩ : syracuseStep 815015 = 1222523) B1222523
theorem B120713225 : Blo 814346 120713225 := bstep (se 2 (by rfl) ⟨45267459, by rfl⟩ : syracuseStep 120713225 = 90534919) B90534919
theorem B5238857 : Blo 814346 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B815263 : Blo 814346 815263 := bstep (se 1 (by rfl) ⟨611447, by rfl⟩ : syracuseStep 815263 = 1222895) B1222895
theorem B815783 : Blo 814346 815783 := bstep (se 1 (by rfl) ⟨611837, by rfl⟩ : syracuseStep 815783 = 1223675) B1223675
theorem B2323187 : Blo 814346 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B980191 : Blo 814346 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B816351 : Blo 814346 816351 := bstep (se 1 (by rfl) ⟨612263, by rfl⟩ : syracuseStep 816351 = 1224527) B1224527
theorem B1832399 : Blo 814346 1832399 := bstep (se 1 (by rfl) ⟨1374299, by rfl⟩ : syracuseStep 1832399 = 2748599) B2748599
theorem B2749949 : Blo 814346 2749949 := bstep (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) B1031231
theorem B2750759 : Blo 814346 2750759 := bstep (se 1 (by rfl) ⟨2063069, by rfl⟩ : syracuseStep 2750759 = 4126139) B4126139
theorem B13957433 : Blo 814346 13957433 := bstep (se 2 (by rfl) ⟨5234037, by rfl⟩ : syracuseStep 13957433 = 10468075) B10468075
theorem B2750975 : Blo 814346 2750975 := bstep (se 1 (by rfl) ⟨2063231, by rfl⟩ : syracuseStep 2750975 = 4126463) B4126463
theorem B1833641 : Blo 814346 1833641 := bstep (se 2 (by rfl) ⟨687615, by rfl⟩ : syracuseStep 1833641 = 1375231) B1375231
theorem B4127435 : Blo 814346 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B817951 : Blo 814346 817951 := bstep (se 1 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 817951 = 1226927) B1226927
theorem B1375015 : Blo 814346 1375015 := bstep (se 1 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 1375015 = 2062523) B2062523
theorem B2063465 : Blo 814346 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B1834991 : Blo 814346 1834991 := bstep (se 1 (by rfl) ⟨1376243, by rfl⟩ : syracuseStep 1834991 = 2752487) B2752487
theorem B1835081 : Blo 814346 1835081 := bstep (se 2 (by rfl) ⟨688155, by rfl⟩ : syracuseStep 1835081 = 1376311) B1376311
theorem B2752595 : Blo 814346 2752595 := bstep (se 1 (by rfl) ⟨2064446, by rfl⟩ : syracuseStep 2752595 = 4128893) B4128893
theorem B3145823 : Blo 814346 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B1376507 : Blo 814346 1376507 := bstep (se 1 (by rfl) ⟨1032380, by rfl⟩ : syracuseStep 1376507 = 2064761) B2064761
theorem B1835657 : Blo 814346 1835657 := bstep (se 2 (by rfl) ⟨688371, by rfl⟩ : syracuseStep 1835657 = 1376743) B1376743
theorem B4129865 : Blo 814346 4129865 := bstep (se 2 (by rfl) ⟨1548699, by rfl⟩ : syracuseStep 4129865 = 3097399) B3097399
theorem B1836215 : Blo 814346 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B3541403 : Blo 814346 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B920443 : Blo 814346 920443 := bstep (se 1 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 920443 = 1380665) B1380665
theorem B2756267 : Blo 814346 2756267 := bstep (se 1 (by rfl) ⟨2067200, by rfl⟩ : syracuseStep 2756267 = 4134401) B4134401
theorem B1380091 : Blo 814346 1380091 := bstep (se 1 (by rfl) ⟨1035068, by rfl⟩ : syracuseStep 1380091 = 2070137) B2070137
theorem B1740647 : Blo 814346 1740647 := bstep (se 1 (by rfl) ⟨1305485, by rfl⟩ : syracuseStep 1740647 = 2610971) B2610971
theorem B150638615 : Blo 814346 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B1839311 : Blo 814346 1839311 := bstep (se 1 (by rfl) ⟨1379483, by rfl⟩ : syracuseStep 1839311 = 2758967) B2758967
theorem B2758319 : Blo 814346 2758319 := bstep (se 1 (by rfl) ⟨2068739, by rfl⟩ : syracuseStep 2758319 = 4137479) B4137479
theorem B2987887 : Blo 814346 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2758697 : Blo 814346 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B5873417 : Blo 814346 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B1548791 : Blo 814346 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B992027 : Blo 814346 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B1221599 : Blo 814346 1221599 := bstep (se 1 (by rfl) ⟨916199, by rfl⟩ : syracuseStep 1221599 = 1832399) B1832399
theorem B11150921 : Blo 814346 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B1222427 : Blo 814346 1222427 := bstep (se 1 (by rfl) ⟨916820, by rfl⟩ : syracuseStep 1222427 = 1833641) B1833641
theorem B20916467 : Blo 814346 20916467 := bstep (se 1 (by rfl) ⟨15687350, by rfl⟩ : syracuseStep 20916467 = 31374701) B31374701
theorem B1223327 : Blo 814346 1223327 := bstep (se 1 (by rfl) ⟨917495, by rfl⟩ : syracuseStep 1223327 = 1834991) B1834991
theorem B1223465 : Blo 814346 1223465 := bstep (se 2 (by rfl) ⟨458799, by rfl⟩ : syracuseStep 1223465 = 917599) B917599
theorem B1551145 : Blo 814346 1551145 := bstep (se 2 (by rfl) ⟨581679, by rfl⟩ : syracuseStep 1551145 = 1163359) B1163359
theorem B1223783 : Blo 814346 1223783 := bstep (se 1 (by rfl) ⟨917837, by rfl⟩ : syracuseStep 1223783 = 1835675) B1835675
theorem B1224329 : Blo 814346 1224329 := bstep (se 2 (by rfl) ⟨459123, by rfl⟩ : syracuseStep 1224329 = 918247) B918247
theorem B3354335 : Blo 814346 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B1224575 : Blo 814346 1224575 := bstep (se 1 (by rfl) ⟨918431, by rfl⟩ : syracuseStep 1224575 = 1836863) B1836863
theorem B1224617 : Blo 814346 1224617 := bstep (se 2 (by rfl) ⟨459231, by rfl⟩ : syracuseStep 1224617 = 918463) B918463
theorem B89370661 : Blo 814346 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B142816465 : Blo 814346 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B8828635 : Blo 814346 8828635 := bstep (se 1 (by rfl) ⟨6621476, by rfl⟩ : syracuseStep 8828635 = 13242953) B13242953
theorem B1227359 : Blo 814346 1227359 := bstep (se 1 (by rfl) ⟨920519, by rfl⟩ : syracuseStep 1227359 = 1841039) B1841039
theorem B35797747 : Blo 814346 35797747 := bstep (se 1 (by rfl) ⟨26848310, by rfl⟩ : syracuseStep 35797747 = 53696621) B53696621
theorem B57425369 : Blo 814346 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B6209135 : Blo 814346 6209135 := bstep (se 1 (by rfl) ⟨4656851, by rfl⟩ : syracuseStep 6209135 = 9313703) B9313703
theorem B3718781 : Blo 814346 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B8832185 : Blo 814346 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B50382323 : Blo 814346 50382323 := bstep (se 1 (by rfl) ⟨37786742, by rfl⟩ : syracuseStep 50382323 = 75573485) B75573485
theorem B3098843 : Blo 814346 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B7457305 : Blo 814346 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B3492571 : Blo 814346 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B267570701 : Blo 814346 267570701 := bstep (se 3 (by rfl) ⟨50169506, by rfl⟩ : syracuseStep 267570701 = 100339013) B100339013
theorem B10473407 : Blo 814346 10473407 := bstep (se 1 (by rfl) ⟨7855055, by rfl⟩ : syracuseStep 10473407 = 15710111) B15710111
theorem B321901933 : Blo 814346 321901933 := bstep (se 3 (by rfl) ⟨60356612, by rfl⟩ : syracuseStep 321901933 = 120713225) B120713225
theorem B2513273 : Blo 814346 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B21814123 : Blo 814346 21814123 := bstep (se 1 (by rfl) ⟨16360592, by rfl⟩ : syracuseStep 21814123 = 32721185) B32721185
theorem B6610031 : Blo 814346 6610031 := bstep (se 1 (by rfl) ⟨4957523, by rfl⟩ : syracuseStep 6610031 = 9915047) B9915047
theorem B3104189 : Blo 814346 3104189 := bstep (se 3 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 3104189 = 1164071) B1164071
theorem B23848339 : Blo 814346 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B7857823 : Blo 814346 7857823 := bstep (se 1 (by rfl) ⟨5893367, by rfl⟩ : syracuseStep 7857823 = 11786735) B11786735
theorem B11791007 : Blo 814346 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B2616047 : Blo 814346 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B13233743 : Blo 814346 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B59469497 : Blo 814346 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B815151 : Blo 814346 815151 := bstep (se 1 (by rfl) ⟨611363, by rfl⟩ : syracuseStep 815151 = 1222727) B1222727
theorem B815343 : Blo 814346 815343 := bstep (se 1 (by rfl) ⟨611507, by rfl⟩ : syracuseStep 815343 = 1223015) B1223015
theorem B1306921 : Blo 814346 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B2749085 : Blo 814346 2749085 := bstep (se 3 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 2749085 = 1030907) B1030907
theorem B816287 : Blo 814346 816287 := bstep (se 1 (by rfl) ⟨612215, by rfl⟩ : syracuseStep 816287 = 1224431) B1224431
theorem B3306911 : Blo 814346 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B816687 : Blo 814346 816687 := bstep (se 1 (by rfl) ⟨612515, by rfl⟩ : syracuseStep 816687 = 1225031) B1225031
theorem B817151 : Blo 814346 817151 := bstep (se 1 (by rfl) ⟨612863, by rfl⟩ : syracuseStep 817151 = 1225727) B1225727
theorem B817255 : Blo 814346 817255 := bstep (se 1 (by rfl) ⟨612941, by rfl⟩ : syracuseStep 817255 = 1225883) B1225883
theorem B817359 : Blo 814346 817359 := bstep (se 1 (by rfl) ⟨613019, by rfl⟩ : syracuseStep 817359 = 1226039) B1226039
theorem B1472737 : Blo 814346 1472737 := bstep (se 2 (by rfl) ⟨552276, by rfl⟩ : syracuseStep 1472737 = 1104553) B1104553
theorem B1833299 : Blo 814346 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1833353 : Blo 814346 1833353 := bstep (se 2 (by rfl) ⟨687507, by rfl⟩ : syracuseStep 1833353 = 1375015) B1375015
theorem B817711 : Blo 814346 817711 := bstep (se 1 (by rfl) ⟨613283, by rfl⟩ : syracuseStep 817711 = 1226567) B1226567
theorem B1833839 : Blo 814346 1833839 := bstep (se 1 (by rfl) ⟨1375379, by rfl⟩ : syracuseStep 1833839 = 2750759) B2750759
theorem B9304955 : Blo 814346 9304955 := bstep (se 1 (by rfl) ⟨6978716, by rfl⟩ : syracuseStep 9304955 = 13957433) B13957433
theorem B1833983 : Blo 814346 1833983 := bstep (se 1 (by rfl) ⟨1375487, by rfl⟩ : syracuseStep 1833983 = 2750975) B2750975
theorem B818287 : Blo 814346 818287 := bstep (se 1 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 818287 = 1227431) B1227431
theorem B2751623 : Blo 814346 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B818343 : Blo 814346 818343 := bstep (se 1 (by rfl) ⟨613757, by rfl⟩ : syracuseStep 818343 = 1227515) B1227515
theorem B1375609 : Blo 814346 1375609 := bstep (se 2 (by rfl) ⟨515853, by rfl⟩ : syracuseStep 1375609 = 1031707) B1031707
theorem B1473913 : Blo 814346 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B28343675 : Blo 814346 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B1375643 : Blo 814346 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B1835063 : Blo 814346 1835063 := bstep (se 1 (by rfl) ⟨1376297, by rfl⟩ : syracuseStep 1835063 = 2752595) B2752595
theorem B2097215 : Blo 814346 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B917671 : Blo 814346 917671 := bstep (se 1 (by rfl) ⟨688253, by rfl⟩ : syracuseStep 917671 = 1376507) B1376507
theorem B2753243 : Blo 814346 2753243 := bstep (se 1 (by rfl) ⟨2064932, by rfl⟩ : syracuseStep 2753243 = 4129865) B4129865
theorem B33588215 : Blo 814346 33588215 := bstep (se 1 (by rfl) ⟨25191161, by rfl⟩ : syracuseStep 33588215 = 50382323) B50382323
theorem B2065895 : Blo 814346 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B2360935 : Blo 814346 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B1837511 : Blo 814346 1837511 := bstep (se 1 (by rfl) ⟨1378133, by rfl⟩ : syracuseStep 1837511 = 2756267) B2756267
theorem B6982271 : Blo 814346 6982271 := bstep (se 1 (by rfl) ⟨5236703, by rfl⟩ : syracuseStep 6982271 = 10473407) B10473407
theorem B4656761 : Blo 814346 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2068193 : Blo 814346 2068193 := bstep (se 2 (by rfl) ⟨775572, by rfl⟩ : syracuseStep 2068193 = 1551145) B1551145
theorem B8818429 : Blo 814346 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B1838879 : Blo 814346 1838879 := bstep (se 1 (by rfl) ⟨1379159, by rfl⟩ : syracuseStep 1838879 = 2758319) B2758319
theorem B26808245 : Blo 814346 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B1839131 : Blo 814346 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B2069459 : Blo 814346 2069459 := bstep (se 1 (by rfl) ⟨1552094, by rfl⟩ : syracuseStep 2069459 = 3104189) B3104189
theorem B1840121 : Blo 814346 1840121 := bstep (se 2 (by rfl) ⟨690045, by rfl⟩ : syracuseStep 1840121 = 1380091) B1380091
theorem B1742561 : Blo 814346 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B429202577 : Blo 814346 429202577 := bstep (se 2 (by rfl) ⟨160950966, by rfl⟩ : syracuseStep 429202577 = 321901933) B321901933
theorem B1744031 : Blo 814346 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B11771513 : Blo 814346 11771513 := bstep (se 2 (by rfl) ⟨4414317, by rfl⟩ : syracuseStep 11771513 = 8828635) B8828635
theorem B8822495 : Blo 814346 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B2236223 : Blo 814346 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B153134317 : Blo 814346 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B1222199 : Blo 814346 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B1222235 : Blo 814346 1222235 := bstep (se 1 (by rfl) ⟨916676, by rfl⟩ : syracuseStep 1222235 = 1833353) B1833353
theorem B1222559 : Blo 814346 1222559 := bstep (se 1 (by rfl) ⟨916919, by rfl⟩ : syracuseStep 1222559 = 1833839) B1833839
theorem B6203303 : Blo 814346 6203303 := bstep (se 1 (by rfl) ⟨4652477, by rfl⟩ : syracuseStep 6203303 = 9304955) B9304955
theorem B1222655 : Blo 814346 1222655 := bstep (se 1 (by rfl) ⟨916991, by rfl⟩ : syracuseStep 1222655 = 1833983) B1833983
theorem B4139423 : Blo 814346 4139423 := bstep (se 1 (by rfl) ⟨3104567, by rfl⟩ : syracuseStep 4139423 = 6209135) B6209135
theorem B1223387 : Blo 814346 1223387 := bstep (se 1 (by rfl) ⟨917540, by rfl⟩ : syracuseStep 1223387 = 1835081) B1835081
theorem B1223771 : Blo 814346 1223771 := bstep (se 1 (by rfl) ⟨917828, by rfl⟩ : syracuseStep 1223771 = 1835657) B1835657
theorem B1224143 : Blo 814346 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B31797785 : Blo 814346 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B1226207 : Blo 814346 1226207 := bstep (se 1 (by rfl) ⟨919655, by rfl⟩ : syracuseStep 1226207 = 1839311) B1839311
theorem B9943073 : Blo 814346 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B1227257 : Blo 814346 1227257 := bstep (se 2 (by rfl) ⟨460221, by rfl⟩ : syracuseStep 1227257 = 920443) B920443
theorem B4406687 : Blo 814346 4406687 := bstep (se 1 (by rfl) ⟨3305015, by rfl⟩ : syracuseStep 4406687 = 6610031) B6610031
theorem B3915611 : Blo 814346 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B119160881 : Blo 814346 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B1032527 : Blo 814346 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B13944311 : Blo 814346 13944311 := bstep (se 1 (by rfl) ⟨10458233, by rfl⟩ : syracuseStep 13944311 = 20916467) B20916467
theorem B3983849 : Blo 814346 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B47730329 : Blo 814346 47730329 := bstep (se 2 (by rfl) ⟨17898873, by rfl⟩ : syracuseStep 47730329 = 35797747) B35797747
theorem B29085497 : Blo 814346 29085497 := bstep (se 2 (by rfl) ⟨10907061, by rfl⟩ : syracuseStep 29085497 = 21814123) B21814123
theorem B18895783 : Blo 814346 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B4641725 : Blo 814346 4641725 := bstep (se 3 (by rfl) ⟨870323, by rfl⟩ : syracuseStep 4641725 = 1740647) B1740647
theorem B2479187 : Blo 814346 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B5888123 : Blo 814346 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B2645405 : Blo 814346 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B10477097 : Blo 814346 10477097 := bstep (se 2 (by rfl) ⟨3928911, by rfl⟩ : syracuseStep 10477097 = 7857823) B7857823
theorem B178380467 : Blo 814346 178380467 := bstep (se 1 (by rfl) ⟨133785350, by rfl⟩ : syracuseStep 178380467 = 267570701) B267570701
theorem B100425743 : Blo 814346 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B814399 : Blo 814346 814399 := bstep (se 1 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 814399 = 1221599) B1221599
theorem B7433947 : Blo 814346 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B761687813 : Blo 814346 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B814951 : Blo 814346 814951 := bstep (se 1 (by rfl) ⟨611213, by rfl⟩ : syracuseStep 814951 = 1222427) B1222427
theorem B815551 : Blo 814346 815551 := bstep (se 1 (by rfl) ⟨611663, by rfl⟩ : syracuseStep 815551 = 1223327) B1223327
theorem B7860671 : Blo 814346 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B815643 : Blo 814346 815643 := bstep (se 1 (by rfl) ⟨611732, by rfl⟩ : syracuseStep 815643 = 1223465) B1223465
theorem B815855 : Blo 814346 815855 := bstep (se 1 (by rfl) ⟨611891, by rfl⟩ : syracuseStep 815855 = 1223783) B1223783
theorem B816219 : Blo 814346 816219 := bstep (se 1 (by rfl) ⟨612164, by rfl⟩ : syracuseStep 816219 = 1224329) B1224329
theorem B39646331 : Blo 814346 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B816383 : Blo 814346 816383 := bstep (se 1 (by rfl) ⟨612287, by rfl⟩ : syracuseStep 816383 = 1224575) B1224575
theorem B816411 : Blo 814346 816411 := bstep (se 1 (by rfl) ⟨612308, by rfl⟩ : syracuseStep 816411 = 1224617) B1224617
theorem B1963649 : Blo 814346 1963649 := bstep (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) B1472737
theorem B1832723 : Blo 814346 1832723 := bstep (se 1 (by rfl) ⟨1374542, by rfl⟩ : syracuseStep 1832723 = 2749085) B2749085
theorem B818239 : Blo 814346 818239 := bstep (se 1 (by rfl) ⟨613679, by rfl⟩ : syracuseStep 818239 = 1227359) B1227359
theorem B1834145 : Blo 814346 1834145 := bstep (se 2 (by rfl) ⟨687804, by rfl⟩ : syracuseStep 1834145 = 1375609) B1375609
theorem B1965217 : Blo 814346 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1834415 : Blo 814346 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B917095 : Blo 814346 917095 := bstep (se 1 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 917095 = 1375643) B1375643
theorem B1835495 : Blo 814346 1835495 := bstep (se 1 (by rfl) ⟨1376621, by rfl⟩ : syracuseStep 1835495 = 2753243) B2753243
theorem B2753405 : Blo 814346 2753405 := bstep (se 3 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 2753405 = 1032527) B1032527
theorem B1377263 : Blo 814346 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B2655899 : Blo 814346 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B4654847 : Blo 814346 4654847 := bstep (se 1 (by rfl) ⟨3491135, by rfl⟩ : syracuseStep 4654847 = 6982271) B6982271
theorem B3147913 : Blo 814346 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B31820219 : Blo 814346 31820219 := bstep (se 1 (by rfl) ⟨23865164, by rfl⟩ : syracuseStep 31820219 = 47730329) B47730329
theorem B1378795 : Blo 814346 1378795 := bstep (se 1 (by rfl) ⟨1034096, by rfl⟩ : syracuseStep 1378795 = 2068193) B2068193
theorem B1379639 : Blo 814346 1379639 := bstep (se 1 (by rfl) ⟨1034729, by rfl⟩ : syracuseStep 1379639 = 2069459) B2069459
theorem B6984731 : Blo 814346 6984731 := bstep (se 1 (by rfl) ⟨5238548, by rfl⟩ : syracuseStep 6984731 = 10477097) B10477097
theorem B118920311 : Blo 814346 118920311 := bstep (se 1 (by rfl) ⟨89190233, by rfl⟩ : syracuseStep 118920311 = 178380467) B178380467
theorem B66950495 : Blo 814346 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B816716357 : Blo 814346 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B4135535 : Blo 814346 4135535 := bstep (se 1 (by rfl) ⟨3101651, by rfl⟩ : syracuseStep 4135535 = 6203303) B6203303
theorem B2759615 : Blo 814346 2759615 := bstep (se 1 (by rfl) ⟨2069711, by rfl⟩ : syracuseStep 2759615 = 4139423) B4139423
theorem B1221815 : Blo 814346 1221815 := bstep (se 1 (by rfl) ⟨916361, by rfl⟩ : syracuseStep 1221815 = 1832723) B1832723
theorem B6628715 : Blo 814346 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B1222763 : Blo 814346 1222763 := bstep (se 1 (by rfl) ⟨917072, by rfl⟩ : syracuseStep 1222763 = 1834145) B1834145
theorem B1222793 : Blo 814346 1222793 := bstep (se 2 (by rfl) ⟨458547, by rfl⟩ : syracuseStep 1222793 = 917095) B917095
theorem B1222943 : Blo 814346 1222943 := bstep (se 1 (by rfl) ⟨917207, by rfl⟩ : syracuseStep 1222943 = 1834415) B1834415
theorem B79440587 : Blo 814346 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B1223375 : Blo 814346 1223375 := bstep (se 1 (by rfl) ⟨917531, by rfl⟩ : syracuseStep 1223375 = 1835063) B1835063
theorem B1223561 : Blo 814346 1223561 := bstep (se 2 (by rfl) ⟨458835, by rfl⟩ : syracuseStep 1223561 = 917671) B917671
theorem B22392143 : Blo 814346 22392143 := bstep (se 1 (by rfl) ⟨16794107, by rfl⟩ : syracuseStep 22392143 = 33588215) B33588215
theorem B1225007 : Blo 814346 1225007 := bstep (se 1 (by rfl) ⟨918755, by rfl⟩ : syracuseStep 1225007 = 1837511) B1837511
theorem B1225919 : Blo 814346 1225919 := bstep (se 1 (by rfl) ⟨919439, by rfl⟩ : syracuseStep 1225919 = 1838879) B1838879
theorem B17872163 : Blo 814346 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B1226087 : Blo 814346 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B3094483 : Blo 814346 3094483 := bstep (se 1 (by rfl) ⟨2320862, by rfl⟩ : syracuseStep 3094483 = 4641725) B4641725
theorem B1226747 : Blo 814346 1226747 := bstep (se 1 (by rfl) ⟨920060, by rfl⟩ : syracuseStep 1226747 = 1840121) B1840121
theorem B1161707 : Blo 814346 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B1162687 : Blo 814346 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B9911929 : Blo 814346 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B7847675 : Blo 814346 7847675 := bstep (se 1 (by rfl) ⟨5885756, by rfl⟩ : syracuseStep 7847675 = 11771513) B11771513
theorem B5881663 : Blo 814346 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B1490815 : Blo 814346 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B507791875 : Blo 814346 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B1144540205 : Blo 814346 1144540205 := bstep (se 3 (by rfl) ⟨214601288, by rfl⟩ : syracuseStep 1144540205 = 429202577) B429202577
theorem B26430887 : Blo 814346 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B2937791 : Blo 814346 2937791 := bstep (se 1 (by rfl) ⟨2203343, by rfl⟩ : syracuseStep 2937791 = 4406687) B4406687
theorem B2610407 : Blo 814346 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B1398143 : Blo 814346 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B9296207 : Blo 814346 9296207 := bstep (se 1 (by rfl) ⟨6972155, by rfl⟩ : syracuseStep 9296207 = 13944311) B13944311
theorem B3104507 : Blo 814346 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B19390331 : Blo 814346 19390331 := bstep (se 1 (by rfl) ⟨14542748, by rfl⟩ : syracuseStep 19390331 = 29085497) B29085497
theorem B6611165 : Blo 814346 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B3925415 : Blo 814346 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B5236397 : Blo 814346 5236397 := bstep (se 3 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 5236397 = 1963649) B1963649
theorem B1763603 : Blo 814346 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B11757905 : Blo 814346 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B814799 : Blo 814346 814799 := bstep (se 1 (by rfl) ⟨611099, by rfl⟩ : syracuseStep 814799 = 1222199) B1222199
theorem B814823 : Blo 814346 814823 := bstep (se 1 (by rfl) ⟨611117, by rfl⟩ : syracuseStep 814823 = 1222235) B1222235
theorem B25194377 : Blo 814346 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B815039 : Blo 814346 815039 := bstep (se 1 (by rfl) ⟨611279, by rfl⟩ : syracuseStep 815039 = 1222559) B1222559
theorem B815103 : Blo 814346 815103 := bstep (se 1 (by rfl) ⟨611327, by rfl⟩ : syracuseStep 815103 = 1222655) B1222655
theorem B815591 : Blo 814346 815591 := bstep (se 1 (by rfl) ⟨611693, by rfl⟩ : syracuseStep 815591 = 1223387) B1223387
theorem B815847 : Blo 814346 815847 := bstep (se 1 (by rfl) ⟨611885, by rfl⟩ : syracuseStep 815847 = 1223771) B1223771
theorem B816095 : Blo 814346 816095 := bstep (se 1 (by rfl) ⟨612071, by rfl⟩ : syracuseStep 816095 = 1224143) B1224143
theorem B5240447 : Blo 814346 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B21198523 : Blo 814346 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B817471 : Blo 814346 817471 := bstep (se 1 (by rfl) ⟨613103, by rfl⟩ : syracuseStep 817471 = 1226207) B1226207
theorem B2620289 : Blo 814346 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B818171 : Blo 814346 818171 := bstep (se 1 (by rfl) ⟨613628, by rfl⟩ : syracuseStep 818171 = 1227257) B1227257
theorem B1835603 : Blo 814346 1835603 := bstep (se 1 (by rfl) ⟨1376702, by rfl⟩ : syracuseStep 1835603 = 2753405) B2753405
theorem B918175 : Blo 814346 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B1770599 : Blo 814346 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B919759 : Blo 814346 919759 := bstep (se 1 (by rfl) ⟨689819, by rfl⟩ : syracuseStep 919759 = 1379639) B1379639
theorem B4197217 : Blo 814346 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B1838393 : Blo 814346 1838393 := bstep (se 2 (by rfl) ⟨689397, by rfl⟩ : syracuseStep 1838393 = 1378795) B1378795
theorem B677055833 : Blo 814346 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B4656487 : Blo 814346 4656487 := bstep (se 1 (by rfl) ⟨3492365, by rfl⟩ : syracuseStep 4656487 = 6984731) B6984731
theorem B44633663 : Blo 814346 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B6197471 : Blo 814346 6197471 := bstep (se 1 (by rfl) ⟨4648103, by rfl⟩ : syracuseStep 6197471 = 9296207) B9296207
theorem B544477571 : Blo 814346 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B2757023 : Blo 814346 2757023 := bstep (se 1 (by rfl) ⟨2067767, by rfl⟩ : syracuseStep 2757023 = 4135535) B4135535
theorem B1839743 : Blo 814346 1839743 := bstep (se 1 (by rfl) ⟨1379807, by rfl⟩ : syracuseStep 1839743 = 2759615) B2759615
theorem B2069671 : Blo 814346 2069671 := bstep (se 1 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 2069671 = 3104507) B3104507
theorem B7838603 : Blo 814346 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B52960391 : Blo 814346 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B1550249 : Blo 814346 1550249 := bstep (se 2 (by rfl) ⟨581343, by rfl⟩ : syracuseStep 1550249 = 1162687) B1162687
theorem B1746859 : Blo 814346 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B13215905 : Blo 814346 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B7842217 : Blo 814346 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1223663 : Blo 814346 1223663 := bstep (se 1 (by rfl) ⟨917747, by rfl⟩ : syracuseStep 1223663 = 1835495) B1835495
theorem B21213479 : Blo 814346 21213479 := bstep (se 1 (by rfl) ⟨15910109, by rfl⟩ : syracuseStep 21213479 = 31820219) B31820219
theorem B6961085 : Blo 814346 6961085 := bstep (se 3 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 6961085 = 2610407) B2610407
theorem B79280207 : Blo 814346 79280207 := bstep (se 1 (by rfl) ⟨59460155, by rfl⟩ : syracuseStep 79280207 = 118920311) B118920311
theorem B932095 : Blo 814346 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B4407443 : Blo 814346 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B3490931 : Blo 814346 3490931 := bstep (se 1 (by rfl) ⟨2618198, by rfl⟩ : syracuseStep 3490931 = 5236397) B5236397
theorem B3097885 : Blo 814346 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B14928095 : Blo 814346 14928095 := bstep (se 1 (by rfl) ⟨11196071, by rfl⟩ : syracuseStep 14928095 = 22392143) B22392143
theorem B28264697 : Blo 814346 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B16796251 : Blo 814346 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B11914775 : Blo 814346 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B3493631 : Blo 814346 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B5231783 : Blo 814346 5231783 := bstep (se 1 (by rfl) ⟨3923837, by rfl⟩ : syracuseStep 5231783 = 7847675) B7847675
theorem B1987753 : Blo 814346 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B3103231 : Blo 814346 3103231 := bstep (se 1 (by rfl) ⟨2327423, by rfl⟩ : syracuseStep 3103231 = 4654847) B4654847
theorem B763026803 : Blo 814346 763026803 := bstep (se 1 (by rfl) ⟨572270102, by rfl⟩ : syracuseStep 763026803 = 1144540205) B1144540205
theorem B17620591 : Blo 814346 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B1958527 : Blo 814346 1958527 := bstep (se 1 (by rfl) ⟨1468895, by rfl⟩ : syracuseStep 1958527 = 2937791) B2937791
theorem B814543 : Blo 814346 814543 := bstep (se 1 (by rfl) ⟨610907, by rfl⟩ : syracuseStep 814543 = 1221815) B1221815
theorem B4419143 : Blo 814346 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B2616943 : Blo 814346 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B815175 : Blo 814346 815175 := bstep (se 1 (by rfl) ⟨611381, by rfl⟩ : syracuseStep 815175 = 1222763) B1222763
theorem B815195 : Blo 814346 815195 := bstep (se 1 (by rfl) ⟨611396, by rfl⟩ : syracuseStep 815195 = 1222793) B1222793
theorem B1175735 : Blo 814346 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B815295 : Blo 814346 815295 := bstep (se 1 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 815295 = 1222943) B1222943
theorem B815583 : Blo 814346 815583 := bstep (se 1 (by rfl) ⟨611687, by rfl⟩ : syracuseStep 815583 = 1223375) B1223375
theorem B815707 : Blo 814346 815707 := bstep (se 1 (by rfl) ⟨611780, by rfl⟩ : syracuseStep 815707 = 1223561) B1223561
theorem B4125977 : Blo 814346 4125977 := bstep (se 2 (by rfl) ⟨1547241, by rfl⟩ : syracuseStep 4125977 = 3094483) B3094483
theorem B816671 : Blo 814346 816671 := bstep (se 1 (by rfl) ⟨612503, by rfl⟩ : syracuseStep 816671 = 1225007) B1225007
theorem B817279 : Blo 814346 817279 := bstep (se 1 (by rfl) ⟨612959, by rfl⟩ : syracuseStep 817279 = 1225919) B1225919
theorem B817391 : Blo 814346 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B817831 : Blo 814346 817831 := bstep (se 1 (by rfl) ⟨613373, by rfl⟩ : syracuseStep 817831 = 1226747) B1226747
theorem B51707549 : Blo 814346 51707549 := bstep (se 3 (by rfl) ⟨9695165, by rfl⟩ : syracuseStep 51707549 = 19390331) B19390331
theorem B2327287 : Blo 814346 2327287 := bstep (se 1 (by rfl) ⟨1745465, by rfl⟩ : syracuseStep 2327287 = 3490931) B3490931
theorem B18843131 : Blo 814346 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B4130513 : Blo 814346 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B29755775 : Blo 814346 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B2329087 : Blo 814346 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B2329145 : Blo 814346 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B4131647 : Blo 814346 4131647 := bstep (se 1 (by rfl) ⟨3098735, by rfl⟩ : syracuseStep 4131647 = 6197471) B6197471
theorem B4721597 : Blo 814346 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B1838015 : Blo 814346 1838015 := bstep (se 1 (by rfl) ⟨1378511, by rfl⟩ : syracuseStep 1838015 = 2757023) B2757023
theorem B10456289 : Blo 814346 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B2759561 : Blo 814346 2759561 := bstep (se 2 (by rfl) ⟨1034835, by rfl⟩ : syracuseStep 2759561 = 2069671) B2069671
theorem B4137641 : Blo 814346 4137641 := bstep (se 2 (by rfl) ⟨1551615, by rfl⟩ : syracuseStep 4137641 = 3103231) B3103231
theorem B1223735 : Blo 814346 1223735 := bstep (se 1 (by rfl) ⟨917801, by rfl⟩ : syracuseStep 1223735 = 1835603) B1835603
theorem B1224233 : Blo 814346 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B1225595 : Blo 814346 1225595 := bstep (se 1 (by rfl) ⟨919196, by rfl⟩ : syracuseStep 1225595 = 1838393) B1838393
theorem B7943183 : Blo 814346 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B362985047 : Blo 814346 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1226345 : Blo 814346 1226345 := bstep (se 2 (by rfl) ⟨459879, by rfl⟩ : syracuseStep 1226345 = 919759) B919759
theorem B1226495 : Blo 814346 1226495 := bstep (se 1 (by rfl) ⟨919871, by rfl⟩ : syracuseStep 1226495 = 1839743) B1839743
theorem B3487855 : Blo 814346 3487855 := bstep (se 1 (by rfl) ⟨2615891, by rfl⟩ : syracuseStep 3487855 = 5231783) B5231783
theorem B22395001 : Blo 814346 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B6208649 : Blo 814346 6208649 := bstep (se 2 (by rfl) ⟨2328243, by rfl⟩ : syracuseStep 6208649 = 4656487) B4656487
theorem B5225735 : Blo 814346 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B35306927 : Blo 814346 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B3489257 : Blo 814346 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B1033499 : Blo 814346 1033499 := bstep (se 1 (by rfl) ⟨775124, by rfl⟩ : syracuseStep 1033499 = 1550249) B1550249
theorem B14142319 : Blo 814346 14142319 := bstep (se 1 (by rfl) ⟨10606739, by rfl⟩ : syracuseStep 14142319 = 21213479) B21213479
theorem B4640723 : Blo 814346 4640723 := bstep (se 1 (by rfl) ⟨3480542, by rfl⟩ : syracuseStep 4640723 = 6961085) B6961085
theorem B2938295 : Blo 814346 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B3135293 : Blo 814346 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B2611369 : Blo 814346 2611369 := bstep (se 2 (by rfl) ⟨979263, by rfl⟩ : syracuseStep 2611369 = 1958527) B1958527
theorem B451370555 : Blo 814346 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B5596289 : Blo 814346 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B508684535 : Blo 814346 508684535 := bstep (se 1 (by rfl) ⟨381513401, by rfl⟩ : syracuseStep 508684535 = 763026803) B763026803
theorem B39808253 : Blo 814346 39808253 := bstep (se 3 (by rfl) ⟨7464047, by rfl⟩ : syracuseStep 39808253 = 14928095) B14928095
theorem B8810603 : Blo 814346 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B2650337 : Blo 814346 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B815775 : Blo 814346 815775 := bstep (se 1 (by rfl) ⟨611831, by rfl⟩ : syracuseStep 815775 = 1223663) B1223663
theorem B2946095 : Blo 814346 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B1242793 : Blo 814346 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B2750651 : Blo 814346 2750651 := bstep (se 1 (by rfl) ⟨2062988, by rfl⟩ : syracuseStep 2750651 = 4125977) B4125977
theorem B52853471 : Blo 814346 52853471 := bstep (se 1 (by rfl) ⟨39640103, by rfl⟩ : syracuseStep 52853471 = 79280207) B79280207
theorem B23494121 : Blo 814346 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B34471699 : Blo 814346 34471699 := bstep (se 1 (by rfl) ⟨25853774, by rfl⟩ : syracuseStep 34471699 = 51707549) B51707549
theorem B2753675 : Blo 814346 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B2754431 : Blo 814346 2754431 := bstep (se 1 (by rfl) ⟨2065823, by rfl⟩ : syracuseStep 2754431 = 4131647) B4131647
theorem B3147731 : Blo 814346 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2755997 : Blo 814346 2755997 := bstep (se 3 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 2755997 = 1033499) B1033499
theorem B7835453 : Blo 814346 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B1839707 : Blo 814346 1839707 := bstep (se 1 (by rfl) ⟨1379780, by rfl⟩ : syracuseStep 1839707 = 2759561) B2759561
theorem B300913703 : Blo 814346 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B2758427 : Blo 814346 2758427 := bstep (se 1 (by rfl) ⟨2068820, by rfl⟩ : syracuseStep 2758427 = 4137641) B4137641
theorem B339123023 : Blo 814346 339123023 := bstep (se 1 (by rfl) ⟨254342267, by rfl⟩ : syracuseStep 339123023 = 508684535) B508684535
theorem B5873735 : Blo 814346 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B29860001 : Blo 814346 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B3481825 : Blo 814346 3481825 := bstep (se 2 (by rfl) ⟨1305684, by rfl⟩ : syracuseStep 3481825 = 2611369) B2611369
theorem B6628229 : Blo 814346 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B35235647 : Blo 814346 35235647 := bstep (se 1 (by rfl) ⟨26426735, by rfl⟩ : syracuseStep 35235647 = 52853471) B52853471
theorem B4139099 : Blo 814346 4139099 := bstep (se 1 (by rfl) ⟨3104324, by rfl⟩ : syracuseStep 4139099 = 6208649) B6208649
theorem B3483823 : Blo 814346 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B23537951 : Blo 814346 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B12562087 : Blo 814346 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B19837183 : Blo 814346 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B1552763 : Blo 814346 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B1225343 : Blo 814346 1225343 := bstep (se 1 (by rfl) ⟨919007, by rfl⟩ : syracuseStep 1225343 = 1838015) B1838015
theorem B3093815 : Blo 814346 3093815 := bstep (se 1 (by rfl) ⟨2320361, by rfl⟩ : syracuseStep 3093815 = 4640723) B4640723
theorem B5295455 : Blo 814346 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B183849061 : Blo 814346 183849061 := bstep (se 4 (by rfl) ⟨17235849, by rfl⟩ : syracuseStep 183849061 = 34471699) B34471699
theorem B3103049 : Blo 814346 3103049 := bstep (se 2 (by rfl) ⟨1163643, by rfl⟩ : syracuseStep 3103049 = 2327287) B2327287
theorem B6970859 : Blo 814346 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B3105449 : Blo 814346 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B2090195 : Blo 814346 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B75425701 : Blo 814346 75425701 := bstep (se 4 (by rfl) ⟨7071159, by rfl⟩ : syracuseStep 75425701 = 14142319) B14142319
theorem B3730859 : Blo 814346 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B815823 : Blo 814346 815823 := bstep (se 1 (by rfl) ⟨611867, by rfl⟩ : syracuseStep 815823 = 1223735) B1223735
theorem B26538835 : Blo 814346 26538835 := bstep (se 1 (by rfl) ⟨19904126, by rfl⟩ : syracuseStep 26538835 = 39808253) B39808253
theorem B816155 : Blo 814346 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B4650473 : Blo 814346 4650473 := bstep (se 2 (by rfl) ⟨1743927, by rfl⟩ : syracuseStep 4650473 = 3487855) B3487855
theorem B1766891 : Blo 814346 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B817063 : Blo 814346 817063 := bstep (se 1 (by rfl) ⟨612797, by rfl⟩ : syracuseStep 817063 = 1225595) B1225595
theorem B1964063 : Blo 814346 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B241990031 : Blo 814346 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B817563 : Blo 814346 817563 := bstep (se 1 (by rfl) ⟨613172, by rfl⟩ : syracuseStep 817563 = 1226345) B1226345
theorem B817663 : Blo 814346 817663 := bstep (se 1 (by rfl) ⟨613247, by rfl⟩ : syracuseStep 817663 = 1226495) B1226495
theorem B1833767 : Blo 814346 1833767 := bstep (se 1 (by rfl) ⟨1375325, by rfl⟩ : syracuseStep 1833767 = 2750651) B2750651
theorem B15662747 : Blo 814346 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B2326171 : Blo 814346 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B15663293 : Blo 814346 15663293 := bstep (se 3 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 15663293 = 5873735) B5873735
theorem B1835783 : Blo 814346 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B1836287 : Blo 814346 1836287 := bstep (se 1 (by rfl) ⟨1377215, by rfl⟩ : syracuseStep 1836287 = 2754431) B2754431
theorem B2098487 : Blo 814346 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1837331 : Blo 814346 1837331 := bstep (se 1 (by rfl) ⟨1377998, by rfl⟩ : syracuseStep 1837331 = 2755997) B2755997
theorem B100567601 : Blo 814346 100567601 := bstep (se 2 (by rfl) ⟨37712850, by rfl⟩ : syracuseStep 100567601 = 75425701) B75425701
theorem B200609135 : Blo 814346 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B1838951 : Blo 814346 1838951 := bstep (se 1 (by rfl) ⟨1379213, by rfl⟩ : syracuseStep 1838951 = 2758427) B2758427
theorem B2068699 : Blo 814346 2068699 := bstep (se 1 (by rfl) ⟨1551524, by rfl⟩ : syracuseStep 2068699 = 3103049) B3103049
theorem B16749449 : Blo 814346 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B26449577 : Blo 814346 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B2070299 : Blo 814346 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B2759399 : Blo 814346 2759399 := bstep (se 1 (by rfl) ⟨2069549, by rfl⟩ : syracuseStep 2759399 = 4139099) B4139099
theorem B161326687 : Blo 814346 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B1222511 : Blo 814346 1222511 := bstep (se 1 (by rfl) ⟨916883, by rfl⟩ : syracuseStep 1222511 = 1833767) B1833767
theorem B5223635 : Blo 814346 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B1226471 : Blo 814346 1226471 := bstep (se 1 (by rfl) ⟨919853, by rfl⟩ : syracuseStep 1226471 = 1839707) B1839707
theorem B226082015 : Blo 814346 226082015 := bstep (se 1 (by rfl) ⟨169561511, by rfl⟩ : syracuseStep 226082015 = 339123023) B339123023
theorem B19906667 : Blo 814346 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B1393463 : Blo 814346 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B1035175 : Blo 814346 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B3100315 : Blo 814346 3100315 := bstep (se 1 (by rfl) ⟨2325236, by rfl⟩ : syracuseStep 3100315 = 4650473) B4650473
theorem B3101561 : Blo 814346 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B10441831 : Blo 814346 10441831 := bstep (se 1 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 10441831 = 15662747) B15662747
theorem B4642433 : Blo 814346 4642433 := bstep (se 2 (by rfl) ⟨1740912, by rfl⟩ : syracuseStep 4642433 = 3481825) B3481825
theorem B3530303 : Blo 814346 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B4645097 : Blo 814346 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B4711709 : Blo 814346 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B4647239 : Blo 814346 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B245132081 : Blo 814346 245132081 := bstep (se 2 (by rfl) ⟨91924530, by rfl⟩ : syracuseStep 245132081 = 183849061) B183849061
theorem B4418819 : Blo 814346 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B35385113 : Blo 814346 35385113 := bstep (se 2 (by rfl) ⟨13269417, by rfl⟩ : syracuseStep 35385113 = 26538835) B26538835
theorem B23490431 : Blo 814346 23490431 := bstep (se 1 (by rfl) ⟨17617823, by rfl⟩ : syracuseStep 23490431 = 35235647) B35235647
theorem B15691967 : Blo 814346 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B2487239 : Blo 814346 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B816895 : Blo 814346 816895 := bstep (se 1 (by rfl) ⟨612671, by rfl⟩ : syracuseStep 816895 = 1225343) B1225343
theorem B2062543 : Blo 814346 2062543 := bstep (se 1 (by rfl) ⟨1546907, by rfl⟩ : syracuseStep 2062543 = 3093815) B3093815
theorem B1309375 : Blo 814346 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B13271111 : Blo 814346 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B67045067 : Blo 814346 67045067 := bstep (se 1 (by rfl) ⟨50283800, by rfl⟩ : syracuseStep 67045067 = 100567601) B100567601
theorem B2067707 : Blo 814346 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B6983333 : Blo 814346 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B17633051 : Blo 814346 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B1380199 : Blo 814346 1380199 := bstep (se 1 (by rfl) ⟨1035149, by rfl⟩ : syracuseStep 1380199 = 2070299) B2070299
theorem B1380233 : Blo 814346 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B1839599 : Blo 814346 1839599 := bstep (se 1 (by rfl) ⟨1379699, by rfl⟩ : syracuseStep 1839599 = 2759399) B2759399
theorem B4133753 : Blo 814346 4133753 := bstep (se 2 (by rfl) ⟨1550157, by rfl⟩ : syracuseStep 4133753 = 3100315) B3100315
theorem B2758265 : Blo 814346 2758265 := bstep (se 2 (by rfl) ⟨1034349, by rfl⟩ : syracuseStep 2758265 = 2068699) B2068699
theorem B163421387 : Blo 814346 163421387 := bstep (se 1 (by rfl) ⟨122566040, by rfl⟩ : syracuseStep 163421387 = 245132081) B245132081
theorem B10461311 : Blo 814346 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B3482423 : Blo 814346 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B1223855 : Blo 814346 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B928975 : Blo 814346 928975 := bstep (se 1 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 928975 = 1393463) B1393463
theorem B1224191 : Blo 814346 1224191 := bstep (se 1 (by rfl) ⟨918143, by rfl⟩ : syracuseStep 1224191 = 1836287) B1836287
theorem B1224887 : Blo 814346 1224887 := bstep (se 1 (by rfl) ⟨918665, by rfl⟩ : syracuseStep 1224887 = 1837331) B1837331
theorem B215102249 : Blo 814346 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B133739423 : Blo 814346 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B1225967 : Blo 814346 1225967 := bstep (se 1 (by rfl) ⟨919475, by rfl⟩ : syracuseStep 1225967 = 1838951) B1838951
theorem B12564557 : Blo 814346 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B3094955 : Blo 814346 3094955 := bstep (se 1 (by rfl) ⟨2321216, by rfl⟩ : syracuseStep 3094955 = 4642433) B4642433
theorem B3096731 : Blo 814346 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B3098159 : Blo 814346 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B1658159 : Blo 814346 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B150721343 : Blo 814346 150721343 := bstep (se 1 (by rfl) ⟨113041007, by rfl⟩ : syracuseStep 150721343 = 226082015) B226082015
theorem B10442195 : Blo 814346 10442195 := bstep (se 1 (by rfl) ⟨7831646, by rfl⟩ : syracuseStep 10442195 = 15663293) B15663293
theorem B11166299 : Blo 814346 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B5595965 : Blo 814346 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B2353535 : Blo 814346 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B815007 : Blo 814346 815007 := bstep (se 1 (by rfl) ⟨611255, by rfl⟩ : syracuseStep 815007 = 1222511) B1222511
theorem B13922441 : Blo 814346 13922441 := bstep (se 2 (by rfl) ⟨5220915, by rfl⟩ : syracuseStep 13922441 = 10441831) B10441831
theorem B2945879 : Blo 814346 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B23590075 : Blo 814346 23590075 := bstep (se 1 (by rfl) ⟨17692556, by rfl⟩ : syracuseStep 23590075 = 35385113) B35385113
theorem B15660287 : Blo 814346 15660287 := bstep (se 1 (by rfl) ⟨11745215, by rfl⟩ : syracuseStep 15660287 = 23490431) B23490431
theorem B2750057 : Blo 814346 2750057 := bstep (se 2 (by rfl) ⟨1031271, by rfl⟩ : syracuseStep 2750057 = 2062543) B2062543
theorem B817647 : Blo 814346 817647 := bstep (se 1 (by rfl) ⟨613235, by rfl⟩ : syracuseStep 817647 = 1226471) B1226471
theorem B8847407 : Blo 814346 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B2064487 : Blo 814346 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B2065439 : Blo 814346 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B44696711 : Blo 814346 44696711 := bstep (se 1 (by rfl) ⟨33522533, by rfl⟩ : syracuseStep 44696711 = 67045067) B67045067
theorem B1378471 : Blo 814346 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B4655555 : Blo 814346 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B920155 : Blo 814346 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B2755835 : Blo 814346 2755835 := bstep (se 1 (by rfl) ⟨2066876, by rfl⟩ : syracuseStep 2755835 = 4133753) B4133753
theorem B1838843 : Blo 814346 1838843 := bstep (se 1 (by rfl) ⟨1379132, by rfl⟩ : syracuseStep 1838843 = 2758265) B2758265
theorem B1840265 : Blo 814346 1840265 := bstep (se 2 (by rfl) ⟨690099, by rfl⟩ : syracuseStep 1840265 = 1380199) B1380199
theorem B7444199 : Blo 814346 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B9281627 : Blo 814346 9281627 := bstep (se 1 (by rfl) ⟨6961220, by rfl⟩ : syracuseStep 9281627 = 13922441) B13922441
theorem B143401499 : Blo 814346 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1226399 : Blo 814346 1226399 := bstep (se 1 (by rfl) ⟨919799, by rfl⟩ : syracuseStep 1226399 = 1839599) B1839599
theorem B100480895 : Blo 814346 100480895 := bstep (se 1 (by rfl) ⟨75360671, by rfl⟩ : syracuseStep 100480895 = 150721343) B150721343
theorem B6961463 : Blo 814346 6961463 := bstep (se 1 (by rfl) ⟨5221097, by rfl⟩ : syracuseStep 6961463 = 10442195) B10442195
theorem B10440191 : Blo 814346 10440191 := bstep (se 1 (by rfl) ⟨7830143, by rfl⟩ : syracuseStep 10440191 = 15660287) B15660287
theorem B8376371 : Blo 814346 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B1105439 : Blo 814346 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B11755367 : Blo 814346 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B1238633 : Blo 814346 1238633 := bstep (se 2 (by rfl) ⟨464487, by rfl⟩ : syracuseStep 1238633 = 928975) B928975
theorem B108947591 : Blo 814346 108947591 := bstep (se 1 (by rfl) ⟨81710693, by rfl⟩ : syracuseStep 108947591 = 163421387) B163421387
theorem B6974207 : Blo 814346 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B2321615 : Blo 814346 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B3730643 : Blo 814346 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B31453433 : Blo 814346 31453433 := bstep (se 2 (by rfl) ⟨11795037, by rfl⟩ : syracuseStep 31453433 = 23590075) B23590075
theorem B1569023 : Blo 814346 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B815903 : Blo 814346 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B816127 : Blo 814346 816127 := bstep (se 1 (by rfl) ⟨612095, by rfl⟩ : syracuseStep 816127 = 1224191) B1224191
theorem B816591 : Blo 814346 816591 := bstep (se 1 (by rfl) ⟨612443, by rfl⟩ : syracuseStep 816591 = 1224887) B1224887
theorem B1963919 : Blo 814346 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B89159615 : Blo 814346 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B817311 : Blo 814346 817311 := bstep (se 1 (by rfl) ⟨612983, by rfl⟩ : syracuseStep 817311 = 1225967) B1225967
theorem B1833371 : Blo 814346 1833371 := bstep (se 1 (by rfl) ⟨1375028, by rfl⟩ : syracuseStep 1833371 = 2750057) B2750057
theorem B2063303 : Blo 814346 2063303 := bstep (se 1 (by rfl) ⟨1547477, by rfl⟩ : syracuseStep 2063303 = 3094955) B3094955
theorem B5898271 : Blo 814346 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B2752649 : Blo 814346 2752649 := bstep (se 2 (by rfl) ⟨1032243, by rfl⟩ : syracuseStep 2752649 = 2064487) B2064487
theorem B1376959 : Blo 814346 1376959 := bstep (se 1 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 1376959 = 2065439) B2065439
theorem B1837223 : Blo 814346 1837223 := bstep (se 1 (by rfl) ⟨1377917, by rfl⟩ : syracuseStep 1837223 = 2755835) B2755835
theorem B1837961 : Blo 814346 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B7836911 : Blo 814346 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B825755 : Blo 814346 825755 := bstep (se 1 (by rfl) ⟨619316, by rfl⟩ : syracuseStep 825755 = 1238633) B1238633
theorem B1547743 : Blo 814346 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B66987263 : Blo 814346 66987263 := bstep (se 1 (by rfl) ⟨50240447, by rfl⟩ : syracuseStep 66987263 = 100480895) B100480895
theorem B1222247 : Blo 814346 1222247 := bstep (se 1 (by rfl) ⟨916685, by rfl⟩ : syracuseStep 1222247 = 1833371) B1833371
theorem B29797807 : Blo 814346 29797807 := bstep (se 1 (by rfl) ⟨22348355, by rfl⟩ : syracuseStep 29797807 = 44696711) B44696711
theorem B6960127 : Blo 814346 6960127 := bstep (se 1 (by rfl) ⟨5220095, by rfl⟩ : syracuseStep 6960127 = 10440191) B10440191
theorem B1225895 : Blo 814346 1225895 := bstep (se 1 (by rfl) ⟨919421, by rfl⟩ : syracuseStep 1225895 = 1838843) B1838843
theorem B5584247 : Blo 814346 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B1226843 : Blo 814346 1226843 := bstep (se 1 (by rfl) ⟨920132, by rfl⟩ : syracuseStep 1226843 = 1840265) B1840265
theorem B1226873 : Blo 814346 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B4962799 : Blo 814346 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B95600999 : Blo 814346 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B72631727 : Blo 814346 72631727 := bstep (se 1 (by rfl) ⟨54473795, by rfl⟩ : syracuseStep 72631727 = 108947591) B108947591
theorem B4640975 : Blo 814346 4640975 := bstep (se 1 (by rfl) ⟨3480731, by rfl⟩ : syracuseStep 4640975 = 6961463) B6961463
theorem B3103703 : Blo 814346 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B6187751 : Blo 814346 6187751 := bstep (se 1 (by rfl) ⟨4640813, by rfl⟩ : syracuseStep 6187751 = 9281627) B9281627
theorem B4649471 : Blo 814346 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B2487095 : Blo 814346 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B20968955 : Blo 814346 20968955 := bstep (se 1 (by rfl) ⟨15726716, by rfl⟩ : syracuseStep 20968955 = 31453433) B31453433
theorem B1046015 : Blo 814346 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B817599 : Blo 814346 817599 := bstep (se 1 (by rfl) ⟨613199, by rfl⟩ : syracuseStep 817599 = 1226399) B1226399
theorem B1309279 : Blo 814346 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B59439743 : Blo 814346 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B2947837 : Blo 814346 2947837 := bstep (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) B1105439
theorem B1375535 : Blo 814346 1375535 := bstep (se 1 (by rfl) ⟨1031651, by rfl⟩ : syracuseStep 1375535 = 2063303) B2063303
theorem B7864361 : Blo 814346 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B1835099 : Blo 814346 1835099 := bstep (se 1 (by rfl) ⟨1376324, by rfl⟩ : syracuseStep 1835099 = 2752649) B2752649
theorem B63733999 : Blo 814346 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B1835945 : Blo 814346 1835945 := bstep (se 2 (by rfl) ⟨688479, by rfl⟩ : syracuseStep 1835945 = 1376959) B1376959
theorem B2069135 : Blo 814346 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B2202013 : Blo 814346 2202013 := bstep (se 3 (by rfl) ⟨412877, by rfl⟩ : syracuseStep 2202013 = 825755) B825755
theorem B9280169 : Blo 814346 9280169 := bstep (se 2 (by rfl) ⟨3480063, by rfl⟩ : syracuseStep 9280169 = 6960127) B6960127
theorem B1745705 : Blo 814346 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B39626495 : Blo 814346 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B1224815 : Blo 814346 1224815 := bstep (se 1 (by rfl) ⟨918611, by rfl⟩ : syracuseStep 1224815 = 1837223) B1837223
theorem B1225307 : Blo 814346 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B3093983 : Blo 814346 3093983 := bstep (se 1 (by rfl) ⟨2320487, by rfl⟩ : syracuseStep 3093983 = 4640975) B4640975
theorem B5224607 : Blo 814346 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B39730409 : Blo 814346 39730409 := bstep (se 2 (by rfl) ⟨14898903, by rfl⟩ : syracuseStep 39730409 = 29797807) B29797807
theorem B3099647 : Blo 814346 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B1658063 : Blo 814346 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B3722831 : Blo 814346 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B13979303 : Blo 814346 13979303 := bstep (se 1 (by rfl) ⟨10484477, by rfl⟩ : syracuseStep 13979303 = 20968955) B20968955
theorem B48421151 : Blo 814346 48421151 := bstep (se 1 (by rfl) ⟨36315863, by rfl⟩ : syracuseStep 48421151 = 72631727) B72631727
theorem B44658175 : Blo 814346 44658175 := bstep (se 1 (by rfl) ⟨33493631, by rfl⟩ : syracuseStep 44658175 = 66987263) B66987263
theorem B814831 : Blo 814346 814831 := bstep (se 1 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 814831 = 1222247) B1222247
theorem B4125167 : Blo 814346 4125167 := bstep (se 1 (by rfl) ⟨3093875, by rfl⟩ : syracuseStep 4125167 = 6187751) B6187751
theorem B6617065 : Blo 814346 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B817263 : Blo 814346 817263 := bstep (se 1 (by rfl) ⟨612947, by rfl⟩ : syracuseStep 817263 = 1225895) B1225895
theorem B3930449 : Blo 814346 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B817895 : Blo 814346 817895 := bstep (se 1 (by rfl) ⟨613421, by rfl⟩ : syracuseStep 817895 = 1226843) B1226843
theorem B817915 : Blo 814346 817915 := bstep (se 1 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 817915 = 1226873) B1226873
theorem B2063657 : Blo 814346 2063657 := bstep (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) B1547743
theorem B917023 : Blo 814346 917023 := bstep (se 1 (by rfl) ⟨687767, by rfl⟩ : syracuseStep 917023 = 1375535) B1375535
theorem B44629973 : Blo 814346 44629973 := bstep (se 7 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 44629973 = 1046015) B1046015
theorem B5242907 : Blo 814346 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B2066431 : Blo 814346 2066431 := bstep (se 1 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 2066431 = 3099647) B3099647
theorem B1379423 : Blo 814346 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B32280767 : Blo 814346 32280767 := bstep (se 1 (by rfl) ⟨24210575, by rfl⟩ : syracuseStep 32280767 = 48421151) B48421151
theorem B59544233 : Blo 814346 59544233 := bstep (se 2 (by rfl) ⟨22329087, by rfl⟩ : syracuseStep 59544233 = 44658175) B44658175
theorem B26417663 : Blo 814346 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B8822753 : Blo 814346 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B3483071 : Blo 814346 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B1222697 : Blo 814346 1222697 := bstep (se 2 (by rfl) ⟨458511, by rfl⟩ : syracuseStep 1222697 = 917023) B917023
theorem B26486939 : Blo 814346 26486939 := bstep (se 1 (by rfl) ⟨19865204, by rfl⟩ : syracuseStep 26486939 = 39730409) B39730409
theorem B1223399 : Blo 814346 1223399 := bstep (se 1 (by rfl) ⟨917549, by rfl⟩ : syracuseStep 1223399 = 1835099) B1835099
theorem B84978665 : Blo 814346 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B1223963 : Blo 814346 1223963 := bstep (se 1 (by rfl) ⟨917972, by rfl⟩ : syracuseStep 1223963 = 1835945) B1835945
theorem B9319535 : Blo 814346 9319535 := bstep (se 1 (by rfl) ⟨6989651, by rfl⟩ : syracuseStep 9319535 = 13979303) B13979303
theorem B1163803 : Blo 814346 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B2936017 : Blo 814346 2936017 := bstep (se 2 (by rfl) ⟨1101006, by rfl⟩ : syracuseStep 2936017 = 2202013) B2202013
theorem B1105375 : Blo 814346 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B2481887 : Blo 814346 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B6186779 : Blo 814346 6186779 := bstep (se 1 (by rfl) ⟨4640084, by rfl⟩ : syracuseStep 6186779 = 9280169) B9280169
theorem B10481197 : Blo 814346 10481197 := bstep (se 3 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 10481197 = 3930449) B3930449
theorem B816543 : Blo 814346 816543 := bstep (se 1 (by rfl) ⟨612407, by rfl⟩ : syracuseStep 816543 = 1224815) B1224815
theorem B2750111 : Blo 814346 2750111 := bstep (se 1 (by rfl) ⟨2062583, by rfl⟩ : syracuseStep 2750111 = 4125167) B4125167
theorem B816871 : Blo 814346 816871 := bstep (se 1 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 816871 = 1225307) B1225307
theorem B2062655 : Blo 814346 2062655 := bstep (se 1 (by rfl) ⟨1546991, by rfl⟩ : syracuseStep 2062655 = 3093983) B3093983
theorem B1375771 : Blo 814346 1375771 := bstep (se 1 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 1375771 = 2063657) B2063657
theorem B29753315 : Blo 814346 29753315 := bstep (se 1 (by rfl) ⟨22314986, by rfl⟩ : syracuseStep 29753315 = 44629973) B44629973
theorem B919615 : Blo 814346 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B2755241 : Blo 814346 2755241 := bstep (se 2 (by rfl) ⟨1033215, by rfl⟩ : syracuseStep 2755241 = 2066431) B2066431
theorem B19835543 : Blo 814346 19835543 := bstep (se 1 (by rfl) ⟨14876657, by rfl⟩ : syracuseStep 19835543 = 29753315) B29753315
theorem B1551737 : Blo 814346 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B39696155 : Blo 814346 39696155 := bstep (se 1 (by rfl) ⟨29772116, by rfl⟩ : syracuseStep 39696155 = 59544233) B59544233
theorem B3914689 : Blo 814346 3914689 := bstep (se 2 (by rfl) ⟨1468008, by rfl⟩ : syracuseStep 3914689 = 2936017) B2936017
theorem B17611775 : Blo 814346 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B13974929 : Blo 814346 13974929 := bstep (se 2 (by rfl) ⟨5240598, by rfl⟩ : syracuseStep 13974929 = 10481197) B10481197
theorem B1654591 : Blo 814346 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B5881835 : Blo 814346 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B6213023 : Blo 814346 6213023 := bstep (se 1 (by rfl) ⟨4659767, by rfl⟩ : syracuseStep 6213023 = 9319535) B9319535
theorem B3495271 : Blo 814346 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B21520511 : Blo 814346 21520511 := bstep (se 1 (by rfl) ⟨16140383, by rfl⟩ : syracuseStep 21520511 = 32280767) B32280767
theorem B2322047 : Blo 814346 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B4124519 : Blo 814346 4124519 := bstep (se 1 (by rfl) ⟨3093389, by rfl⟩ : syracuseStep 4124519 = 6186779) B6186779
theorem B815131 : Blo 814346 815131 := bstep (se 1 (by rfl) ⟨611348, by rfl⟩ : syracuseStep 815131 = 1222697) B1222697
theorem B17657959 : Blo 814346 17657959 := bstep (se 1 (by rfl) ⟨13243469, by rfl⟩ : syracuseStep 17657959 = 26486939) B26486939
theorem B815599 : Blo 814346 815599 := bstep (se 1 (by rfl) ⟨611699, by rfl⟩ : syracuseStep 815599 = 1223399) B1223399
theorem B56652443 : Blo 814346 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B815975 : Blo 814346 815975 := bstep (se 1 (by rfl) ⟨611981, by rfl⟩ : syracuseStep 815975 = 1223963) B1223963
theorem B1833407 : Blo 814346 1833407 := bstep (se 1 (by rfl) ⟨1375055, by rfl⟩ : syracuseStep 1833407 = 2750111) B2750111
theorem B1375103 : Blo 814346 1375103 := bstep (se 1 (by rfl) ⟨1031327, by rfl⟩ : syracuseStep 1375103 = 2062655) B2062655
theorem B1473833 : Blo 814346 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B1834361 : Blo 814346 1834361 := bstep (se 2 (by rfl) ⟨687885, by rfl⟩ : syracuseStep 1834361 = 1375771) B1375771
theorem B1836827 : Blo 814346 1836827 := bstep (se 1 (by rfl) ⟨1377620, by rfl⟩ : syracuseStep 1836827 = 2755241) B2755241
theorem B4660361 : Blo 814346 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B4137965 : Blo 814346 4137965 := bstep (se 3 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 4137965 = 1551737) B1551737
theorem B5219585 : Blo 814346 5219585 := bstep (se 2 (by rfl) ⟨1957344, by rfl⟩ : syracuseStep 5219585 = 3914689) B3914689
theorem B1222271 : Blo 814346 1222271 := bstep (se 1 (by rfl) ⟨916703, by rfl⟩ : syracuseStep 1222271 = 1833407) B1833407
theorem B11741183 : Blo 814346 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B1222907 : Blo 814346 1222907 := bstep (se 1 (by rfl) ⟨917180, by rfl⟩ : syracuseStep 1222907 = 1834361) B1834361
theorem B9316619 : Blo 814346 9316619 := bstep (se 1 (by rfl) ⟨6987464, by rfl⟩ : syracuseStep 9316619 = 13974929) B13974929
theorem B2206121 : Blo 814346 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B4142015 : Blo 814346 4142015 := bstep (se 1 (by rfl) ⟨3106511, by rfl⟩ : syracuseStep 4142015 = 6213023) B6213023
theorem B1226153 : Blo 814346 1226153 := bstep (se 2 (by rfl) ⟨459807, by rfl⟩ : syracuseStep 1226153 = 919615) B919615
theorem B23543945 : Blo 814346 23543945 := bstep (se 2 (by rfl) ⟨8828979, by rfl⟩ : syracuseStep 23543945 = 17657959) B17657959
theorem B13223695 : Blo 814346 13223695 := bstep (se 1 (by rfl) ⟨9917771, by rfl⟩ : syracuseStep 13223695 = 19835543) B19835543
theorem B37768295 : Blo 814346 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B26464103 : Blo 814346 26464103 := bstep (se 1 (by rfl) ⟨19848077, by rfl⟩ : syracuseStep 26464103 = 39696155) B39696155
theorem B3921223 : Blo 814346 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B14347007 : Blo 814346 14347007 := bstep (se 1 (by rfl) ⟨10760255, by rfl⟩ : syracuseStep 14347007 = 21520511) B21520511
theorem B2749679 : Blo 814346 2749679 := bstep (se 1 (by rfl) ⟨2062259, by rfl⟩ : syracuseStep 2749679 = 4124519) B4124519
theorem B3930221 : Blo 814346 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B6192125 : Blo 814346 6192125 := bstep (se 3 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 6192125 = 2322047) B2322047
theorem B916735 : Blo 814346 916735 := bstep (se 1 (by rfl) ⟨687551, by rfl⟩ : syracuseStep 916735 = 1375103) B1375103
theorem B15695963 : Blo 814346 15695963 := bstep (se 1 (by rfl) ⟨11771972, by rfl⟩ : syracuseStep 15695963 = 23543945) B23543945
theorem B17631593 : Blo 814346 17631593 := bstep (se 2 (by rfl) ⟨6611847, by rfl⟩ : syracuseStep 17631593 = 13223695) B13223695
theorem B2758643 : Blo 814346 2758643 := bstep (se 1 (by rfl) ⟨2068982, by rfl⟩ : syracuseStep 2758643 = 4137965) B4137965
theorem B3479723 : Blo 814346 3479723 := bstep (se 1 (by rfl) ⟨2609792, by rfl⟩ : syracuseStep 3479723 = 5219585) B5219585
theorem B2761343 : Blo 814346 2761343 := bstep (se 1 (by rfl) ⟨2071007, by rfl⟩ : syracuseStep 2761343 = 4142015) B4142015
theorem B1222313 : Blo 814346 1222313 := bstep (se 2 (by rfl) ⟨458367, by rfl⟩ : syracuseStep 1222313 = 916735) B916735
theorem B1224551 : Blo 814346 1224551 := bstep (se 1 (by rfl) ⟨918413, by rfl⟩ : syracuseStep 1224551 = 1836827) B1836827
theorem B25178863 : Blo 814346 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B17642735 : Blo 814346 17642735 := bstep (se 1 (by rfl) ⟨13232051, by rfl⟩ : syracuseStep 17642735 = 26464103) B26464103
theorem B5882989 : Blo 814346 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B6211079 : Blo 814346 6211079 := bstep (se 1 (by rfl) ⟨4658309, by rfl⟩ : syracuseStep 6211079 = 9316619) B9316619
theorem B5228297 : Blo 814346 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B3106907 : Blo 814346 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B814847 : Blo 814346 814847 := bstep (se 1 (by rfl) ⟨611135, by rfl⟩ : syracuseStep 814847 = 1222271) B1222271
theorem B7827455 : Blo 814346 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B815271 : Blo 814346 815271 := bstep (se 1 (by rfl) ⟨611453, by rfl⟩ : syracuseStep 815271 = 1222907) B1222907
theorem B9564671 : Blo 814346 9564671 := bstep (se 1 (by rfl) ⟨7173503, by rfl⟩ : syracuseStep 9564671 = 14347007) B14347007
theorem B1833119 : Blo 814346 1833119 := bstep (se 1 (by rfl) ⟨1374839, by rfl⟩ : syracuseStep 1833119 = 2749679) B2749679
theorem B817435 : Blo 814346 817435 := bstep (se 1 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 817435 = 1226153) B1226153
theorem B2620147 : Blo 814346 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B4128083 : Blo 814346 4128083 := bstep (se 1 (by rfl) ⟨3096062, by rfl⟩ : syracuseStep 4128083 = 6192125) B6192125
theorem B1839095 : Blo 814346 1839095 := bstep (se 1 (by rfl) ⟨1379321, by rfl⟩ : syracuseStep 1839095 = 2758643) B2758643
theorem B1840895 : Blo 814346 1840895 := bstep (se 1 (by rfl) ⟨1380671, by rfl⟩ : syracuseStep 1840895 = 2761343) B2761343
theorem B2071271 : Blo 814346 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B5218303 : Blo 814346 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B1222079 : Blo 814346 1222079 := bstep (se 1 (by rfl) ⟨916559, by rfl⟩ : syracuseStep 1222079 = 1833119) B1833119
theorem B10463975 : Blo 814346 10463975 := bstep (se 1 (by rfl) ⟨7847981, by rfl⟩ : syracuseStep 10463975 = 15695963) B15695963
theorem B4140719 : Blo 814346 4140719 := bstep (se 1 (by rfl) ⟨3105539, by rfl⟩ : syracuseStep 4140719 = 6211079) B6211079
theorem B3485531 : Blo 814346 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B7843985 : Blo 814346 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B33571817 : Blo 814346 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B6376447 : Blo 814346 6376447 := bstep (se 1 (by rfl) ⟨4782335, by rfl⟩ : syracuseStep 6376447 = 9564671) B9564671
theorem B3493529 : Blo 814346 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B11754395 : Blo 814346 11754395 := bstep (se 1 (by rfl) ⟨8815796, by rfl⟩ : syracuseStep 11754395 = 17631593) B17631593
theorem B2319815 : Blo 814346 2319815 := bstep (se 1 (by rfl) ⟨1739861, by rfl⟩ : syracuseStep 2319815 = 3479723) B3479723
theorem B814875 : Blo 814346 814875 := bstep (se 1 (by rfl) ⟨611156, by rfl⟩ : syracuseStep 814875 = 1222313) B1222313
theorem B816367 : Blo 814346 816367 := bstep (se 1 (by rfl) ⟨612275, by rfl⟩ : syracuseStep 816367 = 1224551) B1224551
theorem B11761823 : Blo 814346 11761823 := bstep (se 1 (by rfl) ⟨8821367, by rfl⟩ : syracuseStep 11761823 = 17642735) B17642735
theorem B2752055 : Blo 814346 2752055 := bstep (se 1 (by rfl) ⟨2064041, by rfl⟩ : syracuseStep 2752055 = 4128083) B4128083
theorem B22381211 : Blo 814346 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B2329019 : Blo 814346 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B1380847 : Blo 814346 1380847 := bstep (se 1 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 1380847 = 2071271) B2071271
theorem B7836263 : Blo 814346 7836263 := bstep (se 1 (by rfl) ⟨5877197, by rfl⟩ : syracuseStep 7836263 = 11754395) B11754395
theorem B1546543 : Blo 814346 1546543 := bstep (se 1 (by rfl) ⟨1159907, by rfl⟩ : syracuseStep 1546543 = 2319815) B2319815
theorem B2760479 : Blo 814346 2760479 := bstep (se 1 (by rfl) ⟨2070359, by rfl⟩ : syracuseStep 2760479 = 4140719) B4140719
theorem B7841215 : Blo 814346 7841215 := bstep (se 1 (by rfl) ⟨5880911, by rfl⟩ : syracuseStep 7841215 = 11761823) B11761823
theorem B6957737 : Blo 814346 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B1226063 : Blo 814346 1226063 := bstep (se 1 (by rfl) ⟨919547, by rfl⟩ : syracuseStep 1226063 = 1839095) B1839095
theorem B1227263 : Blo 814346 1227263 := bstep (se 1 (by rfl) ⟨920447, by rfl⟩ : syracuseStep 1227263 = 1840895) B1840895
theorem B8501929 : Blo 814346 8501929 := bstep (se 2 (by rfl) ⟨3188223, by rfl⟩ : syracuseStep 8501929 = 6376447) B6376447
theorem B5229323 : Blo 814346 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B9294749 : Blo 814346 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B814719 : Blo 814346 814719 := bstep (se 1 (by rfl) ⟨611039, by rfl⟩ : syracuseStep 814719 = 1222079) B1222079
theorem B6975983 : Blo 814346 6975983 := bstep (se 1 (by rfl) ⟨5231987, by rfl⟩ : syracuseStep 6975983 = 10463975) B10463975
theorem B1834703 : Blo 814346 1834703 := bstep (se 1 (by rfl) ⟨1376027, by rfl⟩ : syracuseStep 1834703 = 2752055) B2752055
theorem B10454953 : Blo 814346 10454953 := bstep (se 2 (by rfl) ⟨3920607, by rfl⟩ : syracuseStep 10454953 = 7841215) B7841215
theorem B6196499 : Blo 814346 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B1840319 : Blo 814346 1840319 := bstep (se 1 (by rfl) ⟨1380239, by rfl⟩ : syracuseStep 1840319 = 2760479) B2760479
theorem B1841129 : Blo 814346 1841129 := bstep (se 2 (by rfl) ⟨690423, by rfl⟩ : syracuseStep 1841129 = 1380847) B1380847
theorem B1223135 : Blo 814346 1223135 := bstep (se 1 (by rfl) ⟨917351, by rfl⟩ : syracuseStep 1223135 = 1834703) B1834703
theorem B14920807 : Blo 814346 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B1552679 : Blo 814346 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B3486215 : Blo 814346 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B5224175 : Blo 814346 5224175 := bstep (se 1 (by rfl) ⟨3918131, by rfl⟩ : syracuseStep 5224175 = 7836263) B7836263
theorem B4638491 : Blo 814346 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B45343621 : Blo 814346 45343621 := bstep (se 4 (by rfl) ⟨4250964, by rfl⟩ : syracuseStep 45343621 = 8501929) B8501929
theorem B4650655 : Blo 814346 4650655 := bstep (se 1 (by rfl) ⟨3487991, by rfl⟩ : syracuseStep 4650655 = 6975983) B6975983
theorem B2062057 : Blo 814346 2062057 := bstep (se 2 (by rfl) ⟨773271, by rfl⟩ : syracuseStep 2062057 = 1546543) B1546543
theorem B817375 : Blo 814346 817375 := bstep (se 1 (by rfl) ⟨613031, by rfl⟩ : syracuseStep 817375 = 1226063) B1226063
theorem B818175 : Blo 814346 818175 := bstep (se 1 (by rfl) ⟨613631, by rfl⟩ : syracuseStep 818175 = 1227263) B1227263
theorem B60458161 : Blo 814346 60458161 := bstep (se 2 (by rfl) ⟨22671810, by rfl⟩ : syracuseStep 60458161 = 45343621) B45343621
theorem B4130999 : Blo 814346 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B19894409 : Blo 814346 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B6200873 : Blo 814346 6200873 := bstep (se 2 (by rfl) ⟨2325327, by rfl⟩ : syracuseStep 6200873 = 4650655) B4650655
theorem B3482783 : Blo 814346 3482783 := bstep (se 1 (by rfl) ⟨2612087, by rfl⟩ : syracuseStep 3482783 = 5224175) B5224175
theorem B3092327 : Blo 814346 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B13939937 : Blo 814346 13939937 := bstep (se 2 (by rfl) ⟨5227476, by rfl⟩ : syracuseStep 13939937 = 10454953) B10454953
theorem B1226879 : Blo 814346 1226879 := bstep (se 1 (by rfl) ⟨920159, by rfl⟩ : syracuseStep 1226879 = 1840319) B1840319
theorem B1227419 : Blo 814346 1227419 := bstep (se 1 (by rfl) ⟨920564, by rfl⟩ : syracuseStep 1227419 = 1841129) B1841129
theorem B1035119 : Blo 814346 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B815423 : Blo 814346 815423 := bstep (se 1 (by rfl) ⟨611567, by rfl⟩ : syracuseStep 815423 = 1223135) B1223135
theorem B2749409 : Blo 814346 2749409 := bstep (se 2 (by rfl) ⟨1031028, by rfl⟩ : syracuseStep 2749409 = 2062057) B2062057
theorem B2324143 : Blo 814346 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B2753999 : Blo 814346 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B80610881 : Blo 814346 80610881 := bstep (se 2 (by rfl) ⟨30229080, by rfl⟩ : syracuseStep 80610881 = 60458161) B60458161
theorem B4133915 : Blo 814346 4133915 := bstep (se 1 (by rfl) ⟨3100436, by rfl⟩ : syracuseStep 4133915 = 6200873) B6200873
theorem B2760317 : Blo 814346 2760317 := bstep (se 3 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 2760317 = 1035119) B1035119
theorem B3098857 : Blo 814346 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B9293291 : Blo 814346 9293291 := bstep (se 1 (by rfl) ⟨6969968, by rfl⟩ : syracuseStep 9293291 = 13939937) B13939937
theorem B13262939 : Blo 814346 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B2321855 : Blo 814346 2321855 := bstep (se 1 (by rfl) ⟨1741391, by rfl⟩ : syracuseStep 2321855 = 3482783) B3482783
theorem B2061551 : Blo 814346 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B1832939 : Blo 814346 1832939 := bstep (se 1 (by rfl) ⟨1374704, by rfl⟩ : syracuseStep 1832939 = 2749409) B2749409
theorem B817919 : Blo 814346 817919 := bstep (se 1 (by rfl) ⟨613439, by rfl⟩ : syracuseStep 817919 = 1226879) B1226879
theorem B818279 : Blo 814346 818279 := bstep (se 1 (by rfl) ⟨613709, by rfl⟩ : syracuseStep 818279 = 1227419) B1227419
theorem B1835999 : Blo 814346 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B6195527 : Blo 814346 6195527 := bstep (se 1 (by rfl) ⟨4646645, by rfl⟩ : syracuseStep 6195527 = 9293291) B9293291
theorem B4131809 : Blo 814346 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B2755943 : Blo 814346 2755943 := bstep (se 1 (by rfl) ⟨2066957, by rfl⟩ : syracuseStep 2755943 = 4133915) B4133915
theorem B214962349 : Blo 814346 214962349 := bstep (se 3 (by rfl) ⟨40305440, by rfl⟩ : syracuseStep 214962349 = 80610881) B80610881
theorem B1840211 : Blo 814346 1840211 := bstep (se 1 (by rfl) ⟨1380158, by rfl⟩ : syracuseStep 1840211 = 2760317) B2760317
theorem B1547903 : Blo 814346 1547903 := bstep (se 1 (by rfl) ⟨1160927, by rfl⟩ : syracuseStep 1547903 = 2321855) B2321855
theorem B1221959 : Blo 814346 1221959 := bstep (se 1 (by rfl) ⟨916469, by rfl⟩ : syracuseStep 1221959 = 1832939) B1832939
theorem B8841959 : Blo 814346 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B1374367 : Blo 814346 1374367 := bstep (se 1 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 1374367 = 2061551) B2061551
theorem B4130351 : Blo 814346 4130351 := bstep (se 1 (by rfl) ⟨3097763, by rfl⟩ : syracuseStep 4130351 = 6195527) B6195527
theorem B2754539 : Blo 814346 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B1837295 : Blo 814346 1837295 := bstep (se 1 (by rfl) ⟨1377971, by rfl⟩ : syracuseStep 1837295 = 2755943) B2755943
theorem B1223999 : Blo 814346 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B1226807 : Blo 814346 1226807 := bstep (se 1 (by rfl) ⟨920105, by rfl⟩ : syracuseStep 1226807 = 1840211) B1840211
theorem B1031935 : Blo 814346 1031935 := bstep (se 1 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 1031935 = 1547903) B1547903
theorem B286616465 : Blo 814346 286616465 := bstep (se 2 (by rfl) ⟨107481174, by rfl⟩ : syracuseStep 286616465 = 214962349) B214962349
theorem B814639 : Blo 814346 814639 := bstep (se 1 (by rfl) ⟨610979, by rfl⟩ : syracuseStep 814639 = 1221959) B1221959
theorem B5894639 : Blo 814346 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B1832489 : Blo 814346 1832489 := bstep (se 2 (by rfl) ⟨687183, by rfl⟩ : syracuseStep 1832489 = 1374367) B1374367
theorem B2753567 : Blo 814346 2753567 := bstep (se 1 (by rfl) ⟨2065175, by rfl⟩ : syracuseStep 2753567 = 4130351) B4130351
theorem B1836359 : Blo 814346 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B191077643 : Blo 814346 191077643 := bstep (se 1 (by rfl) ⟨143308232, by rfl⟩ : syracuseStep 191077643 = 286616465) B286616465
theorem B1221659 : Blo 814346 1221659 := bstep (se 1 (by rfl) ⟨916244, by rfl⟩ : syracuseStep 1221659 = 1832489) B1832489
theorem B1224863 : Blo 814346 1224863 := bstep (se 1 (by rfl) ⟨918647, by rfl⟩ : syracuseStep 1224863 = 1837295) B1837295
theorem B815999 : Blo 814346 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B3929759 : Blo 814346 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B817871 : Blo 814346 817871 := bstep (se 1 (by rfl) ⟨613403, by rfl⟩ : syracuseStep 817871 = 1226807) B1226807
theorem B1375913 : Blo 814346 1375913 := bstep (se 2 (by rfl) ⟨515967, by rfl⟩ : syracuseStep 1375913 = 1031935) B1031935
theorem B1835711 : Blo 814346 1835711 := bstep (se 1 (by rfl) ⟨1376783, by rfl⟩ : syracuseStep 1835711 = 2753567) B2753567
theorem B1224239 : Blo 814346 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B127385095 : Blo 814346 127385095 := bstep (se 1 (by rfl) ⟨95538821, by rfl⟩ : syracuseStep 127385095 = 191077643) B191077643
theorem B814439 : Blo 814346 814439 := bstep (se 1 (by rfl) ⟨610829, by rfl⟩ : syracuseStep 814439 = 1221659) B1221659
theorem B816575 : Blo 814346 816575 := bstep (se 1 (by rfl) ⟨612431, by rfl⟩ : syracuseStep 816575 = 1224863) B1224863
theorem B2619839 : Blo 814346 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B917275 : Blo 814346 917275 := bstep (se 1 (by rfl) ⟨687956, by rfl⟩ : syracuseStep 917275 = 1375913) B1375913
theorem B1746559 : Blo 814346 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B169846793 : Blo 814346 169846793 := bstep (se 2 (by rfl) ⟨63692547, by rfl⟩ : syracuseStep 169846793 = 127385095) B127385095
theorem B1223033 : Blo 814346 1223033 := bstep (se 2 (by rfl) ⟨458637, by rfl⟩ : syracuseStep 1223033 = 917275) B917275
theorem B1223807 : Blo 814346 1223807 := bstep (se 1 (by rfl) ⟨917855, by rfl⟩ : syracuseStep 1223807 = 1835711) B1835711
theorem B816159 : Blo 814346 816159 := bstep (se 1 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 816159 = 1224239) B1224239
theorem B2328745 : Blo 814346 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B113231195 : Blo 814346 113231195 := bstep (se 1 (by rfl) ⟨84923396, by rfl⟩ : syracuseStep 113231195 = 169846793) B169846793
theorem B815355 : Blo 814346 815355 := bstep (se 1 (by rfl) ⟨611516, by rfl⟩ : syracuseStep 815355 = 1223033) B1223033
theorem B815871 : Blo 814346 815871 := bstep (se 1 (by rfl) ⟨611903, by rfl⟩ : syracuseStep 815871 = 1223807) B1223807
theorem B75487463 : Blo 814346 75487463 := bstep (se 1 (by rfl) ⟨56615597, by rfl⟩ : syracuseStep 75487463 = 113231195) B113231195
theorem B3104993 : Blo 814346 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B2069995 : Blo 814346 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B50324975 : Blo 814346 50324975 := bstep (se 1 (by rfl) ⟨37743731, by rfl⟩ : syracuseStep 50324975 = 75487463) B75487463
theorem B2759993 : Blo 814346 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B33549983 : Blo 814346 33549983 := bstep (se 1 (by rfl) ⟨25162487, by rfl⟩ : syracuseStep 33549983 = 50324975) B50324975
theorem B1839995 : Blo 814346 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B22366655 : Blo 814346 22366655 := bstep (se 1 (by rfl) ⟨16774991, by rfl⟩ : syracuseStep 22366655 = 33549983) B33549983
theorem B14911103 : Blo 814346 14911103 := bstep (se 1 (by rfl) ⟨11183327, by rfl⟩ : syracuseStep 14911103 = 22366655) B22366655
theorem B1226663 : Blo 814346 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B9940735 : Blo 814346 9940735 := bstep (se 1 (by rfl) ⟨7455551, by rfl⟩ : syracuseStep 9940735 = 14911103) B14911103
theorem B817775 : Blo 814346 817775 := bstep (se 1 (by rfl) ⟨613331, by rfl⟩ : syracuseStep 817775 = 1226663) B1226663
theorem B13254313 : Blo 814346 13254313 := bstep (se 2 (by rfl) ⟨4970367, by rfl⟩ : syracuseStep 13254313 = 9940735) B9940735
theorem B17672417 : Blo 814346 17672417 := bstep (se 2 (by rfl) ⟨6627156, by rfl⟩ : syracuseStep 17672417 = 13254313) B13254313
theorem B11781611 : Blo 814346 11781611 := bstep (se 1 (by rfl) ⟨8836208, by rfl⟩ : syracuseStep 11781611 = 17672417) B17672417
theorem B7854407 : Blo 814346 7854407 := bstep (se 1 (by rfl) ⟨5890805, by rfl⟩ : syracuseStep 7854407 = 11781611) B11781611
theorem B5236271 : Blo 814346 5236271 := bstep (se 1 (by rfl) ⟨3927203, by rfl⟩ : syracuseStep 5236271 = 7854407) B7854407
theorem B3490847 : Blo 814346 3490847 := bstep (se 1 (by rfl) ⟨2618135, by rfl⟩ : syracuseStep 3490847 = 5236271) B5236271
theorem B2327231 : Blo 814346 2327231 := bstep (se 1 (by rfl) ⟨1745423, by rfl⟩ : syracuseStep 2327231 = 3490847) B3490847
theorem B1551487 : Blo 814346 1551487 := bstep (se 1 (by rfl) ⟨1163615, by rfl⟩ : syracuseStep 1551487 = 2327231) B2327231
theorem B2068649 : Blo 814346 2068649 := bstep (se 2 (by rfl) ⟨775743, by rfl⟩ : syracuseStep 2068649 = 1551487) B1551487
theorem B1379099 : Blo 814346 1379099 := bstep (se 1 (by rfl) ⟨1034324, by rfl⟩ : syracuseStep 1379099 = 2068649) B2068649
theorem B919399 : Blo 814346 919399 := bstep (se 1 (by rfl) ⟨689549, by rfl⟩ : syracuseStep 919399 = 1379099) B1379099
theorem B1225865 : Blo 814346 1225865 := bstep (se 2 (by rfl) ⟨459699, by rfl⟩ : syracuseStep 1225865 = 919399) B919399
theorem B817243 : Blo 814346 817243 := bstep (se 1 (by rfl) ⟨612932, by rfl⟩ : syracuseStep 817243 = 1225865) B1225865

theorem C0 (j : ℕ) (h1 : 203586 ≤ j) (h2 : j ≤ 204285) : Blo 814346 (4 * j + 3) := by
  interval_cases j
  · exact B814347
  · exact B814351
  · exact B814355
  · exact B814359
  · exact B814363
  · exact B814367
  · exact B814371
  · exact B814375
  · exact B814379
  · exact B814383
  · exact B814387
  · exact B814391
  · exact B814395
  · exact B814399
  · exact B814403
  · exact B814407
  · exact B814411
  · exact B814415
  · exact B814419
  · exact B814423
  · exact B814427
  · exact B814431
  · exact B814435
  · exact B814439
  · exact B814443
  · exact B814447
  · exact B814451
  · exact B814455
  · exact B814459
  · exact B814463
  · exact B814467
  · exact B814471
  · exact B814475
  · exact B814479
  · exact B814483
  · exact B814487
  · exact B814491
  · exact B814495
  · exact B814499
  · exact B814503
  · exact B814507
  · exact B814511
  · exact B814515
  · exact B814519
  · exact B814523
  · exact B814527
  · exact B814531
  · exact B814535
  · exact B814539
  · exact B814543
  · exact B814547
  · exact B814551
  · exact B814555
  · exact B814559
  · exact B814563
  · exact B814567
  · exact B814571
  · exact B814575
  · exact B814579
  · exact B814583
  · exact B814587
  · exact B814591
  · exact B814595
  · exact B814599
  · exact B814603
  · exact B814607
  · exact B814611
  · exact B814615
  · exact B814619
  · exact B814623
  · exact B814627
  · exact B814631
  · exact B814635
  · exact B814639
  · exact B814643
  · exact B814647
  · exact B814651
  · exact B814655
  · exact B814659
  · exact B814663
  · exact B814667
  · exact B814671
  · exact B814675
  · exact B814679
  · exact B814683
  · exact B814687
  · exact B814691
  · exact B814695
  · exact B814699
  · exact B814703
  · exact B814707
  · exact B814711
  · exact B814715
  · exact B814719
  · exact B814723
  · exact B814727
  · exact B814731
  · exact B814735
  · exact B814739
  · exact B814743
  · exact B814747
  · exact B814751
  · exact B814755
  · exact B814759
  · exact B814763
  · exact B814767
  · exact B814771
  · exact B814775
  · exact B814779
  · exact B814783
  · exact B814787
  · exact B814791
  · exact B814795
  · exact B814799
  · exact B814803
  · exact B814807
  · exact B814811
  · exact B814815
  · exact B814819
  · exact B814823
  · exact B814827
  · exact B814831
  · exact B814835
  · exact B814839
  · exact B814843
  · exact B814847
  · exact B814851
  · exact B814855
  · exact B814859
  · exact B814863
  · exact B814867
  · exact B814871
  · exact B814875
  · exact B814879
  · exact B814883
  · exact B814887
  · exact B814891
  · exact B814895
  · exact B814899
  · exact B814903
  · exact B814907
  · exact B814911
  · exact B814915
  · exact B814919
  · exact B814923
  · exact B814927
  · exact B814931
  · exact B814935
  · exact B814939
  · exact B814943
  · exact B814947
  · exact B814951
  · exact B814955
  · exact B814959
  · exact B814963
  · exact B814967
  · exact B814971
  · exact B814975
  · exact B814979
  · exact B814983
  · exact B814987
  · exact B814991
  · exact B814995
  · exact B814999
  · exact B815003
  · exact B815007
  · exact B815011
  · exact B815015
  · exact B815019
  · exact B815023
  · exact B815027
  · exact B815031
  · exact B815035
  · exact B815039
  · exact B815043
  · exact B815047
  · exact B815051
  · exact B815055
  · exact B815059
  · exact B815063
  · exact B815067
  · exact B815071
  · exact B815075
  · exact B815079
  · exact B815083
  · exact B815087
  · exact B815091
  · exact B815095
  · exact B815099
  · exact B815103
  · exact B815107
  · exact B815111
  · exact B815115
  · exact B815119
  · exact B815123
  · exact B815127
  · exact B815131
  · exact B815135
  · exact B815139
  · exact B815143
  · exact B815147
  · exact B815151
  · exact B815155
  · exact B815159
  · exact B815163
  · exact B815167
  · exact B815171
  · exact B815175
  · exact B815179
  · exact B815183
  · exact B815187
  · exact B815191
  · exact B815195
  · exact B815199
  · exact B815203
  · exact B815207
  · exact B815211
  · exact B815215
  · exact B815219
  · exact B815223
  · exact B815227
  · exact B815231
  · exact B815235
  · exact B815239
  · exact B815243
  · exact B815247
  · exact B815251
  · exact B815255
  · exact B815259
  · exact B815263
  · exact B815267
  · exact B815271
  · exact B815275
  · exact B815279
  · exact B815283
  · exact B815287
  · exact B815291
  · exact B815295
  · exact B815299
  · exact B815303
  · exact B815307
  · exact B815311
  · exact B815315
  · exact B815319
  · exact B815323
  · exact B815327
  · exact B815331
  · exact B815335
  · exact B815339
  · exact B815343
  · exact B815347
  · exact B815351
  · exact B815355
  · exact B815359
  · exact B815363
  · exact B815367
  · exact B815371
  · exact B815375
  · exact B815379
  · exact B815383
  · exact B815387
  · exact B815391
  · exact B815395
  · exact B815399
  · exact B815403
  · exact B815407
  · exact B815411
  · exact B815415
  · exact B815419
  · exact B815423
  · exact B815427
  · exact B815431
  · exact B815435
  · exact B815439
  · exact B815443
  · exact B815447
  · exact B815451
  · exact B815455
  · exact B815459
  · exact B815463
  · exact B815467
  · exact B815471
  · exact B815475
  · exact B815479
  · exact B815483
  · exact B815487
  · exact B815491
  · exact B815495
  · exact B815499
  · exact B815503
  · exact B815507
  · exact B815511
  · exact B815515
  · exact B815519
  · exact B815523
  · exact B815527
  · exact B815531
  · exact B815535
  · exact B815539
  · exact B815543
  · exact B815547
  · exact B815551
  · exact B815555
  · exact B815559
  · exact B815563
  · exact B815567
  · exact B815571
  · exact B815575
  · exact B815579
  · exact B815583
  · exact B815587
  · exact B815591
  · exact B815595
  · exact B815599
  · exact B815603
  · exact B815607
  · exact B815611
  · exact B815615
  · exact B815619
  · exact B815623
  · exact B815627
  · exact B815631
  · exact B815635
  · exact B815639
  · exact B815643
  · exact B815647
  · exact B815651
  · exact B815655
  · exact B815659
  · exact B815663
  · exact B815667
  · exact B815671
  · exact B815675
  · exact B815679
  · exact B815683
  · exact B815687
  · exact B815691
  · exact B815695
  · exact B815699
  · exact B815703
  · exact B815707
  · exact B815711
  · exact B815715
  · exact B815719
  · exact B815723
  · exact B815727
  · exact B815731
  · exact B815735
  · exact B815739
  · exact B815743
  · exact B815747
  · exact B815751
  · exact B815755
  · exact B815759
  · exact B815763
  · exact B815767
  · exact B815771
  · exact B815775
  · exact B815779
  · exact B815783
  · exact B815787
  · exact B815791
  · exact B815795
  · exact B815799
  · exact B815803
  · exact B815807
  · exact B815811
  · exact B815815
  · exact B815819
  · exact B815823
  · exact B815827
  · exact B815831
  · exact B815835
  · exact B815839
  · exact B815843
  · exact B815847
  · exact B815851
  · exact B815855
  · exact B815859
  · exact B815863
  · exact B815867
  · exact B815871
  · exact B815875
  · exact B815879
  · exact B815883
  · exact B815887
  · exact B815891
  · exact B815895
  · exact B815899
  · exact B815903
  · exact B815907
  · exact B815911
  · exact B815915
  · exact B815919
  · exact B815923
  · exact B815927
  · exact B815931
  · exact B815935
  · exact B815939
  · exact B815943
  · exact B815947
  · exact B815951
  · exact B815955
  · exact B815959
  · exact B815963
  · exact B815967
  · exact B815971
  · exact B815975
  · exact B815979
  · exact B815983
  · exact B815987
  · exact B815991
  · exact B815995
  · exact B815999
  · exact B816003
  · exact B816007
  · exact B816011
  · exact B816015
  · exact B816019
  · exact B816023
  · exact B816027
  · exact B816031
  · exact B816035
  · exact B816039
  · exact B816043
  · exact B816047
  · exact B816051
  · exact B816055
  · exact B816059
  · exact B816063
  · exact B816067
  · exact B816071
  · exact B816075
  · exact B816079
  · exact B816083
  · exact B816087
  · exact B816091
  · exact B816095
  · exact B816099
  · exact B816103
  · exact B816107
  · exact B816111
  · exact B816115
  · exact B816119
  · exact B816123
  · exact B816127
  · exact B816131
  · exact B816135
  · exact B816139
  · exact B816143
  · exact B816147
  · exact B816151
  · exact B816155
  · exact B816159
  · exact B816163
  · exact B816167
  · exact B816171
  · exact B816175
  · exact B816179
  · exact B816183
  · exact B816187
  · exact B816191
  · exact B816195
  · exact B816199
  · exact B816203
  · exact B816207
  · exact B816211
  · exact B816215
  · exact B816219
  · exact B816223
  · exact B816227
  · exact B816231
  · exact B816235
  · exact B816239
  · exact B816243
  · exact B816247
  · exact B816251
  · exact B816255
  · exact B816259
  · exact B816263
  · exact B816267
  · exact B816271
  · exact B816275
  · exact B816279
  · exact B816283
  · exact B816287
  · exact B816291
  · exact B816295
  · exact B816299
  · exact B816303
  · exact B816307
  · exact B816311
  · exact B816315
  · exact B816319
  · exact B816323
  · exact B816327
  · exact B816331
  · exact B816335
  · exact B816339
  · exact B816343
  · exact B816347
  · exact B816351
  · exact B816355
  · exact B816359
  · exact B816363
  · exact B816367
  · exact B816371
  · exact B816375
  · exact B816379
  · exact B816383
  · exact B816387
  · exact B816391
  · exact B816395
  · exact B816399
  · exact B816403
  · exact B816407
  · exact B816411
  · exact B816415
  · exact B816419
  · exact B816423
  · exact B816427
  · exact B816431
  · exact B816435
  · exact B816439
  · exact B816443
  · exact B816447
  · exact B816451
  · exact B816455
  · exact B816459
  · exact B816463
  · exact B816467
  · exact B816471
  · exact B816475
  · exact B816479
  · exact B816483
  · exact B816487
  · exact B816491
  · exact B816495
  · exact B816499
  · exact B816503
  · exact B816507
  · exact B816511
  · exact B816515
  · exact B816519
  · exact B816523
  · exact B816527
  · exact B816531
  · exact B816535
  · exact B816539
  · exact B816543
  · exact B816547
  · exact B816551
  · exact B816555
  · exact B816559
  · exact B816563
  · exact B816567
  · exact B816571
  · exact B816575
  · exact B816579
  · exact B816583
  · exact B816587
  · exact B816591
  · exact B816595
  · exact B816599
  · exact B816603
  · exact B816607
  · exact B816611
  · exact B816615
  · exact B816619
  · exact B816623
  · exact B816627
  · exact B816631
  · exact B816635
  · exact B816639
  · exact B816643
  · exact B816647
  · exact B816651
  · exact B816655
  · exact B816659
  · exact B816663
  · exact B816667
  · exact B816671
  · exact B816675
  · exact B816679
  · exact B816683
  · exact B816687
  · exact B816691
  · exact B816695
  · exact B816699
  · exact B816703
  · exact B816707
  · exact B816711
  · exact B816715
  · exact B816719
  · exact B816723
  · exact B816727
  · exact B816731
  · exact B816735
  · exact B816739
  · exact B816743
  · exact B816747
  · exact B816751
  · exact B816755
  · exact B816759
  · exact B816763
  · exact B816767
  · exact B816771
  · exact B816775
  · exact B816779
  · exact B816783
  · exact B816787
  · exact B816791
  · exact B816795
  · exact B816799
  · exact B816803
  · exact B816807
  · exact B816811
  · exact B816815
  · exact B816819
  · exact B816823
  · exact B816827
  · exact B816831
  · exact B816835
  · exact B816839
  · exact B816843
  · exact B816847
  · exact B816851
  · exact B816855
  · exact B816859
  · exact B816863
  · exact B816867
  · exact B816871
  · exact B816875
  · exact B816879
  · exact B816883
  · exact B816887
  · exact B816891
  · exact B816895
  · exact B816899
  · exact B816903
  · exact B816907
  · exact B816911
  · exact B816915
  · exact B816919
  · exact B816923
  · exact B816927
  · exact B816931
  · exact B816935
  · exact B816939
  · exact B816943
  · exact B816947
  · exact B816951
  · exact B816955
  · exact B816959
  · exact B816963
  · exact B816967
  · exact B816971
  · exact B816975
  · exact B816979
  · exact B816983
  · exact B816987
  · exact B816991
  · exact B816995
  · exact B816999
  · exact B817003
  · exact B817007
  · exact B817011
  · exact B817015
  · exact B817019
  · exact B817023
  · exact B817027
  · exact B817031
  · exact B817035
  · exact B817039
  · exact B817043
  · exact B817047
  · exact B817051
  · exact B817055
  · exact B817059
  · exact B817063
  · exact B817067
  · exact B817071
  · exact B817075
  · exact B817079
  · exact B817083
  · exact B817087
  · exact B817091
  · exact B817095
  · exact B817099
  · exact B817103
  · exact B817107
  · exact B817111
  · exact B817115
  · exact B817119
  · exact B817123
  · exact B817127
  · exact B817131
  · exact B817135
  · exact B817139
  · exact B817143

theorem C1 (j : ℕ) (h1 : 204286 ≤ j) (h2 : j ≤ 204585) : Blo 814346 (4 * j + 3) := by
  interval_cases j
  · exact B817147
  · exact B817151
  · exact B817155
  · exact B817159
  · exact B817163
  · exact B817167
  · exact B817171
  · exact B817175
  · exact B817179
  · exact B817183
  · exact B817187
  · exact B817191
  · exact B817195
  · exact B817199
  · exact B817203
  · exact B817207
  · exact B817211
  · exact B817215
  · exact B817219
  · exact B817223
  · exact B817227
  · exact B817231
  · exact B817235
  · exact B817239
  · exact B817243
  · exact B817247
  · exact B817251
  · exact B817255
  · exact B817259
  · exact B817263
  · exact B817267
  · exact B817271
  · exact B817275
  · exact B817279
  · exact B817283
  · exact B817287
  · exact B817291
  · exact B817295
  · exact B817299
  · exact B817303
  · exact B817307
  · exact B817311
  · exact B817315
  · exact B817319
  · exact B817323
  · exact B817327
  · exact B817331
  · exact B817335
  · exact B817339
  · exact B817343
  · exact B817347
  · exact B817351
  · exact B817355
  · exact B817359
  · exact B817363
  · exact B817367
  · exact B817371
  · exact B817375
  · exact B817379
  · exact B817383
  · exact B817387
  · exact B817391
  · exact B817395
  · exact B817399
  · exact B817403
  · exact B817407
  · exact B817411
  · exact B817415
  · exact B817419
  · exact B817423
  · exact B817427
  · exact B817431
  · exact B817435
  · exact B817439
  · exact B817443
  · exact B817447
  · exact B817451
  · exact B817455
  · exact B817459
  · exact B817463
  · exact B817467
  · exact B817471
  · exact B817475
  · exact B817479
  · exact B817483
  · exact B817487
  · exact B817491
  · exact B817495
  · exact B817499
  · exact B817503
  · exact B817507
  · exact B817511
  · exact B817515
  · exact B817519
  · exact B817523
  · exact B817527
  · exact B817531
  · exact B817535
  · exact B817539
  · exact B817543
  · exact B817547
  · exact B817551
  · exact B817555
  · exact B817559
  · exact B817563
  · exact B817567
  · exact B817571
  · exact B817575
  · exact B817579
  · exact B817583
  · exact B817587
  · exact B817591
  · exact B817595
  · exact B817599
  · exact B817603
  · exact B817607
  · exact B817611
  · exact B817615
  · exact B817619
  · exact B817623
  · exact B817627
  · exact B817631
  · exact B817635
  · exact B817639
  · exact B817643
  · exact B817647
  · exact B817651
  · exact B817655
  · exact B817659
  · exact B817663
  · exact B817667
  · exact B817671
  · exact B817675
  · exact B817679
  · exact B817683
  · exact B817687
  · exact B817691
  · exact B817695
  · exact B817699
  · exact B817703
  · exact B817707
  · exact B817711
  · exact B817715
  · exact B817719
  · exact B817723
  · exact B817727
  · exact B817731
  · exact B817735
  · exact B817739
  · exact B817743
  · exact B817747
  · exact B817751
  · exact B817755
  · exact B817759
  · exact B817763
  · exact B817767
  · exact B817771
  · exact B817775
  · exact B817779
  · exact B817783
  · exact B817787
  · exact B817791
  · exact B817795
  · exact B817799
  · exact B817803
  · exact B817807
  · exact B817811
  · exact B817815
  · exact B817819
  · exact B817823
  · exact B817827
  · exact B817831
  · exact B817835
  · exact B817839
  · exact B817843
  · exact B817847
  · exact B817851
  · exact B817855
  · exact B817859
  · exact B817863
  · exact B817867
  · exact B817871
  · exact B817875
  · exact B817879
  · exact B817883
  · exact B817887
  · exact B817891
  · exact B817895
  · exact B817899
  · exact B817903
  · exact B817907
  · exact B817911
  · exact B817915
  · exact B817919
  · exact B817923
  · exact B817927
  · exact B817931
  · exact B817935
  · exact B817939
  · exact B817943
  · exact B817947
  · exact B817951
  · exact B817955
  · exact B817959
  · exact B817963
  · exact B817967
  · exact B817971
  · exact B817975
  · exact B817979
  · exact B817983
  · exact B817987
  · exact B817991
  · exact B817995
  · exact B817999
  · exact B818003
  · exact B818007
  · exact B818011
  · exact B818015
  · exact B818019
  · exact B818023
  · exact B818027
  · exact B818031
  · exact B818035
  · exact B818039
  · exact B818043
  · exact B818047
  · exact B818051
  · exact B818055
  · exact B818059
  · exact B818063
  · exact B818067
  · exact B818071
  · exact B818075
  · exact B818079
  · exact B818083
  · exact B818087
  · exact B818091
  · exact B818095
  · exact B818099
  · exact B818103
  · exact B818107
  · exact B818111
  · exact B818115
  · exact B818119
  · exact B818123
  · exact B818127
  · exact B818131
  · exact B818135
  · exact B818139
  · exact B818143
  · exact B818147
  · exact B818151
  · exact B818155
  · exact B818159
  · exact B818163
  · exact B818167
  · exact B818171
  · exact B818175
  · exact B818179
  · exact B818183
  · exact B818187
  · exact B818191
  · exact B818195
  · exact B818199
  · exact B818203
  · exact B818207
  · exact B818211
  · exact B818215
  · exact B818219
  · exact B818223
  · exact B818227
  · exact B818231
  · exact B818235
  · exact B818239
  · exact B818243
  · exact B818247
  · exact B818251
  · exact B818255
  · exact B818259
  · exact B818263
  · exact B818267
  · exact B818271
  · exact B818275
  · exact B818279
  · exact B818283
  · exact B818287
  · exact B818291
  · exact B818295
  · exact B818299
  · exact B818303
  · exact B818307
  · exact B818311
  · exact B818315
  · exact B818319
  · exact B818323
  · exact B818327
  · exact B818331
  · exact B818335
  · exact B818339
  · exact B818343

theorem solution (m : ℕ) (hlo : 814346 ≤ m) (hhi : m ≤ 818346) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 203586 ≤ j := by omega
    have hj2 : j ≤ 204585 := by omega
    have hb : Blo 814346 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 204286 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
