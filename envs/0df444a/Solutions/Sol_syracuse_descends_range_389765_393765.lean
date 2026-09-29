-- Prove2me | solution 1 for syracuse_descends_range_389765_393765
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:45.37077+00:00
-- url     : https://prove2.me/submissions/6fd8f28a-a26c-433d-8ca5-68df0f361734

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


theorem B589829 : Blo 389765 589829 := bbase (se 4 (by rfl) ⟨55296, by rfl⟩ : syracuseStep 589829 = 110593) (by norm_num)
theorem B589853 : Blo 389765 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B884789 : Blo 389765 884789 := bbase (se 5 (by rfl) ⟨41474, by rfl⟩ : syracuseStep 884789 = 82949) (by norm_num)
theorem B589877 : Blo 389765 589877 := bbase (se 5 (by rfl) ⟨27650, by rfl⟩ : syracuseStep 589877 = 55301) (by norm_num)
theorem B589901 : Blo 389765 589901 := bbase (se 3 (by rfl) ⟨110606, by rfl⟩ : syracuseStep 589901 = 221213) (by norm_num)
theorem B589925 : Blo 389765 589925 := bbase (se 4 (by rfl) ⟨55305, by rfl⟩ : syracuseStep 589925 = 110611) (by norm_num)
theorem B884861 : Blo 389765 884861 := bbase (se 3 (by rfl) ⟨165911, by rfl⟩ : syracuseStep 884861 = 331823) (by norm_num)
theorem B589949 : Blo 389765 589949 := bbase (se 3 (by rfl) ⟨110615, by rfl⟩ : syracuseStep 589949 = 221231) (by norm_num)
theorem B589973 : Blo 389765 589973 := bbase (se 6 (by rfl) ⟨13827, by rfl⟩ : syracuseStep 589973 = 27655) (by norm_num)
theorem B589997 : Blo 389765 589997 := bbase (se 3 (by rfl) ⟨110624, by rfl⟩ : syracuseStep 589997 = 221249) (by norm_num)
theorem B884933 : Blo 389765 884933 := bbase (se 4 (by rfl) ⟨82962, by rfl⟩ : syracuseStep 884933 = 165925) (by norm_num)
theorem B590021 : Blo 389765 590021 := bbase (se 4 (by rfl) ⟨55314, by rfl⟩ : syracuseStep 590021 = 110629) (by norm_num)
theorem B590045 : Blo 389765 590045 := bbase (se 3 (by rfl) ⟨110633, by rfl⟩ : syracuseStep 590045 = 221267) (by norm_num)
theorem B1114357 : Blo 389765 1114357 := bbase (se 5 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 1114357 = 104471) (by norm_num)
theorem B590069 : Blo 389765 590069 := bbase (se 5 (by rfl) ⟨27659, by rfl⟩ : syracuseStep 590069 = 55319) (by norm_num)
theorem B885005 : Blo 389765 885005 := bbase (se 3 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 885005 = 331877) (by norm_num)
theorem B590093 : Blo 389765 590093 := bbase (se 3 (by rfl) ⟨110642, by rfl⟩ : syracuseStep 590093 = 221285) (by norm_num)
theorem B590117 : Blo 389765 590117 := bbase (se 4 (by rfl) ⟨55323, by rfl⟩ : syracuseStep 590117 = 110647) (by norm_num)
theorem B590141 : Blo 389765 590141 := bbase (se 3 (by rfl) ⟨110651, by rfl⟩ : syracuseStep 590141 = 221303) (by norm_num)
theorem B557389 : Blo 389765 557389 := bbase (se 3 (by rfl) ⟨104510, by rfl⟩ : syracuseStep 557389 = 209021) (by norm_num)
theorem B885077 : Blo 389765 885077 := bbase (se 10 (by rfl) ⟨1296, by rfl⟩ : syracuseStep 885077 = 2593) (by norm_num)
theorem B590165 : Blo 389765 590165 := bbase (se 10 (by rfl) ⟨864, by rfl⟩ : syracuseStep 590165 = 1729) (by norm_num)
theorem B590189 : Blo 389765 590189 := bbase (se 3 (by rfl) ⟨110660, by rfl⟩ : syracuseStep 590189 = 221321) (by norm_num)
theorem B590213 : Blo 389765 590213 := bbase (se 4 (by rfl) ⟨55332, by rfl⟩ : syracuseStep 590213 = 110665) (by norm_num)
theorem B885149 : Blo 389765 885149 := bbase (se 3 (by rfl) ⟨165965, by rfl⟩ : syracuseStep 885149 = 331931) (by norm_num)
theorem B590237 : Blo 389765 590237 := bbase (se 3 (by rfl) ⟨110669, by rfl⟩ : syracuseStep 590237 = 221339) (by norm_num)
theorem B590261 : Blo 389765 590261 := bbase (se 5 (by rfl) ⟨27668, by rfl⟩ : syracuseStep 590261 = 55337) (by norm_num)
theorem B590285 : Blo 389765 590285 := bbase (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) (by norm_num)
theorem B885221 : Blo 389765 885221 := bbase (se 4 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 885221 = 165979) (by norm_num)
theorem B590309 : Blo 389765 590309 := bbase (se 4 (by rfl) ⟨55341, by rfl⟩ : syracuseStep 590309 = 110683) (by norm_num)
theorem B590333 : Blo 389765 590333 := bbase (se 3 (by rfl) ⟨110687, by rfl⟩ : syracuseStep 590333 = 221375) (by norm_num)
theorem B590357 : Blo 389765 590357 := bbase (se 6 (by rfl) ⟨13836, by rfl⟩ : syracuseStep 590357 = 27673) (by norm_num)
theorem B885293 : Blo 389765 885293 := bbase (se 3 (by rfl) ⟨165992, by rfl⟩ : syracuseStep 885293 = 331985) (by norm_num)
theorem B590381 : Blo 389765 590381 := bbase (se 3 (by rfl) ⟨110696, by rfl⟩ : syracuseStep 590381 = 221393) (by norm_num)
theorem B590405 : Blo 389765 590405 := bbase (se 4 (by rfl) ⟨55350, by rfl⟩ : syracuseStep 590405 = 110701) (by norm_num)
theorem B590429 : Blo 389765 590429 := bbase (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) (by norm_num)
theorem B885365 : Blo 389765 885365 := bbase (se 5 (by rfl) ⟨41501, by rfl⟩ : syracuseStep 885365 = 83003) (by norm_num)
theorem B590453 : Blo 389765 590453 := bbase (se 5 (by rfl) ⟨27677, by rfl⟩ : syracuseStep 590453 = 55355) (by norm_num)
theorem B590477 : Blo 389765 590477 := bbase (se 3 (by rfl) ⟨110714, by rfl⟩ : syracuseStep 590477 = 221429) (by norm_num)
theorem B590501 : Blo 389765 590501 := bbase (se 4 (by rfl) ⟨55359, by rfl⟩ : syracuseStep 590501 = 110719) (by norm_num)
theorem B2228917 : Blo 389765 2228917 := bbase (se 5 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 2228917 = 208961) (by norm_num)
theorem B2982581 : Blo 389765 2982581 := bbase (se 5 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 2982581 = 279617) (by norm_num)
theorem B885437 : Blo 389765 885437 := bbase (se 3 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 885437 = 332039) (by norm_num)
theorem B590525 : Blo 389765 590525 := bbase (se 3 (by rfl) ⟨110723, by rfl⟩ : syracuseStep 590525 = 221447) (by norm_num)
theorem B590549 : Blo 389765 590549 := bbase (se 7 (by rfl) ⟨6920, by rfl⟩ : syracuseStep 590549 = 13841) (by norm_num)
theorem B590573 : Blo 389765 590573 := bbase (se 3 (by rfl) ⟨110732, by rfl⟩ : syracuseStep 590573 = 221465) (by norm_num)
theorem B885509 : Blo 389765 885509 := bbase (se 4 (by rfl) ⟨83016, by rfl⟩ : syracuseStep 885509 = 166033) (by norm_num)
theorem B590597 : Blo 389765 590597 := bbase (se 4 (by rfl) ⟨55368, by rfl⟩ : syracuseStep 590597 = 110737) (by norm_num)
theorem B590621 : Blo 389765 590621 := bbase (se 3 (by rfl) ⟨110741, by rfl⟩ : syracuseStep 590621 = 221483) (by norm_num)
theorem B590645 : Blo 389765 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B885581 : Blo 389765 885581 := bbase (se 3 (by rfl) ⟨166046, by rfl⟩ : syracuseStep 885581 = 332093) (by norm_num)
theorem B885653 : Blo 389765 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B885725 : Blo 389765 885725 := bbase (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) (by norm_num)
theorem B885797 : Blo 389765 885797 := bbase (se 4 (by rfl) ⟨83043, by rfl⟩ : syracuseStep 885797 = 166087) (by norm_num)
theorem B558181 : Blo 389765 558181 := bbase (se 4 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 558181 = 104659) (by norm_num)
theorem B885869 : Blo 389765 885869 := bbase (se 3 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 885869 = 332201) (by norm_num)
theorem B6325397 : Blo 389765 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B885941 : Blo 389765 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B1115461 : Blo 389765 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B558517 : Blo 389765 558517 := bbase (se 5 (by rfl) ⟨26180, by rfl⟩ : syracuseStep 558517 = 52361) (by norm_num)
theorem B1672645 : Blo 389765 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B755173 : Blo 389765 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1050085 : Blo 389765 1050085 := bbase (se 4 (by rfl) ⟨98445, by rfl⟩ : syracuseStep 1050085 = 196891) (by norm_num)
theorem B788077 : Blo 389765 788077 := bbase (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) (by norm_num)
theorem B558733 : Blo 389765 558733 := bbase (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) (by norm_num)
theorem B1410821 : Blo 389765 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B493381 : Blo 389765 493381 := bbase (se 4 (by rfl) ⟨46254, by rfl⟩ : syracuseStep 493381 = 92509) (by norm_num)
theorem B1410949 : Blo 389765 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B493553 : Blo 389765 493553 := bbase (se 2 (by rfl) ⟨185082, by rfl⟩ : syracuseStep 493553 = 370165) (by norm_num)
theorem B559109 : Blo 389765 559109 := bbase (se 4 (by rfl) ⟨52416, by rfl⟩ : syracuseStep 559109 = 104833) (by norm_num)
theorem B493609 : Blo 389765 493609 := bbase (se 2 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 493609 = 370207) (by norm_num)
theorem B493705 : Blo 389765 493705 := bbase (se 2 (by rfl) ⟨185139, by rfl⟩ : syracuseStep 493705 = 370279) (by norm_num)
theorem B395561 : Blo 389765 395561 := bbase (se 2 (by rfl) ⟨148335, by rfl⟩ : syracuseStep 395561 = 296671) (by norm_num)
theorem B493877 : Blo 389765 493877 := bbase (se 5 (by rfl) ⟨23150, by rfl⟩ : syracuseStep 493877 = 46301) (by norm_num)
theorem B657733 : Blo 389765 657733 := bbase (se 4 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 657733 = 123325) (by norm_num)
theorem B395597 : Blo 389765 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B493933 : Blo 389765 493933 := bbase (se 3 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 493933 = 185225) (by norm_num)
theorem B625013 : Blo 389765 625013 := bbase (se 5 (by rfl) ⟨29297, by rfl⟩ : syracuseStep 625013 = 58595) (by norm_num)
theorem B8063381 : Blo 389765 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B657821 : Blo 389765 657821 := bbase (se 3 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 657821 = 246683) (by norm_num)
theorem B494029 : Blo 389765 494029 := bbase (se 3 (by rfl) ⟨92630, by rfl⟩ : syracuseStep 494029 = 185261) (by norm_num)
theorem B657949 : Blo 389765 657949 := bbase (se 3 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 657949 = 246731) (by norm_num)
theorem B625205 : Blo 389765 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B395857 : Blo 389765 395857 := bbase (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) (by norm_num)
theorem B658037 : Blo 389765 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B2230901 : Blo 389765 2230901 := bbase (se 5 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 2230901 = 209147) (by norm_num)
theorem B494201 : Blo 389765 494201 := bbase (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) (by norm_num)
theorem B494257 : Blo 389765 494257 := bbase (se 2 (by rfl) ⟨185346, by rfl⟩ : syracuseStep 494257 = 370693) (by norm_num)
theorem B3148469 : Blo 389765 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B658165 : Blo 389765 658165 := bbase (se 5 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 658165 = 61703) (by norm_num)
theorem B494353 : Blo 389765 494353 := bbase (se 2 (by rfl) ⟨185382, by rfl⟩ : syracuseStep 494353 = 370765) (by norm_num)
theorem B1116965 : Blo 389765 1116965 := bbase (se 4 (by rfl) ⟨104715, by rfl⟩ : syracuseStep 1116965 = 209431) (by norm_num)
theorem B658253 : Blo 389765 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B396181 : Blo 389765 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B494525 : Blo 389765 494525 := bbase (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) (by norm_num)
theorem B756677 : Blo 389765 756677 := bbase (se 4 (by rfl) ⟨70938, by rfl⟩ : syracuseStep 756677 = 141877) (by norm_num)
theorem B658381 : Blo 389765 658381 := bbase (se 3 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 658381 = 246893) (by norm_num)
theorem B494581 : Blo 389765 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B658469 : Blo 389765 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B494677 : Blo 389765 494677 := bbase (se 8 (by rfl) ⟨2898, by rfl⟩ : syracuseStep 494677 = 5797) (by norm_num)
theorem B1510517 : Blo 389765 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B658597 : Blo 389765 658597 := bbase (se 4 (by rfl) ⟨61743, by rfl⟩ : syracuseStep 658597 = 123487) (by norm_num)
theorem B658685 : Blo 389765 658685 := bbase (se 3 (by rfl) ⟨123503, by rfl⟩ : syracuseStep 658685 = 247007) (by norm_num)
theorem B494849 : Blo 389765 494849 := bbase (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) (by norm_num)
theorem B494905 : Blo 389765 494905 := bbase (se 2 (by rfl) ⟨185589, by rfl⟩ : syracuseStep 494905 = 371179) (by norm_num)
theorem B658813 : Blo 389765 658813 := bbase (se 3 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 658813 = 247055) (by norm_num)
theorem B560533 : Blo 389765 560533 := bbase (se 6 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 560533 = 26275) (by norm_num)
theorem B495001 : Blo 389765 495001 := bbase (se 2 (by rfl) ⟨185625, by rfl⟩ : syracuseStep 495001 = 371251) (by norm_num)
theorem B396733 : Blo 389765 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B658901 : Blo 389765 658901 := bbase (se 7 (by rfl) ⟨7721, by rfl⟩ : syracuseStep 658901 = 15443) (by norm_num)
theorem B495173 : Blo 389765 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B986701 : Blo 389765 986701 := bbase (se 3 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 986701 = 370013) (by norm_num)
theorem B659029 : Blo 389765 659029 := bbase (se 8 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 659029 = 7723) (by norm_num)
theorem B495229 : Blo 389765 495229 := bbase (se 3 (by rfl) ⟨92855, by rfl⟩ : syracuseStep 495229 = 185711) (by norm_num)
theorem B659117 : Blo 389765 659117 := bbase (se 3 (by rfl) ⟨123584, by rfl⟩ : syracuseStep 659117 = 247169) (by norm_num)
theorem B986813 : Blo 389765 986813 := bbase (se 3 (by rfl) ⟨185027, by rfl⟩ : syracuseStep 986813 = 370055) (by norm_num)
theorem B495325 : Blo 389765 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B659245 : Blo 389765 659245 := bbase (se 3 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 659245 = 247217) (by norm_num)
theorem B626525 : Blo 389765 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B987005 : Blo 389765 987005 := bbase (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) (by norm_num)
theorem B659333 : Blo 389765 659333 := bbase (se 4 (by rfl) ⟨61812, by rfl⟩ : syracuseStep 659333 = 123625) (by norm_num)
theorem B495497 : Blo 389765 495497 := bbase (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) (by norm_num)
theorem B626621 : Blo 389765 626621 := bbase (se 3 (by rfl) ⟨117491, by rfl⟩ : syracuseStep 626621 = 234983) (by norm_num)
theorem B495553 : Blo 389765 495553 := bbase (se 2 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 495553 = 371665) (by norm_num)
theorem B626653 : Blo 389765 626653 := bbase (se 3 (by rfl) ⟨117497, by rfl⟩ : syracuseStep 626653 = 234995) (by norm_num)
theorem B659461 : Blo 389765 659461 := bbase (se 4 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 659461 = 123649) (by norm_num)
theorem B495649 : Blo 389765 495649 := bbase (se 2 (by rfl) ⟨185868, by rfl⟩ : syracuseStep 495649 = 371737) (by norm_num)
theorem B659549 : Blo 389765 659549 := bbase (se 3 (by rfl) ⟨123665, by rfl⟩ : syracuseStep 659549 = 247331) (by norm_num)
theorem B594029 : Blo 389765 594029 := bbase (se 3 (by rfl) ⟨111380, by rfl⟩ : syracuseStep 594029 = 222761) (by norm_num)
theorem B495821 : Blo 389765 495821 := bbase (se 3 (by rfl) ⟨92966, by rfl⟩ : syracuseStep 495821 = 185933) (by norm_num)
theorem B987349 : Blo 389765 987349 := bbase (se 7 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 987349 = 23141) (by norm_num)
theorem B659677 : Blo 389765 659677 := bbase (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) (by norm_num)
theorem B495877 : Blo 389765 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B790805 : Blo 389765 790805 := bbase (se 6 (by rfl) ⟨18534, by rfl⟩ : syracuseStep 790805 = 37069) (by norm_num)
theorem B659765 : Blo 389765 659765 := bbase (se 5 (by rfl) ⟨30926, by rfl⟩ : syracuseStep 659765 = 61853) (by norm_num)
theorem B987461 : Blo 389765 987461 := bbase (se 4 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 987461 = 185149) (by norm_num)
theorem B3772757 : Blo 389765 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B1118549 : Blo 389765 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B397657 : Blo 389765 397657 := bbase (se 2 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 397657 = 298243) (by norm_num)
theorem B495973 : Blo 389765 495973 := bbase (se 4 (by rfl) ⟨46497, by rfl⟩ : syracuseStep 495973 = 92995) (by norm_num)
theorem B1675637 : Blo 389765 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B659893 : Blo 389765 659893 := bbase (se 5 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 659893 = 61865) (by norm_num)
theorem B987653 : Blo 389765 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B659981 : Blo 389765 659981 := bbase (se 3 (by rfl) ⟨123746, by rfl⟩ : syracuseStep 659981 = 247493) (by norm_num)
theorem B496145 : Blo 389765 496145 := bbase (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) (by norm_num)
theorem B496201 : Blo 389765 496201 := bbase (se 2 (by rfl) ⟨186075, by rfl⟩ : syracuseStep 496201 = 372151) (by norm_num)
theorem B660109 : Blo 389765 660109 := bbase (se 3 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 660109 = 247541) (by norm_num)
theorem B1315493 : Blo 389765 1315493 := bbase (se 4 (by rfl) ⟨123327, by rfl⟩ : syracuseStep 1315493 = 246655) (by norm_num)
theorem B496297 : Blo 389765 496297 := bbase (se 2 (by rfl) ⟨186111, by rfl⟩ : syracuseStep 496297 = 372223) (by norm_num)
theorem B397997 : Blo 389765 397997 := bbase (se 3 (by rfl) ⟨74624, by rfl⟩ : syracuseStep 397997 = 149249) (by norm_num)
theorem B660197 : Blo 389765 660197 := bbase (se 4 (by rfl) ⟨61893, by rfl⟩ : syracuseStep 660197 = 123787) (by norm_num)
theorem B2233109 : Blo 389765 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B496469 : Blo 389765 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B987997 : Blo 389765 987997 := bbase (se 3 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 987997 = 370499) (by norm_num)
theorem B660325 : Blo 389765 660325 := bbase (se 4 (by rfl) ⟨61905, by rfl⟩ : syracuseStep 660325 = 123811) (by norm_num)
theorem B496525 : Blo 389765 496525 := bbase (se 3 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 496525 = 186197) (by norm_num)
theorem B660413 : Blo 389765 660413 := bbase (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) (by norm_num)
theorem B988109 : Blo 389765 988109 := bbase (se 3 (by rfl) ⟨185270, by rfl⟩ : syracuseStep 988109 = 370541) (by norm_num)
theorem B496621 : Blo 389765 496621 := bbase (se 3 (by rfl) ⟨93116, by rfl⟩ : syracuseStep 496621 = 186233) (by norm_num)
theorem B1119221 : Blo 389765 1119221 := bbase (se 5 (by rfl) ⟨52463, by rfl⟩ : syracuseStep 1119221 = 104927) (by norm_num)
theorem B3347477 : Blo 389765 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B660541 : Blo 389765 660541 := bbase (se 3 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 660541 = 247703) (by norm_num)
theorem B1315925 : Blo 389765 1315925 := bbase (se 8 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 1315925 = 15421) (by norm_num)
theorem B988301 : Blo 389765 988301 := bbase (se 3 (by rfl) ⟨185306, by rfl⟩ : syracuseStep 988301 = 370613) (by norm_num)
theorem B660629 : Blo 389765 660629 := bbase (se 6 (by rfl) ⟨15483, by rfl⟩ : syracuseStep 660629 = 30967) (by norm_num)
theorem B496793 : Blo 389765 496793 := bbase (se 2 (by rfl) ⟨186297, by rfl⟩ : syracuseStep 496793 = 372595) (by norm_num)
theorem B496849 : Blo 389765 496849 := bbase (se 2 (by rfl) ⟨186318, by rfl⟩ : syracuseStep 496849 = 372637) (by norm_num)
theorem B660757 : Blo 389765 660757 := bbase (se 6 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 660757 = 30973) (by norm_num)
theorem B6722837 : Blo 389765 6722837 := bbase (se 6 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 6722837 = 315133) (by norm_num)
theorem B496945 : Blo 389765 496945 := bbase (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) (by norm_num)
theorem B1676645 : Blo 389765 1676645 := bbase (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) (by norm_num)
theorem B660845 : Blo 389765 660845 := bbase (se 3 (by rfl) ⟨123908, by rfl⟩ : syracuseStep 660845 = 247817) (by norm_num)
theorem B1119653 : Blo 389765 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B628165 : Blo 389765 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B2004437 : Blo 389765 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B497117 : Blo 389765 497117 := bbase (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) (by norm_num)
theorem B988645 : Blo 389765 988645 := bbase (se 4 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 988645 = 185371) (by norm_num)
theorem B660973 : Blo 389765 660973 := bbase (se 3 (by rfl) ⟨123932, by rfl⟩ : syracuseStep 660973 = 247865) (by norm_num)
theorem B562685 : Blo 389765 562685 := bbase (se 3 (by rfl) ⟨105503, by rfl⟩ : syracuseStep 562685 = 211007) (by norm_num)
theorem B1316357 : Blo 389765 1316357 := bbase (se 4 (by rfl) ⟨123408, by rfl⟩ : syracuseStep 1316357 = 246817) (by norm_num)
theorem B497173 : Blo 389765 497173 := bbase (se 6 (by rfl) ⟨11652, by rfl⟩ : syracuseStep 497173 = 23305) (by norm_num)
theorem B661061 : Blo 389765 661061 := bbase (se 4 (by rfl) ⟨61974, by rfl⟩ : syracuseStep 661061 = 123949) (by norm_num)
theorem B988757 : Blo 389765 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B497269 : Blo 389765 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B530101 : Blo 389765 530101 := bbase (se 5 (by rfl) ⟨24848, by rfl⟩ : syracuseStep 530101 = 49697) (by norm_num)
theorem B661189 : Blo 389765 661189 := bbase (se 4 (by rfl) ⟨61986, by rfl⟩ : syracuseStep 661189 = 123973) (by norm_num)
theorem B988949 : Blo 389765 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B661277 : Blo 389765 661277 := bbase (se 3 (by rfl) ⟨123989, by rfl⟩ : syracuseStep 661277 = 247979) (by norm_num)
theorem B497441 : Blo 389765 497441 := bbase (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) (by norm_num)
theorem B497497 : Blo 389765 497497 := bbase (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) (by norm_num)
theorem B530285 : Blo 389765 530285 := bbase (se 3 (by rfl) ⟨99428, by rfl⟩ : syracuseStep 530285 = 198857) (by norm_num)
theorem B595829 : Blo 389765 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B530317 : Blo 389765 530317 := bbase (se 3 (by rfl) ⟨99434, by rfl⟩ : syracuseStep 530317 = 198869) (by norm_num)
theorem B661405 : Blo 389765 661405 := bbase (se 3 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 661405 = 248027) (by norm_num)
theorem B1316789 : Blo 389765 1316789 := bbase (se 5 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 1316789 = 123449) (by norm_num)
theorem B497593 : Blo 389765 497593 := bbase (se 2 (by rfl) ⟨186597, by rfl⟩ : syracuseStep 497593 = 373195) (by norm_num)
theorem B9050069 : Blo 389765 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B661493 : Blo 389765 661493 := bbase (se 5 (by rfl) ⟨31007, by rfl⟩ : syracuseStep 661493 = 62015) (by norm_num)
theorem B1873925 : Blo 389765 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B497765 : Blo 389765 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B989293 : Blo 389765 989293 := bbase (se 3 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 989293 = 370985) (by norm_num)
theorem B2136181 : Blo 389765 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B661621 : Blo 389765 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B956549 : Blo 389765 956549 := bbase (se 4 (by rfl) ⟨89676, by rfl⟩ : syracuseStep 956549 = 179353) (by norm_num)
theorem B628877 : Blo 389765 628877 := bbase (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) (by norm_num)
theorem B1120405 : Blo 389765 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B497821 : Blo 389765 497821 := bbase (se 3 (by rfl) ⟨93341, by rfl⟩ : syracuseStep 497821 = 186683) (by norm_num)
theorem B661709 : Blo 389765 661709 := bbase (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) (by norm_num)
theorem B989405 : Blo 389765 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B1480949 : Blo 389765 1480949 := bbase (se 5 (by rfl) ⟨69419, by rfl⟩ : syracuseStep 1480949 = 138839) (by norm_num)
theorem B497917 : Blo 389765 497917 := bbase (se 3 (by rfl) ⟨93359, by rfl⟩ : syracuseStep 497917 = 186719) (by norm_num)
theorem B661837 : Blo 389765 661837 := bbase (se 3 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 661837 = 248189) (by norm_num)
theorem B1317221 : Blo 389765 1317221 := bbase (se 4 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 1317221 = 246979) (by norm_num)
theorem B989597 : Blo 389765 989597 := bbase (se 3 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 989597 = 371099) (by norm_num)
theorem B661925 : Blo 389765 661925 := bbase (se 4 (by rfl) ⟨62055, by rfl⟩ : syracuseStep 661925 = 124111) (by norm_num)
theorem B498089 : Blo 389765 498089 := bbase (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) (by norm_num)
theorem B596413 : Blo 389765 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B498145 : Blo 389765 498145 := bbase (se 2 (by rfl) ⟨186804, by rfl⟩ : syracuseStep 498145 = 373609) (by norm_num)
theorem B1251845 : Blo 389765 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B1481237 : Blo 389765 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B662053 : Blo 389765 662053 := bbase (se 4 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 662053 = 124135) (by norm_num)
theorem B498241 : Blo 389765 498241 := bbase (se 2 (by rfl) ⟨186840, by rfl⟩ : syracuseStep 498241 = 373681) (by norm_num)
theorem B662141 : Blo 389765 662141 := bbase (se 3 (by rfl) ⟨124151, by rfl⟩ : syracuseStep 662141 = 248303) (by norm_num)
theorem B989941 : Blo 389765 989941 := bbase (se 5 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 989941 = 92807) (by norm_num)
theorem B662269 : Blo 389765 662269 := bbase (se 3 (by rfl) ⟨124175, by rfl⟩ : syracuseStep 662269 = 248351) (by norm_num)
theorem B1317653 : Blo 389765 1317653 := bbase (se 6 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 1317653 = 61765) (by norm_num)
theorem B629549 : Blo 389765 629549 := bbase (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) (by norm_num)
theorem B662357 : Blo 389765 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B990053 : Blo 389765 990053 := bbase (se 4 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 990053 = 185635) (by norm_num)
theorem B662485 : Blo 389765 662485 := bbase (se 7 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 662485 = 15527) (by norm_num)
theorem B1416197 : Blo 389765 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B990245 : Blo 389765 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B662573 : Blo 389765 662573 := bbase (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) (by norm_num)
theorem B1678421 : Blo 389765 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B793741 : Blo 389765 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B662701 : Blo 389765 662701 := bbase (se 3 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 662701 = 248513) (by norm_num)
theorem B1318085 : Blo 389765 1318085 := bbase (se 4 (by rfl) ⟨123570, by rfl⟩ : syracuseStep 1318085 = 247141) (by norm_num)
theorem B662789 : Blo 389765 662789 := bbase (se 4 (by rfl) ⟨62136, by rfl⟩ : syracuseStep 662789 = 124273) (by norm_num)
theorem B630061 : Blo 389765 630061 := bbase (se 3 (by rfl) ⟨118136, by rfl⟩ : syracuseStep 630061 = 236273) (by norm_num)
theorem B990589 : Blo 389765 990589 := bbase (se 3 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 990589 = 371471) (by norm_num)
theorem B1252741 : Blo 389765 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B662917 : Blo 389765 662917 := bbase (se 4 (by rfl) ⟨62148, by rfl⟩ : syracuseStep 662917 = 124297) (by norm_num)
theorem B957853 : Blo 389765 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B663005 : Blo 389765 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B990701 : Blo 389765 990701 := bbase (se 3 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 990701 = 371513) (by norm_num)
theorem B663133 : Blo 389765 663133 := bbase (se 3 (by rfl) ⟨124337, by rfl⟩ : syracuseStep 663133 = 248675) (by norm_num)
theorem B958061 : Blo 389765 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B1318517 : Blo 389765 1318517 := bbase (se 5 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 1318517 = 123611) (by norm_num)
theorem B794261 : Blo 389765 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B532133 : Blo 389765 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B990893 : Blo 389765 990893 := bbase (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) (by norm_num)
theorem B1482421 : Blo 389765 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B663221 : Blo 389765 663221 := bbase (se 5 (by rfl) ⟨31088, by rfl⟩ : syracuseStep 663221 = 62177) (by norm_num)
theorem B892613 : Blo 389765 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B630517 : Blo 389765 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B1253141 : Blo 389765 1253141 := bbase (se 6 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 1253141 = 58741) (by norm_num)
theorem B663349 : Blo 389765 663349 := bbase (se 5 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 663349 = 62189) (by norm_num)
theorem B761717 : Blo 389765 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B663437 : Blo 389765 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B1482725 : Blo 389765 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B598013 : Blo 389765 598013 := bbase (se 3 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 598013 = 224255) (by norm_num)
theorem B991237 : Blo 389765 991237 := bbase (se 4 (by rfl) ⟨92928, by rfl⟩ : syracuseStep 991237 = 185857) (by norm_num)
theorem B663565 : Blo 389765 663565 := bbase (se 3 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 663565 = 248837) (by norm_num)
theorem B1974293 : Blo 389765 1974293 := bbase (se 6 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 1974293 = 92545) (by norm_num)
theorem B1318949 : Blo 389765 1318949 := bbase (se 4 (by rfl) ⟨123651, by rfl⟩ : syracuseStep 1318949 = 247303) (by norm_num)
theorem B16162901 : Blo 389765 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B663653 : Blo 389765 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B991349 : Blo 389765 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B598213 : Blo 389765 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B663781 : Blo 389765 663781 := bbase (se 4 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 663781 = 124459) (by norm_num)
theorem B991541 : Blo 389765 991541 := bbase (se 5 (by rfl) ⟨46478, by rfl⟩ : syracuseStep 991541 = 92957) (by norm_num)
theorem B663869 : Blo 389765 663869 := bbase (se 3 (by rfl) ⟨124475, by rfl⟩ : syracuseStep 663869 = 248951) (by norm_num)
theorem B663997 : Blo 389765 663997 := bbase (se 3 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 663997 = 248999) (by norm_num)
theorem B1319381 : Blo 389765 1319381 := bbase (se 7 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 1319381 = 30923) (by norm_num)
theorem B664085 : Blo 389765 664085 := bbase (se 6 (by rfl) ⟨15564, by rfl⟩ : syracuseStep 664085 = 31129) (by norm_num)
theorem B3875381 : Blo 389765 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B434765 : Blo 389765 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B991885 : Blo 389765 991885 := bbase (se 3 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 991885 = 371957) (by norm_num)
theorem B664213 : Blo 389765 664213 := bbase (se 6 (by rfl) ⟨15567, by rfl⟩ : syracuseStep 664213 = 31135) (by norm_num)
theorem B664301 : Blo 389765 664301 := bbase (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) (by norm_num)
theorem B500473 : Blo 389765 500473 := bbase (se 2 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 500473 = 375355) (by norm_num)
theorem B991997 : Blo 389765 991997 := bbase (se 3 (by rfl) ⟨185999, by rfl⟩ : syracuseStep 991997 = 371999) (by norm_num)
theorem B500513 : Blo 389765 500513 := bbase (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) (by norm_num)
theorem B664429 : Blo 389765 664429 := bbase (se 3 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 664429 = 249161) (by norm_num)
theorem B1319813 : Blo 389765 1319813 := bbase (se 4 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 1319813 = 247465) (by norm_num)
theorem B992189 : Blo 389765 992189 := bbase (se 3 (by rfl) ⟨186035, by rfl⟩ : syracuseStep 992189 = 372071) (by norm_num)
theorem B828613 : Blo 389765 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B1582325 : Blo 389765 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B992533 : Blo 389765 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B1975589 : Blo 389765 1975589 := bbase (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) (by norm_num)
theorem B1320245 : Blo 389765 1320245 := bbase (se 5 (by rfl) ⟨61886, by rfl⟩ : syracuseStep 1320245 = 123773) (by norm_num)
theorem B468289 : Blo 389765 468289 := bbase (se 2 (by rfl) ⟨175608, by rfl⟩ : syracuseStep 468289 = 351217) (by norm_num)
theorem B468337 : Blo 389765 468337 := bbase (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) (by norm_num)
theorem B992645 : Blo 389765 992645 := bbase (se 4 (by rfl) ⟨93060, by rfl⟩ : syracuseStep 992645 = 186121) (by norm_num)
theorem B4760981 : Blo 389765 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B796061 : Blo 389765 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B1582517 : Blo 389765 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B468433 : Blo 389765 468433 := bbase (se 2 (by rfl) ⟨175662, by rfl⟩ : syracuseStep 468433 = 351325) (by norm_num)
theorem B992837 : Blo 389765 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B534101 : Blo 389765 534101 := bbase (se 8 (by rfl) ⟨3129, by rfl⟩ : syracuseStep 534101 = 6259) (by norm_num)
theorem B1320677 : Blo 389765 1320677 := bbase (se 4 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 1320677 = 247627) (by norm_num)
theorem B1058645 : Blo 389765 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B993181 : Blo 389765 993181 := bbase (se 3 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 993181 = 372443) (by norm_num)
theorem B993293 : Blo 389765 993293 := bbase (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) (by norm_num)
theorem B469009 : Blo 389765 469009 := bbase (se 2 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 469009 = 351757) (by norm_num)
theorem B1779749 : Blo 389765 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B1484837 : Blo 389765 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B1321109 : Blo 389765 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B2009285 : Blo 389765 2009285 := bbase (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) (by norm_num)
theorem B993485 : Blo 389765 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B1059077 : Blo 389765 1059077 := bbase (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) (by norm_num)
theorem B1485125 : Blo 389765 1485125 := bbase (se 4 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 1485125 = 278461) (by norm_num)
theorem B895349 : Blo 389765 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B895421 : Blo 389765 895421 := bbase (se 3 (by rfl) ⟨167891, by rfl⟩ : syracuseStep 895421 = 335783) (by norm_num)
theorem B11446741 : Blo 389765 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B993829 : Blo 389765 993829 := bbase (se 4 (by rfl) ⟨93171, by rfl⟩ : syracuseStep 993829 = 186343) (by norm_num)
theorem B1976885 : Blo 389765 1976885 := bbase (se 5 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 1976885 = 185333) (by norm_num)
theorem B1321541 : Blo 389765 1321541 := bbase (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) (by norm_num)
theorem B502357 : Blo 389765 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B797293 : Blo 389765 797293 := bbase (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) (by norm_num)
theorem B2894453 : Blo 389765 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B993941 : Blo 389765 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B3189557 : Blo 389765 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B994133 : Blo 389765 994133 := bbase (se 9 (by rfl) ⟨2912, by rfl⟩ : syracuseStep 994133 = 5825) (by norm_num)
theorem B1321973 : Blo 389765 1321973 := bbase (se 5 (by rfl) ⟨61967, by rfl⟩ : syracuseStep 1321973 = 123935) (by norm_num)
theorem B470009 : Blo 389765 470009 := bbase (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) (by norm_num)
theorem B470057 : Blo 389765 470057 := bbase (se 2 (by rfl) ⟨176271, by rfl⟩ : syracuseStep 470057 = 352543) (by norm_num)
theorem B502849 : Blo 389765 502849 := bbase (se 2 (by rfl) ⟨188568, by rfl⟩ : syracuseStep 502849 = 377137) (by norm_num)
theorem B666749 : Blo 389765 666749 := bbase (se 3 (by rfl) ⟨125015, by rfl⟩ : syracuseStep 666749 = 250031) (by norm_num)
theorem B633997 : Blo 389765 633997 := bbase (se 3 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 633997 = 237749) (by norm_num)
theorem B994477 : Blo 389765 994477 := bbase (se 3 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 994477 = 372929) (by norm_num)
theorem B994589 : Blo 389765 994589 := bbase (se 3 (by rfl) ⟨186485, by rfl⟩ : syracuseStep 994589 = 372971) (by norm_num)
theorem B4828501 : Blo 389765 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B1322405 : Blo 389765 1322405 := bbase (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) (by norm_num)
theorem B994781 : Blo 389765 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B1486309 : Blo 389765 1486309 := bbase (se 4 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 1486309 = 278683) (by norm_num)
theorem B1256933 : Blo 389765 1256933 := bbase (se 4 (by rfl) ⟨117837, by rfl⟩ : syracuseStep 1256933 = 235675) (by norm_num)
theorem B470605 : Blo 389765 470605 := bbase (se 3 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 470605 = 176477) (by norm_num)
theorem B896773 : Blo 389765 896773 := bbase (se 4 (by rfl) ⟨84072, by rfl⟩ : syracuseStep 896773 = 168145) (by norm_num)
theorem B1486613 : Blo 389765 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B995125 : Blo 389765 995125 := bbase (se 5 (by rfl) ⟨46646, by rfl⟩ : syracuseStep 995125 = 93293) (by norm_num)
theorem B1978181 : Blo 389765 1978181 := bbase (se 4 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 1978181 = 370909) (by norm_num)
theorem B7515989 : Blo 389765 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B1322837 : Blo 389765 1322837 := bbase (se 9 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 1322837 = 7751) (by norm_num)
theorem B995237 : Blo 389765 995237 := bbase (se 4 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 995237 = 186607) (by norm_num)
theorem B471085 : Blo 389765 471085 := bbase (se 3 (by rfl) ⟨88328, by rfl⟩ : syracuseStep 471085 = 176657) (by norm_num)
theorem B995429 : Blo 389765 995429 := bbase (se 4 (by rfl) ⟨93321, by rfl⟩ : syracuseStep 995429 = 186643) (by norm_num)
theorem B897173 : Blo 389765 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B438493 : Blo 389765 438493 := bbase (se 3 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 438493 = 164435) (by norm_num)
theorem B438529 : Blo 389765 438529 := bbase (se 2 (by rfl) ⟨164448, by rfl⟩ : syracuseStep 438529 = 328897) (by norm_num)
theorem B1323269 : Blo 389765 1323269 := bbase (se 4 (by rfl) ⟨124056, by rfl⟩ : syracuseStep 1323269 = 248113) (by norm_num)
theorem B438565 : Blo 389765 438565 := bbase (se 4 (by rfl) ⟨41115, by rfl⟩ : syracuseStep 438565 = 82231) (by norm_num)
theorem B438601 : Blo 389765 438601 := bbase (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) (by norm_num)
theorem B438637 : Blo 389765 438637 := bbase (se 3 (by rfl) ⟨82244, by rfl⟩ : syracuseStep 438637 = 164489) (by norm_num)
theorem B438673 : Blo 389765 438673 := bbase (se 2 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 438673 = 329005) (by norm_num)
theorem B438709 : Blo 389765 438709 := bbase (se 5 (by rfl) ⟨20564, by rfl⟩ : syracuseStep 438709 = 41129) (by norm_num)
theorem B995773 : Blo 389765 995773 := bbase (se 3 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 995773 = 373415) (by norm_num)
theorem B438745 : Blo 389765 438745 := bbase (se 2 (by rfl) ⟨164529, by rfl⟩ : syracuseStep 438745 = 329059) (by norm_num)
theorem B438781 : Blo 389765 438781 := bbase (se 3 (by rfl) ⟨82271, by rfl⟩ : syracuseStep 438781 = 164543) (by norm_num)
theorem B602653 : Blo 389765 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B438817 : Blo 389765 438817 := bbase (se 2 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 438817 = 329113) (by norm_num)
theorem B1258021 : Blo 389765 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B995885 : Blo 389765 995885 := bbase (se 3 (by rfl) ⟨186728, by rfl⟩ : syracuseStep 995885 = 373457) (by norm_num)
theorem B438853 : Blo 389765 438853 := bbase (se 4 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 438853 = 82285) (by norm_num)
theorem B438889 : Blo 389765 438889 := bbase (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) (by norm_num)
theorem B438925 : Blo 389765 438925 := bbase (se 3 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 438925 = 164597) (by norm_num)
theorem B438961 : Blo 389765 438961 := bbase (se 2 (by rfl) ⟨164610, by rfl⟩ : syracuseStep 438961 = 329221) (by norm_num)
theorem B1323701 : Blo 389765 1323701 := bbase (se 5 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 1323701 = 124097) (by norm_num)
theorem B504517 : Blo 389765 504517 := bbase (se 4 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 504517 = 94597) (by norm_num)
theorem B438997 : Blo 389765 438997 := bbase (se 7 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 438997 = 10289) (by norm_num)
theorem B996077 : Blo 389765 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B439033 : Blo 389765 439033 := bbase (se 2 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 439033 = 329275) (by norm_num)
theorem B439069 : Blo 389765 439069 := bbase (se 3 (by rfl) ⟨82325, by rfl⟩ : syracuseStep 439069 = 164651) (by norm_num)
theorem B439105 : Blo 389765 439105 := bbase (se 2 (by rfl) ⟨164664, by rfl⟩ : syracuseStep 439105 = 329329) (by norm_num)
theorem B439141 : Blo 389765 439141 := bbase (se 4 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 439141 = 82339) (by norm_num)
theorem B439177 : Blo 389765 439177 := bbase (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) (by norm_num)
theorem B471965 : Blo 389765 471965 := bbase (se 3 (by rfl) ⟨88493, by rfl⟩ : syracuseStep 471965 = 176987) (by norm_num)
theorem B439213 : Blo 389765 439213 := bbase (se 3 (by rfl) ⟨82352, by rfl⟩ : syracuseStep 439213 = 164705) (by norm_num)
theorem B439249 : Blo 389765 439249 := bbase (se 2 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 439249 = 329437) (by norm_num)
theorem B439285 : Blo 389765 439285 := bbase (se 5 (by rfl) ⟨20591, by rfl⟩ : syracuseStep 439285 = 41183) (by norm_num)
theorem B472081 : Blo 389765 472081 := bbase (se 2 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 472081 = 354061) (by norm_num)
theorem B439321 : Blo 389765 439321 := bbase (se 2 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 439321 = 329491) (by norm_num)
theorem B439357 : Blo 389765 439357 := bbase (se 3 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 439357 = 164759) (by norm_num)
theorem B996421 : Blo 389765 996421 := bbase (se 4 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 996421 = 186829) (by norm_num)
theorem B1979477 : Blo 389765 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B439393 : Blo 389765 439393 := bbase (se 2 (by rfl) ⟨164772, by rfl⟩ : syracuseStep 439393 = 329545) (by norm_num)
theorem B1324133 : Blo 389765 1324133 := bbase (se 4 (by rfl) ⟨124137, by rfl⟩ : syracuseStep 1324133 = 248275) (by norm_num)
theorem B439429 : Blo 389765 439429 := bbase (se 4 (by rfl) ⟨41196, by rfl⟩ : syracuseStep 439429 = 82393) (by norm_num)
theorem B439465 : Blo 389765 439465 := bbase (se 2 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 439465 = 329599) (by norm_num)
theorem B832693 : Blo 389765 832693 := bbase (se 5 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 832693 = 78065) (by norm_num)
theorem B996533 : Blo 389765 996533 := bbase (se 5 (by rfl) ⟨46712, by rfl⟩ : syracuseStep 996533 = 93425) (by norm_num)
theorem B439501 : Blo 389765 439501 := bbase (se 3 (by rfl) ⟨82406, by rfl⟩ : syracuseStep 439501 = 164813) (by norm_num)
theorem B472277 : Blo 389765 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B439537 : Blo 389765 439537 := bbase (se 2 (by rfl) ⟨164826, by rfl⟩ : syracuseStep 439537 = 329653) (by norm_num)
theorem B439573 : Blo 389765 439573 := bbase (se 6 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 439573 = 20605) (by norm_num)
theorem B439609 : Blo 389765 439609 := bbase (se 2 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 439609 = 329707) (by norm_num)
theorem B832837 : Blo 389765 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B2012485 : Blo 389765 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B2110805 : Blo 389765 2110805 := bbase (se 13 (by rfl) ⟨386, by rfl⟩ : syracuseStep 2110805 = 773) (by norm_num)
theorem B439645 : Blo 389765 439645 := bbase (se 3 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 439645 = 164867) (by norm_num)
theorem B439681 : Blo 389765 439681 := bbase (se 2 (by rfl) ⟨164880, by rfl⟩ : syracuseStep 439681 = 329761) (by norm_num)
theorem B439717 : Blo 389765 439717 := bbase (se 4 (by rfl) ⟨41223, by rfl⟩ : syracuseStep 439717 = 82447) (by norm_num)
theorem B439753 : Blo 389765 439753 := bbase (se 2 (by rfl) ⟨164907, by rfl⟩ : syracuseStep 439753 = 329815) (by norm_num)
theorem B636373 : Blo 389765 636373 := bbase (se 7 (by rfl) ⟨7457, by rfl⟩ : syracuseStep 636373 = 14915) (by norm_num)
theorem B439789 : Blo 389765 439789 := bbase (se 3 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 439789 = 164921) (by norm_num)
theorem B439825 : Blo 389765 439825 := bbase (se 2 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 439825 = 329869) (by norm_num)
theorem B1324565 : Blo 389765 1324565 := bbase (se 6 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 1324565 = 62089) (by norm_num)
theorem B439861 : Blo 389765 439861 := bbase (se 5 (by rfl) ⟨20618, by rfl⟩ : syracuseStep 439861 = 41237) (by norm_num)
theorem B439897 : Blo 389765 439897 := bbase (se 2 (by rfl) ⟨164961, by rfl⟩ : syracuseStep 439897 = 329923) (by norm_num)
theorem B439933 : Blo 389765 439933 := bbase (se 3 (by rfl) ⟨82487, by rfl⟩ : syracuseStep 439933 = 164975) (by norm_num)
theorem B439969 : Blo 389765 439969 := bbase (se 2 (by rfl) ⟨164988, by rfl⟩ : syracuseStep 439969 = 329977) (by norm_num)
theorem B1259189 : Blo 389765 1259189 := bbase (se 5 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 1259189 = 118049) (by norm_num)
theorem B833213 : Blo 389765 833213 := bbase (se 3 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 833213 = 312455) (by norm_num)
theorem B440005 : Blo 389765 440005 := bbase (se 4 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 440005 = 82501) (by norm_num)
theorem B440041 : Blo 389765 440041 := bbase (se 2 (by rfl) ⟨165015, by rfl⟩ : syracuseStep 440041 = 330031) (by norm_num)
theorem B472825 : Blo 389765 472825 := bbase (se 2 (by rfl) ⟨177309, by rfl⟩ : syracuseStep 472825 = 354619) (by norm_num)
theorem B440077 : Blo 389765 440077 := bbase (se 3 (by rfl) ⟨82514, by rfl⟩ : syracuseStep 440077 = 165029) (by norm_num)
theorem B440113 : Blo 389765 440113 := bbase (se 2 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 440113 = 330085) (by norm_num)
theorem B440149 : Blo 389765 440149 := bbase (se 9 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 440149 = 2579) (by norm_num)
theorem B1488725 : Blo 389765 1488725 := bbase (se 9 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 1488725 = 8723) (by norm_num)
theorem B669541 : Blo 389765 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B440185 : Blo 389765 440185 := bbase (se 2 (by rfl) ⟨165069, by rfl⟩ : syracuseStep 440185 = 330139) (by norm_num)
theorem B472969 : Blo 389765 472969 := bbase (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) (by norm_num)
theorem B2537365 : Blo 389765 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B440221 : Blo 389765 440221 := bbase (se 3 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 440221 = 165083) (by norm_num)
theorem B440257 : Blo 389765 440257 := bbase (se 2 (by rfl) ⟨165096, by rfl⟩ : syracuseStep 440257 = 330193) (by norm_num)
theorem B1324997 : Blo 389765 1324997 := bbase (se 4 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 1324997 = 248437) (by norm_num)
theorem B440293 : Blo 389765 440293 := bbase (se 4 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 440293 = 82555) (by norm_num)
theorem B604157 : Blo 389765 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B440329 : Blo 389765 440329 := bbase (se 2 (by rfl) ⟨165123, by rfl⟩ : syracuseStep 440329 = 330247) (by norm_num)
theorem B833581 : Blo 389765 833581 := bbase (se 3 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 833581 = 312593) (by norm_num)
theorem B440365 : Blo 389765 440365 := bbase (se 3 (by rfl) ⟨82568, by rfl⟩ : syracuseStep 440365 = 165137) (by norm_num)
theorem B440401 : Blo 389765 440401 := bbase (se 2 (by rfl) ⟨165150, by rfl⟩ : syracuseStep 440401 = 330301) (by norm_num)
theorem B440437 : Blo 389765 440437 := bbase (se 5 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 440437 = 41291) (by norm_num)
theorem B1489013 : Blo 389765 1489013 := bbase (se 5 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 1489013 = 139595) (by norm_num)
theorem B440473 : Blo 389765 440473 := bbase (se 2 (by rfl) ⟨165177, by rfl⟩ : syracuseStep 440473 = 330355) (by norm_num)
theorem B440509 : Blo 389765 440509 := bbase (se 3 (by rfl) ⟨82595, by rfl⟩ : syracuseStep 440509 = 165191) (by norm_num)
theorem B440545 : Blo 389765 440545 := bbase (se 2 (by rfl) ⟨165204, by rfl⟩ : syracuseStep 440545 = 330409) (by norm_num)
theorem B440581 : Blo 389765 440581 := bbase (se 4 (by rfl) ⟨41304, by rfl⟩ : syracuseStep 440581 = 82609) (by norm_num)
theorem B440617 : Blo 389765 440617 := bbase (se 2 (by rfl) ⟨165231, by rfl⟩ : syracuseStep 440617 = 330463) (by norm_num)
theorem B440653 : Blo 389765 440653 := bbase (se 3 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 440653 = 165245) (by norm_num)
theorem B1980773 : Blo 389765 1980773 := bbase (se 4 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 1980773 = 371395) (by norm_num)
theorem B440689 : Blo 389765 440689 := bbase (se 2 (by rfl) ⟨165258, by rfl⟩ : syracuseStep 440689 = 330517) (by norm_num)
theorem B1325429 : Blo 389765 1325429 := bbase (se 5 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 1325429 = 124259) (by norm_num)
theorem B440725 : Blo 389765 440725 := bbase (se 6 (by rfl) ⟨10329, by rfl⟩ : syracuseStep 440725 = 20659) (by norm_num)
theorem B440761 : Blo 389765 440761 := bbase (se 2 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 440761 = 330571) (by norm_num)
theorem B440797 : Blo 389765 440797 := bbase (se 3 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 440797 = 165299) (by norm_num)
theorem B440833 : Blo 389765 440833 := bbase (se 2 (by rfl) ⟨165312, by rfl⟩ : syracuseStep 440833 = 330625) (by norm_num)
theorem B440869 : Blo 389765 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B440905 : Blo 389765 440905 := bbase (se 2 (by rfl) ⟨165339, by rfl⟩ : syracuseStep 440905 = 330679) (by norm_num)
theorem B440941 : Blo 389765 440941 := bbase (se 3 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 440941 = 165353) (by norm_num)
theorem B440977 : Blo 389765 440977 := bbase (se 2 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 440977 = 330733) (by norm_num)
theorem B441013 : Blo 389765 441013 := bbase (se 5 (by rfl) ⟨20672, by rfl⟩ : syracuseStep 441013 = 41345) (by norm_num)
theorem B441049 : Blo 389765 441049 := bbase (se 2 (by rfl) ⟨165393, by rfl⟩ : syracuseStep 441049 = 330787) (by norm_num)
theorem B441085 : Blo 389765 441085 := bbase (se 3 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 441085 = 165407) (by norm_num)
theorem B3160853 : Blo 389765 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B441121 : Blo 389765 441121 := bbase (se 2 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 441121 = 330841) (by norm_num)
theorem B1325861 : Blo 389765 1325861 := bbase (se 4 (by rfl) ⟨124299, by rfl⟩ : syracuseStep 1325861 = 248599) (by norm_num)
theorem B441157 : Blo 389765 441157 := bbase (se 4 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 441157 = 82717) (by norm_num)
theorem B441193 : Blo 389765 441193 := bbase (se 2 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 441193 = 330895) (by norm_num)
theorem B1882997 : Blo 389765 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B441229 : Blo 389765 441229 := bbase (se 3 (by rfl) ⟨82730, by rfl⟩ : syracuseStep 441229 = 165461) (by norm_num)
theorem B441265 : Blo 389765 441265 := bbase (se 2 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 441265 = 330949) (by norm_num)
theorem B441301 : Blo 389765 441301 := bbase (se 7 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 441301 = 10343) (by norm_num)
theorem B441337 : Blo 389765 441337 := bbase (se 2 (by rfl) ⟨165501, by rfl⟩ : syracuseStep 441337 = 331003) (by norm_num)
theorem B441373 : Blo 389765 441373 := bbase (se 3 (by rfl) ⟨82757, by rfl⟩ : syracuseStep 441373 = 165515) (by norm_num)
theorem B1883189 : Blo 389765 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B441409 : Blo 389765 441409 := bbase (se 2 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 441409 = 331057) (by norm_num)
theorem B441445 : Blo 389765 441445 := bbase (se 4 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 441445 = 82771) (by norm_num)
theorem B441481 : Blo 389765 441481 := bbase (se 2 (by rfl) ⟨165555, by rfl⟩ : syracuseStep 441481 = 331111) (by norm_num)
theorem B441517 : Blo 389765 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B441553 : Blo 389765 441553 := bbase (se 2 (by rfl) ⟨165582, by rfl⟩ : syracuseStep 441553 = 331165) (by norm_num)
theorem B1326293 : Blo 389765 1326293 := bbase (se 7 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 1326293 = 31085) (by norm_num)
theorem B441589 : Blo 389765 441589 := bbase (se 5 (by rfl) ⟨20699, by rfl⟩ : syracuseStep 441589 = 41399) (by norm_num)
theorem B1490197 : Blo 389765 1490197 := bbase (se 6 (by rfl) ⟨34926, by rfl⟩ : syracuseStep 1490197 = 69853) (by norm_num)
theorem B441625 : Blo 389765 441625 := bbase (se 2 (by rfl) ⟨165609, by rfl⟩ : syracuseStep 441625 = 331219) (by norm_num)
theorem B441661 : Blo 389765 441661 := bbase (se 3 (by rfl) ⟨82811, by rfl⟩ : syracuseStep 441661 = 165623) (by norm_num)
theorem B441697 : Blo 389765 441697 := bbase (se 2 (by rfl) ⟨165636, by rfl⟩ : syracuseStep 441697 = 331273) (by norm_num)
theorem B441733 : Blo 389765 441733 := bbase (se 4 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 441733 = 82825) (by norm_num)
theorem B441769 : Blo 389765 441769 := bbase (se 2 (by rfl) ⟨165663, by rfl⟩ : syracuseStep 441769 = 331327) (by norm_num)
theorem B1883573 : Blo 389765 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B441805 : Blo 389765 441805 := bbase (se 3 (by rfl) ⟨82838, by rfl⟩ : syracuseStep 441805 = 165677) (by norm_num)
theorem B4996565 : Blo 389765 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B441841 : Blo 389765 441841 := bbase (se 2 (by rfl) ⟨165690, by rfl⟩ : syracuseStep 441841 = 331381) (by norm_num)
theorem B1261045 : Blo 389765 1261045 := bbase (se 5 (by rfl) ⟨59111, by rfl⟩ : syracuseStep 1261045 = 118223) (by norm_num)
theorem B835085 : Blo 389765 835085 := bbase (se 3 (by rfl) ⟨156578, by rfl⟩ : syracuseStep 835085 = 313157) (by norm_num)
theorem B441877 : Blo 389765 441877 := bbase (se 6 (by rfl) ⟨10356, by rfl⟩ : syracuseStep 441877 = 20713) (by norm_num)
theorem B441913 : Blo 389765 441913 := bbase (se 2 (by rfl) ⟨165717, by rfl⟩ : syracuseStep 441913 = 331435) (by norm_num)
theorem B1490501 : Blo 389765 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B441949 : Blo 389765 441949 := bbase (se 3 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 441949 = 165731) (by norm_num)
theorem B1982069 : Blo 389765 1982069 := bbase (se 5 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 1982069 = 185819) (by norm_num)
theorem B441985 : Blo 389765 441985 := bbase (se 2 (by rfl) ⟨165744, by rfl⟩ : syracuseStep 441985 = 331489) (by norm_num)
theorem B1326725 : Blo 389765 1326725 := bbase (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) (by norm_num)
theorem B835229 : Blo 389765 835229 := bbase (se 3 (by rfl) ⟨156605, by rfl⟩ : syracuseStep 835229 = 313211) (by norm_num)
theorem B442021 : Blo 389765 442021 := bbase (se 4 (by rfl) ⟨41439, by rfl⟩ : syracuseStep 442021 = 82879) (by norm_num)
theorem B442057 : Blo 389765 442057 := bbase (se 2 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 442057 = 331543) (by norm_num)
theorem B442093 : Blo 389765 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B442129 : Blo 389765 442129 := bbase (se 2 (by rfl) ⟨165798, by rfl⟩ : syracuseStep 442129 = 331597) (by norm_num)
theorem B442165 : Blo 389765 442165 := bbase (se 5 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 442165 = 41453) (by norm_num)
theorem B442201 : Blo 389765 442201 := bbase (se 2 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 442201 = 331651) (by norm_num)
theorem B442237 : Blo 389765 442237 := bbase (se 3 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 442237 = 165839) (by norm_num)
theorem B442273 : Blo 389765 442273 := bbase (se 2 (by rfl) ⟨165852, by rfl⟩ : syracuseStep 442273 = 331705) (by norm_num)
theorem B442309 : Blo 389765 442309 := bbase (se 4 (by rfl) ⟨41466, by rfl⟩ : syracuseStep 442309 = 82933) (by norm_num)
theorem B2015189 : Blo 389765 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B442345 : Blo 389765 442345 := bbase (se 2 (by rfl) ⟨165879, by rfl⟩ : syracuseStep 442345 = 331759) (by norm_num)
theorem B835589 : Blo 389765 835589 := bbase (se 4 (by rfl) ⟨78336, by rfl⟩ : syracuseStep 835589 = 156673) (by norm_num)
theorem B442381 : Blo 389765 442381 := bbase (se 3 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 442381 = 165893) (by norm_num)
theorem B507925 : Blo 389765 507925 := bbase (se 6 (by rfl) ⟨11904, by rfl⟩ : syracuseStep 507925 = 23809) (by norm_num)
theorem B442417 : Blo 389765 442417 := bbase (se 2 (by rfl) ⟨165906, by rfl⟩ : syracuseStep 442417 = 331813) (by norm_num)
theorem B1327157 : Blo 389765 1327157 := bbase (se 5 (by rfl) ⟨62210, by rfl⟩ : syracuseStep 1327157 = 124421) (by norm_num)
theorem B442453 : Blo 389765 442453 := bbase (se 8 (by rfl) ⟨2592, by rfl⟩ : syracuseStep 442453 = 5185) (by norm_num)
theorem B442489 : Blo 389765 442489 := bbase (se 2 (by rfl) ⟨165933, by rfl⟩ : syracuseStep 442489 = 331867) (by norm_num)
theorem B442525 : Blo 389765 442525 := bbase (se 3 (by rfl) ⟨82973, by rfl⟩ : syracuseStep 442525 = 165947) (by norm_num)
theorem B442561 : Blo 389765 442561 := bbase (se 2 (by rfl) ⟨165960, by rfl⟩ : syracuseStep 442561 = 331921) (by norm_num)
theorem B442597 : Blo 389765 442597 := bbase (se 4 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 442597 = 82987) (by norm_num)
theorem B442633 : Blo 389765 442633 := bbase (se 2 (by rfl) ⟨165987, by rfl⟩ : syracuseStep 442633 = 331975) (by norm_num)
theorem B442669 : Blo 389765 442669 := bbase (se 3 (by rfl) ⟨83000, by rfl⟩ : syracuseStep 442669 = 166001) (by norm_num)
theorem B1589557 : Blo 389765 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442705 : Blo 389765 442705 := bbase (se 2 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 442705 = 332029) (by norm_num)
theorem B442741 : Blo 389765 442741 := bbase (se 5 (by rfl) ⟨20753, by rfl⟩ : syracuseStep 442741 = 41507) (by norm_num)
theorem B1589653 : Blo 389765 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B442777 : Blo 389765 442777 := bbase (se 2 (by rfl) ⟨166041, by rfl⟩ : syracuseStep 442777 = 332083) (by norm_num)
theorem B442813 : Blo 389765 442813 := bbase (se 3 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 442813 = 166055) (by norm_num)
theorem B442849 : Blo 389765 442849 := bbase (se 2 (by rfl) ⟨166068, by rfl⟩ : syracuseStep 442849 = 332137) (by norm_num)
theorem B1327589 : Blo 389765 1327589 := bbase (se 4 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 1327589 = 248923) (by norm_num)
theorem B442885 : Blo 389765 442885 := bbase (se 4 (by rfl) ⟨41520, by rfl⟩ : syracuseStep 442885 = 83041) (by norm_num)
theorem B442921 : Blo 389765 442921 := bbase (se 2 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 442921 = 332191) (by norm_num)
theorem B442957 : Blo 389765 442957 := bbase (se 3 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 442957 = 166109) (by norm_num)
theorem B2507381 : Blo 389765 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B836477 : Blo 389765 836477 := bbase (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) (by norm_num)
theorem B1983365 : Blo 389765 1983365 := bbase (se 4 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 1983365 = 371881) (by norm_num)
theorem B672661 : Blo 389765 672661 := bbase (se 6 (by rfl) ⟨15765, by rfl⟩ : syracuseStep 672661 = 31531) (by norm_num)
theorem B1328021 : Blo 389765 1328021 := bbase (se 6 (by rfl) ⟨31125, by rfl⟩ : syracuseStep 1328021 = 62251) (by norm_num)
theorem B836725 : Blo 389765 836725 := bbase (se 5 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 836725 = 78443) (by norm_num)
theorem B1328453 : Blo 389765 1328453 := bbase (se 4 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 1328453 = 249085) (by norm_num)
theorem B2967029 : Blo 389765 2967029 := bbase (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) (by norm_num)
theorem B1590821 : Blo 389765 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B837229 : Blo 389765 837229 := bbase (se 3 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 837229 = 313961) (by norm_num)
theorem B1492613 : Blo 389765 1492613 := bbase (se 4 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 1492613 = 279865) (by norm_num)
theorem B706253 : Blo 389765 706253 := bbase (se 3 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 706253 = 264845) (by norm_num)
theorem B1328885 : Blo 389765 1328885 := bbase (se 5 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 1328885 = 124583) (by norm_num)
theorem B1492901 : Blo 389765 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1001605 : Blo 389765 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B1984661 : Blo 389765 1984661 := bbase (se 6 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 1984661 = 93031) (by norm_num)
theorem B2017493 : Blo 389765 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B838117 : Blo 389765 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B740117 : Blo 389765 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B445225 : Blo 389765 445225 := bbase (se 2 (by rfl) ⟨166959, by rfl⟩ : syracuseStep 445225 = 333919) (by norm_num)
theorem B1002341 : Blo 389765 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B2116469 : Blo 389765 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2378645 : Blo 389765 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B740269 : Blo 389765 740269 := bbase (se 3 (by rfl) ⟨138800, by rfl⟩ : syracuseStep 740269 = 277601) (by norm_num)
theorem B838613 : Blo 389765 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B3754997 : Blo 389765 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B2018357 : Blo 389765 2018357 := bbase (se 5 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 2018357 = 189221) (by norm_num)
theorem B1494085 : Blo 389765 1494085 := bbase (se 4 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 1494085 = 280141) (by norm_num)
theorem B707717 : Blo 389765 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B3591317 : Blo 389765 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B740573 : Blo 389765 740573 := bbase (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) (by norm_num)
theorem B2379029 : Blo 389765 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B1494389 : Blo 389765 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1985957 : Blo 389765 1985957 := bbase (se 4 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 1985957 = 372367) (by norm_num)
theorem B970181 : Blo 389765 970181 := bbase (se 4 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 970181 = 181909) (by norm_num)
theorem B445969 : Blo 389765 445969 := bbase (se 2 (by rfl) ⟨167238, by rfl⟩ : syracuseStep 445969 = 334477) (by norm_num)
theorem B1887877 : Blo 389765 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B839501 : Blo 389765 839501 := bbase (se 3 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 839501 = 314813) (by norm_num)
theorem B446357 : Blo 389765 446357 := bbase (se 6 (by rfl) ⟨10461, by rfl⟩ : syracuseStep 446357 = 20923) (by norm_num)
theorem B839621 : Blo 389765 839621 := bbase (se 4 (by rfl) ⟨78714, by rfl⟩ : syracuseStep 839621 = 157429) (by norm_num)
theorem B741325 : Blo 389765 741325 := bbase (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) (by norm_num)
theorem B741469 : Blo 389765 741469 := bbase (se 3 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 741469 = 278051) (by norm_num)
theorem B741629 : Blo 389765 741629 := bbase (se 3 (by rfl) ⟨139055, by rfl⟩ : syracuseStep 741629 = 278111) (by norm_num)
theorem B741773 : Blo 389765 741773 := bbase (se 3 (by rfl) ⟨139082, by rfl⟩ : syracuseStep 741773 = 278165) (by norm_num)
theorem B709021 : Blo 389765 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B709165 : Blo 389765 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B938557 : Blo 389765 938557 := bbase (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) (by norm_num)
theorem B840253 : Blo 389765 840253 := bbase (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) (by norm_num)
theorem B742061 : Blo 389765 742061 := bbase (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) (by norm_num)
theorem B1987253 : Blo 389765 1987253 := bbase (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) (by norm_num)
theorem B742213 : Blo 389765 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B7131989 : Blo 389765 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B709469 : Blo 389765 709469 := bbase (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) (by norm_num)
theorem B742517 : Blo 389765 742517 := bbase (se 5 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 742517 = 69611) (by norm_num)
theorem B11621717 : Blo 389765 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B743269 : Blo 389765 743269 := bbase (se 4 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 743269 = 139363) (by norm_num)
theorem B939941 : Blo 389765 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B1988549 : Blo 389765 1988549 := bbase (se 4 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 1988549 = 372853) (by norm_num)
theorem B743413 : Blo 389765 743413 := bbase (se 5 (by rfl) ⟨34847, by rfl⟩ : syracuseStep 743413 = 69695) (by norm_num)
theorem B2414645 : Blo 389765 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1595477 : Blo 389765 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B940133 : Blo 389765 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B743573 : Blo 389765 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B2513045 : Blo 389765 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B743717 : Blo 389765 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B744005 : Blo 389765 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B416449 : Blo 389765 416449 := bbase (se 2 (by rfl) ⟨156168, by rfl⟩ : syracuseStep 416449 = 312337) (by norm_num)
theorem B744157 : Blo 389765 744157 := bbase (se 3 (by rfl) ⟨139529, by rfl⟩ : syracuseStep 744157 = 279059) (by norm_num)
theorem B416521 : Blo 389765 416521 := bbase (se 2 (by rfl) ⟨156195, by rfl⟩ : syracuseStep 416521 = 312391) (by norm_num)
theorem B416701 : Blo 389765 416701 := bbase (se 3 (by rfl) ⟨78131, by rfl⟩ : syracuseStep 416701 = 156263) (by norm_num)
theorem B744461 : Blo 389765 744461 := bbase (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) (by norm_num)
theorem B1989845 : Blo 389765 1989845 := bbase (se 7 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 1989845 = 46637) (by norm_num)
theorem B417145 : Blo 389765 417145 := bbase (se 2 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 417145 = 312859) (by norm_num)
theorem B417269 : Blo 389765 417269 := bbase (se 5 (by rfl) ⟨19559, by rfl⟩ : syracuseStep 417269 = 39119) (by norm_num)
theorem B941701 : Blo 389765 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B483041 : Blo 389765 483041 := bbase (se 2 (by rfl) ⟨181140, by rfl⟩ : syracuseStep 483041 = 362281) (by norm_num)
theorem B417521 : Blo 389765 417521 := bbase (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) (by norm_num)
theorem B745213 : Blo 389765 745213 := bbase (se 3 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 745213 = 279455) (by norm_num)
theorem B5103445 : Blo 389765 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B745357 : Blo 389765 745357 := bbase (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) (by norm_num)
theorem B745517 : Blo 389765 745517 := bbase (se 3 (by rfl) ⟨139784, by rfl⟩ : syracuseStep 745517 = 279569) (by norm_num)
theorem B712837 : Blo 389765 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B417965 : Blo 389765 417965 := bbase (se 3 (by rfl) ⟨78368, by rfl⟩ : syracuseStep 417965 = 156737) (by norm_num)
theorem B745661 : Blo 389765 745661 := bbase (se 3 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 745661 = 279623) (by norm_num)
theorem B942317 : Blo 389765 942317 := bbase (se 3 (by rfl) ⟨176684, by rfl⟩ : syracuseStep 942317 = 353369) (by norm_num)
theorem B418213 : Blo 389765 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B877013 : Blo 389765 877013 := bbase (se 7 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 877013 = 20555) (by norm_num)
theorem B745949 : Blo 389765 745949 := bbase (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) (by norm_num)
theorem B1991141 : Blo 389765 1991141 := bbase (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) (by norm_num)
theorem B877085 : Blo 389765 877085 := bbase (se 3 (by rfl) ⟨164453, by rfl⟩ : syracuseStep 877085 = 328907) (by norm_num)
theorem B877157 : Blo 389765 877157 := bbase (se 4 (by rfl) ⟨82233, by rfl⟩ : syracuseStep 877157 = 164467) (by norm_num)
theorem B746101 : Blo 389765 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B877229 : Blo 389765 877229 := bbase (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) (by norm_num)
theorem B877301 : Blo 389765 877301 := bbase (se 5 (by rfl) ⟨41123, by rfl⟩ : syracuseStep 877301 = 82247) (by norm_num)
theorem B877373 : Blo 389765 877373 := bbase (se 3 (by rfl) ⟨164507, by rfl⟩ : syracuseStep 877373 = 329015) (by norm_num)
theorem B2253653 : Blo 389765 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B418657 : Blo 389765 418657 := bbase (se 2 (by rfl) ⟨156996, by rfl⟩ : syracuseStep 418657 = 313993) (by norm_num)
theorem B877445 : Blo 389765 877445 := bbase (se 4 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 877445 = 164521) (by norm_num)
theorem B418717 : Blo 389765 418717 := bbase (se 3 (by rfl) ⟨78509, by rfl⟩ : syracuseStep 418717 = 157019) (by norm_num)
theorem B746405 : Blo 389765 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B877517 : Blo 389765 877517 := bbase (se 3 (by rfl) ⟨164534, by rfl⟩ : syracuseStep 877517 = 329069) (by norm_num)
theorem B943093 : Blo 389765 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B877589 : Blo 389765 877589 := bbase (se 6 (by rfl) ⟨20568, by rfl⟩ : syracuseStep 877589 = 41137) (by norm_num)
theorem B2974805 : Blo 389765 2974805 := bbase (se 8 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 2974805 = 34861) (by norm_num)
theorem B877661 : Blo 389765 877661 := bbase (se 3 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 877661 = 329123) (by norm_num)
theorem B877733 : Blo 389765 877733 := bbase (se 4 (by rfl) ⟨82287, by rfl⟩ : syracuseStep 877733 = 164575) (by norm_num)
theorem B419033 : Blo 389765 419033 := bbase (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) (by norm_num)
theorem B877805 : Blo 389765 877805 := bbase (se 3 (by rfl) ⟨164588, by rfl⟩ : syracuseStep 877805 = 329177) (by norm_num)
theorem B877877 : Blo 389765 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B714101 : Blo 389765 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B877949 : Blo 389765 877949 := bbase (se 3 (by rfl) ⟨164615, by rfl⟩ : syracuseStep 877949 = 329231) (by norm_num)
theorem B878021 : Blo 389765 878021 := bbase (se 4 (by rfl) ⟨82314, by rfl⟩ : syracuseStep 878021 = 164629) (by norm_num)
theorem B878093 : Blo 389765 878093 := bbase (se 3 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 878093 = 329285) (by norm_num)
theorem B878165 : Blo 389765 878165 := bbase (se 8 (by rfl) ⟨5145, by rfl⟩ : syracuseStep 878165 = 10291) (by norm_num)
theorem B419477 : Blo 389765 419477 := bbase (se 6 (by rfl) ⟨9831, by rfl⟩ : syracuseStep 419477 = 19663) (by norm_num)
theorem B747157 : Blo 389765 747157 := bbase (se 6 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 747157 = 35023) (by norm_num)
theorem B878237 : Blo 389765 878237 := bbase (se 3 (by rfl) ⟨164669, by rfl⟩ : syracuseStep 878237 = 329339) (by norm_num)
theorem B943805 : Blo 389765 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B419537 : Blo 389765 419537 := bbase (se 2 (by rfl) ⟨157326, by rfl⟩ : syracuseStep 419537 = 314653) (by norm_num)
theorem B878309 : Blo 389765 878309 := bbase (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) (by norm_num)
theorem B1992437 : Blo 389765 1992437 := bbase (se 5 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 1992437 = 186791) (by norm_num)
theorem B747301 : Blo 389765 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B878381 : Blo 389765 878381 := bbase (se 3 (by rfl) ⟨164696, by rfl⟩ : syracuseStep 878381 = 329393) (by norm_num)
theorem B485185 : Blo 389765 485185 := bbase (se 2 (by rfl) ⟨181944, by rfl⟩ : syracuseStep 485185 = 363889) (by norm_num)
theorem B419665 : Blo 389765 419665 := bbase (se 2 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 419665 = 314749) (by norm_num)
theorem B878453 : Blo 389765 878453 := bbase (se 5 (by rfl) ⟨41177, by rfl⟩ : syracuseStep 878453 = 82355) (by norm_num)
theorem B878525 : Blo 389765 878525 := bbase (se 3 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 878525 = 329447) (by norm_num)
theorem B747461 : Blo 389765 747461 := bbase (se 4 (by rfl) ⟨70074, by rfl⟩ : syracuseStep 747461 = 140149) (by norm_num)
theorem B878597 : Blo 389765 878597 := bbase (se 4 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 878597 = 164737) (by norm_num)
theorem B878669 : Blo 389765 878669 := bbase (se 3 (by rfl) ⟨164750, by rfl⟩ : syracuseStep 878669 = 329501) (by norm_num)
theorem B2386037 : Blo 389765 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B878741 : Blo 389765 878741 := bbase (se 6 (by rfl) ⟨20595, by rfl⟩ : syracuseStep 878741 = 41191) (by norm_num)
theorem B3565781 : Blo 389765 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B878813 : Blo 389765 878813 := bbase (se 3 (by rfl) ⟨164777, by rfl⟩ : syracuseStep 878813 = 329555) (by norm_num)
theorem B420109 : Blo 389765 420109 := bbase (se 3 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 420109 = 157541) (by norm_num)
theorem B4483349 : Blo 389765 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B878885 : Blo 389765 878885 := bbase (se 4 (by rfl) ⟨82395, by rfl⟩ : syracuseStep 878885 = 164791) (by norm_num)
theorem B944477 : Blo 389765 944477 := bbase (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) (by norm_num)
theorem B878957 : Blo 389765 878957 := bbase (se 3 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 878957 = 329609) (by norm_num)
theorem B420229 : Blo 389765 420229 := bbase (se 4 (by rfl) ⟨39396, by rfl⟩ : syracuseStep 420229 = 78793) (by norm_num)
theorem B879029 : Blo 389765 879029 := bbase (se 5 (by rfl) ⟨41204, by rfl⟩ : syracuseStep 879029 = 82409) (by norm_num)
theorem B1272277 : Blo 389765 1272277 := bbase (se 7 (by rfl) ⟨14909, by rfl⟩ : syracuseStep 1272277 = 29819) (by norm_num)
theorem B879101 : Blo 389765 879101 := bbase (se 3 (by rfl) ⟨164831, by rfl⟩ : syracuseStep 879101 = 329663) (by norm_num)
theorem B879173 : Blo 389765 879173 := bbase (se 4 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 879173 = 164845) (by norm_num)
theorem B420481 : Blo 389765 420481 := bbase (se 2 (by rfl) ⟨157680, by rfl⟩ : syracuseStep 420481 = 315361) (by norm_num)
theorem B420485 : Blo 389765 420485 := bbase (se 4 (by rfl) ⟨39420, by rfl⟩ : syracuseStep 420485 = 78841) (by norm_num)
theorem B879245 : Blo 389765 879245 := bbase (se 3 (by rfl) ⟨164858, by rfl⟩ : syracuseStep 879245 = 329717) (by norm_num)
theorem B879317 : Blo 389765 879317 := bbase (se 7 (by rfl) ⟨10304, by rfl⟩ : syracuseStep 879317 = 20609) (by norm_num)
theorem B879389 : Blo 389765 879389 := bbase (se 3 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 879389 = 329771) (by norm_num)
theorem B879461 : Blo 389765 879461 := bbase (se 4 (by rfl) ⟨82449, by rfl⟩ : syracuseStep 879461 = 164899) (by norm_num)
theorem B879533 : Blo 389765 879533 := bbase (se 3 (by rfl) ⟨164912, by rfl⟩ : syracuseStep 879533 = 329825) (by norm_num)
theorem B584669 : Blo 389765 584669 := bbase (se 3 (by rfl) ⟨109625, by rfl⟩ : syracuseStep 584669 = 219251) (by norm_num)
theorem B584693 : Blo 389765 584693 := bbase (se 5 (by rfl) ⟨27407, by rfl⟩ : syracuseStep 584693 = 54815) (by norm_num)
theorem B879605 : Blo 389765 879605 := bbase (se 5 (by rfl) ⟨41231, by rfl⟩ : syracuseStep 879605 = 82463) (by norm_num)
theorem B584717 : Blo 389765 584717 := bbase (se 3 (by rfl) ⟨109634, by rfl⟩ : syracuseStep 584717 = 219269) (by norm_num)
theorem B1534997 : Blo 389765 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B584741 : Blo 389765 584741 := bbase (se 4 (by rfl) ⟨54819, by rfl⟩ : syracuseStep 584741 = 109639) (by norm_num)
theorem B584765 : Blo 389765 584765 := bbase (se 3 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 584765 = 219287) (by norm_num)
theorem B879677 : Blo 389765 879677 := bbase (se 3 (by rfl) ⟨164939, by rfl⟩ : syracuseStep 879677 = 329879) (by norm_num)
theorem B584789 : Blo 389765 584789 := bbase (se 8 (by rfl) ⟨3426, by rfl⟩ : syracuseStep 584789 = 6853) (by norm_num)
theorem B584813 : Blo 389765 584813 := bbase (se 3 (by rfl) ⟨109652, by rfl⟩ : syracuseStep 584813 = 219305) (by norm_num)
theorem B584837 : Blo 389765 584837 := bbase (se 4 (by rfl) ⟨54828, by rfl⟩ : syracuseStep 584837 = 109657) (by norm_num)
theorem B879749 : Blo 389765 879749 := bbase (se 4 (by rfl) ⟨82476, by rfl⟩ : syracuseStep 879749 = 164953) (by norm_num)
theorem B584861 : Blo 389765 584861 := bbase (se 3 (by rfl) ⟨109661, by rfl⟩ : syracuseStep 584861 = 219323) (by norm_num)
theorem B584885 : Blo 389765 584885 := bbase (se 5 (by rfl) ⟨27416, by rfl⟩ : syracuseStep 584885 = 54833) (by norm_num)
theorem B584909 : Blo 389765 584909 := bbase (se 3 (by rfl) ⟨109670, by rfl⟩ : syracuseStep 584909 = 219341) (by norm_num)
theorem B879821 : Blo 389765 879821 := bbase (se 3 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 879821 = 329933) (by norm_num)
theorem B584933 : Blo 389765 584933 := bbase (se 4 (by rfl) ⟨54837, by rfl⟩ : syracuseStep 584933 = 109675) (by norm_num)
theorem B584957 : Blo 389765 584957 := bbase (se 3 (by rfl) ⟨109679, by rfl⟩ : syracuseStep 584957 = 219359) (by norm_num)
theorem B584981 : Blo 389765 584981 := bbase (se 6 (by rfl) ⟨13710, by rfl⟩ : syracuseStep 584981 = 27421) (by norm_num)
theorem B879893 : Blo 389765 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B585005 : Blo 389765 585005 := bbase (se 3 (by rfl) ⟨109688, by rfl⟩ : syracuseStep 585005 = 219377) (by norm_num)
theorem B585029 : Blo 389765 585029 := bbase (se 4 (by rfl) ⟨54846, by rfl⟩ : syracuseStep 585029 = 109693) (by norm_num)
theorem B585053 : Blo 389765 585053 := bbase (se 3 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 585053 = 219395) (by norm_num)
theorem B879965 : Blo 389765 879965 := bbase (se 3 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 879965 = 329987) (by norm_num)
theorem B585077 : Blo 389765 585077 := bbase (se 5 (by rfl) ⟨27425, by rfl⟩ : syracuseStep 585077 = 54851) (by norm_num)
theorem B585101 : Blo 389765 585101 := bbase (se 3 (by rfl) ⟨109706, by rfl⟩ : syracuseStep 585101 = 219413) (by norm_num)
theorem B585125 : Blo 389765 585125 := bbase (se 4 (by rfl) ⟨54855, by rfl⟩ : syracuseStep 585125 = 109711) (by norm_num)
theorem B880037 : Blo 389765 880037 := bbase (se 4 (by rfl) ⟨82503, by rfl⟩ : syracuseStep 880037 = 165007) (by norm_num)
theorem B585149 : Blo 389765 585149 := bbase (se 3 (by rfl) ⟨109715, by rfl⟩ : syracuseStep 585149 = 219431) (by norm_num)
theorem B585173 : Blo 389765 585173 := bbase (se 7 (by rfl) ⟨6857, by rfl⟩ : syracuseStep 585173 = 13715) (by norm_num)
theorem B585197 : Blo 389765 585197 := bbase (se 3 (by rfl) ⟨109724, by rfl⟩ : syracuseStep 585197 = 219449) (by norm_num)
theorem B880109 : Blo 389765 880109 := bbase (se 3 (by rfl) ⟨165020, by rfl⟩ : syracuseStep 880109 = 330041) (by norm_num)
theorem B585221 : Blo 389765 585221 := bbase (se 4 (by rfl) ⟨54864, by rfl⟩ : syracuseStep 585221 = 109729) (by norm_num)
theorem B585245 : Blo 389765 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B585269 : Blo 389765 585269 := bbase (se 5 (by rfl) ⟨27434, by rfl⟩ : syracuseStep 585269 = 54869) (by norm_num)
theorem B880181 : Blo 389765 880181 := bbase (se 5 (by rfl) ⟨41258, by rfl⟩ : syracuseStep 880181 = 82517) (by norm_num)
theorem B585293 : Blo 389765 585293 := bbase (se 3 (by rfl) ⟨109742, by rfl⟩ : syracuseStep 585293 = 219485) (by norm_num)
theorem B585317 : Blo 389765 585317 := bbase (se 4 (by rfl) ⟨54873, by rfl⟩ : syracuseStep 585317 = 109747) (by norm_num)
theorem B585341 : Blo 389765 585341 := bbase (se 3 (by rfl) ⟨109751, by rfl⟩ : syracuseStep 585341 = 219503) (by norm_num)
theorem B880253 : Blo 389765 880253 := bbase (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) (by norm_num)
theorem B585365 : Blo 389765 585365 := bbase (se 6 (by rfl) ⟨13719, by rfl⟩ : syracuseStep 585365 = 27439) (by norm_num)
theorem B585389 : Blo 389765 585389 := bbase (se 3 (by rfl) ⟨109760, by rfl⟩ : syracuseStep 585389 = 219521) (by norm_num)
theorem B585413 : Blo 389765 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B880325 : Blo 389765 880325 := bbase (se 4 (by rfl) ⟨82530, by rfl⟩ : syracuseStep 880325 = 165061) (by norm_num)
theorem B585437 : Blo 389765 585437 := bbase (se 3 (by rfl) ⟨109769, by rfl⟩ : syracuseStep 585437 = 219539) (by norm_num)
theorem B585461 : Blo 389765 585461 := bbase (se 5 (by rfl) ⟨27443, by rfl⟩ : syracuseStep 585461 = 54887) (by norm_num)
theorem B585485 : Blo 389765 585485 := bbase (se 3 (by rfl) ⟨109778, by rfl⟩ : syracuseStep 585485 = 219557) (by norm_num)
theorem B880397 : Blo 389765 880397 := bbase (se 3 (by rfl) ⟨165074, by rfl⟩ : syracuseStep 880397 = 330149) (by norm_num)
theorem B585509 : Blo 389765 585509 := bbase (se 4 (by rfl) ⟨54891, by rfl⟩ : syracuseStep 585509 = 109783) (by norm_num)
theorem B585533 : Blo 389765 585533 := bbase (se 3 (by rfl) ⟨109787, by rfl⟩ : syracuseStep 585533 = 219575) (by norm_num)
theorem B585557 : Blo 389765 585557 := bbase (se 9 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 585557 = 3431) (by norm_num)
theorem B880469 : Blo 389765 880469 := bbase (se 9 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 880469 = 5159) (by norm_num)
theorem B585581 : Blo 389765 585581 := bbase (se 3 (by rfl) ⟨109796, by rfl⟩ : syracuseStep 585581 = 219593) (by norm_num)
theorem B585605 : Blo 389765 585605 := bbase (se 4 (by rfl) ⟨54900, by rfl⟩ : syracuseStep 585605 = 109801) (by norm_num)
theorem B585629 : Blo 389765 585629 := bbase (se 3 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 585629 = 219611) (by norm_num)
theorem B880541 : Blo 389765 880541 := bbase (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) (by norm_num)
theorem B585653 : Blo 389765 585653 := bbase (se 5 (by rfl) ⟨27452, by rfl⟩ : syracuseStep 585653 = 54905) (by norm_num)
theorem B585677 : Blo 389765 585677 := bbase (se 3 (by rfl) ⟨109814, by rfl⟩ : syracuseStep 585677 = 219629) (by norm_num)
theorem B1142741 : Blo 389765 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B585701 : Blo 389765 585701 := bbase (se 4 (by rfl) ⟨54909, by rfl⟩ : syracuseStep 585701 = 109819) (by norm_num)
theorem B880613 : Blo 389765 880613 := bbase (se 4 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 880613 = 165115) (by norm_num)
theorem B585725 : Blo 389765 585725 := bbase (se 3 (by rfl) ⟨109823, by rfl⟩ : syracuseStep 585725 = 219647) (by norm_num)
theorem B585749 : Blo 389765 585749 := bbase (se 6 (by rfl) ⟨13728, by rfl⟩ : syracuseStep 585749 = 27457) (by norm_num)
theorem B585773 : Blo 389765 585773 := bbase (se 3 (by rfl) ⟨109832, by rfl⟩ : syracuseStep 585773 = 219665) (by norm_num)
theorem B880685 : Blo 389765 880685 := bbase (se 3 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 880685 = 330257) (by norm_num)
theorem B454717 : Blo 389765 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B585797 : Blo 389765 585797 := bbase (se 4 (by rfl) ⟨54918, by rfl⟩ : syracuseStep 585797 = 109837) (by norm_num)
theorem B585821 : Blo 389765 585821 := bbase (se 3 (by rfl) ⟨109841, by rfl⟩ : syracuseStep 585821 = 219683) (by norm_num)
theorem B585845 : Blo 389765 585845 := bbase (se 5 (by rfl) ⟨27461, by rfl⟩ : syracuseStep 585845 = 54923) (by norm_num)
theorem B880757 : Blo 389765 880757 := bbase (se 5 (by rfl) ⟨41285, by rfl⟩ : syracuseStep 880757 = 82571) (by norm_num)
theorem B585869 : Blo 389765 585869 := bbase (se 3 (by rfl) ⟨109850, by rfl⟩ : syracuseStep 585869 = 219701) (by norm_num)
theorem B585893 : Blo 389765 585893 := bbase (se 4 (by rfl) ⟨54927, by rfl⟩ : syracuseStep 585893 = 109855) (by norm_num)
theorem B585917 : Blo 389765 585917 := bbase (se 3 (by rfl) ⟨109859, by rfl⟩ : syracuseStep 585917 = 219719) (by norm_num)
theorem B880829 : Blo 389765 880829 := bbase (se 3 (by rfl) ⟨165155, by rfl⟩ : syracuseStep 880829 = 330311) (by norm_num)
theorem B585941 : Blo 389765 585941 := bbase (se 7 (by rfl) ⟨6866, by rfl⟩ : syracuseStep 585941 = 13733) (by norm_num)
theorem B585965 : Blo 389765 585965 := bbase (se 3 (by rfl) ⟨109868, by rfl⟩ : syracuseStep 585965 = 219737) (by norm_num)
theorem B585989 : Blo 389765 585989 := bbase (se 4 (by rfl) ⟨54936, by rfl⟩ : syracuseStep 585989 = 109873) (by norm_num)
theorem B880901 : Blo 389765 880901 := bbase (se 4 (by rfl) ⟨82584, by rfl⟩ : syracuseStep 880901 = 165169) (by norm_num)
theorem B586013 : Blo 389765 586013 := bbase (se 3 (by rfl) ⟨109877, by rfl⟩ : syracuseStep 586013 = 219755) (by norm_num)
theorem B586037 : Blo 389765 586037 := bbase (se 5 (by rfl) ⟨27470, by rfl⟩ : syracuseStep 586037 = 54941) (by norm_num)
theorem B586061 : Blo 389765 586061 := bbase (se 3 (by rfl) ⟨109886, by rfl⟩ : syracuseStep 586061 = 219773) (by norm_num)
theorem B880973 : Blo 389765 880973 := bbase (se 3 (by rfl) ⟨165182, by rfl⟩ : syracuseStep 880973 = 330365) (by norm_num)
theorem B586085 : Blo 389765 586085 := bbase (se 4 (by rfl) ⟨54945, by rfl⟩ : syracuseStep 586085 = 109891) (by norm_num)
theorem B586109 : Blo 389765 586109 := bbase (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) (by norm_num)
theorem B586133 : Blo 389765 586133 := bbase (se 6 (by rfl) ⟨13737, by rfl⟩ : syracuseStep 586133 = 27475) (by norm_num)
theorem B881045 : Blo 389765 881045 := bbase (se 6 (by rfl) ⟨20649, by rfl⟩ : syracuseStep 881045 = 41299) (by norm_num)
theorem B586157 : Blo 389765 586157 := bbase (se 3 (by rfl) ⟨109904, by rfl⟩ : syracuseStep 586157 = 219809) (by norm_num)
theorem B586181 : Blo 389765 586181 := bbase (se 4 (by rfl) ⟨54954, by rfl⟩ : syracuseStep 586181 = 109909) (by norm_num)
theorem B586205 : Blo 389765 586205 := bbase (se 3 (by rfl) ⟨109913, by rfl⟩ : syracuseStep 586205 = 219827) (by norm_num)
theorem B881117 : Blo 389765 881117 := bbase (se 3 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 881117 = 330419) (by norm_num)
theorem B1667573 : Blo 389765 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B586229 : Blo 389765 586229 := bbase (se 5 (by rfl) ⟨27479, by rfl⟩ : syracuseStep 586229 = 54959) (by norm_num)
theorem B586253 : Blo 389765 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B586277 : Blo 389765 586277 := bbase (se 4 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 586277 = 109927) (by norm_num)
theorem B881189 : Blo 389765 881189 := bbase (se 4 (by rfl) ⟨82611, by rfl⟩ : syracuseStep 881189 = 165223) (by norm_num)
theorem B586301 : Blo 389765 586301 := bbase (se 3 (by rfl) ⟨109931, by rfl⟩ : syracuseStep 586301 = 219863) (by norm_num)
theorem B586325 : Blo 389765 586325 := bbase (se 8 (by rfl) ⟨3435, by rfl⟩ : syracuseStep 586325 = 6871) (by norm_num)
theorem B586349 : Blo 389765 586349 := bbase (se 3 (by rfl) ⟨109940, by rfl⟩ : syracuseStep 586349 = 219881) (by norm_num)
theorem B881261 : Blo 389765 881261 := bbase (se 3 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 881261 = 330473) (by norm_num)
theorem B586373 : Blo 389765 586373 := bbase (se 4 (by rfl) ⟨54972, by rfl⟩ : syracuseStep 586373 = 109945) (by norm_num)
theorem B586397 : Blo 389765 586397 := bbase (se 3 (by rfl) ⟨109949, by rfl⟩ : syracuseStep 586397 = 219899) (by norm_num)
theorem B586421 : Blo 389765 586421 := bbase (se 5 (by rfl) ⟨27488, by rfl⟩ : syracuseStep 586421 = 54977) (by norm_num)
theorem B881333 : Blo 389765 881333 := bbase (se 5 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 881333 = 82625) (by norm_num)
theorem B750277 : Blo 389765 750277 := bbase (se 4 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 750277 = 140677) (by norm_num)
theorem B586445 : Blo 389765 586445 := bbase (se 3 (by rfl) ⟨109958, by rfl⟩ : syracuseStep 586445 = 219917) (by norm_num)
theorem B586469 : Blo 389765 586469 := bbase (se 4 (by rfl) ⟨54981, by rfl⟩ : syracuseStep 586469 = 109963) (by norm_num)
theorem B586493 : Blo 389765 586493 := bbase (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) (by norm_num)
theorem B881405 : Blo 389765 881405 := bbase (se 3 (by rfl) ⟨165263, by rfl⟩ : syracuseStep 881405 = 330527) (by norm_num)
theorem B1667861 : Blo 389765 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B586517 : Blo 389765 586517 := bbase (se 6 (by rfl) ⟨13746, by rfl⟩ : syracuseStep 586517 = 27493) (by norm_num)
theorem B586541 : Blo 389765 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B586565 : Blo 389765 586565 := bbase (se 4 (by rfl) ⟨54990, by rfl⟩ : syracuseStep 586565 = 109981) (by norm_num)
theorem B881477 : Blo 389765 881477 := bbase (se 4 (by rfl) ⟨82638, by rfl⟩ : syracuseStep 881477 = 165277) (by norm_num)
theorem B586589 : Blo 389765 586589 := bbase (se 3 (by rfl) ⟨109985, by rfl⟩ : syracuseStep 586589 = 219971) (by norm_num)
theorem B586613 : Blo 389765 586613 := bbase (se 5 (by rfl) ⟨27497, by rfl⟩ : syracuseStep 586613 = 54995) (by norm_num)
theorem B586637 : Blo 389765 586637 := bbase (se 3 (by rfl) ⟨109994, by rfl⟩ : syracuseStep 586637 = 219989) (by norm_num)
theorem B881549 : Blo 389765 881549 := bbase (se 3 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 881549 = 330581) (by norm_num)
theorem B586661 : Blo 389765 586661 := bbase (se 4 (by rfl) ⟨54999, by rfl⟩ : syracuseStep 586661 = 109999) (by norm_num)
theorem B586685 : Blo 389765 586685 := bbase (se 3 (by rfl) ⟨110003, by rfl⟩ : syracuseStep 586685 = 220007) (by norm_num)
theorem B586709 : Blo 389765 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B881621 : Blo 389765 881621 := bbase (se 7 (by rfl) ⟨10331, by rfl⟩ : syracuseStep 881621 = 20663) (by norm_num)
theorem B586733 : Blo 389765 586733 := bbase (se 3 (by rfl) ⟨110012, by rfl⟩ : syracuseStep 586733 = 220025) (by norm_num)
theorem B586757 : Blo 389765 586757 := bbase (se 4 (by rfl) ⟨55008, by rfl⟩ : syracuseStep 586757 = 110017) (by norm_num)
theorem B586781 : Blo 389765 586781 := bbase (se 3 (by rfl) ⟨110021, by rfl⟩ : syracuseStep 586781 = 220043) (by norm_num)
theorem B881693 : Blo 389765 881693 := bbase (se 3 (by rfl) ⟨165317, by rfl⟩ : syracuseStep 881693 = 330635) (by norm_num)
theorem B586805 : Blo 389765 586805 := bbase (se 5 (by rfl) ⟨27506, by rfl⟩ : syracuseStep 586805 = 55013) (by norm_num)
theorem B586829 : Blo 389765 586829 := bbase (se 3 (by rfl) ⟨110030, by rfl⟩ : syracuseStep 586829 = 220061) (by norm_num)
theorem B423001 : Blo 389765 423001 := bbase (se 2 (by rfl) ⟨158625, by rfl⟩ : syracuseStep 423001 = 317251) (by norm_num)
theorem B586853 : Blo 389765 586853 := bbase (se 4 (by rfl) ⟨55017, by rfl⟩ : syracuseStep 586853 = 110035) (by norm_num)
theorem B881765 : Blo 389765 881765 := bbase (se 4 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 881765 = 165331) (by norm_num)
theorem B586877 : Blo 389765 586877 := bbase (se 3 (by rfl) ⟨110039, by rfl⟩ : syracuseStep 586877 = 220079) (by norm_num)
theorem B3339413 : Blo 389765 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B586901 : Blo 389765 586901 := bbase (se 6 (by rfl) ⟨13755, by rfl⟩ : syracuseStep 586901 = 27511) (by norm_num)
theorem B586925 : Blo 389765 586925 := bbase (se 3 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 586925 = 220097) (by norm_num)
theorem B881837 : Blo 389765 881837 := bbase (se 3 (by rfl) ⟨165344, by rfl⟩ : syracuseStep 881837 = 330689) (by norm_num)
theorem B586949 : Blo 389765 586949 := bbase (se 4 (by rfl) ⟨55026, by rfl⟩ : syracuseStep 586949 = 110053) (by norm_num)
theorem B586973 : Blo 389765 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B586997 : Blo 389765 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B881909 : Blo 389765 881909 := bbase (se 5 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 881909 = 82679) (by norm_num)
theorem B587021 : Blo 389765 587021 := bbase (se 3 (by rfl) ⟨110066, by rfl⟩ : syracuseStep 587021 = 220133) (by norm_num)
theorem B587045 : Blo 389765 587045 := bbase (se 4 (by rfl) ⟨55035, by rfl⟩ : syracuseStep 587045 = 110071) (by norm_num)
theorem B587069 : Blo 389765 587069 := bbase (se 3 (by rfl) ⟨110075, by rfl⟩ : syracuseStep 587069 = 220151) (by norm_num)
theorem B881981 : Blo 389765 881981 := bbase (se 3 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 881981 = 330743) (by norm_num)
theorem B587093 : Blo 389765 587093 := bbase (se 13 (by rfl) ⟨107, by rfl⟩ : syracuseStep 587093 = 215) (by norm_num)
theorem B587117 : Blo 389765 587117 := bbase (se 3 (by rfl) ⟨110084, by rfl⟩ : syracuseStep 587117 = 220169) (by norm_num)
theorem B587141 : Blo 389765 587141 := bbase (se 4 (by rfl) ⟨55044, by rfl⟩ : syracuseStep 587141 = 110089) (by norm_num)
theorem B882053 : Blo 389765 882053 := bbase (se 4 (by rfl) ⟨82692, by rfl⟩ : syracuseStep 882053 = 165385) (by norm_num)
theorem B587165 : Blo 389765 587165 := bbase (se 3 (by rfl) ⟨110093, by rfl⟩ : syracuseStep 587165 = 220187) (by norm_num)
theorem B587189 : Blo 389765 587189 := bbase (se 5 (by rfl) ⟨27524, by rfl⟩ : syracuseStep 587189 = 55049) (by norm_num)
theorem B587213 : Blo 389765 587213 := bbase (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) (by norm_num)
theorem B882125 : Blo 389765 882125 := bbase (se 3 (by rfl) ⟨165398, by rfl⟩ : syracuseStep 882125 = 330797) (by norm_num)
theorem B587237 : Blo 389765 587237 := bbase (se 4 (by rfl) ⟨55053, by rfl⟩ : syracuseStep 587237 = 110107) (by norm_num)
theorem B718309 : Blo 389765 718309 := bbase (se 4 (by rfl) ⟨67341, by rfl⟩ : syracuseStep 718309 = 134683) (by norm_num)
theorem B587261 : Blo 389765 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B1668613 : Blo 389765 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B587285 : Blo 389765 587285 := bbase (se 6 (by rfl) ⟨13764, by rfl⟩ : syracuseStep 587285 = 27529) (by norm_num)
theorem B882197 : Blo 389765 882197 := bbase (se 6 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 882197 = 41353) (by norm_num)
theorem B751141 : Blo 389765 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B1111589 : Blo 389765 1111589 := bbase (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) (by norm_num)
theorem B587309 : Blo 389765 587309 := bbase (se 3 (by rfl) ⟨110120, by rfl⟩ : syracuseStep 587309 = 220241) (by norm_num)
theorem B587333 : Blo 389765 587333 := bbase (se 4 (by rfl) ⟨55062, by rfl⟩ : syracuseStep 587333 = 110125) (by norm_num)
theorem B423517 : Blo 389765 423517 := bbase (se 3 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 423517 = 158819) (by norm_num)
theorem B587357 : Blo 389765 587357 := bbase (se 3 (by rfl) ⟨110129, by rfl⟩ : syracuseStep 587357 = 220259) (by norm_num)
theorem B882269 : Blo 389765 882269 := bbase (se 3 (by rfl) ⟨165425, by rfl⟩ : syracuseStep 882269 = 330851) (by norm_num)
theorem B587381 : Blo 389765 587381 := bbase (se 5 (by rfl) ⟨27533, by rfl⟩ : syracuseStep 587381 = 55067) (by norm_num)
theorem B587405 : Blo 389765 587405 := bbase (se 3 (by rfl) ⟨110138, by rfl⟩ : syracuseStep 587405 = 220277) (by norm_num)
theorem B390809 : Blo 389765 390809 := bbase (se 2 (by rfl) ⟨146553, by rfl⟩ : syracuseStep 390809 = 293107) (by norm_num)
theorem B587429 : Blo 389765 587429 := bbase (se 4 (by rfl) ⟨55071, by rfl⟩ : syracuseStep 587429 = 110143) (by norm_num)
theorem B882341 : Blo 389765 882341 := bbase (se 4 (by rfl) ⟨82719, by rfl⟩ : syracuseStep 882341 = 165439) (by norm_num)
theorem B2127541 : Blo 389765 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B587453 : Blo 389765 587453 := bbase (se 3 (by rfl) ⟨110147, by rfl⟩ : syracuseStep 587453 = 220295) (by norm_num)
theorem B587477 : Blo 389765 587477 := bbase (se 7 (by rfl) ⟨6884, by rfl⟩ : syracuseStep 587477 = 13769) (by norm_num)
theorem B587501 : Blo 389765 587501 := bbase (se 3 (by rfl) ⟨110156, by rfl⟩ : syracuseStep 587501 = 220313) (by norm_num)
theorem B882413 : Blo 389765 882413 := bbase (se 3 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 882413 = 330905) (by norm_num)
theorem B587525 : Blo 389765 587525 := bbase (se 4 (by rfl) ⟨55080, by rfl⟩ : syracuseStep 587525 = 110161) (by norm_num)
theorem B587549 : Blo 389765 587549 := bbase (se 3 (by rfl) ⟨110165, by rfl⟩ : syracuseStep 587549 = 220331) (by norm_num)
theorem B849709 : Blo 389765 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B587573 : Blo 389765 587573 := bbase (se 5 (by rfl) ⟨27542, by rfl⟩ : syracuseStep 587573 = 55085) (by norm_num)
theorem B882485 : Blo 389765 882485 := bbase (se 5 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 882485 = 82733) (by norm_num)
theorem B587597 : Blo 389765 587597 := bbase (se 3 (by rfl) ⟨110174, by rfl⟩ : syracuseStep 587597 = 220349) (by norm_num)
theorem B587621 : Blo 389765 587621 := bbase (se 4 (by rfl) ⟨55089, by rfl⟩ : syracuseStep 587621 = 110179) (by norm_num)
theorem B587645 : Blo 389765 587645 := bbase (se 3 (by rfl) ⟨110183, by rfl⟩ : syracuseStep 587645 = 220367) (by norm_num)
theorem B882557 : Blo 389765 882557 := bbase (se 3 (by rfl) ⟨165479, by rfl⟩ : syracuseStep 882557 = 330959) (by norm_num)
theorem B587669 : Blo 389765 587669 := bbase (se 6 (by rfl) ⟨13773, by rfl⟩ : syracuseStep 587669 = 27547) (by norm_num)
theorem B587693 : Blo 389765 587693 := bbase (se 3 (by rfl) ⟨110192, by rfl⟩ : syracuseStep 587693 = 220385) (by norm_num)
theorem B587717 : Blo 389765 587717 := bbase (se 4 (by rfl) ⟨55098, by rfl⟩ : syracuseStep 587717 = 110197) (by norm_num)
theorem B882629 : Blo 389765 882629 := bbase (se 4 (by rfl) ⟨82746, by rfl⟩ : syracuseStep 882629 = 165493) (by norm_num)
theorem B587741 : Blo 389765 587741 := bbase (se 3 (by rfl) ⟨110201, by rfl⟩ : syracuseStep 587741 = 220403) (by norm_num)
theorem B587765 : Blo 389765 587765 := bbase (se 5 (by rfl) ⟨27551, by rfl⟩ : syracuseStep 587765 = 55103) (by norm_num)
theorem B587789 : Blo 389765 587789 := bbase (se 3 (by rfl) ⟨110210, by rfl⟩ : syracuseStep 587789 = 220421) (by norm_num)
theorem B882701 : Blo 389765 882701 := bbase (se 3 (by rfl) ⟨165506, by rfl⟩ : syracuseStep 882701 = 331013) (by norm_num)
theorem B587813 : Blo 389765 587813 := bbase (se 4 (by rfl) ⟨55107, by rfl⟩ : syracuseStep 587813 = 110215) (by norm_num)
theorem B587837 : Blo 389765 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B587861 : Blo 389765 587861 := bbase (se 8 (by rfl) ⟨3444, by rfl⟩ : syracuseStep 587861 = 6889) (by norm_num)
theorem B882773 : Blo 389765 882773 := bbase (se 8 (by rfl) ⟨5172, by rfl⟩ : syracuseStep 882773 = 10345) (by norm_num)
theorem B587885 : Blo 389765 587885 := bbase (se 3 (by rfl) ⟨110228, by rfl⟩ : syracuseStep 587885 = 220457) (by norm_num)
theorem B587909 : Blo 389765 587909 := bbase (se 4 (by rfl) ⟨55116, by rfl⟩ : syracuseStep 587909 = 110233) (by norm_num)
theorem B587933 : Blo 389765 587933 := bbase (se 3 (by rfl) ⟨110237, by rfl⟩ : syracuseStep 587933 = 220475) (by norm_num)
theorem B882845 : Blo 389765 882845 := bbase (se 3 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 882845 = 331067) (by norm_num)
theorem B587957 : Blo 389765 587957 := bbase (se 5 (by rfl) ⟨27560, by rfl⟩ : syracuseStep 587957 = 55121) (by norm_num)
theorem B587981 : Blo 389765 587981 := bbase (se 3 (by rfl) ⟨110246, by rfl⟩ : syracuseStep 587981 = 220493) (by norm_num)
theorem B1669349 : Blo 389765 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B588005 : Blo 389765 588005 := bbase (se 4 (by rfl) ⟨55125, by rfl⟩ : syracuseStep 588005 = 110251) (by norm_num)
theorem B882917 : Blo 389765 882917 := bbase (se 4 (by rfl) ⟨82773, by rfl⟩ : syracuseStep 882917 = 165547) (by norm_num)
theorem B588029 : Blo 389765 588029 := bbase (se 3 (by rfl) ⟨110255, by rfl⟩ : syracuseStep 588029 = 220511) (by norm_num)
theorem B588053 : Blo 389765 588053 := bbase (se 6 (by rfl) ⟨13782, by rfl⟩ : syracuseStep 588053 = 27565) (by norm_num)
theorem B555293 : Blo 389765 555293 := bbase (se 3 (by rfl) ⟨104117, by rfl⟩ : syracuseStep 555293 = 208235) (by norm_num)
theorem B588077 : Blo 389765 588077 := bbase (se 3 (by rfl) ⟨110264, by rfl⟩ : syracuseStep 588077 = 220529) (by norm_num)
theorem B882989 : Blo 389765 882989 := bbase (se 3 (by rfl) ⟨165560, by rfl⟩ : syracuseStep 882989 = 331121) (by norm_num)
theorem B588101 : Blo 389765 588101 := bbase (se 4 (by rfl) ⟨55134, by rfl⟩ : syracuseStep 588101 = 110269) (by norm_num)
theorem B588125 : Blo 389765 588125 := bbase (se 3 (by rfl) ⟨110273, by rfl⟩ : syracuseStep 588125 = 220547) (by norm_num)
theorem B555373 : Blo 389765 555373 := bbase (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) (by norm_num)
theorem B588149 : Blo 389765 588149 := bbase (se 5 (by rfl) ⟨27569, by rfl⟩ : syracuseStep 588149 = 55139) (by norm_num)
theorem B883061 : Blo 389765 883061 := bbase (se 5 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 883061 = 82787) (by norm_num)
theorem B588173 : Blo 389765 588173 := bbase (se 3 (by rfl) ⟨110282, by rfl⟩ : syracuseStep 588173 = 220565) (by norm_num)
theorem B588197 : Blo 389765 588197 := bbase (se 4 (by rfl) ⟨55143, by rfl⟩ : syracuseStep 588197 = 110287) (by norm_num)
theorem B588221 : Blo 389765 588221 := bbase (se 3 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 588221 = 220583) (by norm_num)
theorem B883133 : Blo 389765 883133 := bbase (se 3 (by rfl) ⟨165587, by rfl⟩ : syracuseStep 883133 = 331175) (by norm_num)
theorem B588245 : Blo 389765 588245 := bbase (se 7 (by rfl) ⟨6893, by rfl⟩ : syracuseStep 588245 = 13787) (by norm_num)
theorem B555493 : Blo 389765 555493 := bbase (se 4 (by rfl) ⟨52077, by rfl⟩ : syracuseStep 555493 = 104155) (by norm_num)
theorem B588269 : Blo 389765 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B588293 : Blo 389765 588293 := bbase (se 4 (by rfl) ⟨55152, by rfl⟩ : syracuseStep 588293 = 110305) (by norm_num)
theorem B883205 : Blo 389765 883205 := bbase (se 4 (by rfl) ⟨82800, by rfl⟩ : syracuseStep 883205 = 165601) (by norm_num)
theorem B588317 : Blo 389765 588317 := bbase (se 3 (by rfl) ⟨110309, by rfl⟩ : syracuseStep 588317 = 220619) (by norm_num)
theorem B588341 : Blo 389765 588341 := bbase (se 5 (by rfl) ⟨27578, by rfl⟩ : syracuseStep 588341 = 55157) (by norm_num)
theorem B555589 : Blo 389765 555589 := bbase (se 4 (by rfl) ⟨52086, by rfl⟩ : syracuseStep 555589 = 104173) (by norm_num)
theorem B424525 : Blo 389765 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B588365 : Blo 389765 588365 := bbase (se 3 (by rfl) ⟨110318, by rfl⟩ : syracuseStep 588365 = 220637) (by norm_num)
theorem B883277 : Blo 389765 883277 := bbase (se 3 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 883277 = 331229) (by norm_num)
theorem B588389 : Blo 389765 588389 := bbase (se 4 (by rfl) ⟨55161, by rfl⟩ : syracuseStep 588389 = 110323) (by norm_num)
theorem B588413 : Blo 389765 588413 := bbase (se 3 (by rfl) ⟨110327, by rfl⟩ : syracuseStep 588413 = 220655) (by norm_num)
theorem B588437 : Blo 389765 588437 := bbase (se 6 (by rfl) ⟨13791, by rfl⟩ : syracuseStep 588437 = 27583) (by norm_num)
theorem B883349 : Blo 389765 883349 := bbase (se 6 (by rfl) ⟨20703, by rfl⟩ : syracuseStep 883349 = 41407) (by norm_num)
theorem B588461 : Blo 389765 588461 := bbase (se 3 (by rfl) ⟨110336, by rfl⟩ : syracuseStep 588461 = 220673) (by norm_num)
theorem B1112773 : Blo 389765 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B588485 : Blo 389765 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B588509 : Blo 389765 588509 := bbase (se 3 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 588509 = 220691) (by norm_num)
theorem B883421 : Blo 389765 883421 := bbase (se 3 (by rfl) ⟨165641, by rfl⟩ : syracuseStep 883421 = 331283) (by norm_num)
theorem B588533 : Blo 389765 588533 := bbase (se 5 (by rfl) ⟨27587, by rfl⟩ : syracuseStep 588533 = 55175) (by norm_num)
theorem B588557 : Blo 389765 588557 := bbase (se 3 (by rfl) ⟨110354, by rfl⟩ : syracuseStep 588557 = 220709) (by norm_num)
theorem B588581 : Blo 389765 588581 := bbase (se 4 (by rfl) ⟨55179, by rfl⟩ : syracuseStep 588581 = 110359) (by norm_num)
theorem B883493 : Blo 389765 883493 := bbase (se 4 (by rfl) ⟨82827, by rfl⟩ : syracuseStep 883493 = 165655) (by norm_num)
theorem B588605 : Blo 389765 588605 := bbase (se 3 (by rfl) ⟨110363, by rfl⟩ : syracuseStep 588605 = 220727) (by norm_num)
theorem B1604437 : Blo 389765 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B588629 : Blo 389765 588629 := bbase (se 9 (by rfl) ⟨1724, by rfl⟩ : syracuseStep 588629 = 3449) (by norm_num)
theorem B1112933 : Blo 389765 1112933 := bbase (se 4 (by rfl) ⟨104337, by rfl⟩ : syracuseStep 1112933 = 208675) (by norm_num)
theorem B588653 : Blo 389765 588653 := bbase (se 3 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 588653 = 220745) (by norm_num)
theorem B883565 : Blo 389765 883565 := bbase (se 3 (by rfl) ⟨165668, by rfl⟩ : syracuseStep 883565 = 331337) (by norm_num)
theorem B588677 : Blo 389765 588677 := bbase (se 4 (by rfl) ⟨55188, by rfl⟩ : syracuseStep 588677 = 110377) (by norm_num)
theorem B588701 : Blo 389765 588701 := bbase (se 3 (by rfl) ⟨110381, by rfl⟩ : syracuseStep 588701 = 220763) (by norm_num)
theorem B588725 : Blo 389765 588725 := bbase (se 5 (by rfl) ⟨27596, by rfl⟩ : syracuseStep 588725 = 55193) (by norm_num)
theorem B883637 : Blo 389765 883637 := bbase (se 5 (by rfl) ⟨41420, by rfl⟩ : syracuseStep 883637 = 82841) (by norm_num)
theorem B588749 : Blo 389765 588749 := bbase (se 3 (by rfl) ⟨110390, by rfl⟩ : syracuseStep 588749 = 220781) (by norm_num)
theorem B588773 : Blo 389765 588773 := bbase (se 4 (by rfl) ⟨55197, by rfl⟩ : syracuseStep 588773 = 110395) (by norm_num)
theorem B3177461 : Blo 389765 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B588797 : Blo 389765 588797 := bbase (se 3 (by rfl) ⟨110399, by rfl⟩ : syracuseStep 588797 = 220799) (by norm_num)
theorem B883709 : Blo 389765 883709 := bbase (se 3 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 883709 = 331391) (by norm_num)
theorem B588821 : Blo 389765 588821 := bbase (se 6 (by rfl) ⟨13800, by rfl⟩ : syracuseStep 588821 = 27601) (by norm_num)
theorem B588845 : Blo 389765 588845 := bbase (se 3 (by rfl) ⟨110408, by rfl⟩ : syracuseStep 588845 = 220817) (by norm_num)
theorem B556085 : Blo 389765 556085 := bbase (se 5 (by rfl) ⟨26066, by rfl⟩ : syracuseStep 556085 = 52133) (by norm_num)
theorem B588869 : Blo 389765 588869 := bbase (se 4 (by rfl) ⟨55206, by rfl⟩ : syracuseStep 588869 = 110413) (by norm_num)
theorem B883781 : Blo 389765 883781 := bbase (se 4 (by rfl) ⟨82854, by rfl⟩ : syracuseStep 883781 = 165709) (by norm_num)
theorem B1113173 : Blo 389765 1113173 := bbase (se 8 (by rfl) ⟨6522, by rfl⟩ : syracuseStep 1113173 = 13045) (by norm_num)
theorem B588893 : Blo 389765 588893 := bbase (se 3 (by rfl) ⟨110417, by rfl⟩ : syracuseStep 588893 = 220835) (by norm_num)
theorem B588917 : Blo 389765 588917 := bbase (se 5 (by rfl) ⟨27605, by rfl⟩ : syracuseStep 588917 = 55211) (by norm_num)
theorem B588941 : Blo 389765 588941 := bbase (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) (by norm_num)
theorem B883853 : Blo 389765 883853 := bbase (se 3 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 883853 = 331445) (by norm_num)
theorem B588965 : Blo 389765 588965 := bbase (se 4 (by rfl) ⟨55215, by rfl⟩ : syracuseStep 588965 = 110431) (by norm_num)
theorem B588989 : Blo 389765 588989 := bbase (se 3 (by rfl) ⟨110435, by rfl⟩ : syracuseStep 588989 = 220871) (by norm_num)
theorem B589013 : Blo 389765 589013 := bbase (se 7 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 589013 = 13805) (by norm_num)
theorem B883925 : Blo 389765 883925 := bbase (se 7 (by rfl) ⟨10358, by rfl⟩ : syracuseStep 883925 = 20717) (by norm_num)
theorem B589037 : Blo 389765 589037 := bbase (se 3 (by rfl) ⟨110444, by rfl⟩ : syracuseStep 589037 = 220889) (by norm_num)
theorem B589061 : Blo 389765 589061 := bbase (se 4 (by rfl) ⟨55224, by rfl⟩ : syracuseStep 589061 = 110449) (by norm_num)
theorem B1113365 : Blo 389765 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B589085 : Blo 389765 589085 := bbase (se 3 (by rfl) ⟨110453, by rfl⟩ : syracuseStep 589085 = 220907) (by norm_num)
theorem B883997 : Blo 389765 883997 := bbase (se 3 (by rfl) ⟨165749, by rfl⟩ : syracuseStep 883997 = 331499) (by norm_num)
theorem B589109 : Blo 389765 589109 := bbase (se 5 (by rfl) ⟨27614, by rfl⟩ : syracuseStep 589109 = 55229) (by norm_num)
theorem B589133 : Blo 389765 589133 := bbase (se 3 (by rfl) ⟨110462, by rfl⟩ : syracuseStep 589133 = 220925) (by norm_num)
theorem B425305 : Blo 389765 425305 := bbase (se 2 (by rfl) ⟨159489, by rfl⟩ : syracuseStep 425305 = 318979) (by norm_num)
theorem B752989 : Blo 389765 752989 := bbase (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) (by norm_num)
theorem B589157 : Blo 389765 589157 := bbase (se 4 (by rfl) ⟨55233, by rfl⟩ : syracuseStep 589157 = 110467) (by norm_num)
theorem B884069 : Blo 389765 884069 := bbase (se 4 (by rfl) ⟨82881, by rfl⟩ : syracuseStep 884069 = 165763) (by norm_num)
theorem B589181 : Blo 389765 589181 := bbase (se 3 (by rfl) ⟨110471, by rfl⟩ : syracuseStep 589181 = 220943) (by norm_num)
theorem B589205 : Blo 389765 589205 := bbase (se 6 (by rfl) ⟨13809, by rfl⟩ : syracuseStep 589205 = 27619) (by norm_num)
theorem B589229 : Blo 389765 589229 := bbase (se 3 (by rfl) ⟨110480, by rfl⟩ : syracuseStep 589229 = 220961) (by norm_num)
theorem B884141 : Blo 389765 884141 := bbase (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) (by norm_num)
theorem B589253 : Blo 389765 589253 := bbase (se 4 (by rfl) ⟨55242, by rfl⟩ : syracuseStep 589253 = 110485) (by norm_num)
theorem B589277 : Blo 389765 589277 := bbase (se 3 (by rfl) ⟨110489, by rfl⟩ : syracuseStep 589277 = 220979) (by norm_num)
theorem B589301 : Blo 389765 589301 := bbase (se 5 (by rfl) ⟨27623, by rfl⟩ : syracuseStep 589301 = 55247) (by norm_num)
theorem B884213 : Blo 389765 884213 := bbase (se 5 (by rfl) ⟨41447, by rfl⟩ : syracuseStep 884213 = 82895) (by norm_num)
theorem B589325 : Blo 389765 589325 := bbase (se 3 (by rfl) ⟨110498, by rfl⟩ : syracuseStep 589325 = 220997) (by norm_num)
theorem B2227733 : Blo 389765 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B589349 : Blo 389765 589349 := bbase (se 4 (by rfl) ⟨55251, by rfl⟩ : syracuseStep 589349 = 110503) (by norm_num)
theorem B589373 : Blo 389765 589373 := bbase (se 3 (by rfl) ⟨110507, by rfl⟩ : syracuseStep 589373 = 221015) (by norm_num)
theorem B884285 : Blo 389765 884285 := bbase (se 3 (by rfl) ⟨165803, by rfl⟩ : syracuseStep 884285 = 331607) (by norm_num)
theorem B589397 : Blo 389765 589397 := bbase (se 8 (by rfl) ⟨3453, by rfl⟩ : syracuseStep 589397 = 6907) (by norm_num)
theorem B556637 : Blo 389765 556637 := bbase (se 3 (by rfl) ⟨104369, by rfl⟩ : syracuseStep 556637 = 208739) (by norm_num)
theorem B589421 : Blo 389765 589421 := bbase (se 3 (by rfl) ⟨110516, by rfl⟩ : syracuseStep 589421 = 221033) (by norm_num)
theorem B589445 : Blo 389765 589445 := bbase (se 4 (by rfl) ⟨55260, by rfl⟩ : syracuseStep 589445 = 110521) (by norm_num)
theorem B884357 : Blo 389765 884357 := bbase (se 4 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 884357 = 165817) (by norm_num)
theorem B589469 : Blo 389765 589469 := bbase (se 3 (by rfl) ⟨110525, by rfl⟩ : syracuseStep 589469 = 221051) (by norm_num)
theorem B589493 : Blo 389765 589493 := bbase (se 5 (by rfl) ⟨27632, by rfl⟩ : syracuseStep 589493 = 55265) (by norm_num)
theorem B589517 : Blo 389765 589517 := bbase (se 3 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 589517 = 221069) (by norm_num)
theorem B884429 : Blo 389765 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B589541 : Blo 389765 589541 := bbase (se 4 (by rfl) ⟨55269, by rfl⟩ : syracuseStep 589541 = 110539) (by norm_num)
theorem B589565 : Blo 389765 589565 := bbase (se 3 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 589565 = 221087) (by norm_num)
theorem B589589 : Blo 389765 589589 := bbase (se 6 (by rfl) ⟨13818, by rfl⟩ : syracuseStep 589589 = 27637) (by norm_num)
theorem B884501 : Blo 389765 884501 := bbase (se 6 (by rfl) ⟨20730, by rfl⟩ : syracuseStep 884501 = 41461) (by norm_num)
theorem B589613 : Blo 389765 589613 := bbase (se 3 (by rfl) ⟨110552, by rfl⟩ : syracuseStep 589613 = 221105) (by norm_num)
theorem B589637 : Blo 389765 589637 := bbase (se 4 (by rfl) ⟨55278, by rfl⟩ : syracuseStep 589637 = 110557) (by norm_num)
theorem B589661 : Blo 389765 589661 := bbase (se 3 (by rfl) ⟨110561, by rfl⟩ : syracuseStep 589661 = 221123) (by norm_num)
theorem B884573 : Blo 389765 884573 := bbase (se 3 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 884573 = 331715) (by norm_num)
theorem B589685 : Blo 389765 589685 := bbase (se 5 (by rfl) ⟨27641, by rfl⟩ : syracuseStep 589685 = 55283) (by norm_num)
theorem B589709 : Blo 389765 589709 := bbase (se 3 (by rfl) ⟨110570, by rfl⟩ : syracuseStep 589709 = 221141) (by norm_num)
theorem B589733 : Blo 389765 589733 := bbase (se 4 (by rfl) ⟨55287, by rfl⟩ : syracuseStep 589733 = 110575) (by norm_num)
theorem B884645 : Blo 389765 884645 := bbase (se 4 (by rfl) ⟨82935, by rfl⟩ : syracuseStep 884645 = 165871) (by norm_num)
theorem B589757 : Blo 389765 589757 := bbase (se 3 (by rfl) ⟨110579, by rfl⟩ : syracuseStep 589757 = 221159) (by norm_num)
theorem B589781 : Blo 389765 589781 := bbase (se 7 (by rfl) ⟨6911, by rfl⟩ : syracuseStep 589781 = 13823) (by norm_num)
theorem B589805 : Blo 389765 589805 := bbase (se 3 (by rfl) ⟨110588, by rfl⟩ : syracuseStep 589805 = 221177) (by norm_num)
theorem B884717 : Blo 389765 884717 := bbase (se 3 (by rfl) ⟨165884, by rfl⟩ : syracuseStep 884717 = 331769) (by norm_num)
theorem B557059 : Blo 389765 557059 := bstep (se 1 (by rfl) ⟨417794, by rfl⟩ : syracuseStep 557059 = 835589) B835589
theorem B393219 : Blo 389765 393219 := bstep (se 1 (by rfl) ⟨294914, by rfl⟩ : syracuseStep 393219 = 589829) B589829
theorem B884753 : Blo 389765 884753 := bstep (se 2 (by rfl) ⟨331782, by rfl⟩ : syracuseStep 884753 = 663565) B663565
theorem B589841 : Blo 389765 589841 := bstep (se 2 (by rfl) ⟨221190, by rfl⟩ : syracuseStep 589841 = 442381) B442381
theorem B393235 : Blo 389765 393235 := bstep (se 1 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 393235 = 589853) B589853
theorem B884771 : Blo 389765 884771 := bstep (se 1 (by rfl) ⟨663578, by rfl⟩ : syracuseStep 884771 = 1327157) B1327157
theorem B589859 : Blo 389765 589859 := bstep (se 1 (by rfl) ⟨442394, by rfl⟩ : syracuseStep 589859 = 884789) B884789
theorem B393251 : Blo 389765 393251 := bstep (se 1 (by rfl) ⟨294938, by rfl⟩ : syracuseStep 393251 = 589877) B589877
theorem B393267 : Blo 389765 393267 := bstep (se 1 (by rfl) ⟨294950, by rfl⟩ : syracuseStep 393267 = 589901) B589901
theorem B589889 : Blo 389765 589889 := bstep (se 2 (by rfl) ⟨221208, by rfl⟩ : syracuseStep 589889 = 442417) B442417
theorem B393283 : Blo 389765 393283 := bstep (se 1 (by rfl) ⟨294962, by rfl⟩ : syracuseStep 393283 = 589925) B589925
theorem B589907 : Blo 389765 589907 := bstep (se 1 (by rfl) ⟨442430, by rfl⟩ : syracuseStep 589907 = 884861) B884861
theorem B393299 : Blo 389765 393299 := bstep (se 1 (by rfl) ⟨294974, by rfl⟩ : syracuseStep 393299 = 589949) B589949
theorem B393315 : Blo 389765 393315 := bstep (se 1 (by rfl) ⟨294986, by rfl⟩ : syracuseStep 393315 = 589973) B589973
theorem B589937 : Blo 389765 589937 := bstep (se 2 (by rfl) ⟨221226, by rfl⟩ : syracuseStep 589937 = 442453) B442453
theorem B393331 : Blo 389765 393331 := bstep (se 1 (by rfl) ⟨294998, by rfl⟩ : syracuseStep 393331 = 589997) B589997
theorem B589955 : Blo 389765 589955 := bstep (se 1 (by rfl) ⟨442466, by rfl⟩ : syracuseStep 589955 = 884933) B884933
theorem B393347 : Blo 389765 393347 := bstep (se 1 (by rfl) ⟨295010, by rfl⟩ : syracuseStep 393347 = 590021) B590021
theorem B393363 : Blo 389765 393363 := bstep (se 1 (by rfl) ⟨295022, by rfl⟩ : syracuseStep 393363 = 590045) B590045
theorem B589985 : Blo 389765 589985 := bstep (se 2 (by rfl) ⟨221244, by rfl⟩ : syracuseStep 589985 = 442489) B442489
theorem B393379 : Blo 389765 393379 := bstep (se 1 (by rfl) ⟨295034, by rfl⟩ : syracuseStep 393379 = 590069) B590069
theorem B950449 : Blo 389765 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B590003 : Blo 389765 590003 := bstep (se 1 (by rfl) ⟨442502, by rfl⟩ : syracuseStep 590003 = 885005) B885005
theorem B393395 : Blo 389765 393395 := bstep (se 1 (by rfl) ⟨295046, by rfl⟩ : syracuseStep 393395 = 590093) B590093
theorem B393411 : Blo 389765 393411 := bstep (se 1 (by rfl) ⟨295058, by rfl⟩ : syracuseStep 393411 = 590117) B590117
theorem B590033 : Blo 389765 590033 := bstep (se 2 (by rfl) ⟨221262, by rfl⟩ : syracuseStep 590033 = 442525) B442525
theorem B393427 : Blo 389765 393427 := bstep (se 1 (by rfl) ⟨295070, by rfl⟩ : syracuseStep 393427 = 590141) B590141
theorem B590051 : Blo 389765 590051 := bstep (se 1 (by rfl) ⟨442538, by rfl⟩ : syracuseStep 590051 = 885077) B885077
theorem B393443 : Blo 389765 393443 := bstep (se 1 (by rfl) ⟨295082, by rfl⟩ : syracuseStep 393443 = 590165) B590165
theorem B393459 : Blo 389765 393459 := bstep (se 1 (by rfl) ⟨295094, by rfl⟩ : syracuseStep 393459 = 590189) B590189
theorem B590081 : Blo 389765 590081 := bstep (se 2 (by rfl) ⟨221280, by rfl⟩ : syracuseStep 590081 = 442561) B442561
theorem B393475 : Blo 389765 393475 := bstep (se 1 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 393475 = 590213) B590213
theorem B590099 : Blo 389765 590099 := bstep (se 1 (by rfl) ⟨442574, by rfl⟩ : syracuseStep 590099 = 885149) B885149
theorem B393491 : Blo 389765 393491 := bstep (se 1 (by rfl) ⟨295118, by rfl⟩ : syracuseStep 393491 = 590237) B590237
theorem B393507 : Blo 389765 393507 := bstep (se 1 (by rfl) ⟨295130, by rfl⟩ : syracuseStep 393507 = 590261) B590261
theorem B885041 : Blo 389765 885041 := bstep (se 2 (by rfl) ⟨331890, by rfl⟩ : syracuseStep 885041 = 663781) B663781
theorem B590129 : Blo 389765 590129 := bstep (se 2 (by rfl) ⟨221298, by rfl⟩ : syracuseStep 590129 = 442597) B442597
theorem B393523 : Blo 389765 393523 := bstep (se 1 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 393523 = 590285) B590285
theorem B885059 : Blo 389765 885059 := bstep (se 1 (by rfl) ⟨663794, by rfl⟩ : syracuseStep 885059 = 1327589) B1327589
theorem B590147 : Blo 389765 590147 := bstep (se 1 (by rfl) ⟨442610, by rfl⟩ : syracuseStep 590147 = 885221) B885221
theorem B393539 : Blo 389765 393539 := bstep (se 1 (by rfl) ⟨295154, by rfl⟩ : syracuseStep 393539 = 590309) B590309
theorem B393555 : Blo 389765 393555 := bstep (se 1 (by rfl) ⟨295166, by rfl⟩ : syracuseStep 393555 = 590333) B590333
theorem B590177 : Blo 389765 590177 := bstep (se 2 (by rfl) ⟨221316, by rfl⟩ : syracuseStep 590177 = 442633) B442633
theorem B393571 : Blo 389765 393571 := bstep (se 1 (by rfl) ⟨295178, by rfl⟩ : syracuseStep 393571 = 590357) B590357
theorem B590195 : Blo 389765 590195 := bstep (se 1 (by rfl) ⟨442646, by rfl⟩ : syracuseStep 590195 = 885293) B885293
theorem B393587 : Blo 389765 393587 := bstep (se 1 (by rfl) ⟨295190, by rfl⟩ : syracuseStep 393587 = 590381) B590381
theorem B393603 : Blo 389765 393603 := bstep (se 1 (by rfl) ⟨295202, by rfl⟩ : syracuseStep 393603 = 590405) B590405
theorem B590225 : Blo 389765 590225 := bstep (se 2 (by rfl) ⟨221334, by rfl⟩ : syracuseStep 590225 = 442669) B442669
theorem B393619 : Blo 389765 393619 := bstep (se 1 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 393619 = 590429) B590429
theorem B1671587 : Blo 389765 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B590243 : Blo 389765 590243 := bstep (se 1 (by rfl) ⟨442682, by rfl⟩ : syracuseStep 590243 = 885365) B885365
theorem B393635 : Blo 389765 393635 := bstep (se 1 (by rfl) ⟨295226, by rfl⟩ : syracuseStep 393635 = 590453) B590453
theorem B393651 : Blo 389765 393651 := bstep (se 1 (by rfl) ⟨295238, by rfl⟩ : syracuseStep 393651 = 590477) B590477
theorem B590273 : Blo 389765 590273 := bstep (se 2 (by rfl) ⟨221352, by rfl⟩ : syracuseStep 590273 = 442705) B442705
theorem B393667 : Blo 389765 393667 := bstep (se 1 (by rfl) ⟨295250, by rfl⟩ : syracuseStep 393667 = 590501) B590501
theorem B1114573 : Blo 389765 1114573 := bstep (se 3 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 1114573 = 417965) B417965
theorem B590291 : Blo 389765 590291 := bstep (se 1 (by rfl) ⟨442718, by rfl⟩ : syracuseStep 590291 = 885437) B885437
theorem B393683 : Blo 389765 393683 := bstep (se 1 (by rfl) ⟨295262, by rfl⟩ : syracuseStep 393683 = 590525) B590525
theorem B393699 : Blo 389765 393699 := bstep (se 1 (by rfl) ⟨295274, by rfl⟩ : syracuseStep 393699 = 590549) B590549
theorem B590321 : Blo 389765 590321 := bstep (se 2 (by rfl) ⟨221370, by rfl⟩ : syracuseStep 590321 = 442741) B442741
theorem B393715 : Blo 389765 393715 := bstep (se 1 (by rfl) ⟨295286, by rfl⟩ : syracuseStep 393715 = 590573) B590573
theorem B590339 : Blo 389765 590339 := bstep (se 1 (by rfl) ⟨442754, by rfl⟩ : syracuseStep 590339 = 885509) B885509
theorem B393731 : Blo 389765 393731 := bstep (se 1 (by rfl) ⟨295298, by rfl⟩ : syracuseStep 393731 = 590597) B590597
theorem B393747 : Blo 389765 393747 := bstep (se 1 (by rfl) ⟨295310, by rfl⟩ : syracuseStep 393747 = 590621) B590621
theorem B590369 : Blo 389765 590369 := bstep (se 2 (by rfl) ⟨221388, by rfl⟩ : syracuseStep 590369 = 442777) B442777
theorem B393763 : Blo 389765 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B557617 : Blo 389765 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B590387 : Blo 389765 590387 := bstep (se 1 (by rfl) ⟨442790, by rfl⟩ : syracuseStep 590387 = 885581) B885581
theorem B885329 : Blo 389765 885329 := bstep (se 2 (by rfl) ⟨331998, by rfl⟩ : syracuseStep 885329 = 663997) B663997
theorem B590417 : Blo 389765 590417 := bstep (se 2 (by rfl) ⟨221406, by rfl⟩ : syracuseStep 590417 = 442813) B442813
theorem B557651 : Blo 389765 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B885347 : Blo 389765 885347 := bstep (se 1 (by rfl) ⟨664010, by rfl⟩ : syracuseStep 885347 = 1328021) B1328021
theorem B590435 : Blo 389765 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B590465 : Blo 389765 590465 := bstep (se 2 (by rfl) ⟨221424, by rfl⟩ : syracuseStep 590465 = 442849) B442849
theorem B590483 : Blo 389765 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B590513 : Blo 389765 590513 := bstep (se 2 (by rfl) ⟨221442, by rfl⟩ : syracuseStep 590513 = 442885) B442885
theorem B590531 : Blo 389765 590531 := bstep (se 1 (by rfl) ⟨442898, by rfl⟩ : syracuseStep 590531 = 885797) B885797
theorem B590561 : Blo 389765 590561 := bstep (se 2 (by rfl) ⟨221460, by rfl⟩ : syracuseStep 590561 = 442921) B442921
theorem B590579 : Blo 389765 590579 := bstep (se 1 (by rfl) ⟨442934, by rfl⟩ : syracuseStep 590579 = 885869) B885869
theorem B590609 : Blo 389765 590609 := bstep (se 2 (by rfl) ⟨221478, by rfl⟩ : syracuseStep 590609 = 442957) B442957
theorem B590627 : Blo 389765 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B885617 : Blo 389765 885617 := bstep (se 2 (by rfl) ⟨332106, by rfl⟩ : syracuseStep 885617 = 664213) B664213
theorem B885635 : Blo 389765 885635 := bstep (se 1 (by rfl) ⟨664226, by rfl⟩ : syracuseStep 885635 = 1328453) B1328453
theorem B558209 : Blo 389765 558209 := bstep (se 2 (by rfl) ⟨209328, by rfl⟩ : syracuseStep 558209 = 418657) B418657
theorem B885905 : Blo 389765 885905 := bstep (se 2 (by rfl) ⟨332214, by rfl⟩ : syracuseStep 885905 = 664429) B664429
theorem B885923 : Blo 389765 885923 := bstep (se 1 (by rfl) ⟨664442, by rfl⟩ : syracuseStep 885923 = 1328885) B1328885
theorem B558289 : Blo 389765 558289 := bstep (se 2 (by rfl) ⟨209358, by rfl⟩ : syracuseStep 558289 = 418717) B418717
theorem B1344995 : Blo 389765 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B1115633 : Blo 389765 1115633 := bstep (se 2 (by rfl) ⟨418362, by rfl⟩ : syracuseStep 1115633 = 836725) B836725
theorem B5375587 : Blo 389765 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B624385 : Blo 389765 624385 := bstep (se 2 (by rfl) ⟨234144, by rfl⟩ : syracuseStep 624385 = 468289) B468289
theorem B2098979 : Blo 389765 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B624449 : Blo 389765 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B2230193 : Blo 389765 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B624577 : Blo 389765 624577 := bstep (se 2 (by rfl) ⟨234216, by rfl⟩ : syracuseStep 624577 = 468433) B468433
theorem B559075 : Blo 389765 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B1345571 : Blo 389765 1345571 := bstep (se 1 (by rfl) ⟨1009178, by rfl⟩ : syracuseStep 1345571 = 2018357) B2018357
theorem B2394211 : Blo 389765 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1116305 : Blo 389765 1116305 := bstep (se 2 (by rfl) ⟨418614, by rfl⟩ : syracuseStep 1116305 = 837229) B837229
theorem B1050769 : Blo 389765 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B493715 : Blo 389765 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B3180869 : Blo 389765 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B657841 : Blo 389765 657841 := bstep (se 2 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 657841 = 493381) B493381
theorem B559553 : Blo 389765 559553 := bstep (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) B419665
theorem B61049285 : Blo 389765 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B6785477 : Blo 389765 6785477 := bstep (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) B1272277
theorem B657875 : Blo 389765 657875 := bstep (se 1 (by rfl) ⟨493406, by rfl⟩ : syracuseStep 657875 = 986813) B986813
theorem B559667 : Blo 389765 559667 := bstep (se 1 (by rfl) ⟨419750, by rfl⟩ : syracuseStep 559667 = 839501) B839501
theorem B658003 : Blo 389765 658003 := bstep (se 1 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 658003 = 987005) B987005
theorem B559747 : Blo 389765 559747 := bstep (se 1 (by rfl) ⟨419810, by rfl⟩ : syracuseStep 559747 = 839621) B839621
theorem B658145 : Blo 389765 658145 := bstep (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) B493609
theorem B396019 : Blo 389765 396019 := bstep (se 1 (by rfl) ⟨297014, by rfl⟩ : syracuseStep 396019 = 594029) B594029
theorem B494419 : Blo 389765 494419 := bstep (se 1 (by rfl) ⟨370814, by rfl⟩ : syracuseStep 494419 = 741629) B741629
theorem B658273 : Blo 389765 658273 := bstep (se 2 (by rfl) ⟨246852, by rfl⟩ : syracuseStep 658273 = 493705) B493705
theorem B527203 : Blo 389765 527203 := bstep (se 1 (by rfl) ⟨395402, by rfl⟩ : syracuseStep 527203 = 790805) B790805
theorem B658307 : Blo 389765 658307 := bstep (se 1 (by rfl) ⟨493730, by rfl⟩ : syracuseStep 658307 = 987461) B987461
theorem B1117091 : Blo 389765 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B494515 : Blo 389765 494515 := bstep (se 1 (by rfl) ⟨370886, by rfl⟩ : syracuseStep 494515 = 741773) B741773
theorem B658435 : Blo 389765 658435 := bstep (se 1 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 658435 = 987653) B987653
theorem B658577 : Blo 389765 658577 := bstep (se 2 (by rfl) ⟨246966, by rfl⟩ : syracuseStep 658577 = 493933) B493933
theorem B560305 : Blo 389765 560305 := bstep (se 2 (by rfl) ⟨210114, by rfl⟩ : syracuseStep 560305 = 420229) B420229
theorem B4754659 : Blo 389765 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1117421 : Blo 389765 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B658705 : Blo 389765 658705 := bstep (se 2 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 658705 = 494029) B494029
theorem B1117489 : Blo 389765 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B658739 : Blo 389765 658739 := bstep (se 1 (by rfl) ⟨494054, by rfl⟩ : syracuseStep 658739 = 988109) B988109
theorem B2231651 : Blo 389765 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B495011 : Blo 389765 495011 := bstep (se 1 (by rfl) ⟨371258, by rfl⟩ : syracuseStep 495011 = 742517) B742517
theorem B658867 : Blo 389765 658867 := bstep (se 1 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 658867 = 988301) B988301
theorem B527809 : Blo 389765 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B659009 : Blo 389765 659009 := bstep (se 2 (by rfl) ⟨247128, by rfl⟩ : syracuseStep 659009 = 494257) B494257
theorem B1117763 : Blo 389765 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B1904269 : Blo 389765 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B659137 : Blo 389765 659137 := bstep (se 2 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 659137 = 494353) B494353
theorem B593633 : Blo 389765 593633 := bstep (se 2 (by rfl) ⟨222612, by rfl⟩ : syracuseStep 593633 = 445225) B445225
theorem B659171 : Blo 389765 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B659299 : Blo 389765 659299 := bstep (se 1 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 659299 = 988949) B988949
theorem B5345165 : Blo 389765 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B987025 : Blo 389765 987025 := bstep (se 2 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 987025 = 740269) B740269
theorem B397219 : Blo 389765 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B626627 : Blo 389765 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B6033379 : Blo 389765 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B659441 : Blo 389765 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B1249283 : Blo 389765 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B1609763 : Blo 389765 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B495715 : Blo 389765 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B1675363 : Blo 389765 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B659569 : Blo 389765 659569 := bstep (se 2 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 659569 = 494677) B494677
theorem B659603 : Blo 389765 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B987299 : Blo 389765 987299 := bstep (se 1 (by rfl) ⟨740474, by rfl⟩ : syracuseStep 987299 = 1480949) B1480949
theorem B495811 : Blo 389765 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B659731 : Blo 389765 659731 := bstep (se 1 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 659731 = 989597) B989597
theorem B987491 : Blo 389765 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B1118605 : Blo 389765 1118605 := bstep (se 3 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 1118605 = 419477) B419477
theorem B659873 : Blo 389765 659873 := bstep (se 2 (by rfl) ⟨247452, by rfl⟩ : syracuseStep 659873 = 494905) B494905
theorem B8556997 : Blo 389765 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B660001 : Blo 389765 660001 := bstep (se 2 (by rfl) ⟨247500, by rfl⟩ : syracuseStep 660001 = 495001) B495001
theorem B1118765 : Blo 389765 1118765 := bstep (se 3 (by rfl) ⟨209768, by rfl⟩ : syracuseStep 1118765 = 419537) B419537
theorem B660035 : Blo 389765 660035 := bstep (se 1 (by rfl) ⟨495026, by rfl⟩ : syracuseStep 660035 = 990053) B990053
theorem B528977 : Blo 389765 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B496307 : Blo 389765 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B594625 : Blo 389765 594625 := bstep (se 2 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 594625 = 445969) B445969
theorem B660163 : Blo 389765 660163 := bstep (se 1 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 660163 = 990245) B990245
theorem B1118947 : Blo 389765 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1315601 : Blo 389765 1315601 := bstep (se 2 (by rfl) ⟨493350, by rfl⟩ : syracuseStep 1315601 = 986701) B986701
theorem B627473 : Blo 389765 627473 := bstep (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) B470605
theorem B660305 : Blo 389765 660305 := bstep (se 2 (by rfl) ⟨247614, by rfl⟩ : syracuseStep 660305 = 495229) B495229
theorem B1414093 : Blo 389765 1414093 := bstep (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) B530285
theorem B660433 : Blo 389765 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B660467 : Blo 389765 660467 := bstep (se 1 (by rfl) ⟨495350, by rfl⟩ : syracuseStep 660467 = 990701) B990701
theorem B529507 : Blo 389765 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B660595 : Blo 389765 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B595075 : Blo 389765 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B660737 : Blo 389765 660737 := bstep (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) B495553
theorem B988433 : Blo 389765 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B1316141 : Blo 389765 1316141 := bstep (se 3 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 1316141 = 493553) B493553
theorem B988483 : Blo 389765 988483 := bstep (se 1 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 988483 = 1482725) B1482725
theorem B1611085 : Blo 389765 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B398675 : Blo 389765 398675 := bstep (se 1 (by rfl) ⟨299006, by rfl⟩ : syracuseStep 398675 = 598013) B598013
theorem B1316195 : Blo 389765 1316195 := bstep (se 1 (by rfl) ⟨987146, by rfl⟩ : syracuseStep 1316195 = 1974293) B1974293
theorem B497011 : Blo 389765 497011 := bstep (se 1 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 497011 = 745517) B745517
theorem B660865 : Blo 389765 660865 := bstep (se 2 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 660865 = 495649) B495649
theorem B660899 : Blo 389765 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B988625 : Blo 389765 988625 := bstep (se 2 (by rfl) ⟨370734, by rfl⟩ : syracuseStep 988625 = 741469) B741469
theorem B497107 : Blo 389765 497107 := bstep (se 1 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 497107 = 745661) B745661
theorem B628211 : Blo 389765 628211 := bstep (se 1 (by rfl) ⟨471158, by rfl⟩ : syracuseStep 628211 = 942317) B942317
theorem B661027 : Blo 389765 661027 := bstep (se 1 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 661027 = 991541) B991541
theorem B1316465 : Blo 389765 1316465 := bstep (se 2 (by rfl) ⟨493674, by rfl⟩ : syracuseStep 1316465 = 987349) B987349
theorem B661169 : Blo 389765 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B530209 : Blo 389765 530209 := bstep (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) B397657
theorem B661297 : Blo 389765 661297 := bstep (se 2 (by rfl) ⟨247986, by rfl⟩ : syracuseStep 661297 = 495973) B495973
theorem B661331 : Blo 389765 661331 := bstep (se 1 (by rfl) ⟨495998, by rfl⟩ : syracuseStep 661331 = 991997) B991997
theorem B497603 : Blo 389765 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B661459 : Blo 389765 661459 := bstep (se 1 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 661459 = 992189) B992189
theorem B1677361 : Blo 389765 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1480781 : Blo 389765 1480781 := bstep (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) B555293
theorem B1251409 : Blo 389765 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B1120337 : Blo 389765 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B661601 : Blo 389765 661601 := bstep (se 2 (by rfl) ⟨248100, by rfl⟩ : syracuseStep 661601 = 496201) B496201
theorem B1054829 : Blo 389765 1054829 := bstep (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) B395561
theorem B1317005 : Blo 389765 1317005 := bstep (se 3 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 1317005 = 493877) B493877
theorem B1054883 : Blo 389765 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B1317059 : Blo 389765 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B1054925 : Blo 389765 1054925 := bstep (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) B395597
theorem B661729 : Blo 389765 661729 := bstep (se 2 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 661729 = 496297) B496297
theorem B661763 : Blo 389765 661763 := bstep (se 1 (by rfl) ⟨496322, by rfl⟩ : syracuseStep 661763 = 992645) B992645
theorem B530707 : Blo 389765 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B661891 : Blo 389765 661891 := bstep (se 1 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 661891 = 992837) B992837
theorem B989617 : Blo 389765 989617 := bstep (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) B742213
theorem B1317329 : Blo 389765 1317329 := bstep (se 2 (by rfl) ⟨493998, by rfl⟩ : syracuseStep 1317329 = 987997) B987997
theorem B629203 : Blo 389765 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B662033 : Blo 389765 662033 := bstep (se 2 (by rfl) ⟨248262, by rfl⟩ : syracuseStep 662033 = 496525) B496525
theorem B498307 : Blo 389765 498307 := bstep (se 1 (by rfl) ⟨373730, by rfl⟩ : syracuseStep 498307 = 747461) B747461
theorem B662161 : Blo 389765 662161 := bstep (se 2 (by rfl) ⟨248310, by rfl⟩ : syracuseStep 662161 = 496621) B496621
theorem B662195 : Blo 389765 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B629441 : Blo 389765 629441 := bstep (se 2 (by rfl) ⟨236040, by rfl⟩ : syracuseStep 629441 = 472081) B472081
theorem B1186499 : Blo 389765 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B989891 : Blo 389765 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B662323 : Blo 389765 662323 := bstep (se 1 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 662323 = 993485) B993485
theorem B2988899 : Blo 389765 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B990083 : Blo 389765 990083 := bstep (se 1 (by rfl) ⟨742562, by rfl⟩ : syracuseStep 990083 = 1485125) B1485125
theorem B629651 : Blo 389765 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B596899 : Blo 389765 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B662465 : Blo 389765 662465 := bstep (se 2 (by rfl) ⟨248424, by rfl⟩ : syracuseStep 662465 = 496849) B496849
theorem B1317869 : Blo 389765 1317869 := bstep (se 3 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 1317869 = 494201) B494201
theorem B1121293 : Blo 389765 1121293 := bstep (se 3 (by rfl) ⟨210242, by rfl⟩ : syracuseStep 1121293 = 420485) B420485
theorem B1317923 : Blo 389765 1317923 := bstep (se 1 (by rfl) ⟨988442, by rfl⟩ : syracuseStep 1317923 = 1976885) B1976885
theorem B5676085 : Blo 389765 5676085 := bstep (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) B532133
theorem B662593 : Blo 389765 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B662627 : Blo 389765 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B662755 : Blo 389765 662755 := bstep (se 1 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 662755 = 994133) B994133
theorem B1318193 : Blo 389765 1318193 := bstep (se 2 (by rfl) ⟨494322, by rfl⟩ : syracuseStep 1318193 = 988645) B988645
theorem B957745 : Blo 389765 957745 := bstep (se 2 (by rfl) ⟨359154, by rfl⟩ : syracuseStep 957745 = 718309) B718309
theorem B1023331 : Blo 389765 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B662897 : Blo 389765 662897 := bstep (se 2 (by rfl) ⟨248586, by rfl⟩ : syracuseStep 662897 = 497173) B497173
theorem B1973645 : Blo 389765 1973645 := bstep (se 3 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 1973645 = 740117) B740117
theorem B564689 : Blo 389765 564689 := bstep (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) B423517
theorem B663025 : Blo 389765 663025 := bstep (se 2 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 663025 = 497269) B497269
theorem B663059 : Blo 389765 663059 := bstep (se 1 (by rfl) ⟨497294, by rfl⟩ : syracuseStep 663059 = 994589) B994589
theorem B5643917 : Blo 389765 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B663187 : Blo 389765 663187 := bstep (se 1 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 663187 = 994781) B994781
theorem B630433 : Blo 389765 630433 := bstep (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) B472825
theorem B663329 : Blo 389765 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B892721 : Blo 389765 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B991025 : Blo 389765 991025 := bstep (se 2 (by rfl) ⟨371634, by rfl⟩ : syracuseStep 991025 = 743269) B743269
theorem B1318733 : Blo 389765 1318733 := bstep (se 3 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 1318733 = 494525) B494525
theorem B991075 : Blo 389765 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B3383153 : Blo 389765 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B1318787 : Blo 389765 1318787 := bstep (se 1 (by rfl) ⟨989090, by rfl⟩ : syracuseStep 1318787 = 1978181) B1978181
theorem B663457 : Blo 389765 663457 := bstep (se 2 (by rfl) ⟨248796, by rfl⟩ : syracuseStep 663457 = 497593) B497593
theorem B663491 : Blo 389765 663491 := bstep (se 1 (by rfl) ⟨497618, by rfl⟩ : syracuseStep 663491 = 995237) B995237
theorem B761827 : Blo 389765 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B1253357 : Blo 389765 1253357 := bstep (se 3 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 1253357 = 470009) B470009
theorem B991217 : Blo 389765 991217 := bstep (se 2 (by rfl) ⟨371706, by rfl⟩ : syracuseStep 991217 = 743413) B743413
theorem B663619 : Blo 389765 663619 := bstep (se 1 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 663619 = 995429) B995429
theorem B598115 : Blo 389765 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B1253485 : Blo 389765 1253485 := bstep (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) B470057
theorem B1482893 : Blo 389765 1482893 := bstep (se 3 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 1482893 = 556085) B556085
theorem B1319057 : Blo 389765 1319057 := bstep (se 2 (by rfl) ⟨494646, by rfl⟩ : syracuseStep 1319057 = 989293) B989293
theorem B663761 : Blo 389765 663761 := bstep (se 2 (by rfl) ⟨248910, by rfl⟩ : syracuseStep 663761 = 497821) B497821
theorem B1777997 : Blo 389765 1777997 := bstep (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) B666749
theorem B663889 : Blo 389765 663889 := bstep (se 2 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 663889 = 497917) B497917
theorem B663923 : Blo 389765 663923 := bstep (se 1 (by rfl) ⟨497942, by rfl⟩ : syracuseStep 663923 = 995885) B995885
theorem B664051 : Blo 389765 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B664193 : Blo 389765 664193 := bstep (se 2 (by rfl) ⟨249072, by rfl⟩ : syracuseStep 664193 = 498145) B498145
theorem B1319597 : Blo 389765 1319597 := bstep (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) B494849
theorem B1319651 : Blo 389765 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B664321 : Blo 389765 664321 := bstep (se 2 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 664321 = 498241) B498241
theorem B566033 : Blo 389765 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B664355 : Blo 389765 664355 := bstep (se 1 (by rfl) ⟨498266, by rfl⟩ : syracuseStep 664355 = 996533) B996533
theorem B1483697 : Blo 389765 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B992209 : Blo 389765 992209 := bstep (se 2 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 992209 = 744157) B744157
theorem B1319921 : Blo 389765 1319921 := bstep (se 2 (by rfl) ⟨494970, by rfl⟩ : syracuseStep 1319921 = 989941) B989941
theorem B992483 : Blo 389765 992483 := bstep (se 1 (by rfl) ⟨744362, by rfl⟩ : syracuseStep 992483 = 1488725) B1488725
theorem B992675 : Blo 389765 992675 := bstep (se 1 (by rfl) ⟨744506, by rfl⟩ : syracuseStep 992675 = 1489013) B1489013
theorem B1320461 : Blo 389765 1320461 := bstep (se 3 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 1320461 = 495173) B495173
theorem B1058321 : Blo 389765 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B1320515 : Blo 389765 1320515 := bstep (se 1 (by rfl) ⟨990386, by rfl⟩ : syracuseStep 1320515 = 1980773) B1980773
theorem B4531781 : Blo 389765 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B1484365 : Blo 389765 1484365 := bstep (se 3 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 1484365 = 556637) B556637
theorem B567073 : Blo 389765 567073 := bstep (se 2 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 567073 = 425305) B425305
theorem B1320785 : Blo 389765 1320785 := bstep (se 2 (by rfl) ⟨495294, by rfl⟩ : syracuseStep 1320785 = 990589) B990589
theorem B2107235 : Blo 389765 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B1255331 : Blo 389765 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B1288109 : Blo 389765 1288109 := bstep (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) B483041
theorem B1681393 : Blo 389765 1681393 := bstep (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) B1261045
theorem B1255459 : Blo 389765 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B2828357 : Blo 389765 2828357 := bstep (se 4 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 2828357 = 530317) B530317
theorem B1255601 : Blo 389765 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B1976561 : Blo 389765 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B1255715 : Blo 389765 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B993617 : Blo 389765 993617 := bstep (se 2 (by rfl) ⟨372606, by rfl⟩ : syracuseStep 993617 = 745213) B745213
theorem B1485155 : Blo 389765 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B1321325 : Blo 389765 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B993667 : Blo 389765 993667 := bstep (se 1 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 993667 = 1490501) B1490501
theorem B1190285 : Blo 389765 1190285 := bstep (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) B446357
theorem B1321379 : Blo 389765 1321379 := bstep (se 1 (by rfl) ⟨991034, by rfl⟩ : syracuseStep 1321379 = 1982069) B1982069
theorem B993809 : Blo 389765 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B1321649 : Blo 389765 1321649 := bstep (se 2 (by rfl) ⟨495618, by rfl⟩ : syracuseStep 1321649 = 991237) B991237
theorem B2501381 : Blo 389765 2501381 := bstep (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) B469009
theorem B797617 : Blo 389765 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B1485809 : Blo 389765 1485809 := bstep (se 2 (by rfl) ⟨557178, by rfl⟩ : syracuseStep 1485809 = 1114357) B1114357
theorem B1322189 : Blo 389765 1322189 := bstep (se 3 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 1322189 = 495821) B495821
theorem B1322243 : Blo 389765 1322243 := bstep (se 1 (by rfl) ⟨991682, by rfl⟩ : syracuseStep 1322243 = 1983365) B1983365
theorem B994801 : Blo 389765 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B1322513 : Blo 389765 1322513 := bstep (se 2 (by rfl) ⟨495942, by rfl⟩ : syracuseStep 1322513 = 991885) B991885
theorem B667297 : Blo 389765 667297 := bstep (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) B500473
theorem B1978019 : Blo 389765 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B1060547 : Blo 389765 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B995075 : Blo 389765 995075 := bstep (se 1 (by rfl) ⟨746306, by rfl⟩ : syracuseStep 995075 = 1492613) B1492613
theorem B896881 : Blo 389765 896881 := bstep (se 2 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 896881 = 672661) B672661
theorem B995267 : Blo 389765 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B1257457 : Blo 389765 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B1323053 : Blo 389765 1323053 := bstep (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) B496145
theorem B2240581 : Blo 389765 2240581 := bstep (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) B420109
theorem B1323107 : Blo 389765 1323107 := bstep (se 1 (by rfl) ⟨992330, by rfl⟩ : syracuseStep 1323107 = 1984661) B1984661
theorem B1159373 : Blo 389765 1159373 := bstep (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) B434765
theorem B438547 : Blo 389765 438547 := bstep (se 1 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 438547 = 657821) B657821
theorem B1323377 : Blo 389765 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B438691 : Blo 389765 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B1487267 : Blo 389765 1487267 := bstep (se 1 (by rfl) ⟨1115450, by rfl⟩ : syracuseStep 1487267 = 2230901) B2230901
theorem B1487281 : Blo 389765 1487281 := bstep (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) B1115461
theorem B1978829 : Blo 389765 1978829 := bstep (se 3 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 1978829 = 742061) B742061
theorem B438835 : Blo 389765 438835 := bstep (se 1 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 438835 = 658253) B658253
theorem B1585763 : Blo 389765 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B504451 : Blo 389765 504451 := bstep (se 1 (by rfl) ⟨378338, by rfl⟩ : syracuseStep 504451 = 756677) B756677
theorem B2503331 : Blo 389765 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B438979 : Blo 389765 438979 := bstep (se 1 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 438979 = 658469) B658469
theorem B439123 : Blo 389765 439123 := bstep (se 1 (by rfl) ⟨329342, by rfl⟩ : syracuseStep 439123 = 658685) B658685
theorem B996209 : Blo 389765 996209 := bstep (se 2 (by rfl) ⟨373578, by rfl⟩ : syracuseStep 996209 = 747157) B747157
theorem B1323917 : Blo 389765 1323917 := bstep (se 3 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 1323917 = 496469) B496469
theorem B996259 : Blo 389765 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B1323971 : Blo 389765 1323971 := bstep (se 1 (by rfl) ⟨992978, by rfl⟩ : syracuseStep 1323971 = 1985957) B1985957
theorem B439267 : Blo 389765 439267 := bstep (se 1 (by rfl) ⟨329450, by rfl⟩ : syracuseStep 439267 = 658901) B658901
theorem B996401 : Blo 389765 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B1258573 : Blo 389765 1258573 := bstep (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) B471965
theorem B439411 : Blo 389765 439411 := bstep (se 1 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 439411 = 659117) B659117
theorem B1881265 : Blo 389765 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1324241 : Blo 389765 1324241 := bstep (se 2 (by rfl) ⟨496590, by rfl⟩ : syracuseStep 1324241 = 993181) B993181
theorem B439555 : Blo 389765 439555 := bstep (se 1 (by rfl) ⟨329666, by rfl⟩ : syracuseStep 439555 = 659333) B659333
theorem B439699 : Blo 389765 439699 := bstep (se 1 (by rfl) ⟨329774, by rfl⟩ : syracuseStep 439699 = 659549) B659549
theorem B439843 : Blo 389765 439843 := bstep (se 1 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 439843 = 659765) B659765
theorem B3782213 : Blo 389765 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B439987 : Blo 389765 439987 := bstep (se 1 (by rfl) ⟨329990, by rfl⟩ : syracuseStep 439987 = 659981) B659981
theorem B2963141 : Blo 389765 2963141 := bstep (se 4 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 2963141 = 555589) B555589
theorem B1324781 : Blo 389765 1324781 := bstep (se 3 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 1324781 = 496793) B496793
theorem B1324835 : Blo 389765 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B440131 : Blo 389765 440131 := bstep (se 1 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 440131 = 660197) B660197
theorem B1488739 : Blo 389765 1488739 := bstep (se 1 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 1488739 = 2233109) B2233109
theorem B1259405 : Blo 389765 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B472979 : Blo 389765 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B440275 : Blo 389765 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B2242565 : Blo 389765 2242565 := bstep (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) B420481
theorem B1325105 : Blo 389765 1325105 := bstep (se 2 (by rfl) ⟨496914, by rfl⟩ : syracuseStep 1325105 = 993829) B993829
theorem B440419 : Blo 389765 440419 := bstep (se 1 (by rfl) ⟨330314, by rfl⟩ : syracuseStep 440419 = 660629) B660629
theorem B669809 : Blo 389765 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B1063057 : Blo 389765 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B7747811 : Blo 389765 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B440563 : Blo 389765 440563 := bstep (se 1 (by rfl) ⟨330422, by rfl⟩ : syracuseStep 440563 = 660845) B660845
theorem B440707 : Blo 389765 440707 := bstep (se 1 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 440707 = 661061) B661061
theorem B440851 : Blo 389765 440851 := bstep (se 1 (by rfl) ⟨330638, by rfl⟩ : syracuseStep 440851 = 661277) B661277
theorem B1325645 : Blo 389765 1325645 := bstep (se 3 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 1325645 = 497117) B497117
theorem B1325699 : Blo 389765 1325699 := bstep (se 1 (by rfl) ⟨994274, by rfl⟩ : syracuseStep 1325699 = 1988549) B1988549
theorem B440995 : Blo 389765 440995 := bstep (se 1 (by rfl) ⟨330746, by rfl⟩ : syracuseStep 440995 = 661493) B661493
theorem B670465 : Blo 389765 670465 := bstep (se 2 (by rfl) ⟨251424, by rfl⟩ : syracuseStep 670465 = 502849) B502849
theorem B637699 : Blo 389765 637699 := bstep (se 1 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 637699 = 956549) B956549
theorem B441139 : Blo 389765 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B1424269 : Blo 389765 1424269 := bstep (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) B534101
theorem B1325969 : Blo 389765 1325969 := bstep (se 2 (by rfl) ⟨497238, by rfl⟩ : syracuseStep 1325969 = 994477) B994477
theorem B441283 : Blo 389765 441283 := bstep (se 1 (by rfl) ⟨330962, by rfl⟩ : syracuseStep 441283 = 661925) B661925
theorem B834563 : Blo 389765 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B441427 : Blo 389765 441427 := bstep (se 1 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 441427 = 662141) B662141
theorem B6438001 : Blo 389765 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B1883341 : Blo 389765 1883341 := bstep (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) B706253
theorem B441571 : Blo 389765 441571 := bstep (se 1 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 441571 = 662357) B662357
theorem B1981745 : Blo 389765 1981745 := bstep (se 2 (by rfl) ⟨743154, by rfl⟩ : syracuseStep 1981745 = 1486309) B1486309
theorem B441715 : Blo 389765 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B1326509 : Blo 389765 1326509 := bstep (se 3 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 1326509 = 497441) B497441
theorem B2112965 : Blo 389765 2112965 := bstep (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) B396181
theorem B1326563 : Blo 389765 1326563 := bstep (se 1 (by rfl) ⟨994922, by rfl⟩ : syracuseStep 1326563 = 1989845) B1989845
theorem B441859 : Blo 389765 441859 := bstep (se 1 (by rfl) ⟨331394, by rfl⟩ : syracuseStep 441859 = 662789) B662789
theorem B442003 : Blo 389765 442003 := bstep (se 1 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 442003 = 663005) B663005
theorem B1195697 : Blo 389765 1195697 := bstep (se 2 (by rfl) ⟨448386, by rfl⟩ : syracuseStep 1195697 = 896773) B896773
theorem B1326833 : Blo 389765 1326833 := bstep (se 2 (by rfl) ⟨497562, by rfl⟩ : syracuseStep 1326833 = 995125) B995125
theorem B638707 : Blo 389765 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B442147 : Blo 389765 442147 := bstep (se 1 (by rfl) ⟨331610, by rfl⟩ : syracuseStep 442147 = 663221) B663221
theorem B835427 : Blo 389765 835427 := bstep (se 1 (by rfl) ⟨626570, by rfl⟩ : syracuseStep 835427 = 1253141) B1253141
theorem B507811 : Blo 389765 507811 := bstep (se 1 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 507811 = 761717) B761717
theorem B442291 : Blo 389765 442291 := bstep (se 1 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 442291 = 663437) B663437
theorem B835537 : Blo 389765 835537 := bstep (se 2 (by rfl) ⟨313326, by rfl⟩ : syracuseStep 835537 = 626653) B626653
theorem B1490957 : Blo 389765 1490957 := bstep (se 3 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 1490957 = 559109) B559109
theorem B442435 : Blo 389765 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B606289 : Blo 389765 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B442579 : Blo 389765 442579 := bstep (se 1 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 442579 = 663869) B663869
theorem B2507021 : Blo 389765 2507021 := bstep (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) B940133
theorem B1327373 : Blo 389765 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B1327427 : Blo 389765 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B442723 : Blo 389765 442723 := bstep (se 1 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 442723 = 664085) B664085
theorem B442867 : Blo 389765 442867 := bstep (se 1 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 442867 = 664301) B664301
theorem B1327697 : Blo 389765 1327697 := bstep (se 2 (by rfl) ⟨497886, by rfl⟩ : syracuseStep 1327697 = 995773) B995773
theorem B803537 : Blo 389765 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B1983203 : Blo 389765 1983203 := bstep (se 1 (by rfl) ⟨1487402, by rfl⟩ : syracuseStep 1983203 = 2974805) B2974805
theorem B1000369 : Blo 389765 1000369 := bstep (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) B750277
theorem B672689 : Blo 389765 672689 := bstep (se 2 (by rfl) ⟨252258, by rfl⟩ : syracuseStep 672689 = 504517) B504517
theorem B1328237 : Blo 389765 1328237 := bstep (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) B498089
theorem B1328291 : Blo 389765 1328291 := bstep (se 1 (by rfl) ⟨996218, by rfl⟩ : syracuseStep 1328291 = 1992437) B1992437
theorem B705763 : Blo 389765 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B1590691 : Blo 389765 1590691 := bstep (se 1 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 1590691 = 2386037) B2386037
theorem B1328561 : Blo 389765 1328561 := bstep (se 2 (by rfl) ⟨498210, by rfl⟩ : syracuseStep 1328561 = 996421) B996421
theorem B2377187 : Blo 389765 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B706051 : Blo 389765 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B1984013 : Blo 389765 1984013 := bstep (se 3 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 1984013 = 744005) B744005
theorem B3360325 : Blo 389765 3360325 := bstep (se 4 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 3360325 = 630061) B630061
theorem B4245301 : Blo 389765 4245301 := bstep (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) B397997
theorem B837553 : Blo 389765 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B1001521 : Blo 389765 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B8505485 : Blo 389765 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B706801 : Blo 389765 706801 := bstep (se 2 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 706801 = 530101) B530101
theorem B2836721 : Blo 389765 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B2672909 : Blo 389765 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B837955 : Blo 389765 837955 := bstep (se 1 (by rfl) ⟨628466, by rfl⟩ : syracuseStep 837955 = 1256933) B1256933
theorem B1493873 : Blo 389765 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B1887245 : Blo 389765 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B740497 : Blo 389765 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B740657 : Blo 389765 740657 := bstep (se 2 (by rfl) ⟨277746, by rfl⟩ : syracuseStep 740657 = 555493) B555493
theorem B2968973 : Blo 389765 2968973 := bstep (se 3 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 2968973 = 1113365) B1113365
theorem B6344077 : Blo 389765 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B741059 : Blo 389765 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B839459 : Blo 389765 839459 := bstep (se 1 (by rfl) ⟨629594, by rfl⟩ : syracuseStep 839459 = 1259189) B1259189
theorem B1986929 : Blo 389765 1986929 := bstep (se 2 (by rfl) ⟨745098, by rfl⟩ : syracuseStep 1986929 = 1490197) B1490197
theorem B1003985 : Blo 389765 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B741955 : Blo 389765 741955 := bstep (se 1 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 741955 = 1112933) B1112933
theorem B2118307 : Blo 389765 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B742115 : Blo 389765 742115 := bstep (se 1 (by rfl) ⟨556586, by rfl⟩ : syracuseStep 742115 = 1113173) B1113173
theorem B3331043 : Blo 389765 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B840689 : Blo 389765 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B6804593 : Blo 389765 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B677233 : Blo 389765 677233 := bstep (se 2 (by rfl) ⟨253962, by rfl⟩ : syracuseStep 677233 = 507925) B507925
theorem B2512453 : Blo 389765 2512453 := bstep (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) B471085
theorem B2119409 : Blo 389765 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B743185 : Blo 389765 743185 := bstep (se 2 (by rfl) ⟨278694, by rfl⟩ : syracuseStep 743185 = 557389) B557389
theorem B1988387 : Blo 389765 1988387 := bstep (se 1 (by rfl) ⟨1491290, by rfl⟩ : syracuseStep 1988387 = 2982581) B2982581
theorem B2119537 : Blo 389765 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B4216931 : Blo 389765 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2971889 : Blo 389765 2971889 := bstep (se 2 (by rfl) ⟨1114458, by rfl⟩ : syracuseStep 2971889 = 2228917) B2228917
theorem B940547 : Blo 389765 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B1989197 : Blo 389765 1989197 := bstep (se 3 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 1989197 = 745949) B745949
theorem B744241 : Blo 389765 744241 := bstep (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) B558181
theorem B416675 : Blo 389765 416675 := bstep (se 1 (by rfl) ⟨312506, by rfl⟩ : syracuseStep 416675 = 625013) B625013
theorem B744643 : Blo 389765 744643 := bstep (se 1 (by rfl) ⟨558482, by rfl⟩ : syracuseStep 744643 = 1116965) B1116965
theorem B744689 : Blo 389765 744689 := bstep (se 2 (by rfl) ⟨279258, by rfl⟩ : syracuseStep 744689 = 558517) B558517
theorem B1400113 : Blo 389765 1400113 := bstep (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) B1050085
theorem B1007011 : Blo 389765 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B1334701 : Blo 389765 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B744977 : Blo 389765 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B646787 : Blo 389765 646787 := bstep (se 1 (by rfl) ⟨485090, by rfl⟩ : syracuseStep 646787 = 970181) B970181
theorem B646913 : Blo 389765 646913 := bstep (se 2 (by rfl) ⟨242592, by rfl⟩ : syracuseStep 646913 = 485185) B485185
theorem B417683 : Blo 389765 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B1335473 : Blo 389765 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B2515171 : Blo 389765 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B745699 : Blo 389765 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B876977 : Blo 389765 876977 := bstep (se 2 (by rfl) ⟨328866, by rfl⟩ : syracuseStep 876977 = 657733) B657733
theorem B876995 : Blo 389765 876995 := bstep (se 1 (by rfl) ⟨657746, by rfl⟩ : syracuseStep 876995 = 1315493) B1315493
theorem B746147 : Blo 389765 746147 := bstep (se 1 (by rfl) ⟨559610, by rfl⟩ : syracuseStep 746147 = 1119221) B1119221
theorem B877265 : Blo 389765 877265 := bstep (se 2 (by rfl) ⟨328974, by rfl⟩ : syracuseStep 877265 = 657949) B657949
theorem B877283 : Blo 389765 877283 := bstep (se 1 (by rfl) ⟨657962, by rfl⟩ : syracuseStep 877283 = 1315925) B1315925
theorem B4481891 : Blo 389765 4481891 := bstep (se 1 (by rfl) ⟨3361418, by rfl⟩ : syracuseStep 4481891 = 6722837) B6722837
theorem B746435 : Blo 389765 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B877553 : Blo 389765 877553 := bstep (se 2 (by rfl) ⟨329082, by rfl⟩ : syracuseStep 877553 = 658165) B658165
theorem B877571 : Blo 389765 877571 := bstep (se 1 (by rfl) ⟨658178, by rfl⟩ : syracuseStep 877571 = 1316357) B1316357
theorem B4220045 : Blo 389765 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B877841 : Blo 389765 877841 := bstep (se 2 (by rfl) ⟨329190, by rfl⟩ : syracuseStep 877841 = 658381) B658381
theorem B877859 : Blo 389765 877859 := bstep (se 1 (by rfl) ⟨658394, by rfl⟩ : syracuseStep 877859 = 1316789) B1316789
theorem B1500493 : Blo 389765 1500493 := bstep (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) B562685
theorem B2221445 : Blo 389765 2221445 := bstep (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) B416521
theorem B1992113 : Blo 389765 1992113 := bstep (se 2 (by rfl) ⟨747042, by rfl⟩ : syracuseStep 1992113 = 1494085) B1494085
theorem B419251 : Blo 389765 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B845329 : Blo 389765 845329 := bstep (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) B633997
theorem B878129 : Blo 389765 878129 := bstep (se 2 (by rfl) ⟨329298, by rfl⟩ : syracuseStep 878129 = 658597) B658597
theorem B878147 : Blo 389765 878147 := bstep (se 1 (by rfl) ⟨658610, by rfl⟩ : syracuseStep 878147 = 1317221) B1317221
theorem B1042157 : Blo 389765 1042157 := bstep (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) B390809
theorem B2221901 : Blo 389765 2221901 := bstep (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) B833213
theorem B878417 : Blo 389765 878417 := bstep (se 2 (by rfl) ⟨329406, by rfl⟩ : syracuseStep 878417 = 658813) B658813
theorem B878435 : Blo 389765 878435 := bstep (se 1 (by rfl) ⟨658826, by rfl⟩ : syracuseStep 878435 = 1317653) B1317653
theorem B747377 : Blo 389765 747377 := bstep (se 2 (by rfl) ⟨280266, by rfl⟩ : syracuseStep 747377 = 560533) B560533
theorem B419699 : Blo 389765 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B944131 : Blo 389765 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B878705 : Blo 389765 878705 := bstep (se 2 (by rfl) ⟨329514, by rfl⟩ : syracuseStep 878705 = 659029) B659029
theorem B878723 : Blo 389765 878723 := bstep (se 1 (by rfl) ⟨659042, by rfl⟩ : syracuseStep 878723 = 1318085) B1318085
theorem B2517169 : Blo 389765 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B878993 : Blo 389765 878993 := bstep (se 2 (by rfl) ⟨329622, by rfl⟩ : syracuseStep 878993 = 659245) B659245
theorem B879011 : Blo 389765 879011 := bstep (se 1 (by rfl) ⟨659258, by rfl⟩ : syracuseStep 879011 = 1318517) B1318517
theorem B879281 : Blo 389765 879281 := bstep (se 2 (by rfl) ⟨329730, by rfl⟩ : syracuseStep 879281 = 659461) B659461
theorem B879299 : Blo 389765 879299 := bstep (se 1 (by rfl) ⟨659474, by rfl⟩ : syracuseStep 879299 = 1318949) B1318949
theorem B10775267 : Blo 389765 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B4254605 : Blo 389765 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B584657 : Blo 389765 584657 := bstep (se 2 (by rfl) ⟨219246, by rfl⟩ : syracuseStep 584657 = 438493) B438493
theorem B879569 : Blo 389765 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B584675 : Blo 389765 584675 := bstep (se 1 (by rfl) ⟨438506, by rfl⟩ : syracuseStep 584675 = 877013) B877013
theorem B879587 : Blo 389765 879587 := bstep (se 1 (by rfl) ⟨659690, by rfl⟩ : syracuseStep 879587 = 1319381) B1319381
theorem B584705 : Blo 389765 584705 := bstep (se 2 (by rfl) ⟨219264, by rfl⟩ : syracuseStep 584705 = 438529) B438529
theorem B584723 : Blo 389765 584723 := bstep (se 1 (by rfl) ⟨438542, by rfl⟩ : syracuseStep 584723 = 877085) B877085
theorem B2583587 : Blo 389765 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B584753 : Blo 389765 584753 := bstep (se 2 (by rfl) ⟨219282, by rfl⟩ : syracuseStep 584753 = 438565) B438565
theorem B584771 : Blo 389765 584771 := bstep (se 1 (by rfl) ⟨438578, by rfl⟩ : syracuseStep 584771 = 877157) B877157
theorem B584801 : Blo 389765 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B584819 : Blo 389765 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B2256005 : Blo 389765 2256005 := bstep (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) B423001
theorem B584849 : Blo 389765 584849 := bstep (se 2 (by rfl) ⟨219318, by rfl⟩ : syracuseStep 584849 = 438637) B438637
theorem B584867 : Blo 389765 584867 := bstep (se 1 (by rfl) ⟨438650, by rfl⟩ : syracuseStep 584867 = 877301) B877301
theorem B584897 : Blo 389765 584897 := bstep (se 2 (by rfl) ⟨219336, by rfl⟩ : syracuseStep 584897 = 438673) B438673
theorem B945361 : Blo 389765 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B584915 : Blo 389765 584915 := bstep (se 1 (by rfl) ⟨438686, by rfl⟩ : syracuseStep 584915 = 877373) B877373
theorem B1502435 : Blo 389765 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B584945 : Blo 389765 584945 := bstep (se 2 (by rfl) ⟨219354, by rfl⟩ : syracuseStep 584945 = 438709) B438709
theorem B879857 : Blo 389765 879857 := bstep (se 2 (by rfl) ⟨329946, by rfl⟩ : syracuseStep 879857 = 659893) B659893
theorem B584963 : Blo 389765 584963 := bstep (se 1 (by rfl) ⟨438722, by rfl⟩ : syracuseStep 584963 = 877445) B877445
theorem B879875 : Blo 389765 879875 := bstep (se 1 (by rfl) ⟨659906, by rfl⟩ : syracuseStep 879875 = 1319813) B1319813
theorem B584993 : Blo 389765 584993 := bstep (se 2 (by rfl) ⟨219372, by rfl⟩ : syracuseStep 584993 = 438745) B438745
theorem B585011 : Blo 389765 585011 := bstep (se 1 (by rfl) ⟨438758, by rfl⟩ : syracuseStep 585011 = 877517) B877517
theorem B585041 : Blo 389765 585041 := bstep (se 2 (by rfl) ⟨219390, by rfl⟩ : syracuseStep 585041 = 438781) B438781
theorem B585059 : Blo 389765 585059 := bstep (se 1 (by rfl) ⟨438794, by rfl⟩ : syracuseStep 585059 = 877589) B877589
theorem B585089 : Blo 389765 585089 := bstep (se 2 (by rfl) ⟨219408, by rfl⟩ : syracuseStep 585089 = 438817) B438817
theorem B585107 : Blo 389765 585107 := bstep (se 1 (by rfl) ⟨438830, by rfl⟩ : syracuseStep 585107 = 877661) B877661
theorem B585137 : Blo 389765 585137 := bstep (se 2 (by rfl) ⟨219426, by rfl⟩ : syracuseStep 585137 = 438853) B438853
theorem B585155 : Blo 389765 585155 := bstep (se 1 (by rfl) ⟨438866, by rfl⟩ : syracuseStep 585155 = 877733) B877733
theorem B585185 : Blo 389765 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B585203 : Blo 389765 585203 := bstep (se 1 (by rfl) ⟨438902, by rfl⟩ : syracuseStep 585203 = 877805) B877805
theorem B585233 : Blo 389765 585233 := bstep (se 2 (by rfl) ⟨219462, by rfl⟩ : syracuseStep 585233 = 438925) B438925
theorem B880145 : Blo 389765 880145 := bstep (se 2 (by rfl) ⟨330054, by rfl⟩ : syracuseStep 880145 = 660109) B660109
theorem B585251 : Blo 389765 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B880163 : Blo 389765 880163 := bstep (se 1 (by rfl) ⟨660122, by rfl⟩ : syracuseStep 880163 = 1320245) B1320245
theorem B585281 : Blo 389765 585281 := bstep (se 2 (by rfl) ⟨219480, by rfl⟩ : syracuseStep 585281 = 438961) B438961
theorem B585299 : Blo 389765 585299 := bstep (se 1 (by rfl) ⟨438974, by rfl⟩ : syracuseStep 585299 = 877949) B877949
theorem B3173987 : Blo 389765 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B585329 : Blo 389765 585329 := bstep (se 2 (by rfl) ⟨219498, by rfl⟩ : syracuseStep 585329 = 438997) B438997
theorem B585347 : Blo 389765 585347 := bstep (se 1 (by rfl) ⟨439010, by rfl⟩ : syracuseStep 585347 = 878021) B878021
theorem B585377 : Blo 389765 585377 := bstep (se 2 (by rfl) ⟨219516, by rfl⟩ : syracuseStep 585377 = 439033) B439033
theorem B585395 : Blo 389765 585395 := bstep (se 1 (by rfl) ⟨439046, by rfl⟩ : syracuseStep 585395 = 878093) B878093
theorem B4419269 : Blo 389765 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B585425 : Blo 389765 585425 := bstep (se 2 (by rfl) ⟨219534, by rfl⟩ : syracuseStep 585425 = 439069) B439069
theorem B585443 : Blo 389765 585443 := bstep (se 1 (by rfl) ⟨439082, by rfl⟩ : syracuseStep 585443 = 878165) B878165
theorem B585473 : Blo 389765 585473 := bstep (se 2 (by rfl) ⟨219552, by rfl⟩ : syracuseStep 585473 = 439105) B439105
theorem B585491 : Blo 389765 585491 := bstep (se 1 (by rfl) ⟨439118, by rfl⟩ : syracuseStep 585491 = 878237) B878237
theorem B585521 : Blo 389765 585521 := bstep (se 2 (by rfl) ⟨219570, by rfl⟩ : syracuseStep 585521 = 439141) B439141
theorem B880433 : Blo 389765 880433 := bstep (se 2 (by rfl) ⟨330162, by rfl⟩ : syracuseStep 880433 = 660325) B660325
theorem B585539 : Blo 389765 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B880451 : Blo 389765 880451 := bstep (se 1 (by rfl) ⟨660338, by rfl⟩ : syracuseStep 880451 = 1320677) B1320677
theorem B2387789 : Blo 389765 2387789 := bstep (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) B895421
theorem B585569 : Blo 389765 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B585587 : Blo 389765 585587 := bstep (se 1 (by rfl) ⟨439190, by rfl⟩ : syracuseStep 585587 = 878381) B878381
theorem B585617 : Blo 389765 585617 := bstep (se 2 (by rfl) ⟨219606, by rfl⟩ : syracuseStep 585617 = 439213) B439213
theorem B585635 : Blo 389765 585635 := bstep (se 1 (by rfl) ⟨439226, by rfl⟩ : syracuseStep 585635 = 878453) B878453
theorem B585665 : Blo 389765 585665 := bstep (se 2 (by rfl) ⟨219624, by rfl⟩ : syracuseStep 585665 = 439249) B439249
theorem B585683 : Blo 389765 585683 := bstep (se 1 (by rfl) ⟨439262, by rfl⟩ : syracuseStep 585683 = 878525) B878525
theorem B585713 : Blo 389765 585713 := bstep (se 2 (by rfl) ⟨219642, by rfl⟩ : syracuseStep 585713 = 439285) B439285
theorem B585731 : Blo 389765 585731 := bstep (se 1 (by rfl) ⟨439298, by rfl⟩ : syracuseStep 585731 = 878597) B878597
theorem B585761 : Blo 389765 585761 := bstep (se 2 (by rfl) ⟨219660, by rfl⟩ : syracuseStep 585761 = 439321) B439321
theorem B585779 : Blo 389765 585779 := bstep (se 1 (by rfl) ⟨439334, by rfl⟩ : syracuseStep 585779 = 878669) B878669
theorem B585809 : Blo 389765 585809 := bstep (se 2 (by rfl) ⟨219678, by rfl⟩ : syracuseStep 585809 = 439357) B439357
theorem B880721 : Blo 389765 880721 := bstep (se 2 (by rfl) ⟨330270, by rfl⟩ : syracuseStep 880721 = 660541) B660541
theorem B585827 : Blo 389765 585827 := bstep (se 1 (by rfl) ⟨439370, by rfl⟩ : syracuseStep 585827 = 878741) B878741
theorem B880739 : Blo 389765 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B585857 : Blo 389765 585857 := bstep (se 2 (by rfl) ⟨219696, by rfl⟩ : syracuseStep 585857 = 439393) B439393
theorem B1339523 : Blo 389765 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1667213 : Blo 389765 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B585875 : Blo 389765 585875 := bstep (se 1 (by rfl) ⟨439406, by rfl⟩ : syracuseStep 585875 = 878813) B878813
theorem B585905 : Blo 389765 585905 := bstep (se 2 (by rfl) ⟨219714, by rfl⟩ : syracuseStep 585905 = 439429) B439429
theorem B585923 : Blo 389765 585923 := bstep (se 1 (by rfl) ⟨439442, by rfl⟩ : syracuseStep 585923 = 878885) B878885
theorem B585953 : Blo 389765 585953 := bstep (se 2 (by rfl) ⟨219732, by rfl⟩ : syracuseStep 585953 = 439465) B439465
theorem B1110257 : Blo 389765 1110257 := bstep (se 2 (by rfl) ⟨416346, by rfl⟩ : syracuseStep 1110257 = 832693) B832693
theorem B585971 : Blo 389765 585971 := bstep (se 1 (by rfl) ⟨439478, by rfl⟩ : syracuseStep 585971 = 878957) B878957
theorem B586001 : Blo 389765 586001 := bstep (se 2 (by rfl) ⟨219750, by rfl⟩ : syracuseStep 586001 = 439501) B439501
theorem B586019 : Blo 389765 586019 := bstep (se 1 (by rfl) ⟨439514, by rfl⟩ : syracuseStep 586019 = 879029) B879029
theorem B586049 : Blo 389765 586049 := bstep (se 2 (by rfl) ⟨219768, by rfl⟩ : syracuseStep 586049 = 439537) B439537
theorem B586067 : Blo 389765 586067 := bstep (se 1 (by rfl) ⟨439550, by rfl⟩ : syracuseStep 586067 = 879101) B879101
theorem B586097 : Blo 389765 586097 := bstep (se 2 (by rfl) ⟨219786, by rfl⟩ : syracuseStep 586097 = 439573) B439573
theorem B881009 : Blo 389765 881009 := bstep (se 2 (by rfl) ⟨330378, by rfl⟩ : syracuseStep 881009 = 660757) B660757
theorem B586115 : Blo 389765 586115 := bstep (se 1 (by rfl) ⟨439586, by rfl⟩ : syracuseStep 586115 = 879173) B879173
theorem B881027 : Blo 389765 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B586145 : Blo 389765 586145 := bstep (se 2 (by rfl) ⟨219804, by rfl⟩ : syracuseStep 586145 = 439609) B439609
theorem B1929635 : Blo 389765 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B1110449 : Blo 389765 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B2683313 : Blo 389765 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B586163 : Blo 389765 586163 := bstep (se 1 (by rfl) ⟨439622, by rfl⟩ : syracuseStep 586163 = 879245) B879245
theorem B586193 : Blo 389765 586193 := bstep (se 2 (by rfl) ⟨219822, by rfl⟩ : syracuseStep 586193 = 439645) B439645
theorem B586211 : Blo 389765 586211 := bstep (se 1 (by rfl) ⟨439658, by rfl⟩ : syracuseStep 586211 = 879317) B879317
theorem B586241 : Blo 389765 586241 := bstep (se 2 (by rfl) ⟨219840, by rfl⟩ : syracuseStep 586241 = 439681) B439681
theorem B586259 : Blo 389765 586259 := bstep (se 1 (by rfl) ⟨439694, by rfl⟩ : syracuseStep 586259 = 879389) B879389
theorem B586289 : Blo 389765 586289 := bstep (se 2 (by rfl) ⟨219858, by rfl⟩ : syracuseStep 586289 = 439717) B439717
theorem B586307 : Blo 389765 586307 := bstep (se 1 (by rfl) ⟨439730, by rfl⟩ : syracuseStep 586307 = 879461) B879461
theorem B586337 : Blo 389765 586337 := bstep (se 2 (by rfl) ⟨219876, by rfl⟩ : syracuseStep 586337 = 439753) B439753
theorem B848497 : Blo 389765 848497 := bstep (se 2 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 848497 = 636373) B636373
theorem B586355 : Blo 389765 586355 := bstep (se 1 (by rfl) ⟨439766, by rfl⟩ : syracuseStep 586355 = 879533) B879533
theorem B586385 : Blo 389765 586385 := bstep (se 2 (by rfl) ⟨219894, by rfl⟩ : syracuseStep 586385 = 439789) B439789
theorem B881297 : Blo 389765 881297 := bstep (se 2 (by rfl) ⟨330486, by rfl⟩ : syracuseStep 881297 = 660973) B660973
theorem B389779 : Blo 389765 389779 := bstep (se 1 (by rfl) ⟨292334, by rfl⟩ : syracuseStep 389779 = 584669) B584669
theorem B389795 : Blo 389765 389795 := bstep (se 1 (by rfl) ⟨292346, by rfl⟩ : syracuseStep 389795 = 584693) B584693
theorem B586403 : Blo 389765 586403 := bstep (se 1 (by rfl) ⟨439802, by rfl⟩ : syracuseStep 586403 = 879605) B879605
theorem B881315 : Blo 389765 881315 := bstep (se 1 (by rfl) ⟨660986, by rfl⟩ : syracuseStep 881315 = 1321973) B1321973
theorem B2224817 : Blo 389765 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B389811 : Blo 389765 389811 := bstep (se 1 (by rfl) ⟨292358, by rfl⟩ : syracuseStep 389811 = 584717) B584717
theorem B586433 : Blo 389765 586433 := bstep (se 2 (by rfl) ⟨219912, by rfl⟩ : syracuseStep 586433 = 439825) B439825
theorem B389827 : Blo 389765 389827 := bstep (se 1 (by rfl) ⟨292370, by rfl⟩ : syracuseStep 389827 = 584741) B584741
theorem B389843 : Blo 389765 389843 := bstep (se 1 (by rfl) ⟨292382, by rfl⟩ : syracuseStep 389843 = 584765) B584765
theorem B586451 : Blo 389765 586451 := bstep (se 1 (by rfl) ⟨439838, by rfl⟩ : syracuseStep 586451 = 879677) B879677
theorem B389859 : Blo 389765 389859 := bstep (se 1 (by rfl) ⟨292394, by rfl⟩ : syracuseStep 389859 = 584789) B584789
theorem B586481 : Blo 389765 586481 := bstep (se 2 (by rfl) ⟨219930, by rfl⟩ : syracuseStep 586481 = 439861) B439861
theorem B389875 : Blo 389765 389875 := bstep (se 1 (by rfl) ⟨292406, by rfl⟩ : syracuseStep 389875 = 584813) B584813
theorem B389891 : Blo 389765 389891 := bstep (se 1 (by rfl) ⟨292418, by rfl⟩ : syracuseStep 389891 = 584837) B584837
theorem B586499 : Blo 389765 586499 := bstep (se 1 (by rfl) ⟨439874, by rfl⟩ : syracuseStep 586499 = 879749) B879749
theorem B389907 : Blo 389765 389907 := bstep (se 1 (by rfl) ⟨292430, by rfl⟩ : syracuseStep 389907 = 584861) B584861
theorem B586529 : Blo 389765 586529 := bstep (se 2 (by rfl) ⟨219948, by rfl⟩ : syracuseStep 586529 = 439897) B439897
theorem B389923 : Blo 389765 389923 := bstep (se 1 (by rfl) ⟨292442, by rfl⟩ : syracuseStep 389923 = 584885) B584885
theorem B389939 : Blo 389765 389939 := bstep (se 1 (by rfl) ⟨292454, by rfl⟩ : syracuseStep 389939 = 584909) B584909
theorem B586547 : Blo 389765 586547 := bstep (se 1 (by rfl) ⟨439910, by rfl⟩ : syracuseStep 586547 = 879821) B879821
theorem B389955 : Blo 389765 389955 := bstep (se 1 (by rfl) ⟨292466, by rfl⟩ : syracuseStep 389955 = 584933) B584933
theorem B586577 : Blo 389765 586577 := bstep (se 2 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 586577 = 439933) B439933
theorem B389971 : Blo 389765 389971 := bstep (se 1 (by rfl) ⟨292478, by rfl⟩ : syracuseStep 389971 = 584957) B584957
theorem B389987 : Blo 389765 389987 := bstep (se 1 (by rfl) ⟨292490, by rfl⟩ : syracuseStep 389987 = 584981) B584981
theorem B586595 : Blo 389765 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B390003 : Blo 389765 390003 := bstep (se 1 (by rfl) ⟨292502, by rfl⟩ : syracuseStep 390003 = 585005) B585005
theorem B586625 : Blo 389765 586625 := bstep (se 2 (by rfl) ⟨219984, by rfl⟩ : syracuseStep 586625 = 439969) B439969
theorem B390019 : Blo 389765 390019 := bstep (se 1 (by rfl) ⟨292514, by rfl⟩ : syracuseStep 390019 = 585029) B585029
theorem B390035 : Blo 389765 390035 := bstep (se 1 (by rfl) ⟨292526, by rfl⟩ : syracuseStep 390035 = 585053) B585053
theorem B586643 : Blo 389765 586643 := bstep (se 1 (by rfl) ⟨439982, by rfl⟩ : syracuseStep 586643 = 879965) B879965
theorem B390051 : Blo 389765 390051 := bstep (se 1 (by rfl) ⟨292538, by rfl⟩ : syracuseStep 390051 = 585077) B585077
theorem B586673 : Blo 389765 586673 := bstep (se 2 (by rfl) ⟨220002, by rfl⟩ : syracuseStep 586673 = 440005) B440005
theorem B881585 : Blo 389765 881585 := bstep (se 2 (by rfl) ⟨330594, by rfl⟩ : syracuseStep 881585 = 661189) B661189
theorem B390067 : Blo 389765 390067 := bstep (se 1 (by rfl) ⟨292550, by rfl⟩ : syracuseStep 390067 = 585101) B585101
theorem B390083 : Blo 389765 390083 := bstep (se 1 (by rfl) ⟨292562, by rfl⟩ : syracuseStep 390083 = 585125) B585125
theorem B586691 : Blo 389765 586691 := bstep (se 1 (by rfl) ⟨440018, by rfl⟩ : syracuseStep 586691 = 880037) B880037
theorem B881603 : Blo 389765 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B390099 : Blo 389765 390099 := bstep (se 1 (by rfl) ⟨292574, by rfl⟩ : syracuseStep 390099 = 585149) B585149
theorem B586721 : Blo 389765 586721 := bstep (se 2 (by rfl) ⟨220020, by rfl⟩ : syracuseStep 586721 = 440041) B440041
theorem B390115 : Blo 389765 390115 := bstep (se 1 (by rfl) ⟨292586, by rfl⟩ : syracuseStep 390115 = 585173) B585173
theorem B390131 : Blo 389765 390131 := bstep (se 1 (by rfl) ⟨292598, by rfl⟩ : syracuseStep 390131 = 585197) B585197
theorem B586739 : Blo 389765 586739 := bstep (se 1 (by rfl) ⟨440054, by rfl⟩ : syracuseStep 586739 = 880109) B880109
theorem B390147 : Blo 389765 390147 := bstep (se 1 (by rfl) ⟨292610, by rfl⟩ : syracuseStep 390147 = 585221) B585221
theorem B586769 : Blo 389765 586769 := bstep (se 2 (by rfl) ⟨220038, by rfl⟩ : syracuseStep 586769 = 440077) B440077
theorem B390163 : Blo 389765 390163 := bstep (se 1 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 390163 = 585245) B585245
theorem B390179 : Blo 389765 390179 := bstep (se 1 (by rfl) ⟨292634, by rfl⟩ : syracuseStep 390179 = 585269) B585269
theorem B586787 : Blo 389765 586787 := bstep (se 1 (by rfl) ⟨440090, by rfl⟩ : syracuseStep 586787 = 880181) B880181
theorem B390195 : Blo 389765 390195 := bstep (se 1 (by rfl) ⟨292646, by rfl⟩ : syracuseStep 390195 = 585293) B585293
theorem B586817 : Blo 389765 586817 := bstep (se 2 (by rfl) ⟨220056, by rfl⟩ : syracuseStep 586817 = 440113) B440113
theorem B390211 : Blo 389765 390211 := bstep (se 1 (by rfl) ⟨292658, by rfl⟩ : syracuseStep 390211 = 585317) B585317
theorem B390227 : Blo 389765 390227 := bstep (se 1 (by rfl) ⟨292670, by rfl⟩ : syracuseStep 390227 = 585341) B585341
theorem B586835 : Blo 389765 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B390243 : Blo 389765 390243 := bstep (se 1 (by rfl) ⟨292682, by rfl⟩ : syracuseStep 390243 = 585365) B585365
theorem B586865 : Blo 389765 586865 := bstep (se 2 (by rfl) ⟨220074, by rfl⟩ : syracuseStep 586865 = 440149) B440149
theorem B390259 : Blo 389765 390259 := bstep (se 1 (by rfl) ⟨292694, by rfl⟩ : syracuseStep 390259 = 585389) B585389
theorem B390275 : Blo 389765 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B586883 : Blo 389765 586883 := bstep (se 1 (by rfl) ⟨440162, by rfl⟩ : syracuseStep 586883 = 880325) B880325
theorem B390291 : Blo 389765 390291 := bstep (se 1 (by rfl) ⟨292718, by rfl⟩ : syracuseStep 390291 = 585437) B585437
theorem B586913 : Blo 389765 586913 := bstep (se 2 (by rfl) ⟨220092, by rfl⟩ : syracuseStep 586913 = 440185) B440185
theorem B390307 : Blo 389765 390307 := bstep (se 1 (by rfl) ⟨292730, by rfl⟩ : syracuseStep 390307 = 585461) B585461
theorem B390323 : Blo 389765 390323 := bstep (se 1 (by rfl) ⟨292742, by rfl⟩ : syracuseStep 390323 = 585485) B585485
theorem B586931 : Blo 389765 586931 := bstep (se 1 (by rfl) ⟨440198, by rfl⟩ : syracuseStep 586931 = 880397) B880397
theorem B390339 : Blo 389765 390339 := bstep (se 1 (by rfl) ⟨292754, by rfl⟩ : syracuseStep 390339 = 585509) B585509
theorem B4027589 : Blo 389765 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B586961 : Blo 389765 586961 := bstep (se 2 (by rfl) ⟨220110, by rfl⟩ : syracuseStep 586961 = 440221) B440221
theorem B881873 : Blo 389765 881873 := bstep (se 2 (by rfl) ⟨330702, by rfl⟩ : syracuseStep 881873 = 661405) B661405
theorem B390355 : Blo 389765 390355 := bstep (se 1 (by rfl) ⟨292766, by rfl⟩ : syracuseStep 390355 = 585533) B585533
theorem B390371 : Blo 389765 390371 := bstep (se 1 (by rfl) ⟨292778, by rfl⟩ : syracuseStep 390371 = 585557) B585557
theorem B5010659 : Blo 389765 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B586979 : Blo 389765 586979 := bstep (se 1 (by rfl) ⟨440234, by rfl⟩ : syracuseStep 586979 = 880469) B880469
theorem B881891 : Blo 389765 881891 := bstep (se 1 (by rfl) ⟨661418, by rfl⟩ : syracuseStep 881891 = 1322837) B1322837
theorem B390387 : Blo 389765 390387 := bstep (se 1 (by rfl) ⟨292790, by rfl⟩ : syracuseStep 390387 = 585581) B585581
theorem B587009 : Blo 389765 587009 := bstep (se 2 (by rfl) ⟨220128, by rfl⟩ : syracuseStep 587009 = 440257) B440257
theorem B390403 : Blo 389765 390403 := bstep (se 1 (by rfl) ⟨292802, by rfl⟩ : syracuseStep 390403 = 585605) B585605
theorem B390419 : Blo 389765 390419 := bstep (se 1 (by rfl) ⟨292814, by rfl⟩ : syracuseStep 390419 = 585629) B585629
theorem B587027 : Blo 389765 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B390435 : Blo 389765 390435 := bstep (se 1 (by rfl) ⟨292826, by rfl⟩ : syracuseStep 390435 = 585653) B585653
theorem B587057 : Blo 389765 587057 := bstep (se 2 (by rfl) ⟨220146, by rfl⟩ : syracuseStep 587057 = 440293) B440293
theorem B390451 : Blo 389765 390451 := bstep (se 1 (by rfl) ⟨292838, by rfl⟩ : syracuseStep 390451 = 585677) B585677
theorem B390467 : Blo 389765 390467 := bstep (se 1 (by rfl) ⟨292850, by rfl⟩ : syracuseStep 390467 = 585701) B585701
theorem B587075 : Blo 389765 587075 := bstep (se 1 (by rfl) ⟨440306, by rfl⟩ : syracuseStep 587075 = 880613) B880613
theorem B390483 : Blo 389765 390483 := bstep (se 1 (by rfl) ⟨292862, by rfl⟩ : syracuseStep 390483 = 585725) B585725
theorem B587105 : Blo 389765 587105 := bstep (se 2 (by rfl) ⟨220164, by rfl⟩ : syracuseStep 587105 = 440329) B440329
theorem B390499 : Blo 389765 390499 := bstep (se 1 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 390499 = 585749) B585749
theorem B390515 : Blo 389765 390515 := bstep (se 1 (by rfl) ⟨292886, by rfl⟩ : syracuseStep 390515 = 585773) B585773
theorem B587123 : Blo 389765 587123 := bstep (se 1 (by rfl) ⟨440342, by rfl⟩ : syracuseStep 587123 = 880685) B880685
theorem B390531 : Blo 389765 390531 := bstep (se 1 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 390531 = 585797) B585797
theorem B1111441 : Blo 389765 1111441 := bstep (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) B833581
theorem B587153 : Blo 389765 587153 := bstep (se 2 (by rfl) ⟨220182, by rfl⟩ : syracuseStep 587153 = 440365) B440365
theorem B390547 : Blo 389765 390547 := bstep (se 1 (by rfl) ⟨292910, by rfl⟩ : syracuseStep 390547 = 585821) B585821
theorem B390563 : Blo 389765 390563 := bstep (se 1 (by rfl) ⟨292922, by rfl⟩ : syracuseStep 390563 = 585845) B585845
theorem B587171 : Blo 389765 587171 := bstep (se 1 (by rfl) ⟨440378, by rfl⟩ : syracuseStep 587171 = 880757) B880757
theorem B390579 : Blo 389765 390579 := bstep (se 1 (by rfl) ⟨292934, by rfl⟩ : syracuseStep 390579 = 585869) B585869
theorem B587201 : Blo 389765 587201 := bstep (se 2 (by rfl) ⟨220200, by rfl⟩ : syracuseStep 587201 = 440401) B440401
theorem B390595 : Blo 389765 390595 := bstep (se 1 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 390595 = 585893) B585893
theorem B390611 : Blo 389765 390611 := bstep (se 1 (by rfl) ⟨292958, by rfl⟩ : syracuseStep 390611 = 585917) B585917
theorem B587219 : Blo 389765 587219 := bstep (se 1 (by rfl) ⟨440414, by rfl⟩ : syracuseStep 587219 = 880829) B880829
theorem B390627 : Blo 389765 390627 := bstep (se 1 (by rfl) ⟨292970, by rfl⟩ : syracuseStep 390627 = 585941) B585941
theorem B2848241 : Blo 389765 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B587249 : Blo 389765 587249 := bstep (se 2 (by rfl) ⟨220218, by rfl⟩ : syracuseStep 587249 = 440437) B440437
theorem B390643 : Blo 389765 390643 := bstep (se 1 (by rfl) ⟨292982, by rfl⟩ : syracuseStep 390643 = 585965) B585965
theorem B882161 : Blo 389765 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B390659 : Blo 389765 390659 := bstep (se 1 (by rfl) ⟨292994, by rfl⟩ : syracuseStep 390659 = 585989) B585989
theorem B587267 : Blo 389765 587267 := bstep (se 1 (by rfl) ⟨440450, by rfl⟩ : syracuseStep 587267 = 880901) B880901
theorem B882179 : Blo 389765 882179 := bstep (se 1 (by rfl) ⟨661634, by rfl⟩ : syracuseStep 882179 = 1323269) B1323269
theorem B390675 : Blo 389765 390675 := bstep (se 1 (by rfl) ⟨293006, by rfl⟩ : syracuseStep 390675 = 586013) B586013
theorem B587297 : Blo 389765 587297 := bstep (se 2 (by rfl) ⟨220236, by rfl⟩ : syracuseStep 587297 = 440473) B440473
theorem B390691 : Blo 389765 390691 := bstep (se 1 (by rfl) ⟨293018, by rfl⟩ : syracuseStep 390691 = 586037) B586037
theorem B390707 : Blo 389765 390707 := bstep (se 1 (by rfl) ⟨293030, by rfl⟩ : syracuseStep 390707 = 586061) B586061
theorem B587315 : Blo 389765 587315 := bstep (se 1 (by rfl) ⟨440486, by rfl⟩ : syracuseStep 587315 = 880973) B880973
theorem B390723 : Blo 389765 390723 := bstep (se 1 (by rfl) ⟨293042, by rfl⟩ : syracuseStep 390723 = 586085) B586085
theorem B587345 : Blo 389765 587345 := bstep (se 2 (by rfl) ⟨220254, by rfl⟩ : syracuseStep 587345 = 440509) B440509
theorem B390739 : Blo 389765 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B390755 : Blo 389765 390755 := bstep (se 1 (by rfl) ⟨293066, by rfl⟩ : syracuseStep 390755 = 586133) B586133
theorem B587363 : Blo 389765 587363 := bstep (se 1 (by rfl) ⟨440522, by rfl⟩ : syracuseStep 587363 = 881045) B881045
theorem B390771 : Blo 389765 390771 := bstep (se 1 (by rfl) ⟨293078, by rfl⟩ : syracuseStep 390771 = 586157) B586157
theorem B587393 : Blo 389765 587393 := bstep (se 2 (by rfl) ⟨220272, by rfl⟩ : syracuseStep 587393 = 440545) B440545
theorem B390787 : Blo 389765 390787 := bstep (se 1 (by rfl) ⟨293090, by rfl⟩ : syracuseStep 390787 = 586181) B586181
theorem B390803 : Blo 389765 390803 := bstep (se 1 (by rfl) ⟨293102, by rfl⟩ : syracuseStep 390803 = 586205) B586205
theorem B587411 : Blo 389765 587411 := bstep (se 1 (by rfl) ⟨440558, by rfl⟩ : syracuseStep 587411 = 881117) B881117
theorem B1111715 : Blo 389765 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B390819 : Blo 389765 390819 := bstep (se 1 (by rfl) ⟨293114, by rfl⟩ : syracuseStep 390819 = 586229) B586229
theorem B587441 : Blo 389765 587441 := bstep (se 2 (by rfl) ⟨220290, by rfl⟩ : syracuseStep 587441 = 440581) B440581
theorem B390835 : Blo 389765 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B390851 : Blo 389765 390851 := bstep (se 1 (by rfl) ⟨293138, by rfl⟩ : syracuseStep 390851 = 586277) B586277
theorem B587459 : Blo 389765 587459 := bstep (se 1 (by rfl) ⟨440594, by rfl⟩ : syracuseStep 587459 = 881189) B881189
theorem B390867 : Blo 389765 390867 := bstep (se 1 (by rfl) ⟨293150, by rfl⟩ : syracuseStep 390867 = 586301) B586301
theorem B587489 : Blo 389765 587489 := bstep (se 2 (by rfl) ⟨220308, by rfl⟩ : syracuseStep 587489 = 440617) B440617
theorem B390883 : Blo 389765 390883 := bstep (se 1 (by rfl) ⟨293162, by rfl⟩ : syracuseStep 390883 = 586325) B586325
theorem B390899 : Blo 389765 390899 := bstep (se 1 (by rfl) ⟨293174, by rfl⟩ : syracuseStep 390899 = 586349) B586349
theorem B587507 : Blo 389765 587507 := bstep (se 1 (by rfl) ⟨440630, by rfl⟩ : syracuseStep 587507 = 881261) B881261
theorem B390915 : Blo 389765 390915 := bstep (se 1 (by rfl) ⟨293186, by rfl⟩ : syracuseStep 390915 = 586373) B586373
theorem B587537 : Blo 389765 587537 := bstep (se 2 (by rfl) ⟨220326, by rfl⟩ : syracuseStep 587537 = 440653) B440653
theorem B882449 : Blo 389765 882449 := bstep (se 2 (by rfl) ⟨330918, by rfl⟩ : syracuseStep 882449 = 661837) B661837
theorem B390931 : Blo 389765 390931 := bstep (se 1 (by rfl) ⟨293198, by rfl⟩ : syracuseStep 390931 = 586397) B586397
theorem B390947 : Blo 389765 390947 := bstep (se 1 (by rfl) ⟨293210, by rfl⟩ : syracuseStep 390947 = 586421) B586421
theorem B587555 : Blo 389765 587555 := bstep (se 1 (by rfl) ⟨440666, by rfl⟩ : syracuseStep 587555 = 881333) B881333
theorem B882467 : Blo 389765 882467 := bstep (se 1 (by rfl) ⟨661850, by rfl⟩ : syracuseStep 882467 = 1323701) B1323701
theorem B390963 : Blo 389765 390963 := bstep (se 1 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 390963 = 586445) B586445
theorem B587585 : Blo 389765 587585 := bstep (se 2 (by rfl) ⟨220344, by rfl⟩ : syracuseStep 587585 = 440689) B440689
theorem B390979 : Blo 389765 390979 := bstep (se 1 (by rfl) ⟨293234, by rfl⟩ : syracuseStep 390979 = 586469) B586469
theorem B390995 : Blo 389765 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B587603 : Blo 389765 587603 := bstep (se 1 (by rfl) ⟨440702, by rfl⟩ : syracuseStep 587603 = 881405) B881405
theorem B1111907 : Blo 389765 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B391011 : Blo 389765 391011 := bstep (se 1 (by rfl) ⟨293258, by rfl⟩ : syracuseStep 391011 = 586517) B586517
theorem B587633 : Blo 389765 587633 := bstep (se 2 (by rfl) ⟨220362, by rfl⟩ : syracuseStep 587633 = 440725) B440725
theorem B391027 : Blo 389765 391027 := bstep (se 1 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 391027 = 586541) B586541
theorem B391043 : Blo 389765 391043 := bstep (se 1 (by rfl) ⟨293282, by rfl⟩ : syracuseStep 391043 = 586565) B586565
theorem B587651 : Blo 389765 587651 := bstep (se 1 (by rfl) ⟨440738, by rfl⟩ : syracuseStep 587651 = 881477) B881477
theorem B391059 : Blo 389765 391059 := bstep (se 1 (by rfl) ⟨293294, by rfl⟩ : syracuseStep 391059 = 586589) B586589
theorem B587681 : Blo 389765 587681 := bstep (se 2 (by rfl) ⟨220380, by rfl⟩ : syracuseStep 587681 = 440761) B440761
theorem B391075 : Blo 389765 391075 := bstep (se 1 (by rfl) ⟨293306, by rfl⟩ : syracuseStep 391075 = 586613) B586613
theorem B391091 : Blo 389765 391091 := bstep (se 1 (by rfl) ⟨293318, by rfl⟩ : syracuseStep 391091 = 586637) B586637
theorem B587699 : Blo 389765 587699 := bstep (se 1 (by rfl) ⟨440774, by rfl⟩ : syracuseStep 587699 = 881549) B881549
theorem B391107 : Blo 389765 391107 := bstep (se 1 (by rfl) ⟨293330, by rfl⟩ : syracuseStep 391107 = 586661) B586661
theorem B587729 : Blo 389765 587729 := bstep (se 2 (by rfl) ⟨220398, by rfl⟩ : syracuseStep 587729 = 440797) B440797
theorem B391123 : Blo 389765 391123 := bstep (se 1 (by rfl) ⟨293342, by rfl⟩ : syracuseStep 391123 = 586685) B586685
theorem B391139 : Blo 389765 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B587747 : Blo 389765 587747 := bstep (se 1 (by rfl) ⟨440810, by rfl⟩ : syracuseStep 587747 = 881621) B881621
theorem B391155 : Blo 389765 391155 := bstep (se 1 (by rfl) ⟨293366, by rfl⟩ : syracuseStep 391155 = 586733) B586733
theorem B587777 : Blo 389765 587777 := bstep (se 2 (by rfl) ⟨220416, by rfl⟩ : syracuseStep 587777 = 440833) B440833
theorem B391171 : Blo 389765 391171 := bstep (se 1 (by rfl) ⟨293378, by rfl⟩ : syracuseStep 391171 = 586757) B586757
theorem B391187 : Blo 389765 391187 := bstep (se 1 (by rfl) ⟨293390, by rfl⟩ : syracuseStep 391187 = 586781) B586781
theorem B587795 : Blo 389765 587795 := bstep (se 1 (by rfl) ⟨440846, by rfl⟩ : syracuseStep 587795 = 881693) B881693
theorem B391203 : Blo 389765 391203 := bstep (se 1 (by rfl) ⟨293402, by rfl⟩ : syracuseStep 391203 = 586805) B586805
theorem B587825 : Blo 389765 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B882737 : Blo 389765 882737 := bstep (se 2 (by rfl) ⟨331026, by rfl⟩ : syracuseStep 882737 = 662053) B662053
theorem B391219 : Blo 389765 391219 := bstep (se 1 (by rfl) ⟨293414, by rfl⟩ : syracuseStep 391219 = 586829) B586829
theorem B391235 : Blo 389765 391235 := bstep (se 1 (by rfl) ⟨293426, by rfl⟩ : syracuseStep 391235 = 586853) B586853
theorem B587843 : Blo 389765 587843 := bstep (se 1 (by rfl) ⟨440882, by rfl⟩ : syracuseStep 587843 = 881765) B881765
theorem B882755 : Blo 389765 882755 := bstep (se 1 (by rfl) ⟨662066, by rfl⟩ : syracuseStep 882755 = 1324133) B1324133
theorem B391251 : Blo 389765 391251 := bstep (se 1 (by rfl) ⟨293438, by rfl⟩ : syracuseStep 391251 = 586877) B586877
theorem B587873 : Blo 389765 587873 := bstep (se 2 (by rfl) ⟨220452, by rfl⟩ : syracuseStep 587873 = 440905) B440905
theorem B2226275 : Blo 389765 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B391267 : Blo 389765 391267 := bstep (se 1 (by rfl) ⟨293450, by rfl⟩ : syracuseStep 391267 = 586901) B586901
theorem B391283 : Blo 389765 391283 := bstep (se 1 (by rfl) ⟨293462, by rfl⟩ : syracuseStep 391283 = 586925) B586925
theorem B587891 : Blo 389765 587891 := bstep (se 1 (by rfl) ⟨440918, by rfl⟩ : syracuseStep 587891 = 881837) B881837
theorem B391299 : Blo 389765 391299 := bstep (se 1 (by rfl) ⟨293474, by rfl⟩ : syracuseStep 391299 = 586949) B586949
theorem B587921 : Blo 389765 587921 := bstep (se 2 (by rfl) ⟨220470, by rfl⟩ : syracuseStep 587921 = 440941) B440941
theorem B391315 : Blo 389765 391315 := bstep (se 1 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 391315 = 586973) B586973
theorem B391331 : Blo 389765 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B587939 : Blo 389765 587939 := bstep (se 1 (by rfl) ⟨440954, by rfl⟩ : syracuseStep 587939 = 881909) B881909
theorem B391347 : Blo 389765 391347 := bstep (se 1 (by rfl) ⟨293510, by rfl⟩ : syracuseStep 391347 = 587021) B587021
theorem B587969 : Blo 389765 587969 := bstep (se 2 (by rfl) ⟨220488, by rfl⟩ : syracuseStep 587969 = 440977) B440977
theorem B391363 : Blo 389765 391363 := bstep (se 1 (by rfl) ⟨293522, by rfl⟩ : syracuseStep 391363 = 587045) B587045
theorem B391379 : Blo 389765 391379 := bstep (se 1 (by rfl) ⟨293534, by rfl⟩ : syracuseStep 391379 = 587069) B587069
theorem B587987 : Blo 389765 587987 := bstep (se 1 (by rfl) ⟨440990, by rfl⟩ : syracuseStep 587987 = 881981) B881981
theorem B1407203 : Blo 389765 1407203 := bstep (se 1 (by rfl) ⟨1055402, by rfl⟩ : syracuseStep 1407203 = 2110805) B2110805
theorem B391395 : Blo 389765 391395 := bstep (se 1 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 391395 = 587093) B587093
theorem B588017 : Blo 389765 588017 := bstep (se 2 (by rfl) ⟨220506, by rfl⟩ : syracuseStep 588017 = 441013) B441013
theorem B391411 : Blo 389765 391411 := bstep (se 1 (by rfl) ⟨293558, by rfl⟩ : syracuseStep 391411 = 587117) B587117
theorem B555265 : Blo 389765 555265 := bstep (se 2 (by rfl) ⟨208224, by rfl⟩ : syracuseStep 555265 = 416449) B416449
theorem B391427 : Blo 389765 391427 := bstep (se 1 (by rfl) ⟨293570, by rfl⟩ : syracuseStep 391427 = 587141) B587141
theorem B588035 : Blo 389765 588035 := bstep (se 1 (by rfl) ⟨441026, by rfl⟩ : syracuseStep 588035 = 882053) B882053
theorem B391443 : Blo 389765 391443 := bstep (se 1 (by rfl) ⟨293582, by rfl⟩ : syracuseStep 391443 = 587165) B587165
theorem B588065 : Blo 389765 588065 := bstep (se 2 (by rfl) ⟨220524, by rfl⟩ : syracuseStep 588065 = 441049) B441049
theorem B391459 : Blo 389765 391459 := bstep (se 1 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 391459 = 587189) B587189
theorem B391475 : Blo 389765 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B588083 : Blo 389765 588083 := bstep (se 1 (by rfl) ⟨441062, by rfl⟩ : syracuseStep 588083 = 882125) B882125
theorem B391491 : Blo 389765 391491 := bstep (se 1 (by rfl) ⟨293618, by rfl⟩ : syracuseStep 391491 = 587237) B587237
theorem B588113 : Blo 389765 588113 := bstep (se 2 (by rfl) ⟨220542, by rfl⟩ : syracuseStep 588113 = 441085) B441085
theorem B883025 : Blo 389765 883025 := bstep (se 2 (by rfl) ⟨331134, by rfl⟩ : syracuseStep 883025 = 662269) B662269
theorem B391507 : Blo 389765 391507 := bstep (se 1 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 391507 = 587261) B587261
theorem B391523 : Blo 389765 391523 := bstep (se 1 (by rfl) ⟨293642, by rfl⟩ : syracuseStep 391523 = 587285) B587285
theorem B588131 : Blo 389765 588131 := bstep (se 1 (by rfl) ⟨441098, by rfl⟩ : syracuseStep 588131 = 882197) B882197
theorem B883043 : Blo 389765 883043 := bstep (se 1 (by rfl) ⟨662282, by rfl⟩ : syracuseStep 883043 = 1324565) B1324565
theorem B391539 : Blo 389765 391539 := bstep (se 1 (by rfl) ⟨293654, by rfl⟩ : syracuseStep 391539 = 587309) B587309
theorem B588161 : Blo 389765 588161 := bstep (se 2 (by rfl) ⟨220560, by rfl⟩ : syracuseStep 588161 = 441121) B441121
theorem B391555 : Blo 389765 391555 := bstep (se 1 (by rfl) ⟨293666, by rfl⟩ : syracuseStep 391555 = 587333) B587333
theorem B391571 : Blo 389765 391571 := bstep (se 1 (by rfl) ⟨293678, by rfl⟩ : syracuseStep 391571 = 587357) B587357
theorem B588179 : Blo 389765 588179 := bstep (se 1 (by rfl) ⟨441134, by rfl⟩ : syracuseStep 588179 = 882269) B882269
theorem B391587 : Blo 389765 391587 := bstep (se 1 (by rfl) ⟨293690, by rfl⟩ : syracuseStep 391587 = 587381) B587381
theorem B588209 : Blo 389765 588209 := bstep (se 2 (by rfl) ⟨220578, by rfl⟩ : syracuseStep 588209 = 441157) B441157
theorem B391603 : Blo 389765 391603 := bstep (se 1 (by rfl) ⟨293702, by rfl⟩ : syracuseStep 391603 = 587405) B587405
theorem B391619 : Blo 389765 391619 := bstep (se 1 (by rfl) ⟨293714, by rfl⟩ : syracuseStep 391619 = 587429) B587429
theorem B588227 : Blo 389765 588227 := bstep (se 1 (by rfl) ⟨441170, by rfl⟩ : syracuseStep 588227 = 882341) B882341
theorem B391635 : Blo 389765 391635 := bstep (se 1 (by rfl) ⟨293726, by rfl⟩ : syracuseStep 391635 = 587453) B587453
theorem B588257 : Blo 389765 588257 := bstep (se 2 (by rfl) ⟨220596, by rfl⟩ : syracuseStep 588257 = 441193) B441193
theorem B391651 : Blo 389765 391651 := bstep (se 1 (by rfl) ⟨293738, by rfl⟩ : syracuseStep 391651 = 587477) B587477
theorem B391667 : Blo 389765 391667 := bstep (se 1 (by rfl) ⟨293750, by rfl⟩ : syracuseStep 391667 = 587501) B587501
theorem B588275 : Blo 389765 588275 := bstep (se 1 (by rfl) ⟨441206, by rfl⟩ : syracuseStep 588275 = 882413) B882413
theorem B391683 : Blo 389765 391683 := bstep (se 1 (by rfl) ⟨293762, by rfl⟩ : syracuseStep 391683 = 587525) B587525
theorem B588305 : Blo 389765 588305 := bstep (se 2 (by rfl) ⟨220614, by rfl⟩ : syracuseStep 588305 = 441229) B441229
theorem B391699 : Blo 389765 391699 := bstep (se 1 (by rfl) ⟨293774, by rfl⟩ : syracuseStep 391699 = 587549) B587549
theorem B391715 : Blo 389765 391715 := bstep (se 1 (by rfl) ⟨293786, by rfl⟩ : syracuseStep 391715 = 587573) B587573
theorem B588323 : Blo 389765 588323 := bstep (se 1 (by rfl) ⟨441242, by rfl⟩ : syracuseStep 588323 = 882485) B882485
theorem B391731 : Blo 389765 391731 := bstep (se 1 (by rfl) ⟨293798, by rfl⟩ : syracuseStep 391731 = 587597) B587597
theorem B588353 : Blo 389765 588353 := bstep (se 2 (by rfl) ⟨220632, by rfl⟩ : syracuseStep 588353 = 441265) B441265
theorem B391747 : Blo 389765 391747 := bstep (se 1 (by rfl) ⟨293810, by rfl⟩ : syracuseStep 391747 = 587621) B587621
theorem B555601 : Blo 389765 555601 := bstep (se 2 (by rfl) ⟨208350, by rfl⟩ : syracuseStep 555601 = 416701) B416701
theorem B391763 : Blo 389765 391763 := bstep (se 1 (by rfl) ⟨293822, by rfl⟩ : syracuseStep 391763 = 587645) B587645
theorem B588371 : Blo 389765 588371 := bstep (se 1 (by rfl) ⟨441278, by rfl⟩ : syracuseStep 588371 = 882557) B882557
theorem B391779 : Blo 389765 391779 := bstep (se 1 (by rfl) ⟨293834, by rfl⟩ : syracuseStep 391779 = 587669) B587669
theorem B588401 : Blo 389765 588401 := bstep (se 2 (by rfl) ⟨220650, by rfl⟩ : syracuseStep 588401 = 441301) B441301
theorem B883313 : Blo 389765 883313 := bstep (se 2 (by rfl) ⟨331242, by rfl⟩ : syracuseStep 883313 = 662485) B662485
theorem B391795 : Blo 389765 391795 := bstep (se 1 (by rfl) ⟨293846, by rfl⟩ : syracuseStep 391795 = 587693) B587693
theorem B391811 : Blo 389765 391811 := bstep (se 1 (by rfl) ⟨293858, by rfl⟩ : syracuseStep 391811 = 587717) B587717
theorem B588419 : Blo 389765 588419 := bstep (se 1 (by rfl) ⟨441314, by rfl⟩ : syracuseStep 588419 = 882629) B882629
theorem B883331 : Blo 389765 883331 := bstep (se 1 (by rfl) ⟨662498, by rfl⟩ : syracuseStep 883331 = 1324997) B1324997
theorem B1112717 : Blo 389765 1112717 := bstep (se 3 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 1112717 = 417269) B417269
theorem B391827 : Blo 389765 391827 := bstep (se 1 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 391827 = 587741) B587741
theorem B588449 : Blo 389765 588449 := bstep (se 2 (by rfl) ⟨220668, by rfl⟩ : syracuseStep 588449 = 441337) B441337
theorem B391843 : Blo 389765 391843 := bstep (se 1 (by rfl) ⟨293882, by rfl⟩ : syracuseStep 391843 = 587765) B587765
theorem B391859 : Blo 389765 391859 := bstep (se 1 (by rfl) ⟨293894, by rfl⟩ : syracuseStep 391859 = 587789) B587789
theorem B588467 : Blo 389765 588467 := bstep (se 1 (by rfl) ⟨441350, by rfl⟩ : syracuseStep 588467 = 882701) B882701
theorem B391875 : Blo 389765 391875 := bstep (se 1 (by rfl) ⟨293906, by rfl⟩ : syracuseStep 391875 = 587813) B587813
theorem B588497 : Blo 389765 588497 := bstep (se 2 (by rfl) ⟨220686, by rfl⟩ : syracuseStep 588497 = 441373) B441373
theorem B391891 : Blo 389765 391891 := bstep (se 1 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 391891 = 587837) B587837
theorem B391907 : Blo 389765 391907 := bstep (se 1 (by rfl) ⟨293930, by rfl⟩ : syracuseStep 391907 = 587861) B587861
theorem B588515 : Blo 389765 588515 := bstep (se 1 (by rfl) ⟨441386, by rfl⟩ : syracuseStep 588515 = 882773) B882773
theorem B391923 : Blo 389765 391923 := bstep (se 1 (by rfl) ⟨293942, by rfl⟩ : syracuseStep 391923 = 587885) B587885
theorem B588545 : Blo 389765 588545 := bstep (se 2 (by rfl) ⟨220704, by rfl⟩ : syracuseStep 588545 = 441409) B441409
theorem B391939 : Blo 389765 391939 := bstep (se 1 (by rfl) ⟨293954, by rfl⟩ : syracuseStep 391939 = 587909) B587909
theorem B391955 : Blo 389765 391955 := bstep (se 1 (by rfl) ⟨293966, by rfl⟩ : syracuseStep 391955 = 587933) B587933
theorem B588563 : Blo 389765 588563 := bstep (se 1 (by rfl) ⟨441422, by rfl⟩ : syracuseStep 588563 = 882845) B882845
theorem B391971 : Blo 389765 391971 := bstep (se 1 (by rfl) ⟨293978, by rfl⟩ : syracuseStep 391971 = 587957) B587957
theorem B588593 : Blo 389765 588593 := bstep (se 2 (by rfl) ⟨220722, by rfl⟩ : syracuseStep 588593 = 441445) B441445
theorem B391987 : Blo 389765 391987 := bstep (se 1 (by rfl) ⟨293990, by rfl⟩ : syracuseStep 391987 = 587981) B587981
theorem B1112899 : Blo 389765 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B392003 : Blo 389765 392003 := bstep (se 1 (by rfl) ⟨294002, by rfl⟩ : syracuseStep 392003 = 588005) B588005
theorem B588611 : Blo 389765 588611 := bstep (se 1 (by rfl) ⟨441458, by rfl⟩ : syracuseStep 588611 = 882917) B882917
theorem B392019 : Blo 389765 392019 := bstep (se 1 (by rfl) ⟨294014, by rfl⟩ : syracuseStep 392019 = 588029) B588029
theorem B588641 : Blo 389765 588641 := bstep (se 2 (by rfl) ⟨220740, by rfl⟩ : syracuseStep 588641 = 441481) B441481
theorem B392035 : Blo 389765 392035 := bstep (se 1 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 392035 = 588053) B588053
theorem B392051 : Blo 389765 392051 := bstep (se 1 (by rfl) ⟨294038, by rfl⟩ : syracuseStep 392051 = 588077) B588077
theorem B588659 : Blo 389765 588659 := bstep (se 1 (by rfl) ⟨441494, by rfl⟩ : syracuseStep 588659 = 882989) B882989
theorem B392067 : Blo 389765 392067 := bstep (se 1 (by rfl) ⟨294050, by rfl⟩ : syracuseStep 392067 = 588101) B588101
theorem B588689 : Blo 389765 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B883601 : Blo 389765 883601 := bstep (se 2 (by rfl) ⟨331350, by rfl⟩ : syracuseStep 883601 = 662701) B662701
theorem B392083 : Blo 389765 392083 := bstep (se 1 (by rfl) ⟨294062, by rfl⟩ : syracuseStep 392083 = 588125) B588125
theorem B883619 : Blo 389765 883619 := bstep (se 1 (by rfl) ⟨662714, by rfl⟩ : syracuseStep 883619 = 1325429) B1325429
theorem B392099 : Blo 389765 392099 := bstep (se 1 (by rfl) ⟨294074, by rfl⟩ : syracuseStep 392099 = 588149) B588149
theorem B588707 : Blo 389765 588707 := bstep (se 1 (by rfl) ⟨441530, by rfl⟩ : syracuseStep 588707 = 883061) B883061
theorem B392115 : Blo 389765 392115 := bstep (se 1 (by rfl) ⟨294086, by rfl⟩ : syracuseStep 392115 = 588173) B588173
theorem B588737 : Blo 389765 588737 := bstep (se 2 (by rfl) ⟨220776, by rfl⟩ : syracuseStep 588737 = 441553) B441553
theorem B392131 : Blo 389765 392131 := bstep (se 1 (by rfl) ⟨294098, by rfl⟩ : syracuseStep 392131 = 588197) B588197
theorem B392147 : Blo 389765 392147 := bstep (se 1 (by rfl) ⟨294110, by rfl⟩ : syracuseStep 392147 = 588221) B588221
theorem B588755 : Blo 389765 588755 := bstep (se 1 (by rfl) ⟨441566, by rfl⟩ : syracuseStep 588755 = 883133) B883133
theorem B392163 : Blo 389765 392163 := bstep (se 1 (by rfl) ⟨294122, by rfl⟩ : syracuseStep 392163 = 588245) B588245
theorem B588785 : Blo 389765 588785 := bstep (se 2 (by rfl) ⟨220794, by rfl⟩ : syracuseStep 588785 = 441589) B441589
theorem B392179 : Blo 389765 392179 := bstep (se 1 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 392179 = 588269) B588269
theorem B392195 : Blo 389765 392195 := bstep (se 1 (by rfl) ⟨294146, by rfl⟩ : syracuseStep 392195 = 588293) B588293
theorem B588803 : Blo 389765 588803 := bstep (se 1 (by rfl) ⟨441602, by rfl⟩ : syracuseStep 588803 = 883205) B883205
theorem B392211 : Blo 389765 392211 := bstep (se 1 (by rfl) ⟨294158, by rfl⟩ : syracuseStep 392211 = 588317) B588317
theorem B588833 : Blo 389765 588833 := bstep (se 2 (by rfl) ⟨220812, by rfl⟩ : syracuseStep 588833 = 441625) B441625
theorem B392227 : Blo 389765 392227 := bstep (se 1 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 392227 = 588341) B588341
theorem B392243 : Blo 389765 392243 := bstep (se 1 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 392243 = 588365) B588365
theorem B588851 : Blo 389765 588851 := bstep (se 1 (by rfl) ⟨441638, by rfl⟩ : syracuseStep 588851 = 883277) B883277
theorem B392259 : Blo 389765 392259 := bstep (se 1 (by rfl) ⟨294194, by rfl⟩ : syracuseStep 392259 = 588389) B588389
theorem B2227277 : Blo 389765 2227277 := bstep (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) B835229
theorem B588881 : Blo 389765 588881 := bstep (se 2 (by rfl) ⟨220830, by rfl⟩ : syracuseStep 588881 = 441661) B441661
theorem B392275 : Blo 389765 392275 := bstep (se 1 (by rfl) ⟨294206, by rfl⟩ : syracuseStep 392275 = 588413) B588413
theorem B392291 : Blo 389765 392291 := bstep (se 1 (by rfl) ⟨294218, by rfl⟩ : syracuseStep 392291 = 588437) B588437
theorem B588899 : Blo 389765 588899 := bstep (se 1 (by rfl) ⟨441674, by rfl⟩ : syracuseStep 588899 = 883349) B883349
theorem B392307 : Blo 389765 392307 := bstep (se 1 (by rfl) ⟨294230, by rfl⟩ : syracuseStep 392307 = 588461) B588461
theorem B588929 : Blo 389765 588929 := bstep (se 2 (by rfl) ⟨220848, by rfl⟩ : syracuseStep 588929 = 441697) B441697
theorem B392323 : Blo 389765 392323 := bstep (se 1 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 392323 = 588485) B588485
theorem B392339 : Blo 389765 392339 := bstep (se 1 (by rfl) ⟨294254, by rfl⟩ : syracuseStep 392339 = 588509) B588509
theorem B588947 : Blo 389765 588947 := bstep (se 1 (by rfl) ⟨441710, by rfl⟩ : syracuseStep 588947 = 883421) B883421
theorem B556193 : Blo 389765 556193 := bstep (se 2 (by rfl) ⟨208572, by rfl⟩ : syracuseStep 556193 = 417145) B417145
theorem B392355 : Blo 389765 392355 := bstep (se 1 (by rfl) ⟨294266, by rfl⟩ : syracuseStep 392355 = 588533) B588533
theorem B1670321 : Blo 389765 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B588977 : Blo 389765 588977 := bstep (se 2 (by rfl) ⟨220866, by rfl⟩ : syracuseStep 588977 = 441733) B441733
theorem B392371 : Blo 389765 392371 := bstep (se 1 (by rfl) ⟨294278, by rfl⟩ : syracuseStep 392371 = 588557) B588557
theorem B883889 : Blo 389765 883889 := bstep (se 2 (by rfl) ⟨331458, by rfl⟩ : syracuseStep 883889 = 662917) B662917
theorem B392387 : Blo 389765 392387 := bstep (se 1 (by rfl) ⟨294290, by rfl⟩ : syracuseStep 392387 = 588581) B588581
theorem B588995 : Blo 389765 588995 := bstep (se 1 (by rfl) ⟨441746, by rfl⟩ : syracuseStep 588995 = 883493) B883493
theorem B883907 : Blo 389765 883907 := bstep (se 1 (by rfl) ⟨662930, by rfl⟩ : syracuseStep 883907 = 1325861) B1325861
theorem B1277137 : Blo 389765 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B392403 : Blo 389765 392403 := bstep (se 1 (by rfl) ⟨294302, by rfl⟩ : syracuseStep 392403 = 588605) B588605
theorem B589025 : Blo 389765 589025 := bstep (se 2 (by rfl) ⟨220884, by rfl⟩ : syracuseStep 589025 = 441769) B441769
theorem B392419 : Blo 389765 392419 := bstep (se 1 (by rfl) ⟨294314, by rfl⟩ : syracuseStep 392419 = 588629) B588629
theorem B392435 : Blo 389765 392435 := bstep (se 1 (by rfl) ⟨294326, by rfl⟩ : syracuseStep 392435 = 588653) B588653
theorem B589043 : Blo 389765 589043 := bstep (se 1 (by rfl) ⟨441782, by rfl⟩ : syracuseStep 589043 = 883565) B883565
theorem B392451 : Blo 389765 392451 := bstep (se 1 (by rfl) ⟨294338, by rfl⟩ : syracuseStep 392451 = 588677) B588677
theorem B589073 : Blo 389765 589073 := bstep (se 2 (by rfl) ⟨220902, by rfl⟩ : syracuseStep 589073 = 441805) B441805
theorem B392467 : Blo 389765 392467 := bstep (se 1 (by rfl) ⟨294350, by rfl⟩ : syracuseStep 392467 = 588701) B588701
theorem B392483 : Blo 389765 392483 := bstep (se 1 (by rfl) ⟨294362, by rfl⟩ : syracuseStep 392483 = 588725) B588725
theorem B589091 : Blo 389765 589091 := bstep (se 1 (by rfl) ⟨441818, by rfl⟩ : syracuseStep 589091 = 883637) B883637
theorem B1113389 : Blo 389765 1113389 := bstep (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) B417521
theorem B392499 : Blo 389765 392499 := bstep (se 1 (by rfl) ⟨294374, by rfl⟩ : syracuseStep 392499 = 588749) B588749
theorem B589121 : Blo 389765 589121 := bstep (se 2 (by rfl) ⟨220920, by rfl⟩ : syracuseStep 589121 = 441841) B441841
theorem B392515 : Blo 389765 392515 := bstep (se 1 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 392515 = 588773) B588773
theorem B392531 : Blo 389765 392531 := bstep (se 1 (by rfl) ⟨294398, by rfl⟩ : syracuseStep 392531 = 588797) B588797
theorem B589139 : Blo 389765 589139 := bstep (se 1 (by rfl) ⟨441854, by rfl⟩ : syracuseStep 589139 = 883709) B883709
theorem B392547 : Blo 389765 392547 := bstep (se 1 (by rfl) ⟨294410, by rfl⟩ : syracuseStep 392547 = 588821) B588821
theorem B589169 : Blo 389765 589169 := bstep (se 2 (by rfl) ⟨220938, by rfl⟩ : syracuseStep 589169 = 441877) B441877
theorem B392563 : Blo 389765 392563 := bstep (se 1 (by rfl) ⟨294422, by rfl⟩ : syracuseStep 392563 = 588845) B588845
theorem B392579 : Blo 389765 392579 := bstep (se 1 (by rfl) ⟨294434, by rfl⟩ : syracuseStep 392579 = 588869) B588869
theorem B589187 : Blo 389765 589187 := bstep (se 1 (by rfl) ⟨441890, by rfl⟩ : syracuseStep 589187 = 883781) B883781
theorem B2522501 : Blo 389765 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B392595 : Blo 389765 392595 := bstep (se 1 (by rfl) ⟨294446, by rfl⟩ : syracuseStep 392595 = 588893) B588893
theorem B589217 : Blo 389765 589217 := bstep (se 2 (by rfl) ⟨220956, by rfl⟩ : syracuseStep 589217 = 441913) B441913
theorem B392611 : Blo 389765 392611 := bstep (se 1 (by rfl) ⟨294458, by rfl⟩ : syracuseStep 392611 = 588917) B588917
theorem B392627 : Blo 389765 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B589235 : Blo 389765 589235 := bstep (se 1 (by rfl) ⟨441926, by rfl⟩ : syracuseStep 589235 = 883853) B883853
theorem B392643 : Blo 389765 392643 := bstep (se 1 (by rfl) ⟨294482, by rfl⟩ : syracuseStep 392643 = 588965) B588965
theorem B589265 : Blo 389765 589265 := bstep (se 2 (by rfl) ⟨220974, by rfl⟩ : syracuseStep 589265 = 441949) B441949
theorem B884177 : Blo 389765 884177 := bstep (se 2 (by rfl) ⟨331566, by rfl⟩ : syracuseStep 884177 = 663133) B663133
theorem B392659 : Blo 389765 392659 := bstep (se 1 (by rfl) ⟨294494, by rfl⟩ : syracuseStep 392659 = 588989) B588989
theorem B392675 : Blo 389765 392675 := bstep (se 1 (by rfl) ⟨294506, by rfl⟩ : syracuseStep 392675 = 589013) B589013
theorem B589283 : Blo 389765 589283 := bstep (se 1 (by rfl) ⟨441962, by rfl⟩ : syracuseStep 589283 = 883925) B883925
theorem B884195 : Blo 389765 884195 := bstep (se 1 (by rfl) ⟨663146, by rfl⟩ : syracuseStep 884195 = 1326293) B1326293
theorem B392691 : Blo 389765 392691 := bstep (se 1 (by rfl) ⟨294518, by rfl⟩ : syracuseStep 392691 = 589037) B589037
theorem B589313 : Blo 389765 589313 := bstep (se 2 (by rfl) ⟨220992, by rfl⟩ : syracuseStep 589313 = 441985) B441985
theorem B392707 : Blo 389765 392707 := bstep (se 1 (by rfl) ⟨294530, by rfl⟩ : syracuseStep 392707 = 589061) B589061
theorem B392723 : Blo 389765 392723 := bstep (se 1 (by rfl) ⟨294542, by rfl⟩ : syracuseStep 392723 = 589085) B589085
theorem B589331 : Blo 389765 589331 := bstep (se 1 (by rfl) ⟨441998, by rfl⟩ : syracuseStep 589331 = 883997) B883997
theorem B392739 : Blo 389765 392739 := bstep (se 1 (by rfl) ⟨294554, by rfl⟩ : syracuseStep 392739 = 589109) B589109
theorem B589361 : Blo 389765 589361 := bstep (se 2 (by rfl) ⟨221010, by rfl⟩ : syracuseStep 589361 = 442021) B442021
theorem B392755 : Blo 389765 392755 := bstep (se 1 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 392755 = 589133) B589133
theorem B392771 : Blo 389765 392771 := bstep (se 1 (by rfl) ⟨294578, by rfl⟩ : syracuseStep 392771 = 589157) B589157
theorem B589379 : Blo 389765 589379 := bstep (se 1 (by rfl) ⟨442034, by rfl⟩ : syracuseStep 589379 = 884069) B884069
theorem B392787 : Blo 389765 392787 := bstep (se 1 (by rfl) ⟨294590, by rfl⟩ : syracuseStep 392787 = 589181) B589181
theorem B589409 : Blo 389765 589409 := bstep (se 2 (by rfl) ⟨221028, by rfl⟩ : syracuseStep 589409 = 442057) B442057
theorem B392803 : Blo 389765 392803 := bstep (se 1 (by rfl) ⟨294602, by rfl⟩ : syracuseStep 392803 = 589205) B589205
theorem B392819 : Blo 389765 392819 := bstep (se 1 (by rfl) ⟨294614, by rfl⟩ : syracuseStep 392819 = 589229) B589229
theorem B589427 : Blo 389765 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B392835 : Blo 389765 392835 := bstep (se 1 (by rfl) ⟨294626, by rfl⟩ : syracuseStep 392835 = 589253) B589253
theorem B589457 : Blo 389765 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B392851 : Blo 389765 392851 := bstep (se 1 (by rfl) ⟨294638, by rfl⟩ : syracuseStep 392851 = 589277) B589277
theorem B589475 : Blo 389765 589475 := bstep (se 1 (by rfl) ⟨442106, by rfl⟩ : syracuseStep 589475 = 884213) B884213
theorem B392867 : Blo 389765 392867 := bstep (se 1 (by rfl) ⟨294650, by rfl⟩ : syracuseStep 392867 = 589301) B589301
theorem B556723 : Blo 389765 556723 := bstep (se 1 (by rfl) ⟨417542, by rfl⟩ : syracuseStep 556723 = 835085) B835085
theorem B392883 : Blo 389765 392883 := bstep (se 1 (by rfl) ⟨294662, by rfl⟩ : syracuseStep 392883 = 589325) B589325
theorem B589505 : Blo 389765 589505 := bstep (se 2 (by rfl) ⟨221064, by rfl⟩ : syracuseStep 589505 = 442129) B442129
theorem B392899 : Blo 389765 392899 := bstep (se 1 (by rfl) ⟨294674, by rfl⟩ : syracuseStep 392899 = 589349) B589349
theorem B392915 : Blo 389765 392915 := bstep (se 1 (by rfl) ⟨294686, by rfl⟩ : syracuseStep 392915 = 589373) B589373
theorem B589523 : Blo 389765 589523 := bstep (se 1 (by rfl) ⟨442142, by rfl⟩ : syracuseStep 589523 = 884285) B884285
theorem B392931 : Blo 389765 392931 := bstep (se 1 (by rfl) ⟨294698, by rfl⟩ : syracuseStep 392931 = 589397) B589397
theorem B589553 : Blo 389765 589553 := bstep (se 2 (by rfl) ⟨221082, by rfl⟩ : syracuseStep 589553 = 442165) B442165
theorem B884465 : Blo 389765 884465 := bstep (se 2 (by rfl) ⟨331674, by rfl⟩ : syracuseStep 884465 = 663349) B663349
theorem B392947 : Blo 389765 392947 := bstep (se 1 (by rfl) ⟨294710, by rfl⟩ : syracuseStep 392947 = 589421) B589421
theorem B392963 : Blo 389765 392963 := bstep (se 1 (by rfl) ⟨294722, by rfl⟩ : syracuseStep 392963 = 589445) B589445
theorem B589571 : Blo 389765 589571 := bstep (se 1 (by rfl) ⟨442178, by rfl⟩ : syracuseStep 589571 = 884357) B884357
theorem B884483 : Blo 389765 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B392979 : Blo 389765 392979 := bstep (se 1 (by rfl) ⟨294734, by rfl⟩ : syracuseStep 392979 = 589469) B589469
theorem B589601 : Blo 389765 589601 := bstep (se 2 (by rfl) ⟨221100, by rfl⟩ : syracuseStep 589601 = 442201) B442201
theorem B392995 : Blo 389765 392995 := bstep (se 1 (by rfl) ⟨294746, by rfl⟩ : syracuseStep 392995 = 589493) B589493
theorem B393011 : Blo 389765 393011 := bstep (se 1 (by rfl) ⟨294758, by rfl⟩ : syracuseStep 393011 = 589517) B589517
theorem B589619 : Blo 389765 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B393027 : Blo 389765 393027 := bstep (se 1 (by rfl) ⟨294770, by rfl⟩ : syracuseStep 393027 = 589541) B589541
theorem B1670989 : Blo 389765 1670989 := bstep (se 3 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 1670989 = 626621) B626621
theorem B589649 : Blo 389765 589649 := bstep (se 2 (by rfl) ⟨221118, by rfl⟩ : syracuseStep 589649 = 442237) B442237
theorem B393043 : Blo 389765 393043 := bstep (se 1 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 393043 = 589565) B589565
theorem B393059 : Blo 389765 393059 := bstep (se 1 (by rfl) ⟨294794, by rfl⟩ : syracuseStep 393059 = 589589) B589589
theorem B589667 : Blo 389765 589667 := bstep (se 1 (by rfl) ⟨442250, by rfl⟩ : syracuseStep 589667 = 884501) B884501
theorem B393075 : Blo 389765 393075 := bstep (se 1 (by rfl) ⟨294806, by rfl⟩ : syracuseStep 393075 = 589613) B589613
theorem B589697 : Blo 389765 589697 := bstep (se 2 (by rfl) ⟨221136, by rfl⟩ : syracuseStep 589697 = 442273) B442273
theorem B393091 : Blo 389765 393091 := bstep (se 1 (by rfl) ⟨294818, by rfl⟩ : syracuseStep 393091 = 589637) B589637
theorem B393107 : Blo 389765 393107 := bstep (se 1 (by rfl) ⟨294830, by rfl⟩ : syracuseStep 393107 = 589661) B589661
theorem B589715 : Blo 389765 589715 := bstep (se 1 (by rfl) ⟨442286, by rfl⟩ : syracuseStep 589715 = 884573) B884573
theorem B393123 : Blo 389765 393123 := bstep (se 1 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 393123 = 589685) B589685
theorem B589745 : Blo 389765 589745 := bstep (se 2 (by rfl) ⟨221154, by rfl⟩ : syracuseStep 589745 = 442309) B442309
theorem B393139 : Blo 389765 393139 := bstep (se 1 (by rfl) ⟨294854, by rfl⟩ : syracuseStep 393139 = 589709) B589709
theorem B393155 : Blo 389765 393155 := bstep (se 1 (by rfl) ⟨294866, by rfl⟩ : syracuseStep 393155 = 589733) B589733
theorem B589763 : Blo 389765 589763 := bstep (se 1 (by rfl) ⟨442322, by rfl⟩ : syracuseStep 589763 = 884645) B884645
theorem B393171 : Blo 389765 393171 := bstep (se 1 (by rfl) ⟨294878, by rfl⟩ : syracuseStep 393171 = 589757) B589757
theorem B589793 : Blo 389765 589793 := bstep (se 2 (by rfl) ⟨221172, by rfl⟩ : syracuseStep 589793 = 442345) B442345
theorem B1343459 : Blo 389765 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B393187 : Blo 389765 393187 := bstep (se 1 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 393187 = 589781) B589781
theorem B393203 : Blo 389765 393203 := bstep (se 1 (by rfl) ⟨294902, by rfl⟩ : syracuseStep 393203 = 589805) B589805
theorem B589811 : Blo 389765 589811 := bstep (se 1 (by rfl) ⟨442358, by rfl⟩ : syracuseStep 589811 = 884717) B884717
theorem B589835 : Blo 389765 589835 := bstep (se 1 (by rfl) ⟨442376, by rfl⟩ : syracuseStep 589835 = 884753) B884753
theorem B393227 : Blo 389765 393227 := bstep (se 1 (by rfl) ⟨294920, by rfl⟩ : syracuseStep 393227 = 589841) B589841
theorem B589847 : Blo 389765 589847 := bstep (se 1 (by rfl) ⟨442385, by rfl⟩ : syracuseStep 589847 = 884771) B884771
theorem B393239 : Blo 389765 393239 := bstep (se 1 (by rfl) ⟨294929, by rfl⟩ : syracuseStep 393239 = 589859) B589859
theorem B393259 : Blo 389765 393259 := bstep (se 1 (by rfl) ⟨294944, by rfl⟩ : syracuseStep 393259 = 589889) B589889
theorem B393271 : Blo 389765 393271 := bstep (se 1 (by rfl) ⟨294953, by rfl⟩ : syracuseStep 393271 = 589907) B589907
theorem B393291 : Blo 389765 393291 := bstep (se 1 (by rfl) ⟨294968, by rfl⟩ : syracuseStep 393291 = 589937) B589937
theorem B393303 : Blo 389765 393303 := bstep (se 1 (by rfl) ⟨294977, by rfl⟩ : syracuseStep 393303 = 589955) B589955
theorem B884825 : Blo 389765 884825 := bstep (se 2 (by rfl) ⟨331809, by rfl⟩ : syracuseStep 884825 = 663619) B663619
theorem B589913 : Blo 389765 589913 := bstep (se 2 (by rfl) ⟨221217, by rfl⟩ : syracuseStep 589913 = 442435) B442435
theorem B393323 : Blo 389765 393323 := bstep (se 1 (by rfl) ⟨294992, by rfl⟩ : syracuseStep 393323 = 589985) B589985
theorem B393335 : Blo 389765 393335 := bstep (se 1 (by rfl) ⟨295001, by rfl⟩ : syracuseStep 393335 = 590003) B590003
theorem B393355 : Blo 389765 393355 := bstep (se 1 (by rfl) ⟨295016, by rfl⟩ : syracuseStep 393355 = 590033) B590033
theorem B1671313 : Blo 389765 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B393367 : Blo 389765 393367 := bstep (se 1 (by rfl) ⟨295025, by rfl⟩ : syracuseStep 393367 = 590051) B590051
theorem B393387 : Blo 389765 393387 := bstep (se 1 (by rfl) ⟨295040, by rfl⟩ : syracuseStep 393387 = 590081) B590081
theorem B1671347 : Blo 389765 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B884915 : Blo 389765 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B393399 : Blo 389765 393399 := bstep (se 1 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 393399 = 590099) B590099
theorem B590027 : Blo 389765 590027 := bstep (se 1 (by rfl) ⟨442520, by rfl⟩ : syracuseStep 590027 = 885041) B885041
theorem B393419 : Blo 389765 393419 := bstep (se 1 (by rfl) ⟨295064, by rfl⟩ : syracuseStep 393419 = 590129) B590129
theorem B884951 : Blo 389765 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B590039 : Blo 389765 590039 := bstep (se 1 (by rfl) ⟨442529, by rfl⟩ : syracuseStep 590039 = 885059) B885059
theorem B393431 : Blo 389765 393431 := bstep (se 1 (by rfl) ⟨295073, by rfl⟩ : syracuseStep 393431 = 590147) B590147
theorem B393451 : Blo 389765 393451 := bstep (se 1 (by rfl) ⟨295088, by rfl⟩ : syracuseStep 393451 = 590177) B590177
theorem B393463 : Blo 389765 393463 := bstep (se 1 (by rfl) ⟨295097, by rfl⟩ : syracuseStep 393463 = 590195) B590195
theorem B393483 : Blo 389765 393483 := bstep (se 1 (by rfl) ⟨295112, by rfl⟩ : syracuseStep 393483 = 590225) B590225
theorem B1114391 : Blo 389765 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B590105 : Blo 389765 590105 := bstep (se 2 (by rfl) ⟨221289, by rfl⟩ : syracuseStep 590105 = 442579) B442579
theorem B393495 : Blo 389765 393495 := bstep (se 1 (by rfl) ⟨295121, by rfl⟩ : syracuseStep 393495 = 590243) B590243
theorem B393515 : Blo 389765 393515 := bstep (se 1 (by rfl) ⟨295136, by rfl⟩ : syracuseStep 393515 = 590273) B590273
theorem B393527 : Blo 389765 393527 := bstep (se 1 (by rfl) ⟨295145, by rfl⟩ : syracuseStep 393527 = 590291) B590291
theorem B393547 : Blo 389765 393547 := bstep (se 1 (by rfl) ⟨295160, by rfl⟩ : syracuseStep 393547 = 590321) B590321
theorem B393559 : Blo 389765 393559 := bstep (se 1 (by rfl) ⟨295169, by rfl⟩ : syracuseStep 393559 = 590339) B590339
theorem B393579 : Blo 389765 393579 := bstep (se 1 (by rfl) ⟨295184, by rfl⟩ : syracuseStep 393579 = 590369) B590369
theorem B17170805 : Blo 389765 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B393591 : Blo 389765 393591 := bstep (se 1 (by rfl) ⟨295193, by rfl⟩ : syracuseStep 393591 = 590387) B590387
theorem B885131 : Blo 389765 885131 := bstep (se 1 (by rfl) ⟨663848, by rfl⟩ : syracuseStep 885131 = 1327697) B1327697
theorem B590219 : Blo 389765 590219 := bstep (se 1 (by rfl) ⟨442664, by rfl⟩ : syracuseStep 590219 = 885329) B885329
theorem B393611 : Blo 389765 393611 := bstep (se 1 (by rfl) ⟨295208, by rfl⟩ : syracuseStep 393611 = 590417) B590417
theorem B590231 : Blo 389765 590231 := bstep (se 1 (by rfl) ⟨442673, by rfl⟩ : syracuseStep 590231 = 885347) B885347
theorem B393623 : Blo 389765 393623 := bstep (se 1 (by rfl) ⟨295217, by rfl⟩ : syracuseStep 393623 = 590435) B590435
theorem B393643 : Blo 389765 393643 := bstep (se 1 (by rfl) ⟨295232, by rfl⟩ : syracuseStep 393643 = 590465) B590465
theorem B393655 : Blo 389765 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B885185 : Blo 389765 885185 := bstep (se 2 (by rfl) ⟨331944, by rfl⟩ : syracuseStep 885185 = 663889) B663889
theorem B393675 : Blo 389765 393675 := bstep (se 1 (by rfl) ⟨295256, by rfl⟩ : syracuseStep 393675 = 590513) B590513
theorem B393687 : Blo 389765 393687 := bstep (se 1 (by rfl) ⟨295265, by rfl⟩ : syracuseStep 393687 = 590531) B590531
theorem B590297 : Blo 389765 590297 := bstep (se 2 (by rfl) ⟨221361, by rfl⟩ : syracuseStep 590297 = 442723) B442723
theorem B393707 : Blo 389765 393707 := bstep (se 1 (by rfl) ⟨295280, by rfl⟩ : syracuseStep 393707 = 590561) B590561
theorem B393719 : Blo 389765 393719 := bstep (se 1 (by rfl) ⟨295289, by rfl⟩ : syracuseStep 393719 = 590579) B590579
theorem B393739 : Blo 389765 393739 := bstep (se 1 (by rfl) ⟨295304, by rfl⟩ : syracuseStep 393739 = 590609) B590609
theorem B393751 : Blo 389765 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B590411 : Blo 389765 590411 := bstep (se 1 (by rfl) ⟨442808, by rfl⟩ : syracuseStep 590411 = 885617) B885617
theorem B590423 : Blo 389765 590423 := bstep (se 1 (by rfl) ⟨442817, by rfl⟩ : syracuseStep 590423 = 885635) B885635
theorem B885401 : Blo 389765 885401 := bstep (se 2 (by rfl) ⟨332025, by rfl⟩ : syracuseStep 885401 = 664051) B664051
theorem B590489 : Blo 389765 590489 := bstep (se 2 (by rfl) ⟨221433, by rfl⟩ : syracuseStep 590489 = 442867) B442867
theorem B885491 : Blo 389765 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B590603 : Blo 389765 590603 := bstep (se 1 (by rfl) ⟨442952, by rfl⟩ : syracuseStep 590603 = 885905) B885905
theorem B885527 : Blo 389765 885527 := bstep (se 1 (by rfl) ⟨664145, by rfl⟩ : syracuseStep 885527 = 1328291) B1328291
theorem B590615 : Blo 389765 590615 := bstep (se 1 (by rfl) ⟨442961, by rfl⟩ : syracuseStep 590615 = 885923) B885923
theorem B885707 : Blo 389765 885707 := bstep (se 1 (by rfl) ⟨664280, by rfl⟩ : syracuseStep 885707 = 1328561) B1328561
theorem B885761 : Blo 389765 885761 := bstep (se 2 (by rfl) ⟨332160, by rfl⟩ : syracuseStep 885761 = 664321) B664321
theorem B5670323 : Blo 389765 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B1410605 : Blo 389765 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B40699523 : Blo 389765 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B4523651 : Blo 389765 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B2000657 : Blo 389765 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B559001 : Blo 389765 559001 := bstep (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) B419251
theorem B1673261 : Blo 389765 1673261 := bstep (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) B627473
theorem B1509421 : Blo 389765 1509421 := bstep (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) B566033
theorem B493771 : Blo 389765 493771 := bstep (se 1 (by rfl) ⟨370328, by rfl⟩ : syracuseStep 493771 = 740657) B740657
theorem B756097 : Blo 389765 756097 := bstep (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) B567073
theorem B494039 : Blo 389765 494039 := bstep (se 1 (by rfl) ⟨370529, by rfl⟩ : syracuseStep 494039 = 741059) B741059
theorem B559639 : Blo 389765 559639 := bstep (se 1 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 559639 = 839459) B839459
theorem B1116737 : Blo 389765 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B1673945 : Blo 389765 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B658199 : Blo 389765 658199 := bstep (se 1 (by rfl) ⟨493649, by rfl⟩ : syracuseStep 658199 = 987299) B987299
theorem B658327 : Blo 389765 658327 := bstep (se 1 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 658327 = 987491) B987491
theorem B1117273 : Blo 389765 1117273 := bstep (se 2 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 1117273 = 837955) B837955
theorem B494743 : Blo 389765 494743 := bstep (se 1 (by rfl) ⟨371057, by rfl⟩ : syracuseStep 494743 = 742115) B742115
theorem B560459 : Blo 389765 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B2690405 : Blo 389765 2690405 := bstep (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) B504451
theorem B658955 : Blo 389765 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B659083 : Blo 389765 659083 := bstep (se 1 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 659083 = 988625) B988625
theorem B659225 : Blo 389765 659225 := bstep (se 2 (by rfl) ⟨247209, by rfl⟩ : syracuseStep 659225 = 494419) B494419
theorem B1412939 : Blo 389765 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B659353 : Blo 389765 659353 := bstep (se 2 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 659353 = 494515) B494515
theorem B987187 : Blo 389765 987187 := bstep (se 1 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 987187 = 1480781) B1480781
theorem B987329 : Blo 389765 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B627031 : Blo 389765 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B659927 : Blo 389765 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B8458769 : Blo 389765 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B660055 : Blo 389765 660055 := bstep (se 1 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 660055 = 990083) B990083
theorem B496459 : Blo 389765 496459 := bstep (se 1 (by rfl) ⟨372344, by rfl⟩ : syracuseStep 496459 = 744689) B744689
theorem B3183461 : Blo 389765 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B1315763 : Blo 389765 1315763 := bstep (se 1 (by rfl) ⟨986822, by rfl⟩ : syracuseStep 1315763 = 1973645) B1973645
theorem B1119197 : Blo 389765 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B431191 : Blo 389765 431191 := bstep (se 1 (by rfl) ⟨323393, by rfl⟩ : syracuseStep 431191 = 646787) B646787
theorem B431275 : Blo 389765 431275 := bstep (se 1 (by rfl) ⟨323456, by rfl⟩ : syracuseStep 431275 = 646913) B646913
theorem B1316033 : Blo 389765 1316033 := bstep (se 2 (by rfl) ⟨493512, by rfl⟩ : syracuseStep 1316033 = 987025) B987025
theorem B660683 : Blo 389765 660683 := bstep (se 1 (by rfl) ⟨495512, by rfl⟩ : syracuseStep 660683 = 991025) B991025
theorem B529625 : Blo 389765 529625 := bstep (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) B397219
theorem B1676609 : Blo 389765 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B660811 : Blo 389765 660811 := bstep (se 1 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 660811 = 991217) B991217
theorem B2987441 : Blo 389765 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B988595 : Blo 389765 988595 := bstep (se 1 (by rfl) ⟨741446, by rfl⟩ : syracuseStep 988595 = 1482893) B1482893
theorem B890315 : Blo 389765 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B660953 : Blo 389765 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B2233817 : Blo 389765 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B661081 : Blo 389765 661081 := bstep (se 2 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 661081 = 495811) B495811
theorem B1316573 : Blo 389765 1316573 := bstep (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) B493715
theorem B497431 : Blo 389765 497431 := bstep (se 1 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 497431 = 746147) B746147
theorem B2987927 : Blo 389765 2987927 := bstep (se 1 (by rfl) ⟨2240945, by rfl⟩ : syracuseStep 2987927 = 4481891) B4481891
theorem B11409329 : Blo 389765 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B989131 : Blo 389765 989131 := bstep (se 1 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 989131 = 1483697) B1483697
theorem B989273 : Blo 389765 989273 := bstep (se 2 (by rfl) ⟨370977, by rfl⟩ : syracuseStep 989273 = 741955) B741955
theorem B661655 : Blo 389765 661655 := bstep (se 1 (by rfl) ⟨496241, by rfl⟩ : syracuseStep 661655 = 992483) B992483
theorem B2824409 : Blo 389765 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B792833 : Blo 389765 792833 := bstep (se 2 (by rfl) ⟨297312, by rfl⟩ : syracuseStep 792833 = 594625) B594625
theorem B1480963 : Blo 389765 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B661783 : Blo 389765 661783 := bstep (se 1 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 661783 = 992675) B992675
theorem B3021187 : Blo 389765 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B1481267 : Blo 389765 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B498251 : Blo 389765 498251 := bstep (se 1 (by rfl) ⟨373688, by rfl⟩ : syracuseStep 498251 = 747377) B747377
theorem B1678097 : Blo 389765 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B1317707 : Blo 389765 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B793433 : Blo 389765 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B662411 : Blo 389765 662411 := bstep (se 1 (by rfl) ⟨496808, by rfl⟩ : syracuseStep 662411 = 993617) B993617
theorem B990103 : Blo 389765 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B793523 : Blo 389765 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B662539 : Blo 389765 662539 := bstep (se 1 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 662539 = 993809) B993809
theorem B1317977 : Blo 389765 1317977 := bstep (se 2 (by rfl) ⟨494241, by rfl⟩ : syracuseStep 1317977 = 988483) B988483
theorem B7183511 : Blo 389765 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B662681 : Blo 389765 662681 := bstep (se 2 (by rfl) ⟨248505, by rfl⟩ : syracuseStep 662681 = 497011) B497011
theorem B1481921 : Blo 389765 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B662809 : Blo 389765 662809 := bstep (se 2 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 662809 = 497107) B497107
theorem B990539 : Blo 389765 990539 := bstep (se 1 (by rfl) ⟨742904, by rfl⟩ : syracuseStep 990539 = 1485809) B1485809
theorem B3349937 : Blo 389765 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B7118405 : Blo 389765 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B990913 : Blo 389765 990913 := bstep (se 2 (by rfl) ⟨371592, by rfl⟩ : syracuseStep 990913 = 743185) B743185
theorem B1679069 : Blo 389765 1679069 := bstep (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) B629651
theorem B1318679 : Blo 389765 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B2826049 : Blo 389765 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B663383 : Blo 389765 663383 := bstep (se 1 (by rfl) ⟨497537, by rfl⟩ : syracuseStep 663383 = 995075) B995075
theorem B663511 : Blo 389765 663511 := bstep (se 1 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 663511 = 995267) B995267
theorem B2236481 : Blo 389765 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B893015 : Blo 389765 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B1417409 : Blo 389765 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B1286423 : Blo 389765 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B991511 : Blo 389765 991511 := bstep (se 1 (by rfl) ⟨743633, by rfl⟩ : syracuseStep 991511 = 1487267) B1487267
theorem B1319219 : Blo 389765 1319219 := bstep (se 1 (by rfl) ⟨989414, by rfl⟩ : syracuseStep 1319219 = 1978829) B1978829
theorem B1057175 : Blo 389765 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B1483181 : Blo 389765 1483181 := bstep (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) B556193
theorem B1483211 : Blo 389765 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1319489 : Blo 389765 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B664139 : Blo 389765 664139 := bstep (se 1 (by rfl) ⟨498104, by rfl⟩ : syracuseStep 664139 = 996209) B996209
theorem B4006493 : Blo 389765 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B664267 : Blo 389765 664267 := bstep (se 1 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 664267 = 996401) B996401
theorem B664409 : Blo 389765 664409 := bstep (se 2 (by rfl) ⟨249153, by rfl⟩ : syracuseStep 664409 = 498307) B498307
theorem B893953 : Blo 389765 893953 := bstep (se 2 (by rfl) ⟨335232, by rfl⟩ : syracuseStep 893953 = 670465) B670465
theorem B992321 : Blo 389765 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B1483865 : Blo 389765 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B1320029 : Blo 389765 1320029 := bstep (se 3 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 1320029 = 495011) B495011
theorem B1975427 : Blo 389765 1975427 := bstep (se 1 (by rfl) ⟨1481570, by rfl⟩ : syracuseStep 1975427 = 2963141) B2963141
theorem B1484183 : Blo 389765 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B2827781 : Blo 389765 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B992857 : Blo 389765 992857 := bstep (se 2 (by rfl) ⟨372321, by rfl⟩ : syracuseStep 992857 = 744643) B744643
theorem B2828125 : Blo 389765 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B1583021 : Blo 389765 1583021 := bstep (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) B593633
theorem B1484851 : Blo 389765 1484851 := bstep (se 1 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 1484851 = 2227277) B2227277
theorem B1321163 : Blo 389765 1321163 := bstep (se 1 (by rfl) ⟨990872, by rfl⟩ : syracuseStep 1321163 = 1981745) B1981745
theorem B1681667 : Blo 389765 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B797131 : Blo 389765 797131 := bstep (se 1 (by rfl) ⟨597848, by rfl⟩ : syracuseStep 797131 = 1195697) B1195697
theorem B1321433 : Blo 389765 1321433 := bstep (se 2 (by rfl) ⟨495537, by rfl⟩ : syracuseStep 1321433 = 991075) B991075
theorem B3582557 : Blo 389765 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B993971 : Blo 389765 993971 := bstep (se 1 (by rfl) ⟨745478, by rfl⟩ : syracuseStep 993971 = 1490957) B1490957
theorem B3353561 : Blo 389765 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B994265 : Blo 389765 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B535691 : Blo 389765 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B1322135 : Blo 389765 1322135 := bstep (se 1 (by rfl) ⟨991601, by rfl⟩ : syracuseStep 1322135 = 1983203) B1983203
theorem B1486097 : Blo 389765 1486097 := bstep (se 2 (by rfl) ⟨557286, by rfl⟩ : syracuseStep 1486097 = 1114573) B1114573
theorem B1584791 : Blo 389765 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B896663 : Blo 389765 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B1322675 : Blo 389765 1322675 := bstep (se 1 (by rfl) ⟨992006, by rfl⟩ : syracuseStep 1322675 = 1984013) B1984013
theorem B2961197 : Blo 389765 2961197 := bstep (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) B1110449
theorem B1322945 : Blo 389765 1322945 := bstep (se 2 (by rfl) ⟨496104, by rfl⟩ : syracuseStep 1322945 = 992209) B992209
theorem B1486795 : Blo 389765 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B393207 : Blo 389765 393207 := bstep (se 1 (by rfl) ⟨294905, by rfl⟩ : syracuseStep 393207 = 589811) B589811
theorem B897047 : Blo 389765 897047 := bstep (se 1 (by rfl) ⟨672785, by rfl⟩ : syracuseStep 897047 = 1345571) B1345571
theorem B1781939 : Blo 389765 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1487069 : Blo 389765 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B438583 : Blo 389765 438583 := bstep (se 1 (by rfl) ⟨328937, by rfl⟩ : syracuseStep 438583 = 657875) B657875
theorem B1323485 : Blo 389765 1323485 := bstep (se 3 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 1323485 = 496307) B496307
theorem B438763 : Blo 389765 438763 := bstep (se 1 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 438763 = 658145) B658145
theorem B995915 : Blo 389765 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B438871 : Blo 389765 438871 := bstep (se 1 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 438871 = 658307) B658307
theorem B1258163 : Blo 389765 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B1127105 : Blo 389765 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B439051 : Blo 389765 439051 := bstep (se 1 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 439051 = 658577) B658577
theorem B1979153 : Blo 389765 1979153 := bstep (se 2 (by rfl) ⟨742182, by rfl⟩ : syracuseStep 1979153 = 1484365) B1484365
theorem B439159 : Blo 389765 439159 := bstep (se 1 (by rfl) ⟨329369, by rfl⟩ : syracuseStep 439159 = 658739) B658739
theorem B1487767 : Blo 389765 1487767 := bstep (se 1 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 1487767 = 2231651) B2231651
theorem B1979315 : Blo 389765 1979315 := bstep (se 1 (by rfl) ⟨1484486, by rfl⟩ : syracuseStep 1979315 = 2968973) B2968973
theorem B832513 : Blo 389765 832513 := bstep (se 2 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 832513 = 624385) B624385
theorem B439339 : Blo 389765 439339 := bstep (se 1 (by rfl) ⟨329504, by rfl⟩ : syracuseStep 439339 = 659009) B659009
theorem B439447 : Blo 389765 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B832769 : Blo 389765 832769 := bstep (se 2 (by rfl) ⟨312288, by rfl⟩ : syracuseStep 832769 = 624577) B624577
theorem B2241857 : Blo 389765 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B439627 : Blo 389765 439627 := bstep (se 1 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 439627 = 659441) B659441
theorem B832855 : Blo 389765 832855 := bstep (se 1 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 832855 = 1249283) B1249283
theorem B1258841 : Blo 389765 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B439735 : Blo 389765 439735 := bstep (se 1 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 439735 = 659603) B659603
theorem B3192281 : Blo 389765 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B3356225 : Blo 389765 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B1324619 : Blo 389765 1324619 := bstep (se 1 (by rfl) ⟨993464, by rfl⟩ : syracuseStep 1324619 = 1986929) B1986929
theorem B439915 : Blo 389765 439915 := bstep (se 1 (by rfl) ⟨329936, by rfl⟩ : syracuseStep 439915 = 659873) B659873
theorem B669323 : Blo 389765 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B1488557 : Blo 389765 1488557 := bstep (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) B558209
theorem B440023 : Blo 389765 440023 := bstep (se 1 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 440023 = 660035) B660035
theorem B1324889 : Blo 389765 1324889 := bstep (se 2 (by rfl) ⟨496833, by rfl⟩ : syracuseStep 1324889 = 993667) B993667
theorem B440203 : Blo 389765 440203 := bstep (se 1 (by rfl) ⟨330152, by rfl⟩ : syracuseStep 440203 = 660305) B660305
theorem B440311 : Blo 389765 440311 := bstep (se 1 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 440311 = 660467) B660467
theorem B4536395 : Blo 389765 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B440491 : Blo 389765 440491 := bstep (se 1 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 440491 = 660737) B660737
theorem B1063133 : Blo 389765 1063133 := bstep (se 3 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 1063133 = 398675) B398675
theorem B440599 : Blo 389765 440599 := bstep (se 1 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 440599 = 660899) B660899
theorem B440779 : Blo 389765 440779 := bstep (se 1 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 440779 = 661169) B661169
theorem B702937 : Blo 389765 702937 := bstep (se 2 (by rfl) ⟨263601, by rfl⟩ : syracuseStep 702937 = 527203) B527203
theorem B1325591 : Blo 389765 1325591 := bstep (se 1 (by rfl) ⟨994193, by rfl⟩ : syracuseStep 1325591 = 1988387) B1988387
theorem B440887 : Blo 389765 440887 := bstep (se 1 (by rfl) ⟨330665, by rfl⟩ : syracuseStep 440887 = 661331) B661331
theorem B2112101 : Blo 389765 2112101 := bstep (se 4 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 2112101 = 396019) B396019
theorem B441067 : Blo 389765 441067 := bstep (se 1 (by rfl) ⟨330800, by rfl⟩ : syracuseStep 441067 = 661601) B661601
theorem B703255 : Blo 389765 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B703283 : Blo 389765 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B1981259 : Blo 389765 1981259 := bstep (se 1 (by rfl) ⟨1485944, by rfl⟩ : syracuseStep 1981259 = 2971889) B2971889
theorem B441175 : Blo 389765 441175 := bstep (se 1 (by rfl) ⟨330881, by rfl⟩ : syracuseStep 441175 = 661763) B661763
theorem B6339545 : Blo 389765 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B441355 : Blo 389765 441355 := bstep (se 1 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 441355 = 662033) B662033
theorem B1326131 : Blo 389765 1326131 := bstep (se 1 (by rfl) ⟨994598, by rfl⟩ : syracuseStep 1326131 = 1989197) B1989197
theorem B1489985 : Blo 389765 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B441463 : Blo 389765 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B703745 : Blo 389765 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B441643 : Blo 389765 441643 := bstep (se 1 (by rfl) ⟨331232, by rfl⟩ : syracuseStep 441643 = 662465) B662465
theorem B1326401 : Blo 389765 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B441751 : Blo 389765 441751 := bstep (se 1 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 441751 = 662627) B662627
theorem B2539025 : Blo 389765 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B441931 : Blo 389765 441931 := bstep (se 1 (by rfl) ⟨331448, by rfl⟩ : syracuseStep 441931 = 662897) B662897
theorem B5619293 : Blo 389765 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B2965085 : Blo 389765 2965085 := bstep (se 3 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 2965085 = 1111907) B1111907
theorem B442039 : Blo 389765 442039 := bstep (se 1 (by rfl) ⟨331529, by rfl⟩ : syracuseStep 442039 = 663059) B663059
theorem B1261277 : Blo 389765 1261277 := bstep (se 3 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 1261277 = 472979) B472979
theorem B1195841 : Blo 389765 1195841 := bstep (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) B896881
theorem B1326941 : Blo 389765 1326941 := bstep (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) B497603
theorem B442219 : Blo 389765 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B442327 : Blo 389765 442327 := bstep (se 1 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 442327 = 663491) B663491
theorem B8044505 : Blo 389765 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B835571 : Blo 389765 835571 := bstep (se 1 (by rfl) ⟨626678, by rfl⟩ : syracuseStep 835571 = 1253357) B1253357
theorem B442507 : Blo 389765 442507 := bstep (se 1 (by rfl) ⟨331880, by rfl⟩ : syracuseStep 442507 = 663761) B663761
theorem B442615 : Blo 389765 442615 := bstep (se 1 (by rfl) ⟨331961, by rfl⟩ : syracuseStep 442615 = 663923) B663923
theorem B1786157 : Blo 389765 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B442795 : Blo 389765 442795 := bstep (se 1 (by rfl) ⟨332096, by rfl⟩ : syracuseStep 442795 = 664193) B664193
theorem B1491473 : Blo 389765 1491473 := bstep (se 2 (by rfl) ⟨559302, by rfl⟩ : syracuseStep 1491473 = 1118605) B1118605
theorem B442903 : Blo 389765 442903 := bstep (se 1 (by rfl) ⟨332177, by rfl⟩ : syracuseStep 442903 = 664355) B664355
theorem B1983041 : Blo 389765 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B1131329 : Blo 389765 1131329 := bstep (se 2 (by rfl) ⟨424248, by rfl⟩ : syracuseStep 1131329 = 848497) B848497
theorem B1328075 : Blo 389765 1328075 := bstep (se 1 (by rfl) ⟨996056, by rfl⟩ : syracuseStep 1328075 = 1992113) B1992113
theorem B1491929 : Blo 389765 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B705547 : Blo 389765 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B1492141 : Blo 389765 1492141 := bstep (se 3 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 1492141 = 559553) B559553
theorem B1328345 : Blo 389765 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B1885457 : Blo 389765 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B836887 : Blo 389765 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B1885571 : Blo 389765 1885571 := bstep (se 1 (by rfl) ⟨1414178, by rfl⟩ : syracuseStep 1885571 = 2828357) B2828357
theorem B837067 : Blo 389765 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B706009 : Blo 389765 706009 := bstep (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) B529507
theorem B1492445 : Blo 389765 1492445 := bstep (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) B559667
theorem B837143 : Blo 389765 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B2508353 : Blo 389765 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B2148113 : Blo 389765 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B902977 : Blo 389765 902977 := bstep (se 2 (by rfl) ⟨338616, by rfl⟩ : syracuseStep 902977 = 677233) B677233
theorem B3163997 : Blo 389765 3163997 := bstep (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) B1186499
theorem B2836403 : Blo 389765 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B6670349 : Blo 389765 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B1722391 : Blo 389765 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B2115991 : Blo 389765 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B1984985 : Blo 389765 1984985 := bstep (se 2 (by rfl) ⟨744369, by rfl⟩ : syracuseStep 1984985 = 1488739) B1488739
theorem B1591859 : Blo 389765 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B772915 : Blo 389765 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B740171 : Blo 389765 740171 := bstep (se 1 (by rfl) ⟨555128, by rfl⟩ : syracuseStep 740171 = 1110257) B1110257
theorem B1788875 : Blo 389765 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B740353 : Blo 389765 740353 := bstep (se 2 (by rfl) ⟨277632, by rfl⟩ : syracuseStep 740353 = 555265) B555265
theorem B707609 : Blo 389765 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B838937 : Blo 389765 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B10833301 : Blo 389765 10833301 := bstep (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) B507811
theorem B740801 : Blo 389765 740801 := bstep (se 2 (by rfl) ⟨277800, by rfl⟩ : syracuseStep 740801 = 555601) B555601
theorem B3558917 : Blo 389765 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B3362309 : Blo 389765 3362309 := bstep (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) B630433
theorem B741143 : Blo 389765 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B839603 : Blo 389765 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B1495043 : Blo 389765 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B1495057 : Blo 389765 1495057 := bstep (se 2 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 1495057 = 1121293) B1121293
theorem B1986605 : Blo 389765 1986605 := bstep (se 3 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 1986605 = 744977) B744977
theorem B938135 : Blo 389765 938135 := bstep (se 1 (by rfl) ⟨703601, by rfl⟩ : syracuseStep 938135 = 1407203) B1407203
theorem B5165207 : Blo 389765 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B2511121 : Blo 389765 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B741811 : Blo 389765 741811 := bstep (se 1 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 741811 = 1112717) B1112717
theorem B1364441 : Blo 389765 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B2380589 : Blo 389765 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B742259 : Blo 389765 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B742297 : Blo 389765 742297 := bstep (se 2 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 742297 = 556723) B556723
theorem B742745 : Blo 389765 742745 := bstep (se 2 (by rfl) ⟨278529, by rfl⟩ : syracuseStep 742745 = 557059) B557059
theorem B808385 : Blo 389765 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B1267265 : Blo 389765 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B1594973 : Blo 389765 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B448459 : Blo 389765 448459 := bstep (se 1 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 448459 = 672689) B672689
theorem B743489 : Blo 389765 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B4741325 : Blo 389765 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B743755 : Blo 389765 743755 := bstep (se 1 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 743755 = 1115633) B1115633
theorem B1399319 : Blo 389765 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B744203 : Blo 389765 744203 := bstep (se 1 (by rfl) ⟨558152, by rfl⟩ : syracuseStep 744203 = 1116305) B1116305
theorem B1891147 : Blo 389765 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B2120579 : Blo 389765 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B744385 : Blo 389765 744385 := bstep (se 2 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 744385 = 558289) B558289
theorem B2120921 : Blo 389765 2120921 := bstep (se 2 (by rfl) ⟨795345, by rfl⟩ : syracuseStep 2120921 = 1590691) B1590691
theorem B744727 : Blo 389765 744727 := bstep (se 1 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 744727 = 1117091) B1117091
theorem B941401 : Blo 389765 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B4480433 : Blo 389765 4480433 := bstep (se 2 (by rfl) ⟨1680162, by rfl⟩ : syracuseStep 4480433 = 3360325) B3360325
theorem B7167449 : Blo 389765 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B744947 : Blo 389765 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B745175 : Blo 389765 745175 := bstep (se 1 (by rfl) ⟨558881, by rfl⟩ : syracuseStep 745175 = 1117763) B1117763
theorem B5660401 : Blo 389765 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B1990493 : Blo 389765 1990493 := bstep (se 3 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 1990493 = 746435) B746435
theorem B3563443 : Blo 389765 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B745433 : Blo 389765 745433 := bstep (se 2 (by rfl) ⟨279537, by rfl⟩ : syracuseStep 745433 = 559075) B559075
theorem B1335361 : Blo 389765 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B1401025 : Blo 389765 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B942401 : Blo 389765 942401 := bstep (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) B706801
theorem B745843 : Blo 389765 745843 := bstep (se 1 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 745843 = 1118765) B1118765
theorem B877067 : Blo 389765 877067 := bstep (se 1 (by rfl) ⟨657800, by rfl⟩ : syracuseStep 877067 = 1315601) B1315601
theorem B877121 : Blo 389765 877121 := bstep (se 2 (by rfl) ⟨328920, by rfl⟩ : syracuseStep 877121 = 657841) B657841
theorem B2220695 : Blo 389765 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B877337 : Blo 389765 877337 := bstep (se 2 (by rfl) ⟨329001, by rfl⟩ : syracuseStep 877337 = 658003) B658003
theorem B746329 : Blo 389765 746329 := bstep (se 2 (by rfl) ⟨279873, by rfl⟩ : syracuseStep 746329 = 559747) B559747
theorem B877427 : Blo 389765 877427 := bstep (se 1 (by rfl) ⟨658070, by rfl⟩ : syracuseStep 877427 = 1316141) B1316141
theorem B877463 : Blo 389765 877463 := bstep (se 1 (by rfl) ⟨658097, by rfl⟩ : syracuseStep 877463 = 1316195) B1316195
theorem B418807 : Blo 389765 418807 := bstep (se 1 (by rfl) ⟨314105, by rfl⟩ : syracuseStep 418807 = 628211) B628211
theorem B877643 : Blo 389765 877643 := bstep (se 1 (by rfl) ⟨658232, by rfl⟩ : syracuseStep 877643 = 1316465) B1316465
theorem B877697 : Blo 389765 877697 := bstep (se 2 (by rfl) ⟨329136, by rfl⟩ : syracuseStep 877697 = 658273) B658273
theorem B7595309 : Blo 389765 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B877913 : Blo 389765 877913 := bstep (se 2 (by rfl) ⟨329217, by rfl⟩ : syracuseStep 877913 = 658435) B658435
theorem B746891 : Blo 389765 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B2811287 : Blo 389765 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B878003 : Blo 389765 878003 := bstep (se 1 (by rfl) ⟨658502, by rfl⟩ : syracuseStep 878003 = 1317005) B1317005
theorem B878039 : Blo 389765 878039 := bstep (se 1 (by rfl) ⟨658529, by rfl⟩ : syracuseStep 878039 = 1317059) B1317059
theorem B747073 : Blo 389765 747073 := bstep (se 2 (by rfl) ⟨280152, by rfl⟩ : syracuseStep 747073 = 560305) B560305
theorem B878219 : Blo 389765 878219 := bstep (se 1 (by rfl) ⟨658664, by rfl⟩ : syracuseStep 878219 = 1317329) B1317329
theorem B878273 : Blo 389765 878273 := bstep (se 2 (by rfl) ⟨329352, by rfl⟩ : syracuseStep 878273 = 658705) B658705
theorem B419627 : Blo 389765 419627 := bstep (se 1 (by rfl) ⟨314720, by rfl⟩ : syracuseStep 419627 = 629441) B629441
theorem B1992599 : Blo 389765 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B878489 : Blo 389765 878489 := bstep (se 2 (by rfl) ⟨329433, by rfl⟩ : syracuseStep 878489 = 658867) B658867
theorem B2779085 : Blo 389765 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B878579 : Blo 389765 878579 := bstep (se 1 (by rfl) ⟨658934, by rfl⟩ : syracuseStep 878579 = 1317869) B1317869
theorem B878615 : Blo 389765 878615 := bstep (se 1 (by rfl) ⟨658961, by rfl⟩ : syracuseStep 878615 = 1317923) B1317923
theorem B7596101 : Blo 389765 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1665197 : Blo 389765 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B878795 : Blo 389765 878795 := bstep (se 1 (by rfl) ⟨659096, by rfl⟩ : syracuseStep 878795 = 1318193) B1318193
theorem B878849 : Blo 389765 878849 := bstep (se 2 (by rfl) ⟨329568, by rfl⟩ : syracuseStep 878849 = 659137) B659137
theorem B5335301 : Blo 389765 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B4253957 : Blo 389765 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B3762611 : Blo 389765 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B3434957 : Blo 389765 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B879065 : Blo 389765 879065 := bstep (se 2 (by rfl) ⟨329649, by rfl⟩ : syracuseStep 879065 = 659299) B659299
theorem B879155 : Blo 389765 879155 := bstep (se 1 (by rfl) ⟨659366, by rfl⟩ : syracuseStep 879155 = 1318733) B1318733
theorem B2255435 : Blo 389765 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B879191 : Blo 389765 879191 := bstep (se 1 (by rfl) ⟨659393, by rfl⟩ : syracuseStep 879191 = 1318787) B1318787
theorem B879371 : Blo 389765 879371 := bstep (se 1 (by rfl) ⟨659528, by rfl⟩ : syracuseStep 879371 = 1319057) B1319057
theorem B879425 : Blo 389765 879425 := bstep (se 2 (by rfl) ⟨329784, by rfl⟩ : syracuseStep 879425 = 659569) B659569
theorem B584651 : Blo 389765 584651 := bstep (se 1 (by rfl) ⟨438488, by rfl⟩ : syracuseStep 584651 = 876977) B876977
theorem B2812877 : Blo 389765 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B584663 : Blo 389765 584663 := bstep (se 1 (by rfl) ⟨438497, by rfl⟩ : syracuseStep 584663 = 876995) B876995
theorem B584729 : Blo 389765 584729 := bstep (se 2 (by rfl) ⟨219273, by rfl⟩ : syracuseStep 584729 = 438547) B438547
theorem B879641 : Blo 389765 879641 := bstep (se 2 (by rfl) ⟨329865, by rfl⟩ : syracuseStep 879641 = 659731) B659731
theorem B879731 : Blo 389765 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B584843 : Blo 389765 584843 := bstep (se 1 (by rfl) ⟨438632, by rfl⟩ : syracuseStep 584843 = 877265) B877265
theorem B584855 : Blo 389765 584855 := bstep (se 1 (by rfl) ⟨438641, by rfl⟩ : syracuseStep 584855 = 877283) B877283
theorem B879767 : Blo 389765 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B584921 : Blo 389765 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B585035 : Blo 389765 585035 := bstep (se 1 (by rfl) ⟨438776, by rfl⟩ : syracuseStep 585035 = 877553) B877553
theorem B879947 : Blo 389765 879947 := bstep (se 1 (by rfl) ⟨659960, by rfl⟩ : syracuseStep 879947 = 1319921) B1319921
theorem B585047 : Blo 389765 585047 := bstep (se 1 (by rfl) ⟨438785, by rfl⟩ : syracuseStep 585047 = 877571) B877571
theorem B880001 : Blo 389765 880001 := bstep (se 2 (by rfl) ⟨330000, by rfl⟩ : syracuseStep 880001 = 660001) B660001
theorem B585113 : Blo 389765 585113 := bstep (se 2 (by rfl) ⟨219417, by rfl⟩ : syracuseStep 585113 = 438835) B438835
theorem B2813363 : Blo 389765 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B585227 : Blo 389765 585227 := bstep (se 1 (by rfl) ⟨438920, by rfl⟩ : syracuseStep 585227 = 877841) B877841
theorem B585239 : Blo 389765 585239 := bstep (se 1 (by rfl) ⟨438929, by rfl⟩ : syracuseStep 585239 = 877859) B877859
theorem B585305 : Blo 389765 585305 := bstep (se 2 (by rfl) ⟨219489, by rfl⟩ : syracuseStep 585305 = 438979) B438979
theorem B880217 : Blo 389765 880217 := bstep (se 2 (by rfl) ⟨330081, by rfl⟩ : syracuseStep 880217 = 660163) B660163
theorem B880307 : Blo 389765 880307 := bstep (se 1 (by rfl) ⟨660230, by rfl⟩ : syracuseStep 880307 = 1320461) B1320461
theorem B585419 : Blo 389765 585419 := bstep (se 1 (by rfl) ⟨439064, by rfl⟩ : syracuseStep 585419 = 878129) B878129
theorem B585431 : Blo 389765 585431 := bstep (se 1 (by rfl) ⟨439073, by rfl⟩ : syracuseStep 585431 = 878147) B878147
theorem B880343 : Blo 389765 880343 := bstep (se 1 (by rfl) ⟨660257, by rfl⟩ : syracuseStep 880343 = 1320515) B1320515
theorem B6811397 : Blo 389765 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B5041925 : Blo 389765 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B585497 : Blo 389765 585497 := bstep (se 2 (by rfl) ⟨219561, by rfl⟩ : syracuseStep 585497 = 439123) B439123
theorem B3764069 : Blo 389765 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B585611 : Blo 389765 585611 := bstep (se 1 (by rfl) ⟨439208, by rfl⟩ : syracuseStep 585611 = 878417) B878417
theorem B880523 : Blo 389765 880523 := bstep (se 1 (by rfl) ⟨660392, by rfl⟩ : syracuseStep 880523 = 1320785) B1320785
theorem B585623 : Blo 389765 585623 := bstep (se 1 (by rfl) ⟨439217, by rfl⟩ : syracuseStep 585623 = 878435) B878435
theorem B880577 : Blo 389765 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B585689 : Blo 389765 585689 := bstep (se 2 (by rfl) ⟨219633, by rfl⟩ : syracuseStep 585689 = 439267) B439267
theorem B585803 : Blo 389765 585803 := bstep (se 1 (by rfl) ⟨439352, by rfl⟩ : syracuseStep 585803 = 878705) B878705
theorem B585815 : Blo 389765 585815 := bstep (se 1 (by rfl) ⟨439361, by rfl⟩ : syracuseStep 585815 = 878723) B878723
theorem B585881 : Blo 389765 585881 := bstep (se 2 (by rfl) ⟨219705, by rfl⟩ : syracuseStep 585881 = 439411) B439411
theorem B880793 : Blo 389765 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B880883 : Blo 389765 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B585995 : Blo 389765 585995 := bstep (se 1 (by rfl) ⟨439496, by rfl⟩ : syracuseStep 585995 = 878993) B878993
theorem B586007 : Blo 389765 586007 := bstep (se 1 (by rfl) ⟨439505, by rfl⟩ : syracuseStep 586007 = 879011) B879011
theorem B880919 : Blo 389765 880919 := bstep (se 1 (by rfl) ⟨660689, by rfl⟩ : syracuseStep 880919 = 1321379) B1321379
theorem B586073 : Blo 389765 586073 := bstep (se 2 (by rfl) ⟨219777, by rfl⟩ : syracuseStep 586073 = 439555) B439555
theorem B586187 : Blo 389765 586187 := bstep (se 1 (by rfl) ⟨439640, by rfl⟩ : syracuseStep 586187 = 879281) B879281
theorem B881099 : Blo 389765 881099 := bstep (se 1 (by rfl) ⟨660824, by rfl⟩ : syracuseStep 881099 = 1321649) B1321649
theorem B586199 : Blo 389765 586199 := bstep (se 1 (by rfl) ⟨439649, by rfl⟩ : syracuseStep 586199 = 879299) B879299
theorem B881153 : Blo 389765 881153 := bstep (se 2 (by rfl) ⟨330432, by rfl⟩ : syracuseStep 881153 = 660865) B660865
theorem B586265 : Blo 389765 586265 := bstep (se 2 (by rfl) ⟨219849, by rfl⟩ : syracuseStep 586265 = 439699) B439699
theorem B389771 : Blo 389765 389771 := bstep (se 1 (by rfl) ⟨292328, by rfl⟩ : syracuseStep 389771 = 584657) B584657
theorem B586379 : Blo 389765 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B389783 : Blo 389765 389783 := bstep (se 1 (by rfl) ⟨292337, by rfl⟩ : syracuseStep 389783 = 584675) B584675
theorem B586391 : Blo 389765 586391 := bstep (se 1 (by rfl) ⟨439793, by rfl⟩ : syracuseStep 586391 = 879587) B879587
theorem B389803 : Blo 389765 389803 := bstep (se 1 (by rfl) ⟨292352, by rfl⟩ : syracuseStep 389803 = 584705) B584705
theorem B389815 : Blo 389765 389815 := bstep (se 1 (by rfl) ⟨292361, by rfl⟩ : syracuseStep 389815 = 584723) B584723
theorem B389835 : Blo 389765 389835 := bstep (se 1 (by rfl) ⟨292376, by rfl⟩ : syracuseStep 389835 = 584753) B584753
theorem B389847 : Blo 389765 389847 := bstep (se 1 (by rfl) ⟨292385, by rfl⟩ : syracuseStep 389847 = 584771) B584771
theorem B586457 : Blo 389765 586457 := bstep (se 2 (by rfl) ⟨219921, by rfl⟩ : syracuseStep 586457 = 439843) B439843
theorem B881369 : Blo 389765 881369 := bstep (se 2 (by rfl) ⟨330513, by rfl⟩ : syracuseStep 881369 = 661027) B661027
theorem B389867 : Blo 389765 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B389879 : Blo 389765 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B1504003 : Blo 389765 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B389899 : Blo 389765 389899 := bstep (se 1 (by rfl) ⟨292424, by rfl⟩ : syracuseStep 389899 = 584849) B584849
theorem B389911 : Blo 389765 389911 := bstep (se 1 (by rfl) ⟨292433, by rfl⟩ : syracuseStep 389911 = 584867) B584867
theorem B389931 : Blo 389765 389931 := bstep (se 1 (by rfl) ⟨292448, by rfl⟩ : syracuseStep 389931 = 584897) B584897
theorem B881459 : Blo 389765 881459 := bstep (se 1 (by rfl) ⟨661094, by rfl⟩ : syracuseStep 881459 = 1322189) B1322189
theorem B389943 : Blo 389765 389943 := bstep (se 1 (by rfl) ⟨292457, by rfl⟩ : syracuseStep 389943 = 584915) B584915
theorem B389963 : Blo 389765 389963 := bstep (se 1 (by rfl) ⟨292472, by rfl⟩ : syracuseStep 389963 = 584945) B584945
theorem B586571 : Blo 389765 586571 := bstep (se 1 (by rfl) ⟨439928, by rfl⟩ : syracuseStep 586571 = 879857) B879857
theorem B389975 : Blo 389765 389975 := bstep (se 1 (by rfl) ⟨292481, by rfl⟩ : syracuseStep 389975 = 584963) B584963
theorem B586583 : Blo 389765 586583 := bstep (se 1 (by rfl) ⟨439937, by rfl⟩ : syracuseStep 586583 = 879875) B879875
theorem B881495 : Blo 389765 881495 := bstep (se 1 (by rfl) ⟨661121, by rfl⟩ : syracuseStep 881495 = 1322243) B1322243
theorem B5370725 : Blo 389765 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B389995 : Blo 389765 389995 := bstep (se 1 (by rfl) ⟨292496, by rfl⟩ : syracuseStep 389995 = 584993) B584993
theorem B390007 : Blo 389765 390007 := bstep (se 1 (by rfl) ⟨292505, by rfl⟩ : syracuseStep 390007 = 585011) B585011
theorem B390027 : Blo 389765 390027 := bstep (se 1 (by rfl) ⟨292520, by rfl⟩ : syracuseStep 390027 = 585041) B585041
theorem B390039 : Blo 389765 390039 := bstep (se 1 (by rfl) ⟨292529, by rfl⟩ : syracuseStep 390039 = 585059) B585059
theorem B586649 : Blo 389765 586649 := bstep (se 2 (by rfl) ⟨219993, by rfl⟩ : syracuseStep 586649 = 439987) B439987
theorem B390059 : Blo 389765 390059 := bstep (se 1 (by rfl) ⟨292544, by rfl⟩ : syracuseStep 390059 = 585089) B585089
theorem B390071 : Blo 389765 390071 := bstep (se 1 (by rfl) ⟨292553, by rfl⟩ : syracuseStep 390071 = 585107) B585107
theorem B390091 : Blo 389765 390091 := bstep (se 1 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 390091 = 585137) B585137
theorem B390103 : Blo 389765 390103 := bstep (se 1 (by rfl) ⟨292577, by rfl⟩ : syracuseStep 390103 = 585155) B585155
theorem B390123 : Blo 389765 390123 := bstep (se 1 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 390123 = 585185) B585185
theorem B390135 : Blo 389765 390135 := bstep (se 1 (by rfl) ⟨292601, by rfl⟩ : syracuseStep 390135 = 585203) B585203
theorem B390155 : Blo 389765 390155 := bstep (se 1 (by rfl) ⟨292616, by rfl⟩ : syracuseStep 390155 = 585233) B585233
theorem B586763 : Blo 389765 586763 := bstep (se 1 (by rfl) ⟨440072, by rfl⟩ : syracuseStep 586763 = 880145) B880145
theorem B881675 : Blo 389765 881675 := bstep (se 1 (by rfl) ⟨661256, by rfl⟩ : syracuseStep 881675 = 1322513) B1322513
theorem B390167 : Blo 389765 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B586775 : Blo 389765 586775 := bstep (se 1 (by rfl) ⟨440081, by rfl⟩ : syracuseStep 586775 = 880163) B880163
theorem B390187 : Blo 389765 390187 := bstep (se 1 (by rfl) ⟨292640, by rfl⟩ : syracuseStep 390187 = 585281) B585281
theorem B390199 : Blo 389765 390199 := bstep (se 1 (by rfl) ⟨292649, by rfl⟩ : syracuseStep 390199 = 585299) B585299
theorem B881729 : Blo 389765 881729 := bstep (se 2 (by rfl) ⟨330648, by rfl⟩ : syracuseStep 881729 = 661297) B661297
theorem B390219 : Blo 389765 390219 := bstep (se 1 (by rfl) ⟨292664, by rfl⟩ : syracuseStep 390219 = 585329) B585329
theorem B390231 : Blo 389765 390231 := bstep (se 1 (by rfl) ⟨292673, by rfl⟩ : syracuseStep 390231 = 585347) B585347
theorem B586841 : Blo 389765 586841 := bstep (se 2 (by rfl) ⟨220065, by rfl⟩ : syracuseStep 586841 = 440131) B440131
theorem B1111133 : Blo 389765 1111133 := bstep (se 3 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 1111133 = 416675) B416675
theorem B390251 : Blo 389765 390251 := bstep (se 1 (by rfl) ⟨292688, by rfl⟩ : syracuseStep 390251 = 585377) B585377
theorem B390263 : Blo 389765 390263 := bstep (se 1 (by rfl) ⟨292697, by rfl⟩ : syracuseStep 390263 = 585395) B585395
theorem B2946179 : Blo 389765 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B390283 : Blo 389765 390283 := bstep (se 1 (by rfl) ⟨292712, by rfl⟩ : syracuseStep 390283 = 585425) B585425
theorem B390295 : Blo 389765 390295 := bstep (se 1 (by rfl) ⟨292721, by rfl⟩ : syracuseStep 390295 = 585443) B585443
theorem B390315 : Blo 389765 390315 := bstep (se 1 (by rfl) ⟨292736, by rfl⟩ : syracuseStep 390315 = 585473) B585473
theorem B390327 : Blo 389765 390327 := bstep (se 1 (by rfl) ⟨292745, by rfl⟩ : syracuseStep 390327 = 585491) B585491
theorem B390347 : Blo 389765 390347 := bstep (se 1 (by rfl) ⟨292760, by rfl⟩ : syracuseStep 390347 = 585521) B585521
theorem B586955 : Blo 389765 586955 := bstep (se 1 (by rfl) ⟨440216, by rfl⟩ : syracuseStep 586955 = 880433) B880433
theorem B390359 : Blo 389765 390359 := bstep (se 1 (by rfl) ⟨292769, by rfl⟩ : syracuseStep 390359 = 585539) B585539
theorem B586967 : Blo 389765 586967 := bstep (se 1 (by rfl) ⟨440225, by rfl⟩ : syracuseStep 586967 = 880451) B880451
theorem B390379 : Blo 389765 390379 := bstep (se 1 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 390379 = 585569) B585569
theorem B390391 : Blo 389765 390391 := bstep (se 1 (by rfl) ⟨292793, by rfl⟩ : syracuseStep 390391 = 585587) B585587
theorem B390411 : Blo 389765 390411 := bstep (se 1 (by rfl) ⟨292808, by rfl⟩ : syracuseStep 390411 = 585617) B585617
theorem B390423 : Blo 389765 390423 := bstep (se 1 (by rfl) ⟨292817, by rfl⟩ : syracuseStep 390423 = 585635) B585635
theorem B587033 : Blo 389765 587033 := bstep (se 2 (by rfl) ⟨220137, by rfl⟩ : syracuseStep 587033 = 440275) B440275
theorem B881945 : Blo 389765 881945 := bstep (se 2 (by rfl) ⟨330729, by rfl⟩ : syracuseStep 881945 = 661459) B661459
theorem B390443 : Blo 389765 390443 := bstep (se 1 (by rfl) ⟨292832, by rfl⟩ : syracuseStep 390443 = 585665) B585665
theorem B390455 : Blo 389765 390455 := bstep (se 1 (by rfl) ⟨292841, by rfl⟩ : syracuseStep 390455 = 585683) B585683
theorem B390475 : Blo 389765 390475 := bstep (se 1 (by rfl) ⟨292856, by rfl⟩ : syracuseStep 390475 = 585713) B585713
theorem B390487 : Blo 389765 390487 := bstep (se 1 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 390487 = 585731) B585731
theorem B2225501 : Blo 389765 2225501 := bstep (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) B834563
theorem B390507 : Blo 389765 390507 := bstep (se 1 (by rfl) ⟨292880, by rfl⟩ : syracuseStep 390507 = 585761) B585761
theorem B882035 : Blo 389765 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B390519 : Blo 389765 390519 := bstep (se 1 (by rfl) ⟨292889, by rfl⟩ : syracuseStep 390519 = 585779) B585779
theorem B390539 : Blo 389765 390539 := bstep (se 1 (by rfl) ⟨292904, by rfl⟩ : syracuseStep 390539 = 585809) B585809
theorem B587147 : Blo 389765 587147 := bstep (se 1 (by rfl) ⟨440360, by rfl⟩ : syracuseStep 587147 = 880721) B880721
theorem B390551 : Blo 389765 390551 := bstep (se 1 (by rfl) ⟨292913, by rfl⟩ : syracuseStep 390551 = 585827) B585827
theorem B587159 : Blo 389765 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B882071 : Blo 389765 882071 := bstep (se 1 (by rfl) ⟨661553, by rfl⟩ : syracuseStep 882071 = 1323107) B1323107
theorem B390571 : Blo 389765 390571 := bstep (se 1 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 390571 = 585857) B585857
theorem B1111475 : Blo 389765 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B390583 : Blo 389765 390583 := bstep (se 1 (by rfl) ⟨292937, by rfl⟩ : syracuseStep 390583 = 585875) B585875
theorem B1668545 : Blo 389765 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B390603 : Blo 389765 390603 := bstep (se 1 (by rfl) ⟨292952, by rfl⟩ : syracuseStep 390603 = 585905) B585905
theorem B390615 : Blo 389765 390615 := bstep (se 1 (by rfl) ⟨292961, by rfl⟩ : syracuseStep 390615 = 585923) B585923
theorem B587225 : Blo 389765 587225 := bstep (se 2 (by rfl) ⟨220209, by rfl⟩ : syracuseStep 587225 = 440419) B440419
theorem B390635 : Blo 389765 390635 := bstep (se 1 (by rfl) ⟨292976, by rfl⟩ : syracuseStep 390635 = 585953) B585953
theorem B390647 : Blo 389765 390647 := bstep (se 1 (by rfl) ⟨292985, by rfl⟩ : syracuseStep 390647 = 585971) B585971
theorem B390667 : Blo 389765 390667 := bstep (se 1 (by rfl) ⟨293000, by rfl⟩ : syracuseStep 390667 = 586001) B586001
theorem B390679 : Blo 389765 390679 := bstep (se 1 (by rfl) ⟨293009, by rfl⟩ : syracuseStep 390679 = 586019) B586019
theorem B390699 : Blo 389765 390699 := bstep (se 1 (by rfl) ⟨293024, by rfl⟩ : syracuseStep 390699 = 586049) B586049
theorem B390711 : Blo 389765 390711 := bstep (se 1 (by rfl) ⟨293033, by rfl⟩ : syracuseStep 390711 = 586067) B586067
theorem B390731 : Blo 389765 390731 := bstep (se 1 (by rfl) ⟨293048, by rfl⟩ : syracuseStep 390731 = 586097) B586097
theorem B587339 : Blo 389765 587339 := bstep (se 1 (by rfl) ⟨440504, by rfl⟩ : syracuseStep 587339 = 881009) B881009
theorem B882251 : Blo 389765 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B390743 : Blo 389765 390743 := bstep (se 1 (by rfl) ⟨293057, by rfl⟩ : syracuseStep 390743 = 586115) B586115
theorem B587351 : Blo 389765 587351 := bstep (se 1 (by rfl) ⟨440513, by rfl⟩ : syracuseStep 587351 = 881027) B881027
theorem B390763 : Blo 389765 390763 := bstep (se 1 (by rfl) ⟨293072, by rfl⟩ : syracuseStep 390763 = 586145) B586145
theorem B390775 : Blo 389765 390775 := bstep (se 1 (by rfl) ⟨293081, by rfl⟩ : syracuseStep 390775 = 586163) B586163
theorem B882305 : Blo 389765 882305 := bstep (se 2 (by rfl) ⟨330864, by rfl⟩ : syracuseStep 882305 = 661729) B661729
theorem B390795 : Blo 389765 390795 := bstep (se 1 (by rfl) ⟨293096, by rfl⟩ : syracuseStep 390795 = 586193) B586193
theorem B390807 : Blo 389765 390807 := bstep (se 1 (by rfl) ⟨293105, by rfl⟩ : syracuseStep 390807 = 586211) B586211
theorem B587417 : Blo 389765 587417 := bstep (se 2 (by rfl) ⟨220281, by rfl⟩ : syracuseStep 587417 = 440563) B440563
theorem B390827 : Blo 389765 390827 := bstep (se 1 (by rfl) ⟨293120, by rfl⟩ : syracuseStep 390827 = 586241) B586241
theorem B390839 : Blo 389765 390839 := bstep (se 1 (by rfl) ⟨293129, by rfl⟩ : syracuseStep 390839 = 586259) B586259
theorem B390859 : Blo 389765 390859 := bstep (se 1 (by rfl) ⟨293144, by rfl⟩ : syracuseStep 390859 = 586289) B586289
theorem B390871 : Blo 389765 390871 := bstep (se 1 (by rfl) ⟨293153, by rfl⟩ : syracuseStep 390871 = 586307) B586307
theorem B390891 : Blo 389765 390891 := bstep (se 1 (by rfl) ⟨293168, by rfl⟩ : syracuseStep 390891 = 586337) B586337
theorem B390903 : Blo 389765 390903 := bstep (se 1 (by rfl) ⟨293177, by rfl⟩ : syracuseStep 390903 = 586355) B586355
theorem B390923 : Blo 389765 390923 := bstep (se 1 (by rfl) ⟨293192, by rfl⟩ : syracuseStep 390923 = 586385) B586385
theorem B587531 : Blo 389765 587531 := bstep (se 1 (by rfl) ⟨440648, by rfl⟩ : syracuseStep 587531 = 881297) B881297
theorem B1668887 : Blo 389765 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B390935 : Blo 389765 390935 := bstep (se 1 (by rfl) ⟨293201, by rfl⟩ : syracuseStep 390935 = 586403) B586403
theorem B587543 : Blo 389765 587543 := bstep (se 1 (by rfl) ⟨440657, by rfl⟩ : syracuseStep 587543 = 881315) B881315
theorem B390955 : Blo 389765 390955 := bstep (se 1 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 390955 = 586433) B586433
theorem B4454189 : Blo 389765 4454189 := bstep (se 3 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 4454189 = 1670321) B1670321
theorem B390967 : Blo 389765 390967 := bstep (se 1 (by rfl) ⟨293225, by rfl⟩ : syracuseStep 390967 = 586451) B586451
theorem B390987 : Blo 389765 390987 := bstep (se 1 (by rfl) ⟨293240, by rfl⟩ : syracuseStep 390987 = 586481) B586481
theorem B390999 : Blo 389765 390999 := bstep (se 1 (by rfl) ⟨293249, by rfl⟩ : syracuseStep 390999 = 586499) B586499
theorem B587609 : Blo 389765 587609 := bstep (se 2 (by rfl) ⟨220353, by rfl⟩ : syracuseStep 587609 = 440707) B440707
theorem B882521 : Blo 389765 882521 := bstep (se 2 (by rfl) ⟨330945, by rfl⟩ : syracuseStep 882521 = 661891) B661891
theorem B391019 : Blo 389765 391019 := bstep (se 1 (by rfl) ⟨293264, by rfl⟩ : syracuseStep 391019 = 586529) B586529
theorem B391031 : Blo 389765 391031 := bstep (se 1 (by rfl) ⟨293273, by rfl⟩ : syracuseStep 391031 = 586547) B586547
theorem B391051 : Blo 389765 391051 := bstep (se 1 (by rfl) ⟨293288, by rfl⟩ : syracuseStep 391051 = 586577) B586577
theorem B391063 : Blo 389765 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B391083 : Blo 389765 391083 := bstep (se 1 (by rfl) ⟨293312, by rfl⟩ : syracuseStep 391083 = 586625) B586625
theorem B882611 : Blo 389765 882611 := bstep (se 1 (by rfl) ⟨661958, by rfl⟩ : syracuseStep 882611 = 1323917) B1323917
theorem B391095 : Blo 389765 391095 := bstep (se 1 (by rfl) ⟨293321, by rfl⟩ : syracuseStep 391095 = 586643) B586643
theorem B391115 : Blo 389765 391115 := bstep (se 1 (by rfl) ⟨293336, by rfl⟩ : syracuseStep 391115 = 586673) B586673
theorem B587723 : Blo 389765 587723 := bstep (se 1 (by rfl) ⟨440792, by rfl⟩ : syracuseStep 587723 = 881585) B881585
theorem B391127 : Blo 389765 391127 := bstep (se 1 (by rfl) ⟨293345, by rfl⟩ : syracuseStep 391127 = 586691) B586691
theorem B587735 : Blo 389765 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B882647 : Blo 389765 882647 := bstep (se 1 (by rfl) ⟨661985, by rfl⟩ : syracuseStep 882647 = 1323971) B1323971
theorem B391147 : Blo 389765 391147 := bstep (se 1 (by rfl) ⟨293360, by rfl⟩ : syracuseStep 391147 = 586721) B586721
theorem B391159 : Blo 389765 391159 := bstep (se 1 (by rfl) ⟨293369, by rfl⟩ : syracuseStep 391159 = 586739) B586739
theorem B391179 : Blo 389765 391179 := bstep (se 1 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 391179 = 586769) B586769
theorem B391191 : Blo 389765 391191 := bstep (se 1 (by rfl) ⟨293393, by rfl⟩ : syracuseStep 391191 = 586787) B586787
theorem B587801 : Blo 389765 587801 := bstep (se 2 (by rfl) ⟨220425, by rfl⟩ : syracuseStep 587801 = 440851) B440851
theorem B391211 : Blo 389765 391211 := bstep (se 1 (by rfl) ⟨293408, by rfl⟩ : syracuseStep 391211 = 586817) B586817
theorem B391223 : Blo 389765 391223 := bstep (se 1 (by rfl) ⟨293417, by rfl⟩ : syracuseStep 391223 = 586835) B586835
theorem B391243 : Blo 389765 391243 := bstep (se 1 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 391243 = 586865) B586865
theorem B391255 : Blo 389765 391255 := bstep (se 1 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 391255 = 586883) B586883
theorem B391275 : Blo 389765 391275 := bstep (se 1 (by rfl) ⟨293456, by rfl⟩ : syracuseStep 391275 = 586913) B586913
theorem B391287 : Blo 389765 391287 := bstep (se 1 (by rfl) ⟨293465, by rfl⟩ : syracuseStep 391287 = 586931) B586931
theorem B2685059 : Blo 389765 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B391307 : Blo 389765 391307 := bstep (se 1 (by rfl) ⟨293480, by rfl⟩ : syracuseStep 391307 = 586961) B586961
theorem B587915 : Blo 389765 587915 := bstep (se 1 (by rfl) ⟨440936, by rfl⟩ : syracuseStep 587915 = 881873) B881873
theorem B882827 : Blo 389765 882827 := bstep (se 1 (by rfl) ⟨662120, by rfl⟩ : syracuseStep 882827 = 1324241) B1324241
theorem B3340439 : Blo 389765 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B391319 : Blo 389765 391319 := bstep (se 1 (by rfl) ⟨293489, by rfl⟩ : syracuseStep 391319 = 586979) B586979
theorem B587927 : Blo 389765 587927 := bstep (se 1 (by rfl) ⟨440945, by rfl⟩ : syracuseStep 587927 = 881891) B881891
theorem B391339 : Blo 389765 391339 := bstep (se 1 (by rfl) ⟨293504, by rfl⟩ : syracuseStep 391339 = 587009) B587009
theorem B391351 : Blo 389765 391351 := bstep (se 1 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 391351 = 587027) B587027
theorem B882881 : Blo 389765 882881 := bstep (se 2 (by rfl) ⟨331080, by rfl⟩ : syracuseStep 882881 = 662161) B662161
theorem B391371 : Blo 389765 391371 := bstep (se 1 (by rfl) ⟨293528, by rfl⟩ : syracuseStep 391371 = 587057) B587057
theorem B391383 : Blo 389765 391383 := bstep (se 1 (by rfl) ⟨293537, by rfl⟩ : syracuseStep 391383 = 587075) B587075
theorem B587993 : Blo 389765 587993 := bstep (se 2 (by rfl) ⟨220497, by rfl⟩ : syracuseStep 587993 = 440995) B440995
theorem B391403 : Blo 389765 391403 := bstep (se 1 (by rfl) ⟨293552, by rfl⟩ : syracuseStep 391403 = 587105) B587105
theorem B391415 : Blo 389765 391415 := bstep (se 1 (by rfl) ⟨293561, by rfl⟩ : syracuseStep 391415 = 587123) B587123
theorem B391435 : Blo 389765 391435 := bstep (se 1 (by rfl) ⟨293576, by rfl⟩ : syracuseStep 391435 = 587153) B587153
theorem B391447 : Blo 389765 391447 := bstep (se 1 (by rfl) ⟨293585, by rfl⟩ : syracuseStep 391447 = 587171) B587171
theorem B391467 : Blo 389765 391467 := bstep (se 1 (by rfl) ⟨293600, by rfl⟩ : syracuseStep 391467 = 587201) B587201
theorem B391479 : Blo 389765 391479 := bstep (se 1 (by rfl) ⟨293609, by rfl⟩ : syracuseStep 391479 = 587219) B587219
theorem B391499 : Blo 389765 391499 := bstep (se 1 (by rfl) ⟨293624, by rfl⟩ : syracuseStep 391499 = 587249) B587249
theorem B588107 : Blo 389765 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B391511 : Blo 389765 391511 := bstep (se 1 (by rfl) ⟨293633, by rfl⟩ : syracuseStep 391511 = 587267) B587267
theorem B588119 : Blo 389765 588119 := bstep (se 1 (by rfl) ⟨441089, by rfl⟩ : syracuseStep 588119 = 882179) B882179
theorem B850265 : Blo 389765 850265 := bstep (se 2 (by rfl) ⟨318849, by rfl⟩ : syracuseStep 850265 = 637699) B637699
theorem B391531 : Blo 389765 391531 := bstep (se 1 (by rfl) ⟨293648, by rfl⟩ : syracuseStep 391531 = 587297) B587297
theorem B391543 : Blo 389765 391543 := bstep (se 1 (by rfl) ⟨293657, by rfl⟩ : syracuseStep 391543 = 587315) B587315
theorem B2521475 : Blo 389765 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B391563 : Blo 389765 391563 := bstep (se 1 (by rfl) ⟨293672, by rfl⟩ : syracuseStep 391563 = 587345) B587345
theorem B391575 : Blo 389765 391575 := bstep (se 1 (by rfl) ⟨293681, by rfl⟩ : syracuseStep 391575 = 587363) B587363
theorem B588185 : Blo 389765 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B883097 : Blo 389765 883097 := bstep (se 2 (by rfl) ⟨331161, by rfl⟩ : syracuseStep 883097 = 662323) B662323
theorem B391595 : Blo 389765 391595 := bstep (se 1 (by rfl) ⟨293696, by rfl⟩ : syracuseStep 391595 = 587393) B587393
theorem B391607 : Blo 389765 391607 := bstep (se 1 (by rfl) ⟨293705, by rfl⟩ : syracuseStep 391607 = 587411) B587411
theorem B391627 : Blo 389765 391627 := bstep (se 1 (by rfl) ⟨293720, by rfl⟩ : syracuseStep 391627 = 587441) B587441
theorem B391639 : Blo 389765 391639 := bstep (se 1 (by rfl) ⟨293729, by rfl⟩ : syracuseStep 391639 = 587459) B587459
theorem B391659 : Blo 389765 391659 := bstep (se 1 (by rfl) ⟨293744, by rfl⟩ : syracuseStep 391659 = 587489) B587489
theorem B883187 : Blo 389765 883187 := bstep (se 1 (by rfl) ⟨662390, by rfl⟩ : syracuseStep 883187 = 1324781) B1324781
theorem B391671 : Blo 389765 391671 := bstep (se 1 (by rfl) ⟨293753, by rfl⟩ : syracuseStep 391671 = 587507) B587507
theorem B391691 : Blo 389765 391691 := bstep (se 1 (by rfl) ⟨293768, by rfl⟩ : syracuseStep 391691 = 587537) B587537
theorem B588299 : Blo 389765 588299 := bstep (se 1 (by rfl) ⟨441224, by rfl⟩ : syracuseStep 588299 = 882449) B882449
theorem B391703 : Blo 389765 391703 := bstep (se 1 (by rfl) ⟨293777, by rfl⟩ : syracuseStep 391703 = 587555) B587555
theorem B588311 : Blo 389765 588311 := bstep (se 1 (by rfl) ⟨441233, by rfl⟩ : syracuseStep 588311 = 882467) B882467
theorem B883223 : Blo 389765 883223 := bstep (se 1 (by rfl) ⟨662417, by rfl⟩ : syracuseStep 883223 = 1324835) B1324835
theorem B391723 : Blo 389765 391723 := bstep (se 1 (by rfl) ⟨293792, by rfl⟩ : syracuseStep 391723 = 587585) B587585
theorem B1505837 : Blo 389765 1505837 := bstep (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) B564689
theorem B391735 : Blo 389765 391735 := bstep (se 1 (by rfl) ⟨293801, by rfl⟩ : syracuseStep 391735 = 587603) B587603
theorem B391755 : Blo 389765 391755 := bstep (se 1 (by rfl) ⟨293816, by rfl⟩ : syracuseStep 391755 = 587633) B587633
theorem B391767 : Blo 389765 391767 := bstep (se 1 (by rfl) ⟨293825, by rfl⟩ : syracuseStep 391767 = 587651) B587651
theorem B588377 : Blo 389765 588377 := bstep (se 2 (by rfl) ⟨220641, by rfl⟩ : syracuseStep 588377 = 441283) B441283
theorem B391787 : Blo 389765 391787 := bstep (se 1 (by rfl) ⟨293840, by rfl⟩ : syracuseStep 391787 = 587681) B587681
theorem B391799 : Blo 389765 391799 := bstep (se 1 (by rfl) ⟨293849, by rfl⟩ : syracuseStep 391799 = 587699) B587699
theorem B391819 : Blo 389765 391819 := bstep (se 1 (by rfl) ⟨293864, by rfl⟩ : syracuseStep 391819 = 587729) B587729
theorem B391831 : Blo 389765 391831 := bstep (se 1 (by rfl) ⟨293873, by rfl⟩ : syracuseStep 391831 = 587747) B587747
theorem B391851 : Blo 389765 391851 := bstep (se 1 (by rfl) ⟨293888, by rfl⟩ : syracuseStep 391851 = 587777) B587777
theorem B391863 : Blo 389765 391863 := bstep (se 1 (by rfl) ⟨293897, by rfl⟩ : syracuseStep 391863 = 587795) B587795
theorem B391883 : Blo 389765 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B588491 : Blo 389765 588491 := bstep (se 1 (by rfl) ⟨441368, by rfl⟩ : syracuseStep 588491 = 882737) B882737
theorem B883403 : Blo 389765 883403 := bstep (se 1 (by rfl) ⟨662552, by rfl⟩ : syracuseStep 883403 = 1325105) B1325105
theorem B391895 : Blo 389765 391895 := bstep (se 1 (by rfl) ⟨293921, by rfl⟩ : syracuseStep 391895 = 587843) B587843
theorem B588503 : Blo 389765 588503 := bstep (se 1 (by rfl) ⟨441377, by rfl⟩ : syracuseStep 588503 = 882755) B882755
theorem B391915 : Blo 389765 391915 := bstep (se 1 (by rfl) ⟨293936, by rfl⟩ : syracuseStep 391915 = 587873) B587873
theorem B7568113 : Blo 389765 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B391927 : Blo 389765 391927 := bstep (se 1 (by rfl) ⟨293945, by rfl⟩ : syracuseStep 391927 = 587891) B587891
theorem B883457 : Blo 389765 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B391947 : Blo 389765 391947 := bstep (se 1 (by rfl) ⟨293960, by rfl⟩ : syracuseStep 391947 = 587921) B587921
theorem B391959 : Blo 389765 391959 := bstep (se 1 (by rfl) ⟨293969, by rfl⟩ : syracuseStep 391959 = 587939) B587939
theorem B588569 : Blo 389765 588569 := bstep (se 2 (by rfl) ⟨220713, by rfl⟩ : syracuseStep 588569 = 441427) B441427
theorem B391979 : Blo 389765 391979 := bstep (se 1 (by rfl) ⟨293984, by rfl⟩ : syracuseStep 391979 = 587969) B587969
theorem B391991 : Blo 389765 391991 := bstep (se 1 (by rfl) ⟨293993, by rfl⟩ : syracuseStep 391991 = 587987) B587987
theorem B8584001 : Blo 389765 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B392011 : Blo 389765 392011 := bstep (se 1 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 392011 = 588017) B588017
theorem B392023 : Blo 389765 392023 := bstep (se 1 (by rfl) ⟨294017, by rfl⟩ : syracuseStep 392023 = 588035) B588035
theorem B392043 : Blo 389765 392043 := bstep (se 1 (by rfl) ⟨294032, by rfl⟩ : syracuseStep 392043 = 588065) B588065
theorem B392055 : Blo 389765 392055 := bstep (se 1 (by rfl) ⟨294041, by rfl⟩ : syracuseStep 392055 = 588083) B588083
theorem B392075 : Blo 389765 392075 := bstep (se 1 (by rfl) ⟨294056, by rfl⟩ : syracuseStep 392075 = 588113) B588113
theorem B588683 : Blo 389765 588683 := bstep (se 1 (by rfl) ⟨441512, by rfl⟩ : syracuseStep 588683 = 883025) B883025
theorem B392087 : Blo 389765 392087 := bstep (se 1 (by rfl) ⟨294065, by rfl⟩ : syracuseStep 392087 = 588131) B588131
theorem B588695 : Blo 389765 588695 := bstep (se 1 (by rfl) ⟨441521, by rfl⟩ : syracuseStep 588695 = 883043) B883043
theorem B392107 : Blo 389765 392107 := bstep (se 1 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 392107 = 588161) B588161
theorem B392119 : Blo 389765 392119 := bstep (se 1 (by rfl) ⟨294089, by rfl⟩ : syracuseStep 392119 = 588179) B588179
theorem B392139 : Blo 389765 392139 := bstep (se 1 (by rfl) ⟨294104, by rfl⟩ : syracuseStep 392139 = 588209) B588209
theorem B392151 : Blo 389765 392151 := bstep (se 1 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 392151 = 588227) B588227
theorem B588761 : Blo 389765 588761 := bstep (se 2 (by rfl) ⟨220785, by rfl⟩ : syracuseStep 588761 = 441571) B441571
theorem B883673 : Blo 389765 883673 := bstep (se 2 (by rfl) ⟨331377, by rfl⟩ : syracuseStep 883673 = 662755) B662755
theorem B392171 : Blo 389765 392171 := bstep (se 1 (by rfl) ⟨294128, by rfl⟩ : syracuseStep 392171 = 588257) B588257
theorem B392183 : Blo 389765 392183 := bstep (se 1 (by rfl) ⟨294137, by rfl⟩ : syracuseStep 392183 = 588275) B588275
theorem B392203 : Blo 389765 392203 := bstep (se 1 (by rfl) ⟨294152, by rfl⟩ : syracuseStep 392203 = 588305) B588305
theorem B392215 : Blo 389765 392215 := bstep (se 1 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 392215 = 588323) B588323
theorem B392235 : Blo 389765 392235 := bstep (se 1 (by rfl) ⟨294176, by rfl⟩ : syracuseStep 392235 = 588353) B588353
theorem B883763 : Blo 389765 883763 := bstep (se 1 (by rfl) ⟨662822, by rfl⟩ : syracuseStep 883763 = 1325645) B1325645
theorem B392247 : Blo 389765 392247 := bstep (se 1 (by rfl) ⟨294185, by rfl⟩ : syracuseStep 392247 = 588371) B588371
theorem B1866817 : Blo 389765 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B1276993 : Blo 389765 1276993 := bstep (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) B957745
theorem B392267 : Blo 389765 392267 := bstep (se 1 (by rfl) ⟨294200, by rfl⟩ : syracuseStep 392267 = 588401) B588401
theorem B588875 : Blo 389765 588875 := bstep (se 1 (by rfl) ⟨441656, by rfl⟩ : syracuseStep 588875 = 883313) B883313
theorem B392279 : Blo 389765 392279 := bstep (se 1 (by rfl) ⟨294209, by rfl⟩ : syracuseStep 392279 = 588419) B588419
theorem B588887 : Blo 389765 588887 := bstep (se 1 (by rfl) ⟨441665, by rfl⟩ : syracuseStep 588887 = 883331) B883331
theorem B883799 : Blo 389765 883799 := bstep (se 1 (by rfl) ⟨662849, by rfl⟩ : syracuseStep 883799 = 1325699) B1325699
theorem B392299 : Blo 389765 392299 := bstep (se 1 (by rfl) ⟨294224, by rfl⟩ : syracuseStep 392299 = 588449) B588449
theorem B392311 : Blo 389765 392311 := bstep (se 1 (by rfl) ⟨294233, by rfl⟩ : syracuseStep 392311 = 588467) B588467
theorem B392331 : Blo 389765 392331 := bstep (se 1 (by rfl) ⟨294248, by rfl⟩ : syracuseStep 392331 = 588497) B588497
theorem B392343 : Blo 389765 392343 := bstep (se 1 (by rfl) ⟨294257, by rfl⟩ : syracuseStep 392343 = 588515) B588515
theorem B588953 : Blo 389765 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B392363 : Blo 389765 392363 := bstep (se 1 (by rfl) ⟨294272, by rfl⟩ : syracuseStep 392363 = 588545) B588545
theorem B392375 : Blo 389765 392375 := bstep (se 1 (by rfl) ⟨294281, by rfl⟩ : syracuseStep 392375 = 588563) B588563
theorem B392395 : Blo 389765 392395 := bstep (se 1 (by rfl) ⟨294296, by rfl⟩ : syracuseStep 392395 = 588593) B588593
theorem B392407 : Blo 389765 392407 := bstep (se 1 (by rfl) ⟨294305, by rfl⟩ : syracuseStep 392407 = 588611) B588611
theorem B392427 : Blo 389765 392427 := bstep (se 1 (by rfl) ⟨294320, by rfl⟩ : syracuseStep 392427 = 588641) B588641
theorem B392439 : Blo 389765 392439 := bstep (se 1 (by rfl) ⟨294329, by rfl⟩ : syracuseStep 392439 = 588659) B588659
theorem B392459 : Blo 389765 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B589067 : Blo 389765 589067 := bstep (se 1 (by rfl) ⟨441800, by rfl⟩ : syracuseStep 589067 = 883601) B883601
theorem B883979 : Blo 389765 883979 := bstep (se 1 (by rfl) ⟨662984, by rfl⟩ : syracuseStep 883979 = 1325969) B1325969
theorem B392471 : Blo 389765 392471 := bstep (se 1 (by rfl) ⟨294353, by rfl⟩ : syracuseStep 392471 = 588707) B588707
theorem B589079 : Blo 389765 589079 := bstep (se 1 (by rfl) ⟨441809, by rfl⟩ : syracuseStep 589079 = 883619) B883619
theorem B392491 : Blo 389765 392491 := bstep (se 1 (by rfl) ⟨294368, by rfl⟩ : syracuseStep 392491 = 588737) B588737
theorem B392503 : Blo 389765 392503 := bstep (se 1 (by rfl) ⟨294377, by rfl⟩ : syracuseStep 392503 = 588755) B588755
theorem B884033 : Blo 389765 884033 := bstep (se 2 (by rfl) ⟨331512, by rfl⟩ : syracuseStep 884033 = 663025) B663025
theorem B392523 : Blo 389765 392523 := bstep (se 1 (by rfl) ⟨294392, by rfl⟩ : syracuseStep 392523 = 588785) B588785
theorem B392535 : Blo 389765 392535 := bstep (se 1 (by rfl) ⟨294401, by rfl⟩ : syracuseStep 392535 = 588803) B588803
theorem B589145 : Blo 389765 589145 := bstep (se 2 (by rfl) ⟨220929, by rfl⟩ : syracuseStep 589145 = 441859) B441859
theorem B392555 : Blo 389765 392555 := bstep (se 1 (by rfl) ⟨294416, by rfl⟩ : syracuseStep 392555 = 588833) B588833
theorem B392567 : Blo 389765 392567 := bstep (se 1 (by rfl) ⟨294425, by rfl⟩ : syracuseStep 392567 = 588851) B588851
theorem B392587 : Blo 389765 392587 := bstep (se 1 (by rfl) ⟨294440, by rfl⟩ : syracuseStep 392587 = 588881) B588881
theorem B392599 : Blo 389765 392599 := bstep (se 1 (by rfl) ⟨294449, by rfl⟩ : syracuseStep 392599 = 588899) B588899
theorem B392619 : Blo 389765 392619 := bstep (se 1 (by rfl) ⟨294464, by rfl⟩ : syracuseStep 392619 = 588929) B588929
theorem B392631 : Blo 389765 392631 := bstep (se 1 (by rfl) ⟨294473, by rfl⟩ : syracuseStep 392631 = 588947) B588947
theorem B392651 : Blo 389765 392651 := bstep (se 1 (by rfl) ⟨294488, by rfl⟩ : syracuseStep 392651 = 588977) B588977
theorem B589259 : Blo 389765 589259 := bstep (se 1 (by rfl) ⟨441944, by rfl⟩ : syracuseStep 589259 = 883889) B883889
theorem B392663 : Blo 389765 392663 := bstep (se 1 (by rfl) ⟨294497, by rfl⟩ : syracuseStep 392663 = 588995) B588995
theorem B589271 : Blo 389765 589271 := bstep (se 1 (by rfl) ⟨441953, by rfl⟩ : syracuseStep 589271 = 883907) B883907
theorem B392683 : Blo 389765 392683 := bstep (se 1 (by rfl) ⟨294512, by rfl⟩ : syracuseStep 392683 = 589025) B589025
theorem B392695 : Blo 389765 392695 := bstep (se 1 (by rfl) ⟨294521, by rfl⟩ : syracuseStep 392695 = 589043) B589043
theorem B392715 : Blo 389765 392715 := bstep (se 1 (by rfl) ⟨294536, by rfl⟩ : syracuseStep 392715 = 589073) B589073
theorem B392727 : Blo 389765 392727 := bstep (se 1 (by rfl) ⟨294545, by rfl⟩ : syracuseStep 392727 = 589091) B589091
theorem B589337 : Blo 389765 589337 := bstep (se 2 (by rfl) ⟨221001, by rfl⟩ : syracuseStep 589337 = 442003) B442003
theorem B884249 : Blo 389765 884249 := bstep (se 2 (by rfl) ⟨331593, by rfl⟩ : syracuseStep 884249 = 663187) B663187
theorem B392747 : Blo 389765 392747 := bstep (se 1 (by rfl) ⟨294560, by rfl⟩ : syracuseStep 392747 = 589121) B589121
theorem B392759 : Blo 389765 392759 := bstep (se 1 (by rfl) ⟨294569, by rfl⟩ : syracuseStep 392759 = 589139) B589139
theorem B392779 : Blo 389765 392779 := bstep (se 1 (by rfl) ⟨294584, by rfl⟩ : syracuseStep 392779 = 589169) B589169
theorem B392791 : Blo 389765 392791 := bstep (se 1 (by rfl) ⟨294593, by rfl⟩ : syracuseStep 392791 = 589187) B589187
theorem B392811 : Blo 389765 392811 := bstep (se 1 (by rfl) ⟨294608, by rfl⟩ : syracuseStep 392811 = 589217) B589217
theorem B884339 : Blo 389765 884339 := bstep (se 1 (by rfl) ⟨663254, by rfl⟩ : syracuseStep 884339 = 1326509) B1326509
theorem B392823 : Blo 389765 392823 := bstep (se 1 (by rfl) ⟨294617, by rfl⟩ : syracuseStep 392823 = 589235) B589235
theorem B1408643 : Blo 389765 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B392843 : Blo 389765 392843 := bstep (se 1 (by rfl) ⟨294632, by rfl⟩ : syracuseStep 392843 = 589265) B589265
theorem B589451 : Blo 389765 589451 := bstep (se 1 (by rfl) ⟨442088, by rfl⟩ : syracuseStep 589451 = 884177) B884177
theorem B392855 : Blo 389765 392855 := bstep (se 1 (by rfl) ⟨294641, by rfl⟩ : syracuseStep 392855 = 589283) B589283
theorem B589463 : Blo 389765 589463 := bstep (se 1 (by rfl) ⟨442097, by rfl⟩ : syracuseStep 589463 = 884195) B884195
theorem B884375 : Blo 389765 884375 := bstep (se 1 (by rfl) ⟨663281, by rfl⟩ : syracuseStep 884375 = 1326563) B1326563
theorem B851609 : Blo 389765 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B392875 : Blo 389765 392875 := bstep (se 1 (by rfl) ⟨294656, by rfl⟩ : syracuseStep 392875 = 589313) B589313
theorem B392887 : Blo 389765 392887 := bstep (se 1 (by rfl) ⟨294665, by rfl⟩ : syracuseStep 392887 = 589331) B589331
theorem B392907 : Blo 389765 392907 := bstep (se 1 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 392907 = 589361) B589361
theorem B392919 : Blo 389765 392919 := bstep (se 1 (by rfl) ⟨294689, by rfl⟩ : syracuseStep 392919 = 589379) B589379
theorem B589529 : Blo 389765 589529 := bstep (se 2 (by rfl) ⟨221073, by rfl⟩ : syracuseStep 589529 = 442147) B442147
theorem B1113821 : Blo 389765 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B392939 : Blo 389765 392939 := bstep (se 1 (by rfl) ⟨294704, by rfl⟩ : syracuseStep 392939 = 589409) B589409
theorem B392951 : Blo 389765 392951 := bstep (se 1 (by rfl) ⟨294713, by rfl⟩ : syracuseStep 392951 = 589427) B589427
theorem B392971 : Blo 389765 392971 := bstep (se 1 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 392971 = 589457) B589457
theorem B2227985 : Blo 389765 2227985 := bstep (se 2 (by rfl) ⟨835494, by rfl⟩ : syracuseStep 2227985 = 1670989) B1670989
theorem B392983 : Blo 389765 392983 := bstep (se 1 (by rfl) ⟨294737, by rfl⟩ : syracuseStep 392983 = 589475) B589475
theorem B393003 : Blo 389765 393003 := bstep (se 1 (by rfl) ⟨294752, by rfl⟩ : syracuseStep 393003 = 589505) B589505
theorem B393015 : Blo 389765 393015 := bstep (se 1 (by rfl) ⟨294761, by rfl⟩ : syracuseStep 393015 = 589523) B589523
theorem B393035 : Blo 389765 393035 := bstep (se 1 (by rfl) ⟨294776, by rfl⟩ : syracuseStep 393035 = 589553) B589553
theorem B589643 : Blo 389765 589643 := bstep (se 1 (by rfl) ⟨442232, by rfl⟩ : syracuseStep 589643 = 884465) B884465
theorem B884555 : Blo 389765 884555 := bstep (se 1 (by rfl) ⟨663416, by rfl⟩ : syracuseStep 884555 = 1326833) B1326833
theorem B393047 : Blo 389765 393047 := bstep (se 1 (by rfl) ⟨294785, by rfl⟩ : syracuseStep 393047 = 589571) B589571
theorem B589655 : Blo 389765 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B1671005 : Blo 389765 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B393067 : Blo 389765 393067 := bstep (se 1 (by rfl) ⟨294800, by rfl⟩ : syracuseStep 393067 = 589601) B589601
theorem B393079 : Blo 389765 393079 := bstep (se 1 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 393079 = 589619) B589619
theorem B884609 : Blo 389765 884609 := bstep (se 2 (by rfl) ⟨331728, by rfl⟩ : syracuseStep 884609 = 663457) B663457
theorem B393099 : Blo 389765 393099 := bstep (se 1 (by rfl) ⟨294824, by rfl⟩ : syracuseStep 393099 = 589649) B589649
theorem B556951 : Blo 389765 556951 := bstep (se 1 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 556951 = 835427) B835427
theorem B393111 : Blo 389765 393111 := bstep (se 1 (by rfl) ⟨294833, by rfl⟩ : syracuseStep 393111 = 589667) B589667
theorem B589721 : Blo 389765 589721 := bstep (se 2 (by rfl) ⟨221145, by rfl⟩ : syracuseStep 589721 = 442291) B442291
theorem B393131 : Blo 389765 393131 := bstep (se 1 (by rfl) ⟨294848, by rfl⟩ : syracuseStep 393131 = 589697) B589697
theorem B393143 : Blo 389765 393143 := bstep (se 1 (by rfl) ⟨294857, by rfl⟩ : syracuseStep 393143 = 589715) B589715
theorem B1114049 : Blo 389765 1114049 := bstep (se 2 (by rfl) ⟨417768, by rfl⟩ : syracuseStep 1114049 = 835537) B835537
theorem B393163 : Blo 389765 393163 := bstep (se 1 (by rfl) ⟨294872, by rfl⟩ : syracuseStep 393163 = 589745) B589745
theorem B393175 : Blo 389765 393175 := bstep (se 1 (by rfl) ⟨294881, by rfl⟩ : syracuseStep 393175 = 589763) B589763
theorem B1015769 : Blo 389765 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B393195 : Blo 389765 393195 := bstep (se 1 (by rfl) ⟨294896, by rfl⟩ : syracuseStep 393195 = 589793) B589793
theorem B393223 : Blo 389765 393223 := bstep (se 1 (by rfl) ⟨294917, by rfl⟩ : syracuseStep 393223 = 589835) B589835
theorem B393231 : Blo 389765 393231 := bstep (se 1 (by rfl) ⟨294923, by rfl⟩ : syracuseStep 393231 = 589847) B589847
theorem B589883 : Blo 389765 589883 := bstep (se 1 (by rfl) ⟨442412, by rfl⟩ : syracuseStep 589883 = 884825) B884825
theorem B393275 : Blo 389765 393275 := bstep (se 1 (by rfl) ⟨294956, by rfl⟩ : syracuseStep 393275 = 589913) B589913
theorem B1114231 : Blo 389765 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B589943 : Blo 389765 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B393351 : Blo 389765 393351 := bstep (se 1 (by rfl) ⟨295013, by rfl⟩ : syracuseStep 393351 = 590027) B590027
theorem B589967 : Blo 389765 589967 := bstep (se 1 (by rfl) ⟨442475, by rfl⟩ : syracuseStep 589967 = 884951) B884951
theorem B393359 : Blo 389765 393359 := bstep (se 1 (by rfl) ⟨295019, by rfl⟩ : syracuseStep 393359 = 590039) B590039
theorem B590009 : Blo 389765 590009 := bstep (se 2 (by rfl) ⟨221253, by rfl⟩ : syracuseStep 590009 = 442507) B442507
theorem B393403 : Blo 389765 393403 := bstep (se 1 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 393403 = 590105) B590105
theorem B2228417 : Blo 389765 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B1868033 : Blo 389765 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B590087 : Blo 389765 590087 := bstep (se 1 (by rfl) ⟨442565, by rfl⟩ : syracuseStep 590087 = 885131) B885131
theorem B393479 : Blo 389765 393479 := bstep (se 1 (by rfl) ⟨295109, by rfl⟩ : syracuseStep 393479 = 590219) B590219
theorem B393487 : Blo 389765 393487 := bstep (se 1 (by rfl) ⟨295115, by rfl⟩ : syracuseStep 393487 = 590231) B590231
theorem B590123 : Blo 389765 590123 := bstep (se 1 (by rfl) ⟨442592, by rfl⟩ : syracuseStep 590123 = 885185) B885185
theorem B393531 : Blo 389765 393531 := bstep (se 1 (by rfl) ⟨295148, by rfl⟩ : syracuseStep 393531 = 590297) B590297
theorem B590153 : Blo 389765 590153 := bstep (se 2 (by rfl) ⟨221307, by rfl⟩ : syracuseStep 590153 = 442615) B442615
theorem B393607 : Blo 389765 393607 := bstep (se 1 (by rfl) ⟨295205, by rfl⟩ : syracuseStep 393607 = 590411) B590411
theorem B393615 : Blo 389765 393615 := bstep (se 1 (by rfl) ⟨295211, by rfl⟩ : syracuseStep 393615 = 590423) B590423
theorem B590267 : Blo 389765 590267 := bstep (se 1 (by rfl) ⟨442700, by rfl⟩ : syracuseStep 590267 = 885401) B885401
theorem B393659 : Blo 389765 393659 := bstep (se 1 (by rfl) ⟨295244, by rfl⟩ : syracuseStep 393659 = 590489) B590489
theorem B590327 : Blo 389765 590327 := bstep (se 1 (by rfl) ⟨442745, by rfl⟩ : syracuseStep 590327 = 885491) B885491
theorem B393735 : Blo 389765 393735 := bstep (se 1 (by rfl) ⟨295301, by rfl⟩ : syracuseStep 393735 = 590603) B590603
theorem B590351 : Blo 389765 590351 := bstep (se 1 (by rfl) ⟨442763, by rfl⟩ : syracuseStep 590351 = 885527) B885527
theorem B393743 : Blo 389765 393743 := bstep (se 1 (by rfl) ⟨295307, by rfl⟩ : syracuseStep 393743 = 590615) B590615
theorem B754219 : Blo 389765 754219 := bstep (se 1 (by rfl) ⟨565664, by rfl⟩ : syracuseStep 754219 = 1131329) B1131329
theorem B590393 : Blo 389765 590393 := bstep (se 2 (by rfl) ⟨221397, by rfl⟩ : syracuseStep 590393 = 442795) B442795
theorem B885383 : Blo 389765 885383 := bstep (se 1 (by rfl) ⟨664037, by rfl⟩ : syracuseStep 885383 = 1328075) B1328075
theorem B590471 : Blo 389765 590471 := bstep (se 1 (by rfl) ⟨442853, by rfl⟩ : syracuseStep 590471 = 885707) B885707
theorem B590507 : Blo 389765 590507 := bstep (se 1 (by rfl) ⟨442880, by rfl⟩ : syracuseStep 590507 = 885761) B885761
theorem B590537 : Blo 389765 590537 := bstep (se 2 (by rfl) ⟨221451, by rfl⟩ : syracuseStep 590537 = 442903) B442903
theorem B885563 : Blo 389765 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B885689 : Blo 389765 885689 := bstep (se 2 (by rfl) ⟨332133, by rfl⟩ : syracuseStep 885689 = 664267) B664267
theorem B54887381 : Blo 389765 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B558095 : Blo 389765 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B1672235 : Blo 389765 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B3015767 : Blo 389765 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B558409 : Blo 389765 558409 := bstep (se 2 (by rfl) ⟨209403, by rfl⟩ : syracuseStep 558409 = 418807) B418807
theorem B1115507 : Blo 389765 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B1115849 : Blo 389765 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B3344165 : Blo 389765 3344165 := bstep (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) B627031
theorem B1115963 : Blo 389765 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B493447 : Blo 389765 493447 := bstep (se 1 (by rfl) ⟨370085, by rfl⟩ : syracuseStep 493447 = 740171) B740171
theorem B1116089 : Blo 389765 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B4032517 : Blo 389765 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B493867 : Blo 389765 493867 := bstep (se 1 (by rfl) ⟨370400, by rfl⟩ : syracuseStep 493867 = 740801) B740801
theorem B3770833 : Blo 389765 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B494095 : Blo 389765 494095 := bstep (se 1 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 494095 = 741143) B741143
theorem B2984525 : Blo 389765 2984525 := bstep (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) B1119197
theorem B625423 : Blo 389765 625423 := bstep (se 1 (by rfl) ⟨469067, by rfl⟩ : syracuseStep 625423 = 938135) B938135
theorem B3443471 : Blo 389765 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B658219 : Blo 389765 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B658361 : Blo 389765 658361 := bstep (se 2 (by rfl) ⟨246885, by rfl⟩ : syracuseStep 658361 = 493771) B493771
theorem B2821321 : Blo 389765 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B1412333 : Blo 389765 1412333 := bstep (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) B529625
theorem B494839 : Blo 389765 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B20254157 : Blo 389765 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B1117739 : Blo 389765 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B495163 : Blo 389765 495163 := bstep (se 1 (by rfl) ⟨371372, by rfl⟩ : syracuseStep 495163 = 742745) B742745
theorem B659063 : Blo 389765 659063 := bstep (se 1 (by rfl) ⟨494297, by rfl⟩ : syracuseStep 659063 = 988595) B988595
theorem B593543 : Blo 389765 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B7606219 : Blo 389765 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B987137 : Blo 389765 987137 := bstep (se 2 (by rfl) ⟨370176, by rfl⟩ : syracuseStep 987137 = 740353) B740353
theorem B495659 : Blo 389765 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B659515 : Blo 389765 659515 := bstep (se 1 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 659515 = 989273) B989273
theorem B659657 : Blo 389765 659657 := bstep (se 2 (by rfl) ⟨247371, by rfl⟩ : syracuseStep 659657 = 494743) B494743
theorem B108532061 : Blo 389765 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B987511 : Blo 389765 987511 := bstep (se 1 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 987511 = 1481267) B1481267
theorem B496135 : Blo 389765 496135 := bstep (se 1 (by rfl) ⟨372101, by rfl⟩ : syracuseStep 496135 = 744203) B744203
theorem B1118731 : Blo 389765 1118731 := bstep (se 1 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 1118731 = 1678097) B1678097
theorem B1413719 : Blo 389765 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B529015 : Blo 389765 529015 := bstep (se 1 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 529015 = 793523) B793523
theorem B8622773 : Blo 389765 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B4789007 : Blo 389765 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1119005 : Blo 389765 1119005 := bstep (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) B419627
theorem B987947 : Blo 389765 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B1413947 : Blo 389765 1413947 := bstep (se 1 (by rfl) ⟨1060460, by rfl⟩ : syracuseStep 1413947 = 2120921) B2120921
theorem B660359 : Blo 389765 660359 := bstep (se 1 (by rfl) ⟨495269, by rfl⟩ : syracuseStep 660359 = 990539) B990539
theorem B14554037 : Blo 389765 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B2233291 : Blo 389765 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B2986955 : Blo 389765 2986955 := bstep (se 1 (by rfl) ⟨2240216, by rfl⟩ : syracuseStep 2986955 = 4480433) B4480433
theorem B496631 : Blo 389765 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B496783 : Blo 389765 496783 := bstep (se 1 (by rfl) ⟨372587, by rfl⟩ : syracuseStep 496783 = 745175) B745175
theorem B496955 : Blo 389765 496955 := bstep (se 1 (by rfl) ⟨372716, by rfl⟩ : syracuseStep 496955 = 745433) B745433
theorem B595343 : Blo 389765 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B1316249 : Blo 389765 1316249 := bstep (se 2 (by rfl) ⟨493593, by rfl⟩ : syracuseStep 1316249 = 987187) B987187
theorem B661007 : Blo 389765 661007 := bstep (se 1 (by rfl) ⟨495755, by rfl⟩ : syracuseStep 661007 = 991511) B991511
theorem B988787 : Blo 389765 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B988807 : Blo 389765 988807 := bstep (se 1 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 988807 = 1483211) B1483211
theorem B3348161 : Blo 389765 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B1480463 : Blo 389765 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B989081 : Blo 389765 989081 := bstep (se 2 (by rfl) ⟨370905, by rfl⟩ : syracuseStep 989081 = 741811) B741811
theorem B661547 : Blo 389765 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B989243 : Blo 389765 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B1316951 : Blo 389765 1316951 := bstep (se 1 (by rfl) ⟨987713, by rfl⟩ : syracuseStep 1316951 = 1975427) B1975427
theorem B497927 : Blo 389765 497927 := bstep (se 1 (by rfl) ⟨373445, by rfl⟩ : syracuseStep 497927 = 746891) B746891
theorem B1874191 : Blo 389765 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B989455 : Blo 389765 989455 := bstep (se 1 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 989455 = 1484183) B1484183
theorem B2005337 : Blo 389765 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B661945 : Blo 389765 661945 := bstep (se 2 (by rfl) ⟨248229, by rfl⟩ : syracuseStep 661945 = 496459) B496459
theorem B989729 : Blo 389765 989729 := bstep (se 2 (by rfl) ⟨371148, by rfl⟩ : syracuseStep 989729 = 742297) B742297
theorem B1317437 : Blo 389765 1317437 := bstep (se 3 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 1317437 = 494039) B494039
theorem B1121111 : Blo 389765 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B662647 : Blo 389765 662647 := bstep (se 1 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 662647 = 993971) B993971
theorem B5020805 : Blo 389765 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B1875251 : Blo 389765 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B662843 : Blo 389765 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B2235707 : Blo 389765 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B1875421 : Blo 389765 1875421 := bstep (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) B703283
theorem B990731 : Blo 389765 990731 := bstep (se 1 (by rfl) ⟨743048, by rfl⟩ : syracuseStep 990731 = 1486097) B1486097
theorem B1875575 : Blo 389765 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B663241 : Blo 389765 663241 := bstep (se 2 (by rfl) ⟨248715, by rfl⟩ : syracuseStep 663241 = 497431) B497431
theorem B1056527 : Blo 389765 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B597775 : Blo 389765 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B1974131 : Blo 389765 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B1318841 : Blo 389765 1318841 := bstep (se 2 (by rfl) ⟨494565, by rfl⟩ : syracuseStep 1318841 = 989131) B989131
theorem B598031 : Blo 389765 598031 := bstep (se 1 (by rfl) ⟨448523, by rfl⟩ : syracuseStep 598031 = 897047) B897047
theorem B1187959 : Blo 389765 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B991379 : Blo 389765 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B1974617 : Blo 389765 1974617 := bstep (se 2 (by rfl) ⟨740481, by rfl⟩ : syracuseStep 1974617 = 1480963) B1480963
theorem B663943 : Blo 389765 663943 := bstep (se 1 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 663943 = 995915) B995915
theorem B991673 : Blo 389765 991673 := bstep (se 2 (by rfl) ⟨371877, by rfl⟩ : syracuseStep 991673 = 743755) B743755
theorem B1319435 : Blo 389765 1319435 := bstep (se 1 (by rfl) ⟨989576, by rfl⟩ : syracuseStep 1319435 = 1979153) B1979153
theorem B3580483 : Blo 389765 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B1319543 : Blo 389765 1319543 := bstep (se 1 (by rfl) ⟨989657, by rfl⟩ : syracuseStep 1319543 = 1979315) B1979315
theorem B2237165 : Blo 389765 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B1483667 : Blo 389765 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B2237483 : Blo 389765 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B992371 : Blo 389765 992371 := bstep (se 1 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 992371 = 1488557) B1488557
theorem B1320137 : Blo 389765 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B992513 : Blo 389765 992513 := bstep (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) B744385
theorem B3024263 : Blo 389765 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B566843 : Blo 389765 566843 := bstep (se 1 (by rfl) ⟨425132, by rfl⟩ : syracuseStep 566843 = 850265) B850265
theorem B1680983 : Blo 389765 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B992969 : Blo 389765 992969 := bstep (se 2 (by rfl) ⟨372363, by rfl⟩ : syracuseStep 992969 = 744727) B744727
theorem B1320839 : Blo 389765 1320839 := bstep (se 1 (by rfl) ⟨990629, by rfl⟩ : syracuseStep 1320839 = 1981259) B1981259
theorem B993323 : Blo 389765 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B469163 : Blo 389765 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B3188909 : Blo 389765 3188909 := bstep (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) B1195841
theorem B1321217 : Blo 389765 1321217 := bstep (se 2 (by rfl) ⟨495456, by rfl⟩ : syracuseStep 1321217 = 990913) B990913
theorem B7547201 : Blo 389765 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B3746195 : Blo 389765 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B1976723 : Blo 389765 1976723 := bstep (se 1 (by rfl) ⟨1482542, by rfl⟩ : syracuseStep 1976723 = 2965085) B2965085
theorem B567739 : Blo 389765 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B2238941 : Blo 389765 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B1485323 : Blo 389765 1485323 := bstep (se 1 (by rfl) ⟨1113992, by rfl⟩ : syracuseStep 1485323 = 2227985) B2227985
theorem B1780481 : Blo 389765 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B9186085 : Blo 389765 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1190771 : Blo 389765 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B11447203 : Blo 389765 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B994315 : Blo 389765 994315 := bstep (se 1 (by rfl) ⟨745736, by rfl⟩ : syracuseStep 994315 = 1491473) B1491473
theorem B1322027 : Blo 389765 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B994457 : Blo 389765 994457 := bstep (se 2 (by rfl) ⟨372921, by rfl⟩ : syracuseStep 994457 = 745843) B745843
theorem B994619 : Blo 389765 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B1256971 : Blo 389765 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B1257047 : Blo 389765 1257047 := bstep (se 1 (by rfl) ⟨942785, by rfl⟩ : syracuseStep 1257047 = 1885571) B1885571
theorem B3780215 : Blo 389765 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B994963 : Blo 389765 994963 := bstep (se 1 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 994963 = 1492445) B1492445
theorem B995105 : Blo 389765 995105 := bstep (se 2 (by rfl) ⟨373164, by rfl⟩ : syracuseStep 995105 = 746329) B746329
theorem B2109331 : Blo 389765 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B1191937 : Blo 389765 1191937 := bstep (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) B893953
theorem B22556717 : Blo 389765 22556717 := bstep (se 3 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 22556717 = 8458769) B8458769
theorem B1323323 : Blo 389765 1323323 := bstep (se 1 (by rfl) ⟨992492, by rfl⟩ : syracuseStep 1323323 = 1984985) B1984985
theorem B438799 : Blo 389765 438799 := bstep (se 1 (by rfl) ⟨329099, by rfl⟩ : syracuseStep 438799 = 658199) B658199
theorem B1192583 : Blo 389765 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B471739 : Blo 389765 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B996097 : Blo 389765 996097 := bstep (se 2 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 996097 = 747073) B747073
theorem B1323809 : Blo 389765 1323809 := bstep (se 2 (by rfl) ⟨496428, by rfl⟩ : syracuseStep 1323809 = 992857) B992857
theorem B2372611 : Blo 389765 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B2241539 : Blo 389765 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B439303 : Blo 389765 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B3748997 : Blo 389765 3748997 := bstep (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) B702937
theorem B439483 : Blo 389765 439483 := bstep (se 1 (by rfl) ⟨329612, by rfl⟩ : syracuseStep 439483 = 659225) B659225
theorem B996695 : Blo 389765 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B1324403 : Blo 389765 1324403 := bstep (se 1 (by rfl) ⟨993302, by rfl⟩ : syracuseStep 1324403 = 1986605) B1986605
theorem B2012561 : Blo 389765 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B1979801 : Blo 389765 1979801 := bstep (se 2 (by rfl) ⟨742425, by rfl⟩ : syracuseStep 1979801 = 1484851) B1484851
theorem B439951 : Blo 389765 439951 := bstep (se 1 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 439951 = 659927) B659927
theorem B1587059 : Blo 389765 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B1062841 : Blo 389765 1062841 := bstep (se 2 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 1062841 = 797131) B797131
theorem B440455 : Blo 389765 440455 := bstep (se 1 (by rfl) ⟨330341, by rfl⟩ : syracuseStep 440455 = 660683) B660683
theorem B3356909 : Blo 389765 3356909 := bstep (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) B1258841
theorem B440635 : Blo 389765 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B1489211 : Blo 389765 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B1063315 : Blo 389765 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1030553 : Blo 389765 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B441103 : Blo 389765 441103 := bstep (se 1 (by rfl) ⟨330827, by rfl⟩ : syracuseStep 441103 = 661655) B661655
theorem B1489697 : Blo 389765 1489697 := bstep (se 2 (by rfl) ⟨558636, by rfl⟩ : syracuseStep 1489697 = 1117273) B1117273
theorem B3160883 : Blo 389765 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B1882939 : Blo 389765 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B932879 : Blo 389765 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B441607 : Blo 389765 441607 := bstep (se 1 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 441607 = 662411) B662411
theorem B441787 : Blo 389765 441787 := bstep (se 1 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 441787 = 662681) B662681
theorem B1490669 : Blo 389765 1490669 := bstep (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) B559001
theorem B442255 : Blo 389765 442255 := bstep (se 1 (by rfl) ⟨331691, by rfl⟩ : syracuseStep 442255 = 663383) B663383
theorem B1326995 : Blo 389765 1326995 := bstep (se 1 (by rfl) ⟨995246, by rfl⟩ : syracuseStep 1326995 = 1990493) B1990493
theorem B1982393 : Blo 389765 1982393 := bstep (se 2 (by rfl) ⟨743397, by rfl⟩ : syracuseStep 1982393 = 1486795) B1486795
theorem B1490987 : Blo 389765 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B704783 : Blo 389765 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B442759 : Blo 389765 442759 := bstep (se 1 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 442759 = 664139) B664139
theorem B2670995 : Blo 389765 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B442939 : Blo 389765 442939 := bstep (se 1 (by rfl) ⟨332204, by rfl⟩ : syracuseStep 442939 = 664409) B664409
theorem B2114221 : Blo 389765 2114221 := bstep (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) B792833
theorem B1885187 : Blo 389765 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B1983689 : Blo 389765 1983689 := bstep (se 2 (by rfl) ⟨743883, by rfl⟩ : syracuseStep 1983689 = 1487767) B1487767
theorem B1328399 : Blo 389765 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B1852723 : Blo 389765 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B5064067 : Blo 389765 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B574921 : Blo 389765 574921 := bstep (se 2 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 574921 = 431191) B431191
theorem B4015565 : Blo 389765 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B4244957 : Blo 389765 4244957 := bstep (se 3 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 4244957 = 1591859) B1591859
theorem B3556867 : Blo 389765 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B2835971 : Blo 389765 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B1328669 : Blo 389765 1328669 := bstep (se 3 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 1328669 = 498251) B498251
theorem B575033 : Blo 389765 575033 := bstep (se 2 (by rfl) ⟨215637, by rfl⟩ : syracuseStep 575033 = 431275) B431275
theorem B2508407 : Blo 389765 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B2115821 : Blo 389765 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B4540931 : Blo 389765 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B3361283 : Blo 389765 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B2509379 : Blo 389765 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B1428509 : Blo 389765 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B838775 : Blo 389765 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B740755 : Blo 389765 740755 := bstep (se 1 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 740755 = 1111133) B1111133
theorem B1494557 : Blo 389765 1494557 := bstep (se 3 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 1494557 = 560459) B560459
theorem B1494571 : Blo 389765 1494571 := bstep (se 1 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 1494571 = 2241857) B2241857
theorem B740983 : Blo 389765 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B937673 : Blo 389765 937673 := bstep (se 2 (by rfl) ⟨351627, by rfl⟩ : syracuseStep 937673 = 703255) B703255
theorem B446215 : Blo 389765 446215 := bstep (se 1 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 446215 = 669323) B669323
theorem B2969459 : Blo 389765 2969459 := bstep (se 1 (by rfl) ⟨2227094, by rfl⟩ : syracuseStep 2969459 = 4454189) B4454189
theorem B1790039 : Blo 389765 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B708755 : Blo 389765 708755 := bstep (se 1 (by rfl) ⟨531566, by rfl⟩ : syracuseStep 708755 = 1063133) B1063133
theorem B5722667 : Blo 389765 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B4477517 : Blo 389765 4477517 := bstep (se 3 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 4477517 = 1679069) B1679069
theorem B1692683 : Blo 389765 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B939095 : Blo 389765 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B742547 : Blo 389765 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B840851 : Blo 389765 840851 := bstep (se 1 (by rfl) ⟨630638, by rfl⟩ : syracuseStep 840851 = 1261277) B1261277
theorem B742601 : Blo 389765 742601 := bstep (se 2 (by rfl) ⟨278475, by rfl⟩ : syracuseStep 742601 = 556951) B556951
theorem B742699 : Blo 389765 742699 := bstep (se 1 (by rfl) ⟨557024, by rfl⟩ : syracuseStep 742699 = 1114049) B1114049
theorem B677179 : Blo 389765 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B5363003 : Blo 389765 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B742927 : Blo 389765 742927 := bstep (se 1 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 742927 = 1114391) B1114391
theorem B2513069 : Blo 389765 2513069 := bstep (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) B942401
theorem B940403 : Blo 389765 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B1432075 : Blo 389765 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B1890935 : Blo 389765 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B4446899 : Blo 389765 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B940729 : Blo 389765 940729 := bstep (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) B705547
theorem B1989521 : Blo 389765 1989521 := bstep (se 2 (by rfl) ⟨746070, by rfl⟩ : syracuseStep 1989521 = 1492141) B1492141
theorem B744491 : Blo 389765 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B941345 : Blo 389765 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B1793603 : Blo 389765 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B941959 : Blo 389765 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B2122307 : Blo 389765 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B877175 : Blo 389765 877175 := bstep (se 1 (by rfl) ⟨657881, by rfl⟩ : syracuseStep 877175 = 1315763) B1315763
theorem B746185 : Blo 389765 746185 := bstep (se 2 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 746185 = 559639) B559639
theorem B877355 : Blo 389765 877355 := bstep (se 1 (by rfl) ⟨658016, by rfl⟩ : syracuseStep 877355 = 1316033) B1316033
theorem B1991627 : Blo 389765 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B844843 : Blo 389765 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B877715 : Blo 389765 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B877769 : Blo 389765 877769 := bstep (se 2 (by rfl) ⟨329163, by rfl⟩ : syracuseStep 877769 = 658327) B658327
theorem B1991951 : Blo 389765 1991951 := bstep (se 1 (by rfl) ⟨1493963, by rfl⟩ : syracuseStep 1991951 = 2987927) B2987927
theorem B14444401 : Blo 389765 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B878471 : Blo 389765 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B5335085 : Blo 389765 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B878651 : Blo 389765 878651 := bstep (se 1 (by rfl) ⟨658988, by rfl⟩ : syracuseStep 878651 = 1317977) B1317977
theorem B878777 : Blo 389765 878777 := bstep (se 2 (by rfl) ⟨329541, by rfl⟩ : syracuseStep 878777 = 659083) B659083
theorem B4778299 : Blo 389765 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B4745603 : Blo 389765 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B4221389 : Blo 389765 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B879119 : Blo 389765 879119 := bstep (se 1 (by rfl) ⟨659339, by rfl⟩ : syracuseStep 879119 = 1318679) B1318679
theorem B879137 : Blo 389765 879137 := bstep (se 2 (by rfl) ⟨329676, by rfl⟩ : syracuseStep 879137 = 659353) B659353
theorem B1993409 : Blo 389765 1993409 := bstep (se 2 (by rfl) ⟨747528, by rfl⟩ : syracuseStep 1993409 = 1495057) B1495057
theorem B944939 : Blo 389765 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B879479 : Blo 389765 879479 := bstep (se 1 (by rfl) ⟨659609, by rfl⟩ : syracuseStep 879479 = 1319219) B1319219
theorem B9956357 : Blo 389765 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B584711 : Blo 389765 584711 := bstep (se 1 (by rfl) ⟨438533, by rfl⟩ : syracuseStep 584711 = 877067) B877067
theorem B584747 : Blo 389765 584747 := bstep (se 1 (by rfl) ⟨438560, by rfl⟩ : syracuseStep 584747 = 877121) B877121
theorem B879659 : Blo 389765 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B584777 : Blo 389765 584777 := bstep (se 2 (by rfl) ⟨219291, by rfl⟩ : syracuseStep 584777 = 438583) B438583
theorem B584891 : Blo 389765 584891 := bstep (se 1 (by rfl) ⟨438668, by rfl⟩ : syracuseStep 584891 = 877337) B877337
theorem B584951 : Blo 389765 584951 := bstep (se 1 (by rfl) ⟨438713, by rfl⟩ : syracuseStep 584951 = 877427) B877427
theorem B584975 : Blo 389765 584975 := bstep (se 1 (by rfl) ⟨438731, by rfl⟩ : syracuseStep 584975 = 877463) B877463
theorem B585017 : Blo 389765 585017 := bstep (se 2 (by rfl) ⟨219381, by rfl⟩ : syracuseStep 585017 = 438763) B438763
theorem B585095 : Blo 389765 585095 := bstep (se 1 (by rfl) ⟨438821, by rfl⟩ : syracuseStep 585095 = 877643) B877643
theorem B880019 : Blo 389765 880019 := bstep (se 1 (by rfl) ⟨660014, by rfl⟩ : syracuseStep 880019 = 1320029) B1320029
theorem B585131 : Blo 389765 585131 := bstep (se 1 (by rfl) ⟨438848, by rfl⟩ : syracuseStep 585131 = 877697) B877697
theorem B585161 : Blo 389765 585161 := bstep (se 2 (by rfl) ⟨219435, by rfl⟩ : syracuseStep 585161 = 438871) B438871
theorem B880073 : Blo 389765 880073 := bstep (se 2 (by rfl) ⟨330027, by rfl⟩ : syracuseStep 880073 = 660055) B660055
theorem B585275 : Blo 389765 585275 := bstep (se 1 (by rfl) ⟨438956, by rfl⟩ : syracuseStep 585275 = 877913) B877913
theorem B585335 : Blo 389765 585335 := bstep (se 1 (by rfl) ⟨439001, by rfl⟩ : syracuseStep 585335 = 878003) B878003
theorem B585359 : Blo 389765 585359 := bstep (se 1 (by rfl) ⟨439019, by rfl⟩ : syracuseStep 585359 = 878039) B878039
theorem B585401 : Blo 389765 585401 := bstep (se 2 (by rfl) ⟨219525, by rfl⟩ : syracuseStep 585401 = 439051) B439051
theorem B585479 : Blo 389765 585479 := bstep (se 1 (by rfl) ⟨439109, by rfl⟩ : syracuseStep 585479 = 878219) B878219
theorem B585515 : Blo 389765 585515 := bstep (se 1 (by rfl) ⟨439136, by rfl⟩ : syracuseStep 585515 = 878273) B878273
theorem B585545 : Blo 389765 585545 := bstep (se 2 (by rfl) ⟨219579, by rfl⟩ : syracuseStep 585545 = 439159) B439159
theorem B585659 : Blo 389765 585659 := bstep (se 1 (by rfl) ⟨439244, by rfl⟩ : syracuseStep 585659 = 878489) B878489
theorem B585719 : Blo 389765 585719 := bstep (se 1 (by rfl) ⟨439289, by rfl⟩ : syracuseStep 585719 = 878579) B878579
theorem B1110017 : Blo 389765 1110017 := bstep (se 2 (by rfl) ⟨416256, by rfl⟩ : syracuseStep 1110017 = 832513) B832513
theorem B585743 : Blo 389765 585743 := bstep (se 1 (by rfl) ⟨439307, by rfl⟩ : syracuseStep 585743 = 878615) B878615
theorem B585785 : Blo 389765 585785 := bstep (se 2 (by rfl) ⟨219669, by rfl⟩ : syracuseStep 585785 = 439339) B439339
theorem B1110131 : Blo 389765 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B585863 : Blo 389765 585863 := bstep (se 1 (by rfl) ⟨439397, by rfl⟩ : syracuseStep 585863 = 878795) B878795
theorem B880775 : Blo 389765 880775 := bstep (se 1 (by rfl) ⟨660581, by rfl⟩ : syracuseStep 880775 = 1321163) B1321163
theorem B585899 : Blo 389765 585899 := bstep (se 1 (by rfl) ⟨439424, by rfl⟩ : syracuseStep 585899 = 878849) B878849
theorem B585929 : Blo 389765 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B2289971 : Blo 389765 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B586043 : Blo 389765 586043 := bstep (se 1 (by rfl) ⟨439532, by rfl⟩ : syracuseStep 586043 = 879065) B879065
theorem B880955 : Blo 389765 880955 := bstep (se 1 (by rfl) ⟨660716, by rfl⟩ : syracuseStep 880955 = 1321433) B1321433
theorem B586103 : Blo 389765 586103 := bstep (se 1 (by rfl) ⟨439577, by rfl⟩ : syracuseStep 586103 = 879155) B879155
theorem B1503623 : Blo 389765 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B586127 : Blo 389765 586127 := bstep (se 1 (by rfl) ⟨439595, by rfl⟩ : syracuseStep 586127 = 879191) B879191
theorem B2388371 : Blo 389765 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B586169 : Blo 389765 586169 := bstep (se 2 (by rfl) ⟨219813, by rfl⟩ : syracuseStep 586169 = 439627) B439627
theorem B881081 : Blo 389765 881081 := bstep (se 2 (by rfl) ⟨330405, by rfl⟩ : syracuseStep 881081 = 660811) B660811
theorem B1110473 : Blo 389765 1110473 := bstep (se 2 (by rfl) ⟨416427, by rfl⟩ : syracuseStep 1110473 = 832855) B832855
theorem B586247 : Blo 389765 586247 := bstep (se 1 (by rfl) ⟨439685, by rfl⟩ : syracuseStep 586247 = 879371) B879371
theorem B586283 : Blo 389765 586283 := bstep (se 1 (by rfl) ⟨439712, by rfl⟩ : syracuseStep 586283 = 879425) B879425
theorem B586313 : Blo 389765 586313 := bstep (se 2 (by rfl) ⟨219867, by rfl⟩ : syracuseStep 586313 = 439735) B439735
theorem B389767 : Blo 389765 389767 := bstep (se 1 (by rfl) ⟨292325, by rfl⟩ : syracuseStep 389767 = 584651) B584651
theorem B389775 : Blo 389765 389775 := bstep (se 1 (by rfl) ⟨292331, by rfl⟩ : syracuseStep 389775 = 584663) B584663
theorem B389819 : Blo 389765 389819 := bstep (se 1 (by rfl) ⟨292364, by rfl⟩ : syracuseStep 389819 = 584729) B584729
theorem B586427 : Blo 389765 586427 := bstep (se 1 (by rfl) ⟨439820, by rfl⟩ : syracuseStep 586427 = 879641) B879641
theorem B586487 : Blo 389765 586487 := bstep (se 1 (by rfl) ⟨439865, by rfl⟩ : syracuseStep 586487 = 879731) B879731
theorem B389895 : Blo 389765 389895 := bstep (se 1 (by rfl) ⟨292421, by rfl⟩ : syracuseStep 389895 = 584843) B584843
theorem B389903 : Blo 389765 389903 := bstep (se 1 (by rfl) ⟨292427, by rfl⟩ : syracuseStep 389903 = 584855) B584855
theorem B586511 : Blo 389765 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B881423 : Blo 389765 881423 := bstep (se 1 (by rfl) ⟨661067, by rfl⟩ : syracuseStep 881423 = 1322135) B1322135
theorem B881441 : Blo 389765 881441 := bstep (se 2 (by rfl) ⟨330540, by rfl⟩ : syracuseStep 881441 = 661081) B661081
theorem B586553 : Blo 389765 586553 := bstep (se 2 (by rfl) ⟨219957, by rfl⟩ : syracuseStep 586553 = 439915) B439915
theorem B389947 : Blo 389765 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B390023 : Blo 389765 390023 := bstep (se 1 (by rfl) ⟨292517, by rfl⟩ : syracuseStep 390023 = 585035) B585035
theorem B586631 : Blo 389765 586631 := bstep (se 1 (by rfl) ⟨439973, by rfl⟩ : syracuseStep 586631 = 879947) B879947
theorem B390031 : Blo 389765 390031 := bstep (se 1 (by rfl) ⟨292523, by rfl⟩ : syracuseStep 390031 = 585047) B585047
theorem B586667 : Blo 389765 586667 := bstep (se 1 (by rfl) ⟨440000, by rfl⟩ : syracuseStep 586667 = 880001) B880001
theorem B390075 : Blo 389765 390075 := bstep (se 1 (by rfl) ⟨292556, by rfl⟩ : syracuseStep 390075 = 585113) B585113
theorem B586697 : Blo 389765 586697 := bstep (se 2 (by rfl) ⟨220011, by rfl⟩ : syracuseStep 586697 = 440023) B440023
theorem B390151 : Blo 389765 390151 := bstep (se 1 (by rfl) ⟨292613, by rfl⟩ : syracuseStep 390151 = 585227) B585227
theorem B390159 : Blo 389765 390159 := bstep (se 1 (by rfl) ⟨292619, by rfl⟩ : syracuseStep 390159 = 585239) B585239
theorem B390203 : Blo 389765 390203 := bstep (se 1 (by rfl) ⟨292652, by rfl⟩ : syracuseStep 390203 = 585305) B585305
theorem B586811 : Blo 389765 586811 := bstep (se 1 (by rfl) ⟨440108, by rfl⟩ : syracuseStep 586811 = 880217) B880217
theorem B586871 : Blo 389765 586871 := bstep (se 1 (by rfl) ⟨440153, by rfl⟩ : syracuseStep 586871 = 880307) B880307
theorem B881783 : Blo 389765 881783 := bstep (se 1 (by rfl) ⟨661337, by rfl⟩ : syracuseStep 881783 = 1322675) B1322675
theorem B390279 : Blo 389765 390279 := bstep (se 1 (by rfl) ⟨292709, by rfl⟩ : syracuseStep 390279 = 585419) B585419
theorem B390287 : Blo 389765 390287 := bstep (se 1 (by rfl) ⟨292715, by rfl⟩ : syracuseStep 390287 = 585431) B585431
theorem B586895 : Blo 389765 586895 := bstep (se 1 (by rfl) ⟨440171, by rfl⟩ : syracuseStep 586895 = 880343) B880343
theorem B586937 : Blo 389765 586937 := bstep (se 2 (by rfl) ⟨220101, by rfl⟩ : syracuseStep 586937 = 440203) B440203
theorem B390331 : Blo 389765 390331 := bstep (se 1 (by rfl) ⟨292748, by rfl⟩ : syracuseStep 390331 = 585497) B585497
theorem B390407 : Blo 389765 390407 := bstep (se 1 (by rfl) ⟨292805, by rfl⟩ : syracuseStep 390407 = 585611) B585611
theorem B587015 : Blo 389765 587015 := bstep (se 1 (by rfl) ⟨440261, by rfl⟩ : syracuseStep 587015 = 880523) B880523
theorem B390415 : Blo 389765 390415 := bstep (se 1 (by rfl) ⟨292811, by rfl⟩ : syracuseStep 390415 = 585623) B585623
theorem B587051 : Blo 389765 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B881963 : Blo 389765 881963 := bstep (se 1 (by rfl) ⟨661472, by rfl⟩ : syracuseStep 881963 = 1322945) B1322945
theorem B390459 : Blo 389765 390459 := bstep (se 1 (by rfl) ⟨292844, by rfl⟩ : syracuseStep 390459 = 585689) B585689
theorem B587081 : Blo 389765 587081 := bstep (se 2 (by rfl) ⟨220155, by rfl⟩ : syracuseStep 587081 = 440311) B440311
theorem B390535 : Blo 389765 390535 := bstep (se 1 (by rfl) ⟨292901, by rfl⟩ : syracuseStep 390535 = 585803) B585803
theorem B390543 : Blo 389765 390543 := bstep (se 1 (by rfl) ⟨292907, by rfl⟩ : syracuseStep 390543 = 585815) B585815
theorem B390587 : Blo 389765 390587 := bstep (se 1 (by rfl) ⟨292940, by rfl⟩ : syracuseStep 390587 = 585881) B585881
theorem B587195 : Blo 389765 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B587255 : Blo 389765 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B390663 : Blo 389765 390663 := bstep (se 1 (by rfl) ⟨292997, by rfl⟩ : syracuseStep 390663 = 585995) B585995
theorem B390671 : Blo 389765 390671 := bstep (se 1 (by rfl) ⟨293003, by rfl⟩ : syracuseStep 390671 = 586007) B586007
theorem B587279 : Blo 389765 587279 := bstep (se 1 (by rfl) ⟨440459, by rfl⟩ : syracuseStep 587279 = 880919) B880919
theorem B587321 : Blo 389765 587321 := bstep (se 2 (by rfl) ⟨220245, by rfl⟩ : syracuseStep 587321 = 440491) B440491
theorem B390715 : Blo 389765 390715 := bstep (se 1 (by rfl) ⟨293036, by rfl⟩ : syracuseStep 390715 = 586073) B586073
theorem B390791 : Blo 389765 390791 := bstep (se 1 (by rfl) ⟨293093, by rfl⟩ : syracuseStep 390791 = 586187) B586187
theorem B587399 : Blo 389765 587399 := bstep (se 1 (by rfl) ⟨440549, by rfl⟩ : syracuseStep 587399 = 881099) B881099
theorem B390799 : Blo 389765 390799 := bstep (se 1 (by rfl) ⟨293099, by rfl⟩ : syracuseStep 390799 = 586199) B586199
theorem B882323 : Blo 389765 882323 := bstep (se 1 (by rfl) ⟨661742, by rfl⟩ : syracuseStep 882323 = 1323485) B1323485
theorem B587435 : Blo 389765 587435 := bstep (se 1 (by rfl) ⟨440576, by rfl⟩ : syracuseStep 587435 = 881153) B881153
theorem B390843 : Blo 389765 390843 := bstep (se 1 (by rfl) ⟨293132, by rfl⟩ : syracuseStep 390843 = 586265) B586265
theorem B587465 : Blo 389765 587465 := bstep (se 2 (by rfl) ⟨220299, by rfl⟩ : syracuseStep 587465 = 440599) B440599
theorem B882377 : Blo 389765 882377 := bstep (se 2 (by rfl) ⟨330891, by rfl⟩ : syracuseStep 882377 = 661783) B661783
theorem B390919 : Blo 389765 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B390927 : Blo 389765 390927 := bstep (se 1 (by rfl) ⟨293195, by rfl⟩ : syracuseStep 390927 = 586391) B586391
theorem B751403 : Blo 389765 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B390971 : Blo 389765 390971 := bstep (se 1 (by rfl) ⟨293228, by rfl⟩ : syracuseStep 390971 = 586457) B586457
theorem B587579 : Blo 389765 587579 := bstep (se 1 (by rfl) ⟨440684, by rfl⟩ : syracuseStep 587579 = 881369) B881369
theorem B4028249 : Blo 389765 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B587639 : Blo 389765 587639 := bstep (se 1 (by rfl) ⟨440729, by rfl⟩ : syracuseStep 587639 = 881459) B881459
theorem B391047 : Blo 389765 391047 := bstep (se 1 (by rfl) ⟨293285, by rfl⟩ : syracuseStep 391047 = 586571) B586571
theorem B391055 : Blo 389765 391055 := bstep (se 1 (by rfl) ⟨293291, by rfl⟩ : syracuseStep 391055 = 586583) B586583
theorem B587663 : Blo 389765 587663 := bstep (se 1 (by rfl) ⟨440747, by rfl⟩ : syracuseStep 587663 = 881495) B881495
theorem B587705 : Blo 389765 587705 := bstep (se 2 (by rfl) ⟨220389, by rfl⟩ : syracuseStep 587705 = 440779) B440779
theorem B391099 : Blo 389765 391099 := bstep (se 1 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 391099 = 586649) B586649
theorem B391175 : Blo 389765 391175 := bstep (se 1 (by rfl) ⟨293381, by rfl⟩ : syracuseStep 391175 = 586763) B586763
theorem B587783 : Blo 389765 587783 := bstep (se 1 (by rfl) ⟨440837, by rfl⟩ : syracuseStep 587783 = 881675) B881675
theorem B391183 : Blo 389765 391183 := bstep (se 1 (by rfl) ⟨293387, by rfl⟩ : syracuseStep 391183 = 586775) B586775
theorem B587819 : Blo 389765 587819 := bstep (se 1 (by rfl) ⟨440864, by rfl⟩ : syracuseStep 587819 = 881729) B881729
theorem B391227 : Blo 389765 391227 := bstep (se 1 (by rfl) ⟨293420, by rfl⟩ : syracuseStep 391227 = 586841) B586841
theorem B587849 : Blo 389765 587849 := bstep (se 2 (by rfl) ⟨220443, by rfl⟩ : syracuseStep 587849 = 440887) B440887
theorem B1964119 : Blo 389765 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B391303 : Blo 389765 391303 := bstep (se 1 (by rfl) ⟨293477, by rfl⟩ : syracuseStep 391303 = 586955) B586955
theorem B391311 : Blo 389765 391311 := bstep (se 1 (by rfl) ⟨293483, by rfl⟩ : syracuseStep 391311 = 586967) B586967
theorem B555179 : Blo 389765 555179 := bstep (se 1 (by rfl) ⟨416384, by rfl⟩ : syracuseStep 555179 = 832769) B832769
theorem B391355 : Blo 389765 391355 := bstep (se 1 (by rfl) ⟨293516, by rfl⟩ : syracuseStep 391355 = 587033) B587033
theorem B587963 : Blo 389765 587963 := bstep (se 1 (by rfl) ⟨440972, by rfl⟩ : syracuseStep 587963 = 881945) B881945
theorem B588023 : Blo 389765 588023 := bstep (se 1 (by rfl) ⟨441017, by rfl⟩ : syracuseStep 588023 = 882035) B882035
theorem B391431 : Blo 389765 391431 := bstep (se 1 (by rfl) ⟨293573, by rfl⟩ : syracuseStep 391431 = 587147) B587147
theorem B391439 : Blo 389765 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B588047 : Blo 389765 588047 := bstep (se 1 (by rfl) ⟨441035, by rfl⟩ : syracuseStep 588047 = 882071) B882071
theorem B1112363 : Blo 389765 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B588089 : Blo 389765 588089 := bstep (se 2 (by rfl) ⟨220533, by rfl⟩ : syracuseStep 588089 = 441067) B441067
theorem B391483 : Blo 389765 391483 := bstep (se 1 (by rfl) ⟨293612, by rfl⟩ : syracuseStep 391483 = 587225) B587225
theorem B2128187 : Blo 389765 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B10090817 : Blo 389765 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B391559 : Blo 389765 391559 := bstep (se 1 (by rfl) ⟨293669, by rfl⟩ : syracuseStep 391559 = 587339) B587339
theorem B588167 : Blo 389765 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B883079 : Blo 389765 883079 := bstep (se 1 (by rfl) ⟨662309, by rfl⟩ : syracuseStep 883079 = 1324619) B1324619
theorem B391567 : Blo 389765 391567 := bstep (se 1 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 391567 = 587351) B587351
theorem B588203 : Blo 389765 588203 := bstep (se 1 (by rfl) ⟨441152, by rfl⟩ : syracuseStep 588203 = 882305) B882305
theorem B2521529 : Blo 389765 2521529 := bstep (se 2 (by rfl) ⟨945573, by rfl⟩ : syracuseStep 2521529 = 1891147) B1891147
theorem B391611 : Blo 389765 391611 := bstep (se 1 (by rfl) ⟨293708, by rfl⟩ : syracuseStep 391611 = 587417) B587417
theorem B588233 : Blo 389765 588233 := bstep (se 2 (by rfl) ⟨220587, by rfl⟩ : syracuseStep 588233 = 441175) B441175
theorem B391687 : Blo 389765 391687 := bstep (se 1 (by rfl) ⟨293765, by rfl⟩ : syracuseStep 391687 = 587531) B587531
theorem B1112591 : Blo 389765 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B391695 : Blo 389765 391695 := bstep (se 1 (by rfl) ⟨293771, by rfl⟩ : syracuseStep 391695 = 587543) B587543
theorem B391739 : Blo 389765 391739 := bstep (se 1 (by rfl) ⟨293804, by rfl⟩ : syracuseStep 391739 = 587609) B587609
theorem B588347 : Blo 389765 588347 := bstep (se 1 (by rfl) ⟨441260, by rfl⟩ : syracuseStep 588347 = 882521) B882521
theorem B883259 : Blo 389765 883259 := bstep (se 1 (by rfl) ⟨662444, by rfl⟩ : syracuseStep 883259 = 1324889) B1324889
theorem B588407 : Blo 389765 588407 := bstep (se 1 (by rfl) ⟨441305, by rfl⟩ : syracuseStep 588407 = 882611) B882611
theorem B391815 : Blo 389765 391815 := bstep (se 1 (by rfl) ⟨293861, by rfl⟩ : syracuseStep 391815 = 587723) B587723
theorem B391823 : Blo 389765 391823 := bstep (se 1 (by rfl) ⟨293867, by rfl⟩ : syracuseStep 391823 = 587735) B587735
theorem B588431 : Blo 389765 588431 := bstep (se 1 (by rfl) ⟨441323, by rfl⟩ : syracuseStep 588431 = 882647) B882647
theorem B588473 : Blo 389765 588473 := bstep (se 2 (by rfl) ⟨220677, by rfl⟩ : syracuseStep 588473 = 441355) B441355
theorem B883385 : Blo 389765 883385 := bstep (se 2 (by rfl) ⟨331269, by rfl⟩ : syracuseStep 883385 = 662539) B662539
theorem B391867 : Blo 389765 391867 := bstep (se 1 (by rfl) ⟨293900, by rfl⟩ : syracuseStep 391867 = 587801) B587801
theorem B1702657 : Blo 389765 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B391943 : Blo 389765 391943 := bstep (se 1 (by rfl) ⟨293957, by rfl⟩ : syracuseStep 391943 = 587915) B587915
theorem B588551 : Blo 389765 588551 := bstep (se 1 (by rfl) ⟨441413, by rfl⟩ : syracuseStep 588551 = 882827) B882827
theorem B2226959 : Blo 389765 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B391951 : Blo 389765 391951 := bstep (se 1 (by rfl) ⟨293963, by rfl⟩ : syracuseStep 391951 = 587927) B587927
theorem B588587 : Blo 389765 588587 := bstep (se 1 (by rfl) ⟨441440, by rfl⟩ : syracuseStep 588587 = 882881) B882881
theorem B391995 : Blo 389765 391995 := bstep (se 1 (by rfl) ⟨293996, by rfl⟩ : syracuseStep 391995 = 587993) B587993
theorem B588617 : Blo 389765 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B392071 : Blo 389765 392071 := bstep (se 1 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 392071 = 588107) B588107
theorem B392079 : Blo 389765 392079 := bstep (se 1 (by rfl) ⟨294059, by rfl⟩ : syracuseStep 392079 = 588119) B588119
theorem B392123 : Blo 389765 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B588731 : Blo 389765 588731 := bstep (se 1 (by rfl) ⟨441548, by rfl⟩ : syracuseStep 588731 = 883097) B883097
theorem B588791 : Blo 389765 588791 := bstep (se 1 (by rfl) ⟨441593, by rfl⟩ : syracuseStep 588791 = 883187) B883187
theorem B4815877 : Blo 389765 4815877 := bstep (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) B902977
theorem B392199 : Blo 389765 392199 := bstep (se 1 (by rfl) ⟨294149, by rfl⟩ : syracuseStep 392199 = 588299) B588299
theorem B392207 : Blo 389765 392207 := bstep (se 1 (by rfl) ⟨294155, by rfl⟩ : syracuseStep 392207 = 588311) B588311
theorem B588815 : Blo 389765 588815 := bstep (se 1 (by rfl) ⟨441611, by rfl⟩ : syracuseStep 588815 = 883223) B883223
theorem B883727 : Blo 389765 883727 := bstep (se 1 (by rfl) ⟨662795, by rfl⟩ : syracuseStep 883727 = 1325591) B1325591
theorem B883745 : Blo 389765 883745 := bstep (se 2 (by rfl) ⟨331404, by rfl⟩ : syracuseStep 883745 = 662809) B662809
theorem B588857 : Blo 389765 588857 := bstep (se 2 (by rfl) ⟨220821, by rfl⟩ : syracuseStep 588857 = 441643) B441643
theorem B392251 : Blo 389765 392251 := bstep (se 1 (by rfl) ⟨294188, by rfl⟩ : syracuseStep 392251 = 588377) B588377
theorem B1408067 : Blo 389765 1408067 := bstep (se 1 (by rfl) ⟨1056050, by rfl⟩ : syracuseStep 1408067 = 2112101) B2112101
theorem B392327 : Blo 389765 392327 := bstep (se 1 (by rfl) ⟨294245, by rfl⟩ : syracuseStep 392327 = 588491) B588491
theorem B588935 : Blo 389765 588935 := bstep (se 1 (by rfl) ⟨441701, by rfl⟩ : syracuseStep 588935 = 883403) B883403
theorem B392335 : Blo 389765 392335 := bstep (se 1 (by rfl) ⟨294251, by rfl⟩ : syracuseStep 392335 = 588503) B588503
theorem B588971 : Blo 389765 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B392379 : Blo 389765 392379 := bstep (se 1 (by rfl) ⟨294284, by rfl⟩ : syracuseStep 392379 = 588569) B588569
theorem B589001 : Blo 389765 589001 := bstep (se 2 (by rfl) ⟨220875, by rfl⟩ : syracuseStep 589001 = 441751) B441751
theorem B392455 : Blo 389765 392455 := bstep (se 1 (by rfl) ⟨294341, by rfl⟩ : syracuseStep 392455 = 588683) B588683
theorem B392463 : Blo 389765 392463 := bstep (se 1 (by rfl) ⟨294347, by rfl⟩ : syracuseStep 392463 = 588695) B588695
theorem B4226363 : Blo 389765 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B392507 : Blo 389765 392507 := bstep (se 1 (by rfl) ⟨294380, by rfl⟩ : syracuseStep 392507 = 588761) B588761
theorem B589115 : Blo 389765 589115 := bstep (se 1 (by rfl) ⟨441836, by rfl⟩ : syracuseStep 589115 = 883673) B883673
theorem B589175 : Blo 389765 589175 := bstep (se 1 (by rfl) ⟨441881, by rfl⟩ : syracuseStep 589175 = 883763) B883763
theorem B884087 : Blo 389765 884087 := bstep (se 1 (by rfl) ⟨663065, by rfl⟩ : syracuseStep 884087 = 1326131) B1326131
theorem B392583 : Blo 389765 392583 := bstep (se 1 (by rfl) ⟨294437, by rfl⟩ : syracuseStep 392583 = 588875) B588875
theorem B392591 : Blo 389765 392591 := bstep (se 1 (by rfl) ⟨294443, by rfl⟩ : syracuseStep 392591 = 588887) B588887
theorem B589199 : Blo 389765 589199 := bstep (se 1 (by rfl) ⟨441899, by rfl⟩ : syracuseStep 589199 = 883799) B883799
theorem B589241 : Blo 389765 589241 := bstep (se 2 (by rfl) ⟨220965, by rfl⟩ : syracuseStep 589241 = 441931) B441931
theorem B392635 : Blo 389765 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B392711 : Blo 389765 392711 := bstep (se 1 (by rfl) ⟨294533, by rfl⟩ : syracuseStep 392711 = 589067) B589067
theorem B589319 : Blo 389765 589319 := bstep (se 1 (by rfl) ⟨441989, by rfl⟩ : syracuseStep 589319 = 883979) B883979
theorem B392719 : Blo 389765 392719 := bstep (se 1 (by rfl) ⟨294539, by rfl⟩ : syracuseStep 392719 = 589079) B589079
theorem B589355 : Blo 389765 589355 := bstep (se 1 (by rfl) ⟨442016, by rfl⟩ : syracuseStep 589355 = 884033) B884033
theorem B884267 : Blo 389765 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B392763 : Blo 389765 392763 := bstep (se 1 (by rfl) ⟨294572, by rfl⟩ : syracuseStep 392763 = 589145) B589145
theorem B589385 : Blo 389765 589385 := bstep (se 2 (by rfl) ⟨221019, by rfl⟩ : syracuseStep 589385 = 442039) B442039
theorem B392839 : Blo 389765 392839 := bstep (se 1 (by rfl) ⟨294629, by rfl⟩ : syracuseStep 392839 = 589259) B589259
theorem B392847 : Blo 389765 392847 := bstep (se 1 (by rfl) ⟨294635, by rfl⟩ : syracuseStep 392847 = 589271) B589271
theorem B392891 : Blo 389765 392891 := bstep (se 1 (by rfl) ⟨294668, by rfl⟩ : syracuseStep 392891 = 589337) B589337
theorem B589499 : Blo 389765 589499 := bstep (se 1 (by rfl) ⟨442124, by rfl⟩ : syracuseStep 589499 = 884249) B884249
theorem B2391781 : Blo 389765 2391781 := bstep (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) B448459
theorem B589559 : Blo 389765 589559 := bstep (se 1 (by rfl) ⟨442169, by rfl⟩ : syracuseStep 589559 = 884339) B884339
theorem B3768065 : Blo 389765 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B392967 : Blo 389765 392967 := bstep (se 1 (by rfl) ⟨294725, by rfl⟩ : syracuseStep 392967 = 589451) B589451
theorem B392975 : Blo 389765 392975 := bstep (se 1 (by rfl) ⟨294731, by rfl⟩ : syracuseStep 392975 = 589463) B589463
theorem B589583 : Blo 389765 589583 := bstep (se 1 (by rfl) ⟨442187, by rfl⟩ : syracuseStep 589583 = 884375) B884375
theorem B589625 : Blo 389765 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B393019 : Blo 389765 393019 := bstep (se 1 (by rfl) ⟨294764, by rfl⟩ : syracuseStep 393019 = 589529) B589529
theorem B393095 : Blo 389765 393095 := bstep (se 1 (by rfl) ⟨294821, by rfl⟩ : syracuseStep 393095 = 589643) B589643
theorem B589703 : Blo 389765 589703 := bstep (se 1 (by rfl) ⟨442277, by rfl⟩ : syracuseStep 589703 = 884555) B884555
theorem B393103 : Blo 389765 393103 := bstep (se 1 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 393103 = 589655) B589655
theorem B1114003 : Blo 389765 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B884627 : Blo 389765 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B4751257 : Blo 389765 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B589739 : Blo 389765 589739 := bstep (se 1 (by rfl) ⟨442304, by rfl⟩ : syracuseStep 589739 = 884609) B884609
theorem B393147 : Blo 389765 393147 := bstep (se 1 (by rfl) ⟨294860, by rfl⟩ : syracuseStep 393147 = 589721) B589721
theorem B589769 : Blo 389765 589769 := bstep (se 2 (by rfl) ⟨221163, by rfl⟩ : syracuseStep 589769 = 442327) B442327
theorem B884681 : Blo 389765 884681 := bstep (se 2 (by rfl) ⟨331755, by rfl⟩ : syracuseStep 884681 = 663511) B663511
theorem B557047 : Blo 389765 557047 := bstep (se 1 (by rfl) ⟨417785, by rfl⟩ : syracuseStep 557047 = 835571) B835571
theorem B393255 : Blo 389765 393255 := bstep (se 1 (by rfl) ⟨294941, by rfl⟩ : syracuseStep 393255 = 589883) B589883
theorem B393295 : Blo 389765 393295 := bstep (se 1 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 393295 = 589943) B589943
theorem B393311 : Blo 389765 393311 := bstep (se 1 (by rfl) ⟨294983, by rfl⟩ : syracuseStep 393311 = 589967) B589967
theorem B393339 : Blo 389765 393339 := bstep (se 1 (by rfl) ⟨295004, by rfl⟩ : syracuseStep 393339 = 590009) B590009
theorem B393391 : Blo 389765 393391 := bstep (se 1 (by rfl) ⟨295043, by rfl⟩ : syracuseStep 393391 = 590087) B590087
theorem B393415 : Blo 389765 393415 := bstep (se 1 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 393415 = 590123) B590123
theorem B393435 : Blo 389765 393435 := bstep (se 1 (by rfl) ⟨295076, by rfl⟩ : syracuseStep 393435 = 590153) B590153
theorem B393511 : Blo 389765 393511 := bstep (se 1 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 393511 = 590267) B590267
theorem B393551 : Blo 389765 393551 := bstep (se 1 (by rfl) ⟨295163, by rfl⟩ : syracuseStep 393551 = 590327) B590327
theorem B393567 : Blo 389765 393567 := bstep (se 1 (by rfl) ⟨295175, by rfl⟩ : syracuseStep 393567 = 590351) B590351
theorem B393595 : Blo 389765 393595 := bstep (se 1 (by rfl) ⟨295196, by rfl⟩ : syracuseStep 393595 = 590393) B590393
theorem B590255 : Blo 389765 590255 := bstep (se 1 (by rfl) ⟨442691, by rfl⟩ : syracuseStep 590255 = 885383) B885383
theorem B393647 : Blo 389765 393647 := bstep (se 1 (by rfl) ⟨295235, by rfl⟩ : syracuseStep 393647 = 590471) B590471
theorem B393671 : Blo 389765 393671 := bstep (se 1 (by rfl) ⟨295253, by rfl⟩ : syracuseStep 393671 = 590507) B590507
theorem B393691 : Blo 389765 393691 := bstep (se 1 (by rfl) ⟨295268, by rfl⟩ : syracuseStep 393691 = 590537) B590537
theorem B885257 : Blo 389765 885257 := bstep (se 2 (by rfl) ⟨331971, by rfl⟩ : syracuseStep 885257 = 663943) B663943
theorem B590345 : Blo 389765 590345 := bstep (se 2 (by rfl) ⟨221379, by rfl⟩ : syracuseStep 590345 = 442759) B442759
theorem B590375 : Blo 389765 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B590459 : Blo 389765 590459 := bstep (se 1 (by rfl) ⟨442844, by rfl⟩ : syracuseStep 590459 = 885689) B885689
theorem B4981421 : Blo 389765 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1114823 : Blo 389765 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B590585 : Blo 389765 590585 := bstep (se 2 (by rfl) ⟨221469, by rfl⟩ : syracuseStep 590585 = 442939) B442939
theorem B885599 : Blo 389765 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B2818961 : Blo 389765 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B885779 : Blo 389765 885779 := bstep (se 1 (by rfl) ⟨664334, by rfl⟩ : syracuseStep 885779 = 1328669) B1328669
theorem B1672271 : Blo 389765 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B2229443 : Blo 389765 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B1410547 : Blo 389765 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B1672919 : Blo 389765 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B6752089 : Blo 389765 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B2295647 : Blo 389765 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B952339 : Blo 389765 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B3770525 : Blo 389765 3770525 := bstep (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) B1413947
theorem B13502771 : Blo 389765 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B395695 : Blo 389765 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B625115 : Blo 389765 625115 := bstep (se 1 (by rfl) ⟨468836, by rfl⟩ : syracuseStep 625115 = 937673) B937673
theorem B657929 : Blo 389765 657929 := bstep (se 2 (by rfl) ⟨246723, by rfl⟩ : syracuseStep 657929 = 493447) B493447
theorem B658091 : Blo 389765 658091 := bstep (se 1 (by rfl) ⟨493568, by rfl⟩ : syracuseStep 658091 = 987137) B987137
theorem B5376689 : Blo 389765 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B72354707 : Blo 389765 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B2985011 : Blo 389765 2985011 := bstep (se 1 (by rfl) ⟨2238758, by rfl⟩ : syracuseStep 2985011 = 4477517) B4477517
theorem B658489 : Blo 389765 658489 := bstep (se 2 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 658489 = 493867) B493867
theorem B658631 : Blo 389765 658631 := bstep (se 1 (by rfl) ⟨493973, by rfl⟩ : syracuseStep 658631 = 987947) B987947
theorem B756985 : Blo 389765 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B658793 : Blo 389765 658793 := bstep (se 2 (by rfl) ⟨247047, by rfl⟩ : syracuseStep 658793 = 494095) B494095
theorem B626063 : Blo 389765 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B560567 : Blo 389765 560567 := bstep (se 1 (by rfl) ⟨420425, by rfl⟩ : syracuseStep 560567 = 840851) B840851
theorem B495067 : Blo 389765 495067 := bstep (se 1 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 495067 = 742601) B742601
theorem B3575335 : Blo 389765 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B396895 : Blo 389765 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B659191 : Blo 389765 659191 := bstep (se 1 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 659191 = 988787) B988787
theorem B2232107 : Blo 389765 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B986975 : Blo 389765 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B659387 : Blo 389765 659387 := bstep (se 1 (by rfl) ⟨494540, by rfl⟩ : syracuseStep 659387 = 989081) B989081
theorem B659495 : Blo 389765 659495 := bstep (se 1 (by rfl) ⟨494621, by rfl⟩ : syracuseStep 659495 = 989243) B989243
theorem B1675379 : Blo 389765 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B626935 : Blo 389765 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B659785 : Blo 389765 659785 := bstep (se 2 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 659785 = 494839) B494839
theorem B659819 : Blo 389765 659819 := bstep (se 1 (by rfl) ⟨494864, by rfl⟩ : syracuseStep 659819 = 989729) B989729
theorem B987673 : Blo 389765 987673 := bstep (se 2 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 987673 = 740755) B740755
theorem B1675961 : Blo 389765 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B660217 : Blo 389765 660217 := bstep (se 2 (by rfl) ⟨247581, by rfl⟩ : syracuseStep 660217 = 495163) B495163
theorem B3347203 : Blo 389765 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B2003741 : Blo 389765 2003741 := bstep (se 3 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 2003741 = 751403) B751403
theorem B987977 : Blo 389765 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B627563 : Blo 389765 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B1250167 : Blo 389765 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B660487 : Blo 389765 660487 := bstep (se 1 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 660487 = 990731) B990731
theorem B594953 : Blo 389765 594953 := bstep (se 2 (by rfl) ⟨223107, by rfl⟩ : syracuseStep 594953 = 446215) B446215
theorem B1316087 : Blo 389765 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B398687 : Blo 389765 398687 := bstep (se 1 (by rfl) ⟨299015, by rfl⟩ : syracuseStep 398687 = 598031) B598031
theorem B660919 : Blo 389765 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B1316411 : Blo 389765 1316411 := bstep (se 1 (by rfl) ⟨987308, by rfl⟩ : syracuseStep 1316411 = 1974617) B1974617
theorem B661115 : Blo 389765 661115 := bstep (se 1 (by rfl) ⟨495836, by rfl⟩ : syracuseStep 661115 = 991673) B991673
theorem B1414871 : Blo 389765 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B1480477 : Blo 389765 1480477 := bstep (se 3 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 1480477 = 555179) B555179
theorem B1251101 : Blo 389765 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B1316681 : Blo 389765 1316681 := bstep (se 2 (by rfl) ⟨493755, by rfl⟩ : syracuseStep 1316681 = 987511) B987511
theorem B989111 : Blo 389765 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B661513 : Blo 389765 661513 := bstep (se 2 (by rfl) ⟨248067, by rfl⟩ : syracuseStep 661513 = 496135) B496135
theorem B661675 : Blo 389765 661675 := bstep (se 1 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 661675 = 992513) B992513
theorem B5347565 : Blo 389765 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B628985 : Blo 389765 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B1120655 : Blo 389765 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B661979 : Blo 389765 661979 := bstep (se 1 (by rfl) ⟨496484, by rfl⟩ : syracuseStep 661979 = 992969) B992969
theorem B662215 : Blo 389765 662215 := bstep (se 1 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 662215 = 993323) B993323
theorem B662377 : Blo 389765 662377 := bstep (se 2 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 662377 = 496783) B496783
theorem B1317815 : Blo 389765 1317815 := bstep (se 1 (by rfl) ⟨988361, by rfl⟩ : syracuseStep 1317815 = 1976723) B1976723
theorem B2497463 : Blo 389765 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B3611621 : Blo 389765 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B990215 : Blo 389765 990215 := bstep (se 1 (by rfl) ⟨742661, by rfl⟩ : syracuseStep 990215 = 1485323) B1485323
theorem B990265 : Blo 389765 990265 := bstep (se 2 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 990265 = 742699) B742699
theorem B1186987 : Blo 389765 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B629959 : Blo 389765 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B793847 : Blo 389765 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B990569 : Blo 389765 990569 := bstep (se 2 (by rfl) ⟨371463, by rfl⟩ : syracuseStep 990569 = 742927) B742927
theorem B662971 : Blo 389765 662971 := bstep (se 1 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 662971 = 994457) B994457
theorem B1318409 : Blo 389765 1318409 := bstep (se 2 (by rfl) ⟨494403, by rfl⟩ : syracuseStep 1318409 = 988807) B988807
theorem B663079 : Blo 389765 663079 := bstep (se 1 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 663079 = 994619) B994619
theorem B663403 : Blo 389765 663403 := bstep (se 1 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 663403 = 995105) B995105
theorem B1417121 : Blo 389765 1417121 := bstep (se 2 (by rfl) ⟨531420, by rfl⟩ : syracuseStep 1417121 = 1062841) B1062841
theorem B2236733 : Blo 389765 2236733 := bstep (se 3 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 2236733 = 838775) B838775
theorem B2498921 : Blo 389765 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1319273 : Blo 389765 1319273 := bstep (se 2 (by rfl) ⟨494727, by rfl⟩ : syracuseStep 1319273 = 989455) B989455
theorem B795055 : Blo 389765 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B1417753 : Blo 389765 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B1909433 : Blo 389765 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B2499331 : Blo 389765 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B664463 : Blo 389765 664463 := bstep (se 1 (by rfl) ⟨498347, by rfl⟩ : syracuseStep 664463 = 996695) B996695
theorem B1254305 : Blo 389765 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B1319867 : Blo 389765 1319867 := bstep (se 1 (by rfl) ⟨989900, by rfl⟩ : syracuseStep 1319867 = 1979801) B1979801
theorem B2270209 : Blo 389765 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B1058039 : Blo 389765 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B2237939 : Blo 389765 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B992807 : Blo 389765 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B1418791 : Blo 389765 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B6727211 : Blo 389765 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B1681019 : Blo 389765 1681019 := bstep (se 1 (by rfl) ⟨1260764, by rfl⟩ : syracuseStep 1681019 = 2521529) B2521529
theorem B1484639 : Blo 389765 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B993131 : Blo 389765 993131 := bstep (se 1 (by rfl) ⟨744848, by rfl⟩ : syracuseStep 993131 = 1489697) B1489697
theorem B2107255 : Blo 389765 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B2500561 : Blo 389765 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B5023781 : Blo 389765 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B3189041 : Blo 389765 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B797033 : Blo 389765 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B993779 : Blo 389765 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B1485337 : Blo 389765 1485337 := bstep (se 2 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 1485337 = 1114003) B1114003
theorem B6335009 : Blo 389765 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B1321595 : Blo 389765 1321595 := bstep (se 1 (by rfl) ⟨991196, by rfl⟩ : syracuseStep 1321595 = 1982393) B1982393
theorem B993991 : Blo 389765 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B1321757 : Blo 389765 1321757 := bstep (se 3 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 1321757 = 495659) B495659
theorem B1485611 : Blo 389765 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B1583945 : Blo 389765 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B1485641 : Blo 389765 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B469855 : Blo 389765 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B1780663 : Blo 389765 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B1256791 : Blo 389765 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B2010511 : Blo 389765 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B1322459 : Blo 389765 1322459 := bstep (se 1 (by rfl) ⟨991844, by rfl⟩ : syracuseStep 1322459 = 1983689) B1983689
theorem B994913 : Blo 389765 994913 := bstep (se 2 (by rfl) ⟨373092, by rfl⟩ : syracuseStep 994913 = 746185) B746185
theorem B2829971 : Blo 389765 2829971 := bstep (se 1 (by rfl) ⟨2122478, by rfl⟩ : syracuseStep 2829971 = 4244957) B4244957
theorem B4009661 : Blo 389765 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B6368989 : Blo 389765 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B1126457 : Blo 389765 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B1323161 : Blo 389765 1323161 := bstep (se 2 (by rfl) ⟨496185, by rfl⟩ : syracuseStep 1323161 = 992371) B992371
theorem B3027287 : Blo 389765 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B2240855 : Blo 389765 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B2470297 : Blo 389765 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B766561 : Blo 389765 766561 := bstep (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) B574921
theorem B438907 : Blo 389765 438907 := bstep (se 1 (by rfl) ⟨329180, by rfl⟩ : syracuseStep 438907 = 658361) B658361
theorem B996371 : Blo 389765 996371 := bstep (se 1 (by rfl) ⟨747278, by rfl⟩ : syracuseStep 996371 = 1494557) B1494557
theorem B439375 : Blo 389765 439375 := bstep (se 1 (by rfl) ⟨329531, by rfl⟩ : syracuseStep 439375 = 659063) B659063
theorem B38810765 : Blo 389765 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B1979639 : Blo 389765 1979639 := bstep (se 1 (by rfl) ⟨1484729, by rfl⟩ : syracuseStep 1979639 = 2969459) B2969459
theorem B1324349 : Blo 389765 1324349 := bstep (se 3 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 1324349 = 496631) B496631
theorem B1488253 : Blo 389765 1488253 := bstep (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) B558095
theorem B439771 : Blo 389765 439771 := bstep (se 1 (by rfl) ⟨329828, by rfl⟩ : syracuseStep 439771 = 659657) B659657
theorem B3815111 : Blo 389765 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B1980125 : Blo 389765 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B6371065 : Blo 389765 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B5748515 : Blo 389765 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B3192671 : Blo 389765 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B440239 : Blo 389765 440239 := bstep (se 1 (by rfl) ⟨330179, by rfl⟩ : syracuseStep 440239 = 660359) B660359
theorem B5027777 : Blo 389765 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1128455 : Blo 389765 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B1325213 : Blo 389765 1325213 := bstep (se 3 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 1325213 = 496955) B496955
theorem B440671 : Blo 389765 440671 := bstep (se 1 (by rfl) ⟨330503, by rfl⟩ : syracuseStep 440671 = 661007) B661007
theorem B833897 : Blo 389765 833897 := bstep (se 2 (by rfl) ⟨312711, by rfl⟩ : syracuseStep 833897 = 625423) B625423
theorem B1325753 : Blo 389765 1325753 := bstep (se 2 (by rfl) ⟨497157, by rfl⟩ : syracuseStep 1325753 = 994315) B994315
theorem B441031 : Blo 389765 441031 := bstep (se 1 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 441031 = 661547) B661547
theorem B1260623 : Blo 389765 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B2964599 : Blo 389765 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B1326347 : Blo 389765 1326347 := bstep (se 1 (by rfl) ⟨994760, by rfl⟩ : syracuseStep 1326347 = 1989521) B1989521
theorem B1326617 : Blo 389765 1326617 := bstep (se 2 (by rfl) ⟨497481, by rfl⟩ : syracuseStep 1326617 = 994963) B994963
theorem B1490471 : Blo 389765 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B441895 : Blo 389765 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B1195735 : Blo 389765 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B704351 : Blo 389765 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B10141625 : Blo 389765 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B1589249 : Blo 389765 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B1491443 : Blo 389765 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B6046325 : Blo 389765 6046325 := bstep (se 5 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 6046325 = 566843) B566843
theorem B1327751 : Blo 389765 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B1491641 : Blo 389765 1491641 := bstep (se 2 (by rfl) ⟨559365, by rfl⟩ : syracuseStep 1491641 = 1118731) B1118731
theorem B1327805 : Blo 389765 1327805 := bstep (se 3 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 1327805 = 497927) B497927
theorem B1491655 : Blo 389765 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B705353 : Blo 389765 705353 := bstep (se 2 (by rfl) ⟨264507, by rfl⟩ : syracuseStep 705353 = 529015) B529015
theorem B1327967 : Blo 389765 1327967 := bstep (se 1 (by rfl) ⟨995975, by rfl⟩ : syracuseStep 1327967 = 1991951) B1991951
theorem B2016175 : Blo 389765 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B1328129 : Blo 389765 1328129 := bstep (se 2 (by rfl) ⟨498048, by rfl⟩ : syracuseStep 1328129 = 996097) B996097
theorem B3163481 : Blo 389765 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B3556723 : Blo 389765 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B5031467 : Blo 389765 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B3163735 : Blo 389765 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B1492627 : Blo 389765 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B1328939 : Blo 389765 1328939 := bstep (se 1 (by rfl) ⟨996704, by rfl⟩ : syracuseStep 1328939 = 1993409) B1993409
theorem B6637571 : Blo 389765 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B838031 : Blo 389765 838031 := bstep (se 1 (by rfl) ⟨628523, by rfl⟩ : syracuseStep 838031 = 1257047) B1257047
theorem B740011 : Blo 389765 740011 := bstep (se 1 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 740011 = 1110017) B1110017
theorem B740087 : Blo 389765 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B1985309 : Blo 389765 1985309 := bstep (se 3 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 1985309 = 744491) B744491
theorem B1526647 : Blo 389765 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B740315 : Blo 389765 740315 := bstep (se 1 (by rfl) ⟨555236, by rfl⟩ : syracuseStep 740315 = 1110473) B1110473
theorem B1494359 : Blo 389765 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B2510585 : Blo 389765 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B741575 : Blo 389765 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B5001533 : Blo 389765 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B741727 : Blo 389765 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B938711 : Blo 389765 938711 := bstep (se 1 (by rfl) ⟨704033, by rfl⟩ : syracuseStep 938711 = 1408067) B1408067
theorem B2512043 : Blo 389765 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B2970917 : Blo 389765 2970917 := bstep (se 4 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 2970917 = 557047) B557047
theorem B4773437 : Blo 389765 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B1890013 : Blo 389765 1890013 := bstep (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) B708755
theorem B36591587 : Blo 389765 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1005625 : Blo 389765 1005625 := bstep (se 2 (by rfl) ⟨377109, by rfl⟩ : syracuseStep 1005625 = 754219) B754219
theorem B4773977 : Blo 389765 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B743671 : Blo 389765 743671 := bstep (se 1 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 743671 = 1115507) B1115507
theorem B2677043 : Blo 389765 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1890647 : Blo 389765 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B743899 : Blo 389765 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B743975 : Blo 389765 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B744059 : Blo 389765 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B1989683 : Blo 389765 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B744545 : Blo 389765 744545 := bstep (se 2 (by rfl) ⟨279204, by rfl⟩ : syracuseStep 744545 = 558409) B558409
theorem B4742489 : Blo 389765 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B941555 : Blo 389765 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B19259201 : Blo 389765 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B942479 : Blo 389765 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B746003 : Blo 389765 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B1991303 : Blo 389765 1991303 := bstep (se 1 (by rfl) ⟨1493477, by rfl⟩ : syracuseStep 1991303 = 2986955) B2986955
theorem B877499 : Blo 389765 877499 := bstep (se 1 (by rfl) ⟨658124, by rfl⟩ : syracuseStep 877499 = 1316249) B1316249
theorem B12248113 : Blo 389765 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B877625 : Blo 389765 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B15262937 : Blo 389765 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B877967 : Blo 389765 877967 := bstep (se 1 (by rfl) ⟨658475, by rfl⟩ : syracuseStep 877967 = 1316951) B1316951
theorem B1533421 : Blo 389765 1533421 := bstep (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) B575033
theorem B3761761 : Blo 389765 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B878291 : Blo 389765 878291 := bstep (se 1 (by rfl) ⟨658718, by rfl⟩ : syracuseStep 878291 = 1317437) B1317437
theorem B747407 : Blo 389765 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B1992761 : Blo 389765 1992761 := bstep (se 2 (by rfl) ⟨747285, by rfl⟩ : syracuseStep 1992761 = 1494571) B1494571
theorem B10741997 : Blo 389765 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B2812441 : Blo 389765 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B879227 : Blo 389765 879227 := bstep (se 1 (by rfl) ⟨659420, by rfl⟩ : syracuseStep 879227 = 1318841) B1318841
theorem B879353 : Blo 389765 879353 := bstep (se 2 (by rfl) ⟨329757, by rfl⟩ : syracuseStep 879353 = 659515) B659515
theorem B879623 : Blo 389765 879623 := bstep (se 1 (by rfl) ⟨659717, by rfl⟩ : syracuseStep 879623 = 1319435) B1319435
theorem B584783 : Blo 389765 584783 := bstep (se 1 (by rfl) ⟨438587, by rfl⟩ : syracuseStep 584783 = 877175) B877175
theorem B879695 : Blo 389765 879695 := bstep (se 1 (by rfl) ⟨659771, by rfl⟩ : syracuseStep 879695 = 1319543) B1319543
theorem B584903 : Blo 389765 584903 := bstep (se 1 (by rfl) ⟨438677, by rfl⟩ : syracuseStep 584903 = 877355) B877355
theorem B585065 : Blo 389765 585065 := bstep (se 2 (by rfl) ⟨219399, by rfl⟩ : syracuseStep 585065 = 438799) B438799
theorem B585143 : Blo 389765 585143 := bstep (se 1 (by rfl) ⟨438857, by rfl⟩ : syracuseStep 585143 = 877715) B877715
theorem B585179 : Blo 389765 585179 := bstep (se 1 (by rfl) ⟨438884, by rfl⟩ : syracuseStep 585179 = 877769) B877769
theorem B880091 : Blo 389765 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B585647 : Blo 389765 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B880559 : Blo 389765 880559 := bstep (se 1 (by rfl) ⟨660419, by rfl⟩ : syracuseStep 880559 = 1320839) B1320839
theorem B2977721 : Blo 389765 2977721 := bstep (se 2 (by rfl) ⟨1116645, by rfl⟩ : syracuseStep 2977721 = 2233291) B2233291
theorem B585737 : Blo 389765 585737 := bstep (se 2 (by rfl) ⟨219651, by rfl⟩ : syracuseStep 585737 = 439303) B439303
theorem B585767 : Blo 389765 585767 := bstep (se 1 (by rfl) ⟨439325, by rfl⟩ : syracuseStep 585767 = 878651) B878651
theorem B2125939 : Blo 389765 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B585851 : Blo 389765 585851 := bstep (se 1 (by rfl) ⟨439388, by rfl⟩ : syracuseStep 585851 = 878777) B878777
theorem B880811 : Blo 389765 880811 := bstep (se 1 (by rfl) ⟨660608, by rfl⟩ : syracuseStep 880811 = 1321217) B1321217
theorem B585977 : Blo 389765 585977 := bstep (se 2 (by rfl) ⟨219741, by rfl⟩ : syracuseStep 585977 = 439483) B439483
theorem B2814259 : Blo 389765 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B586079 : Blo 389765 586079 := bstep (se 1 (by rfl) ⟨439559, by rfl⟩ : syracuseStep 586079 = 879119) B879119
theorem B586091 : Blo 389765 586091 := bstep (se 1 (by rfl) ⟨439568, by rfl⟩ : syracuseStep 586091 = 879137) B879137
theorem B586319 : Blo 389765 586319 := bstep (se 1 (by rfl) ⟨439739, by rfl⟩ : syracuseStep 586319 = 879479) B879479
theorem B389807 : Blo 389765 389807 := bstep (se 1 (by rfl) ⟨292355, by rfl⟩ : syracuseStep 389807 = 584711) B584711
theorem B389831 : Blo 389765 389831 := bstep (se 1 (by rfl) ⟨292373, by rfl⟩ : syracuseStep 389831 = 584747) B584747
theorem B586439 : Blo 389765 586439 := bstep (se 1 (by rfl) ⟨439829, by rfl⟩ : syracuseStep 586439 = 879659) B879659
theorem B881351 : Blo 389765 881351 := bstep (se 1 (by rfl) ⟨661013, by rfl⟩ : syracuseStep 881351 = 1322027) B1322027
theorem B389851 : Blo 389765 389851 := bstep (se 1 (by rfl) ⟨292388, by rfl⟩ : syracuseStep 389851 = 584777) B584777
theorem B389927 : Blo 389765 389927 := bstep (se 1 (by rfl) ⟨292445, by rfl⟩ : syracuseStep 389927 = 584891) B584891
theorem B389967 : Blo 389765 389967 := bstep (se 1 (by rfl) ⟨292475, by rfl⟩ : syracuseStep 389967 = 584951) B584951
theorem B389983 : Blo 389765 389983 := bstep (se 1 (by rfl) ⟨292487, by rfl⟩ : syracuseStep 389983 = 584975) B584975
theorem B586601 : Blo 389765 586601 := bstep (se 2 (by rfl) ⟨219975, by rfl⟩ : syracuseStep 586601 = 439951) B439951
theorem B390011 : Blo 389765 390011 := bstep (se 1 (by rfl) ⟨292508, by rfl⟩ : syracuseStep 390011 = 585017) B585017
theorem B390063 : Blo 389765 390063 := bstep (se 1 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 390063 = 585095) B585095
theorem B586679 : Blo 389765 586679 := bstep (se 1 (by rfl) ⟨440009, by rfl⟩ : syracuseStep 586679 = 880019) B880019
theorem B390087 : Blo 389765 390087 := bstep (se 1 (by rfl) ⟨292565, by rfl⟩ : syracuseStep 390087 = 585131) B585131
theorem B390107 : Blo 389765 390107 := bstep (se 1 (by rfl) ⟨292580, by rfl⟩ : syracuseStep 390107 = 585161) B585161
theorem B586715 : Blo 389765 586715 := bstep (se 1 (by rfl) ⟨440036, by rfl⟩ : syracuseStep 586715 = 880073) B880073
theorem B390183 : Blo 389765 390183 := bstep (se 1 (by rfl) ⟨292637, by rfl⟩ : syracuseStep 390183 = 585275) B585275
theorem B390223 : Blo 389765 390223 := bstep (se 1 (by rfl) ⟨292667, by rfl⟩ : syracuseStep 390223 = 585335) B585335
theorem B2520143 : Blo 389765 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B390239 : Blo 389765 390239 := bstep (se 1 (by rfl) ⟨292679, by rfl⟩ : syracuseStep 390239 = 585359) B585359
theorem B390267 : Blo 389765 390267 := bstep (se 1 (by rfl) ⟨292700, by rfl⟩ : syracuseStep 390267 = 585401) B585401
theorem B390319 : Blo 389765 390319 := bstep (se 1 (by rfl) ⟨292739, by rfl⟩ : syracuseStep 390319 = 585479) B585479
theorem B390343 : Blo 389765 390343 := bstep (se 1 (by rfl) ⟨292757, by rfl⟩ : syracuseStep 390343 = 585515) B585515
theorem B390363 : Blo 389765 390363 := bstep (se 1 (by rfl) ⟨292772, by rfl⟩ : syracuseStep 390363 = 585545) B585545
theorem B390439 : Blo 389765 390439 := bstep (se 1 (by rfl) ⟨292829, by rfl⟩ : syracuseStep 390439 = 585659) B585659
theorem B390479 : Blo 389765 390479 := bstep (se 1 (by rfl) ⟨292859, by rfl⟩ : syracuseStep 390479 = 585719) B585719
theorem B390495 : Blo 389765 390495 := bstep (se 1 (by rfl) ⟨292871, by rfl⟩ : syracuseStep 390495 = 585743) B585743
theorem B15037811 : Blo 389765 15037811 := bstep (se 1 (by rfl) ⟨11278358, by rfl⟩ : syracuseStep 15037811 = 22556717) B22556717
theorem B390523 : Blo 389765 390523 := bstep (se 1 (by rfl) ⟨292892, by rfl⟩ : syracuseStep 390523 = 585785) B585785
theorem B390575 : Blo 389765 390575 := bstep (se 1 (by rfl) ⟨292931, by rfl⟩ : syracuseStep 390575 = 585863) B585863
theorem B587183 : Blo 389765 587183 := bstep (se 1 (by rfl) ⟨440387, by rfl⟩ : syracuseStep 587183 = 880775) B880775
theorem B390599 : Blo 389765 390599 := bstep (se 1 (by rfl) ⟨292949, by rfl⟩ : syracuseStep 390599 = 585899) B585899
theorem B2618825 : Blo 389765 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B390619 : Blo 389765 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B587273 : Blo 389765 587273 := bstep (se 2 (by rfl) ⟨220227, by rfl⟩ : syracuseStep 587273 = 440455) B440455
theorem B390695 : Blo 389765 390695 := bstep (se 1 (by rfl) ⟨293021, by rfl⟩ : syracuseStep 390695 = 586043) B586043
theorem B587303 : Blo 389765 587303 := bstep (se 1 (by rfl) ⟨440477, by rfl⟩ : syracuseStep 587303 = 880955) B880955
theorem B882215 : Blo 389765 882215 := bstep (se 1 (by rfl) ⟨661661, by rfl⟩ : syracuseStep 882215 = 1323323) B1323323
theorem B390735 : Blo 389765 390735 := bstep (se 1 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 390735 = 586103) B586103
theorem B390751 : Blo 389765 390751 := bstep (se 1 (by rfl) ⟨293063, by rfl⟩ : syracuseStep 390751 = 586127) B586127
theorem B390779 : Blo 389765 390779 := bstep (se 1 (by rfl) ⟨293084, by rfl⟩ : syracuseStep 390779 = 586169) B586169
theorem B587387 : Blo 389765 587387 := bstep (se 1 (by rfl) ⟨440540, by rfl⟩ : syracuseStep 587387 = 881081) B881081
theorem B390831 : Blo 389765 390831 := bstep (se 1 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 390831 = 586247) B586247
theorem B390855 : Blo 389765 390855 := bstep (se 1 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 390855 = 586283) B586283
theorem B390875 : Blo 389765 390875 := bstep (se 1 (by rfl) ⟨293156, by rfl⟩ : syracuseStep 390875 = 586313) B586313
theorem B587513 : Blo 389765 587513 := bstep (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) B440635
theorem B390951 : Blo 389765 390951 := bstep (se 1 (by rfl) ⟨293213, by rfl⟩ : syracuseStep 390951 = 586427) B586427
theorem B390991 : Blo 389765 390991 := bstep (se 1 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 390991 = 586487) B586487
theorem B391007 : Blo 389765 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B587615 : Blo 389765 587615 := bstep (se 1 (by rfl) ⟨440711, by rfl⟩ : syracuseStep 587615 = 881423) B881423
theorem B587627 : Blo 389765 587627 := bstep (se 1 (by rfl) ⟨440720, by rfl⟩ : syracuseStep 587627 = 881441) B881441
theorem B882539 : Blo 389765 882539 := bstep (se 1 (by rfl) ⟨661904, by rfl⟩ : syracuseStep 882539 = 1323809) B1323809
theorem B391035 : Blo 389765 391035 := bstep (se 1 (by rfl) ⟨293276, by rfl⟩ : syracuseStep 391035 = 586553) B586553
theorem B882593 : Blo 389765 882593 := bstep (se 2 (by rfl) ⟨330972, by rfl⟩ : syracuseStep 882593 = 661945) B661945
theorem B391087 : Blo 389765 391087 := bstep (se 1 (by rfl) ⟨293315, by rfl⟩ : syracuseStep 391087 = 586631) B586631
theorem B391111 : Blo 389765 391111 := bstep (se 1 (by rfl) ⟨293333, by rfl⟩ : syracuseStep 391111 = 586667) B586667
theorem B391131 : Blo 389765 391131 := bstep (se 1 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 391131 = 586697) B586697
theorem B391207 : Blo 389765 391207 := bstep (se 1 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 391207 = 586811) B586811
theorem B391247 : Blo 389765 391247 := bstep (se 1 (by rfl) ⟨293435, by rfl⟩ : syracuseStep 391247 = 586871) B586871
theorem B587855 : Blo 389765 587855 := bstep (se 1 (by rfl) ⟨440891, by rfl⟩ : syracuseStep 587855 = 881783) B881783
theorem B391263 : Blo 389765 391263 := bstep (se 1 (by rfl) ⟨293447, by rfl⟩ : syracuseStep 391263 = 586895) B586895
theorem B391291 : Blo 389765 391291 := bstep (se 1 (by rfl) ⟨293468, by rfl⟩ : syracuseStep 391291 = 586937) B586937
theorem B391343 : Blo 389765 391343 := bstep (se 1 (by rfl) ⟨293507, by rfl⟩ : syracuseStep 391343 = 587015) B587015
theorem B391367 : Blo 389765 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B587975 : Blo 389765 587975 := bstep (se 1 (by rfl) ⟨440981, by rfl⟩ : syracuseStep 587975 = 881963) B881963
theorem B391387 : Blo 389765 391387 := bstep (se 1 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 391387 = 587081) B587081
theorem B882935 : Blo 389765 882935 := bstep (se 1 (by rfl) ⟨662201, by rfl⟩ : syracuseStep 882935 = 1324403) B1324403
theorem B1341707 : Blo 389765 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B391463 : Blo 389765 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B391503 : Blo 389765 391503 := bstep (se 1 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 391503 = 587255) B587255
theorem B391519 : Blo 389765 391519 := bstep (se 1 (by rfl) ⟨293639, by rfl⟩ : syracuseStep 391519 = 587279) B587279
theorem B588137 : Blo 389765 588137 := bstep (se 2 (by rfl) ⟨220551, by rfl⟩ : syracuseStep 588137 = 441103) B441103
theorem B391547 : Blo 389765 391547 := bstep (se 1 (by rfl) ⟨293660, by rfl⟩ : syracuseStep 391547 = 587321) B587321
theorem B391599 : Blo 389765 391599 := bstep (se 1 (by rfl) ⟨293699, by rfl⟩ : syracuseStep 391599 = 587399) B587399
theorem B588215 : Blo 389765 588215 := bstep (se 1 (by rfl) ⟨441161, by rfl⟩ : syracuseStep 588215 = 882323) B882323
theorem B391623 : Blo 389765 391623 := bstep (se 1 (by rfl) ⟨293717, by rfl⟩ : syracuseStep 391623 = 587435) B587435
theorem B391643 : Blo 389765 391643 := bstep (se 1 (by rfl) ⟨293732, by rfl⟩ : syracuseStep 391643 = 587465) B587465
theorem B588251 : Blo 389765 588251 := bstep (se 1 (by rfl) ⟨441188, by rfl⟩ : syracuseStep 588251 = 882377) B882377
theorem B391719 : Blo 389765 391719 := bstep (se 1 (by rfl) ⟨293789, by rfl⟩ : syracuseStep 391719 = 587579) B587579
theorem B391759 : Blo 389765 391759 := bstep (se 1 (by rfl) ⟨293819, by rfl⟩ : syracuseStep 391759 = 587639) B587639
theorem B391775 : Blo 389765 391775 := bstep (se 1 (by rfl) ⟨293831, by rfl⟩ : syracuseStep 391775 = 587663) B587663
theorem B391803 : Blo 389765 391803 := bstep (se 1 (by rfl) ⟨293852, by rfl⟩ : syracuseStep 391803 = 587705) B587705
theorem B391855 : Blo 389765 391855 := bstep (se 1 (by rfl) ⟨293891, by rfl⟩ : syracuseStep 391855 = 587783) B587783
theorem B6421169 : Blo 389765 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B391879 : Blo 389765 391879 := bstep (se 1 (by rfl) ⟨293909, by rfl⟩ : syracuseStep 391879 = 587819) B587819
theorem B391899 : Blo 389765 391899 := bstep (se 1 (by rfl) ⟨293924, by rfl⟩ : syracuseStep 391899 = 587849) B587849
theorem B2980637 : Blo 389765 2980637 := bstep (se 3 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 2980637 = 1117739) B1117739
theorem B391975 : Blo 389765 391975 := bstep (se 1 (by rfl) ⟨293981, by rfl⟩ : syracuseStep 391975 = 587963) B587963
theorem B883529 : Blo 389765 883529 := bstep (se 2 (by rfl) ⟨331323, by rfl⟩ : syracuseStep 883529 = 662647) B662647
theorem B392015 : Blo 389765 392015 := bstep (se 1 (by rfl) ⟨294011, by rfl⟩ : syracuseStep 392015 = 588023) B588023
theorem B392031 : Blo 389765 392031 := bstep (se 1 (by rfl) ⟨294023, by rfl⟩ : syracuseStep 392031 = 588047) B588047
theorem B392059 : Blo 389765 392059 := bstep (se 1 (by rfl) ⟨294044, by rfl⟩ : syracuseStep 392059 = 588089) B588089
theorem B392111 : Blo 389765 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B588719 : Blo 389765 588719 := bstep (se 1 (by rfl) ⟨441539, by rfl⟩ : syracuseStep 588719 = 883079) B883079
theorem B687035 : Blo 389765 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B392135 : Blo 389765 392135 := bstep (se 1 (by rfl) ⟨294101, by rfl⟩ : syracuseStep 392135 = 588203) B588203
theorem B392155 : Blo 389765 392155 := bstep (se 1 (by rfl) ⟨294116, by rfl⟩ : syracuseStep 392155 = 588233) B588233
theorem B588809 : Blo 389765 588809 := bstep (se 2 (by rfl) ⟨220803, by rfl⟩ : syracuseStep 588809 = 441607) B441607
theorem B392231 : Blo 389765 392231 := bstep (se 1 (by rfl) ⟨294173, by rfl⟩ : syracuseStep 392231 = 588347) B588347
theorem B588839 : Blo 389765 588839 := bstep (se 1 (by rfl) ⟨441629, by rfl⟩ : syracuseStep 588839 = 883259) B883259
theorem B392271 : Blo 389765 392271 := bstep (se 1 (by rfl) ⟨294203, by rfl⟩ : syracuseStep 392271 = 588407) B588407
theorem B392287 : Blo 389765 392287 := bstep (se 1 (by rfl) ⟨294215, by rfl⟩ : syracuseStep 392287 = 588431) B588431
theorem B392315 : Blo 389765 392315 := bstep (se 1 (by rfl) ⟨294236, by rfl⟩ : syracuseStep 392315 = 588473) B588473
theorem B588923 : Blo 389765 588923 := bstep (se 1 (by rfl) ⟨441692, by rfl⟩ : syracuseStep 588923 = 883385) B883385
theorem B392367 : Blo 389765 392367 := bstep (se 1 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 392367 = 588551) B588551
theorem B392391 : Blo 389765 392391 := bstep (se 1 (by rfl) ⟨294293, by rfl⟩ : syracuseStep 392391 = 588587) B588587
theorem B392411 : Blo 389765 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B589049 : Blo 389765 589049 := bstep (se 2 (by rfl) ⟨220893, by rfl⟩ : syracuseStep 589049 = 441787) B441787
theorem B392487 : Blo 389765 392487 := bstep (se 1 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 392487 = 588731) B588731
theorem B392527 : Blo 389765 392527 := bstep (se 1 (by rfl) ⟨294395, by rfl⟩ : syracuseStep 392527 = 588791) B588791
theorem B392543 : Blo 389765 392543 := bstep (se 1 (by rfl) ⟨294407, by rfl⟩ : syracuseStep 392543 = 588815) B588815
theorem B621919 : Blo 389765 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B589151 : Blo 389765 589151 := bstep (se 1 (by rfl) ⟨441863, by rfl⟩ : syracuseStep 589151 = 883727) B883727
theorem B589163 : Blo 389765 589163 := bstep (se 1 (by rfl) ⟨441872, by rfl⟩ : syracuseStep 589163 = 883745) B883745
theorem B392571 : Blo 389765 392571 := bstep (se 1 (by rfl) ⟨294428, by rfl⟩ : syracuseStep 392571 = 588857) B588857
theorem B392623 : Blo 389765 392623 := bstep (se 1 (by rfl) ⟨294467, by rfl⟩ : syracuseStep 392623 = 588935) B588935
theorem B392647 : Blo 389765 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B392667 : Blo 389765 392667 := bstep (se 1 (by rfl) ⟨294500, by rfl⟩ : syracuseStep 392667 = 589001) B589001
theorem B2817575 : Blo 389765 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B392743 : Blo 389765 392743 := bstep (se 1 (by rfl) ⟨294557, by rfl⟩ : syracuseStep 392743 = 589115) B589115
theorem B392783 : Blo 389765 392783 := bstep (se 1 (by rfl) ⟨294587, by rfl⟩ : syracuseStep 392783 = 589175) B589175
theorem B589391 : Blo 389765 589391 := bstep (se 1 (by rfl) ⟨442043, by rfl⟩ : syracuseStep 589391 = 884087) B884087
theorem B392799 : Blo 389765 392799 := bstep (se 1 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 392799 = 589199) B589199
theorem B884321 : Blo 389765 884321 := bstep (se 2 (by rfl) ⟨331620, by rfl⟩ : syracuseStep 884321 = 663241) B663241
theorem B392827 : Blo 389765 392827 := bstep (se 1 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 392827 = 589241) B589241
theorem B392879 : Blo 389765 392879 := bstep (se 1 (by rfl) ⟨294659, by rfl⟩ : syracuseStep 392879 = 589319) B589319
theorem B392903 : Blo 389765 392903 := bstep (se 1 (by rfl) ⟨294677, by rfl⟩ : syracuseStep 392903 = 589355) B589355
theorem B589511 : Blo 389765 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B392923 : Blo 389765 392923 := bstep (se 1 (by rfl) ⟨294692, by rfl⟩ : syracuseStep 392923 = 589385) B589385
theorem B392999 : Blo 389765 392999 := bstep (se 1 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 392999 = 589499) B589499
theorem B393039 : Blo 389765 393039 := bstep (se 1 (by rfl) ⟨294779, by rfl⟩ : syracuseStep 393039 = 589559) B589559
theorem B393055 : Blo 389765 393055 := bstep (se 1 (by rfl) ⟨294791, by rfl⟩ : syracuseStep 393055 = 589583) B589583
theorem B589673 : Blo 389765 589673 := bstep (se 2 (by rfl) ⟨221127, by rfl⟩ : syracuseStep 589673 = 442255) B442255
theorem B393083 : Blo 389765 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B393135 : Blo 389765 393135 := bstep (se 1 (by rfl) ⟨294851, by rfl⟩ : syracuseStep 393135 = 589703) B589703
theorem B589751 : Blo 389765 589751 := bstep (se 1 (by rfl) ⟨442313, by rfl⟩ : syracuseStep 589751 = 884627) B884627
theorem B884663 : Blo 389765 884663 := bstep (se 1 (by rfl) ⟨663497, by rfl⟩ : syracuseStep 884663 = 1326995) B1326995
theorem B393159 : Blo 389765 393159 := bstep (se 1 (by rfl) ⟨294869, by rfl⟩ : syracuseStep 393159 = 589739) B589739
theorem B393179 : Blo 389765 393179 := bstep (se 1 (by rfl) ⟨294884, by rfl⟩ : syracuseStep 393179 = 589769) B589769
theorem B589787 : Blo 389765 589787 := bstep (se 1 (by rfl) ⟨442340, by rfl⟩ : syracuseStep 589787 = 884681) B884681
theorem B393503 : Blo 389765 393503 := bstep (se 1 (by rfl) ⟨295127, by rfl⟩ : syracuseStep 393503 = 590255) B590255
theorem B590171 : Blo 389765 590171 := bstep (se 1 (by rfl) ⟨442628, by rfl⟩ : syracuseStep 590171 = 885257) B885257
theorem B393563 : Blo 389765 393563 := bstep (se 1 (by rfl) ⟨295172, by rfl⟩ : syracuseStep 393563 = 590345) B590345
theorem B393583 : Blo 389765 393583 := bstep (se 1 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 393583 = 590375) B590375
theorem B4030883 : Blo 389765 4030883 := bstep (se 1 (by rfl) ⟨3023162, by rfl⟩ : syracuseStep 4030883 = 6046325) B6046325
theorem B393639 : Blo 389765 393639 := bstep (se 1 (by rfl) ⟨295229, by rfl⟩ : syracuseStep 393639 = 590459) B590459
theorem B885167 : Blo 389765 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B885203 : Blo 389765 885203 := bstep (se 1 (by rfl) ⟨663902, by rfl⟩ : syracuseStep 885203 = 1327805) B1327805
theorem B393723 : Blo 389765 393723 := bstep (se 1 (by rfl) ⟨295292, by rfl⟩ : syracuseStep 393723 = 590585) B590585
theorem B885311 : Blo 389765 885311 := bstep (se 1 (by rfl) ⟨663983, by rfl⟩ : syracuseStep 885311 = 1327967) B1327967
theorem B590399 : Blo 389765 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B885419 : Blo 389765 885419 := bstep (se 1 (by rfl) ⟨664064, by rfl⟩ : syracuseStep 885419 = 1328129) B1328129
theorem B590519 : Blo 389765 590519 := bstep (se 1 (by rfl) ⟨442889, by rfl⟩ : syracuseStep 590519 = 885779) B885779
theorem B1114847 : Blo 389765 1114847 := bstep (se 1 (by rfl) ⟨836135, by rfl⟩ : syracuseStep 1114847 = 1672271) B1672271
theorem B1115279 : Blo 389765 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B885959 : Blo 389765 885959 := bstep (se 1 (by rfl) ⟨664469, by rfl⟩ : syracuseStep 885959 = 1328939) B1328939
theorem B2688233 : Blo 389765 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B4425047 : Blo 389765 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B493391 : Blo 389765 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B48236471 : Blo 389765 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B493543 : Blo 389765 493543 := bstep (se 1 (by rfl) ⟨370157, by rfl⟩ : syracuseStep 493543 = 740315) B740315
theorem B5015681 : Blo 389765 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B3344813 : Blo 389765 3344813 := bstep (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) B1254305
theorem B1673723 : Blo 389765 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B657983 : Blo 389765 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B1116919 : Blo 389765 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B1117307 : Blo 389765 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B625807 : Blo 389765 625807 := bstep (se 1 (by rfl) ⟨469355, by rfl⟩ : syracuseStep 625807 = 938711) B938711
theorem B658651 : Blo 389765 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B396635 : Blo 389765 396635 := bstep (se 1 (by rfl) ⟨297476, by rfl⟩ : syracuseStep 396635 = 594953) B594953
theorem B1674695 : Blo 389765 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B986681 : Blo 389765 986681 := bstep (se 2 (by rfl) ⟨370005, by rfl⟩ : syracuseStep 986681 = 740011) B740011
theorem B3182291 : Blo 389765 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B626473 : Blo 389765 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B2035529 : Blo 389765 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B6983533 : Blo 389765 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B659407 : Blo 389765 659407 := bstep (se 1 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 659407 = 989111) B989111
theorem B3182651 : Blo 389765 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B495983 : Blo 389765 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B496039 : Blo 389765 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B1675721 : Blo 389765 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B660089 : Blo 389765 660089 := bstep (se 2 (by rfl) ⟨247533, by rfl⟩ : syracuseStep 660089 = 495067) B495067
theorem B660143 : Blo 389765 660143 := bstep (se 1 (by rfl) ⟨495107, by rfl⟩ : syracuseStep 660143 = 990215) B990215
theorem B496363 : Blo 389765 496363 := bstep (se 1 (by rfl) ⟨372272, by rfl⟩ : syracuseStep 496363 = 744545) B744545
theorem B529193 : Blo 389765 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B660379 : Blo 389765 660379 := bstep (se 1 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 660379 = 990569) B990569
theorem B8491985 : Blo 389765 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B628319 : Blo 389765 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B497335 : Blo 389765 497335 := bstep (se 1 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 497335 = 746003) B746003
theorem B988969 : Blo 389765 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B1677293 : Blo 389765 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B1316897 : Blo 389765 1316897 := bstep (se 2 (by rfl) ⟨493836, by rfl⟩ : syracuseStep 1316897 = 987673) B987673
theorem B1022081 : Blo 389765 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B4462937 : Blo 389765 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B661871 : Blo 389765 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B2234749 : Blo 389765 2234749 := bstep (se 3 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 2234749 = 838031) B838031
theorem B2988413 : Blo 389765 2988413 := bstep (se 3 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 2988413 = 1120655) B1120655
theorem B1120679 : Blo 389765 1120679 := bstep (se 1 (by rfl) ⟨840509, by rfl⟩ : syracuseStep 1120679 = 1681019) B1681019
theorem B989759 : Blo 389765 989759 := bstep (se 1 (by rfl) ⟨742319, by rfl⟩ : syracuseStep 989759 = 1484639) B1484639
theorem B662087 : Blo 389765 662087 := bstep (se 1 (by rfl) ⟨496565, by rfl⟩ : syracuseStep 662087 = 993131) B993131
theorem B3349187 : Blo 389765 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B531355 : Blo 389765 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B662519 : Blo 389765 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B990407 : Blo 389765 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B1055963 : Blo 389765 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B990427 : Blo 389765 990427 := bstep (se 1 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 990427 = 1485641) B1485641
theorem B10722725 : Blo 389765 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B8494753 : Blo 389765 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B1973969 : Blo 389765 1973969 := bstep (se 2 (by rfl) ⟨740238, by rfl⟩ : syracuseStep 1973969 = 1480477) B1480477
theorem B663275 : Blo 389765 663275 := bstep (se 1 (by rfl) ⟨497456, by rfl⟩ : syracuseStep 663275 = 994913) B994913
theorem B991561 : Blo 389765 991561 := bstep (se 2 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 991561 = 743671) B743671
theorem B991865 : Blo 389765 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B664247 : Blo 389765 664247 := bstep (se 1 (by rfl) ⟨498185, by rfl⟩ : syracuseStep 664247 = 996371) B996371
theorem B1680095 : Blo 389765 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B1319759 : Blo 389765 1319759 := bstep (se 1 (by rfl) ⟨989819, by rfl⟩ : syracuseStep 1319759 = 1979639) B1979639
theorem B1320083 : Blo 389765 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B3351851 : Blo 389765 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B1320353 : Blo 389765 1320353 := bstep (se 2 (by rfl) ⟨495132, by rfl⟩ : syracuseStep 1320353 = 990265) B990265
theorem B1582649 : Blo 389765 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B829225 : Blo 389765 829225 := bstep (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) B621919
theorem B117253973 : Blo 389765 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B1976399 : Blo 389765 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B1878383 : Blo 389765 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B993647 : Blo 389765 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B469567 : Blo 389765 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B6761083 : Blo 389765 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B1059499 : Blo 389765 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B994295 : Blo 389765 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B3320947 : Blo 389765 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B994427 : Blo 389765 994427 := bstep (se 1 (by rfl) ⟨745820, by rfl⟩ : syracuseStep 994427 = 1491641) B1491641
theorem B1977533 : Blo 389765 1977533 := bstep (se 3 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 1977533 = 741575) B741575
theorem B1060073 : Blo 389765 1060073 := bstep (se 2 (by rfl) ⟨397527, by rfl⟩ : syracuseStep 1060073 = 795055) B795055
theorem B1879307 : Blo 389765 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1486295 : Blo 389765 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B2108987 : Blo 389765 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B3354311 : Blo 389765 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B3026945 : Blo 389765 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B16330817 : Blo 389765 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B438619 : Blo 389765 438619 := bstep (se 1 (by rfl) ⟨328964, by rfl⟩ : syracuseStep 438619 = 657929) B657929
theorem B438727 : Blo 389765 438727 := bstep (se 1 (by rfl) ⟨329045, by rfl⟩ : syracuseStep 438727 = 658091) B658091
theorem B3584459 : Blo 389765 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B1323539 : Blo 389765 1323539 := bstep (se 1 (by rfl) ⟨992654, by rfl⟩ : syracuseStep 1323539 = 1985309) B1985309
theorem B2044561 : Blo 389765 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B1880729 : Blo 389765 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B439087 : Blo 389765 439087 := bstep (se 1 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 439087 = 658631) B658631
theorem B1880941 : Blo 389765 1880941 := bstep (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) B705353
theorem B996239 : Blo 389765 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B439195 : Blo 389765 439195 := bstep (se 1 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 439195 = 658793) B658793
theorem B2110373 : Blo 389765 2110373 := bstep (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) B395695
theorem B1488071 : Blo 389765 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B439591 : Blo 389765 439591 := bstep (se 1 (by rfl) ⟨329693, by rfl⟩ : syracuseStep 439591 = 659387) B659387
theorem B439663 : Blo 389765 439663 := bstep (se 1 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 439663 = 659495) B659495
theorem B439879 : Blo 389765 439879 := bstep (se 1 (by rfl) ⟨329909, by rfl⟩ : syracuseStep 439879 = 659819) B659819
theorem B3749921 : Blo 389765 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B1980449 : Blo 389765 1980449 := bstep (se 2 (by rfl) ⟨742668, by rfl⟩ : syracuseStep 1980449 = 1485337) B1485337
theorem B1980611 : Blo 389765 1980611 := bstep (se 1 (by rfl) ⟨1485458, by rfl⟩ : syracuseStep 1980611 = 2970917) B2970917
theorem B1063165 : Blo 389765 1063165 := bstep (se 3 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 1063165 = 398687) B398687
theorem B1325321 : Blo 389765 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B440743 : Blo 389765 440743 := bstep (se 1 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 440743 = 661115) B661115
theorem B834067 : Blo 389765 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B2374217 : Blo 389765 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B24394391 : Blo 389765 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B1784695 : Blo 389765 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B1260431 : Blo 389765 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B441319 : Blo 389765 441319 := bstep (se 1 (by rfl) ⟨330989, by rfl⟩ : syracuseStep 441319 = 661979) B661979
theorem B2407747 : Blo 389765 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B1326455 : Blo 389765 1326455 := bstep (se 1 (by rfl) ⟨994841, by rfl⟩ : syracuseStep 1326455 = 1989683) B1989683
theorem B4767113 : Blo 389765 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B2834585 : Blo 389765 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B1491155 : Blo 389765 1491155 := bstep (se 1 (by rfl) ⟨1118366, by rfl⟩ : syracuseStep 1491155 = 2236733) B2236733
theorem B835913 : Blo 389765 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B3752345 : Blo 389765 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B1327535 : Blo 389765 1327535 := bstep (se 1 (by rfl) ⟨995651, by rfl⟩ : syracuseStep 1327535 = 1991303) B1991303
theorem B3293729 : Blo 389765 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B442975 : Blo 389765 442975 := bstep (se 1 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 442975 = 664463) B664463
theorem B10175291 : Blo 389765 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B705359 : Blo 389765 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B1491959 : Blo 389765 1491959 := bstep (se 1 (by rfl) ⟨1118969, by rfl⟩ : syracuseStep 1491959 = 2237939) B2237939
theorem B1328507 : Blo 389765 1328507 := bstep (se 1 (by rfl) ⟨996380, by rfl⟩ : syracuseStep 1328507 = 1992761) B1992761
theorem B7161331 : Blo 389765 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B1984337 : Blo 389765 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B1886647 : Blo 389765 1886647 := bstep (se 1 (by rfl) ⟨1414985, by rfl⟩ : syracuseStep 1886647 = 2829971) B2829971
theorem B2673107 : Blo 389765 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B1985147 : Blo 389765 1985147 := bstep (se 1 (by rfl) ⟨1488860, by rfl⟩ : syracuseStep 1985147 = 2977721) B2977721
theorem B3361661 : Blo 389765 3361661 := bstep (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) B1260623
theorem B2018191 : Blo 389765 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1493903 : Blo 389765 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B2116925 : Blo 389765 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B25873843 : Blo 389765 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B2543407 : Blo 389765 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B1494845 : Blo 389765 1494845 := bstep (se 3 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 1494845 = 560567) B560567
theorem B2510813 : Blo 389765 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B839945 : Blo 389765 839945 := bstep (se 2 (by rfl) ⟨314979, by rfl⟩ : syracuseStep 839945 = 629959) B629959
theorem B4280779 : Blo 389765 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B1987091 : Blo 389765 1987091 := bstep (se 1 (by rfl) ⟨1490318, by rfl⟩ : syracuseStep 1987091 = 2980637) B2980637
theorem B1594313 : Blo 389765 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B1988873 : Blo 389765 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B3332441 : Blo 389765 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B1530431 : Blo 389765 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B2513683 : Blo 389765 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B9001847 : Blo 389765 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B4742297 : Blo 389765 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B2972861 : Blo 389765 2972861 := bstep (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) B1114823
theorem B1990007 : Blo 389765 1990007 := bstep (se 1 (by rfl) ⟨1492505, by rfl⟩ : syracuseStep 1990007 = 2985011) B2985011
theorem B1891721 : Blo 389765 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B4218313 : Blo 389765 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1990169 : Blo 389765 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B9002785 : Blo 389765 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B2809673 : Blo 389765 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B3334081 : Blo 389765 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B1269785 : Blo 389765 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B14311541 : Blo 389765 14311541 := bstep (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) B1341707
theorem B7561349 : Blo 389765 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B3334355 : Blo 389765 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B1335827 : Blo 389765 1335827 := bstep (se 1 (by rfl) ⟨1001870, by rfl⟩ : syracuseStep 1335827 = 2003741) B2003741
theorem B418375 : Blo 389765 418375 := bstep (se 1 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 418375 = 627563) B627563
theorem B877391 : Blo 389765 877391 := bstep (se 1 (by rfl) ⟨658043, by rfl⟩ : syracuseStep 877391 = 1316087) B1316087
theorem B877607 : Blo 389765 877607 := bstep (se 1 (by rfl) ⟨658205, by rfl⟩ : syracuseStep 877607 = 1316411) B1316411
theorem B943247 : Blo 389765 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B877787 : Blo 389765 877787 := bstep (se 1 (by rfl) ⟨658340, by rfl⟩ : syracuseStep 877787 = 1316681) B1316681
theorem B877985 : Blo 389765 877985 := bstep (se 2 (by rfl) ⟨329244, by rfl⟩ : syracuseStep 877985 = 658489) B658489
theorem B3565043 : Blo 389765 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B1009313 : Blo 389765 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B1664975 : Blo 389765 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B878543 : Blo 389765 878543 := bstep (se 1 (by rfl) ⟨658907, by rfl⟩ : syracuseStep 878543 = 1317815) B1317815
theorem B878921 : Blo 389765 878921 := bstep (se 2 (by rfl) ⟨329595, by rfl⟩ : syracuseStep 878921 = 659191) B659191
theorem B878939 : Blo 389765 878939 := bstep (se 1 (by rfl) ⟨659204, by rfl⟩ : syracuseStep 878939 = 1318409) B1318409
theorem B1993085 : Blo 389765 1993085 := bstep (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) B747407
theorem B12839467 : Blo 389765 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B944747 : Blo 389765 944747 := bstep (se 1 (by rfl) ⟨708560, by rfl⟩ : syracuseStep 944747 = 1417121) B1417121
theorem B1665947 : Blo 389765 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B879515 : Blo 389765 879515 := bstep (se 1 (by rfl) ⟨659636, by rfl⟩ : syracuseStep 879515 = 1319273) B1319273
theorem B879713 : Blo 389765 879713 := bstep (se 2 (by rfl) ⟨329892, by rfl⟩ : syracuseStep 879713 = 659785) B659785
theorem B1272955 : Blo 389765 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B584999 : Blo 389765 584999 := bstep (se 1 (by rfl) ⟨438749, by rfl⟩ : syracuseStep 584999 = 877499) B877499
theorem B879911 : Blo 389765 879911 := bstep (se 1 (by rfl) ⟨659933, by rfl⟩ : syracuseStep 879911 = 1319867) B1319867
theorem B585083 : Blo 389765 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B585209 : Blo 389765 585209 := bstep (se 2 (by rfl) ⟨219453, by rfl⟩ : syracuseStep 585209 = 438907) B438907
theorem B585311 : Blo 389765 585311 := bstep (se 1 (by rfl) ⟨438983, by rfl⟩ : syracuseStep 585311 = 877967) B877967
theorem B880289 : Blo 389765 880289 := bstep (se 2 (by rfl) ⟨330108, by rfl⟩ : syracuseStep 880289 = 660217) B660217
theorem B4484807 : Blo 389765 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B585527 : Blo 389765 585527 := bstep (se 1 (by rfl) ⟨439145, by rfl⟩ : syracuseStep 585527 = 878291) B878291
theorem B1666889 : Blo 389765 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B1666973 : Blo 389765 1666973 := bstep (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) B625115
theorem B880649 : Blo 389765 880649 := bstep (se 2 (by rfl) ⟨330243, by rfl⟩ : syracuseStep 880649 = 660487) B660487
theorem B585833 : Blo 389765 585833 := bstep (se 2 (by rfl) ⟨219687, by rfl⟩ : syracuseStep 585833 = 439375) B439375
theorem B2126027 : Blo 389765 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B4223339 : Blo 389765 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B586151 : Blo 389765 586151 := bstep (se 1 (by rfl) ⟨439613, by rfl⟩ : syracuseStep 586151 = 879227) B879227
theorem B881063 : Blo 389765 881063 := bstep (se 1 (by rfl) ⟨660797, by rfl⟩ : syracuseStep 881063 = 1321595) B1321595
theorem B586235 : Blo 389765 586235 := bstep (se 1 (by rfl) ⟨439676, by rfl⟩ : syracuseStep 586235 = 879353) B879353
theorem B881171 : Blo 389765 881171 := bstep (se 1 (by rfl) ⟨660878, by rfl⟩ : syracuseStep 881171 = 1321757) B1321757
theorem B881225 : Blo 389765 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B586361 : Blo 389765 586361 := bstep (se 2 (by rfl) ⟨219885, by rfl⟩ : syracuseStep 586361 = 439771) B439771
theorem B586415 : Blo 389765 586415 := bstep (se 1 (by rfl) ⟨439811, by rfl⟩ : syracuseStep 586415 = 879623) B879623
theorem B389855 : Blo 389765 389855 := bstep (se 1 (by rfl) ⟨292391, by rfl⟩ : syracuseStep 389855 = 584783) B584783
theorem B586463 : Blo 389765 586463 := bstep (se 1 (by rfl) ⟨439847, by rfl⟩ : syracuseStep 586463 = 879695) B879695
theorem B389935 : Blo 389765 389935 := bstep (se 1 (by rfl) ⟨292451, by rfl⟩ : syracuseStep 389935 = 584903) B584903
theorem B390043 : Blo 389765 390043 := bstep (se 1 (by rfl) ⟨292532, by rfl⟩ : syracuseStep 390043 = 585065) B585065
theorem B390095 : Blo 389765 390095 := bstep (se 1 (by rfl) ⟨292571, by rfl⟩ : syracuseStep 390095 = 585143) B585143
theorem B2520017 : Blo 389765 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B390119 : Blo 389765 390119 := bstep (se 1 (by rfl) ⟨292589, by rfl⟩ : syracuseStep 390119 = 585179) B585179
theorem B586727 : Blo 389765 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B881639 : Blo 389765 881639 := bstep (se 1 (by rfl) ⟨661229, by rfl⟩ : syracuseStep 881639 = 1322459) B1322459
theorem B521321 : Blo 389765 521321 := bstep (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) B390991
theorem B586985 : Blo 389765 586985 := bstep (se 2 (by rfl) ⟨220119, by rfl⟩ : syracuseStep 586985 = 440239) B440239
theorem B390431 : Blo 389765 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B587039 : Blo 389765 587039 := bstep (se 1 (by rfl) ⟨440279, by rfl⟩ : syracuseStep 587039 = 880559) B880559
theorem B390491 : Blo 389765 390491 := bstep (se 1 (by rfl) ⟨292868, by rfl⟩ : syracuseStep 390491 = 585737) B585737
theorem B882017 : Blo 389765 882017 := bstep (se 2 (by rfl) ⟨330756, by rfl⟩ : syracuseStep 882017 = 661513) B661513
theorem B390511 : Blo 389765 390511 := bstep (se 1 (by rfl) ⟨292883, by rfl⟩ : syracuseStep 390511 = 585767) B585767
theorem B750971 : Blo 389765 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B1340833 : Blo 389765 1340833 := bstep (se 2 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 1340833 = 1005625) B1005625
theorem B390567 : Blo 389765 390567 := bstep (se 1 (by rfl) ⟨292925, by rfl⟩ : syracuseStep 390567 = 585851) B585851
theorem B882107 : Blo 389765 882107 := bstep (se 1 (by rfl) ⟨661580, by rfl⟩ : syracuseStep 882107 = 1323161) B1323161
theorem B587207 : Blo 389765 587207 := bstep (se 1 (by rfl) ⟨440405, by rfl⟩ : syracuseStep 587207 = 880811) B880811
theorem B390651 : Blo 389765 390651 := bstep (se 1 (by rfl) ⟨292988, by rfl⟩ : syracuseStep 390651 = 585977) B585977
theorem B882233 : Blo 389765 882233 := bstep (se 2 (by rfl) ⟨330837, by rfl⟩ : syracuseStep 882233 = 661675) B661675
theorem B390719 : Blo 389765 390719 := bstep (se 1 (by rfl) ⟨293039, by rfl⟩ : syracuseStep 390719 = 586079) B586079
theorem B390727 : Blo 389765 390727 := bstep (se 1 (by rfl) ⟨293045, by rfl⟩ : syracuseStep 390727 = 586091) B586091
theorem B390879 : Blo 389765 390879 := bstep (se 1 (by rfl) ⟨293159, by rfl⟩ : syracuseStep 390879 = 586319) B586319
theorem B587561 : Blo 389765 587561 := bstep (se 2 (by rfl) ⟨220335, by rfl⟩ : syracuseStep 587561 = 440671) B440671
theorem B390959 : Blo 389765 390959 := bstep (se 1 (by rfl) ⟨293219, by rfl⟩ : syracuseStep 390959 = 586439) B586439
theorem B587567 : Blo 389765 587567 := bstep (se 1 (by rfl) ⟨440675, by rfl⟩ : syracuseStep 587567 = 881351) B881351
theorem B391067 : Blo 389765 391067 := bstep (se 1 (by rfl) ⟨293300, by rfl⟩ : syracuseStep 391067 = 586601) B586601
theorem B391119 : Blo 389765 391119 := bstep (se 1 (by rfl) ⟨293339, by rfl⟩ : syracuseStep 391119 = 586679) B586679
theorem B391143 : Blo 389765 391143 := bstep (se 1 (by rfl) ⟨293357, by rfl⟩ : syracuseStep 391143 = 586715) B586715
theorem B882899 : Blo 389765 882899 := bstep (se 1 (by rfl) ⟨662174, by rfl⟩ : syracuseStep 882899 = 1324349) B1324349
theorem B12646637 : Blo 389765 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B10025207 : Blo 389765 10025207 := bstep (se 1 (by rfl) ⟨7518905, by rfl⟩ : syracuseStep 10025207 = 15037811) B15037811
theorem B588041 : Blo 389765 588041 := bstep (se 2 (by rfl) ⟨220515, by rfl⟩ : syracuseStep 588041 = 441031) B441031
theorem B882953 : Blo 389765 882953 := bstep (se 2 (by rfl) ⟨331107, by rfl⟩ : syracuseStep 882953 = 662215) B662215
theorem B391455 : Blo 389765 391455 := bstep (se 1 (by rfl) ⟨293591, by rfl⟩ : syracuseStep 391455 = 587183) B587183
theorem B391515 : Blo 389765 391515 := bstep (se 1 (by rfl) ⟨293636, by rfl⟩ : syracuseStep 391515 = 587273) B587273
theorem B391535 : Blo 389765 391535 := bstep (se 1 (by rfl) ⟨293651, by rfl⟩ : syracuseStep 391535 = 587303) B587303
theorem B588143 : Blo 389765 588143 := bstep (se 1 (by rfl) ⟨441107, by rfl⟩ : syracuseStep 588143 = 882215) B882215
theorem B1669501 : Blo 389765 1669501 := bstep (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) B626063
theorem B391591 : Blo 389765 391591 := bstep (se 1 (by rfl) ⟨293693, by rfl⟩ : syracuseStep 391591 = 587387) B587387
theorem B883169 : Blo 389765 883169 := bstep (se 2 (by rfl) ⟨331188, by rfl⟩ : syracuseStep 883169 = 662377) B662377
theorem B391675 : Blo 389765 391675 := bstep (se 1 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 391675 = 587513) B587513
theorem B3832343 : Blo 389765 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B391743 : Blo 389765 391743 := bstep (se 1 (by rfl) ⟨293807, by rfl⟩ : syracuseStep 391743 = 587615) B587615
theorem B2128447 : Blo 389765 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B391751 : Blo 389765 391751 := bstep (se 1 (by rfl) ⟨293813, by rfl⟩ : syracuseStep 391751 = 587627) B587627
theorem B588359 : Blo 389765 588359 := bstep (se 1 (by rfl) ⟨441269, by rfl⟩ : syracuseStep 588359 = 882539) B882539
theorem B588395 : Blo 389765 588395 := bstep (se 1 (by rfl) ⟨441296, by rfl⟩ : syracuseStep 588395 = 882593) B882593
theorem B752303 : Blo 389765 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B391903 : Blo 389765 391903 := bstep (se 1 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 391903 = 587855) B587855
theorem B883475 : Blo 389765 883475 := bstep (se 1 (by rfl) ⟨662606, by rfl⟩ : syracuseStep 883475 = 1325213) B1325213
theorem B391983 : Blo 389765 391983 := bstep (se 1 (by rfl) ⟨293987, by rfl⟩ : syracuseStep 391983 = 587975) B587975
theorem B588623 : Blo 389765 588623 := bstep (se 1 (by rfl) ⟨441467, by rfl⟩ : syracuseStep 588623 = 882935) B882935
theorem B555931 : Blo 389765 555931 := bstep (se 1 (by rfl) ⟨416948, by rfl⟩ : syracuseStep 555931 = 833897) B833897
theorem B392091 : Blo 389765 392091 := bstep (se 1 (by rfl) ⟨294068, by rfl⟩ : syracuseStep 392091 = 588137) B588137
theorem B392143 : Blo 389765 392143 := bstep (se 1 (by rfl) ⟨294107, by rfl⟩ : syracuseStep 392143 = 588215) B588215
theorem B392167 : Blo 389765 392167 := bstep (se 1 (by rfl) ⟨294125, by rfl⟩ : syracuseStep 392167 = 588251) B588251
theorem B883835 : Blo 389765 883835 := bstep (se 1 (by rfl) ⟨662876, by rfl⟩ : syracuseStep 883835 = 1325753) B1325753
theorem B589019 : Blo 389765 589019 := bstep (se 1 (by rfl) ⟨441764, by rfl⟩ : syracuseStep 589019 = 883529) B883529
theorem B883961 : Blo 389765 883961 := bstep (se 2 (by rfl) ⟨331485, by rfl⟩ : syracuseStep 883961 = 662971) B662971
theorem B392479 : Blo 389765 392479 := bstep (se 1 (by rfl) ⟨294359, by rfl⟩ : syracuseStep 392479 = 588719) B588719
theorem B392539 : Blo 389765 392539 := bstep (se 1 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 392539 = 588809) B588809
theorem B392559 : Blo 389765 392559 := bstep (se 1 (by rfl) ⟨294419, by rfl⟩ : syracuseStep 392559 = 588839) B588839
theorem B589193 : Blo 389765 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B884105 : Blo 389765 884105 := bstep (se 2 (by rfl) ⟨331539, by rfl⟩ : syracuseStep 884105 = 663079) B663079
theorem B392615 : Blo 389765 392615 := bstep (se 1 (by rfl) ⟨294461, by rfl⟩ : syracuseStep 392615 = 588923) B588923
theorem B392699 : Blo 389765 392699 := bstep (se 1 (by rfl) ⟨294524, by rfl⟩ : syracuseStep 392699 = 589049) B589049
theorem B884231 : Blo 389765 884231 := bstep (se 1 (by rfl) ⟨663173, by rfl⟩ : syracuseStep 884231 = 1326347) B1326347
theorem B392767 : Blo 389765 392767 := bstep (se 1 (by rfl) ⟨294575, by rfl⟩ : syracuseStep 392767 = 589151) B589151
theorem B392775 : Blo 389765 392775 := bstep (se 1 (by rfl) ⟨294581, by rfl⟩ : syracuseStep 392775 = 589163) B589163
theorem B884411 : Blo 389765 884411 := bstep (se 1 (by rfl) ⟨663308, by rfl⟩ : syracuseStep 884411 = 1326617) B1326617
theorem B392927 : Blo 389765 392927 := bstep (se 1 (by rfl) ⟨294695, by rfl⟩ : syracuseStep 392927 = 589391) B589391
theorem B589547 : Blo 389765 589547 := bstep (se 1 (by rfl) ⟨442160, by rfl⟩ : syracuseStep 589547 = 884321) B884321
theorem B393007 : Blo 389765 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B884537 : Blo 389765 884537 := bstep (se 2 (by rfl) ⟨331701, by rfl⟩ : syracuseStep 884537 = 663403) B663403
theorem B393115 : Blo 389765 393115 := bstep (se 1 (by rfl) ⟨294836, by rfl⟩ : syracuseStep 393115 = 589673) B589673
theorem B393167 : Blo 389765 393167 := bstep (se 1 (by rfl) ⟨294875, by rfl⟩ : syracuseStep 393167 = 589751) B589751
theorem B589775 : Blo 389765 589775 := bstep (se 1 (by rfl) ⟨442331, by rfl⟩ : syracuseStep 589775 = 884663) B884663
theorem B393191 : Blo 389765 393191 := bstep (se 1 (by rfl) ⟨294893, by rfl⟩ : syracuseStep 393191 = 589787) B589787
theorem B557275 : Blo 389765 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B393447 : Blo 389765 393447 := bstep (se 1 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 393447 = 590171) B590171
theorem B2687255 : Blo 389765 2687255 := bstep (se 1 (by rfl) ⟨2015441, by rfl⟩ : syracuseStep 2687255 = 4030883) B4030883
theorem B885023 : Blo 389765 885023 := bstep (se 1 (by rfl) ⟨663767, by rfl⟩ : syracuseStep 885023 = 1327535) B1327535
theorem B590111 : Blo 389765 590111 := bstep (se 1 (by rfl) ⟨442583, by rfl⟩ : syracuseStep 590111 = 885167) B885167
theorem B590135 : Blo 389765 590135 := bstep (se 1 (by rfl) ⟨442601, by rfl⟩ : syracuseStep 590135 = 885203) B885203
theorem B2195819 : Blo 389765 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B590207 : Blo 389765 590207 := bstep (se 1 (by rfl) ⟨442655, by rfl⟩ : syracuseStep 590207 = 885311) B885311
theorem B393599 : Blo 389765 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B590279 : Blo 389765 590279 := bstep (se 1 (by rfl) ⟨442709, by rfl⟩ : syracuseStep 590279 = 885419) B885419
theorem B393679 : Blo 389765 393679 := bstep (se 1 (by rfl) ⟨295259, by rfl⟩ : syracuseStep 393679 = 590519) B590519
theorem B6783527 : Blo 389765 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B590633 : Blo 389765 590633 := bstep (se 2 (by rfl) ⟨221487, by rfl⟩ : syracuseStep 590633 = 442975) B442975
theorem B590639 : Blo 389765 590639 := bstep (se 1 (by rfl) ⟨442979, by rfl⟩ : syracuseStep 590639 = 885959) B885959
theorem B2950031 : Blo 389765 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B885671 : Blo 389765 885671 := bstep (se 1 (by rfl) ⟨664253, by rfl⟩ : syracuseStep 885671 = 1328507) B1328507
theorem B3343787 : Blo 389765 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B2229875 : Blo 389765 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B1115815 : Blo 389765 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B1411181 : Blo 389765 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B1411283 : Blo 389765 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B657787 : Blo 389765 657787 := bstep (se 1 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 657787 = 986681) B986681
theorem B658057 : Blo 389765 658057 := bstep (se 2 (by rfl) ⟨246771, by rfl⟩ : syracuseStep 658057 = 493543) B493543
theorem B1673875 : Blo 389765 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B559963 : Blo 389765 559963 := bstep (se 1 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 559963 = 839945) B839945
theorem B1117147 : Blo 389765 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B2231333 : Blo 389765 2231333 := bstep (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) B418375
theorem B9014777 : Blo 389765 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B2002589 : Blo 389765 2002589 := bstep (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) B750971
theorem B2690921 : Blo 389765 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B1118195 : Blo 389765 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B4427929 : Blo 389765 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B659839 : Blo 389765 659839 := bstep (se 1 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 659839 = 989759) B989759
theorem B1020287 : Blo 389765 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B2232791 : Blo 389765 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B6001231 : Blo 389765 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B660271 : Blo 389765 660271 := bstep (se 1 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 660271 = 990407) B990407
theorem B1315709 : Blo 389765 1315709 := bstep (se 3 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 1315709 = 493391) B493391
theorem B7148483 : Blo 389765 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B1315979 : Blo 389765 1315979 := bstep (se 1 (by rfl) ⟨986984, by rfl⟩ : syracuseStep 1315979 = 1973969) B1973969
theorem B9311377 : Blo 389765 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B1873115 : Blo 389765 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B9541027 : Blo 389765 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B890551 : Blo 389765 890551 := bstep (se 1 (by rfl) ⟨667913, by rfl⟩ : syracuseStep 890551 = 1335827) B1335827
theorem B661243 : Blo 389765 661243 := bstep (se 1 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 661243 = 991865) B991865
theorem B1120063 : Blo 389765 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B661385 : Blo 389765 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B5707705 : Blo 389765 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B628831 : Blo 389765 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B2726081 : Blo 389765 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B2234567 : Blo 389765 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B661817 : Blo 389765 661817 := bstep (se 2 (by rfl) ⟨248181, by rfl⟩ : syracuseStep 661817 = 496363) B496363
theorem B1055099 : Blo 389765 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B1317599 : Blo 389765 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B1252255 : Blo 389765 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B662431 : Blo 389765 662431 := bstep (se 1 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 662431 = 993647) B993647
theorem B629831 : Blo 389765 629831 := bstep (se 1 (by rfl) ⟨472373, by rfl⟩ : syracuseStep 629831 = 944747) B944747
theorem B662863 : Blo 389765 662863 := bstep (se 1 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 662863 = 994295) B994295
theorem B662951 : Blo 389765 662951 := bstep (se 1 (by rfl) ⟨497213, by rfl⟩ : syracuseStep 662951 = 994427) B994427
theorem B1318355 : Blo 389765 1318355 := bstep (se 1 (by rfl) ⟨988766, by rfl⟩ : syracuseStep 1318355 = 1977533) B1977533
theorem B1252871 : Blo 389765 1252871 := bstep (se 1 (by rfl) ⟨939653, by rfl⟩ : syracuseStep 1252871 = 1879307) B1879307
theorem B663113 : Blo 389765 663113 := bstep (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) B497335
theorem B990863 : Blo 389765 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B1318625 : Blo 389765 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B2236207 : Blo 389765 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B2989871 : Blo 389765 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B10887211 : Blo 389765 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B1417351 : Blo 389765 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B1417553 : Blo 389765 1417553 := bstep (se 2 (by rfl) ⟨531582, by rfl⟩ : syracuseStep 1417553 = 1063165) B1063165
theorem B1253819 : Blo 389765 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B664159 : Blo 389765 664159 := bstep (se 1 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 664159 = 996239) B996239
theorem B1680011 : Blo 389765 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B992047 : Blo 389765 992047 := bstep (se 1 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 992047 = 1488071) B1488071
theorem B1057693 : Blo 389765 1057693 := bstep (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) B396635
theorem B3351577 : Blo 389765 3351577 := bstep (se 2 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 3351577 = 2513683) B2513683
theorem B4465853 : Blo 389765 4465853 := bstep (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) B1674695
theorem B2499947 : Blo 389765 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B1320299 : Blo 389765 1320299 := bstep (se 1 (by rfl) ⟨990224, by rfl⟩ : syracuseStep 1320299 = 1980449) B1980449
theorem B1320407 : Blo 389765 1320407 := bstep (se 1 (by rfl) ⟨990305, by rfl⟩ : syracuseStep 1320407 = 1980611) B1980611
theorem B8431091 : Blo 389765 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B1320569 : Blo 389765 1320569 := bstep (se 2 (by rfl) ⟨495213, by rfl⟩ : syracuseStep 1320569 = 990427) B990427
theorem B1582811 : Blo 389765 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B16262927 : Blo 389765 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B501535 : Blo 389765 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B12003713 : Blo 389765 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B994103 : Blo 389765 994103 := bstep (se 1 (by rfl) ⟨745577, by rfl⟩ : syracuseStep 994103 = 1491155) B1491155
theorem B2501563 : Blo 389765 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B1322081 : Blo 389765 1322081 := bstep (se 2 (by rfl) ⟨495780, by rfl⟩ : syracuseStep 1322081 = 991561) B991561
theorem B994639 : Blo 389765 994639 := bstep (se 1 (by rfl) ⟨745979, by rfl⟩ : syracuseStep 994639 = 1491959) B1491959
theorem B1322621 : Blo 389765 1322621 := bstep (se 3 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 1322621 = 495983) B495983
theorem B1322891 : Blo 389765 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B32157647 : Blo 389765 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B1782071 : Blo 389765 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B438655 : Blo 389765 438655 := bstep (se 1 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 438655 = 657983) B657983
theorem B1323431 : Blo 389765 1323431 := bstep (se 1 (by rfl) ⟨992573, by rfl⟩ : syracuseStep 1323431 = 1985147) B1985147
theorem B2241107 : Blo 389765 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B995935 : Blo 389765 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B9548441 : Blo 389765 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B1880957 : Blo 389765 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B996563 : Blo 389765 996563 := bstep (se 1 (by rfl) ⟨747422, by rfl⟩ : syracuseStep 996563 = 1494845) B1494845
theorem B1357019 : Blo 389765 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B1390189 : Blo 389765 1390189 := bstep (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) B521321
theorem B2504357 : Blo 389765 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B1324727 : Blo 389765 1324727 := bstep (se 1 (by rfl) ⟨993545, by rfl⟩ : syracuseStep 1324727 = 1987091) B1987091
theorem B440059 : Blo 389765 440059 := bstep (se 1 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 440059 = 660089) B660089
theorem B440095 : Blo 389765 440095 := bstep (se 1 (by rfl) ⟨330071, by rfl⟩ : syracuseStep 440095 = 660143) B660143
theorem B1062875 : Blo 389765 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B17119289 : Blo 389765 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B5650661 : Blo 389765 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B1489225 : Blo 389765 1489225 := bstep (se 2 (by rfl) ⟨558459, by rfl⟩ : syracuseStep 1489225 = 1116919) B1116919
theorem B1325915 : Blo 389765 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B834409 : Blo 389765 834409 := bstep (se 2 (by rfl) ⟨312903, by rfl⟩ : syracuseStep 834409 = 625807) B625807
theorem B441247 : Blo 389765 441247 := bstep (se 1 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 441247 = 661871) B661871
theorem B441391 : Blo 389765 441391 := bstep (se 1 (by rfl) ⟨331043, by rfl⟩ : syracuseStep 441391 = 662087) B662087
theorem B441679 : Blo 389765 441679 := bstep (se 1 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 441679 = 662519) B662519
theorem B3161531 : Blo 389765 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B1981907 : Blo 389765 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B703975 : Blo 389765 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B1326671 : Blo 389765 1326671 := bstep (se 1 (by rfl) ⟨995003, by rfl⟩ : syracuseStep 1326671 = 1990007) B1990007
theorem B1326779 : Blo 389765 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B442183 : Blo 389765 442183 := bstep (se 1 (by rfl) ⟨331637, by rfl⟩ : syracuseStep 442183 = 663275) B663275
theorem B442831 : Blo 389765 442831 := bstep (se 1 (by rfl) ⟨332123, by rfl⟩ : syracuseStep 442831 = 664247) B664247
theorem B2376695 : Blo 389765 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B672875 : Blo 389765 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B2507921 : Blo 389765 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B78169315 : Blo 389765 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B1328723 : Blo 389765 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B1787777 : Blo 389765 1787777 := bstep (se 2 (by rfl) ⟨670416, by rfl⟩ : syracuseStep 1787777 = 1340833) B1340833
theorem B706715 : Blo 389765 706715 := bstep (se 1 (by rfl) ⟨530036, by rfl⟩ : syracuseStep 706715 = 1060073) B1060073
theorem B4442525 : Blo 389765 4442525 := bstep (se 3 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 4442525 = 1665947) B1665947
theorem B2017963 : Blo 389765 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B2837929 : Blo 389765 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B2379593 : Blo 389765 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B741241 : Blo 389765 741241 := bstep (se 2 (by rfl) ⟨277965, by rfl⟩ : syracuseStep 741241 = 555931) B555931
theorem B708473 : Blo 389765 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B840287 : Blo 389765 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B5624417 : Blo 389765 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B11326337 : Blo 389765 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B4445441 : Blo 389765 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B1889723 : Blo 389765 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B743231 : Blo 389765 743231 := bstep (se 1 (by rfl) ⟨557423, by rfl⟩ : syracuseStep 743231 = 1114847) B1114847
theorem B743519 : Blo 389765 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B9558557 : Blo 389765 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B10902197 : Blo 389765 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B744871 : Blo 389765 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B1105633 : Blo 389765 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B2121527 : Blo 389765 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B2121767 : Blo 389765 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B4448357 : Blo 389765 4448357 := bstep (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) B834067
theorem B2515529 : Blo 389765 2515529 := bstep (se 2 (by rfl) ⟨943323, by rfl⟩ : syracuseStep 2515529 = 1886647) B1886647
theorem B7168621 : Blo 389765 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B5661323 : Blo 389765 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B418879 : Blo 389765 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B877931 : Blo 389765 877931 := bstep (se 1 (by rfl) ⟨658448, by rfl⟩ : syracuseStep 877931 = 1316897) B1316897
theorem B1697273 : Blo 389765 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B2221627 : Blo 389765 2221627 := bstep (se 1 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 2221627 = 3332441) B3332441
theorem B2975291 : Blo 389765 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1992275 : Blo 389765 1992275 := bstep (se 1 (by rfl) ⟨1494206, by rfl⟩ : syracuseStep 1992275 = 2988413) B2988413
theorem B747119 : Blo 389765 747119 := bstep (se 1 (by rfl) ⟨560339, by rfl⟩ : syracuseStep 747119 = 1120679) B1120679
theorem B878201 : Blo 389765 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B34498457 : Blo 389765 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B879209 : Blo 389765 879209 := bstep (se 2 (by rfl) ⟨329703, by rfl⟩ : syracuseStep 879209 = 659407) B659407
theorem B846523 : Blo 389765 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B5040899 : Blo 389765 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B2222903 : Blo 389765 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B584825 : Blo 389765 584825 := bstep (se 2 (by rfl) ⟨219309, by rfl⟩ : syracuseStep 584825 = 438619) B438619
theorem B584927 : Blo 389765 584927 := bstep (se 1 (by rfl) ⟨438695, by rfl⟩ : syracuseStep 584927 = 877391) B877391
theorem B879839 : Blo 389765 879839 := bstep (se 1 (by rfl) ⟨659879, by rfl⟩ : syracuseStep 879839 = 1319759) B1319759
theorem B584969 : Blo 389765 584969 := bstep (se 2 (by rfl) ⟨219363, by rfl⟩ : syracuseStep 584969 = 438727) B438727
theorem B585071 : Blo 389765 585071 := bstep (se 1 (by rfl) ⟨438803, by rfl⟩ : syracuseStep 585071 = 877607) B877607
theorem B880055 : Blo 389765 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B585191 : Blo 389765 585191 := bstep (se 1 (by rfl) ⟨438893, by rfl⟩ : syracuseStep 585191 = 877787) B877787
theorem B585323 : Blo 389765 585323 := bstep (se 1 (by rfl) ⟨438992, by rfl⟩ : syracuseStep 585323 = 877985) B877985
theorem B880235 : Blo 389765 880235 := bstep (se 1 (by rfl) ⟨660176, by rfl⟩ : syracuseStep 880235 = 1320353) B1320353
theorem B585449 : Blo 389765 585449 := bstep (se 2 (by rfl) ⟨219543, by rfl⟩ : syracuseStep 585449 = 439087) B439087
theorem B585593 : Blo 389765 585593 := bstep (se 2 (by rfl) ⟨219597, by rfl⟩ : syracuseStep 585593 = 439195) B439195
theorem B880505 : Blo 389765 880505 := bstep (se 2 (by rfl) ⟨330189, by rfl⟩ : syracuseStep 880505 = 660379) B660379
theorem B1109983 : Blo 389765 1109983 := bstep (se 1 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 1109983 = 1664975) B1664975
theorem B585695 : Blo 389765 585695 := bstep (se 1 (by rfl) ⟨439271, by rfl⟩ : syracuseStep 585695 = 878543) B878543
theorem B585947 : Blo 389765 585947 := bstep (se 1 (by rfl) ⟨439460, by rfl⟩ : syracuseStep 585947 = 878921) B878921
theorem B585959 : Blo 389765 585959 := bstep (se 1 (by rfl) ⟨439469, by rfl⟩ : syracuseStep 585959 = 878939) B878939
theorem B586121 : Blo 389765 586121 := bstep (se 2 (by rfl) ⟨219795, by rfl⟩ : syracuseStep 586121 = 439591) B439591
theorem B586217 : Blo 389765 586217 := bstep (se 2 (by rfl) ⟨219831, by rfl⟩ : syracuseStep 586217 = 439663) B439663
theorem B586343 : Blo 389765 586343 := bstep (se 1 (by rfl) ⟨439757, by rfl⟩ : syracuseStep 586343 = 879515) B879515
theorem B586475 : Blo 389765 586475 := bstep (se 1 (by rfl) ⟨439856, by rfl⟩ : syracuseStep 586475 = 879713) B879713
theorem B586505 : Blo 389765 586505 := bstep (se 2 (by rfl) ⟨219939, by rfl⟩ : syracuseStep 586505 = 439879) B439879
theorem B389999 : Blo 389765 389999 := bstep (se 1 (by rfl) ⟨292499, by rfl⟩ : syracuseStep 389999 = 584999) B584999
theorem B586607 : Blo 389765 586607 := bstep (se 1 (by rfl) ⟨439955, by rfl⟩ : syracuseStep 586607 = 879911) B879911
theorem B390055 : Blo 389765 390055 := bstep (se 1 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 390055 = 585083) B585083
theorem B390139 : Blo 389765 390139 := bstep (se 1 (by rfl) ⟨292604, by rfl⟩ : syracuseStep 390139 = 585209) B585209
theorem B1405991 : Blo 389765 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B390207 : Blo 389765 390207 := bstep (se 1 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 390207 = 585311) B585311
theorem B586859 : Blo 389765 586859 := bstep (se 1 (by rfl) ⟨440144, by rfl⟩ : syracuseStep 586859 = 880289) B880289
theorem B390351 : Blo 389765 390351 := bstep (se 1 (by rfl) ⟨292763, by rfl⟩ : syracuseStep 390351 = 585527) B585527
theorem B1111259 : Blo 389765 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B1111315 : Blo 389765 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B587099 : Blo 389765 587099 := bstep (se 1 (by rfl) ⟨440324, by rfl⟩ : syracuseStep 587099 = 880649) B880649
theorem B390555 : Blo 389765 390555 := bstep (se 1 (by rfl) ⟨292916, by rfl⟩ : syracuseStep 390555 = 585833) B585833
theorem B2815559 : Blo 389765 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B390767 : Blo 389765 390767 := bstep (se 1 (by rfl) ⟨293075, by rfl⟩ : syracuseStep 390767 = 586151) B586151
theorem B587375 : Blo 389765 587375 := bstep (se 1 (by rfl) ⟨440531, by rfl⟩ : syracuseStep 587375 = 881063) B881063
theorem B390823 : Blo 389765 390823 := bstep (se 1 (by rfl) ⟨293117, by rfl⟩ : syracuseStep 390823 = 586235) B586235
theorem B587447 : Blo 389765 587447 := bstep (se 1 (by rfl) ⟨440585, by rfl⟩ : syracuseStep 587447 = 881171) B881171
theorem B882359 : Blo 389765 882359 := bstep (se 1 (by rfl) ⟨661769, by rfl⟩ : syracuseStep 882359 = 1323539) B1323539
theorem B587483 : Blo 389765 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B390907 : Blo 389765 390907 := bstep (se 1 (by rfl) ⟨293180, by rfl⟩ : syracuseStep 390907 = 586361) B586361
theorem B390943 : Blo 389765 390943 := bstep (se 1 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 390943 = 586415) B586415
theorem B390975 : Blo 389765 390975 := bstep (se 1 (by rfl) ⟨293231, by rfl⟩ : syracuseStep 390975 = 586463) B586463
theorem B2226001 : Blo 389765 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B2979665 : Blo 389765 2979665 := bstep (se 2 (by rfl) ⟨1117374, by rfl⟩ : syracuseStep 2979665 = 2234749) B2234749
theorem B587657 : Blo 389765 587657 := bstep (se 2 (by rfl) ⟨220371, by rfl⟩ : syracuseStep 587657 = 440743) B440743
theorem B1406915 : Blo 389765 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B391151 : Blo 389765 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B587759 : Blo 389765 587759 := bstep (se 1 (by rfl) ⟨440819, by rfl⟩ : syracuseStep 587759 = 881639) B881639
theorem B391323 : Blo 389765 391323 := bstep (se 1 (by rfl) ⟨293492, by rfl⟩ : syracuseStep 391323 = 586985) B586985
theorem B391359 : Blo 389765 391359 := bstep (se 1 (by rfl) ⟨293519, by rfl⟩ : syracuseStep 391359 = 587039) B587039
theorem B588011 : Blo 389765 588011 := bstep (se 1 (by rfl) ⟨441008, by rfl⟩ : syracuseStep 588011 = 882017) B882017
theorem B588071 : Blo 389765 588071 := bstep (se 1 (by rfl) ⟨441053, by rfl⟩ : syracuseStep 588071 = 882107) B882107
theorem B391471 : Blo 389765 391471 := bstep (se 1 (by rfl) ⟨293603, by rfl⟩ : syracuseStep 391471 = 587207) B587207
theorem B12712301 : Blo 389765 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B5044589 : Blo 389765 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B588155 : Blo 389765 588155 := bstep (se 1 (by rfl) ⟨441116, by rfl⟩ : syracuseStep 588155 = 882233) B882233
theorem B391707 : Blo 389765 391707 := bstep (se 1 (by rfl) ⟨293780, by rfl⟩ : syracuseStep 391707 = 587561) B587561
theorem B391711 : Blo 389765 391711 := bstep (se 1 (by rfl) ⟨293783, by rfl⟩ : syracuseStep 391711 = 587567) B587567
theorem B588425 : Blo 389765 588425 := bstep (se 2 (by rfl) ⟨220659, by rfl⟩ : syracuseStep 588425 = 441319) B441319
theorem B588599 : Blo 389765 588599 := bstep (se 1 (by rfl) ⟨441449, by rfl⟩ : syracuseStep 588599 = 882899) B882899
theorem B6683471 : Blo 389765 6683471 := bstep (se 1 (by rfl) ⟨5012603, by rfl⟩ : syracuseStep 6683471 = 10025207) B10025207
theorem B392027 : Blo 389765 392027 := bstep (se 1 (by rfl) ⟨294020, by rfl⟩ : syracuseStep 392027 = 588041) B588041
theorem B588635 : Blo 389765 588635 := bstep (se 1 (by rfl) ⟨441476, by rfl⟩ : syracuseStep 588635 = 882953) B882953
theorem B883547 : Blo 389765 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B3341189 : Blo 389765 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B392095 : Blo 389765 392095 := bstep (se 1 (by rfl) ⟨294071, by rfl⟩ : syracuseStep 392095 = 588143) B588143
theorem B13564837 : Blo 389765 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B588779 : Blo 389765 588779 := bstep (se 1 (by rfl) ⟨441584, by rfl⟩ : syracuseStep 588779 = 883169) B883169
theorem B2554895 : Blo 389765 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B392239 : Blo 389765 392239 := bstep (se 1 (by rfl) ⟨294179, by rfl⟩ : syracuseStep 392239 = 588359) B588359
theorem B392263 : Blo 389765 392263 := bstep (se 1 (by rfl) ⟨294197, by rfl⟩ : syracuseStep 392263 = 588395) B588395
theorem B3210329 : Blo 389765 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B588983 : Blo 389765 588983 := bstep (se 1 (by rfl) ⟨441737, by rfl⟩ : syracuseStep 588983 = 883475) B883475
theorem B392415 : Blo 389765 392415 := bstep (se 1 (by rfl) ⟨294311, by rfl⟩ : syracuseStep 392415 = 588623) B588623
theorem B589223 : Blo 389765 589223 := bstep (se 1 (by rfl) ⟨441917, by rfl⟩ : syracuseStep 589223 = 883835) B883835
theorem B392679 : Blo 389765 392679 := bstep (se 1 (by rfl) ⟨294509, by rfl⟩ : syracuseStep 392679 = 589019) B589019
theorem B589307 : Blo 389765 589307 := bstep (se 1 (by rfl) ⟨441980, by rfl⟩ : syracuseStep 589307 = 883961) B883961
theorem B884303 : Blo 389765 884303 := bstep (se 1 (by rfl) ⟨663227, by rfl⟩ : syracuseStep 884303 = 1326455) B1326455
theorem B392795 : Blo 389765 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B589403 : Blo 389765 589403 := bstep (se 1 (by rfl) ⟨442052, by rfl⟩ : syracuseStep 589403 = 884105) B884105
theorem B589487 : Blo 389765 589487 := bstep (se 1 (by rfl) ⟨442115, by rfl⟩ : syracuseStep 589487 = 884231) B884231
theorem B589607 : Blo 389765 589607 := bstep (se 1 (by rfl) ⟨442205, by rfl⟩ : syracuseStep 589607 = 884411) B884411
theorem B393031 : Blo 389765 393031 := bstep (se 1 (by rfl) ⟨294773, by rfl⟩ : syracuseStep 393031 = 589547) B589547
theorem B589691 : Blo 389765 589691 := bstep (se 1 (by rfl) ⟨442268, by rfl⟩ : syracuseStep 589691 = 884537) B884537
theorem B393183 : Blo 389765 393183 := bstep (se 1 (by rfl) ⟨294887, by rfl⟩ : syracuseStep 393183 = 589775) B589775
theorem B14516281 : Blo 389765 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B590015 : Blo 389765 590015 := bstep (se 1 (by rfl) ⟨442511, by rfl⟩ : syracuseStep 590015 = 885023) B885023
theorem B393407 : Blo 389765 393407 := bstep (se 1 (by rfl) ⟨295055, by rfl⟩ : syracuseStep 393407 = 590111) B590111
theorem B393423 : Blo 389765 393423 := bstep (se 1 (by rfl) ⟨295067, by rfl⟩ : syracuseStep 393423 = 590135) B590135
theorem B393471 : Blo 389765 393471 := bstep (se 1 (by rfl) ⟨295103, by rfl⟩ : syracuseStep 393471 = 590207) B590207
theorem B393519 : Blo 389765 393519 := bstep (se 1 (by rfl) ⟨295139, by rfl⟩ : syracuseStep 393519 = 590279) B590279
theorem B393755 : Blo 389765 393755 := bstep (se 1 (by rfl) ⟨295316, by rfl⟩ : syracuseStep 393755 = 590633) B590633
theorem B393759 : Blo 389765 393759 := bstep (se 1 (by rfl) ⟨295319, by rfl⟩ : syracuseStep 393759 = 590639) B590639
theorem B1966687 : Blo 389765 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B590441 : Blo 389765 590441 := bstep (se 2 (by rfl) ⟨221415, by rfl⟩ : syracuseStep 590441 = 442831) B442831
theorem B590447 : Blo 389765 590447 := bstep (se 1 (by rfl) ⟨442835, by rfl⟩ : syracuseStep 590447 = 885671) B885671
theorem B1671947 : Blo 389765 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B885545 : Blo 389765 885545 := bstep (se 2 (by rfl) ⟨332079, by rfl⟩ : syracuseStep 885545 = 664159) B664159
theorem B2229191 : Blo 389765 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B2720765 : Blo 389765 2720765 := bstep (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) B1020287
theorem B885815 : Blo 389765 885815 := bstep (se 1 (by rfl) ⟨664361, by rfl⟩ : syracuseStep 885815 = 1328723) B1328723
theorem B1410257 : Blo 389765 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B558505 : Blo 389765 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B18089405 : Blo 389765 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B560191 : Blo 389765 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B1248743 : Blo 389765 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B2231833 : Blo 389765 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B495487 : Blo 389765 495487 := bstep (se 1 (by rfl) ⟨371615, by rfl⟩ : syracuseStep 495487 = 743231) B743231
theorem B2986469 : Blo 389765 2986469 := bstep (se 4 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 2986469 = 559963) B559963
theorem B660575 : Blo 389765 660575 := bstep (se 1 (by rfl) ⟨495431, by rfl⟩ : syracuseStep 660575 = 990863) B990863
theorem B988321 : Blo 389765 988321 := bstep (se 2 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 988321 = 741241) B741241
theorem B1414351 : Blo 389765 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B1479977 : Blo 389765 1479977 := bstep (se 2 (by rfl) ⟨554991, by rfl⟩ : syracuseStep 1479977 = 1109983) B1109983
theorem B1414511 : Blo 389765 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B1677019 : Blo 389765 1677019 := bstep (se 1 (by rfl) ⟨1257764, by rfl⟩ : syracuseStep 1677019 = 2515529) B2515529
theorem B3774215 : Blo 389765 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B1120007 : Blo 389765 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B8001641 : Blo 389765 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B498079 : Blo 389765 498079 := bstep (se 1 (by rfl) ⟨373559, by rfl⟩ : syracuseStep 498079 = 747119) B747119
theorem B1055207 : Blo 389765 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B8002475 : Blo 389765 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B1481753 : Blo 389765 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B1481935 : Blo 389765 1481935 := bstep (se 1 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 1481935 = 2222903) B2222903
theorem B662735 : Blo 389765 662735 := bstep (se 1 (by rfl) ⟨497051, by rfl⟩ : syracuseStep 662735 = 994103) B994103
theorem B12721369 : Blo 389765 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B1187401 : Blo 389765 1187401 := bstep (se 2 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 1187401 = 890551) B890551
theorem B7610273 : Blo 389765 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B21438431 : Blo 389765 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B1188047 : Blo 389765 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B6365627 : Blo 389765 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B1253971 : Blo 389765 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B664375 : Blo 389765 664375 := bstep (se 1 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 664375 = 996563) B996563
theorem B1877039 : Blo 389765 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B8430749 : Blo 389765 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B11412859 : Blo 389765 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B993161 : Blo 389765 993161 := bstep (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) B744871
theorem B2140219 : Blo 389765 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B1321271 : Blo 389765 1321271 := bstep (se 1 (by rfl) ⟨990953, by rfl⟩ : syracuseStep 1321271 = 1981907) B1981907
theorem B1584463 : Blo 389765 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B1322729 : Blo 389765 1322729 := bstep (se 2 (by rfl) ⟨496023, by rfl⟩ : syracuseStep 1322729 = 992047) B992047
theorem B1486583 : Blo 389765 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1191851 : Blo 389765 1191851 := bstep (se 1 (by rfl) ⟨893888, by rfl⟩ : syracuseStep 1191851 = 1787777) B1787777
theorem B4468769 : Blo 389765 4468769 := bstep (se 2 (by rfl) ⟨1675788, by rfl⟩ : syracuseStep 4468769 = 3351577) B3351577
theorem B471143 : Blo 389765 471143 := bstep (se 1 (by rfl) ⟨353357, by rfl⟩ : syracuseStep 471143 = 706715) B706715
theorem B2961683 : Blo 389765 2961683 := bstep (se 1 (by rfl) ⟨2221262, by rfl⟩ : syracuseStep 2961683 = 4442525) B4442525
theorem B1487555 : Blo 389765 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B2962169 : Blo 389765 2962169 := bstep (se 2 (by rfl) ⟨1110813, by rfl⟩ : syracuseStep 2962169 = 2221627) B2221627
theorem B1487753 : Blo 389765 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B6009851 : Blo 389765 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B1586395 : Blo 389765 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B1488527 : Blo 389765 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B7550891 : Blo 389765 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B4765655 : Blo 389765 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B2963627 : Blo 389765 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B10762469 : Blo 389765 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B1128697 : Blo 389765 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B1259815 : Blo 389765 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B440923 : Blo 389765 440923 := bstep (se 1 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 440923 = 661385) B661385
theorem B1489529 : Blo 389765 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B1817387 : Blo 389765 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B1489711 : Blo 389765 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B441211 : Blo 389765 441211 := bstep (se 1 (by rfl) ⟨330908, by rfl⟩ : syracuseStep 441211 = 661817) B661817
theorem B703399 : Blo 389765 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B6372371 : Blo 389765 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B1326185 : Blo 389765 1326185 := bstep (se 2 (by rfl) ⟨497319, by rfl⟩ : syracuseStep 1326185 = 994639) B994639
theorem B3783905 : Blo 389765 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B441967 : Blo 389765 441967 := bstep (se 1 (by rfl) ⟨331475, by rfl⟩ : syracuseStep 441967 = 662951) B662951
theorem B835247 : Blo 389765 835247 := bstep (se 1 (by rfl) ⟨626435, by rfl⟩ : syracuseStep 835247 = 1252871) B1252871
theorem B442075 : Blo 389765 442075 := bstep (se 1 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 442075 = 663113) B663113
theorem B2965571 : Blo 389765 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B1982717 : Blo 389765 1982717 := bstep (se 3 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 1982717 = 743519) B743519
theorem B835879 : Blo 389765 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B1327913 : Blo 389765 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B5620727 : Blo 389765 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B1131515 : Blo 389765 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1983527 : Blo 389765 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B1328183 : Blo 389765 1328183 := bstep (se 1 (by rfl) ⟨996137, by rfl⟩ : syracuseStep 1328183 = 1992275) B1992275
theorem B3360599 : Blo 389765 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1853585 : Blo 389765 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1493417 : Blo 389765 1493417 := bstep (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) B1120063
theorem B2968001 : Blo 389765 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B838441 : Blo 389765 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B1494071 : Blo 389765 1494071 := bstep (se 1 (by rfl) ⟨1120553, by rfl⟩ : syracuseStep 1494071 = 2241107) B2241107
theorem B1985633 : Blo 389765 1985633 := bstep (se 2 (by rfl) ⟨744612, by rfl⟩ : syracuseStep 1985633 = 1489225) B1489225
theorem B937327 : Blo 389765 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B740839 : Blo 389765 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B904679 : Blo 389765 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B1986443 : Blo 389765 1986443 := bstep (se 1 (by rfl) ⟨1489832, by rfl⟩ : syracuseStep 1986443 = 2979665) B2979665
theorem B937943 : Blo 389765 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B708583 : Blo 389765 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B2674853 : Blo 389765 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B8474867 : Blo 389765 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B3363059 : Blo 389765 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B938633 : Blo 389765 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B1889261 : Blo 389765 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B1889801 : Blo 389765 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B1791503 : Blo 389765 1791503 := bstep (se 1 (by rfl) ⟨1343627, by rfl⟩ : syracuseStep 1791503 = 2687255) B2687255
theorem B1463879 : Blo 389765 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B743033 : Blo 389765 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B448583 : Blo 389765 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B23615621 : Blo 389765 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B9558161 : Blo 389765 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B940787 : Blo 389765 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B940855 : Blo 389765 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B14998445 : Blo 389765 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B104225753 : Blo 389765 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B1335059 : Blo 389765 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B745463 : Blo 389765 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B877049 : Blo 389765 877049 := bstep (se 2 (by rfl) ⟨328893, by rfl⟩ : syracuseStep 877049 = 657787) B657787
theorem B877139 : Blo 389765 877139 := bstep (se 1 (by rfl) ⟨657854, by rfl⟩ : syracuseStep 877139 = 1315709) B1315709
theorem B877319 : Blo 389765 877319 := bstep (se 1 (by rfl) ⟨657989, by rfl⟩ : syracuseStep 877319 = 1315979) B1315979
theorem B877409 : Blo 389765 877409 := bstep (se 2 (by rfl) ⟨329028, by rfl⟩ : syracuseStep 877409 = 658057) B658057
theorem B3335417 : Blo 389765 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B7268131 : Blo 389765 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B878399 : Blo 389765 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B419887 : Blo 389765 419887 := bstep (se 1 (by rfl) ⟨314915, by rfl⟩ : syracuseStep 419887 = 629831) B629831
theorem B878903 : Blo 389765 878903 := bstep (se 1 (by rfl) ⟨659177, by rfl⟩ : syracuseStep 878903 = 1318355) B1318355
theorem B879083 : Blo 389765 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B1993247 : Blo 389765 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B945035 : Blo 389765 945035 := bstep (se 1 (by rfl) ⟨708776, by rfl⟩ : syracuseStep 945035 = 1417553) B1417553
theorem B584873 : Blo 389765 584873 := bstep (se 2 (by rfl) ⟨219327, by rfl⟩ : syracuseStep 584873 = 438655) B438655
theorem B879785 : Blo 389765 879785 := bstep (se 2 (by rfl) ⟨329919, by rfl⟩ : syracuseStep 879785 = 659839) B659839
theorem B2977235 : Blo 389765 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B1666631 : Blo 389765 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B585287 : Blo 389765 585287 := bstep (se 1 (by rfl) ⟨438965, by rfl⟩ : syracuseStep 585287 = 877931) B877931
theorem B880199 : Blo 389765 880199 := bstep (se 1 (by rfl) ⟨660149, by rfl⟩ : syracuseStep 880199 = 1320299) B1320299
theorem B880271 : Blo 389765 880271 := bstep (se 1 (by rfl) ⟨660203, by rfl⟩ : syracuseStep 880271 = 1320407) B1320407
theorem B880361 : Blo 389765 880361 := bstep (se 2 (by rfl) ⟨330135, by rfl⟩ : syracuseStep 880361 = 660271) B660271
theorem B585467 : Blo 389765 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B880379 : Blo 389765 880379 := bstep (se 1 (by rfl) ⟨660284, by rfl⟩ : syracuseStep 880379 = 1320569) B1320569
theorem B10841951 : Blo 389765 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B22998971 : Blo 389765 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B12415169 : Blo 389765 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B586139 : Blo 389765 586139 := bstep (se 1 (by rfl) ⟨439604, by rfl⟩ : syracuseStep 586139 = 879209) B879209
theorem B881387 : Blo 389765 881387 := bstep (se 1 (by rfl) ⟨661040, by rfl⟩ : syracuseStep 881387 = 1322081) B1322081
theorem B389883 : Blo 389765 389883 := bstep (se 1 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 389883 = 584825) B584825
theorem B389951 : Blo 389765 389951 := bstep (se 1 (by rfl) ⟨292463, by rfl⟩ : syracuseStep 389951 = 584927) B584927
theorem B586559 : Blo 389765 586559 := bstep (se 1 (by rfl) ⟨439919, by rfl⟩ : syracuseStep 586559 = 879839) B879839
theorem B389979 : Blo 389765 389979 := bstep (se 1 (by rfl) ⟨292484, by rfl⟩ : syracuseStep 389979 = 584969) B584969
theorem B390047 : Blo 389765 390047 := bstep (se 1 (by rfl) ⟨292535, by rfl⟩ : syracuseStep 390047 = 585071) B585071
theorem B586703 : Blo 389765 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B390127 : Blo 389765 390127 := bstep (se 1 (by rfl) ⟨292595, by rfl⟩ : syracuseStep 390127 = 585191) B585191
theorem B586745 : Blo 389765 586745 := bstep (se 2 (by rfl) ⟨220029, by rfl⟩ : syracuseStep 586745 = 440059) B440059
theorem B881657 : Blo 389765 881657 := bstep (se 2 (by rfl) ⟨330621, by rfl⟩ : syracuseStep 881657 = 661243) B661243
theorem B586793 : Blo 389765 586793 := bstep (se 2 (by rfl) ⟨220047, by rfl⟩ : syracuseStep 586793 = 440095) B440095
theorem B390215 : Blo 389765 390215 := bstep (se 1 (by rfl) ⟨292661, by rfl⟩ : syracuseStep 390215 = 585323) B585323
theorem B586823 : Blo 389765 586823 := bstep (se 1 (by rfl) ⟨440117, by rfl⟩ : syracuseStep 586823 = 880235) B880235
theorem B881747 : Blo 389765 881747 := bstep (se 1 (by rfl) ⟨661310, by rfl⟩ : syracuseStep 881747 = 1322621) B1322621
theorem B390299 : Blo 389765 390299 := bstep (se 1 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 390299 = 585449) B585449
theorem B390395 : Blo 389765 390395 := bstep (se 1 (by rfl) ⟨292796, by rfl⟩ : syracuseStep 390395 = 585593) B585593
theorem B587003 : Blo 389765 587003 := bstep (se 1 (by rfl) ⟨440252, by rfl⟩ : syracuseStep 587003 = 880505) B880505
theorem B881927 : Blo 389765 881927 := bstep (se 1 (by rfl) ⟨661445, by rfl⟩ : syracuseStep 881927 = 1322891) B1322891
theorem B390463 : Blo 389765 390463 := bstep (se 1 (by rfl) ⟨292847, by rfl⟩ : syracuseStep 390463 = 585695) B585695
theorem B390631 : Blo 389765 390631 := bstep (se 1 (by rfl) ⟨292973, by rfl⟩ : syracuseStep 390631 = 585947) B585947
theorem B390639 : Blo 389765 390639 := bstep (se 1 (by rfl) ⟨292979, by rfl⟩ : syracuseStep 390639 = 585959) B585959
theorem B390747 : Blo 389765 390747 := bstep (se 1 (by rfl) ⟨293060, by rfl⟩ : syracuseStep 390747 = 586121) B586121
theorem B882287 : Blo 389765 882287 := bstep (se 1 (by rfl) ⟨661715, by rfl⟩ : syracuseStep 882287 = 1323431) B1323431
theorem B390811 : Blo 389765 390811 := bstep (se 1 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 390811 = 586217) B586217
theorem B390895 : Blo 389765 390895 := bstep (se 1 (by rfl) ⟨293171, by rfl⟩ : syracuseStep 390895 = 586343) B586343
theorem B390983 : Blo 389765 390983 := bstep (se 1 (by rfl) ⟨293237, by rfl⟩ : syracuseStep 390983 = 586475) B586475
theorem B391003 : Blo 389765 391003 := bstep (se 1 (by rfl) ⟨293252, by rfl⟩ : syracuseStep 391003 = 586505) B586505
theorem B391071 : Blo 389765 391071 := bstep (se 1 (by rfl) ⟨293303, by rfl⟩ : syracuseStep 391071 = 586607) B586607
theorem B391239 : Blo 389765 391239 := bstep (se 1 (by rfl) ⟨293429, by rfl⟩ : syracuseStep 391239 = 586859) B586859
theorem B391399 : Blo 389765 391399 := bstep (se 1 (by rfl) ⟨293549, by rfl⟩ : syracuseStep 391399 = 587099) B587099
theorem B391583 : Blo 389765 391583 := bstep (se 1 (by rfl) ⟨293687, by rfl⟩ : syracuseStep 391583 = 587375) B587375
theorem B1669571 : Blo 389765 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B391631 : Blo 389765 391631 := bstep (se 1 (by rfl) ⟨293723, by rfl⟩ : syracuseStep 391631 = 587447) B587447
theorem B588239 : Blo 389765 588239 := bstep (se 1 (by rfl) ⟨441179, by rfl⟩ : syracuseStep 588239 = 882359) B882359
theorem B883151 : Blo 389765 883151 := bstep (se 1 (by rfl) ⟨662363, by rfl⟩ : syracuseStep 883151 = 1324727) B1324727
theorem B1112545 : Blo 389765 1112545 := bstep (se 2 (by rfl) ⟨417204, by rfl⟩ : syracuseStep 1112545 = 834409) B834409
theorem B391655 : Blo 389765 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B5896709 : Blo 389765 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B1669673 : Blo 389765 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B588329 : Blo 389765 588329 := bstep (se 2 (by rfl) ⟨220623, by rfl⟩ : syracuseStep 588329 = 441247) B441247
theorem B883241 : Blo 389765 883241 := bstep (se 2 (by rfl) ⟨331215, by rfl⟩ : syracuseStep 883241 = 662431) B662431
theorem B18086449 : Blo 389765 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B391771 : Blo 389765 391771 := bstep (se 1 (by rfl) ⟨293828, by rfl⟩ : syracuseStep 391771 = 587657) B587657
theorem B391839 : Blo 389765 391839 := bstep (se 1 (by rfl) ⟨293879, by rfl⟩ : syracuseStep 391839 = 587759) B587759
theorem B588521 : Blo 389765 588521 := bstep (se 2 (by rfl) ⟨220695, by rfl⟩ : syracuseStep 588521 = 441391) B441391
theorem B3767107 : Blo 389765 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B392007 : Blo 389765 392007 := bstep (se 1 (by rfl) ⟨294005, by rfl⟩ : syracuseStep 392007 = 588011) B588011
theorem B392047 : Blo 389765 392047 := bstep (se 1 (by rfl) ⟨294035, by rfl⟩ : syracuseStep 392047 = 588071) B588071
theorem B392103 : Blo 389765 392103 := bstep (se 1 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 392103 = 588155) B588155
theorem B392283 : Blo 389765 392283 := bstep (se 1 (by rfl) ⟨294212, by rfl⟩ : syracuseStep 392283 = 588425) B588425
theorem B588905 : Blo 389765 588905 := bstep (se 2 (by rfl) ⟨220839, by rfl⟩ : syracuseStep 588905 = 441679) B441679
theorem B883817 : Blo 389765 883817 := bstep (se 2 (by rfl) ⟨331431, by rfl⟩ : syracuseStep 883817 = 662863) B662863
theorem B392399 : Blo 389765 392399 := bstep (se 1 (by rfl) ⟨294299, by rfl⟩ : syracuseStep 392399 = 588599) B588599
theorem B4455647 : Blo 389765 4455647 := bstep (se 1 (by rfl) ⟨3341735, by rfl⟩ : syracuseStep 4455647 = 6683471) B6683471
theorem B392423 : Blo 389765 392423 := bstep (se 1 (by rfl) ⟨294317, by rfl⟩ : syracuseStep 392423 = 588635) B588635
theorem B589031 : Blo 389765 589031 := bstep (se 1 (by rfl) ⟨441773, by rfl⟩ : syracuseStep 589031 = 883547) B883547
theorem B883943 : Blo 389765 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B2227459 : Blo 389765 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B392519 : Blo 389765 392519 := bstep (se 1 (by rfl) ⟨294389, by rfl⟩ : syracuseStep 392519 = 588779) B588779
theorem B1703263 : Blo 389765 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B392655 : Blo 389765 392655 := bstep (se 1 (by rfl) ⟨294491, by rfl⟩ : syracuseStep 392655 = 588983) B588983
theorem B7175789 : Blo 389765 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B392815 : Blo 389765 392815 := bstep (se 1 (by rfl) ⟨294611, by rfl⟩ : syracuseStep 392815 = 589223) B589223
theorem B392871 : Blo 389765 392871 := bstep (se 1 (by rfl) ⟨294653, by rfl⟩ : syracuseStep 392871 = 589307) B589307
theorem B589535 : Blo 389765 589535 := bstep (se 1 (by rfl) ⟨442151, by rfl⟩ : syracuseStep 589535 = 884303) B884303
theorem B884447 : Blo 389765 884447 := bstep (se 1 (by rfl) ⟨663335, by rfl⟩ : syracuseStep 884447 = 1326671) B1326671
theorem B392935 : Blo 389765 392935 := bstep (se 1 (by rfl) ⟨294701, by rfl⟩ : syracuseStep 392935 = 589403) B589403
theorem B2981609 : Blo 389765 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B589577 : Blo 389765 589577 := bstep (se 2 (by rfl) ⟨221091, by rfl⟩ : syracuseStep 589577 = 442183) B442183
theorem B392991 : Blo 389765 392991 := bstep (se 1 (by rfl) ⟨294743, by rfl⟩ : syracuseStep 392991 = 589487) B589487
theorem B884519 : Blo 389765 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B393071 : Blo 389765 393071 := bstep (se 1 (by rfl) ⟨294803, by rfl⟩ : syracuseStep 393071 = 589607) B589607
theorem B393127 : Blo 389765 393127 := bstep (se 1 (by rfl) ⟨294845, by rfl⟩ : syracuseStep 393127 = 589691) B589691
theorem B393343 : Blo 389765 393343 := bstep (se 1 (by rfl) ⟨295007, by rfl⟩ : syracuseStep 393343 = 590015) B590015
theorem B1114505 : Blo 389765 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B393627 : Blo 389765 393627 := bstep (se 1 (by rfl) ⟨295220, by rfl⟩ : syracuseStep 393627 = 590441) B590441
theorem B393631 : Blo 389765 393631 := bstep (se 1 (by rfl) ⟨295223, by rfl⟩ : syracuseStep 393631 = 590447) B590447
theorem B1114631 : Blo 389765 1114631 := bstep (se 1 (by rfl) ⟨835973, by rfl⟩ : syracuseStep 1114631 = 1671947) B1671947
theorem B885275 : Blo 389765 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B590363 : Blo 389765 590363 := bstep (se 1 (by rfl) ⟨442772, by rfl⟩ : syracuseStep 590363 = 885545) B885545
theorem B754343 : Blo 389765 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B885455 : Blo 389765 885455 := bstep (se 1 (by rfl) ⟨664091, by rfl⟩ : syracuseStep 885455 = 1328183) B1328183
theorem B590543 : Blo 389765 590543 := bstep (se 1 (by rfl) ⟨442907, by rfl⟩ : syracuseStep 590543 = 885815) B885815
theorem B12059603 : Blo 389765 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B885833 : Blo 389765 885833 := bstep (se 2 (by rfl) ⟨332187, by rfl⟩ : syracuseStep 885833 = 664375) B664375
theorem B625295 : Blo 389765 625295 := bstep (se 1 (by rfl) ⟨468971, by rfl⟩ : syracuseStep 625295 = 937943) B937943
theorem B2853625 : Blo 389765 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B6687845 : Blo 389765 6687845 := bstep (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) B1253971
theorem B10488997 : Blo 389765 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B986651 : Blo 389765 986651 := bstep (se 1 (by rfl) ⟨739988, by rfl⟩ : syracuseStep 986651 = 1479977) B1479977
theorem B3903677 : Blo 389765 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B1249769 : Blo 389765 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B627191 : Blo 389765 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B9998963 : Blo 389765 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B987785 : Blo 389765 987785 := bstep (se 2 (by rfl) ⟨370419, by rfl⟩ : syracuseStep 987785 = 740839) B740839
theorem B987835 : Blo 389765 987835 := bstep (se 1 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 987835 = 1481753) B1481753
theorem B10064573 : Blo 389765 10064573 := bstep (se 3 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 10064573 = 3774215) B3774215
theorem B660649 : Blo 389765 660649 := bstep (se 2 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 660649 = 495487) B495487
theorem B890039 : Blo 389765 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B14292287 : Blo 389765 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B792031 : Blo 389765 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B1251359 : Blo 389765 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B7543205 : Blo 389765 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B8460773 : Blo 389765 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B662107 : Blo 389765 662107 := bstep (se 1 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 662107 = 993161) B993161
theorem B1317761 : Blo 389765 1317761 := bstep (se 2 (by rfl) ⟨494160, by rfl⟩ : syracuseStep 1317761 = 988321) B988321
theorem B630023 : Blo 389765 630023 := bstep (se 1 (by rfl) ⟨472517, by rfl⟩ : syracuseStep 630023 = 945035) B945035
theorem B2236025 : Blo 389765 2236025 := bstep (se 2 (by rfl) ⟨838509, by rfl⟩ : syracuseStep 2236025 = 1677019) B1677019
theorem B991055 : Blo 389765 991055 := bstep (se 1 (by rfl) ⟨743291, by rfl⟩ : syracuseStep 991055 = 1486583) B1486583
theorem B794567 : Blo 389765 794567 := bstep (se 1 (by rfl) ⟨595925, by rfl⟩ : syracuseStep 794567 = 1191851) B1191851
theorem B1974455 : Blo 389765 1974455 := bstep (se 1 (by rfl) ⟨1480841, by rfl⟩ : syracuseStep 1974455 = 2961683) B2961683
theorem B1679753 : Blo 389765 1679753 := bstep (se 2 (by rfl) ⟨629907, by rfl⟩ : syracuseStep 1679753 = 1259815) B1259815
theorem B991703 : Blo 389765 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B1974779 : Blo 389765 1974779 := bstep (se 1 (by rfl) ⟨1481084, by rfl⟩ : syracuseStep 1974779 = 2962169) B2962169
theorem B664105 : Blo 389765 664105 := bstep (se 2 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 664105 = 498079) B498079
theorem B991835 : Blo 389765 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B1483393 : Blo 389765 1483393 := bstep (se 2 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 1483393 = 1112545) B1112545
theorem B4006567 : Blo 389765 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1254473 : Blo 389765 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B5022809 : Blo 389765 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B992351 : Blo 389765 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B1975751 : Blo 389765 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B1975913 : Blo 389765 1975913 := bstep (se 2 (by rfl) ⟨740967, by rfl⟩ : syracuseStep 1975913 = 1481935) B1481935
theorem B993019 : Blo 389765 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B2271017 : Blo 389765 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B1583201 : Blo 389765 1583201 := bstep (se 2 (by rfl) ⟨593700, by rfl⟩ : syracuseStep 1583201 = 1187401) B1187401
theorem B1977047 : Blo 389765 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B1321811 : Blo 389765 1321811 := bstep (se 1 (by rfl) ⟨991358, by rfl⟩ : syracuseStep 1321811 = 1982717) B1982717
theorem B2239397 : Blo 389765 2239397 := bstep (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) B419887
theorem B1256381 : Blo 389765 1256381 := bstep (se 3 (by rfl) ⟨235571, by rfl⟩ : syracuseStep 1256381 = 471143) B471143
theorem B1486127 : Blo 389765 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B3747151 : Blo 389765 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B1813843 : Blo 389765 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B1322351 : Blo 389765 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B2240399 : Blo 389765 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B995611 : Blo 389765 995611 := bstep (se 1 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 995611 = 1493417) B1493417
theorem B1978667 : Blo 389765 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B15217145 : Blo 389765 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B996047 : Blo 389765 996047 := bstep (se 1 (by rfl) ⟨747035, by rfl⟩ : syracuseStep 996047 = 1494071) B1494071
theorem B1323755 : Blo 389765 1323755 := bstep (se 1 (by rfl) ⟨992816, by rfl⟩ : syracuseStep 1323755 = 1985633) B1985633
theorem B603119 : Blo 389765 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B1324295 : Blo 389765 1324295 := bstep (se 1 (by rfl) ⟨993221, by rfl⟩ : syracuseStep 1324295 = 1986443) B1986443
theorem B1783235 : Blo 389765 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B5649911 : Blo 389765 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B2242039 : Blo 389765 2242039 := bstep (se 1 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 2242039 = 3363059) B3363059
theorem B1259507 : Blo 389765 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B440383 : Blo 389765 440383 := bstep (se 1 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 440383 = 660575) B660575
theorem B1259867 : Blo 389765 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1194335 : Blo 389765 1194335 := bstep (se 1 (by rfl) ⟨895751, by rfl⟩ : syracuseStep 1194335 = 1791503) B1791503
theorem B15743747 : Blo 389765 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B6372107 : Blo 389765 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B4471685 : Blo 389765 4471685 := bstep (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) B838441
theorem B1981421 : Blo 389765 1981421 := bstep (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) B743033
theorem B2112617 : Blo 389765 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B69483835 : Blo 389765 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B441823 : Blo 389765 441823 := bstep (se 1 (by rfl) ⟨331367, by rfl⟩ : syracuseStep 441823 = 662735) B662735
theorem B1196221 : Blo 389765 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B4243751 : Blo 389765 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B79086293 : Blo 389765 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B5620499 : Blo 389765 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B10012085 : Blo 389765 10012085 := bstep (se 5 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 10012085 = 938633) B938633
theorem B1328831 : Blo 389765 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B1984823 : Blo 389765 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B7227967 : Blo 389765 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B8276779 : Blo 389765 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1986281 : Blo 389765 1986281 := bstep (se 2 (by rfl) ⟨744855, by rfl⟩ : syracuseStep 1986281 = 1489711) B1489711
theorem B937865 : Blo 389765 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B3329981 : Blo 389765 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B5033927 : Blo 389765 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B16961825 : Blo 389765 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B2969945 : Blo 389765 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B4248247 : Blo 389765 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B2970431 : Blo 389765 2970431 := bstep (se 1 (by rfl) ⟨2227823, by rfl⟩ : syracuseStep 2970431 = 4455647) B4455647
theorem B1987739 : Blo 389765 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B1987901 : Blo 389765 1987901 := bstep (se 3 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 1987901 = 745463) B745463
theorem B19355041 : Blo 389765 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B940171 : Blo 389765 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B6019717 : Blo 389765 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B9690841 : Blo 389765 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B1990979 : Blo 389765 1990979 := bstep (se 1 (by rfl) ⟨1493234, by rfl⟩ : syracuseStep 1990979 = 2986469) B2986469
theorem B943007 : Blo 389765 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B746671 : Blo 389765 746671 := bstep (se 1 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 746671 = 1120007) B1120007
theorem B5334427 : Blo 389765 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B746921 : Blo 389765 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B5334983 : Blo 389765 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B2975777 : Blo 389765 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B5073515 : Blo 389765 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B944777 : Blo 389765 944777 := bstep (se 2 (by rfl) ⟨354291, by rfl⟩ : syracuseStep 944777 = 708583) B708583
theorem B584699 : Blo 389765 584699 := bstep (se 1 (by rfl) ⟨438524, by rfl⟩ : syracuseStep 584699 = 877049) B877049
theorem B584759 : Blo 389765 584759 := bstep (se 1 (by rfl) ⟨438569, by rfl⟩ : syracuseStep 584759 = 877139) B877139
theorem B584879 : Blo 389765 584879 := bstep (se 1 (by rfl) ⟨438659, by rfl⟩ : syracuseStep 584879 = 877319) B877319
theorem B584939 : Blo 389765 584939 := bstep (se 1 (by rfl) ⟨438704, by rfl⟩ : syracuseStep 584939 = 877409) B877409
theorem B2223611 : Blo 389765 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B585599 : Blo 389765 585599 := bstep (se 1 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 585599 = 878399) B878399
theorem B2813885 : Blo 389765 2813885 := bstep (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) B1055207
theorem B585935 : Blo 389765 585935 := bstep (se 1 (by rfl) ⟨439451, by rfl⟩ : syracuseStep 585935 = 878903) B878903
theorem B880847 : Blo 389765 880847 := bstep (se 1 (by rfl) ⟨660635, by rfl⟩ : syracuseStep 880847 = 1321271) B1321271
theorem B586055 : Blo 389765 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B389915 : Blo 389765 389915 := bstep (se 1 (by rfl) ⟨292436, by rfl⟩ : syracuseStep 389915 = 584873) B584873
theorem B586523 : Blo 389765 586523 := bstep (se 1 (by rfl) ⟨439892, by rfl⟩ : syracuseStep 586523 = 879785) B879785
theorem B2978693 : Blo 389765 2978693 := bstep (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) B558505
theorem B1111087 : Blo 389765 1111087 := bstep (se 1 (by rfl) ⟨833315, by rfl⟩ : syracuseStep 1111087 = 1666631) B1666631
theorem B390191 : Blo 389765 390191 := bstep (se 1 (by rfl) ⟨292643, by rfl⟩ : syracuseStep 390191 = 585287) B585287
theorem B586799 : Blo 389765 586799 := bstep (se 1 (by rfl) ⟨440099, by rfl⟩ : syracuseStep 586799 = 880199) B880199
theorem B586847 : Blo 389765 586847 := bstep (se 1 (by rfl) ⟨440135, by rfl⟩ : syracuseStep 586847 = 880271) B880271
theorem B586907 : Blo 389765 586907 := bstep (se 1 (by rfl) ⟨440180, by rfl⟩ : syracuseStep 586907 = 880361) B880361
theorem B881819 : Blo 389765 881819 := bstep (se 1 (by rfl) ⟨661364, by rfl⟩ : syracuseStep 881819 = 1322729) B1322729
theorem B390311 : Blo 389765 390311 := bstep (se 1 (by rfl) ⟨292733, by rfl⟩ : syracuseStep 390311 = 585467) B585467
theorem B586919 : Blo 389765 586919 := bstep (se 1 (by rfl) ⟨440189, by rfl⟩ : syracuseStep 586919 = 880379) B880379
theorem B15332647 : Blo 389765 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2979179 : Blo 389765 2979179 := bstep (se 1 (by rfl) ⟨2234384, by rfl⟩ : syracuseStep 2979179 = 4468769) B4468769
theorem B390759 : Blo 389765 390759 := bstep (se 1 (by rfl) ⟨293069, by rfl⟩ : syracuseStep 390759 = 586139) B586139
theorem B587591 : Blo 389765 587591 := bstep (se 1 (by rfl) ⟨440693, by rfl⟩ : syracuseStep 587591 = 881387) B881387
theorem B391039 : Blo 389765 391039 := bstep (se 1 (by rfl) ⟨293279, by rfl⟩ : syracuseStep 391039 = 586559) B586559
theorem B391135 : Blo 389765 391135 := bstep (se 1 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 391135 = 586703) B586703
theorem B391163 : Blo 389765 391163 := bstep (se 1 (by rfl) ⟨293372, by rfl⟩ : syracuseStep 391163 = 586745) B586745
theorem B587771 : Blo 389765 587771 := bstep (se 1 (by rfl) ⟨440828, by rfl⟩ : syracuseStep 587771 = 881657) B881657
theorem B391195 : Blo 389765 391195 := bstep (se 1 (by rfl) ⟨293396, by rfl⟩ : syracuseStep 391195 = 586793) B586793
theorem B391215 : Blo 389765 391215 := bstep (se 1 (by rfl) ⟨293411, by rfl⟩ : syracuseStep 391215 = 586823) B586823
theorem B587831 : Blo 389765 587831 := bstep (se 1 (by rfl) ⟨440873, by rfl⟩ : syracuseStep 587831 = 881747) B881747
theorem B24115265 : Blo 389765 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B587897 : Blo 389765 587897 := bstep (se 2 (by rfl) ⟨220461, by rfl⟩ : syracuseStep 587897 = 440923) B440923
theorem B391335 : Blo 389765 391335 := bstep (se 1 (by rfl) ⟨293501, by rfl⟩ : syracuseStep 391335 = 587003) B587003
theorem B587951 : Blo 389765 587951 := bstep (se 1 (by rfl) ⟨440963, by rfl⟩ : syracuseStep 587951 = 881927) B881927
theorem B588191 : Blo 389765 588191 := bstep (se 1 (by rfl) ⟨441143, by rfl⟩ : syracuseStep 588191 = 882287) B882287
theorem B588281 : Blo 389765 588281 := bstep (se 2 (by rfl) ⟨220605, by rfl⟩ : syracuseStep 588281 = 441211) B441211
theorem B3177103 : Blo 389765 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B7174979 : Blo 389765 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B1113047 : Blo 389765 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B392159 : Blo 389765 392159 := bstep (se 1 (by rfl) ⟨294119, by rfl⟩ : syracuseStep 392159 = 588239) B588239
theorem B588767 : Blo 389765 588767 := bstep (se 1 (by rfl) ⟨441575, by rfl⟩ : syracuseStep 588767 = 883151) B883151
theorem B3931139 : Blo 389765 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B1113115 : Blo 389765 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B392219 : Blo 389765 392219 := bstep (se 1 (by rfl) ⟨294164, by rfl⟩ : syracuseStep 392219 = 588329) B588329
theorem B588827 : Blo 389765 588827 := bstep (se 1 (by rfl) ⟨441620, by rfl⟩ : syracuseStep 588827 = 883241) B883241
theorem B392347 : Blo 389765 392347 := bstep (se 1 (by rfl) ⟨294260, by rfl⟩ : syracuseStep 392347 = 588521) B588521
theorem B1211591 : Blo 389765 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B392603 : Blo 389765 392603 := bstep (se 1 (by rfl) ⟨294452, by rfl⟩ : syracuseStep 392603 = 588905) B588905
theorem B589211 : Blo 389765 589211 := bstep (se 1 (by rfl) ⟨441908, by rfl⟩ : syracuseStep 589211 = 883817) B883817
theorem B884123 : Blo 389765 884123 := bstep (se 1 (by rfl) ⟨663092, by rfl⟩ : syracuseStep 884123 = 1326185) B1326185
theorem B589289 : Blo 389765 589289 := bstep (se 2 (by rfl) ⟨220983, by rfl⟩ : syracuseStep 589289 = 441967) B441967
theorem B2522603 : Blo 389765 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B392687 : Blo 389765 392687 := bstep (se 1 (by rfl) ⟨294515, by rfl⟩ : syracuseStep 392687 = 589031) B589031
theorem B589295 : Blo 389765 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B589433 : Blo 389765 589433 := bstep (se 2 (by rfl) ⟨221037, by rfl⟩ : syracuseStep 589433 = 442075) B442075
theorem B4783859 : Blo 389765 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B556831 : Blo 389765 556831 := bstep (se 1 (by rfl) ⟨417623, by rfl⟩ : syracuseStep 556831 = 835247) B835247
theorem B393023 : Blo 389765 393023 := bstep (se 1 (by rfl) ⟨294767, by rfl⟩ : syracuseStep 393023 = 589535) B589535
theorem B589631 : Blo 389765 589631 := bstep (se 1 (by rfl) ⟨442223, by rfl⟩ : syracuseStep 589631 = 884447) B884447
theorem B393051 : Blo 389765 393051 := bstep (se 1 (by rfl) ⟨294788, by rfl⟩ : syracuseStep 393051 = 589577) B589577
theorem B589679 : Blo 389765 589679 := bstep (se 1 (by rfl) ⟨442259, by rfl⟩ : syracuseStep 589679 = 884519) B884519
theorem B590183 : Blo 389765 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B393575 : Blo 389765 393575 := bstep (se 1 (by rfl) ⟨295181, by rfl⟩ : syracuseStep 393575 = 590363) B590363
theorem B590303 : Blo 389765 590303 := bstep (se 1 (by rfl) ⟨442727, by rfl⟩ : syracuseStep 590303 = 885455) B885455
theorem B393695 : Blo 389765 393695 := bstep (se 1 (by rfl) ⟨295271, by rfl⟩ : syracuseStep 393695 = 590543) B590543
theorem B52724195 : Blo 389765 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B590555 : Blo 389765 590555 := bstep (se 1 (by rfl) ⟨442916, by rfl⟩ : syracuseStep 590555 = 885833) B885833
theorem B885473 : Blo 389765 885473 := bstep (se 2 (by rfl) ⟨332052, by rfl⟩ : syracuseStep 885473 = 664105) B664105
theorem B885887 : Blo 389765 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B7112569 : Blo 389765 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B4458563 : Blo 389765 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B657767 : Blo 389765 657767 := bstep (se 1 (by rfl) ⟨493325, by rfl⟩ : syracuseStep 657767 = 986651) B986651
theorem B625243 : Blo 389765 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B1608317 : Blo 389765 1608317 := bstep (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) B603119
theorem B11307883 : Blo 389765 11307883 := bstep (se 1 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 11307883 = 16961825) B16961825
theorem B658523 : Blo 389765 658523 := bstep (se 1 (by rfl) ⟨493892, by rfl⟩ : syracuseStep 658523 = 987785) B987785
theorem B9637289 : Blo 389765 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B21368357 : Blo 389765 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B3804833 : Blo 389765 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B5640515 : Blo 389765 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B660703 : Blo 389765 660703 := bstep (se 1 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 660703 = 991055) B991055
theorem B1316303 : Blo 389765 1316303 := bstep (se 1 (by rfl) ⟨987227, by rfl⟩ : syracuseStep 1316303 = 1974455) B1974455
theorem B1119835 : Blo 389765 1119835 := bstep (se 1 (by rfl) ⟨839876, by rfl⟩ : syracuseStep 1119835 = 1679753) B1679753
theorem B661135 : Blo 389765 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B1316519 : Blo 389765 1316519 := bstep (se 1 (by rfl) ⟨987389, by rfl⟩ : syracuseStep 1316519 = 1974779) B1974779
theorem B661223 : Blo 389765 661223 := bstep (se 1 (by rfl) ⟨495917, by rfl⟩ : syracuseStep 661223 = 991835) B991835
theorem B3348539 : Blo 389765 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B661567 : Blo 389765 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B1317113 : Blo 389765 1317113 := bstep (se 2 (by rfl) ⟨493917, by rfl⟩ : syracuseStep 1317113 = 987835) B987835
theorem B1317167 : Blo 389765 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B1317275 : Blo 389765 1317275 := bstep (se 1 (by rfl) ⟨987956, by rfl⟩ : syracuseStep 1317275 = 1975913) B1975913
theorem B1481449 : Blo 389765 1481449 := bstep (se 2 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 1481449 = 1111087) B1111087
theorem B1055467 : Blo 389765 1055467 := bstep (se 1 (by rfl) ⟨791600, by rfl⟩ : syracuseStep 1055467 = 1583201) B1583201
theorem B370580453 : Blo 389765 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B3382343 : Blo 389765 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B629851 : Blo 389765 629851 := bstep (se 1 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 629851 = 944777) B944777
theorem B1318031 : Blo 389765 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B1056041 : Blo 389765 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B2989385 : Blo 389765 2989385 := bstep (se 2 (by rfl) ⟨1121019, by rfl⟩ : syracuseStep 2989385 = 2242039) B2242039
theorem B990751 : Blo 389765 990751 := bstep (se 1 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 990751 = 1486127) B1486127
theorem B1482407 : Blo 389765 1482407 := bstep (se 1 (by rfl) ⟨1111805, by rfl⟩ : syracuseStep 1482407 = 2223611) B2223611
theorem B1875923 : Blo 389765 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1253561 : Blo 389765 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B1319111 : Blo 389765 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B664031 : Blo 389765 664031 := bstep (se 1 (by rfl) ⟨498023, by rfl⟩ : syracuseStep 664031 = 996047) B996047
theorem B1680061 : Blo 389765 1680061 := bstep (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) B630023
theorem B4236137 : Blo 389765 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B1188823 : Blo 389765 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B1484153 : Blo 389765 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B796223 : Blo 389765 796223 := bstep (se 1 (by rfl) ⟨597167, by rfl⟩ : syracuseStep 796223 = 1194335) B1194335
theorem B10495831 : Blo 389765 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B1320947 : Blo 389765 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B12921121 : Blo 389765 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B1681735 : Blo 389765 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B3189239 : Blo 389765 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B2829167 : Blo 389765 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B502895 : Blo 389765 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B3746999 : Blo 389765 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B8039735 : Blo 389765 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1977857 : Blo 389765 1977857 := bstep (se 2 (by rfl) ⟨741696, by rfl⟩ : syracuseStep 1977857 = 1483393) B1483393
theorem B1323215 : Blo 389765 1323215 := bstep (se 1 (by rfl) ⟨992411, by rfl⟩ : syracuseStep 1323215 = 1984823) B1984823
theorem B995561 : Blo 389765 995561 := bstep (se 2 (by rfl) ⟨373335, by rfl⟩ : syracuseStep 995561 = 746671) B746671
theorem B1324025 : Blo 389765 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B1324187 : Blo 389765 1324187 := bstep (se 1 (by rfl) ⟨993140, by rfl⟩ : syracuseStep 1324187 = 1986281) B1986281
theorem B3355951 : Blo 389765 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B2602451 : Blo 389765 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B1979963 : Blo 389765 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B833179 : Blo 389765 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B6665975 : Blo 389765 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B2373437 : Blo 389765 2373437 := bstep (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) B890039
theorem B1980287 : Blo 389765 1980287 := bstep (se 1 (by rfl) ⟨1485215, by rfl⟩ : syracuseStep 1980287 = 2970431) B2970431
theorem B1325159 : Blo 389765 1325159 := bstep (se 1 (by rfl) ⟨993869, by rfl⟩ : syracuseStep 1325159 = 1987739) B1987739
theorem B1325267 : Blo 389765 1325267 := bstep (se 1 (by rfl) ⟨993950, by rfl⟩ : syracuseStep 1325267 = 1987901) B1987901
theorem B834239 : Blo 389765 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B5028803 : Blo 389765 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B4996201 : Blo 389765 4996201 := bstep (se 2 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 4996201 = 3747151) B3747151
theorem B1490683 : Blo 389765 1490683 := bstep (se 1 (by rfl) ⟨1118012, by rfl⟩ : syracuseStep 1490683 = 2236025) B2236025
theorem B3358685 : Blo 389765 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1327319 : Blo 389765 1327319 := bstep (se 1 (by rfl) ⟨995489, by rfl⟩ : syracuseStep 1327319 = 1990979) B1990979
theorem B1327481 : Blo 389765 1327481 := bstep (se 2 (by rfl) ⟨497805, by rfl⟩ : syracuseStep 1327481 = 995611) B995611
theorem B836315 : Blo 389765 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B3556655 : Blo 389765 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B1983851 : Blo 389765 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B25806721 : Blo 389765 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B1492931 : Blo 389765 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B837587 : Blo 389765 837587 := bstep (se 1 (by rfl) ⟨628190, by rfl⟩ : syracuseStep 837587 = 1256381) B1256381
theorem B1493599 : Blo 389765 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B10144763 : Blo 389765 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B1985795 : Blo 389765 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B1986119 : Blo 389765 1986119 := bstep (se 1 (by rfl) ⟨1489589, by rfl⟩ : syracuseStep 1986119 = 2979179) B2979179
theorem B16076843 : Blo 389765 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B839911 : Blo 389765 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B4248071 : Blo 389765 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B742031 : Blo 389765 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B807727 : Blo 389765 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B742441 : Blo 389765 742441 := bstep (se 2 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 742441 = 556831) B556831
theorem B2118845 : Blo 389765 2118845 := bstep (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) B794567
theorem B1594961 : Blo 389765 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B743003 : Blo 389765 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B743087 : Blo 389765 743087 := bstep (se 1 (by rfl) ⟨557315, by rfl⟩ : syracuseStep 743087 = 1114631) B1114631
theorem B6674723 : Blo 389765 6674723 := bstep (se 1 (by rfl) ⟨5006042, by rfl⟩ : syracuseStep 6674723 = 10012085) B10012085
theorem B416863 : Blo 389765 416863 := bstep (se 1 (by rfl) ⟨312647, by rfl⟩ : syracuseStep 416863 = 625295) B625295
theorem B2514685 : Blo 389765 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B2219987 : Blo 389765 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B418127 : Blo 389765 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B6709715 : Blo 389765 6709715 := bstep (se 1 (by rfl) ⟨5032286, by rfl⟩ : syracuseStep 6709715 = 10064573) B10064573
theorem B9528191 : Blo 389765 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B11035705 : Blo 389765 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1991789 : Blo 389765 1991789 := bstep (se 3 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 1991789 = 746921) B746921
theorem B13985329 : Blo 389765 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B2418457 : Blo 389765 2418457 := bstep (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) B1813843
theorem B878507 : Blo 389765 878507 := bstep (se 1 (by rfl) ⟨658880, by rfl⟩ : syracuseStep 878507 = 1317761) B1317761
theorem B6056045 : Blo 389765 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B5664329 : Blo 389765 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B880865 : Blo 389765 880865 := bstep (se 2 (by rfl) ⟨330324, by rfl⟩ : syracuseStep 880865 = 660649) B660649
theorem B20443529 : Blo 389765 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B881207 : Blo 389765 881207 := bstep (se 1 (by rfl) ⟨660905, by rfl⟩ : syracuseStep 881207 = 1321811) B1321811
theorem B389799 : Blo 389765 389799 := bstep (se 1 (by rfl) ⟨292349, by rfl⟩ : syracuseStep 389799 = 584699) B584699
theorem B389839 : Blo 389765 389839 := bstep (se 1 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 389839 = 584759) B584759
theorem B389919 : Blo 389765 389919 := bstep (se 1 (by rfl) ⟨292439, by rfl⟩ : syracuseStep 389919 = 584879) B584879
theorem B389959 : Blo 389765 389959 := bstep (se 1 (by rfl) ⟨292469, by rfl⟩ : syracuseStep 389959 = 584939) B584939
theorem B881567 : Blo 389765 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B390399 : Blo 389765 390399 := bstep (se 1 (by rfl) ⟨292799, by rfl⟩ : syracuseStep 390399 = 585599) B585599
theorem B587177 : Blo 389765 587177 := bstep (se 2 (by rfl) ⟨220191, by rfl⟩ : syracuseStep 587177 = 440383) B440383
theorem B390623 : Blo 389765 390623 := bstep (se 1 (by rfl) ⟨292967, by rfl⟩ : syracuseStep 390623 = 585935) B585935
theorem B587231 : Blo 389765 587231 := bstep (se 1 (by rfl) ⟨440423, by rfl⟩ : syracuseStep 587231 = 880847) B880847
theorem B390703 : Blo 389765 390703 := bstep (se 1 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 390703 = 586055) B586055
theorem B882503 : Blo 389765 882503 := bstep (se 1 (by rfl) ⟨661877, by rfl⟩ : syracuseStep 882503 = 1323755) B1323755
theorem B391015 : Blo 389765 391015 := bstep (se 1 (by rfl) ⟨293261, by rfl⟩ : syracuseStep 391015 = 586523) B586523
theorem B391199 : Blo 389765 391199 := bstep (se 1 (by rfl) ⟨293399, by rfl⟩ : syracuseStep 391199 = 586799) B586799
theorem B391231 : Blo 389765 391231 := bstep (se 1 (by rfl) ⟨293423, by rfl⟩ : syracuseStep 391231 = 586847) B586847
theorem B391271 : Blo 389765 391271 := bstep (se 1 (by rfl) ⟨293453, by rfl⟩ : syracuseStep 391271 = 586907) B586907
theorem B587879 : Blo 389765 587879 := bstep (se 1 (by rfl) ⟨440909, by rfl⟩ : syracuseStep 587879 = 881819) B881819
theorem B391279 : Blo 389765 391279 := bstep (se 1 (by rfl) ⟨293459, by rfl⟩ : syracuseStep 391279 = 586919) B586919
theorem B882809 : Blo 389765 882809 := bstep (se 2 (by rfl) ⟨331053, by rfl⟩ : syracuseStep 882809 = 662107) B662107
theorem B8026289 : Blo 389765 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B882863 : Blo 389765 882863 := bstep (se 1 (by rfl) ⟨662147, by rfl⟩ : syracuseStep 882863 = 1324295) B1324295
theorem B3766607 : Blo 389765 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B391727 : Blo 389765 391727 := bstep (se 1 (by rfl) ⟨293795, by rfl⟩ : syracuseStep 391727 = 587591) B587591
theorem B391847 : Blo 389765 391847 := bstep (se 1 (by rfl) ⟨293885, by rfl⟩ : syracuseStep 391847 = 587771) B587771
theorem B391887 : Blo 389765 391887 := bstep (se 1 (by rfl) ⟨293915, by rfl⟩ : syracuseStep 391887 = 587831) B587831
theorem B391931 : Blo 389765 391931 := bstep (se 1 (by rfl) ⟨293948, by rfl⟩ : syracuseStep 391931 = 587897) B587897
theorem B391967 : Blo 389765 391967 := bstep (se 1 (by rfl) ⟨293975, by rfl⟩ : syracuseStep 391967 = 587951) B587951
theorem B392127 : Blo 389765 392127 := bstep (se 1 (by rfl) ⟨294095, by rfl⟩ : syracuseStep 392127 = 588191) B588191
theorem B392187 : Blo 389765 392187 := bstep (se 1 (by rfl) ⟨294140, by rfl⟩ : syracuseStep 392187 = 588281) B588281
theorem B4783319 : Blo 389765 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B2981123 : Blo 389765 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B589097 : Blo 389765 589097 := bstep (se 2 (by rfl) ⟨220911, by rfl⟩ : syracuseStep 589097 = 441823) B441823
theorem B392511 : Blo 389765 392511 := bstep (se 1 (by rfl) ⟨294383, by rfl⟩ : syracuseStep 392511 = 588767) B588767
theorem B2620759 : Blo 389765 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B392551 : Blo 389765 392551 := bstep (se 1 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 392551 = 588827) B588827
theorem B1408411 : Blo 389765 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B392807 : Blo 389765 392807 := bstep (se 1 (by rfl) ⟨294605, by rfl⟩ : syracuseStep 392807 = 589211) B589211
theorem B589415 : Blo 389765 589415 := bstep (se 1 (by rfl) ⟨442061, by rfl⟩ : syracuseStep 589415 = 884123) B884123
theorem B392859 : Blo 389765 392859 := bstep (se 1 (by rfl) ⟨294644, by rfl⟩ : syracuseStep 392859 = 589289) B589289
theorem B392863 : Blo 389765 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B392955 : Blo 389765 392955 := bstep (se 1 (by rfl) ⟨294716, by rfl⟩ : syracuseStep 392955 = 589433) B589433
theorem B393087 : Blo 389765 393087 := bstep (se 1 (by rfl) ⟨294815, by rfl⟩ : syracuseStep 393087 = 589631) B589631
theorem B393119 : Blo 389765 393119 := bstep (se 1 (by rfl) ⟨294839, by rfl⟩ : syracuseStep 393119 = 589679) B589679
theorem B884879 : Blo 389765 884879 := bstep (se 1 (by rfl) ⟨663659, by rfl⟩ : syracuseStep 884879 = 1327319) B1327319
theorem B393455 : Blo 389765 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B884987 : Blo 389765 884987 := bstep (se 1 (by rfl) ⟨663740, by rfl⟩ : syracuseStep 884987 = 1327481) B1327481
theorem B393535 : Blo 389765 393535 := bstep (se 1 (by rfl) ⟨295151, by rfl⟩ : syracuseStep 393535 = 590303) B590303
theorem B557543 : Blo 389765 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B393703 : Blo 389765 393703 := bstep (se 1 (by rfl) ⟨295277, by rfl⟩ : syracuseStep 393703 = 590555) B590555
theorem B590315 : Blo 389765 590315 := bstep (se 1 (by rfl) ⟨442736, by rfl⟩ : syracuseStep 590315 = 885473) B885473
theorem B3342829 : Blo 389765 3342829 := bstep (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) B1253561
theorem B590591 : Blo 389765 590591 := bstep (se 1 (by rfl) ⟨442943, by rfl⟩ : syracuseStep 590591 = 885887) B885887
theorem B14714273 : Blo 389765 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B18647105 : Blo 389765 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B6424859 : Blo 389765 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B13994441 : Blo 389765 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B34408961 : Blo 389765 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B10717895 : Blo 389765 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B494687 : Blo 389765 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B1412563 : Blo 389765 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B4460021 : Blo 389765 4460021 := bstep (se 5 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 4460021 = 418127) B418127
theorem B495335 : Blo 389765 495335 := bstep (se 1 (by rfl) ⟨371501, by rfl⟩ : syracuseStep 495335 = 743003) B743003
theorem B495391 : Blo 389765 495391 := bstep (se 1 (by rfl) ⟨371543, by rfl⟩ : syracuseStep 495391 = 743087) B743087
theorem B15077177 : Blo 389765 15077177 := bstep (se 2 (by rfl) ⟨5653941, by rfl⟩ : syracuseStep 15077177 = 11307883) B11307883
theorem B2232359 : Blo 389765 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B988271 : Blo 389765 988271 := bstep (se 1 (by rfl) ⟨741203, by rfl⟩ : syracuseStep 988271 = 1482407) B1482407
theorem B2233565 : Blo 389765 2233565 := bstep (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) B837587
theorem B1479991 : Blo 389765 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B1250615 : Blo 389765 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B1119881 : Blo 389765 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B2824091 : Blo 389765 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B989435 : Blo 389765 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B530815 : Blo 389765 530815 := bstep (se 1 (by rfl) ⟨398111, by rfl⟩ : syracuseStep 530815 = 796223) B796223
theorem B989921 : Blo 389765 989921 := bstep (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) B742441
theorem B4037363 : Blo 389765 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B2497999 : Blo 389765 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B7511525 : Blo 389765 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B1318571 : Blo 389765 1318571 := bstep (se 1 (by rfl) ⟨988928, by rfl⟩ : syracuseStep 1318571 = 1977857) B1977857
theorem B3776219 : Blo 389765 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B663707 : Blo 389765 663707 := bstep (se 1 (by rfl) ⟨497780, by rfl⟩ : syracuseStep 663707 = 995561) B995561
theorem B1975265 : Blo 389765 1975265 := bstep (se 2 (by rfl) ⟨740724, by rfl⟩ : syracuseStep 1975265 = 1481449) B1481449
theorem B1319975 : Blo 389765 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B1582291 : Blo 389765 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1320191 : Blo 389765 1320191 := bstep (se 1 (by rfl) ⟨990143, by rfl⟩ : syracuseStep 1320191 = 1980287) B1980287
theorem B5350859 : Blo 389765 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B6661601 : Blo 389765 6661601 := bstep (se 2 (by rfl) ⟨2498100, by rfl⟩ : syracuseStep 6661601 = 4996201) B4996201
theorem B3352535 : Blo 389765 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B1321001 : Blo 389765 1321001 := bstep (se 2 (by rfl) ⟨495375, by rfl⟩ : syracuseStep 1321001 = 990751) B990751
theorem B3188879 : Blo 389765 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B3352913 : Blo 389765 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B2239123 : Blo 389765 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B2371103 : Blo 389765 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1322567 : Blo 389765 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B2240081 : Blo 389765 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B1585097 : Blo 389765 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B995287 : Blo 389765 995287 := bstep (se 1 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 995287 = 1492931) B1492931
theorem B438511 : Blo 389765 438511 := bstep (se 1 (by rfl) ⟨328883, by rfl⟩ : syracuseStep 438511 = 657767) B657767
theorem B6763175 : Blo 389765 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B439015 : Blo 389765 439015 := bstep (se 1 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 439015 = 658523) B658523
theorem B1323863 : Blo 389765 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B3224609 : Blo 389765 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B1324079 : Blo 389765 1324079 := bstep (se 1 (by rfl) ⟨993059, by rfl⟩ : syracuseStep 1324079 = 1986119) B1986119
theorem B2536555 : Blo 389765 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B9483425 : Blo 389765 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B2832047 : Blo 389765 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B2242313 : Blo 389765 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B833657 : Blo 389765 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B1063307 : Blo 389765 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B440815 : Blo 389765 440815 := bstep (se 1 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 440815 = 661223) B661223
theorem B247053635 : Blo 389765 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B704027 : Blo 389765 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B4473143 : Blo 389765 4473143 := bstep (se 1 (by rfl) ⟨3354857, by rfl⟩ : syracuseStep 4473143 = 6709715) B6709715
theorem B442687 : Blo 389765 442687 := bstep (se 1 (by rfl) ⟨332015, by rfl⟩ : syracuseStep 442687 = 664031) B664031
theorem B1327859 : Blo 389765 1327859 := bstep (se 1 (by rfl) ⟨995894, by rfl⟩ : syracuseStep 1327859 = 1991789) B1991789
theorem B4474601 : Blo 389765 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B1886111 : Blo 389765 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B1493113 : Blo 389765 1493113 := bstep (se 2 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 1493113 = 1119835) B1119835
theorem B5359823 : Blo 389765 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B4443983 : Blo 389765 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B839801 : Blo 389765 839801 := bstep (se 2 (by rfl) ⟨314925, by rfl⟩ : syracuseStep 839801 = 629851) B629851
theorem B2511071 : Blo 389765 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B3494345 : Blo 389765 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B1987415 : Blo 389765 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B1987577 : Blo 389765 1987577 := bstep (se 2 (by rfl) ⟨745341, by rfl⟩ : syracuseStep 1987577 = 1490683) B1490683
theorem B35149463 : Blo 389765 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B2972375 : Blo 389765 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B1072211 : Blo 389765 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B14245571 : Blo 389765 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B3760343 : Blo 389765 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B17228161 : Blo 389765 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B1991465 : Blo 389765 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B877535 : Blo 389765 877535 := bstep (se 1 (by rfl) ⟨658151, by rfl⟩ : syracuseStep 877535 = 1316303) B1316303
theorem B877679 : Blo 389765 877679 := bstep (se 1 (by rfl) ⟨658259, by rfl⟩ : syracuseStep 877679 = 1316519) B1316519
theorem B878075 : Blo 389765 878075 := bstep (se 1 (by rfl) ⟨658556, by rfl⟩ : syracuseStep 878075 = 1317113) B1317113
theorem B4449815 : Blo 389765 4449815 := bstep (se 1 (by rfl) ⟨3337361, by rfl⟩ : syracuseStep 4449815 = 6674723) B6674723
theorem B878111 : Blo 389765 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B878183 : Blo 389765 878183 := bstep (se 1 (by rfl) ⟨658637, by rfl⟩ : syracuseStep 878183 = 1317275) B1317275
theorem B2254895 : Blo 389765 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B878687 : Blo 389765 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B1992923 : Blo 389765 1992923 := bstep (se 1 (by rfl) ⟨1494692, by rfl⟩ : syracuseStep 1992923 = 2989385) B2989385
theorem B879407 : Blo 389765 879407 := bstep (se 1 (by rfl) ⟨659555, by rfl⟩ : syracuseStep 879407 = 1319111) B1319111
theorem B6352127 : Blo 389765 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B1076969 : Blo 389765 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B585671 : Blo 389765 585671 := bstep (se 1 (by rfl) ⟨439253, by rfl⟩ : syracuseStep 585671 = 878507) B878507
theorem B880631 : Blo 389765 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B880937 : Blo 389765 880937 := bstep (se 2 (by rfl) ⟨330351, by rfl⟩ : syracuseStep 880937 = 660703) B660703
theorem B2126159 : Blo 389765 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B881513 : Blo 389765 881513 := bstep (se 2 (by rfl) ⟨330567, by rfl⟩ : syracuseStep 881513 = 661135) B661135
theorem B1110905 : Blo 389765 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B882089 : Blo 389765 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B882143 : Blo 389765 882143 := bstep (se 1 (by rfl) ⟨661607, by rfl⟩ : syracuseStep 882143 = 1323215) B1323215
theorem B587243 : Blo 389765 587243 := bstep (se 1 (by rfl) ⟨440432, by rfl⟩ : syracuseStep 587243 = 880865) B880865
theorem B13629019 : Blo 389765 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B1341053 : Blo 389765 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B587471 : Blo 389765 587471 := bstep (se 1 (by rfl) ⟨440603, by rfl⟩ : syracuseStep 587471 = 881207) B881207
theorem B587711 : Blo 389765 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B882683 : Blo 389765 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B882791 : Blo 389765 882791 := bstep (se 1 (by rfl) ⟨662093, by rfl⟩ : syracuseStep 882791 = 1324187) B1324187
theorem B391451 : Blo 389765 391451 := bstep (se 1 (by rfl) ⟨293588, by rfl⟩ : syracuseStep 391451 = 587177) B587177
theorem B1734967 : Blo 389765 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B1407289 : Blo 389765 1407289 := bstep (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) B1055467
theorem B391487 : Blo 389765 391487 := bstep (se 1 (by rfl) ⟨293615, by rfl⟩ : syracuseStep 391487 = 587231) B587231
theorem B588335 : Blo 389765 588335 := bstep (se 1 (by rfl) ⟨441251, by rfl⟩ : syracuseStep 588335 = 882503) B882503
theorem B391919 : Blo 389765 391919 := bstep (se 1 (by rfl) ⟨293939, by rfl⟩ : syracuseStep 391919 = 587879) B587879
theorem B883439 : Blo 389765 883439 := bstep (se 1 (by rfl) ⟨662579, by rfl⟩ : syracuseStep 883439 = 1325159) B1325159
theorem B588539 : Blo 389765 588539 := bstep (se 1 (by rfl) ⟨441404, by rfl⟩ : syracuseStep 588539 = 882809) B882809
theorem B588575 : Blo 389765 588575 := bstep (se 1 (by rfl) ⟨441431, by rfl⟩ : syracuseStep 588575 = 882863) B882863
theorem B555817 : Blo 389765 555817 := bstep (se 2 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 555817 = 416863) B416863
theorem B883511 : Blo 389765 883511 := bstep (se 1 (by rfl) ⟨662633, by rfl⟩ : syracuseStep 883511 = 1325267) B1325267
theorem B556159 : Blo 389765 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B392731 : Blo 389765 392731 := bstep (se 1 (by rfl) ⟨294548, by rfl⟩ : syracuseStep 392731 = 589097) B589097
theorem B392943 : Blo 389765 392943 := bstep (se 1 (by rfl) ⟨294707, by rfl⟩ : syracuseStep 392943 = 589415) B589415
theorem B589919 : Blo 389765 589919 := bstep (se 1 (by rfl) ⟨442439, by rfl⟩ : syracuseStep 589919 = 884879) B884879
theorem B589991 : Blo 389765 589991 := bstep (se 1 (by rfl) ⟨442493, by rfl⟩ : syracuseStep 589991 = 884987) B884987
theorem B2982095 : Blo 389765 2982095 := bstep (se 1 (by rfl) ⟨2236571, by rfl⟩ : syracuseStep 2982095 = 4473143) B4473143
theorem B393543 : Blo 389765 393543 := bstep (se 1 (by rfl) ⟨295157, by rfl⟩ : syracuseStep 393543 = 590315) B590315
theorem B590249 : Blo 389765 590249 := bstep (se 2 (by rfl) ⟨221343, by rfl⟩ : syracuseStep 590249 = 442687) B442687
theorem B885239 : Blo 389765 885239 := bstep (se 1 (by rfl) ⟨663929, by rfl⟩ : syracuseStep 885239 = 1327859) B1327859
theorem B393727 : Blo 389765 393727 := bstep (se 1 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 393727 = 590591) B590591
theorem B22970881 : Blo 389765 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B4457105 : Blo 389765 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B2983067 : Blo 389765 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B3573215 : Blo 389765 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B22939307 : Blo 389765 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B7145263 : Blo 389765 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B559867 : Blo 389765 559867 := bstep (se 1 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 559867 = 839801) B839801
theorem B1674047 : Blo 389765 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B658847 : Blo 389765 658847 := bstep (se 1 (by rfl) ⟨494135, by rfl⟩ : syracuseStep 658847 = 988271) B988271
theorem B2985497 : Blo 389765 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B23432975 : Blo 389765 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B659623 : Blo 389765 659623 := bstep (se 1 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 659623 = 989435) B989435
theorem B659947 : Blo 389765 659947 := bstep (se 1 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 659947 = 989921) B989921
theorem B2691575 : Blo 389765 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B660521 : Blo 389765 660521 := bstep (se 2 (by rfl) ⟨247695, by rfl⟩ : syracuseStep 660521 = 495391) B495391
theorem B1316843 : Blo 389765 1316843 := bstep (se 1 (by rfl) ⟨987632, by rfl⟩ : syracuseStep 1316843 = 1975265) B1975265
theorem B2235023 : Blo 389765 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B3382073 : Blo 389765 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B2235275 : Blo 389765 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B1973321 : Blo 389765 1973321 := bstep (se 2 (by rfl) ⟨739995, by rfl⟩ : syracuseStep 1973321 = 1479991) B1479991
theorem B4234751 : Blo 389765 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B1580735 : Blo 389765 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B1056731 : Blo 389765 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B2859229 : Blo 389765 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B1417439 : Blo 389765 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B1319165 : Blo 389765 1319165 := bstep (se 3 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 1319165 = 494687) B494687
theorem B1876385 : Blo 389765 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B894035 : Blo 389765 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B37988189 : Blo 389765 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B1320893 : Blo 389765 1320893 := bstep (se 3 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 1320893 = 495335) B495335
theorem B164702423 : Blo 389765 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B469351 : Blo 389765 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B9809515 : Blo 389765 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B9318253 : Blo 389765 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B1486781 : Blo 389765 1486781 := bstep (se 3 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 1486781 = 557543) B557543
theorem B1257407 : Blo 389765 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B2109721 : Blo 389765 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B2962655 : Blo 389765 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B1488239 : Blo 389765 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B1324943 : Blo 389765 1324943 := bstep (se 1 (by rfl) ⟨993707, by rfl⟩ : syracuseStep 1324943 = 1987415) B1987415
theorem B1325051 : Blo 389765 1325051 := bstep (se 1 (by rfl) ⟨993788, by rfl⟩ : syracuseStep 1325051 = 1987577) B1987577
theorem B1489043 : Blo 389765 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B833743 : Blo 389765 833743 := bstep (se 1 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 833743 = 1250615) B1250615
theorem B1882727 : Blo 389765 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B1981583 : Blo 389765 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B1883417 : Blo 389765 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B1327049 : Blo 389765 1327049 := bstep (se 2 (by rfl) ⟨497643, by rfl⟩ : syracuseStep 1327049 = 995287) B995287
theorem B442471 : Blo 389765 442471 := bstep (se 1 (by rfl) ⟨331853, by rfl⟩ : syracuseStep 442471 = 663707) B663707
theorem B2506895 : Blo 389765 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B49725613 : Blo 389765 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B1327643 : Blo 389765 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B4441067 : Blo 389765 4441067 := bstep (se 1 (by rfl) ⟨3330800, by rfl⟩ : syracuseStep 4441067 = 6661601) B6661601
theorem B2966543 : Blo 389765 2966543 := bstep (se 1 (by rfl) ⟨2224907, by rfl⟩ : syracuseStep 2966543 = 4449815) B4449815
theorem B1328615 : Blo 389765 1328615 := bstep (se 1 (by rfl) ⟨996461, by rfl⟩ : syracuseStep 1328615 = 1992923) B1992923
theorem B18172025 : Blo 389765 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1493387 : Blo 389765 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B2313289 : Blo 389765 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B4508783 : Blo 389765 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B707753 : Blo 389765 707753 := bstep (se 2 (by rfl) ⟨265407, by rfl⟩ : syracuseStep 707753 = 530815) B530815
theorem B740603 : Blo 389765 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B2149739 : Blo 389765 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B741089 : Blo 389765 741089 := bstep (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) B555817
theorem B1888031 : Blo 389765 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B1494875 : Blo 389765 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B741545 : Blo 389765 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B708871 : Blo 389765 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B3330665 : Blo 389765 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B4283239 : Blo 389765 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B9329627 : Blo 389765 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B2973347 : Blo 389765 2973347 := bstep (se 1 (by rfl) ⟨2230010, by rfl⟩ : syracuseStep 2973347 = 4460021) B4460021
theorem B10051451 : Blo 389765 10051451 := bstep (se 1 (by rfl) ⟨7538588, by rfl⟩ : syracuseStep 10051451 = 15077177) B15077177
theorem B1990817 : Blo 389765 1990817 := bstep (se 2 (by rfl) ⟨746556, by rfl⟩ : syracuseStep 1990817 = 1493113) B1493113
theorem B746587 : Blo 389765 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B5007683 : Blo 389765 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B879047 : Blo 389765 879047 := bstep (se 1 (by rfl) ⟨659285, by rfl⟩ : syracuseStep 879047 = 1318571) B1318571
theorem B2517479 : Blo 389765 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B584681 : Blo 389765 584681 := bstep (se 2 (by rfl) ⟨219255, by rfl⟩ : syracuseStep 584681 = 438511) B438511
theorem B2223085 : Blo 389765 2223085 := bstep (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) B833657
theorem B585023 : Blo 389765 585023 := bstep (se 1 (by rfl) ⟨438767, by rfl⟩ : syracuseStep 585023 = 877535) B877535
theorem B879983 : Blo 389765 879983 := bstep (se 1 (by rfl) ⟨659987, by rfl⟩ : syracuseStep 879983 = 1319975) B1319975
theorem B585119 : Blo 389765 585119 := bstep (se 1 (by rfl) ⟨438839, by rfl⟩ : syracuseStep 585119 = 877679) B877679
theorem B880127 : Blo 389765 880127 := bstep (se 1 (by rfl) ⟨660095, by rfl⟩ : syracuseStep 880127 = 1320191) B1320191
theorem B3567239 : Blo 389765 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B585353 : Blo 389765 585353 := bstep (se 2 (by rfl) ⟨219507, by rfl⟩ : syracuseStep 585353 = 439015) B439015
theorem B585383 : Blo 389765 585383 := bstep (se 1 (by rfl) ⟨439037, by rfl⟩ : syracuseStep 585383 = 878075) B878075
theorem B585407 : Blo 389765 585407 := bstep (se 1 (by rfl) ⟨439055, by rfl⟩ : syracuseStep 585407 = 878111) B878111
theorem B585455 : Blo 389765 585455 := bstep (se 1 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 585455 = 878183) B878183
theorem B880667 : Blo 389765 880667 := bstep (se 1 (by rfl) ⟨660500, by rfl⟩ : syracuseStep 880667 = 1321001) B1321001
theorem B1503263 : Blo 389765 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B585791 : Blo 389765 585791 := bstep (se 1 (by rfl) ⟨439343, by rfl⟩ : syracuseStep 585791 = 878687) B878687
theorem B2125919 : Blo 389765 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B586271 : Blo 389765 586271 := bstep (se 1 (by rfl) ⟨439703, by rfl⟩ : syracuseStep 586271 = 879407) B879407
theorem B881711 : Blo 389765 881711 := bstep (se 1 (by rfl) ⟨661283, by rfl⟩ : syracuseStep 881711 = 1322567) B1322567
theorem B717979 : Blo 389765 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B390447 : Blo 389765 390447 := bstep (se 1 (by rfl) ⟨292835, by rfl⟩ : syracuseStep 390447 = 585671) B585671
theorem B587087 : Blo 389765 587087 := bstep (se 1 (by rfl) ⟨440315, by rfl⟩ : syracuseStep 587087 = 880631) B880631
theorem B587291 : Blo 389765 587291 := bstep (se 1 (by rfl) ⟨440468, by rfl⟩ : syracuseStep 587291 = 880937) B880937
theorem B882575 : Blo 389765 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B587675 : Blo 389765 587675 := bstep (se 1 (by rfl) ⟨440756, by rfl⟩ : syracuseStep 587675 = 881513) B881513
theorem B587753 : Blo 389765 587753 := bstep (se 2 (by rfl) ⟨220407, by rfl⟩ : syracuseStep 587753 = 440815) B440815
theorem B882719 : Blo 389765 882719 := bstep (se 1 (by rfl) ⟨662039, by rfl⟩ : syracuseStep 882719 = 1324079) B1324079
theorem B6322283 : Blo 389765 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B588059 : Blo 389765 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B588095 : Blo 389765 588095 := bstep (se 1 (by rfl) ⟨441071, by rfl⟩ : syracuseStep 588095 = 882143) B882143
theorem B391495 : Blo 389765 391495 := bstep (se 1 (by rfl) ⟨293621, by rfl⟩ : syracuseStep 391495 = 587243) B587243
theorem B391647 : Blo 389765 391647 := bstep (se 1 (by rfl) ⟨293735, by rfl⟩ : syracuseStep 391647 = 587471) B587471
theorem B391807 : Blo 389765 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B588455 : Blo 389765 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B588527 : Blo 389765 588527 := bstep (se 1 (by rfl) ⟨441395, by rfl⟩ : syracuseStep 588527 = 882791) B882791
theorem B392223 : Blo 389765 392223 := bstep (se 1 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 392223 = 588335) B588335
theorem B588959 : Blo 389765 588959 := bstep (se 1 (by rfl) ⟨441719, by rfl⟩ : syracuseStep 588959 = 883439) B883439
theorem B392359 : Blo 389765 392359 := bstep (se 1 (by rfl) ⟨294269, by rfl⟩ : syracuseStep 392359 = 588539) B588539
theorem B392383 : Blo 389765 392383 := bstep (se 1 (by rfl) ⟨294287, by rfl⟩ : syracuseStep 392383 = 588575) B588575
theorem B589007 : Blo 389765 589007 := bstep (se 1 (by rfl) ⟨441755, by rfl⟩ : syracuseStep 589007 = 883511) B883511
theorem B393279 : Blo 389765 393279 := bstep (se 1 (by rfl) ⟨294959, by rfl⟩ : syracuseStep 393279 = 589919) B589919
theorem B1671263 : Blo 389765 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B393327 : Blo 389765 393327 := bstep (se 1 (by rfl) ⟨294995, by rfl⟩ : syracuseStep 393327 = 589991) B589991
theorem B589961 : Blo 389765 589961 := bstep (se 2 (by rfl) ⟨221235, by rfl⟩ : syracuseStep 589961 = 442471) B442471
theorem B393499 : Blo 389765 393499 := bstep (se 1 (by rfl) ⟨295124, by rfl⟩ : syracuseStep 393499 = 590249) B590249
theorem B590159 : Blo 389765 590159 := bstep (se 1 (by rfl) ⟨442619, by rfl⟩ : syracuseStep 590159 = 885239) B885239
theorem B885095 : Blo 389765 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B885743 : Blo 389765 885743 := bstep (se 1 (by rfl) ⟨664307, by rfl⟩ : syracuseStep 885743 = 1328615) B1328615
theorem B1116031 : Blo 389765 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B494363 : Blo 389765 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B625801 : Blo 389765 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B1315547 : Blo 389765 1315547 := bstep (se 1 (by rfl) ⟨986660, by rfl⟩ : syracuseStep 1315547 = 1973321) B1973321
theorem B2823167 : Blo 389765 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B1053823 : Blo 389765 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B12424337 : Blo 389765 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B1250923 : Blo 389765 1250923 := bstep (se 1 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 1250923 = 1876385) B1876385
theorem B957305 : Blo 389765 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B1678319 : Blo 389765 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B24879005 : Blo 389765 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B991187 : Blo 389765 991187 := bstep (se 1 (by rfl) ⟨743390, by rfl⟩ : syracuseStep 991187 = 1486781) B1486781
theorem B1417279 : Blo 389765 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B1974941 : Blo 389765 1974941 := bstep (se 3 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 1974941 = 740603) B740603
theorem B5022445 : Blo 389765 5022445 := bstep (se 3 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 5022445 = 1883417) B1883417
theorem B1975103 : Blo 389765 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B992159 : Blo 389765 992159 := bstep (se 1 (by rfl) ⟨744119, by rfl⟩ : syracuseStep 992159 = 1488239) B1488239
theorem B5710985 : Blo 389765 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B992695 : Blo 389765 992695 := bstep (se 1 (by rfl) ⟨744521, by rfl⟩ : syracuseStep 992695 = 1489043) B1489043
theorem B1255151 : Blo 389765 1255151 := bstep (se 1 (by rfl) ⟨941363, by rfl⟩ : syracuseStep 1255151 = 1882727) B1882727
theorem B1976237 : Blo 389765 1976237 := bstep (se 3 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 1976237 = 741089) B741089
theorem B1321055 : Blo 389765 1321055 := bstep (se 1 (by rfl) ⟨990791, by rfl⟩ : syracuseStep 1321055 = 1981583) B1981583
theorem B4008701 : Blo 389765 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B66300817 : Blo 389765 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B2960711 : Blo 389765 2960711 := bstep (se 1 (by rfl) ⟨2220533, by rfl⟩ : syracuseStep 2960711 = 4441067) B4441067
theorem B1977695 : Blo 389765 1977695 := bstep (se 1 (by rfl) ⟨1483271, by rfl⟩ : syracuseStep 1977695 = 2966543) B2966543
theorem B15249221 : Blo 389765 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B995449 : Blo 389765 995449 := bstep (se 2 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 995449 = 746587) B746587
theorem B995591 : Blo 389765 995591 := bstep (se 1 (by rfl) ⟨746693, by rfl⟩ : syracuseStep 995591 = 1493387) B1493387
theorem B471835 : Blo 389765 471835 := bstep (se 1 (by rfl) ⟨353876, by rfl⟩ : syracuseStep 471835 = 707753) B707753
theorem B439231 : Blo 389765 439231 := bstep (se 1 (by rfl) ⟨329423, by rfl⟩ : syracuseStep 439231 = 658847) B658847
theorem B1258687 : Blo 389765 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B996583 : Blo 389765 996583 := bstep (se 1 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 996583 = 1494875) B1494875
theorem B440347 : Blo 389765 440347 := bstep (se 1 (by rfl) ⟨330260, by rfl⟩ : syracuseStep 440347 = 660521) B660521
theorem B2964113 : Blo 389765 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B1490015 : Blo 389765 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B1490183 : Blo 389765 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B1982231 : Blo 389765 1982231 := bstep (se 1 (by rfl) ⟨1486673, by rfl⟩ : syracuseStep 1982231 = 2973347) B2973347
theorem B6700967 : Blo 389765 6700967 := bstep (se 1 (by rfl) ⟨5025725, by rfl⟩ : syracuseStep 6700967 = 10051451) B10051451
theorem B1327211 : Blo 389765 1327211 := bstep (se 1 (by rfl) ⟨995408, by rfl⟩ : syracuseStep 1327211 = 1990817) B1990817
theorem B12337541 : Blo 389765 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B2378159 : Blo 389765 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B838271 : Blo 389765 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B52317413 : Blo 389765 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B4214855 : Blo 389765 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B1988063 : Blo 389765 1988063 := bstep (se 1 (by rfl) ⟨1491047, by rfl⟩ : syracuseStep 1988063 = 2982095) B2982095
theorem B2971403 : Blo 389765 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B30627841 : Blo 389765 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B1988711 : Blo 389765 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B2382143 : Blo 389765 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B15292871 : Blo 389765 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B12114683 : Blo 389765 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B3005855 : Blo 389765 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B1433159 : Blo 389765 1433159 := bstep (se 1 (by rfl) ⟨1074869, by rfl⟩ : syracuseStep 1433159 = 2149739) B2149739
theorem B1990331 : Blo 389765 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B9527017 : Blo 389765 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B15621983 : Blo 389765 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B2384093 : Blo 389765 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B1794383 : Blo 389765 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B2220443 : Blo 389765 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B746489 : Blo 389765 746489 := bstep (se 2 (by rfl) ⟨279933, by rfl⟩ : syracuseStep 746489 = 559867) B559867
theorem B877895 : Blo 389765 877895 := bstep (se 1 (by rfl) ⟨658421, by rfl⟩ : syracuseStep 877895 = 1316843) B1316843
theorem B2254715 : Blo 389765 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B944959 : Blo 389765 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B879443 : Blo 389765 879443 := bstep (se 1 (by rfl) ⟨659582, by rfl⟩ : syracuseStep 879443 = 1319165) B1319165
theorem B879497 : Blo 389765 879497 := bstep (se 2 (by rfl) ⟨329811, by rfl⟩ : syracuseStep 879497 = 659623) B659623
theorem B945161 : Blo 389765 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B2812961 : Blo 389765 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B879929 : Blo 389765 879929 := bstep (se 2 (by rfl) ⟨329973, by rfl⟩ : syracuseStep 879929 = 659947) B659947
theorem B25325459 : Blo 389765 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B880595 : Blo 389765 880595 := bstep (se 1 (by rfl) ⟨660446, by rfl⟩ : syracuseStep 880595 = 1320893) B1320893
theorem B109801615 : Blo 389765 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B3338455 : Blo 389765 3338455 := bstep (se 1 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 3338455 = 5007683) B5007683
theorem B586031 : Blo 389765 586031 := bstep (se 1 (by rfl) ⟨439523, by rfl⟩ : syracuseStep 586031 = 879047) B879047
theorem B389787 : Blo 389765 389787 := bstep (se 1 (by rfl) ⟨292340, by rfl⟩ : syracuseStep 389787 = 584681) B584681
theorem B390015 : Blo 389765 390015 := bstep (se 1 (by rfl) ⟨292511, by rfl⟩ : syracuseStep 390015 = 585023) B585023
theorem B586655 : Blo 389765 586655 := bstep (se 1 (by rfl) ⟨439991, by rfl⟩ : syracuseStep 586655 = 879983) B879983
theorem B390079 : Blo 389765 390079 := bstep (se 1 (by rfl) ⟨292559, by rfl⟩ : syracuseStep 390079 = 585119) B585119
theorem B586751 : Blo 389765 586751 := bstep (se 1 (by rfl) ⟨440063, by rfl⟩ : syracuseStep 586751 = 880127) B880127
theorem B390235 : Blo 389765 390235 := bstep (se 1 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 390235 = 585353) B585353
theorem B390255 : Blo 389765 390255 := bstep (se 1 (by rfl) ⟨292691, by rfl⟩ : syracuseStep 390255 = 585383) B585383
theorem B390271 : Blo 389765 390271 := bstep (se 1 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 390271 = 585407) B585407
theorem B390303 : Blo 389765 390303 := bstep (se 1 (by rfl) ⟨292727, by rfl⟩ : syracuseStep 390303 = 585455) B585455
theorem B587111 : Blo 389765 587111 := bstep (se 1 (by rfl) ⟨440333, by rfl⟩ : syracuseStep 587111 = 880667) B880667
theorem B390527 : Blo 389765 390527 := bstep (se 1 (by rfl) ⟨292895, by rfl⟩ : syracuseStep 390527 = 585791) B585791
theorem B1111657 : Blo 389765 1111657 := bstep (se 2 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 1111657 = 833743) B833743
theorem B390847 : Blo 389765 390847 := bstep (se 1 (by rfl) ⟨293135, by rfl⟩ : syracuseStep 390847 = 586271) B586271
theorem B587807 : Blo 389765 587807 := bstep (se 1 (by rfl) ⟨440855, by rfl⟩ : syracuseStep 587807 = 881711) B881711
theorem B391391 : Blo 389765 391391 := bstep (se 1 (by rfl) ⟨293543, by rfl⟩ : syracuseStep 391391 = 587087) B587087
theorem B391527 : Blo 389765 391527 := bstep (se 1 (by rfl) ⟨293645, by rfl⟩ : syracuseStep 391527 = 587291) B587291
theorem B588383 : Blo 389765 588383 := bstep (se 1 (by rfl) ⟨441287, by rfl⟩ : syracuseStep 588383 = 882575) B882575
theorem B883295 : Blo 389765 883295 := bstep (se 1 (by rfl) ⟨662471, by rfl⟩ : syracuseStep 883295 = 1324943) B1324943
theorem B391783 : Blo 389765 391783 := bstep (se 1 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 391783 = 587675) B587675
theorem B391835 : Blo 389765 391835 := bstep (se 1 (by rfl) ⟨293876, by rfl⟩ : syracuseStep 391835 = 587753) B587753
theorem B883367 : Blo 389765 883367 := bstep (se 1 (by rfl) ⟨662525, by rfl⟩ : syracuseStep 883367 = 1325051) B1325051
theorem B588479 : Blo 389765 588479 := bstep (se 1 (by rfl) ⟨441359, by rfl⟩ : syracuseStep 588479 = 882719) B882719
theorem B392039 : Blo 389765 392039 := bstep (se 1 (by rfl) ⟨294029, by rfl⟩ : syracuseStep 392039 = 588059) B588059
theorem B392063 : Blo 389765 392063 := bstep (se 1 (by rfl) ⟨294047, by rfl⟩ : syracuseStep 392063 = 588095) B588095
theorem B392303 : Blo 389765 392303 := bstep (se 1 (by rfl) ⟨294227, by rfl⟩ : syracuseStep 392303 = 588455) B588455
theorem B392351 : Blo 389765 392351 := bstep (se 1 (by rfl) ⟨294263, by rfl⟩ : syracuseStep 392351 = 588527) B588527
theorem B392639 : Blo 389765 392639 := bstep (se 1 (by rfl) ⟨294479, by rfl⟩ : syracuseStep 392639 = 588959) B588959
theorem B392671 : Blo 389765 392671 := bstep (se 1 (by rfl) ⟨294503, by rfl⟩ : syracuseStep 392671 = 589007) B589007
theorem B11271797 : Blo 389765 11271797 := bstep (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) B1056731
theorem B884699 : Blo 389765 884699 := bstep (se 1 (by rfl) ⟨663524, by rfl⟩ : syracuseStep 884699 = 1327049) B1327049
theorem B1114175 : Blo 389765 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B884807 : Blo 389765 884807 := bstep (se 1 (by rfl) ⟨663605, by rfl⟩ : syracuseStep 884807 = 1327211) B1327211
theorem B393307 : Blo 389765 393307 := bstep (se 1 (by rfl) ⟨294980, by rfl⟩ : syracuseStep 393307 = 589961) B589961
theorem B393439 : Blo 389765 393439 := bstep (se 1 (by rfl) ⟨295079, by rfl⟩ : syracuseStep 393439 = 590159) B590159
theorem B590063 : Blo 389765 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B8225027 : Blo 389765 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B590495 : Blo 389765 590495 := bstep (se 1 (by rfl) ⟨442871, by rfl⟩ : syracuseStep 590495 = 885743) B885743
theorem B558847 : Blo 389765 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B10195247 : Blo 389765 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B1118879 : Blo 389765 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B2003903 : Blo 389765 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B955439 : Blo 389765 955439 := bstep (se 1 (by rfl) ⟨716579, by rfl⟩ : syracuseStep 955439 = 1433159) B1433159
theorem B16586003 : Blo 389765 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B660791 : Blo 389765 660791 := bstep (se 1 (by rfl) ⟨495593, by rfl⟩ : syracuseStep 660791 = 991187) B991187
theorem B1480295 : Blo 389765 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B1316627 : Blo 389765 1316627 := bstep (se 1 (by rfl) ⟨987470, by rfl⟩ : syracuseStep 1316627 = 1974941) B1974941
theorem B1316735 : Blo 389765 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B661439 : Blo 389765 661439 := bstep (se 1 (by rfl) ⟨496079, by rfl⟩ : syracuseStep 661439 = 992159) B992159
theorem B497659 : Blo 389765 497659 := bstep (se 1 (by rfl) ⟨373244, by rfl⟩ : syracuseStep 497659 = 746489) B746489
theorem B3807323 : Blo 389765 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B1317491 : Blo 389765 1317491 := bstep (se 1 (by rfl) ⟨988118, by rfl⟩ : syracuseStep 1317491 = 1976237) B1976237
theorem B1678249 : Blo 389765 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B10689869 : Blo 389765 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B630107 : Blo 389765 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B1875307 : Blo 389765 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B1318301 : Blo 389765 1318301 := bstep (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) B494363
theorem B1482209 : Blo 389765 1482209 := bstep (se 2 (by rfl) ⟨555828, by rfl⟩ : syracuseStep 1482209 = 1111657) B1111657
theorem B1973807 : Blo 389765 1973807 := bstep (se 1 (by rfl) ⟨1480355, by rfl⟩ : syracuseStep 1973807 = 2960711) B2960711
theorem B1318463 : Blo 389765 1318463 := bstep (se 1 (by rfl) ⟨988847, by rfl⟩ : syracuseStep 1318463 = 1977695) B1977695
theorem B10166147 : Blo 389765 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B16883639 : Blo 389765 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B40837121 : Blo 389765 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B663727 : Blo 389765 663727 := bstep (se 1 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 663727 = 995591) B995591
theorem B1976075 : Blo 389765 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B993343 : Blo 389765 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B993455 : Blo 389765 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B7514531 : Blo 389765 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B1321487 : Blo 389765 1321487 := bstep (se 1 (by rfl) ⟨991115, by rfl⟩ : syracuseStep 1321487 = 1982231) B1982231
theorem B4467311 : Blo 389765 4467311 := bstep (se 1 (by rfl) ⟨3350483, by rfl⟩ : syracuseStep 4467311 = 6700967) B6700967
theorem B6696593 : Blo 389765 6696593 := bstep (se 2 (by rfl) ⟨2511222, by rfl⟩ : syracuseStep 6696593 = 5022445) B5022445
theorem B1585439 : Blo 389765 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B1323593 : Blo 389765 1323593 := bstep (se 2 (by rfl) ⟨496347, by rfl⟩ : syracuseStep 1323593 = 992695) B992695
theorem B34878275 : Blo 389765 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B1488041 : Blo 389765 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1882111 : Blo 389765 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B1325375 : Blo 389765 1325375 := bstep (se 1 (by rfl) ⟨994031, by rfl⟩ : syracuseStep 1325375 = 1988063) B1988063
theorem B1259945 : Blo 389765 1259945 := bstep (se 2 (by rfl) ⟨472479, by rfl⟩ : syracuseStep 1259945 = 944959) B944959
theorem B1980935 : Blo 389765 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B1325807 : Blo 389765 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B834401 : Blo 389765 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B8076455 : Blo 389765 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B1326887 : Blo 389765 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B1589395 : Blo 389765 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1327265 : Blo 389765 1327265 := bstep (se 2 (by rfl) ⟨497724, by rfl⟩ : syracuseStep 1327265 = 995449) B995449
theorem B1196255 : Blo 389765 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B836767 : Blo 389765 836767 := bstep (se 1 (by rfl) ⟨627575, by rfl⟩ : syracuseStep 836767 = 1255151) B1255151
theorem B1328777 : Blo 389765 1328777 := bstep (se 2 (by rfl) ⟨498291, by rfl⟩ : syracuseStep 1328777 = 996583) B996583
theorem B12702689 : Blo 389765 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B1889705 : Blo 389765 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B2809903 : Blo 389765 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B877031 : Blo 389765 877031 := bstep (se 1 (by rfl) ⟨657773, by rfl⟩ : syracuseStep 877031 = 1315547) B1315547
theorem B8282891 : Blo 389765 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B88401089 : Blo 389765 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B2516453 : Blo 389765 2516453 := bstep (se 4 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 2516453 = 471835) B471835
theorem B10414655 : Blo 389765 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B146402153 : Blo 389765 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B4451273 : Blo 389765 4451273 := bstep (se 2 (by rfl) ⟨1669227, by rfl⟩ : syracuseStep 4451273 = 3338455) B3338455
theorem B6352381 : Blo 389765 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B585263 : Blo 389765 585263 := bstep (se 1 (by rfl) ⟨438947, by rfl⟩ : syracuseStep 585263 = 877895) B877895
theorem B1503143 : Blo 389765 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B585641 : Blo 389765 585641 := bstep (se 2 (by rfl) ⟨219615, by rfl⟩ : syracuseStep 585641 = 439231) B439231
theorem B880703 : Blo 389765 880703 := bstep (se 1 (by rfl) ⟨660527, by rfl⟩ : syracuseStep 880703 = 1321055) B1321055
theorem B1405097 : Blo 389765 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B586295 : Blo 389765 586295 := bstep (se 1 (by rfl) ⟨439721, by rfl⟩ : syracuseStep 586295 = 879443) B879443
theorem B586331 : Blo 389765 586331 := bstep (se 1 (by rfl) ⟨439748, by rfl⟩ : syracuseStep 586331 = 879497) B879497
theorem B1667897 : Blo 389765 1667897 := bstep (se 2 (by rfl) ⟨625461, by rfl⟩ : syracuseStep 1667897 = 1250923) B1250923
theorem B586619 : Blo 389765 586619 := bstep (se 1 (by rfl) ⟨439964, by rfl⟩ : syracuseStep 586619 = 879929) B879929
theorem B2552813 : Blo 389765 2552813 := bstep (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) B957305
theorem B587063 : Blo 389765 587063 := bstep (se 1 (by rfl) ⟨440297, by rfl⟩ : syracuseStep 587063 = 880595) B880595
theorem B587129 : Blo 389765 587129 := bstep (se 2 (by rfl) ⟨220173, by rfl⟩ : syracuseStep 587129 = 440347) B440347
theorem B390687 : Blo 389765 390687 := bstep (se 1 (by rfl) ⟨293015, by rfl⟩ : syracuseStep 390687 = 586031) B586031
theorem B391103 : Blo 389765 391103 := bstep (se 1 (by rfl) ⟨293327, by rfl⟩ : syracuseStep 391103 = 586655) B586655
theorem B391167 : Blo 389765 391167 := bstep (se 1 (by rfl) ⟨293375, by rfl⟩ : syracuseStep 391167 = 586751) B586751
theorem B391407 : Blo 389765 391407 := bstep (se 1 (by rfl) ⟨293555, by rfl⟩ : syracuseStep 391407 = 587111) B587111
theorem B391871 : Blo 389765 391871 := bstep (se 1 (by rfl) ⟨293903, by rfl⟩ : syracuseStep 391871 = 587807) B587807
theorem B392255 : Blo 389765 392255 := bstep (se 1 (by rfl) ⟨294191, by rfl⟩ : syracuseStep 392255 = 588383) B588383
theorem B588863 : Blo 389765 588863 := bstep (se 1 (by rfl) ⟨441647, by rfl⟩ : syracuseStep 588863 = 883295) B883295
theorem B588911 : Blo 389765 588911 := bstep (se 1 (by rfl) ⟨441683, by rfl⟩ : syracuseStep 588911 = 883367) B883367
theorem B392319 : Blo 389765 392319 := bstep (se 1 (by rfl) ⟨294239, by rfl⟩ : syracuseStep 392319 = 588479) B588479
theorem B589799 : Blo 389765 589799 := bstep (se 1 (by rfl) ⟨442349, by rfl⟩ : syracuseStep 589799 = 884699) B884699
theorem B589871 : Blo 389765 589871 := bstep (se 1 (by rfl) ⟨442403, by rfl⟩ : syracuseStep 589871 = 884807) B884807
theorem B884843 : Blo 389765 884843 := bstep (se 1 (by rfl) ⟨663632, by rfl⟩ : syracuseStep 884843 = 1327265) B1327265
theorem B393375 : Blo 389765 393375 := bstep (se 1 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 393375 = 590063) B590063
theorem B884969 : Blo 389765 884969 := bstep (se 2 (by rfl) ⟨331863, by rfl⟩ : syracuseStep 884969 = 663727) B663727
theorem B393663 : Blo 389765 393663 := bstep (se 1 (by rfl) ⟨295247, by rfl⟩ : syracuseStep 393663 = 590495) B590495
theorem B885851 : Blo 389765 885851 := bstep (se 1 (by rfl) ⟨664388, by rfl⟩ : syracuseStep 885851 = 1328777) B1328777
theorem B1115689 : Blo 389765 1115689 := bstep (se 2 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 1115689 = 836767) B836767
theorem B22087709 : Blo 389765 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B235736237 : Blo 389765 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B986863 : Blo 389765 986863 := bstep (se 1 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 986863 = 1480295) B1480295
theorem B988139 : Blo 389765 988139 := bstep (se 1 (by rfl) ⟨741104, by rfl⟩ : syracuseStep 988139 = 1482209) B1482209
theorem B1315871 : Blo 389765 1315871 := bstep (se 1 (by rfl) ⟨986903, by rfl⟩ : syracuseStep 1315871 = 1973807) B1973807
theorem B1677635 : Blo 389765 1677635 := bstep (se 1 (by rfl) ⟨1258226, by rfl⟩ : syracuseStep 1677635 = 2516453) B2516453
theorem B1317383 : Blo 389765 1317383 := bstep (se 1 (by rfl) ⟨988037, by rfl⟩ : syracuseStep 1317383 = 1976075) B1976075
theorem B662303 : Blo 389765 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B4464395 : Blo 389765 4464395 := bstep (se 1 (by rfl) ⟨3348296, by rfl⟩ : syracuseStep 4464395 = 6696593) B6696593
theorem B663545 : Blo 389765 663545 := bstep (se 2 (by rfl) ⟨248829, by rfl⟩ : syracuseStep 663545 = 497659) B497659
theorem B1056959 : Blo 389765 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B992027 : Blo 389765 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B2237665 : Blo 389765 2237665 := bstep (se 2 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 2237665 = 1678249) B1678249
theorem B1320623 : Blo 389765 1320623 := bstep (se 1 (by rfl) ⟨990467, by rfl⟩ : syracuseStep 1320623 = 1980935) B1980935
theorem B2500409 : Blo 389765 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B5384303 : Blo 389765 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B3746537 : Blo 389765 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B5483351 : Blo 389765 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B3190013 : Blo 389765 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B1324457 : Blo 389765 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B6796831 : Blo 389765 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B8468459 : Blo 389765 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B636959 : Blo 389765 636959 := bstep (se 1 (by rfl) ⟨477719, by rfl⟩ : syracuseStep 636959 = 955439) B955439
theorem B440527 : Blo 389765 440527 := bstep (se 1 (by rfl) ⟨330395, by rfl⟩ : syracuseStep 440527 = 660791) B660791
theorem B1259803 : Blo 389765 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B440959 : Blo 389765 440959 := bstep (se 1 (by rfl) ⟨330719, by rfl⟩ : syracuseStep 440959 = 661439) B661439
theorem B2538215 : Blo 389765 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B8469841 : Blo 389765 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B7126579 : Blo 389765 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B11255759 : Blo 389765 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B97601435 : Blo 389765 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B2967515 : Blo 389765 2967515 := bstep (se 1 (by rfl) ⟨2225636, by rfl⟩ : syracuseStep 2967515 = 4451273) B4451273
theorem B1002095 : Blo 389765 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B2509481 : Blo 389765 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B936731 : Blo 389765 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B23252183 : Blo 389765 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B839963 : Blo 389765 839963 := bstep (se 1 (by rfl) ⟨629972, by rfl⟩ : syracuseStep 839963 = 1259945) B1259945
theorem B742783 : Blo 389765 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B2119193 : Blo 389765 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B745129 : Blo 389765 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B745919 : Blo 389765 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B1335935 : Blo 389765 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B44229341 : Blo 389765 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B877751 : Blo 389765 877751 := bstep (se 1 (by rfl) ⟨658313, by rfl⟩ : syracuseStep 877751 = 1316627) B1316627
theorem B877823 : Blo 389765 877823 := bstep (se 1 (by rfl) ⟨658367, by rfl⟩ : syracuseStep 877823 = 1316735) B1316735
theorem B878327 : Blo 389765 878327 := bstep (se 1 (by rfl) ⟨658745, by rfl⟩ : syracuseStep 878327 = 1317491) B1317491
theorem B420071 : Blo 389765 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B878867 : Blo 389765 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B878975 : Blo 389765 878975 := bstep (se 1 (by rfl) ⟨659231, by rfl⟩ : syracuseStep 878975 = 1318463) B1318463
theorem B6777431 : Blo 389765 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B27224747 : Blo 389765 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B584687 : Blo 389765 584687 := bstep (se 1 (by rfl) ⟨438515, by rfl⟩ : syracuseStep 584687 = 877031) B877031
theorem B5009687 : Blo 389765 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B880991 : Blo 389765 880991 := bstep (se 1 (by rfl) ⟨660743, by rfl⟩ : syracuseStep 880991 = 1321487) B1321487
theorem B6943103 : Blo 389765 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B2978207 : Blo 389765 2978207 := bstep (se 1 (by rfl) ⟨2233655, by rfl⟩ : syracuseStep 2978207 = 4467311) B4467311
theorem B2225069 : Blo 389765 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B390175 : Blo 389765 390175 := bstep (se 1 (by rfl) ⟨292631, by rfl⟩ : syracuseStep 390175 = 585263) B585263
theorem B390427 : Blo 389765 390427 := bstep (se 1 (by rfl) ⟨292820, by rfl⟩ : syracuseStep 390427 = 585641) B585641
theorem B587135 : Blo 389765 587135 := bstep (se 1 (by rfl) ⟨440351, by rfl⟩ : syracuseStep 587135 = 880703) B880703
theorem B390863 : Blo 389765 390863 := bstep (se 1 (by rfl) ⟨293147, by rfl⟩ : syracuseStep 390863 = 586295) B586295
theorem B882395 : Blo 389765 882395 := bstep (se 1 (by rfl) ⟨661796, by rfl⟩ : syracuseStep 882395 = 1323593) B1323593
theorem B390887 : Blo 389765 390887 := bstep (se 1 (by rfl) ⟨293165, by rfl⟩ : syracuseStep 390887 = 586331) B586331
theorem B1111931 : Blo 389765 1111931 := bstep (se 1 (by rfl) ⟨833948, by rfl⟩ : syracuseStep 1111931 = 1667897) B1667897
theorem B391079 : Blo 389765 391079 := bstep (se 1 (by rfl) ⟨293309, by rfl⟩ : syracuseStep 391079 = 586619) B586619
theorem B1701875 : Blo 389765 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B391375 : Blo 389765 391375 := bstep (se 1 (by rfl) ⟨293531, by rfl⟩ : syracuseStep 391375 = 587063) B587063
theorem B391419 : Blo 389765 391419 := bstep (se 1 (by rfl) ⟨293564, by rfl⟩ : syracuseStep 391419 = 587129) B587129
theorem B883583 : Blo 389765 883583 := bstep (se 1 (by rfl) ⟨662687, by rfl⟩ : syracuseStep 883583 = 1325375) B1325375
theorem B883871 : Blo 389765 883871 := bstep (se 1 (by rfl) ⟨662903, by rfl⟩ : syracuseStep 883871 = 1325807) B1325807
theorem B392575 : Blo 389765 392575 := bstep (se 1 (by rfl) ⟨294431, by rfl⟩ : syracuseStep 392575 = 588863) B588863
theorem B392607 : Blo 389765 392607 := bstep (se 1 (by rfl) ⟨294455, by rfl⟩ : syracuseStep 392607 = 588911) B588911
theorem B884591 : Blo 389765 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B393199 : Blo 389765 393199 := bstep (se 1 (by rfl) ⟨294899, by rfl⟩ : syracuseStep 393199 = 589799) B589799
theorem B393247 : Blo 389765 393247 := bstep (se 1 (by rfl) ⟨294935, by rfl⟩ : syracuseStep 393247 = 589871) B589871
theorem B589895 : Blo 389765 589895 := bstep (se 1 (by rfl) ⟨442421, by rfl⟩ : syracuseStep 589895 = 884843) B884843
theorem B589979 : Blo 389765 589979 := bstep (se 1 (by rfl) ⟨442484, by rfl⟩ : syracuseStep 589979 = 884969) B884969
theorem B235602229 : Blo 389765 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B590567 : Blo 389765 590567 := bstep (se 1 (by rfl) ⟨442925, by rfl⟩ : syracuseStep 590567 = 885851) B885851
theorem B2983553 : Blo 389765 2983553 := bstep (se 2 (by rfl) ⟨1118832, by rfl⟩ : syracuseStep 2983553 = 2237665) B2237665
theorem B1672987 : Blo 389765 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B157157491 : Blo 389765 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B15501455 : Blo 389765 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B559975 : Blo 389765 559975 := bstep (se 1 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 559975 = 839963) B839963
theorem B658759 : Blo 389765 658759 := bstep (se 1 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 658759 = 988139) B988139
theorem B1412795 : Blo 389765 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B1118423 : Blo 389765 1118423 := bstep (se 1 (by rfl) ⟨838817, by rfl⟩ : syracuseStep 1118423 = 1677635) B1677635
theorem B1315817 : Blo 389765 1315817 := bstep (se 2 (by rfl) ⟨493431, by rfl⟩ : syracuseStep 1315817 = 986863) B986863
theorem B497279 : Blo 389765 497279 := bstep (se 1 (by rfl) ⟨372959, by rfl⟩ : syracuseStep 497279 = 745919) B745919
theorem B890623 : Blo 389765 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B661351 : Blo 389765 661351 := bstep (se 1 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 661351 = 992027) B992027
theorem B1120189 : Blo 389765 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B2497691 : Blo 389765 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B990377 : Blo 389765 990377 := bstep (se 2 (by rfl) ⟨371391, by rfl⟩ : syracuseStep 990377 = 742783) B742783
theorem B2497949 : Blo 389765 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B4628735 : Blo 389765 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B1679737 : Blo 389765 1679737 := bstep (se 2 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 1679737 = 1259803) B1259803
theorem B1483379 : Blo 389765 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B5645639 : Blo 389765 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B993505 : Blo 389765 993505 := bstep (se 2 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 993505 = 745129) B745129
theorem B1978343 : Blo 389765 1978343 := bstep (se 1 (by rfl) ⟨1483757, by rfl⟩ : syracuseStep 1978343 = 2967515) B2967515
theorem B668063 : Blo 389765 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B1487585 : Blo 389765 1487585 := bstep (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) B1115689
theorem B441535 : Blo 389765 441535 := bstep (se 1 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 441535 = 662303) B662303
theorem B4538333 : Blo 389765 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B442363 : Blo 389765 442363 := bstep (se 1 (by rfl) ⟨331772, by rfl⟩ : syracuseStep 442363 = 663545) B663545
theorem B704639 : Blo 389765 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B3589535 : Blo 389765 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B3655567 : Blo 389765 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B9062441 : Blo 389765 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1985471 : Blo 389765 1985471 := bstep (se 1 (by rfl) ⟨1489103, by rfl⟩ : syracuseStep 1985471 = 2978207) B2978207
theorem B741287 : Blo 389765 741287 := bstep (se 1 (by rfl) ⟨555965, by rfl⟩ : syracuseStep 741287 = 1111931) B1111931
theorem B11293121 : Blo 389765 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1692143 : Blo 389765 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B65067623 : Blo 389765 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B877247 : Blo 389765 877247 := bstep (se 1 (by rfl) ⟨657935, by rfl⟩ : syracuseStep 877247 = 1315871) B1315871
theorem B878255 : Blo 389765 878255 := bstep (se 1 (by rfl) ⟨658691, by rfl⟩ : syracuseStep 878255 = 1317383) B1317383
theorem B2976263 : Blo 389765 2976263 := bstep (se 1 (by rfl) ⟨2232197, by rfl⟩ : syracuseStep 2976263 = 4464395) B4464395
theorem B29486227 : Blo 389765 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B585167 : Blo 389765 585167 := bstep (se 1 (by rfl) ⟨438875, by rfl⟩ : syracuseStep 585167 = 877751) B877751
theorem B585215 : Blo 389765 585215 := bstep (se 1 (by rfl) ⟨438911, by rfl⟩ : syracuseStep 585215 = 877823) B877823
theorem B880415 : Blo 389765 880415 := bstep (se 1 (by rfl) ⟨660311, by rfl⟩ : syracuseStep 880415 = 1320623) B1320623
theorem B585551 : Blo 389765 585551 := bstep (se 1 (by rfl) ⟨439163, by rfl⟩ : syracuseStep 585551 = 878327) B878327
theorem B1666939 : Blo 389765 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B585911 : Blo 389765 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B585983 : Blo 389765 585983 := bstep (se 1 (by rfl) ⟨439487, by rfl⟩ : syracuseStep 585983 = 878975) B878975
theorem B4518287 : Blo 389765 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B18149831 : Blo 389765 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B389791 : Blo 389765 389791 := bstep (se 1 (by rfl) ⟨292343, by rfl⟩ : syracuseStep 389791 = 584687) B584687
theorem B2126675 : Blo 389765 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B3339791 : Blo 389765 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B587327 : Blo 389765 587327 := bstep (se 1 (by rfl) ⟨440495, by rfl⟩ : syracuseStep 587327 = 880991) B880991
theorem B587369 : Blo 389765 587369 := bstep (se 2 (by rfl) ⟨220263, by rfl⟩ : syracuseStep 587369 = 440527) B440527
theorem B587945 : Blo 389765 587945 := bstep (se 2 (by rfl) ⟨220479, by rfl⟩ : syracuseStep 587945 = 440959) B440959
theorem B391423 : Blo 389765 391423 := bstep (se 1 (by rfl) ⟨293567, by rfl⟩ : syracuseStep 391423 = 587135) B587135
theorem B882971 : Blo 389765 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B588263 : Blo 389765 588263 := bstep (se 1 (by rfl) ⟨441197, by rfl⟩ : syracuseStep 588263 = 882395) B882395
theorem B424639 : Blo 389765 424639 := bstep (se 1 (by rfl) ⟨318479, by rfl⟩ : syracuseStep 424639 = 636959) B636959
theorem B589055 : Blo 389765 589055 := bstep (se 1 (by rfl) ⟨441791, by rfl⟩ : syracuseStep 589055 = 883583) B883583
theorem B9502105 : Blo 389765 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B589247 : Blo 389765 589247 := bstep (se 1 (by rfl) ⟨441935, by rfl⟩ : syracuseStep 589247 = 883871) B883871
theorem B589727 : Blo 389765 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B7503839 : Blo 389765 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B393263 : Blo 389765 393263 := bstep (se 1 (by rfl) ⟨294947, by rfl⟩ : syracuseStep 393263 = 589895) B589895
theorem B393319 : Blo 389765 393319 := bstep (se 1 (by rfl) ⟨294989, by rfl⟩ : syracuseStep 393319 = 589979) B589979
theorem B393711 : Blo 389765 393711 := bstep (se 1 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 393711 = 590567) B590567
theorem B2393023 : Blo 389765 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B5671133 : Blo 389765 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B2230649 : Blo 389765 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B494191 : Blo 389765 494191 := bstep (se 1 (by rfl) ⟨370643, by rfl⟩ : syracuseStep 494191 = 741287) B741287
theorem B660251 : Blo 389765 660251 := bstep (se 1 (by rfl) ⟨495188, by rfl⟩ : syracuseStep 660251 = 990377) B990377
theorem B3085823 : Blo 389765 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B988919 : Blo 389765 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1187497 : Blo 389765 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B1318895 : Blo 389765 1318895 := bstep (se 1 (by rfl) ⟨989171, by rfl⟩ : syracuseStep 1318895 = 1978343) B1978343
theorem B12099887 : Blo 389765 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B991723 : Blo 389765 991723 := bstep (se 1 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 991723 = 1487585) B1487585
theorem B566185 : Blo 389765 566185 := bstep (se 2 (by rfl) ⟨212319, by rfl⟩ : syracuseStep 566185 = 424639) B424639
theorem B3025555 : Blo 389765 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B1879037 : Blo 389765 1879037 := bstep (se 3 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 1879037 = 704639) B704639
theorem B2239649 : Blo 389765 2239649 := bstep (se 2 (by rfl) ⟨839868, by rfl⟩ : syracuseStep 2239649 = 1679737) B1679737
theorem B6041627 : Blo 389765 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B10334303 : Blo 389765 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B1323647 : Blo 389765 1323647 := bstep (se 1 (by rfl) ⟨992735, by rfl⟩ : syracuseStep 1323647 = 1985471) B1985471
theorem B1324673 : Blo 389765 1324673 := bstep (se 2 (by rfl) ⟨496752, by rfl⟩ : syracuseStep 1324673 = 993505) B993505
theorem B1128095 : Blo 389765 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1326077 : Blo 389765 1326077 := bstep (se 3 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 1326077 = 497279) B497279
theorem B1984175 : Blo 389765 1984175 := bstep (se 1 (by rfl) ⟨1488131, by rfl⟩ : syracuseStep 1984175 = 2976263) B2976263
theorem B1493585 : Blo 389765 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B445375 : Blo 389765 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B12669473 : Blo 389765 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B5002559 : Blo 389765 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B314136305 : Blo 389765 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B1989035 : Blo 389765 1989035 := bstep (se 1 (by rfl) ⟨1491776, by rfl⟩ : syracuseStep 1989035 = 2983553) B2983553
theorem B941863 : Blo 389765 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B4874089 : Blo 389765 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B745615 : Blo 389765 745615 := bstep (se 1 (by rfl) ⟨559211, by rfl⟩ : syracuseStep 745615 = 1118423) B1118423
theorem B209543321 : Blo 389765 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B7528747 : Blo 389765 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B877211 : Blo 389765 877211 := bstep (se 1 (by rfl) ⟨657908, by rfl⟩ : syracuseStep 877211 = 1315817) B1315817
theorem B746633 : Blo 389765 746633 := bstep (se 2 (by rfl) ⟨279987, by rfl⟩ : syracuseStep 746633 = 559975) B559975
theorem B39314969 : Blo 389765 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B43378415 : Blo 389765 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B878345 : Blo 389765 878345 := bstep (se 2 (by rfl) ⟨329379, by rfl⟩ : syracuseStep 878345 = 658759) B658759
theorem B1665127 : Blo 389765 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B1665299 : Blo 389765 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B2222585 : Blo 389765 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B584831 : Blo 389765 584831 := bstep (se 1 (by rfl) ⟨438623, by rfl⟩ : syracuseStep 584831 = 877247) B877247
theorem B3763759 : Blo 389765 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B585503 : Blo 389765 585503 := bstep (se 1 (by rfl) ⟨439127, by rfl⟩ : syracuseStep 585503 = 878255) B878255
theorem B390111 : Blo 389765 390111 := bstep (se 1 (by rfl) ⟨292583, by rfl⟩ : syracuseStep 390111 = 585167) B585167
theorem B390143 : Blo 389765 390143 := bstep (se 1 (by rfl) ⟨292607, by rfl⟩ : syracuseStep 390143 = 585215) B585215
theorem B881801 : Blo 389765 881801 := bstep (se 2 (by rfl) ⟨330675, by rfl⟩ : syracuseStep 881801 = 661351) B661351
theorem B586943 : Blo 389765 586943 := bstep (se 1 (by rfl) ⟨440207, by rfl⟩ : syracuseStep 586943 = 880415) B880415
theorem B390367 : Blo 389765 390367 := bstep (se 1 (by rfl) ⟨292775, by rfl⟩ : syracuseStep 390367 = 585551) B585551
theorem B390607 : Blo 389765 390607 := bstep (se 1 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 390607 = 585911) B585911
theorem B390655 : Blo 389765 390655 := bstep (se 1 (by rfl) ⟨292991, by rfl⟩ : syracuseStep 390655 = 585983) B585983
theorem B3012191 : Blo 389765 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B2226527 : Blo 389765 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B391551 : Blo 389765 391551 := bstep (se 1 (by rfl) ⟨293663, by rfl⟩ : syracuseStep 391551 = 587327) B587327
theorem B391579 : Blo 389765 391579 := bstep (se 1 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 391579 = 587369) B587369
theorem B391963 : Blo 389765 391963 := bstep (se 1 (by rfl) ⟨293972, by rfl⟩ : syracuseStep 391963 = 587945) B587945
theorem B588647 : Blo 389765 588647 := bstep (se 1 (by rfl) ⟨441485, by rfl⟩ : syracuseStep 588647 = 882971) B882971
theorem B588713 : Blo 389765 588713 := bstep (se 2 (by rfl) ⟨220767, by rfl⟩ : syracuseStep 588713 = 441535) B441535
theorem B392175 : Blo 389765 392175 := bstep (se 1 (by rfl) ⟨294131, by rfl⟩ : syracuseStep 392175 = 588263) B588263
theorem B392703 : Blo 389765 392703 := bstep (se 1 (by rfl) ⟨294527, by rfl⟩ : syracuseStep 392703 = 589055) B589055
theorem B392831 : Blo 389765 392831 := bstep (se 1 (by rfl) ⟨294623, by rfl⟩ : syracuseStep 392831 = 589247) B589247
theorem B393151 : Blo 389765 393151 := bstep (se 1 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 393151 = 589727) B589727
theorem B589817 : Blo 389765 589817 := bstep (se 2 (by rfl) ⟨221181, by rfl⟩ : syracuseStep 589817 = 442363) B442363
theorem B754913 : Blo 389765 754913 := bstep (se 2 (by rfl) ⟨283092, by rfl⟩ : syracuseStep 754913 = 566185) B566185
theorem B658921 : Blo 389765 658921 := bstep (se 2 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 658921 = 494191) B494191
theorem B209424203 : Blo 389765 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B659279 : Blo 389765 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B8228861 : Blo 389765 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B5018345 : Blo 389765 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B139695547 : Blo 389765 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B8066591 : Blo 389765 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B497755 : Blo 389765 497755 := bstep (se 1 (by rfl) ⟨373316, by rfl⟩ : syracuseStep 497755 = 746633) B746633
theorem B1481723 : Blo 389765 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B1252691 : Blo 389765 1252691 := bstep (se 1 (by rfl) ⟨939518, by rfl⟩ : syracuseStep 1252691 = 1879037) B1879037
theorem B6889535 : Blo 389765 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1484351 : Blo 389765 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B1583329 : Blo 389765 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B1255817 : Blo 389765 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B6498785 : Blo 389765 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B994153 : Blo 389765 994153 := bstep (se 2 (by rfl) ⟨372807, by rfl⟩ : syracuseStep 994153 = 745615) B745615
theorem B10038329 : Blo 389765 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B1322297 : Blo 389765 1322297 := bstep (se 2 (by rfl) ⟨495861, by rfl⟩ : syracuseStep 1322297 = 991723) B991723
theorem B1322783 : Blo 389765 1322783 := bstep (se 1 (by rfl) ⟨992087, by rfl⟩ : syracuseStep 1322783 = 1984175) B1984175
theorem B3190697 : Blo 389765 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B3780755 : Blo 389765 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B1487099 : Blo 389765 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B995723 : Blo 389765 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B440167 : Blo 389765 440167 := bstep (se 1 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 440167 = 660251) B660251
theorem B1326023 : Blo 389765 1326023 := bstep (se 1 (by rfl) ⟨994517, by rfl⟩ : syracuseStep 1326023 = 1989035) B1989035
theorem B2375333 : Blo 389765 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B32130037 : Blo 389765 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B28918943 : Blo 389765 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B1493099 : Blo 389765 1493099 := bstep (se 1 (by rfl) ⟨1119824, by rfl⟩ : syracuseStep 1493099 = 2239649) B2239649
theorem B2220169 : Blo 389765 2220169 := bstep (se 2 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 2220169 = 1665127) B1665127
theorem B8446315 : Blo 389765 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B64545173 : Blo 389765 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B3335039 : Blo 389765 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B879263 : Blo 389765 879263 := bstep (se 1 (by rfl) ⟨659447, by rfl⟩ : syracuseStep 879263 = 1318895) B1318895
theorem B584807 : Blo 389765 584807 := bstep (se 1 (by rfl) ⟨438605, by rfl⟩ : syracuseStep 584807 = 877211) B877211
theorem B26209979 : Blo 389765 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B585563 : Blo 389765 585563 := bstep (se 1 (by rfl) ⟨439172, by rfl⟩ : syracuseStep 585563 = 878345) B878345
theorem B1110199 : Blo 389765 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B389887 : Blo 389765 389887 := bstep (se 1 (by rfl) ⟨292415, by rfl⟩ : syracuseStep 389887 = 584831) B584831
theorem B390335 : Blo 389765 390335 := bstep (se 1 (by rfl) ⟨292751, by rfl⟩ : syracuseStep 390335 = 585503) B585503
theorem B4027751 : Blo 389765 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B882431 : Blo 389765 882431 := bstep (se 1 (by rfl) ⟨661823, by rfl⟩ : syracuseStep 882431 = 1323647) B1323647
theorem B587867 : Blo 389765 587867 := bstep (se 1 (by rfl) ⟨440900, by rfl⟩ : syracuseStep 587867 = 881801) B881801
theorem B391295 : Blo 389765 391295 := bstep (se 1 (by rfl) ⟨293471, by rfl⟩ : syracuseStep 391295 = 586943) B586943
theorem B883115 : Blo 389765 883115 := bstep (se 1 (by rfl) ⟨662336, by rfl⟩ : syracuseStep 883115 = 1324673) B1324673
theorem B752063 : Blo 389765 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B392431 : Blo 389765 392431 := bstep (se 1 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 392431 = 588647) B588647
theorem B392475 : Blo 389765 392475 := bstep (se 1 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 392475 = 588713) B588713
theorem B884051 : Blo 389765 884051 := bstep (se 1 (by rfl) ⟨663038, by rfl⟩ : syracuseStep 884051 = 1326077) B1326077
theorem B393211 : Blo 389765 393211 := bstep (se 1 (by rfl) ⟨294908, by rfl⟩ : syracuseStep 393211 = 589817) B589817
theorem B3345563 : Blo 389765 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B5377727 : Blo 389765 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B987815 : Blo 389765 987815 := bstep (se 1 (by rfl) ⟨740861, by rfl⟩ : syracuseStep 987815 = 1481723) B1481723
theorem B4593023 : Blo 389765 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B1480265 : Blo 389765 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B43030115 : Blo 389765 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B989567 : Blo 389765 989567 := bstep (se 1 (by rfl) ⟨742175, by rfl⟩ : syracuseStep 989567 = 1484351) B1484351
theorem B2005501 : Blo 389765 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B4332523 : Blo 389765 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B186260729 : Blo 389765 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B6692219 : Blo 389765 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B17473319 : Blo 389765 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B663673 : Blo 389765 663673 := bstep (se 2 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 663673 = 497755) B497755
theorem B991399 : Blo 389765 991399 := bstep (se 1 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 991399 = 1487099) B1487099
theorem B663815 : Blo 389765 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B1583555 : Blo 389765 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B2960225 : Blo 389765 2960225 := bstep (se 2 (by rfl) ⟨1110084, by rfl⟩ : syracuseStep 2960225 = 2220169) B2220169
theorem B19279295 : Blo 389765 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B503275 : Blo 389765 503275 := bstep (se 1 (by rfl) ⟨377456, by rfl⟩ : syracuseStep 503275 = 754913) B754913
theorem B42840049 : Blo 389765 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B995399 : Blo 389765 995399 := bstep (se 1 (by rfl) ⟨746549, by rfl⟩ : syracuseStep 995399 = 1493099) B1493099
theorem B439519 : Blo 389765 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B5485907 : Blo 389765 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B2111105 : Blo 389765 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1325537 : Blo 389765 1325537 := bstep (se 2 (by rfl) ⟨497076, by rfl⟩ : syracuseStep 1325537 = 994153) B994153
theorem B835127 : Blo 389765 835127 := bstep (se 1 (by rfl) ⟨626345, by rfl⟩ : syracuseStep 835127 = 1252691) B1252691
theorem B837211 : Blo 389765 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B11261753 : Blo 389765 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B139616135 : Blo 389765 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B878561 : Blo 389765 878561 := bstep (se 2 (by rfl) ⟨329460, by rfl⟩ : syracuseStep 878561 = 658921) B658921
theorem B2223359 : Blo 389765 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B586175 : Blo 389765 586175 := bstep (se 1 (by rfl) ⟨439631, by rfl⟩ : syracuseStep 586175 = 879263) B879263
theorem B389871 : Blo 389765 389871 := bstep (se 1 (by rfl) ⟨292403, by rfl⟩ : syracuseStep 389871 = 584807) B584807
theorem B881531 : Blo 389765 881531 := bstep (se 1 (by rfl) ⟨661148, by rfl⟩ : syracuseStep 881531 = 1322297) B1322297
theorem B586889 : Blo 389765 586889 := bstep (se 2 (by rfl) ⟨220083, by rfl⟩ : syracuseStep 586889 = 440167) B440167
theorem B881855 : Blo 389765 881855 := bstep (se 1 (by rfl) ⟨661391, by rfl⟩ : syracuseStep 881855 = 1322783) B1322783
theorem B390375 : Blo 389765 390375 := bstep (se 1 (by rfl) ⟨292781, by rfl⟩ : syracuseStep 390375 = 585563) B585563
theorem B2127131 : Blo 389765 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B2520503 : Blo 389765 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B2685167 : Blo 389765 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B588287 : Blo 389765 588287 := bstep (se 1 (by rfl) ⟨441215, by rfl⟩ : syracuseStep 588287 = 882431) B882431
theorem B391911 : Blo 389765 391911 := bstep (se 1 (by rfl) ⟨293933, by rfl⟩ : syracuseStep 391911 = 587867) B587867
theorem B588743 : Blo 389765 588743 := bstep (se 1 (by rfl) ⟨441557, by rfl⟩ : syracuseStep 588743 = 883115) B883115
theorem B884015 : Blo 389765 884015 := bstep (se 1 (by rfl) ⟨663011, by rfl⟩ : syracuseStep 884015 = 1326023) B1326023
theorem B589367 : Blo 389765 589367 := bstep (se 1 (by rfl) ⟨442025, by rfl⟩ : syracuseStep 589367 = 884051) B884051
theorem B884897 : Blo 389765 884897 := bstep (se 2 (by rfl) ⟨331836, by rfl⟩ : syracuseStep 884897 = 663673) B663673
theorem B2230375 : Blo 389765 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B1116281 : Blo 389765 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B658543 : Blo 389765 658543 := bstep (se 1 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 658543 = 987815) B987815
theorem B986843 : Blo 389765 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B7507835 : Blo 389765 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B659711 : Blo 389765 659711 := bstep (se 1 (by rfl) ⟨494783, by rfl⟩ : syracuseStep 659711 = 989567) B989567
theorem B4461479 : Blo 389765 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B57120065 : Blo 389765 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B1973483 : Blo 389765 1973483 := bstep (se 1 (by rfl) ⟨1480112, by rfl⟩ : syracuseStep 1973483 = 2960225) B2960225
theorem B1482239 : Blo 389765 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B12852863 : Blo 389765 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B663599 : Blo 389765 663599 := bstep (se 1 (by rfl) ⟨497699, by rfl⟩ : syracuseStep 663599 = 995399) B995399
theorem B1418087 : Blo 389765 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1680335 : Blo 389765 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B5776697 : Blo 389765 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B1321865 : Blo 389765 1321865 := bstep (se 2 (by rfl) ⟨495699, by rfl⟩ : syracuseStep 1321865 = 991399) B991399
theorem B3585151 : Blo 389765 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B14629085 : Blo 389765 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B3062015 : Blo 389765 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B28686743 : Blo 389765 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B671033 : Blo 389765 671033 := bstep (se 2 (by rfl) ⟨251637, by rfl⟩ : syracuseStep 671033 = 503275) B503275
theorem B11648879 : Blo 389765 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B93077423 : Blo 389765 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B442543 : Blo 389765 442543 := bstep (se 1 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 442543 = 663815) B663815
theorem B2674001 : Blo 389765 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1790111 : Blo 389765 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B4222813 : Blo 389765 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B585707 : Blo 389765 585707 := bstep (se 1 (by rfl) ⟨439280, by rfl⟩ : syracuseStep 585707 = 878561) B878561
theorem B586025 : Blo 389765 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B390783 : Blo 389765 390783 := bstep (se 1 (by rfl) ⟨293087, by rfl⟩ : syracuseStep 390783 = 586175) B586175
theorem B587687 : Blo 389765 587687 := bstep (se 1 (by rfl) ⟨440765, by rfl⟩ : syracuseStep 587687 = 881531) B881531
theorem B496695277 : Blo 389765 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B391259 : Blo 389765 391259 := bstep (se 1 (by rfl) ⟨293444, by rfl⟩ : syracuseStep 391259 = 586889) B586889
theorem B587903 : Blo 389765 587903 := bstep (se 1 (by rfl) ⟨440927, by rfl⟩ : syracuseStep 587903 = 881855) B881855
theorem B1407403 : Blo 389765 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B883691 : Blo 389765 883691 := bstep (se 1 (by rfl) ⟨662768, by rfl⟩ : syracuseStep 883691 = 1325537) B1325537
theorem B392191 : Blo 389765 392191 := bstep (se 1 (by rfl) ⟨294143, by rfl⟩ : syracuseStep 392191 = 588287) B588287
theorem B392495 : Blo 389765 392495 := bstep (se 1 (by rfl) ⟨294371, by rfl⟩ : syracuseStep 392495 = 588743) B588743
theorem B589343 : Blo 389765 589343 := bstep (se 1 (by rfl) ⟨442007, by rfl⟩ : syracuseStep 589343 = 884015) B884015
theorem B556751 : Blo 389765 556751 := bstep (se 1 (by rfl) ⟨417563, by rfl⟩ : syracuseStep 556751 = 835127) B835127
theorem B392911 : Blo 389765 392911 := bstep (se 1 (by rfl) ⟨294683, by rfl⟩ : syracuseStep 392911 = 589367) B589367
theorem B589931 : Blo 389765 589931 := bstep (se 1 (by rfl) ⟨442448, by rfl⟩ : syracuseStep 589931 = 884897) B884897
theorem B590057 : Blo 389765 590057 := bstep (se 2 (by rfl) ⟨221271, by rfl⟩ : syracuseStep 590057 = 442543) B442543
theorem B657895 : Blo 389765 657895 := bstep (se 1 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 657895 = 986843) B986843
theorem B15404525 : Blo 389765 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B38080043 : Blo 389765 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B1315655 : Blo 389765 1315655 := bstep (se 1 (by rfl) ⟨986741, by rfl⟩ : syracuseStep 1315655 = 1973483) B1973483
theorem B988159 : Blo 389765 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B1120223 : Blo 389765 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B1876537 : Blo 389765 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B2041343 : Blo 389765 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B1484669 : Blo 389765 1484669 := bstep (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) B556751
theorem B1782667 : Blo 389765 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B3781565 : Blo 389765 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B439807 : Blo 389765 439807 := bstep (se 1 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 439807 = 659711) B659711
theorem B8568575 : Blo 389765 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B442399 : Blo 389765 442399 := bstep (se 1 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 442399 = 663599) B663599
theorem B19120805 : Blo 389765 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B662260369 : Blo 389765 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B9752723 : Blo 389765 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B19124495 : Blo 389765 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B447355 : Blo 389765 447355 := bstep (se 1 (by rfl) ⟨335516, by rfl⟩ : syracuseStep 447355 = 671033) B671033
theorem B62051615 : Blo 389765 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B4773629 : Blo 389765 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B5005223 : Blo 389765 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B2973833 : Blo 389765 2973833 := bstep (se 2 (by rfl) ⟨1115187, by rfl⟩ : syracuseStep 2973833 = 2230375) B2230375
theorem B2974319 : Blo 389765 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B878057 : Blo 389765 878057 := bstep (se 2 (by rfl) ⟨329271, by rfl⟩ : syracuseStep 878057 = 658543) B658543
theorem B5630417 : Blo 389765 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B2976749 : Blo 389765 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B881243 : Blo 389765 881243 := bstep (se 1 (by rfl) ⟨660932, by rfl⟩ : syracuseStep 881243 = 1321865) B1321865
theorem B390471 : Blo 389765 390471 := bstep (se 1 (by rfl) ⟨292853, by rfl⟩ : syracuseStep 390471 = 585707) B585707
theorem B390683 : Blo 389765 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B391791 : Blo 389765 391791 := bstep (se 1 (by rfl) ⟨293843, by rfl⟩ : syracuseStep 391791 = 587687) B587687
theorem B391935 : Blo 389765 391935 := bstep (se 1 (by rfl) ⟨293951, by rfl⟩ : syracuseStep 391935 = 587903) B587903
theorem B589127 : Blo 389765 589127 := bstep (se 1 (by rfl) ⟨441845, by rfl⟩ : syracuseStep 589127 = 883691) B883691
theorem B392895 : Blo 389765 392895 := bstep (se 1 (by rfl) ⟨294671, by rfl⟩ : syracuseStep 392895 = 589343) B589343
theorem B7765919 : Blo 389765 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B589865 : Blo 389765 589865 := bstep (se 2 (by rfl) ⟨221199, by rfl⟩ : syracuseStep 589865 = 442399) B442399
theorem B393287 : Blo 389765 393287 := bstep (se 1 (by rfl) ⟨294965, by rfl⟩ : syracuseStep 393287 = 589931) B589931
theorem B393371 : Blo 389765 393371 := bstep (se 1 (by rfl) ⟨295028, by rfl⟩ : syracuseStep 393371 = 590057) B590057
theorem B12747203 : Blo 389765 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B12749663 : Blo 389765 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B3182419 : Blo 389765 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B9507557 : Blo 389765 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B596473 : Blo 389765 596473 := bstep (se 2 (by rfl) ⟨223677, by rfl⟩ : syracuseStep 596473 = 447355) B447355
theorem B989779 : Blo 389765 989779 := bstep (se 1 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 989779 = 1484669) B1484669
theorem B1317545 : Blo 389765 1317545 := bstep (se 2 (by rfl) ⟨494079, by rfl⟩ : syracuseStep 1317545 = 988159) B988159
theorem B5712383 : Blo 389765 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B2502049 : Blo 389765 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B10269683 : Blo 389765 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B6501815 : Blo 389765 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B41367743 : Blo 389765 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B883013825 : Blo 389765 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B1982555 : Blo 389765 1982555 := bstep (se 1 (by rfl) ⟨1486916, by rfl⟩ : syracuseStep 1982555 = 2973833) B2973833
theorem B1982879 : Blo 389765 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B1360895 : Blo 389765 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B3753611 : Blo 389765 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B1984499 : Blo 389765 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B25386695 : Blo 389765 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B877103 : Blo 389765 877103 := bstep (se 1 (by rfl) ⟨657827, by rfl⟩ : syracuseStep 877103 = 1315655) B1315655
theorem B877193 : Blo 389765 877193 := bstep (se 2 (by rfl) ⟨328947, by rfl⟩ : syracuseStep 877193 = 657895) B657895
theorem B746815 : Blo 389765 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B3336815 : Blo 389765 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B585371 : Blo 389765 585371 := bstep (se 1 (by rfl) ⟨439028, by rfl⟩ : syracuseStep 585371 = 878057) B878057
theorem B586409 : Blo 389765 586409 := bstep (se 2 (by rfl) ⟨219903, by rfl⟩ : syracuseStep 586409 = 439807) B439807
theorem B587495 : Blo 389765 587495 := bstep (se 1 (by rfl) ⟨440621, by rfl⟩ : syracuseStep 587495 = 881243) B881243
theorem B2521043 : Blo 389765 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B392751 : Blo 389765 392751 := bstep (se 1 (by rfl) ⟨294563, by rfl⟩ : syracuseStep 392751 = 589127) B589127
theorem B5177279 : Blo 389765 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B393243 : Blo 389765 393243 := bstep (se 1 (by rfl) ⟨294932, by rfl⟩ : syracuseStep 393243 = 589865) B589865
theorem B3181189 : Blo 389765 3181189 := bstep (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) B596473
theorem B3808255 : Blo 389765 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B1319705 : Blo 389765 1319705 := bstep (se 2 (by rfl) ⟨494889, by rfl⟩ : syracuseStep 1319705 = 989779) B989779
theorem B4334543 : Blo 389765 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B1680695 : Blo 389765 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B13806077 : Blo 389765 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B1321703 : Blo 389765 1321703 := bstep (se 1 (by rfl) ⟨991277, by rfl⟩ : syracuseStep 1321703 = 1982555) B1982555
theorem B1321919 : Blo 389765 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B8498135 : Blo 389765 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B2502407 : Blo 389765 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B1322999 : Blo 389765 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B995753 : Blo 389765 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B8499775 : Blo 389765 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B6338371 : Blo 389765 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B4243225 : Blo 389765 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B16924463 : Blo 389765 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B27578495 : Blo 389765 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B3629053 : Blo 389765 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B878363 : Blo 389765 878363 := bstep (se 1 (by rfl) ⟨658772, by rfl⟩ : syracuseStep 878363 = 1317545) B1317545
theorem B3336065 : Blo 389765 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B584735 : Blo 389765 584735 := bstep (se 1 (by rfl) ⟨438551, by rfl⟩ : syracuseStep 584735 = 877103) B877103
theorem B584795 : Blo 389765 584795 := bstep (se 1 (by rfl) ⟨438596, by rfl⟩ : syracuseStep 584795 = 877193) B877193
theorem B2224543 : Blo 389765 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B390247 : Blo 389765 390247 := bstep (se 1 (by rfl) ⟨292685, by rfl⟩ : syracuseStep 390247 = 585371) B585371
theorem B390939 : Blo 389765 390939 := bstep (se 1 (by rfl) ⟨293204, by rfl⟩ : syracuseStep 390939 = 586409) B586409
theorem B6846455 : Blo 389765 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B391663 : Blo 389765 391663 := bstep (se 1 (by rfl) ⟨293747, by rfl⟩ : syracuseStep 391663 = 587495) B587495
theorem B588675883 : Blo 389765 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B18385663 : Blo 389765 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B18257213 : Blo 389765 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B2889695 : Blo 389765 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B1120463 : Blo 389765 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B663835 : Blo 389765 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B784901177 : Blo 389765 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B11282975 : Blo 389765 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B4241585 : Blo 389765 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B2966057 : Blo 389765 2966057 := bstep (se 2 (by rfl) ⟨1112271, by rfl⟩ : syracuseStep 2966057 = 2224543) B2224543
theorem B36816205 : Blo 389765 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B5657633 : Blo 389765 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B4838737 : Blo 389765 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B879803 : Blo 389765 879803 := bstep (se 1 (by rfl) ⟨659852, by rfl⟩ : syracuseStep 879803 = 1319705) B1319705
theorem B11333033 : Blo 389765 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B585575 : Blo 389765 585575 := bstep (se 1 (by rfl) ⟨439181, by rfl⟩ : syracuseStep 585575 = 878363) B878363
theorem B2224043 : Blo 389765 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B881135 : Blo 389765 881135 := bstep (se 1 (by rfl) ⟨660851, by rfl⟩ : syracuseStep 881135 = 1321703) B1321703
theorem B881279 : Blo 389765 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B5665423 : Blo 389765 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B389823 : Blo 389765 389823 := bstep (se 1 (by rfl) ⟨292367, by rfl⟩ : syracuseStep 389823 = 584735) B584735
theorem B389863 : Blo 389765 389863 := bstep (se 1 (by rfl) ⟨292397, by rfl⟩ : syracuseStep 389863 = 584795) B584795
theorem B8451161 : Blo 389765 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B1668271 : Blo 389765 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B881999 : Blo 389765 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B5077673 : Blo 389765 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B885113 : Blo 389765 885113 := bstep (se 2 (by rfl) ⟨331917, by rfl⟩ : syracuseStep 885113 = 663835) B663835
theorem B49088273 : Blo 389765 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B3771755 : Blo 389765 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B24514217 : Blo 389765 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B1482695 : Blo 389765 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B2827723 : Blo 389765 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B3385115 : Blo 389765 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B1977371 : Blo 389765 1977371 := bstep (se 1 (by rfl) ⟨1483028, by rfl⟩ : syracuseStep 1977371 = 2966057) B2966057
theorem B12171475 : Blo 389765 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B7553897 : Blo 389765 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B7521983 : Blo 389765 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B7555355 : Blo 389765 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B1926463 : Blo 389765 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B746975 : Blo 389765 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B523267451 : Blo 389765 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B2224361 : Blo 389765 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B6451649 : Blo 389765 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B586535 : Blo 389765 586535 := bstep (se 1 (by rfl) ⟨439901, by rfl⟩ : syracuseStep 586535 = 879803) B879803
theorem B390383 : Blo 389765 390383 := bstep (se 1 (by rfl) ⟨292787, by rfl⟩ : syracuseStep 390383 = 585575) B585575
theorem B587423 : Blo 389765 587423 := bstep (se 1 (by rfl) ⟨440567, by rfl⟩ : syracuseStep 587423 = 881135) B881135
theorem B587519 : Blo 389765 587519 := bstep (se 1 (by rfl) ⟨440639, by rfl⟩ : syracuseStep 587519 = 881279) B881279
theorem B5634107 : Blo 389765 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B587999 : Blo 389765 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B590075 : Blo 389765 590075 := bstep (se 1 (by rfl) ⟨442556, by rfl⟩ : syracuseStep 590075 = 885113) B885113
theorem B64914533 : Blo 389765 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B5014655 : Blo 389765 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B3770297 : Blo 389765 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B988463 : Blo 389765 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B497983 : Blo 389765 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B1318247 : Blo 389765 1318247 := bstep (se 1 (by rfl) ⟨988685, by rfl⟩ : syracuseStep 1318247 = 1977371) B1977371
theorem B1482907 : Blo 389765 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B523608245 : Blo 389765 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B4301099 : Blo 389765 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B2568617 : Blo 389765 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B3756071 : Blo 389765 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B5035931 : Blo 389765 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B5036903 : Blo 389765 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B2514503 : Blo 389765 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B16342811 : Blo 389765 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B2256743 : Blo 389765 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B348844967 : Blo 389765 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B391023 : Blo 389765 391023 := bstep (se 1 (by rfl) ⟨293267, by rfl⟩ : syracuseStep 391023 = 586535) B586535
theorem B391615 : Blo 389765 391615 := bstep (se 1 (by rfl) ⟨293711, by rfl⟩ : syracuseStep 391615 = 587423) B587423
theorem B391679 : Blo 389765 391679 := bstep (se 1 (by rfl) ⟨293759, by rfl⟩ : syracuseStep 391679 = 587519) B587519
theorem B391999 : Blo 389765 391999 := bstep (se 1 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 391999 = 587999) B587999
theorem B393383 : Blo 389765 393383 := bstep (se 1 (by rfl) ⟨295037, by rfl⟩ : syracuseStep 393383 = 590075) B590075
theorem B3343103 : Blo 389765 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B658975 : Blo 389765 658975 := bstep (se 1 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 658975 = 988463) B988463
theorem B1712411 : Blo 389765 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B663977 : Blo 389765 663977 := bstep (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) B497983
theorem B232563311 : Blo 389765 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B1977209 : Blo 389765 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B2504047 : Blo 389765 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B3357287 : Blo 389765 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B3357935 : Blo 389765 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B10895207 : Blo 389765 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B2867399 : Blo 389765 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B6705341 : Blo 389765 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B43276355 : Blo 389765 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B2513531 : Blo 389765 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B878831 : Blo 389765 878831 := bstep (se 1 (by rfl) ⟨659123, by rfl⟩ : syracuseStep 878831 = 1318247) B1318247
theorem B349072163 : Blo 389765 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B1504495 : Blo 389765 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B2228735 : Blo 389765 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B1675687 : Blo 389765 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B2005993 : Blo 389765 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B1318139 : Blo 389765 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B2238191 : Blo 389765 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B2238623 : Blo 389765 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B1911599 : Blo 389765 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B4470227 : Blo 389765 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B28850903 : Blo 389765 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B442651 : Blo 389765 442651 := bstep (se 1 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 442651 = 663977) B663977
theorem B155042207 : Blo 389765 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B29053885 : Blo 389765 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B878633 : Blo 389765 878633 := bstep (se 2 (by rfl) ⟨329487, by rfl⟩ : syracuseStep 878633 = 658975) B658975
theorem B1141607 : Blo 389765 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B585887 : Blo 389765 585887 := bstep (se 1 (by rfl) ⟨439415, by rfl⟩ : syracuseStep 585887 = 878831) B878831
theorem B3338729 : Blo 389765 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B232714775 : Blo 389765 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B590201 : Blo 389765 590201 := bstep (se 2 (by rfl) ⟨221325, by rfl⟩ : syracuseStep 590201 = 442651) B442651
theorem B2234249 : Blo 389765 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B38738513 : Blo 389765 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B761071 : Blo 389765 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B103361471 : Blo 389765 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B1485823 : Blo 389765 1485823 := bstep (se 1 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 1485823 = 2228735) B2228735
theorem B1492127 : Blo 389765 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B1492415 : Blo 389765 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B155143183 : Blo 389765 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B2674657 : Blo 389765 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B878759 : Blo 389765 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B585755 : Blo 389765 585755 := bstep (se 1 (by rfl) ⟨439316, by rfl⟩ : syracuseStep 585755 = 878633) B878633
theorem B1274399 : Blo 389765 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B390591 : Blo 389765 390591 := bstep (se 1 (by rfl) ⟨292943, by rfl⟩ : syracuseStep 390591 = 585887) B585887
theorem B2225819 : Blo 389765 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B2980151 : Blo 389765 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B19233935 : Blo 389765 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B393467 : Blo 389765 393467 := bstep (se 1 (by rfl) ⟨295100, by rfl⟩ : syracuseStep 393467 = 590201) B590201
theorem B25825675 : Blo 389765 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B1483879 : Blo 389765 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B12822623 : Blo 389765 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B994751 : Blo 389765 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B994943 : Blo 389765 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B1489499 : Blo 389765 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B1981097 : Blo 389765 1981097 := bstep (se 2 (by rfl) ⟨742911, by rfl⟩ : syracuseStep 1981097 = 1485823) B1485823
theorem B1986767 : Blo 389765 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B206857577 : Blo 389765 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B3566209 : Blo 389765 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B585839 : Blo 389765 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B68907647 : Blo 389765 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B390503 : Blo 389765 390503 := bstep (se 1 (by rfl) ⟨292877, by rfl⟩ : syracuseStep 390503 = 585755) B585755
theorem B849599 : Blo 389765 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B1014761 : Blo 389765 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B4754945 : Blo 389765 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B663167 : Blo 389765 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B663295 : Blo 389765 663295 := bstep (se 1 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 663295 = 994943) B994943
theorem B566399 : Blo 389765 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B992999 : Blo 389765 992999 := bstep (se 1 (by rfl) ⟨744749, by rfl⟩ : syracuseStep 992999 = 1489499) B1489499
theorem B1320731 : Blo 389765 1320731 := bstep (se 1 (by rfl) ⟨990548, by rfl⟩ : syracuseStep 1320731 = 1981097) B1981097
theorem B1978505 : Blo 389765 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B1324511 : Blo 389765 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B137905051 : Blo 389765 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B676507 : Blo 389765 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B34434233 : Blo 389765 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B8548415 : Blo 389765 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B390559 : Blo 389765 390559 := bstep (se 1 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 390559 = 585839) B585839
theorem B45938431 : Blo 389765 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B1510397 : Blo 389765 1510397 := bstep (se 3 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 1510397 = 566399) B566399
theorem B661999 : Blo 389765 661999 := bstep (se 1 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 661999 = 992999) B992999
theorem B61251241 : Blo 389765 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B1319003 : Blo 389765 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B183873401 : Blo 389765 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B442111 : Blo 389765 442111 := bstep (se 1 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 442111 = 663167) B663167
theorem B902009 : Blo 389765 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B22956155 : Blo 389765 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B3169963 : Blo 389765 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B880487 : Blo 389765 880487 := bstep (se 1 (by rfl) ⟨660365, by rfl⟩ : syracuseStep 880487 = 1320731) B1320731
theorem B5698943 : Blo 389765 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B883007 : Blo 389765 883007 := bstep (se 1 (by rfl) ⟨662255, by rfl⟩ : syracuseStep 883007 = 1324511) B1324511
theorem B884393 : Blo 389765 884393 := bstep (se 2 (by rfl) ⟨331647, by rfl⟩ : syracuseStep 884393 = 663295) B663295
theorem B15304103 : Blo 389765 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B81668321 : Blo 389765 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B601339 : Blo 389765 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B1006931 : Blo 389765 1006931 := bstep (se 1 (by rfl) ⟨755198, by rfl⟩ : syracuseStep 1006931 = 1510397) B1510397
theorem B879335 : Blo 389765 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B586991 : Blo 389765 586991 := bstep (se 1 (by rfl) ⟨440243, by rfl⟩ : syracuseStep 586991 = 880487) B880487
theorem B122582267 : Blo 389765 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B882665 : Blo 389765 882665 := bstep (se 2 (by rfl) ⟨330999, by rfl⟩ : syracuseStep 882665 = 661999) B661999
theorem B3799295 : Blo 389765 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B588671 : Blo 389765 588671 := bstep (se 1 (by rfl) ⟨441503, by rfl⟩ : syracuseStep 588671 = 883007) B883007
theorem B4226617 : Blo 389765 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B589481 : Blo 389765 589481 := bstep (se 2 (by rfl) ⟨221055, by rfl⟩ : syracuseStep 589481 = 442111) B442111
theorem B589595 : Blo 389765 589595 := bstep (se 1 (by rfl) ⟨442196, by rfl⟩ : syracuseStep 589595 = 884393) B884393
theorem B2532863 : Blo 389765 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B10202735 : Blo 389765 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B801785 : Blo 389765 801785 := bstep (se 2 (by rfl) ⟨300669, by rfl⟩ : syracuseStep 801785 = 601339) B601339
theorem B54445547 : Blo 389765 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B586223 : Blo 389765 586223 := bstep (se 1 (by rfl) ⟨439667, by rfl⟩ : syracuseStep 586223 = 879335) B879335
theorem B391327 : Blo 389765 391327 := bstep (se 1 (by rfl) ⟨293495, by rfl⟩ : syracuseStep 391327 = 586991) B586991
theorem B81721511 : Blo 389765 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B2685149 : Blo 389765 2685149 := bstep (se 3 (by rfl) ⟨503465, by rfl⟩ : syracuseStep 2685149 = 1006931) B1006931
theorem B588443 : Blo 389765 588443 := bstep (se 1 (by rfl) ⟨441332, by rfl⟩ : syracuseStep 588443 = 882665) B882665
theorem B392447 : Blo 389765 392447 := bstep (se 1 (by rfl) ⟨294335, by rfl⟩ : syracuseStep 392447 = 588671) B588671
theorem B5635489 : Blo 389765 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B392987 : Blo 389765 392987 := bstep (se 1 (by rfl) ⟨294740, by rfl⟩ : syracuseStep 392987 = 589481) B589481
theorem B393063 : Blo 389765 393063 := bstep (se 1 (by rfl) ⟨294797, by rfl⟩ : syracuseStep 393063 = 589595) B589595
theorem B7513985 : Blo 389765 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B534523 : Blo 389765 534523 := bstep (se 1 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 534523 = 801785) B801785
theorem B1688575 : Blo 389765 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B6801823 : Blo 389765 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B54481007 : Blo 389765 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B1790099 : Blo 389765 1790099 := bstep (se 1 (by rfl) ⟨1342574, by rfl⟩ : syracuseStep 1790099 = 2685149) B2685149
theorem B36297031 : Blo 389765 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B390815 : Blo 389765 390815 := bstep (se 1 (by rfl) ⟨293111, by rfl⟩ : syracuseStep 390815 = 586223) B586223
theorem B392295 : Blo 389765 392295 := bstep (se 1 (by rfl) ⟨294221, by rfl⟩ : syracuseStep 392295 = 588443) B588443
theorem B36320671 : Blo 389765 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B1193399 : Blo 389765 1193399 := bstep (se 1 (by rfl) ⟨895049, by rfl⟩ : syracuseStep 1193399 = 1790099) B1790099
theorem B2251433 : Blo 389765 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B712697 : Blo 389765 712697 := bstep (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) B534523
theorem B9069097 : Blo 389765 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B5009323 : Blo 389765 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B48396041 : Blo 389765 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B12092129 : Blo 389765 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B6003821 : Blo 389765 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B795599 : Blo 389765 795599 := bstep (se 1 (by rfl) ⟨596699, by rfl⟩ : syracuseStep 795599 = 1193399) B1193399
theorem B32264027 : Blo 389765 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B6679097 : Blo 389765 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B48427561 : Blo 389765 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B1900525 : Blo 389765 1900525 := bstep (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) B712697
theorem B8061419 : Blo 389765 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B258280325 : Blo 389765 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B4002547 : Blo 389765 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B530399 : Blo 389765 530399 := bstep (se 1 (by rfl) ⟨397799, by rfl⟩ : syracuseStep 530399 = 795599) B795599
theorem B2534033 : Blo 389765 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B21509351 : Blo 389765 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B4452731 : Blo 389765 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B5374279 : Blo 389765 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B1414397 : Blo 389765 1414397 := bstep (se 3 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 1414397 = 530399) B530399
theorem B1689355 : Blo 389765 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B2968487 : Blo 389765 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B14339567 : Blo 389765 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B172186883 : Blo 389765 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B5336729 : Blo 389765 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B114791255 : Blo 389765 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B1978991 : Blo 389765 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B3557819 : Blo 389765 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B7165705 : Blo 389765 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B9559711 : Blo 389765 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B942931 : Blo 389765 942931 := bstep (se 1 (by rfl) ⟨707198, by rfl⟩ : syracuseStep 942931 = 1414397) B1414397
theorem B9009893 : Blo 389765 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B24026381 : Blo 389765 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B1319327 : Blo 389765 1319327 := bstep (se 1 (by rfl) ⟨989495, by rfl⟩ : syracuseStep 1319327 = 1978991) B1978991
theorem B1257241 : Blo 389765 1257241 := bstep (se 2 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 1257241 = 942931) B942931
theorem B2371879 : Blo 389765 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B76527503 : Blo 389765 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B9554273 : Blo 389765 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B12746281 : Blo 389765 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B1676321 : Blo 389765 1676321 := bstep (se 2 (by rfl) ⟨628620, by rfl⟩ : syracuseStep 1676321 = 1257241) B1257241
theorem B6369515 : Blo 389765 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B3162505 : Blo 389765 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B16995041 : Blo 389765 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B16017587 : Blo 389765 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B879551 : Blo 389765 879551 := bstep (se 1 (by rfl) ⟨659663, by rfl⟩ : syracuseStep 879551 = 1319327) B1319327
theorem B51018335 : Blo 389765 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B1117547 : Blo 389765 1117547 := bstep (se 1 (by rfl) ⟨838160, by rfl⟩ : syracuseStep 1117547 = 1676321) B1676321
theorem B4246343 : Blo 389765 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B4216673 : Blo 389765 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B11330027 : Blo 389765 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B10678391 : Blo 389765 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B586367 : Blo 389765 586367 := bstep (se 1 (by rfl) ⟨439775, by rfl⟩ : syracuseStep 586367 = 879551) B879551
theorem B34012223 : Blo 389765 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B7118927 : Blo 389765 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B2830895 : Blo 389765 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B7553351 : Blo 389765 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B745031 : Blo 389765 745031 := bstep (se 1 (by rfl) ⟨558773, by rfl⟩ : syracuseStep 745031 = 1117547) B1117547
theorem B2811115 : Blo 389765 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B390911 : Blo 389765 390911 := bstep (se 1 (by rfl) ⟨293183, by rfl⟩ : syracuseStep 390911 = 586367) B586367
theorem B22674815 : Blo 389765 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B496687 : Blo 389765 496687 := bstep (se 1 (by rfl) ⟨372515, by rfl⟩ : syracuseStep 496687 = 745031) B745031
theorem B15116543 : Blo 389765 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B3748153 : Blo 389765 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B1887263 : Blo 389765 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B5035567 : Blo 389765 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B4745951 : Blo 389765 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B662249 : Blo 389765 662249 := bstep (se 2 (by rfl) ⟨248343, by rfl⟩ : syracuseStep 662249 = 496687) B496687
theorem B1258175 : Blo 389765 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B4997537 : Blo 389765 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B10077695 : Blo 389765 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B3163967 : Blo 389765 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B6714089 : Blo 389765 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B6718463 : Blo 389765 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B2109311 : Blo 389765 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B441499 : Blo 389765 441499 := bstep (se 1 (by rfl) ⟨331124, by rfl⟩ : syracuseStep 441499 = 662249) B662249
theorem B838783 : Blo 389765 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B4476059 : Blo 389765 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B3331691 : Blo 389765 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B2984039 : Blo 389765 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B1118377 : Blo 389765 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B4478975 : Blo 389765 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B2221127 : Blo 389765 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B1406207 : Blo 389765 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B588665 : Blo 389765 588665 := bstep (se 2 (by rfl) ⟨220749, by rfl⟩ : syracuseStep 588665 = 441499) B441499
theorem B2985983 : Blo 389765 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B1480751 : Blo 389765 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B3749885 : Blo 389765 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B1491169 : Blo 389765 1491169 := bstep (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) B1118377
theorem B1989359 : Blo 389765 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B392443 : Blo 389765 392443 := bstep (se 1 (by rfl) ⟨294332, by rfl⟩ : syracuseStep 392443 = 588665) B588665
theorem B987167 : Blo 389765 987167 := bstep (se 1 (by rfl) ⟨740375, by rfl⟩ : syracuseStep 987167 = 1480751) B1480751
theorem B2499923 : Blo 389765 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B1326239 : Blo 389765 1326239 := bstep (se 1 (by rfl) ⟨994679, by rfl⟩ : syracuseStep 1326239 = 1989359) B1989359
theorem B1988225 : Blo 389765 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B1990655 : Blo 389765 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B658111 : Blo 389765 658111 := bstep (se 1 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 658111 = 987167) B987167
theorem B1325483 : Blo 389765 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B1327103 : Blo 389765 1327103 := bstep (se 1 (by rfl) ⟨995327, by rfl⟩ : syracuseStep 1327103 = 1990655) B1990655
theorem B1666615 : Blo 389765 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B884159 : Blo 389765 884159 := bstep (se 1 (by rfl) ⟨663119, by rfl⟩ : syracuseStep 884159 = 1326239) B1326239
theorem B877481 : Blo 389765 877481 := bstep (se 2 (by rfl) ⟨329055, by rfl⟩ : syracuseStep 877481 = 658111) B658111
theorem B2222153 : Blo 389765 2222153 := bstep (se 2 (by rfl) ⟨833307, by rfl⟩ : syracuseStep 2222153 = 1666615) B1666615
theorem B884735 : Blo 389765 884735 := bstep (se 1 (by rfl) ⟨663551, by rfl⟩ : syracuseStep 884735 = 1327103) B1327103
theorem B883655 : Blo 389765 883655 := bstep (se 1 (by rfl) ⟨662741, by rfl⟩ : syracuseStep 883655 = 1325483) B1325483
theorem B589439 : Blo 389765 589439 := bstep (se 1 (by rfl) ⟨442079, by rfl⟩ : syracuseStep 589439 = 884159) B884159
theorem B1481435 : Blo 389765 1481435 := bstep (se 1 (by rfl) ⟨1111076, by rfl⟩ : syracuseStep 1481435 = 2222153) B2222153
theorem B589823 : Blo 389765 589823 := bstep (se 1 (by rfl) ⟨442367, by rfl⟩ : syracuseStep 589823 = 884735) B884735
theorem B584987 : Blo 389765 584987 := bstep (se 1 (by rfl) ⟨438740, by rfl⟩ : syracuseStep 584987 = 877481) B877481
theorem B589103 : Blo 389765 589103 := bstep (se 1 (by rfl) ⟨441827, by rfl⟩ : syracuseStep 589103 = 883655) B883655
theorem B392959 : Blo 389765 392959 := bstep (se 1 (by rfl) ⟨294719, by rfl⟩ : syracuseStep 392959 = 589439) B589439
theorem B987623 : Blo 389765 987623 := bstep (se 1 (by rfl) ⟨740717, by rfl⟩ : syracuseStep 987623 = 1481435) B1481435
theorem B389991 : Blo 389765 389991 := bstep (se 1 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 389991 = 584987) B584987
theorem B392735 : Blo 389765 392735 := bstep (se 1 (by rfl) ⟨294551, by rfl⟩ : syracuseStep 392735 = 589103) B589103
theorem B393215 : Blo 389765 393215 := bstep (se 1 (by rfl) ⟨294911, by rfl⟩ : syracuseStep 393215 = 589823) B589823
theorem B658415 : Blo 389765 658415 := bstep (se 1 (by rfl) ⟨493811, by rfl⟩ : syracuseStep 658415 = 987623) B987623
theorem B438943 : Blo 389765 438943 := bstep (se 1 (by rfl) ⟨329207, by rfl⟩ : syracuseStep 438943 = 658415) B658415
theorem B585257 : Blo 389765 585257 := bstep (se 2 (by rfl) ⟨219471, by rfl⟩ : syracuseStep 585257 = 438943) B438943
theorem B390171 : Blo 389765 390171 := bstep (se 1 (by rfl) ⟨292628, by rfl⟩ : syracuseStep 390171 = 585257) B585257

theorem C0 (j : ℕ) (h1 : 97441 ≤ j) (h2 : j ≤ 98140) : Blo 389765 (4 * j + 3) := by
  interval_cases j
  · exact B389767
  · exact B389771
  · exact B389775
  · exact B389779
  · exact B389783
  · exact B389787
  · exact B389791
  · exact B389795
  · exact B389799
  · exact B389803
  · exact B389807
  · exact B389811
  · exact B389815
  · exact B389819
  · exact B389823
  · exact B389827
  · exact B389831
  · exact B389835
  · exact B389839
  · exact B389843
  · exact B389847
  · exact B389851
  · exact B389855
  · exact B389859
  · exact B389863
  · exact B389867
  · exact B389871
  · exact B389875
  · exact B389879
  · exact B389883
  · exact B389887
  · exact B389891
  · exact B389895
  · exact B389899
  · exact B389903
  · exact B389907
  · exact B389911
  · exact B389915
  · exact B389919
  · exact B389923
  · exact B389927
  · exact B389931
  · exact B389935
  · exact B389939
  · exact B389943
  · exact B389947
  · exact B389951
  · exact B389955
  · exact B389959
  · exact B389963
  · exact B389967
  · exact B389971
  · exact B389975
  · exact B389979
  · exact B389983
  · exact B389987
  · exact B389991
  · exact B389995
  · exact B389999
  · exact B390003
  · exact B390007
  · exact B390011
  · exact B390015
  · exact B390019
  · exact B390023
  · exact B390027
  · exact B390031
  · exact B390035
  · exact B390039
  · exact B390043
  · exact B390047
  · exact B390051
  · exact B390055
  · exact B390059
  · exact B390063
  · exact B390067
  · exact B390071
  · exact B390075
  · exact B390079
  · exact B390083
  · exact B390087
  · exact B390091
  · exact B390095
  · exact B390099
  · exact B390103
  · exact B390107
  · exact B390111
  · exact B390115
  · exact B390119
  · exact B390123
  · exact B390127
  · exact B390131
  · exact B390135
  · exact B390139
  · exact B390143
  · exact B390147
  · exact B390151
  · exact B390155
  · exact B390159
  · exact B390163
  · exact B390167
  · exact B390171
  · exact B390175
  · exact B390179
  · exact B390183
  · exact B390187
  · exact B390191
  · exact B390195
  · exact B390199
  · exact B390203
  · exact B390207
  · exact B390211
  · exact B390215
  · exact B390219
  · exact B390223
  · exact B390227
  · exact B390231
  · exact B390235
  · exact B390239
  · exact B390243
  · exact B390247
  · exact B390251
  · exact B390255
  · exact B390259
  · exact B390263
  · exact B390267
  · exact B390271
  · exact B390275
  · exact B390279
  · exact B390283
  · exact B390287
  · exact B390291
  · exact B390295
  · exact B390299
  · exact B390303
  · exact B390307
  · exact B390311
  · exact B390315
  · exact B390319
  · exact B390323
  · exact B390327
  · exact B390331
  · exact B390335
  · exact B390339
  · exact B390343
  · exact B390347
  · exact B390351
  · exact B390355
  · exact B390359
  · exact B390363
  · exact B390367
  · exact B390371
  · exact B390375
  · exact B390379
  · exact B390383
  · exact B390387
  · exact B390391
  · exact B390395
  · exact B390399
  · exact B390403
  · exact B390407
  · exact B390411
  · exact B390415
  · exact B390419
  · exact B390423
  · exact B390427
  · exact B390431
  · exact B390435
  · exact B390439
  · exact B390443
  · exact B390447
  · exact B390451
  · exact B390455
  · exact B390459
  · exact B390463
  · exact B390467
  · exact B390471
  · exact B390475
  · exact B390479
  · exact B390483
  · exact B390487
  · exact B390491
  · exact B390495
  · exact B390499
  · exact B390503
  · exact B390507
  · exact B390511
  · exact B390515
  · exact B390519
  · exact B390523
  · exact B390527
  · exact B390531
  · exact B390535
  · exact B390539
  · exact B390543
  · exact B390547
  · exact B390551
  · exact B390555
  · exact B390559
  · exact B390563
  · exact B390567
  · exact B390571
  · exact B390575
  · exact B390579
  · exact B390583
  · exact B390587
  · exact B390591
  · exact B390595
  · exact B390599
  · exact B390603
  · exact B390607
  · exact B390611
  · exact B390615
  · exact B390619
  · exact B390623
  · exact B390627
  · exact B390631
  · exact B390635
  · exact B390639
  · exact B390643
  · exact B390647
  · exact B390651
  · exact B390655
  · exact B390659
  · exact B390663
  · exact B390667
  · exact B390671
  · exact B390675
  · exact B390679
  · exact B390683
  · exact B390687
  · exact B390691
  · exact B390695
  · exact B390699
  · exact B390703
  · exact B390707
  · exact B390711
  · exact B390715
  · exact B390719
  · exact B390723
  · exact B390727
  · exact B390731
  · exact B390735
  · exact B390739
  · exact B390743
  · exact B390747
  · exact B390751
  · exact B390755
  · exact B390759
  · exact B390763
  · exact B390767
  · exact B390771
  · exact B390775
  · exact B390779
  · exact B390783
  · exact B390787
  · exact B390791
  · exact B390795
  · exact B390799
  · exact B390803
  · exact B390807
  · exact B390811
  · exact B390815
  · exact B390819
  · exact B390823
  · exact B390827
  · exact B390831
  · exact B390835
  · exact B390839
  · exact B390843
  · exact B390847
  · exact B390851
  · exact B390855
  · exact B390859
  · exact B390863
  · exact B390867
  · exact B390871
  · exact B390875
  · exact B390879
  · exact B390883
  · exact B390887
  · exact B390891
  · exact B390895
  · exact B390899
  · exact B390903
  · exact B390907
  · exact B390911
  · exact B390915
  · exact B390919
  · exact B390923
  · exact B390927
  · exact B390931
  · exact B390935
  · exact B390939
  · exact B390943
  · exact B390947
  · exact B390951
  · exact B390955
  · exact B390959
  · exact B390963
  · exact B390967
  · exact B390971
  · exact B390975
  · exact B390979
  · exact B390983
  · exact B390987
  · exact B390991
  · exact B390995
  · exact B390999
  · exact B391003
  · exact B391007
  · exact B391011
  · exact B391015
  · exact B391019
  · exact B391023
  · exact B391027
  · exact B391031
  · exact B391035
  · exact B391039
  · exact B391043
  · exact B391047
  · exact B391051
  · exact B391055
  · exact B391059
  · exact B391063
  · exact B391067
  · exact B391071
  · exact B391075
  · exact B391079
  · exact B391083
  · exact B391087
  · exact B391091
  · exact B391095
  · exact B391099
  · exact B391103
  · exact B391107
  · exact B391111
  · exact B391115
  · exact B391119
  · exact B391123
  · exact B391127
  · exact B391131
  · exact B391135
  · exact B391139
  · exact B391143
  · exact B391147
  · exact B391151
  · exact B391155
  · exact B391159
  · exact B391163
  · exact B391167
  · exact B391171
  · exact B391175
  · exact B391179
  · exact B391183
  · exact B391187
  · exact B391191
  · exact B391195
  · exact B391199
  · exact B391203
  · exact B391207
  · exact B391211
  · exact B391215
  · exact B391219
  · exact B391223
  · exact B391227
  · exact B391231
  · exact B391235
  · exact B391239
  · exact B391243
  · exact B391247
  · exact B391251
  · exact B391255
  · exact B391259
  · exact B391263
  · exact B391267
  · exact B391271
  · exact B391275
  · exact B391279
  · exact B391283
  · exact B391287
  · exact B391291
  · exact B391295
  · exact B391299
  · exact B391303
  · exact B391307
  · exact B391311
  · exact B391315
  · exact B391319
  · exact B391323
  · exact B391327
  · exact B391331
  · exact B391335
  · exact B391339
  · exact B391343
  · exact B391347
  · exact B391351
  · exact B391355
  · exact B391359
  · exact B391363
  · exact B391367
  · exact B391371
  · exact B391375
  · exact B391379
  · exact B391383
  · exact B391387
  · exact B391391
  · exact B391395
  · exact B391399
  · exact B391403
  · exact B391407
  · exact B391411
  · exact B391415
  · exact B391419
  · exact B391423
  · exact B391427
  · exact B391431
  · exact B391435
  · exact B391439
  · exact B391443
  · exact B391447
  · exact B391451
  · exact B391455
  · exact B391459
  · exact B391463
  · exact B391467
  · exact B391471
  · exact B391475
  · exact B391479
  · exact B391483
  · exact B391487
  · exact B391491
  · exact B391495
  · exact B391499
  · exact B391503
  · exact B391507
  · exact B391511
  · exact B391515
  · exact B391519
  · exact B391523
  · exact B391527
  · exact B391531
  · exact B391535
  · exact B391539
  · exact B391543
  · exact B391547
  · exact B391551
  · exact B391555
  · exact B391559
  · exact B391563
  · exact B391567
  · exact B391571
  · exact B391575
  · exact B391579
  · exact B391583
  · exact B391587
  · exact B391591
  · exact B391595
  · exact B391599
  · exact B391603
  · exact B391607
  · exact B391611
  · exact B391615
  · exact B391619
  · exact B391623
  · exact B391627
  · exact B391631
  · exact B391635
  · exact B391639
  · exact B391643
  · exact B391647
  · exact B391651
  · exact B391655
  · exact B391659
  · exact B391663
  · exact B391667
  · exact B391671
  · exact B391675
  · exact B391679
  · exact B391683
  · exact B391687
  · exact B391691
  · exact B391695
  · exact B391699
  · exact B391703
  · exact B391707
  · exact B391711
  · exact B391715
  · exact B391719
  · exact B391723
  · exact B391727
  · exact B391731
  · exact B391735
  · exact B391739
  · exact B391743
  · exact B391747
  · exact B391751
  · exact B391755
  · exact B391759
  · exact B391763
  · exact B391767
  · exact B391771
  · exact B391775
  · exact B391779
  · exact B391783
  · exact B391787
  · exact B391791
  · exact B391795
  · exact B391799
  · exact B391803
  · exact B391807
  · exact B391811
  · exact B391815
  · exact B391819
  · exact B391823
  · exact B391827
  · exact B391831
  · exact B391835
  · exact B391839
  · exact B391843
  · exact B391847
  · exact B391851
  · exact B391855
  · exact B391859
  · exact B391863
  · exact B391867
  · exact B391871
  · exact B391875
  · exact B391879
  · exact B391883
  · exact B391887
  · exact B391891
  · exact B391895
  · exact B391899
  · exact B391903
  · exact B391907
  · exact B391911
  · exact B391915
  · exact B391919
  · exact B391923
  · exact B391927
  · exact B391931
  · exact B391935
  · exact B391939
  · exact B391943
  · exact B391947
  · exact B391951
  · exact B391955
  · exact B391959
  · exact B391963
  · exact B391967
  · exact B391971
  · exact B391975
  · exact B391979
  · exact B391983
  · exact B391987
  · exact B391991
  · exact B391995
  · exact B391999
  · exact B392003
  · exact B392007
  · exact B392011
  · exact B392015
  · exact B392019
  · exact B392023
  · exact B392027
  · exact B392031
  · exact B392035
  · exact B392039
  · exact B392043
  · exact B392047
  · exact B392051
  · exact B392055
  · exact B392059
  · exact B392063
  · exact B392067
  · exact B392071
  · exact B392075
  · exact B392079
  · exact B392083
  · exact B392087
  · exact B392091
  · exact B392095
  · exact B392099
  · exact B392103
  · exact B392107
  · exact B392111
  · exact B392115
  · exact B392119
  · exact B392123
  · exact B392127
  · exact B392131
  · exact B392135
  · exact B392139
  · exact B392143
  · exact B392147
  · exact B392151
  · exact B392155
  · exact B392159
  · exact B392163
  · exact B392167
  · exact B392171
  · exact B392175
  · exact B392179
  · exact B392183
  · exact B392187
  · exact B392191
  · exact B392195
  · exact B392199
  · exact B392203
  · exact B392207
  · exact B392211
  · exact B392215
  · exact B392219
  · exact B392223
  · exact B392227
  · exact B392231
  · exact B392235
  · exact B392239
  · exact B392243
  · exact B392247
  · exact B392251
  · exact B392255
  · exact B392259
  · exact B392263
  · exact B392267
  · exact B392271
  · exact B392275
  · exact B392279
  · exact B392283
  · exact B392287
  · exact B392291
  · exact B392295
  · exact B392299
  · exact B392303
  · exact B392307
  · exact B392311
  · exact B392315
  · exact B392319
  · exact B392323
  · exact B392327
  · exact B392331
  · exact B392335
  · exact B392339
  · exact B392343
  · exact B392347
  · exact B392351
  · exact B392355
  · exact B392359
  · exact B392363
  · exact B392367
  · exact B392371
  · exact B392375
  · exact B392379
  · exact B392383
  · exact B392387
  · exact B392391
  · exact B392395
  · exact B392399
  · exact B392403
  · exact B392407
  · exact B392411
  · exact B392415
  · exact B392419
  · exact B392423
  · exact B392427
  · exact B392431
  · exact B392435
  · exact B392439
  · exact B392443
  · exact B392447
  · exact B392451
  · exact B392455
  · exact B392459
  · exact B392463
  · exact B392467
  · exact B392471
  · exact B392475
  · exact B392479
  · exact B392483
  · exact B392487
  · exact B392491
  · exact B392495
  · exact B392499
  · exact B392503
  · exact B392507
  · exact B392511
  · exact B392515
  · exact B392519
  · exact B392523
  · exact B392527
  · exact B392531
  · exact B392535
  · exact B392539
  · exact B392543
  · exact B392547
  · exact B392551
  · exact B392555
  · exact B392559
  · exact B392563

theorem C1 (j : ℕ) (h1 : 98141 ≤ j) (h2 : j ≤ 98440) : Blo 389765 (4 * j + 3) := by
  interval_cases j
  · exact B392567
  · exact B392571
  · exact B392575
  · exact B392579
  · exact B392583
  · exact B392587
  · exact B392591
  · exact B392595
  · exact B392599
  · exact B392603
  · exact B392607
  · exact B392611
  · exact B392615
  · exact B392619
  · exact B392623
  · exact B392627
  · exact B392631
  · exact B392635
  · exact B392639
  · exact B392643
  · exact B392647
  · exact B392651
  · exact B392655
  · exact B392659
  · exact B392663
  · exact B392667
  · exact B392671
  · exact B392675
  · exact B392679
  · exact B392683
  · exact B392687
  · exact B392691
  · exact B392695
  · exact B392699
  · exact B392703
  · exact B392707
  · exact B392711
  · exact B392715
  · exact B392719
  · exact B392723
  · exact B392727
  · exact B392731
  · exact B392735
  · exact B392739
  · exact B392743
  · exact B392747
  · exact B392751
  · exact B392755
  · exact B392759
  · exact B392763
  · exact B392767
  · exact B392771
  · exact B392775
  · exact B392779
  · exact B392783
  · exact B392787
  · exact B392791
  · exact B392795
  · exact B392799
  · exact B392803
  · exact B392807
  · exact B392811
  · exact B392815
  · exact B392819
  · exact B392823
  · exact B392827
  · exact B392831
  · exact B392835
  · exact B392839
  · exact B392843
  · exact B392847
  · exact B392851
  · exact B392855
  · exact B392859
  · exact B392863
  · exact B392867
  · exact B392871
  · exact B392875
  · exact B392879
  · exact B392883
  · exact B392887
  · exact B392891
  · exact B392895
  · exact B392899
  · exact B392903
  · exact B392907
  · exact B392911
  · exact B392915
  · exact B392919
  · exact B392923
  · exact B392927
  · exact B392931
  · exact B392935
  · exact B392939
  · exact B392943
  · exact B392947
  · exact B392951
  · exact B392955
  · exact B392959
  · exact B392963
  · exact B392967
  · exact B392971
  · exact B392975
  · exact B392979
  · exact B392983
  · exact B392987
  · exact B392991
  · exact B392995
  · exact B392999
  · exact B393003
  · exact B393007
  · exact B393011
  · exact B393015
  · exact B393019
  · exact B393023
  · exact B393027
  · exact B393031
  · exact B393035
  · exact B393039
  · exact B393043
  · exact B393047
  · exact B393051
  · exact B393055
  · exact B393059
  · exact B393063
  · exact B393067
  · exact B393071
  · exact B393075
  · exact B393079
  · exact B393083
  · exact B393087
  · exact B393091
  · exact B393095
  · exact B393099
  · exact B393103
  · exact B393107
  · exact B393111
  · exact B393115
  · exact B393119
  · exact B393123
  · exact B393127
  · exact B393131
  · exact B393135
  · exact B393139
  · exact B393143
  · exact B393147
  · exact B393151
  · exact B393155
  · exact B393159
  · exact B393163
  · exact B393167
  · exact B393171
  · exact B393175
  · exact B393179
  · exact B393183
  · exact B393187
  · exact B393191
  · exact B393195
  · exact B393199
  · exact B393203
  · exact B393207
  · exact B393211
  · exact B393215
  · exact B393219
  · exact B393223
  · exact B393227
  · exact B393231
  · exact B393235
  · exact B393239
  · exact B393243
  · exact B393247
  · exact B393251
  · exact B393255
  · exact B393259
  · exact B393263
  · exact B393267
  · exact B393271
  · exact B393275
  · exact B393279
  · exact B393283
  · exact B393287
  · exact B393291
  · exact B393295
  · exact B393299
  · exact B393303
  · exact B393307
  · exact B393311
  · exact B393315
  · exact B393319
  · exact B393323
  · exact B393327
  · exact B393331
  · exact B393335
  · exact B393339
  · exact B393343
  · exact B393347
  · exact B393351
  · exact B393355
  · exact B393359
  · exact B393363
  · exact B393367
  · exact B393371
  · exact B393375
  · exact B393379
  · exact B393383
  · exact B393387
  · exact B393391
  · exact B393395
  · exact B393399
  · exact B393403
  · exact B393407
  · exact B393411
  · exact B393415
  · exact B393419
  · exact B393423
  · exact B393427
  · exact B393431
  · exact B393435
  · exact B393439
  · exact B393443
  · exact B393447
  · exact B393451
  · exact B393455
  · exact B393459
  · exact B393463
  · exact B393467
  · exact B393471
  · exact B393475
  · exact B393479
  · exact B393483
  · exact B393487
  · exact B393491
  · exact B393495
  · exact B393499
  · exact B393503
  · exact B393507
  · exact B393511
  · exact B393515
  · exact B393519
  · exact B393523
  · exact B393527
  · exact B393531
  · exact B393535
  · exact B393539
  · exact B393543
  · exact B393547
  · exact B393551
  · exact B393555
  · exact B393559
  · exact B393563
  · exact B393567
  · exact B393571
  · exact B393575
  · exact B393579
  · exact B393583
  · exact B393587
  · exact B393591
  · exact B393595
  · exact B393599
  · exact B393603
  · exact B393607
  · exact B393611
  · exact B393615
  · exact B393619
  · exact B393623
  · exact B393627
  · exact B393631
  · exact B393635
  · exact B393639
  · exact B393643
  · exact B393647
  · exact B393651
  · exact B393655
  · exact B393659
  · exact B393663
  · exact B393667
  · exact B393671
  · exact B393675
  · exact B393679
  · exact B393683
  · exact B393687
  · exact B393691
  · exact B393695
  · exact B393699
  · exact B393703
  · exact B393707
  · exact B393711
  · exact B393715
  · exact B393719
  · exact B393723
  · exact B393727
  · exact B393731
  · exact B393735
  · exact B393739
  · exact B393743
  · exact B393747
  · exact B393751
  · exact B393755
  · exact B393759
  · exact B393763

theorem solution (m : ℕ) (hlo : 389765 ≤ m) (hhi : m ≤ 393765) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 97441 ≤ j := by omega
    have hj2 : j ≤ 98440 := by omega
    have hb : Blo 389765 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 98141 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
