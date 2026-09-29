-- Prove2me | solution 1 for syracuse_descends_range_1721061_1723061
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:29:42.736254+00:00
-- url     : https://prove2.me/submissions/06da38da-8f70-4cba-8c11-e0a25bf8e334

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


theorem B11190325 : Blo 1721061 11190325 := bbase (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) (by norm_num)
theorem B3268669 : Blo 1721061 3268669 := bbase (se 3 (by rfl) ⟨612875, by rfl⟩ : syracuseStep 3268669 = 1225751) (by norm_num)
theorem B3874877 : Blo 1721061 3874877 := bbase (se 3 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 3874877 = 1453079) (by norm_num)
theorem B2179153 : Blo 1721061 2179153 := bbase (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) (by norm_num)
theorem B4358245 : Blo 1721061 4358245 := bbase (se 4 (by rfl) ⟨408585, by rfl⟩ : syracuseStep 4358245 = 817171) (by norm_num)
theorem B3874949 : Blo 1721061 3874949 := bbase (se 4 (by rfl) ⟨363276, by rfl⟩ : syracuseStep 3874949 = 726553) (by norm_num)
theorem B7176325 : Blo 1721061 7176325 := bbase (se 4 (by rfl) ⟨672780, by rfl⟩ : syracuseStep 7176325 = 1345561) (by norm_num)
theorem B1745065 : Blo 1721061 1745065 := bbase (se 2 (by rfl) ⟨654399, by rfl⟩ : syracuseStep 1745065 = 1308799) (by norm_num)
theorem B3875021 : Blo 1721061 3875021 := bbase (se 3 (by rfl) ⟨726566, by rfl⟩ : syracuseStep 3875021 = 1453133) (by norm_num)
theorem B4358357 : Blo 1721061 4358357 := bbase (se 7 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 4358357 = 102149) (by norm_num)
theorem B3268829 : Blo 1721061 3268829 := bbase (se 3 (by rfl) ⟨612905, by rfl⟩ : syracuseStep 3268829 = 1225811) (by norm_num)
theorem B4653301 : Blo 1721061 4653301 := bbase (se 5 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 4653301 = 436247) (by norm_num)
theorem B2179325 : Blo 1721061 2179325 := bbase (se 3 (by rfl) ⟨408623, by rfl⟩ : syracuseStep 2179325 = 817247) (by norm_num)
theorem B3875093 : Blo 1721061 3875093 := bbase (se 6 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 3875093 = 181645) (by norm_num)
theorem B2179381 : Blo 1721061 2179381 := bbase (se 5 (by rfl) ⟨102158, by rfl⟩ : syracuseStep 2179381 = 204317) (by norm_num)
theorem B4538693 : Blo 1721061 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B3875165 : Blo 1721061 3875165 := bbase (se 3 (by rfl) ⟨726593, by rfl⟩ : syracuseStep 3875165 = 1453187) (by norm_num)
theorem B3268973 : Blo 1721061 3268973 := bbase (se 3 (by rfl) ⟨612932, by rfl⟩ : syracuseStep 3268973 = 1225865) (by norm_num)
theorem B4358549 : Blo 1721061 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B2179477 : Blo 1721061 2179477 := bbase (se 6 (by rfl) ⟨51081, by rfl⟩ : syracuseStep 2179477 = 102163) (by norm_num)
theorem B3875237 : Blo 1721061 3875237 := bbase (se 4 (by rfl) ⟨363303, by rfl⟩ : syracuseStep 3875237 = 726607) (by norm_num)
theorem B3678637 : Blo 1721061 3678637 := bbase (se 3 (by rfl) ⟨689744, by rfl⟩ : syracuseStep 3678637 = 1379489) (by norm_num)
theorem B3875309 : Blo 1721061 3875309 := bbase (se 3 (by rfl) ⟨726620, by rfl⟩ : syracuseStep 3875309 = 1453241) (by norm_num)
theorem B3875381 : Blo 1721061 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B2179649 : Blo 1721061 2179649 := bbase (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) (by norm_num)
theorem B5808725 : Blo 1721061 5808725 := bbase (se 8 (by rfl) ⟨34035, by rfl⟩ : syracuseStep 5808725 = 68071) (by norm_num)
theorem B2179705 : Blo 1721061 2179705 := bbase (se 2 (by rfl) ⟨817389, by rfl⟩ : syracuseStep 2179705 = 1634779) (by norm_num)
theorem B3875453 : Blo 1721061 3875453 := bbase (se 3 (by rfl) ⟨726647, by rfl⟩ : syracuseStep 3875453 = 1453295) (by norm_num)
theorem B3269261 : Blo 1721061 3269261 := bbase (se 3 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 3269261 = 1225973) (by norm_num)
theorem B3875525 : Blo 1721061 3875525 := bbase (se 4 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 3875525 = 726661) (by norm_num)
theorem B2179801 : Blo 1721061 2179801 := bbase (se 2 (by rfl) ⟨817425, by rfl⟩ : syracuseStep 2179801 = 1634851) (by norm_num)
theorem B4358893 : Blo 1721061 4358893 := bbase (se 3 (by rfl) ⟨817292, by rfl⟩ : syracuseStep 4358893 = 1634585) (by norm_num)
theorem B14713589 : Blo 1721061 14713589 := bbase (se 5 (by rfl) ⟨689699, by rfl⟩ : syracuseStep 14713589 = 1379399) (by norm_num)
theorem B7357189 : Blo 1721061 7357189 := bbase (se 4 (by rfl) ⟨689736, by rfl⟩ : syracuseStep 7357189 = 1379473) (by norm_num)
theorem B3875597 : Blo 1721061 3875597 := bbase (se 3 (by rfl) ⟨726674, by rfl⟩ : syracuseStep 3875597 = 1453349) (by norm_num)
theorem B7357205 : Blo 1721061 7357205 := bbase (se 6 (by rfl) ⟨172434, by rfl⟩ : syracuseStep 7357205 = 344869) (by norm_num)
theorem B3269413 : Blo 1721061 3269413 := bbase (se 4 (by rfl) ⟨306507, by rfl⟩ : syracuseStep 3269413 = 613015) (by norm_num)
theorem B3679013 : Blo 1721061 3679013 := bbase (se 4 (by rfl) ⟨344907, by rfl⟩ : syracuseStep 3679013 = 689815) (by norm_num)
theorem B1745713 : Blo 1721061 1745713 := bbase (se 2 (by rfl) ⟨654642, by rfl⟩ : syracuseStep 1745713 = 1309285) (by norm_num)
theorem B24814421 : Blo 1721061 24814421 := bbase (se 9 (by rfl) ⟨72698, by rfl⟩ : syracuseStep 24814421 = 145397) (by norm_num)
theorem B3875669 : Blo 1721061 3875669 := bbase (se 9 (by rfl) ⟨11354, by rfl⟩ : syracuseStep 3875669 = 22709) (by norm_num)
theorem B4359005 : Blo 1721061 4359005 := bbase (se 3 (by rfl) ⟨817313, by rfl⟩ : syracuseStep 4359005 = 1634627) (by norm_num)
theorem B2179973 : Blo 1721061 2179973 := bbase (se 4 (by rfl) ⟨204372, by rfl⟩ : syracuseStep 2179973 = 408745) (by norm_num)
theorem B3875741 : Blo 1721061 3875741 := bbase (se 3 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 3875741 = 1453403) (by norm_num)
theorem B2180029 : Blo 1721061 2180029 := bbase (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) (by norm_num)
theorem B13083605 : Blo 1721061 13083605 := bbase (se 7 (by rfl) ⟨153323, by rfl⟩ : syracuseStep 13083605 = 306647) (by norm_num)
theorem B3875813 : Blo 1721061 3875813 := bbase (se 4 (by rfl) ⟨363357, by rfl⟩ : syracuseStep 3875813 = 726715) (by norm_num)
theorem B5809157 : Blo 1721061 5809157 := bbase (se 4 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 5809157 = 1089217) (by norm_num)
theorem B4359197 : Blo 1721061 4359197 := bbase (se 3 (by rfl) ⟨817349, by rfl⟩ : syracuseStep 4359197 = 1634699) (by norm_num)
theorem B2180125 : Blo 1721061 2180125 := bbase (se 3 (by rfl) ⟨408773, by rfl⟩ : syracuseStep 2180125 = 817547) (by norm_num)
theorem B3875885 : Blo 1721061 3875885 := bbase (se 3 (by rfl) ⟨726728, by rfl⟩ : syracuseStep 3875885 = 1453457) (by norm_num)
theorem B8717381 : Blo 1721061 8717381 := bbase (se 4 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 8717381 = 1634509) (by norm_num)
theorem B2327629 : Blo 1721061 2327629 := bbase (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) (by norm_num)
theorem B3269717 : Blo 1721061 3269717 := bbase (se 8 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 3269717 = 38317) (by norm_num)
theorem B2581613 : Blo 1721061 2581613 := bbase (se 3 (by rfl) ⟨484052, by rfl⟩ : syracuseStep 2581613 = 968105) (by norm_num)
theorem B3875957 : Blo 1721061 3875957 := bbase (se 5 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 3875957 = 363371) (by norm_num)
theorem B2581637 : Blo 1721061 2581637 := bbase (se 4 (by rfl) ⟨242028, by rfl⟩ : syracuseStep 2581637 = 484057) (by norm_num)
theorem B2581661 : Blo 1721061 2581661 := bbase (se 3 (by rfl) ⟨484061, by rfl⟩ : syracuseStep 2581661 = 968123) (by norm_num)
theorem B4138141 : Blo 1721061 4138141 := bbase (se 3 (by rfl) ⟨775901, by rfl⟩ : syracuseStep 4138141 = 1551803) (by norm_num)
theorem B2581685 : Blo 1721061 2581685 := bbase (se 5 (by rfl) ⟨121016, by rfl⟩ : syracuseStep 2581685 = 242033) (by norm_num)
theorem B4654261 : Blo 1721061 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B3876029 : Blo 1721061 3876029 := bbase (se 3 (by rfl) ⟨726755, by rfl⟩ : syracuseStep 3876029 = 1453511) (by norm_num)
theorem B2180297 : Blo 1721061 2180297 := bbase (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) (by norm_num)
theorem B2581709 : Blo 1721061 2581709 := bbase (se 3 (by rfl) ⟨484070, by rfl⟩ : syracuseStep 2581709 = 968141) (by norm_num)
theorem B3491021 : Blo 1721061 3491021 := bbase (se 3 (by rfl) ⟨654566, by rfl⟩ : syracuseStep 3491021 = 1309133) (by norm_num)
theorem B2581733 : Blo 1721061 2581733 := bbase (se 4 (by rfl) ⟨242037, by rfl⟩ : syracuseStep 2581733 = 484075) (by norm_num)
theorem B2581757 : Blo 1721061 2581757 := bbase (se 3 (by rfl) ⟨484079, by rfl⟩ : syracuseStep 2581757 = 968159) (by norm_num)
theorem B2180353 : Blo 1721061 2180353 := bbase (se 2 (by rfl) ⟨817632, by rfl⟩ : syracuseStep 2180353 = 1635265) (by norm_num)
theorem B2450693 : Blo 1721061 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B3876101 : Blo 1721061 3876101 := bbase (se 4 (by rfl) ⟨363384, by rfl⟩ : syracuseStep 3876101 = 726769) (by norm_num)
theorem B16540949 : Blo 1721061 16540949 := bbase (se 6 (by rfl) ⟨387678, by rfl⟩ : syracuseStep 16540949 = 775357) (by norm_num)
theorem B2581781 : Blo 1721061 2581781 := bbase (se 6 (by rfl) ⟨60510, by rfl⟩ : syracuseStep 2581781 = 121021) (by norm_num)
theorem B2581805 : Blo 1721061 2581805 := bbase (se 3 (by rfl) ⟨484088, by rfl⟩ : syracuseStep 2581805 = 968177) (by norm_num)
theorem B2581829 : Blo 1721061 2581829 := bbase (se 4 (by rfl) ⟨242046, by rfl⟩ : syracuseStep 2581829 = 484093) (by norm_num)
theorem B3876173 : Blo 1721061 3876173 := bbase (se 3 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 3876173 = 1453565) (by norm_num)
theorem B2450773 : Blo 1721061 2450773 := bbase (se 12 (by rfl) ⟨897, by rfl⟩ : syracuseStep 2450773 = 1795) (by norm_num)
theorem B2581853 : Blo 1721061 2581853 := bbase (se 3 (by rfl) ⟨484097, by rfl⟩ : syracuseStep 2581853 = 968195) (by norm_num)
theorem B2180449 : Blo 1721061 2180449 := bbase (se 2 (by rfl) ⟨817668, by rfl⟩ : syracuseStep 2180449 = 1635337) (by norm_num)
theorem B1746289 : Blo 1721061 1746289 := bbase (se 2 (by rfl) ⟨654858, by rfl⟩ : syracuseStep 1746289 = 1309717) (by norm_num)
theorem B2581877 : Blo 1721061 2581877 := bbase (se 5 (by rfl) ⟨121025, by rfl⟩ : syracuseStep 2581877 = 242051) (by norm_num)
theorem B13075829 : Blo 1721061 13075829 := bbase (se 5 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 13075829 = 1225859) (by norm_num)
theorem B4359541 : Blo 1721061 4359541 := bbase (se 5 (by rfl) ⟨204353, by rfl⟩ : syracuseStep 4359541 = 408707) (by norm_num)
theorem B2581901 : Blo 1721061 2581901 := bbase (se 3 (by rfl) ⟨484106, by rfl⟩ : syracuseStep 2581901 = 968213) (by norm_num)
theorem B7857557 : Blo 1721061 7857557 := bbase (se 6 (by rfl) ⟨184161, by rfl⟩ : syracuseStep 7857557 = 368323) (by norm_num)
theorem B3876245 : Blo 1721061 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B2581925 : Blo 1721061 2581925 := bbase (se 4 (by rfl) ⟨242055, by rfl⟩ : syracuseStep 2581925 = 484111) (by norm_num)
theorem B5809589 : Blo 1721061 5809589 := bbase (se 5 (by rfl) ⟨272324, by rfl⟩ : syracuseStep 5809589 = 544649) (by norm_num)
theorem B2581949 : Blo 1721061 2581949 := bbase (se 3 (by rfl) ⟨484115, by rfl⟩ : syracuseStep 2581949 = 968231) (by norm_num)
theorem B2450893 : Blo 1721061 2450893 := bbase (se 3 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 2450893 = 919085) (by norm_num)
theorem B2581973 : Blo 1721061 2581973 := bbase (se 7 (by rfl) ⟨30257, by rfl⟩ : syracuseStep 2581973 = 60515) (by norm_num)
theorem B3876317 : Blo 1721061 3876317 := bbase (se 3 (by rfl) ⟨726809, by rfl⟩ : syracuseStep 3876317 = 1453619) (by norm_num)
theorem B4359653 : Blo 1721061 4359653 := bbase (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) (by norm_num)
theorem B2581997 : Blo 1721061 2581997 := bbase (se 3 (by rfl) ⟨484124, by rfl⟩ : syracuseStep 2581997 = 968249) (by norm_num)
theorem B2582021 : Blo 1721061 2582021 := bbase (se 4 (by rfl) ⟨242064, by rfl⟩ : syracuseStep 2582021 = 484129) (by norm_num)
theorem B2180621 : Blo 1721061 2180621 := bbase (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) (by norm_num)
theorem B2582045 : Blo 1721061 2582045 := bbase (se 3 (by rfl) ⟨484133, by rfl⟩ : syracuseStep 2582045 = 968267) (by norm_num)
theorem B3876389 : Blo 1721061 3876389 := bbase (se 4 (by rfl) ⟨363411, by rfl⟩ : syracuseStep 3876389 = 726823) (by norm_num)
theorem B2450989 : Blo 1721061 2450989 := bbase (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) (by norm_num)
theorem B2582069 : Blo 1721061 2582069 := bbase (se 5 (by rfl) ⟨121034, by rfl⟩ : syracuseStep 2582069 = 242069) (by norm_num)
theorem B2180677 : Blo 1721061 2180677 := bbase (se 4 (by rfl) ⟨204438, by rfl⟩ : syracuseStep 2180677 = 408877) (by norm_num)
theorem B2582093 : Blo 1721061 2582093 := bbase (se 3 (by rfl) ⟨484142, by rfl⟩ : syracuseStep 2582093 = 968285) (by norm_num)
theorem B2582117 : Blo 1721061 2582117 := bbase (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) (by norm_num)
theorem B3876461 : Blo 1721061 3876461 := bbase (se 3 (by rfl) ⟨726836, by rfl⟩ : syracuseStep 3876461 = 1453673) (by norm_num)
theorem B2582141 : Blo 1721061 2582141 := bbase (se 3 (by rfl) ⟨484151, by rfl⟩ : syracuseStep 2582141 = 968303) (by norm_num)
theorem B2582165 : Blo 1721061 2582165 := bbase (se 6 (by rfl) ⟨60519, by rfl⟩ : syracuseStep 2582165 = 121039) (by norm_num)
theorem B4359845 : Blo 1721061 4359845 := bbase (se 4 (by rfl) ⟨408735, by rfl⟩ : syracuseStep 4359845 = 817471) (by norm_num)
theorem B2582189 : Blo 1721061 2582189 := bbase (se 3 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 2582189 = 968321) (by norm_num)
theorem B3876533 : Blo 1721061 3876533 := bbase (se 5 (by rfl) ⟨181712, by rfl⟩ : syracuseStep 3876533 = 363425) (by norm_num)
theorem B2582213 : Blo 1721061 2582213 := bbase (se 4 (by rfl) ⟨242082, by rfl⟩ : syracuseStep 2582213 = 484165) (by norm_num)
theorem B8840917 : Blo 1721061 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B2582237 : Blo 1721061 2582237 := bbase (se 3 (by rfl) ⟨484169, by rfl⟩ : syracuseStep 2582237 = 968339) (by norm_num)
theorem B2582261 : Blo 1721061 2582261 := bbase (se 5 (by rfl) ⟨121043, by rfl⟩ : syracuseStep 2582261 = 242087) (by norm_num)
theorem B3876605 : Blo 1721061 3876605 := bbase (se 3 (by rfl) ⟨726863, by rfl⟩ : syracuseStep 3876605 = 1453727) (by norm_num)
theorem B2795269 : Blo 1721061 2795269 := bbase (se 4 (by rfl) ⟨262056, by rfl⟩ : syracuseStep 2795269 = 524113) (by norm_num)
theorem B2582285 : Blo 1721061 2582285 := bbase (se 3 (by rfl) ⟨484178, by rfl⟩ : syracuseStep 2582285 = 968357) (by norm_num)
theorem B2582309 : Blo 1721061 2582309 := bbase (se 4 (by rfl) ⟨242091, by rfl⟩ : syracuseStep 2582309 = 484183) (by norm_num)
theorem B2582333 : Blo 1721061 2582333 := bbase (se 3 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 2582333 = 968375) (by norm_num)
theorem B3270469 : Blo 1721061 3270469 := bbase (se 4 (by rfl) ⟨306606, by rfl⟩ : syracuseStep 3270469 = 613213) (by norm_num)
theorem B3876677 : Blo 1721061 3876677 := bbase (se 4 (by rfl) ⟨363438, by rfl⟩ : syracuseStep 3876677 = 726877) (by norm_num)
theorem B2582357 : Blo 1721061 2582357 := bbase (se 9 (by rfl) ⟨7565, by rfl⟩ : syracuseStep 2582357 = 15131) (by norm_num)
theorem B5810021 : Blo 1721061 5810021 := bbase (se 4 (by rfl) ⟨544689, by rfl⟩ : syracuseStep 5810021 = 1089379) (by norm_num)
theorem B2582381 : Blo 1721061 2582381 := bbase (se 3 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 2582381 = 968393) (by norm_num)
theorem B2582405 : Blo 1721061 2582405 := bbase (se 4 (by rfl) ⟨242100, by rfl⟩ : syracuseStep 2582405 = 484201) (by norm_num)
theorem B3876749 : Blo 1721061 3876749 := bbase (se 3 (by rfl) ⟨726890, by rfl⟩ : syracuseStep 3876749 = 1453781) (by norm_num)
theorem B2582429 : Blo 1721061 2582429 := bbase (se 3 (by rfl) ⟨484205, by rfl⟩ : syracuseStep 2582429 = 968411) (by norm_num)
theorem B2582453 : Blo 1721061 2582453 := bbase (se 5 (by rfl) ⟨121052, by rfl⟩ : syracuseStep 2582453 = 242105) (by norm_num)
theorem B2582477 : Blo 1721061 2582477 := bbase (se 3 (by rfl) ⟨484214, by rfl⟩ : syracuseStep 2582477 = 968429) (by norm_num)
theorem B16779221 : Blo 1721061 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B3270613 : Blo 1721061 3270613 := bbase (se 7 (by rfl) ⟨38327, by rfl⟩ : syracuseStep 3270613 = 76655) (by norm_num)
theorem B3876821 : Blo 1721061 3876821 := bbase (se 7 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 3876821 = 90863) (by norm_num)
theorem B2582501 : Blo 1721061 2582501 := bbase (se 4 (by rfl) ⟨242109, by rfl⟩ : syracuseStep 2582501 = 484219) (by norm_num)
theorem B6539237 : Blo 1721061 6539237 := bbase (se 4 (by rfl) ⟨613053, by rfl⟩ : syracuseStep 6539237 = 1226107) (by norm_num)
theorem B2582525 : Blo 1721061 2582525 := bbase (se 3 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 2582525 = 968447) (by norm_num)
theorem B4360189 : Blo 1721061 4360189 := bbase (se 3 (by rfl) ⟨817535, by rfl⟩ : syracuseStep 4360189 = 1635071) (by norm_num)
theorem B2582549 : Blo 1721061 2582549 := bbase (se 6 (by rfl) ⟨60528, by rfl⟩ : syracuseStep 2582549 = 121057) (by norm_num)
theorem B2451485 : Blo 1721061 2451485 := bbase (se 3 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 2451485 = 919307) (by norm_num)
theorem B2582573 : Blo 1721061 2582573 := bbase (se 3 (by rfl) ⟨484232, by rfl⟩ : syracuseStep 2582573 = 968465) (by norm_num)
theorem B2582597 : Blo 1721061 2582597 := bbase (se 4 (by rfl) ⟨242118, by rfl⟩ : syracuseStep 2582597 = 484237) (by norm_num)
theorem B2582621 : Blo 1721061 2582621 := bbase (se 3 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 2582621 = 968483) (by norm_num)
theorem B4360301 : Blo 1721061 4360301 := bbase (se 3 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 4360301 = 1635113) (by norm_num)
theorem B2582645 : Blo 1721061 2582645 := bbase (se 5 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 2582645 = 242123) (by norm_num)
theorem B3270773 : Blo 1721061 3270773 := bbase (se 5 (by rfl) ⟨153317, by rfl⟩ : syracuseStep 3270773 = 306635) (by norm_num)
theorem B2582669 : Blo 1721061 2582669 := bbase (se 3 (by rfl) ⟨484250, by rfl⟩ : syracuseStep 2582669 = 968501) (by norm_num)
theorem B2582693 : Blo 1721061 2582693 := bbase (se 4 (by rfl) ⟨242127, by rfl⟩ : syracuseStep 2582693 = 484255) (by norm_num)
theorem B2582717 : Blo 1721061 2582717 := bbase (se 3 (by rfl) ⟨484259, by rfl⟩ : syracuseStep 2582717 = 968519) (by norm_num)
theorem B2582741 : Blo 1721061 2582741 := bbase (se 7 (by rfl) ⟨30266, by rfl⟩ : syracuseStep 2582741 = 60533) (by norm_num)
theorem B2582765 : Blo 1721061 2582765 := bbase (se 3 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 2582765 = 968537) (by norm_num)
theorem B2582789 : Blo 1721061 2582789 := bbase (se 4 (by rfl) ⟨242136, by rfl⟩ : syracuseStep 2582789 = 484273) (by norm_num)
theorem B6539525 : Blo 1721061 6539525 := bbase (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) (by norm_num)
theorem B3270917 : Blo 1721061 3270917 := bbase (se 4 (by rfl) ⟨306648, by rfl⟩ : syracuseStep 3270917 = 613297) (by norm_num)
theorem B5810453 : Blo 1721061 5810453 := bbase (se 6 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 5810453 = 272365) (by norm_num)
theorem B2582813 : Blo 1721061 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B7080229 : Blo 1721061 7080229 := bbase (se 4 (by rfl) ⟨663771, by rfl⟩ : syracuseStep 7080229 = 1327543) (by norm_num)
theorem B4360493 : Blo 1721061 4360493 := bbase (se 3 (by rfl) ⟨817592, by rfl⟩ : syracuseStep 4360493 = 1635185) (by norm_num)
theorem B5515573 : Blo 1721061 5515573 := bbase (se 5 (by rfl) ⟨258542, by rfl⟩ : syracuseStep 5515573 = 517085) (by norm_num)
theorem B2582837 : Blo 1721061 2582837 := bbase (se 5 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 2582837 = 242141) (by norm_num)
theorem B5237045 : Blo 1721061 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B2582861 : Blo 1721061 2582861 := bbase (se 3 (by rfl) ⟨484286, by rfl⟩ : syracuseStep 2582861 = 968573) (by norm_num)
theorem B8718677 : Blo 1721061 8718677 := bbase (se 10 (by rfl) ⟨12771, by rfl⟩ : syracuseStep 8718677 = 25543) (by norm_num)
theorem B2582885 : Blo 1721061 2582885 := bbase (se 4 (by rfl) ⟨242145, by rfl⟩ : syracuseStep 2582885 = 484291) (by norm_num)
theorem B2582909 : Blo 1721061 2582909 := bbase (se 3 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 2582909 = 968591) (by norm_num)
theorem B2582933 : Blo 1721061 2582933 := bbase (se 6 (by rfl) ⟨60537, by rfl⟩ : syracuseStep 2582933 = 121075) (by norm_num)
theorem B2582957 : Blo 1721061 2582957 := bbase (se 3 (by rfl) ⟨484304, by rfl⟩ : syracuseStep 2582957 = 968609) (by norm_num)
theorem B2582981 : Blo 1721061 2582981 := bbase (se 4 (by rfl) ⟨242154, by rfl⟩ : syracuseStep 2582981 = 484309) (by norm_num)
theorem B2583005 : Blo 1721061 2583005 := bbase (se 3 (by rfl) ⟨484313, by rfl⟩ : syracuseStep 2583005 = 968627) (by norm_num)
theorem B2583029 : Blo 1721061 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B4139525 : Blo 1721061 4139525 := bbase (se 4 (by rfl) ⟨388080, by rfl⟩ : syracuseStep 4139525 = 776161) (by norm_num)
theorem B2583053 : Blo 1721061 2583053 := bbase (se 3 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 2583053 = 968645) (by norm_num)
theorem B2583077 : Blo 1721061 2583077 := bbase (se 4 (by rfl) ⟨242163, by rfl⟩ : syracuseStep 2583077 = 484327) (by norm_num)
theorem B2583101 : Blo 1721061 2583101 := bbase (se 3 (by rfl) ⟨484331, by rfl⟩ : syracuseStep 2583101 = 968663) (by norm_num)
theorem B2452037 : Blo 1721061 2452037 := bbase (se 4 (by rfl) ⟨229878, by rfl⟩ : syracuseStep 2452037 = 459757) (by norm_num)
theorem B2583125 : Blo 1721061 2583125 := bbase (se 8 (by rfl) ⟨15135, by rfl⟩ : syracuseStep 2583125 = 30271) (by norm_num)
theorem B2583149 : Blo 1721061 2583149 := bbase (se 3 (by rfl) ⟨484340, by rfl⟩ : syracuseStep 2583149 = 968681) (by norm_num)
theorem B2583173 : Blo 1721061 2583173 := bbase (se 4 (by rfl) ⟨242172, by rfl⟩ : syracuseStep 2583173 = 484345) (by norm_num)
theorem B4360837 : Blo 1721061 4360837 := bbase (se 4 (by rfl) ⟨408828, by rfl⟩ : syracuseStep 4360837 = 817657) (by norm_num)
theorem B2583197 : Blo 1721061 2583197 := bbase (se 3 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 2583197 = 968699) (by norm_num)
theorem B2583221 : Blo 1721061 2583221 := bbase (se 5 (by rfl) ⟨121088, by rfl⟩ : syracuseStep 2583221 = 242177) (by norm_num)
theorem B5810885 : Blo 1721061 5810885 := bbase (se 4 (by rfl) ⟨544770, by rfl⟩ : syracuseStep 5810885 = 1089541) (by norm_num)
theorem B2583245 : Blo 1721061 2583245 := bbase (se 3 (by rfl) ⟨484358, by rfl⟩ : syracuseStep 2583245 = 968717) (by norm_num)
theorem B2583269 : Blo 1721061 2583269 := bbase (se 4 (by rfl) ⟨242181, by rfl⟩ : syracuseStep 2583269 = 484363) (by norm_num)
theorem B4360949 : Blo 1721061 4360949 := bbase (se 5 (by rfl) ⟨204419, by rfl⟩ : syracuseStep 4360949 = 408839) (by norm_num)
theorem B2583293 : Blo 1721061 2583293 := bbase (se 3 (by rfl) ⟨484367, by rfl⟩ : syracuseStep 2583293 = 968735) (by norm_num)
theorem B2583317 : Blo 1721061 2583317 := bbase (se 6 (by rfl) ⟨60546, by rfl⟩ : syracuseStep 2583317 = 121093) (by norm_num)
theorem B2583341 : Blo 1721061 2583341 := bbase (se 3 (by rfl) ⟨484376, by rfl⟩ : syracuseStep 2583341 = 968753) (by norm_num)
theorem B2583365 : Blo 1721061 2583365 := bbase (se 4 (by rfl) ⟨242190, by rfl⟩ : syracuseStep 2583365 = 484381) (by norm_num)
theorem B1936201 : Blo 1721061 1936201 := bbase (se 2 (by rfl) ⟨726075, by rfl⟩ : syracuseStep 1936201 = 1452151) (by norm_num)
theorem B2583389 : Blo 1721061 2583389 := bbase (se 3 (by rfl) ⟨484385, by rfl⟩ : syracuseStep 2583389 = 968771) (by norm_num)
theorem B1936237 : Blo 1721061 1936237 := bbase (se 3 (by rfl) ⟨363044, by rfl⟩ : syracuseStep 1936237 = 726089) (by norm_num)
theorem B2583413 : Blo 1721061 2583413 := bbase (se 5 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 2583413 = 242195) (by norm_num)
theorem B2583437 : Blo 1721061 2583437 := bbase (se 3 (by rfl) ⟨484394, by rfl⟩ : syracuseStep 2583437 = 968789) (by norm_num)
theorem B1936273 : Blo 1721061 1936273 := bbase (se 2 (by rfl) ⟨726102, by rfl⟩ : syracuseStep 1936273 = 1452205) (by norm_num)
theorem B2583461 : Blo 1721061 2583461 := bbase (se 4 (by rfl) ⟨242199, by rfl⟩ : syracuseStep 2583461 = 484399) (by norm_num)
theorem B1936309 : Blo 1721061 1936309 := bbase (se 5 (by rfl) ⟨90764, by rfl⟩ : syracuseStep 1936309 = 181529) (by norm_num)
theorem B4361141 : Blo 1721061 4361141 := bbase (se 5 (by rfl) ⟨204428, by rfl⟩ : syracuseStep 4361141 = 408857) (by norm_num)
theorem B4139957 : Blo 1721061 4139957 := bbase (se 5 (by rfl) ⟨194060, by rfl⟩ : syracuseStep 4139957 = 388121) (by norm_num)
theorem B2583485 : Blo 1721061 2583485 := bbase (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) (by norm_num)
theorem B3926981 : Blo 1721061 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B2583509 : Blo 1721061 2583509 := bbase (se 7 (by rfl) ⟨30275, by rfl⟩ : syracuseStep 2583509 = 60551) (by norm_num)
theorem B11037653 : Blo 1721061 11037653 := bbase (se 7 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 11037653 = 258695) (by norm_num)
theorem B1936345 : Blo 1721061 1936345 := bbase (se 2 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 1936345 = 1452259) (by norm_num)
theorem B7359461 : Blo 1721061 7359461 := bbase (se 4 (by rfl) ⟨689949, by rfl⟩ : syracuseStep 7359461 = 1379899) (by norm_num)
theorem B2583533 : Blo 1721061 2583533 := bbase (se 3 (by rfl) ⟨484412, by rfl⟩ : syracuseStep 2583533 = 968825) (by norm_num)
theorem B1936381 : Blo 1721061 1936381 := bbase (se 3 (by rfl) ⟨363071, by rfl⟩ : syracuseStep 1936381 = 726143) (by norm_num)
theorem B2583557 : Blo 1721061 2583557 := bbase (se 4 (by rfl) ⟨242208, by rfl⟩ : syracuseStep 2583557 = 484417) (by norm_num)
theorem B2583581 : Blo 1721061 2583581 := bbase (se 3 (by rfl) ⟨484421, by rfl⟩ : syracuseStep 2583581 = 968843) (by norm_num)
theorem B1936417 : Blo 1721061 1936417 := bbase (se 2 (by rfl) ⟨726156, by rfl⟩ : syracuseStep 1936417 = 1452313) (by norm_num)
theorem B5237797 : Blo 1721061 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B2583605 : Blo 1721061 2583605 := bbase (se 5 (by rfl) ⟨121106, by rfl⟩ : syracuseStep 2583605 = 242213) (by norm_num)
theorem B1936453 : Blo 1721061 1936453 := bbase (se 4 (by rfl) ⟨181542, by rfl⟩ : syracuseStep 1936453 = 363085) (by norm_num)
theorem B2583629 : Blo 1721061 2583629 := bbase (se 3 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 2583629 = 968861) (by norm_num)
theorem B2583653 : Blo 1721061 2583653 := bbase (se 4 (by rfl) ⟨242217, by rfl⟩ : syracuseStep 2583653 = 484435) (by norm_num)
theorem B1936489 : Blo 1721061 1936489 := bbase (se 2 (by rfl) ⟨726183, by rfl⟩ : syracuseStep 1936489 = 1452367) (by norm_num)
theorem B5811317 : Blo 1721061 5811317 := bbase (se 5 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 5811317 = 544811) (by norm_num)
theorem B2583677 : Blo 1721061 2583677 := bbase (se 3 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 2583677 = 968879) (by norm_num)
theorem B1936525 : Blo 1721061 1936525 := bbase (se 3 (by rfl) ⟨363098, by rfl⟩ : syracuseStep 1936525 = 726197) (by norm_num)
theorem B1838225 : Blo 1721061 1838225 := bbase (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) (by norm_num)
theorem B2583701 : Blo 1721061 2583701 := bbase (se 6 (by rfl) ⟨60555, by rfl⟩ : syracuseStep 2583701 = 121111) (by norm_num)
theorem B2583725 : Blo 1721061 2583725 := bbase (se 3 (by rfl) ⟨484448, by rfl⟩ : syracuseStep 2583725 = 968897) (by norm_num)
theorem B1936561 : Blo 1721061 1936561 := bbase (se 2 (by rfl) ⟨726210, by rfl⟩ : syracuseStep 1936561 = 1452421) (by norm_num)
theorem B2796725 : Blo 1721061 2796725 := bbase (se 5 (by rfl) ⟨131096, by rfl⟩ : syracuseStep 2796725 = 262193) (by norm_num)
theorem B2583749 : Blo 1721061 2583749 := bbase (se 4 (by rfl) ⟨242226, by rfl⟩ : syracuseStep 2583749 = 484453) (by norm_num)
theorem B1936597 : Blo 1721061 1936597 := bbase (se 7 (by rfl) ⟨22694, by rfl⟩ : syracuseStep 1936597 = 45389) (by norm_num)
theorem B2583773 : Blo 1721061 2583773 := bbase (se 3 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 2583773 = 968915) (by norm_num)
theorem B2583797 : Blo 1721061 2583797 := bbase (se 5 (by rfl) ⟨121115, by rfl⟩ : syracuseStep 2583797 = 242231) (by norm_num)
theorem B1936633 : Blo 1721061 1936633 := bbase (se 2 (by rfl) ⟨726237, by rfl⟩ : syracuseStep 1936633 = 1452475) (by norm_num)
theorem B2067725 : Blo 1721061 2067725 := bbase (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) (by norm_num)
theorem B2583821 : Blo 1721061 2583821 := bbase (se 3 (by rfl) ⟨484466, by rfl⟩ : syracuseStep 2583821 = 968933) (by norm_num)
theorem B4361485 : Blo 1721061 4361485 := bbase (se 3 (by rfl) ⟨817778, by rfl⟩ : syracuseStep 4361485 = 1635557) (by norm_num)
theorem B1936669 : Blo 1721061 1936669 := bbase (se 3 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 1936669 = 726251) (by norm_num)
theorem B6982949 : Blo 1721061 6982949 := bbase (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) (by norm_num)
theorem B2583845 : Blo 1721061 2583845 := bbase (se 4 (by rfl) ⟨242235, by rfl⟩ : syracuseStep 2583845 = 484471) (by norm_num)
theorem B2452789 : Blo 1721061 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B2583869 : Blo 1721061 2583869 := bbase (se 3 (by rfl) ⟨484475, by rfl⟩ : syracuseStep 2583869 = 968951) (by norm_num)
theorem B1936705 : Blo 1721061 1936705 := bbase (se 2 (by rfl) ⟨726264, by rfl⟩ : syracuseStep 1936705 = 1452529) (by norm_num)
theorem B5107013 : Blo 1721061 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B8277317 : Blo 1721061 8277317 := bbase (se 4 (by rfl) ⟨775998, by rfl⟩ : syracuseStep 8277317 = 1551997) (by norm_num)
theorem B1838413 : Blo 1721061 1838413 := bbase (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) (by norm_num)
theorem B2583893 : Blo 1721061 2583893 := bbase (se 11 (by rfl) ⟨1892, by rfl⟩ : syracuseStep 2583893 = 3785) (by norm_num)
theorem B1936741 : Blo 1721061 1936741 := bbase (se 4 (by rfl) ⟨181569, by rfl⟩ : syracuseStep 1936741 = 363139) (by norm_num)
theorem B2583917 : Blo 1721061 2583917 := bbase (se 3 (by rfl) ⟨484484, by rfl⟩ : syracuseStep 2583917 = 968969) (by norm_num)
theorem B2583941 : Blo 1721061 2583941 := bbase (se 4 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 2583941 = 484489) (by norm_num)
theorem B1936777 : Blo 1721061 1936777 := bbase (se 2 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 1936777 = 1452583) (by norm_num)
theorem B4656533 : Blo 1721061 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B2583965 : Blo 1721061 2583965 := bbase (se 3 (by rfl) ⟨484493, by rfl⟩ : syracuseStep 2583965 = 968987) (by norm_num)
theorem B6540709 : Blo 1721061 6540709 := bbase (se 4 (by rfl) ⟨613191, by rfl⟩ : syracuseStep 6540709 = 1226383) (by norm_num)
theorem B1936813 : Blo 1721061 1936813 := bbase (se 3 (by rfl) ⟨363152, by rfl⟩ : syracuseStep 1936813 = 726305) (by norm_num)
theorem B9809333 : Blo 1721061 9809333 := bbase (se 5 (by rfl) ⟨459812, by rfl⟩ : syracuseStep 9809333 = 919625) (by norm_num)
theorem B2583989 : Blo 1721061 2583989 := bbase (se 5 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 2583989 = 242249) (by norm_num)
theorem B8392117 : Blo 1721061 8392117 := bbase (se 5 (by rfl) ⟨393380, by rfl⟩ : syracuseStep 8392117 = 786761) (by norm_num)
theorem B2584013 : Blo 1721061 2584013 := bbase (se 3 (by rfl) ⟨484502, by rfl⟩ : syracuseStep 2584013 = 969005) (by norm_num)
theorem B1936849 : Blo 1721061 1936849 := bbase (se 2 (by rfl) ⟨726318, by rfl⟩ : syracuseStep 1936849 = 1452637) (by norm_num)
theorem B53013973 : Blo 1721061 53013973 := bbase (se 7 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 53013973 = 1242515) (by norm_num)
theorem B3927509 : Blo 1721061 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2584037 : Blo 1721061 2584037 := bbase (se 4 (by rfl) ⟨242253, by rfl⟩ : syracuseStep 2584037 = 484507) (by norm_num)
theorem B4902389 : Blo 1721061 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B1936885 : Blo 1721061 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B2584061 : Blo 1721061 2584061 := bbase (se 3 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 2584061 = 969023) (by norm_num)
theorem B2584085 : Blo 1721061 2584085 := bbase (se 6 (by rfl) ⟨60564, by rfl⟩ : syracuseStep 2584085 = 121129) (by norm_num)
theorem B1936921 : Blo 1721061 1936921 := bbase (se 2 (by rfl) ⟨726345, by rfl⟩ : syracuseStep 1936921 = 1452691) (by norm_num)
theorem B5811749 : Blo 1721061 5811749 := bbase (se 4 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 5811749 = 1089703) (by norm_num)
theorem B2584109 : Blo 1721061 2584109 := bbase (se 3 (by rfl) ⟨484520, by rfl⟩ : syracuseStep 2584109 = 969041) (by norm_num)
theorem B1936957 : Blo 1721061 1936957 := bbase (se 3 (by rfl) ⟨363179, by rfl⟩ : syracuseStep 1936957 = 726359) (by norm_num)
theorem B2068033 : Blo 1721061 2068033 := bbase (se 2 (by rfl) ⟨775512, by rfl⟩ : syracuseStep 2068033 = 1551025) (by norm_num)
theorem B2584133 : Blo 1721061 2584133 := bbase (se 4 (by rfl) ⟨242262, by rfl⟩ : syracuseStep 2584133 = 484525) (by norm_num)
theorem B1863253 : Blo 1721061 1863253 := bbase (se 8 (by rfl) ⟨10917, by rfl⟩ : syracuseStep 1863253 = 21835) (by norm_num)
theorem B2584157 : Blo 1721061 2584157 := bbase (se 3 (by rfl) ⟨484529, by rfl⟩ : syracuseStep 2584157 = 969059) (by norm_num)
theorem B1936993 : Blo 1721061 1936993 := bbase (se 2 (by rfl) ⟨726372, by rfl⟩ : syracuseStep 1936993 = 1452745) (by norm_num)
theorem B8719973 : Blo 1721061 8719973 := bbase (se 4 (by rfl) ⟨817497, by rfl⟩ : syracuseStep 8719973 = 1634995) (by norm_num)
theorem B2584181 : Blo 1721061 2584181 := bbase (se 5 (by rfl) ⟨121133, by rfl⟩ : syracuseStep 2584181 = 242267) (by norm_num)
theorem B1937029 : Blo 1721061 1937029 := bbase (se 4 (by rfl) ⟨181596, by rfl⟩ : syracuseStep 1937029 = 363193) (by norm_num)
theorem B2584205 : Blo 1721061 2584205 := bbase (se 3 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 2584205 = 969077) (by norm_num)
theorem B14716565 : Blo 1721061 14716565 := bbase (se 6 (by rfl) ⟨344919, by rfl⟩ : syracuseStep 14716565 = 689839) (by norm_num)
theorem B2584229 : Blo 1721061 2584229 := bbase (se 4 (by rfl) ⟨242271, by rfl⟩ : syracuseStep 2584229 = 484543) (by norm_num)
theorem B1937065 : Blo 1721061 1937065 := bbase (se 2 (by rfl) ⟨726399, by rfl⟩ : syracuseStep 1937065 = 1452799) (by norm_num)
theorem B2617013 : Blo 1721061 2617013 := bbase (se 5 (by rfl) ⟨122672, by rfl⟩ : syracuseStep 2617013 = 245345) (by norm_num)
theorem B2584253 : Blo 1721061 2584253 := bbase (se 3 (by rfl) ⟨484547, by rfl⟩ : syracuseStep 2584253 = 969095) (by norm_num)
theorem B1937101 : Blo 1721061 1937101 := bbase (se 3 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 1937101 = 726413) (by norm_num)
theorem B6541013 : Blo 1721061 6541013 := bbase (se 7 (by rfl) ⟨76652, by rfl⟩ : syracuseStep 6541013 = 153305) (by norm_num)
theorem B2584277 : Blo 1721061 2584277 := bbase (se 7 (by rfl) ⟨30284, by rfl⟩ : syracuseStep 2584277 = 60569) (by norm_num)
theorem B2584301 : Blo 1721061 2584301 := bbase (se 3 (by rfl) ⟨484556, by rfl⟩ : syracuseStep 2584301 = 969113) (by norm_num)
theorem B1937137 : Blo 1721061 1937137 := bbase (se 2 (by rfl) ⟨726426, by rfl⟩ : syracuseStep 1937137 = 1452853) (by norm_num)
theorem B2584325 : Blo 1721061 2584325 := bbase (se 4 (by rfl) ⟨242280, by rfl⟩ : syracuseStep 2584325 = 484561) (by norm_num)
theorem B1937173 : Blo 1721061 1937173 := bbase (se 6 (by rfl) ⟨45402, by rfl⟩ : syracuseStep 1937173 = 90805) (by norm_num)
theorem B2068249 : Blo 1721061 2068249 := bbase (se 2 (by rfl) ⟨775593, by rfl⟩ : syracuseStep 2068249 = 1551187) (by norm_num)
theorem B2584349 : Blo 1721061 2584349 := bbase (se 3 (by rfl) ⟨484565, by rfl⟩ : syracuseStep 2584349 = 969131) (by norm_num)
theorem B17674037 : Blo 1721061 17674037 := bbase (se 5 (by rfl) ⟨828470, by rfl⟩ : syracuseStep 17674037 = 1656941) (by norm_num)
theorem B2584373 : Blo 1721061 2584373 := bbase (se 5 (by rfl) ⟨121142, by rfl⟩ : syracuseStep 2584373 = 242285) (by norm_num)
theorem B1937209 : Blo 1721061 1937209 := bbase (se 2 (by rfl) ⟨726453, by rfl⟩ : syracuseStep 1937209 = 1452907) (by norm_num)
theorem B2584397 : Blo 1721061 2584397 := bbase (se 3 (by rfl) ⟨484574, by rfl⟩ : syracuseStep 2584397 = 969149) (by norm_num)
theorem B1937245 : Blo 1721061 1937245 := bbase (se 3 (by rfl) ⟨363233, by rfl⟩ : syracuseStep 1937245 = 726467) (by norm_num)
theorem B2584421 : Blo 1721061 2584421 := bbase (se 4 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 2584421 = 484579) (by norm_num)
theorem B2584445 : Blo 1721061 2584445 := bbase (se 3 (by rfl) ⟨484583, by rfl⟩ : syracuseStep 2584445 = 969167) (by norm_num)
theorem B1937281 : Blo 1721061 1937281 := bbase (se 2 (by rfl) ⟨726480, by rfl⟩ : syracuseStep 1937281 = 1452961) (by norm_num)
theorem B2584469 : Blo 1721061 2584469 := bbase (se 6 (by rfl) ⟨60573, by rfl⟩ : syracuseStep 2584469 = 121147) (by norm_num)
theorem B1937317 : Blo 1721061 1937317 := bbase (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) (by norm_num)
theorem B2584493 : Blo 1721061 2584493 := bbase (se 3 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 2584493 = 969185) (by norm_num)
theorem B2584517 : Blo 1721061 2584517 := bbase (se 4 (by rfl) ⟨242298, by rfl⟩ : syracuseStep 2584517 = 484597) (by norm_num)
theorem B1937353 : Blo 1721061 1937353 := bbase (se 2 (by rfl) ⟨726507, by rfl⟩ : syracuseStep 1937353 = 1453015) (by norm_num)
theorem B5812181 : Blo 1721061 5812181 := bbase (se 7 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 5812181 = 136223) (by norm_num)
theorem B2584541 : Blo 1721061 2584541 := bbase (se 3 (by rfl) ⟨484601, by rfl⟩ : syracuseStep 2584541 = 969203) (by norm_num)
theorem B1937389 : Blo 1721061 1937389 := bbase (se 3 (by rfl) ⟨363260, by rfl⟩ : syracuseStep 1937389 = 726521) (by norm_num)
theorem B2584565 : Blo 1721061 2584565 := bbase (se 5 (by rfl) ⟨121151, by rfl⟩ : syracuseStep 2584565 = 242303) (by norm_num)
theorem B6631429 : Blo 1721061 6631429 := bbase (se 4 (by rfl) ⟨621696, by rfl⟩ : syracuseStep 6631429 = 1243393) (by norm_num)
theorem B2584589 : Blo 1721061 2584589 := bbase (se 3 (by rfl) ⟨484610, by rfl⟩ : syracuseStep 2584589 = 969221) (by norm_num)
theorem B1937425 : Blo 1721061 1937425 := bbase (se 2 (by rfl) ⟨726534, by rfl⟩ : syracuseStep 1937425 = 1453069) (by norm_num)
theorem B1937461 : Blo 1721061 1937461 := bbase (se 5 (by rfl) ⟨90818, by rfl⟩ : syracuseStep 1937461 = 181637) (by norm_num)
theorem B6983765 : Blo 1721061 6983765 := bbase (se 8 (by rfl) ⟨40920, by rfl⟩ : syracuseStep 6983765 = 81841) (by norm_num)
theorem B1937497 : Blo 1721061 1937497 := bbase (se 2 (by rfl) ⟨726561, by rfl⟩ : syracuseStep 1937497 = 1453123) (by norm_num)
theorem B15921269 : Blo 1721061 15921269 := bbase (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) (by norm_num)
theorem B1937533 : Blo 1721061 1937533 := bbase (se 3 (by rfl) ⟨363287, by rfl⟩ : syracuseStep 1937533 = 726575) (by norm_num)
theorem B1839233 : Blo 1721061 1839233 := bbase (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) (by norm_num)
theorem B1937569 : Blo 1721061 1937569 := bbase (se 2 (by rfl) ⟨726588, by rfl⟩ : syracuseStep 1937569 = 1453177) (by norm_num)
theorem B4657333 : Blo 1721061 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B1937605 : Blo 1721061 1937605 := bbase (se 4 (by rfl) ⟨181650, by rfl⟩ : syracuseStep 1937605 = 363301) (by norm_num)
theorem B1937641 : Blo 1721061 1937641 := bbase (se 2 (by rfl) ⟨726615, by rfl⟩ : syracuseStep 1937641 = 1453231) (by norm_num)
theorem B2756845 : Blo 1721061 2756845 := bbase (se 3 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 2756845 = 1033817) (by norm_num)
theorem B1937677 : Blo 1721061 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B2904349 : Blo 1721061 2904349 := bbase (se 3 (by rfl) ⟨544565, by rfl⟩ : syracuseStep 2904349 = 1089131) (by norm_num)
theorem B1937713 : Blo 1721061 1937713 := bbase (se 2 (by rfl) ⟨726642, by rfl⟩ : syracuseStep 1937713 = 1453285) (by norm_num)
theorem B1937749 : Blo 1721061 1937749 := bbase (se 10 (by rfl) ⟨2838, by rfl⟩ : syracuseStep 1937749 = 5677) (by norm_num)
theorem B2068849 : Blo 1721061 2068849 := bbase (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) (by norm_num)
theorem B2904437 : Blo 1721061 2904437 := bbase (se 5 (by rfl) ⟨136145, by rfl⟩ : syracuseStep 2904437 = 272291) (by norm_num)
theorem B1937785 : Blo 1721061 1937785 := bbase (se 2 (by rfl) ⟨726669, by rfl⟩ : syracuseStep 1937785 = 1453339) (by norm_num)
theorem B5812613 : Blo 1721061 5812613 := bbase (se 4 (by rfl) ⟨544932, by rfl⟩ : syracuseStep 5812613 = 1089865) (by norm_num)
theorem B1937821 : Blo 1721061 1937821 := bbase (se 3 (by rfl) ⟨363341, by rfl⟩ : syracuseStep 1937821 = 726683) (by norm_num)
theorem B1937857 : Blo 1721061 1937857 := bbase (se 2 (by rfl) ⟨726696, by rfl⟩ : syracuseStep 1937857 = 1453393) (by norm_num)
theorem B1937893 : Blo 1721061 1937893 := bbase (se 4 (by rfl) ⟨181677, by rfl⟩ : syracuseStep 1937893 = 363355) (by norm_num)
theorem B2904565 : Blo 1721061 2904565 := bbase (se 5 (by rfl) ⟨136151, by rfl⟩ : syracuseStep 2904565 = 272303) (by norm_num)
theorem B1937929 : Blo 1721061 1937929 := bbase (se 2 (by rfl) ⟨726723, by rfl⟩ : syracuseStep 1937929 = 1453447) (by norm_num)
theorem B1937965 : Blo 1721061 1937965 := bbase (se 3 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 1937965 = 726737) (by norm_num)
theorem B1839677 : Blo 1721061 1839677 := bbase (se 3 (by rfl) ⟨344939, by rfl⟩ : syracuseStep 1839677 = 689879) (by norm_num)
theorem B2904653 : Blo 1721061 2904653 := bbase (se 3 (by rfl) ⟨544622, by rfl⟩ : syracuseStep 2904653 = 1089245) (by norm_num)
theorem B1938001 : Blo 1721061 1938001 := bbase (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) (by norm_num)
theorem B9810517 : Blo 1721061 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B8270437 : Blo 1721061 8270437 := bbase (se 4 (by rfl) ⟨775353, by rfl⟩ : syracuseStep 8270437 = 1550707) (by norm_num)
theorem B1938037 : Blo 1721061 1938037 := bbase (se 5 (by rfl) ⟨90845, by rfl⟩ : syracuseStep 1938037 = 181691) (by norm_num)
theorem B1962641 : Blo 1721061 1962641 := bbase (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) (by norm_num)
theorem B4903573 : Blo 1721061 4903573 := bbase (se 6 (by rfl) ⟨114927, by rfl⟩ : syracuseStep 4903573 = 229855) (by norm_num)
theorem B1938073 : Blo 1721061 1938073 := bbase (se 2 (by rfl) ⟨726777, by rfl⟩ : syracuseStep 1938073 = 1453555) (by norm_num)
theorem B3928733 : Blo 1721061 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B1864361 : Blo 1721061 1864361 := bbase (se 2 (by rfl) ⟨699135, by rfl⟩ : syracuseStep 1864361 = 1398271) (by norm_num)
theorem B1962673 : Blo 1721061 1962673 := bbase (se 2 (by rfl) ⟨736002, by rfl⟩ : syracuseStep 1962673 = 1472005) (by norm_num)
theorem B1938109 : Blo 1721061 1938109 := bbase (se 3 (by rfl) ⟨363395, by rfl⟩ : syracuseStep 1938109 = 726791) (by norm_num)
theorem B2904781 : Blo 1721061 2904781 := bbase (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) (by norm_num)
theorem B1938145 : Blo 1721061 1938145 := bbase (se 2 (by rfl) ⟨726804, by rfl⟩ : syracuseStep 1938145 = 1453609) (by norm_num)
theorem B1938181 : Blo 1721061 1938181 := bbase (se 4 (by rfl) ⟨181704, by rfl⟩ : syracuseStep 1938181 = 363409) (by norm_num)
theorem B2904869 : Blo 1721061 2904869 := bbase (se 4 (by rfl) ⟨272331, by rfl⟩ : syracuseStep 2904869 = 544663) (by norm_num)
theorem B1938217 : Blo 1721061 1938217 := bbase (se 2 (by rfl) ⟨726831, by rfl⟩ : syracuseStep 1938217 = 1453663) (by norm_num)
theorem B11031349 : Blo 1721061 11031349 := bbase (se 5 (by rfl) ⟨517094, by rfl⟩ : syracuseStep 11031349 = 1034189) (by norm_num)
theorem B4903733 : Blo 1721061 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B5813045 : Blo 1721061 5813045 := bbase (se 5 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 5813045 = 544973) (by norm_num)
theorem B1839925 : Blo 1721061 1839925 := bbase (se 5 (by rfl) ⟨86246, by rfl⟩ : syracuseStep 1839925 = 172493) (by norm_num)
theorem B1938253 : Blo 1721061 1938253 := bbase (se 3 (by rfl) ⟨363422, by rfl⟩ : syracuseStep 1938253 = 726845) (by norm_num)
theorem B7353173 : Blo 1721061 7353173 := bbase (se 9 (by rfl) ⟨21542, by rfl⟩ : syracuseStep 7353173 = 43085) (by norm_num)
theorem B1938289 : Blo 1721061 1938289 := bbase (se 2 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 1938289 = 1453717) (by norm_num)
theorem B8721269 : Blo 1721061 8721269 := bbase (se 5 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 8721269 = 817619) (by norm_num)
theorem B3101573 : Blo 1721061 3101573 := bbase (se 4 (by rfl) ⟨290772, by rfl⟩ : syracuseStep 3101573 = 581545) (by norm_num)
theorem B2618261 : Blo 1721061 2618261 := bbase (se 6 (by rfl) ⟨61365, by rfl⟩ : syracuseStep 2618261 = 122731) (by norm_num)
theorem B1938325 : Blo 1721061 1938325 := bbase (se 6 (by rfl) ⟨45429, by rfl⟩ : syracuseStep 1938325 = 90859) (by norm_num)
theorem B2904997 : Blo 1721061 2904997 := bbase (se 4 (by rfl) ⟨272343, by rfl⟩ : syracuseStep 2904997 = 544687) (by norm_num)
theorem B1938361 : Blo 1721061 1938361 := bbase (se 2 (by rfl) ⟨726885, by rfl⟩ : syracuseStep 1938361 = 1453771) (by norm_num)
theorem B3314621 : Blo 1721061 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B1938397 : Blo 1721061 1938397 := bbase (se 3 (by rfl) ⟨363449, by rfl⟩ : syracuseStep 1938397 = 726899) (by norm_num)
theorem B2905085 : Blo 1721061 2905085 := bbase (se 3 (by rfl) ⟨544703, by rfl⟩ : syracuseStep 2905085 = 1089407) (by norm_num)
theorem B1938433 : Blo 1721061 1938433 := bbase (se 2 (by rfl) ⟨726912, by rfl⟩ : syracuseStep 1938433 = 1453825) (by norm_num)
theorem B4903973 : Blo 1721061 4903973 := bbase (se 4 (by rfl) ⟨459747, by rfl⟩ : syracuseStep 4903973 = 919495) (by norm_num)
theorem B2208833 : Blo 1721061 2208833 := bbase (se 2 (by rfl) ⟨828312, by rfl⟩ : syracuseStep 2208833 = 1656625) (by norm_num)
theorem B7353413 : Blo 1721061 7353413 := bbase (se 4 (by rfl) ⟨689382, by rfl⟩ : syracuseStep 7353413 = 1378765) (by norm_num)
theorem B4478021 : Blo 1721061 4478021 := bbase (se 4 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 4478021 = 839629) (by norm_num)
theorem B2905213 : Blo 1721061 2905213 := bbase (se 3 (by rfl) ⟨544727, by rfl⟩ : syracuseStep 2905213 = 1089455) (by norm_num)
theorem B5518469 : Blo 1721061 5518469 := bbase (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) (by norm_num)
theorem B2757773 : Blo 1721061 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B3101861 : Blo 1721061 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B2208937 : Blo 1721061 2208937 := bbase (se 2 (by rfl) ⟨828351, by rfl⟩ : syracuseStep 2208937 = 1656703) (by norm_num)
theorem B6288581 : Blo 1721061 6288581 := bbase (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) (by norm_num)
theorem B2905301 : Blo 1721061 2905301 := bbase (se 7 (by rfl) ⟨34046, by rfl⟩ : syracuseStep 2905301 = 68093) (by norm_num)
theorem B1963225 : Blo 1721061 1963225 := bbase (se 2 (by rfl) ⟨736209, by rfl⟩ : syracuseStep 1963225 = 1472419) (by norm_num)
theorem B4904165 : Blo 1721061 4904165 := bbase (se 4 (by rfl) ⟨459765, by rfl⟩ : syracuseStep 4904165 = 919531) (by norm_num)
theorem B5813477 : Blo 1721061 5813477 := bbase (se 4 (by rfl) ⟨545013, by rfl⟩ : syracuseStep 5813477 = 1090027) (by norm_num)
theorem B8713493 : Blo 1721061 8713493 := bbase (se 6 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 8713493 = 408445) (by norm_num)
theorem B2905429 : Blo 1721061 2905429 := bbase (se 16 (by rfl) ⟨66, by rfl⟩ : syracuseStep 2905429 = 133) (by norm_num)
theorem B3102085 : Blo 1721061 3102085 := bbase (se 4 (by rfl) ⟨290820, by rfl⟩ : syracuseStep 3102085 = 581641) (by norm_num)
theorem B2905517 : Blo 1721061 2905517 := bbase (se 3 (by rfl) ⟨544784, by rfl⟩ : syracuseStep 2905517 = 1089569) (by norm_num)
theorem B3102149 : Blo 1721061 3102149 := bbase (se 4 (by rfl) ⟨290826, by rfl⟩ : syracuseStep 3102149 = 581653) (by norm_num)
theorem B2069993 : Blo 1721061 2069993 := bbase (se 2 (by rfl) ⟨776247, by rfl⟩ : syracuseStep 2069993 = 1552495) (by norm_num)
theorem B2209285 : Blo 1721061 2209285 := bbase (se 4 (by rfl) ⟨207120, by rfl⟩ : syracuseStep 2209285 = 414241) (by norm_num)
theorem B2905645 : Blo 1721061 2905645 := bbase (se 3 (by rfl) ⟨544808, by rfl⟩ : syracuseStep 2905645 = 1089617) (by norm_num)
theorem B2758229 : Blo 1721061 2758229 := bbase (se 8 (by rfl) ⟨16161, by rfl⟩ : syracuseStep 2758229 = 32323) (by norm_num)
theorem B2905733 : Blo 1721061 2905733 := bbase (se 4 (by rfl) ⟨272412, by rfl⟩ : syracuseStep 2905733 = 544825) (by norm_num)
theorem B5813909 : Blo 1721061 5813909 := bbase (se 6 (by rfl) ⟨136263, by rfl⟩ : syracuseStep 5813909 = 272527) (by norm_num)
theorem B3872429 : Blo 1721061 3872429 := bbase (se 3 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 3872429 = 1452161) (by norm_num)
theorem B3675869 : Blo 1721061 3675869 := bbase (se 3 (by rfl) ⟨689225, by rfl⟩ : syracuseStep 3675869 = 1378451) (by norm_num)
theorem B3872501 : Blo 1721061 3872501 := bbase (se 5 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 3872501 = 363047) (by norm_num)
theorem B2905861 : Blo 1721061 2905861 := bbase (se 4 (by rfl) ⟨272424, by rfl⟩ : syracuseStep 2905861 = 544849) (by norm_num)
theorem B3872573 : Blo 1721061 3872573 := bbase (se 3 (by rfl) ⟨726107, by rfl⟩ : syracuseStep 3872573 = 1452215) (by norm_num)
theorem B2045785 : Blo 1721061 2045785 := bbase (se 2 (by rfl) ⟨767169, by rfl⟩ : syracuseStep 2045785 = 1534339) (by norm_num)
theorem B2905949 : Blo 1721061 2905949 := bbase (se 3 (by rfl) ⟨544865, by rfl⟩ : syracuseStep 2905949 = 1089731) (by norm_num)
theorem B3872645 : Blo 1721061 3872645 := bbase (se 4 (by rfl) ⟨363060, by rfl⟩ : syracuseStep 3872645 = 726121) (by norm_num)
theorem B3872717 : Blo 1721061 3872717 := bbase (se 3 (by rfl) ⟨726134, by rfl⟩ : syracuseStep 3872717 = 1452269) (by norm_num)
theorem B2906077 : Blo 1721061 2906077 := bbase (se 3 (by rfl) ⟨544889, by rfl⟩ : syracuseStep 2906077 = 1089779) (by norm_num)
theorem B4249597 : Blo 1721061 4249597 := bbase (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) (by norm_num)
theorem B3872789 : Blo 1721061 3872789 := bbase (se 6 (by rfl) ⟨90768, by rfl⟩ : syracuseStep 3872789 = 181537) (by norm_num)
theorem B2906165 : Blo 1721061 2906165 := bbase (se 5 (by rfl) ⟨136226, by rfl⟩ : syracuseStep 2906165 = 272453) (by norm_num)
theorem B5814341 : Blo 1721061 5814341 := bbase (se 4 (by rfl) ⟨545094, by rfl⟩ : syracuseStep 5814341 = 1090189) (by norm_num)
theorem B3872861 : Blo 1721061 3872861 := bbase (se 3 (by rfl) ⟨726161, by rfl⟩ : syracuseStep 3872861 = 1452323) (by norm_num)
theorem B8722565 : Blo 1721061 8722565 := bbase (se 4 (by rfl) ⟨817740, by rfl⟩ : syracuseStep 8722565 = 1635481) (by norm_num)
theorem B3872933 : Blo 1721061 3872933 := bbase (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) (by norm_num)
theorem B6535349 : Blo 1721061 6535349 := bbase (se 5 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 6535349 = 612689) (by norm_num)
theorem B2906293 : Blo 1721061 2906293 := bbase (se 5 (by rfl) ⟨136232, by rfl⟩ : syracuseStep 2906293 = 272465) (by norm_num)
theorem B4905157 : Blo 1721061 4905157 := bbase (se 4 (by rfl) ⟨459858, by rfl⟩ : syracuseStep 4905157 = 919717) (by norm_num)
theorem B3873005 : Blo 1721061 3873005 := bbase (se 3 (by rfl) ⟨726188, by rfl⟩ : syracuseStep 3873005 = 1452377) (by norm_num)
theorem B2906381 : Blo 1721061 2906381 := bbase (se 3 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 2906381 = 1089893) (by norm_num)
theorem B3873077 : Blo 1721061 3873077 := bbase (se 5 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 3873077 = 363101) (by norm_num)
theorem B16554293 : Blo 1721061 16554293 := bbase (se 5 (by rfl) ⟨775982, by rfl⟩ : syracuseStep 16554293 = 1551965) (by norm_num)
theorem B3873149 : Blo 1721061 3873149 := bbase (se 3 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 3873149 = 1452431) (by norm_num)
theorem B2906509 : Blo 1721061 2906509 := bbase (se 3 (by rfl) ⟨544970, by rfl⟩ : syracuseStep 2906509 = 1089941) (by norm_num)
theorem B3873221 : Blo 1721061 3873221 := bbase (se 4 (by rfl) ⟨363114, by rfl⟩ : syracuseStep 3873221 = 726229) (by norm_num)
theorem B6535637 : Blo 1721061 6535637 := bbase (se 7 (by rfl) ⟨76589, by rfl⟩ : syracuseStep 6535637 = 153179) (by norm_num)
theorem B2906597 : Blo 1721061 2906597 := bbase (se 4 (by rfl) ⟨272493, by rfl⟩ : syracuseStep 2906597 = 544987) (by norm_num)
theorem B5814773 : Blo 1721061 5814773 := bbase (se 5 (by rfl) ⟨272567, by rfl⟩ : syracuseStep 5814773 = 545135) (by norm_num)
theorem B4356605 : Blo 1721061 4356605 := bbase (se 3 (by rfl) ⟨816863, by rfl⟩ : syracuseStep 4356605 = 1633727) (by norm_num)
theorem B3873293 : Blo 1721061 3873293 := bbase (se 3 (by rfl) ⟨726242, by rfl⟩ : syracuseStep 3873293 = 1452485) (by norm_num)
theorem B9812501 : Blo 1721061 9812501 := bbase (se 6 (by rfl) ⟨229980, by rfl⟩ : syracuseStep 9812501 = 459961) (by norm_num)
theorem B8714789 : Blo 1721061 8714789 := bbase (se 4 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 8714789 = 1634023) (by norm_num)
theorem B3873365 : Blo 1721061 3873365 := bbase (se 8 (by rfl) ⟨22695, by rfl⟩ : syracuseStep 3873365 = 45391) (by norm_num)
theorem B3676757 : Blo 1721061 3676757 := bbase (se 8 (by rfl) ⟨21543, by rfl⟩ : syracuseStep 3676757 = 43087) (by norm_num)
theorem B2906725 : Blo 1721061 2906725 := bbase (se 4 (by rfl) ⟨272505, by rfl⟩ : syracuseStep 2906725 = 545011) (by norm_num)
theorem B11188853 : Blo 1721061 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B3873437 : Blo 1721061 3873437 := bbase (se 3 (by rfl) ⟨726269, by rfl⟩ : syracuseStep 3873437 = 1452539) (by norm_num)
theorem B2906813 : Blo 1721061 2906813 := bbase (se 3 (by rfl) ⟨545027, by rfl⟩ : syracuseStep 2906813 = 1090055) (by norm_num)
theorem B39770837 : Blo 1721061 39770837 := bbase (se 7 (by rfl) ⟨466064, by rfl⟩ : syracuseStep 39770837 = 932129) (by norm_num)
theorem B3873509 : Blo 1721061 3873509 := bbase (se 4 (by rfl) ⟨363141, by rfl⟩ : syracuseStep 3873509 = 726283) (by norm_num)
theorem B4135661 : Blo 1721061 4135661 := bbase (se 3 (by rfl) ⟨775436, by rfl⟩ : syracuseStep 4135661 = 1550873) (by norm_num)
theorem B3873581 : Blo 1721061 3873581 := bbase (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) (by norm_num)
theorem B2906941 : Blo 1721061 2906941 := bbase (se 3 (by rfl) ⟨545051, by rfl⟩ : syracuseStep 2906941 = 1090103) (by norm_num)
theorem B3676997 : Blo 1721061 3676997 := bbase (se 4 (by rfl) ⟨344718, by rfl⟩ : syracuseStep 3676997 = 689437) (by norm_num)
theorem B4356949 : Blo 1721061 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B3873653 : Blo 1721061 3873653 := bbase (se 5 (by rfl) ⟨181577, by rfl⟩ : syracuseStep 3873653 = 363155) (by norm_num)
theorem B3267469 : Blo 1721061 3267469 := bbase (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) (by norm_num)
theorem B3726229 : Blo 1721061 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B2907029 : Blo 1721061 2907029 := bbase (se 6 (by rfl) ⟨68133, by rfl⟩ : syracuseStep 2907029 = 136267) (by norm_num)
theorem B5815205 : Blo 1721061 5815205 := bbase (se 4 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 5815205 = 1090351) (by norm_num)
theorem B4135853 : Blo 1721061 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B3873725 : Blo 1721061 3873725 := bbase (se 3 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 3873725 = 1452647) (by norm_num)
theorem B4357061 : Blo 1721061 4357061 := bbase (se 4 (by rfl) ⟨408474, by rfl⟩ : syracuseStep 4357061 = 816949) (by norm_num)
theorem B2759645 : Blo 1721061 2759645 := bbase (se 3 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 2759645 = 1034867) (by norm_num)
theorem B3873797 : Blo 1721061 3873797 := bbase (se 4 (by rfl) ⟨363168, by rfl⟩ : syracuseStep 3873797 = 726337) (by norm_num)
theorem B2907157 : Blo 1721061 2907157 := bbase (se 6 (by rfl) ⟨68136, by rfl⟩ : syracuseStep 2907157 = 136273) (by norm_num)
theorem B3873869 : Blo 1721061 3873869 := bbase (se 3 (by rfl) ⟨726350, by rfl⟩ : syracuseStep 3873869 = 1452701) (by norm_num)
theorem B15711317 : Blo 1721061 15711317 := bbase (se 8 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 15711317 = 184117) (by norm_num)
theorem B2907245 : Blo 1721061 2907245 := bbase (se 3 (by rfl) ⟨545108, by rfl⟩ : syracuseStep 2907245 = 1090217) (by norm_num)
theorem B4357253 : Blo 1721061 4357253 := bbase (se 4 (by rfl) ⟨408492, by rfl⟩ : syracuseStep 4357253 = 816985) (by norm_num)
theorem B3873941 : Blo 1721061 3873941 := bbase (se 6 (by rfl) ⟨90795, by rfl⟩ : syracuseStep 3873941 = 181591) (by norm_num)
theorem B3267773 : Blo 1721061 3267773 := bbase (se 3 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 3267773 = 1225415) (by norm_num)
theorem B2759869 : Blo 1721061 2759869 := bbase (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) (by norm_num)
theorem B4136141 : Blo 1721061 4136141 := bbase (se 3 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 4136141 = 1551053) (by norm_num)
theorem B3874013 : Blo 1721061 3874013 := bbase (se 3 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 3874013 = 1452755) (by norm_num)
theorem B2907373 : Blo 1721061 2907373 := bbase (se 3 (by rfl) ⟨545132, by rfl⟩ : syracuseStep 2907373 = 1090265) (by norm_num)
theorem B4906261 : Blo 1721061 4906261 := bbase (se 6 (by rfl) ⟨114990, by rfl⟩ : syracuseStep 4906261 = 229981) (by norm_num)
theorem B3874085 : Blo 1721061 3874085 := bbase (se 4 (by rfl) ⟨363195, by rfl⟩ : syracuseStep 3874085 = 726391) (by norm_num)
theorem B2178353 : Blo 1721061 2178353 := bbase (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) (by norm_num)
theorem B7355701 : Blo 1721061 7355701 := bbase (se 5 (by rfl) ⟨344798, by rfl⟩ : syracuseStep 7355701 = 689597) (by norm_num)
theorem B3677501 : Blo 1721061 3677501 := bbase (se 3 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 3677501 = 1379063) (by norm_num)
theorem B3677509 : Blo 1721061 3677509 := bbase (se 4 (by rfl) ⟨344766, by rfl⟩ : syracuseStep 3677509 = 689533) (by norm_num)
theorem B2907461 : Blo 1721061 2907461 := bbase (se 4 (by rfl) ⟨272574, by rfl⟩ : syracuseStep 2907461 = 545149) (by norm_num)
theorem B2178409 : Blo 1721061 2178409 := bbase (se 2 (by rfl) ⟨816903, by rfl⟩ : syracuseStep 2178409 = 1633807) (by norm_num)
theorem B3874157 : Blo 1721061 3874157 := bbase (se 3 (by rfl) ⟨726404, by rfl⟩ : syracuseStep 3874157 = 1452809) (by norm_num)
theorem B4652437 : Blo 1721061 4652437 := bbase (se 6 (by rfl) ⟨109041, by rfl⟩ : syracuseStep 4652437 = 218083) (by norm_num)
theorem B3874229 : Blo 1721061 3874229 := bbase (se 5 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 3874229 = 363209) (by norm_num)
theorem B2907589 : Blo 1721061 2907589 := bbase (se 4 (by rfl) ⟨272586, by rfl⟩ : syracuseStep 2907589 = 545173) (by norm_num)
theorem B2178505 : Blo 1721061 2178505 := bbase (se 2 (by rfl) ⟨816939, by rfl⟩ : syracuseStep 2178505 = 1633879) (by norm_num)
theorem B4357597 : Blo 1721061 4357597 := bbase (se 3 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 4357597 = 1634099) (by norm_num)
theorem B3538421 : Blo 1721061 3538421 := bbase (se 5 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 3538421 = 331727) (by norm_num)
theorem B3874301 : Blo 1721061 3874301 := bbase (se 3 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 3874301 = 1452863) (by norm_num)
theorem B3726853 : Blo 1721061 3726853 := bbase (se 4 (by rfl) ⟨349392, by rfl⟩ : syracuseStep 3726853 = 698785) (by norm_num)
theorem B3874373 : Blo 1721061 3874373 := bbase (se 4 (by rfl) ⟨363222, by rfl⟩ : syracuseStep 3874373 = 726445) (by norm_num)
theorem B4357709 : Blo 1721061 4357709 := bbase (se 3 (by rfl) ⟨817070, by rfl⟩ : syracuseStep 4357709 = 1634141) (by norm_num)
theorem B4972117 : Blo 1721061 4972117 := bbase (se 8 (by rfl) ⟨29133, by rfl⟩ : syracuseStep 4972117 = 58267) (by norm_num)
theorem B2178677 : Blo 1721061 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B6536821 : Blo 1721061 6536821 := bbase (se 5 (by rfl) ⟨306413, by rfl⟩ : syracuseStep 6536821 = 612827) (by norm_num)
theorem B6209141 : Blo 1721061 6209141 := bbase (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) (by norm_num)
theorem B3874445 : Blo 1721061 3874445 := bbase (se 3 (by rfl) ⟨726458, by rfl⟩ : syracuseStep 3874445 = 1452917) (by norm_num)
theorem B2178733 : Blo 1721061 2178733 := bbase (se 3 (by rfl) ⟨408512, by rfl⟩ : syracuseStep 2178733 = 817025) (by norm_num)
theorem B9313973 : Blo 1721061 9313973 := bbase (se 5 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 9313973 = 873185) (by norm_num)
theorem B3874517 : Blo 1721061 3874517 := bbase (se 7 (by rfl) ⟨45404, by rfl⟩ : syracuseStep 3874517 = 90809) (by norm_num)
theorem B2178829 : Blo 1721061 2178829 := bbase (se 3 (by rfl) ⟨408530, by rfl⟩ : syracuseStep 2178829 = 817061) (by norm_num)
theorem B4357901 : Blo 1721061 4357901 := bbase (se 3 (by rfl) ⟨817106, by rfl⟩ : syracuseStep 4357901 = 1634213) (by norm_num)
theorem B3874589 : Blo 1721061 3874589 := bbase (se 3 (by rfl) ⟨726485, by rfl⟩ : syracuseStep 3874589 = 1452971) (by norm_num)
theorem B8716085 : Blo 1721061 8716085 := bbase (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) (by norm_num)
theorem B1769293 : Blo 1721061 1769293 := bbase (se 3 (by rfl) ⟨331742, by rfl⟩ : syracuseStep 1769293 = 663485) (by norm_num)
theorem B3358549 : Blo 1721061 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B4972373 : Blo 1721061 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B3874661 : Blo 1721061 3874661 := bbase (se 4 (by rfl) ⟨363249, by rfl⟩ : syracuseStep 3874661 = 726499) (by norm_num)
theorem B12582773 : Blo 1721061 12582773 := bbase (se 5 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 12582773 = 1179635) (by norm_num)
theorem B6537125 : Blo 1721061 6537125 := bbase (se 4 (by rfl) ⟨612855, by rfl⟩ : syracuseStep 6537125 = 1225711) (by norm_num)
theorem B3268525 : Blo 1721061 3268525 := bbase (se 3 (by rfl) ⟨612848, by rfl⟩ : syracuseStep 3268525 = 1225697) (by norm_num)
theorem B3874733 : Blo 1721061 3874733 := bbase (se 3 (by rfl) ⟨726512, by rfl⟩ : syracuseStep 3874733 = 1453025) (by norm_num)
theorem B2179001 : Blo 1721061 2179001 := bbase (se 2 (by rfl) ⟨817125, by rfl⟩ : syracuseStep 2179001 = 1634251) (by norm_num)
theorem B2179057 : Blo 1721061 2179057 := bbase (se 2 (by rfl) ⟨817146, by rfl⟩ : syracuseStep 2179057 = 1634293) (by norm_num)
theorem B3874805 : Blo 1721061 3874805 := bbase (se 5 (by rfl) ⟨181631, by rfl⟩ : syracuseStep 3874805 = 363263) (by norm_num)
theorem B6537293 : Blo 1721061 6537293 := bstep (se 3 (by rfl) ⟨1225742, by rfl⟩ : syracuseStep 6537293 = 2451485) B2451485
theorem B4358225 : Blo 1721061 4358225 := bstep (se 2 (by rfl) ⟨1634334, by rfl⟩ : syracuseStep 4358225 = 3268669) B3268669
theorem B2179219 : Blo 1721061 2179219 := bstep (se 1 (by rfl) ⟨1634414, by rfl⟩ : syracuseStep 2179219 = 3268829) B3268829
theorem B9568433 : Blo 1721061 9568433 := bstep (se 2 (by rfl) ⟨3588162, by rfl⟩ : syracuseStep 9568433 = 7176325) B7176325
theorem B2326753 : Blo 1721061 2326753 := bstep (se 2 (by rfl) ⟨872532, by rfl⟩ : syracuseStep 2326753 = 1745065) B1745065
theorem B3875057 : Blo 1721061 3875057 := bstep (se 2 (by rfl) ⟨1453146, by rfl⟩ : syracuseStep 3875057 = 2906293) B2906293
theorem B6209777 : Blo 1721061 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B2179315 : Blo 1721061 2179315 := bstep (se 1 (by rfl) ⟨1634486, by rfl⟩ : syracuseStep 2179315 = 3268973) B3268973
theorem B3875075 : Blo 1721061 3875075 := bstep (se 1 (by rfl) ⟨2906306, by rfl⟩ : syracuseStep 3875075 = 5812613) B5812613
theorem B9937349 : Blo 1721061 9937349 := bstep (se 4 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 9937349 = 1863253) B1863253
theorem B16769549 : Blo 1721061 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B3875345 : Blo 1721061 3875345 := bstep (se 2 (by rfl) ⟨1453254, by rfl⟩ : syracuseStep 3875345 = 2906509) B2906509
theorem B3269155 : Blo 1721061 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B3875363 : Blo 1721061 3875363 := bstep (se 1 (by rfl) ⟨2906522, by rfl⟩ : syracuseStep 3875363 = 5813045) B5813045
theorem B1745507 : Blo 1721061 1745507 := bstep (se 1 (by rfl) ⟨1309130, by rfl⟩ : syracuseStep 1745507 = 2618261) B2618261
theorem B23560885 : Blo 1721061 23560885 := bstep (se 5 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 23560885 = 2208833) B2208833
theorem B3269315 : Blo 1721061 3269315 := bstep (se 1 (by rfl) ⟨2451986, by rfl⟩ : syracuseStep 3269315 = 4903973) B4903973
theorem B5513933 : Blo 1721061 5513933 := bstep (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) B2067725
theorem B2179811 : Blo 1721061 2179811 := bstep (se 1 (by rfl) ⟨1634858, by rfl⟩ : syracuseStep 2179811 = 3269717) B3269717
theorem B1721075 : Blo 1721061 1721075 := bstep (se 1 (by rfl) ⟨1290806, by rfl⟩ : syracuseStep 1721075 = 2581613) B2581613
theorem B1721091 : Blo 1721061 1721091 := bstep (se 1 (by rfl) ⟨1290818, by rfl⟩ : syracuseStep 1721091 = 2581637) B2581637
theorem B3678979 : Blo 1721061 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B18621197 : Blo 1721061 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B1721107 : Blo 1721061 1721107 := bstep (se 1 (by rfl) ⟨1290830, by rfl⟩ : syracuseStep 1721107 = 2581661) B2581661
theorem B1721123 : Blo 1721061 1721123 := bstep (se 1 (by rfl) ⟨1290842, by rfl⟩ : syracuseStep 1721123 = 2581685) B2581685
theorem B5808941 : Blo 1721061 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B11027249 : Blo 1721061 11027249 := bstep (se 2 (by rfl) ⟨4135218, by rfl⟩ : syracuseStep 11027249 = 8270437) B8270437
theorem B1721139 : Blo 1721061 1721139 := bstep (se 1 (by rfl) ⟨1290854, by rfl⟩ : syracuseStep 1721139 = 2581709) B2581709
theorem B2327347 : Blo 1721061 2327347 := bstep (se 1 (by rfl) ⟨1745510, by rfl⟩ : syracuseStep 2327347 = 3491021) B3491021
theorem B3875633 : Blo 1721061 3875633 := bstep (se 2 (by rfl) ⟨1453362, by rfl⟩ : syracuseStep 3875633 = 2906725) B2906725
theorem B1721155 : Blo 1721061 1721155 := bstep (se 1 (by rfl) ⟨1290866, by rfl⟩ : syracuseStep 1721155 = 2581733) B2581733
theorem B3875651 : Blo 1721061 3875651 := bstep (se 1 (by rfl) ⟨2906738, by rfl⟩ : syracuseStep 3875651 = 5813477) B5813477
theorem B9806669 : Blo 1721061 9806669 := bstep (se 3 (by rfl) ⟨1838750, by rfl⟩ : syracuseStep 9806669 = 3677501) B3677501
theorem B1721171 : Blo 1721061 1721171 := bstep (se 1 (by rfl) ⟨1290878, by rfl⟩ : syracuseStep 1721171 = 2581757) B2581757
theorem B11027299 : Blo 1721061 11027299 := bstep (se 1 (by rfl) ⟨8270474, by rfl⟩ : syracuseStep 11027299 = 16540949) B16540949
theorem B5808995 : Blo 1721061 5808995 := bstep (se 1 (by rfl) ⟨4356746, by rfl⟩ : syracuseStep 5808995 = 8713493) B8713493
theorem B1721187 : Blo 1721061 1721187 := bstep (se 1 (by rfl) ⟨1290890, by rfl⟩ : syracuseStep 1721187 = 2581781) B2581781
theorem B6538097 : Blo 1721061 6538097 := bstep (se 2 (by rfl) ⟨2451786, by rfl⟩ : syracuseStep 6538097 = 4903573) B4903573
theorem B1721203 : Blo 1721061 1721203 := bstep (se 1 (by rfl) ⟨1290902, by rfl⟩ : syracuseStep 1721203 = 2581805) B2581805
theorem B1721219 : Blo 1721061 1721219 := bstep (se 1 (by rfl) ⟨1290914, by rfl⟩ : syracuseStep 1721219 = 2581829) B2581829
theorem B1721235 : Blo 1721061 1721235 := bstep (se 1 (by rfl) ⟨1290926, by rfl⟩ : syracuseStep 1721235 = 2581853) B2581853
theorem B1721251 : Blo 1721061 1721251 := bstep (se 1 (by rfl) ⟨1290938, by rfl⟩ : syracuseStep 1721251 = 2581877) B2581877
theorem B8717219 : Blo 1721061 8717219 := bstep (se 1 (by rfl) ⟨6537914, by rfl⟩ : syracuseStep 8717219 = 13075829) B13075829
theorem B1721267 : Blo 1721061 1721267 := bstep (se 1 (by rfl) ⟨1290950, by rfl⟩ : syracuseStep 1721267 = 2581901) B2581901
theorem B1721283 : Blo 1721061 1721283 := bstep (se 1 (by rfl) ⟨1290962, by rfl⟩ : syracuseStep 1721283 = 2581925) B2581925
theorem B1721299 : Blo 1721061 1721299 := bstep (se 1 (by rfl) ⟨1290974, by rfl⟩ : syracuseStep 1721299 = 2581949) B2581949
theorem B1721315 : Blo 1721061 1721315 := bstep (se 1 (by rfl) ⟨1290986, by rfl⟩ : syracuseStep 1721315 = 2581973) B2581973
theorem B1721331 : Blo 1721061 1721331 := bstep (se 1 (by rfl) ⟨1290998, by rfl⟩ : syracuseStep 1721331 = 2581997) B2581997
theorem B1721347 : Blo 1721061 1721347 := bstep (se 1 (by rfl) ⟨1291010, by rfl⟩ : syracuseStep 1721347 = 2582021) B2582021
theorem B1721363 : Blo 1721061 1721363 := bstep (se 1 (by rfl) ⟨1291022, by rfl⟩ : syracuseStep 1721363 = 2582045) B2582045
theorem B41870357 : Blo 1721061 41870357 := bstep (se 6 (by rfl) ⟨981336, by rfl⟩ : syracuseStep 41870357 = 1962673) B1962673
theorem B1721379 : Blo 1721061 1721379 := bstep (se 1 (by rfl) ⟨1291034, by rfl⟩ : syracuseStep 1721379 = 2582069) B2582069
theorem B4359217 : Blo 1721061 4359217 := bstep (se 2 (by rfl) ⟨1634706, by rfl⟩ : syracuseStep 4359217 = 3269413) B3269413
theorem B1721395 : Blo 1721061 1721395 := bstep (se 1 (by rfl) ⟨1291046, by rfl⟩ : syracuseStep 1721395 = 2582093) B2582093
theorem B1721411 : Blo 1721061 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B3875921 : Blo 1721061 3875921 := bstep (se 2 (by rfl) ⟨1453470, by rfl⟩ : syracuseStep 3875921 = 2906941) B2906941
theorem B1721427 : Blo 1721061 1721427 := bstep (se 1 (by rfl) ⟨1291070, by rfl⟩ : syracuseStep 1721427 = 2582141) B2582141
theorem B2581601 : Blo 1721061 2581601 := bstep (se 2 (by rfl) ⟨968100, by rfl⟩ : syracuseStep 2581601 = 1936201) B1936201
theorem B1721443 : Blo 1721061 1721443 := bstep (se 1 (by rfl) ⟨1291082, by rfl⟩ : syracuseStep 1721443 = 2582165) B2582165
theorem B3875939 : Blo 1721061 3875939 := bstep (se 1 (by rfl) ⟨2906954, by rfl⟩ : syracuseStep 3875939 = 5813909) B5813909
theorem B5809265 : Blo 1721061 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B2581619 : Blo 1721061 2581619 := bstep (se 1 (by rfl) ⟨1936214, by rfl⟩ : syracuseStep 2581619 = 3872429) B3872429
theorem B1721459 : Blo 1721061 1721459 := bstep (se 1 (by rfl) ⟨1291094, by rfl⟩ : syracuseStep 1721459 = 2582189) B2582189
theorem B1721475 : Blo 1721061 1721475 := bstep (se 1 (by rfl) ⟨1291106, by rfl⟩ : syracuseStep 1721475 = 2582213) B2582213
theorem B2581649 : Blo 1721061 2581649 := bstep (se 2 (by rfl) ⟨968118, by rfl⟩ : syracuseStep 2581649 = 1936237) B1936237
theorem B2450579 : Blo 1721061 2450579 := bstep (se 1 (by rfl) ⟨1837934, by rfl⟩ : syracuseStep 2450579 = 3675869) B3675869
theorem B1721491 : Blo 1721061 1721491 := bstep (se 1 (by rfl) ⟨1291118, by rfl⟩ : syracuseStep 1721491 = 2582237) B2582237
theorem B2581667 : Blo 1721061 2581667 := bstep (se 1 (by rfl) ⟨1936250, by rfl⟩ : syracuseStep 2581667 = 3872501) B3872501
theorem B1721507 : Blo 1721061 1721507 := bstep (se 1 (by rfl) ⟨1291130, by rfl⟩ : syracuseStep 1721507 = 2582261) B2582261
theorem B1721523 : Blo 1721061 1721523 := bstep (se 1 (by rfl) ⟨1291142, by rfl⟩ : syracuseStep 1721523 = 2582285) B2582285
theorem B2581697 : Blo 1721061 2581697 := bstep (se 2 (by rfl) ⟨968136, by rfl⟩ : syracuseStep 2581697 = 1936273) B1936273
theorem B1721539 : Blo 1721061 1721539 := bstep (se 1 (by rfl) ⟨1291154, by rfl⟩ : syracuseStep 1721539 = 2582309) B2582309
theorem B2581715 : Blo 1721061 2581715 := bstep (se 1 (by rfl) ⟨1936286, by rfl⟩ : syracuseStep 2581715 = 3872573) B3872573
theorem B1721555 : Blo 1721061 1721555 := bstep (se 1 (by rfl) ⟨1291166, by rfl⟩ : syracuseStep 1721555 = 2582333) B2582333
theorem B1721571 : Blo 1721061 1721571 := bstep (se 1 (by rfl) ⟨1291178, by rfl⟩ : syracuseStep 1721571 = 2582357) B2582357
theorem B2581745 : Blo 1721061 2581745 := bstep (se 2 (by rfl) ⟨968154, by rfl⟩ : syracuseStep 2581745 = 1936309) B1936309
theorem B1721587 : Blo 1721061 1721587 := bstep (se 1 (by rfl) ⟨1291190, by rfl⟩ : syracuseStep 1721587 = 2582381) B2582381
theorem B2581763 : Blo 1721061 2581763 := bstep (se 1 (by rfl) ⟨1936322, by rfl⟩ : syracuseStep 2581763 = 3872645) B3872645
theorem B1721603 : Blo 1721061 1721603 := bstep (se 1 (by rfl) ⟨1291202, by rfl⟩ : syracuseStep 1721603 = 2582405) B2582405
theorem B1721619 : Blo 1721061 1721619 := bstep (se 1 (by rfl) ⟨1291214, by rfl⟩ : syracuseStep 1721619 = 2582429) B2582429
theorem B2581793 : Blo 1721061 2581793 := bstep (se 2 (by rfl) ⟨968172, by rfl⟩ : syracuseStep 2581793 = 1936345) B1936345
theorem B1721635 : Blo 1721061 1721635 := bstep (se 1 (by rfl) ⟨1291226, by rfl⟩ : syracuseStep 1721635 = 2582453) B2582453
theorem B2581811 : Blo 1721061 2581811 := bstep (se 1 (by rfl) ⟨1936358, by rfl⟩ : syracuseStep 2581811 = 3872717) B3872717
theorem B1721651 : Blo 1721061 1721651 := bstep (se 1 (by rfl) ⟨1291238, by rfl⟩ : syracuseStep 1721651 = 2582477) B2582477
theorem B1721667 : Blo 1721061 1721667 := bstep (se 1 (by rfl) ⟨1291250, by rfl⟩ : syracuseStep 1721667 = 2582501) B2582501
theorem B4359491 : Blo 1721061 4359491 := bstep (se 1 (by rfl) ⟨3269618, by rfl⟩ : syracuseStep 4359491 = 6539237) B6539237
theorem B2581841 : Blo 1721061 2581841 := bstep (se 2 (by rfl) ⟨968190, by rfl⟩ : syracuseStep 2581841 = 1936381) B1936381
theorem B1721683 : Blo 1721061 1721683 := bstep (se 1 (by rfl) ⟨1291262, by rfl⟩ : syracuseStep 1721683 = 2582525) B2582525
theorem B2581859 : Blo 1721061 2581859 := bstep (se 1 (by rfl) ⟨1936394, by rfl⟩ : syracuseStep 2581859 = 3872789) B3872789
theorem B1721699 : Blo 1721061 1721699 := bstep (se 1 (by rfl) ⟨1291274, by rfl⟩ : syracuseStep 1721699 = 2582549) B2582549
theorem B3876209 : Blo 1721061 3876209 := bstep (se 2 (by rfl) ⟨1453578, by rfl⟩ : syracuseStep 3876209 = 2907157) B2907157
theorem B1721715 : Blo 1721061 1721715 := bstep (se 1 (by rfl) ⟨1291286, by rfl⟩ : syracuseStep 1721715 = 2582573) B2582573
theorem B2581889 : Blo 1721061 2581889 := bstep (se 2 (by rfl) ⟨968208, by rfl⟩ : syracuseStep 2581889 = 1936417) B1936417
theorem B1721731 : Blo 1721061 1721731 := bstep (se 1 (by rfl) ⟨1291298, by rfl⟩ : syracuseStep 1721731 = 2582597) B2582597
theorem B3876227 : Blo 1721061 3876227 := bstep (se 1 (by rfl) ⟨2907170, by rfl⟩ : syracuseStep 3876227 = 5814341) B5814341
theorem B2581907 : Blo 1721061 2581907 := bstep (se 1 (by rfl) ⟨1936430, by rfl⟩ : syracuseStep 2581907 = 3872861) B3872861
theorem B1721747 : Blo 1721061 1721747 := bstep (se 1 (by rfl) ⟨1291310, by rfl⟩ : syracuseStep 1721747 = 2582621) B2582621
theorem B1721763 : Blo 1721061 1721763 := bstep (se 1 (by rfl) ⟨1291322, by rfl⟩ : syracuseStep 1721763 = 2582645) B2582645
theorem B2180515 : Blo 1721061 2180515 := bstep (se 1 (by rfl) ⟨1635386, by rfl⟩ : syracuseStep 2180515 = 3270773) B3270773
theorem B2581937 : Blo 1721061 2581937 := bstep (se 2 (by rfl) ⟨968226, by rfl⟩ : syracuseStep 2581937 = 1936453) B1936453
theorem B1721779 : Blo 1721061 1721779 := bstep (se 1 (by rfl) ⟨1291334, by rfl⟩ : syracuseStep 1721779 = 2582669) B2582669
theorem B2581955 : Blo 1721061 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B1721795 : Blo 1721061 1721795 := bstep (se 1 (by rfl) ⟨1291346, by rfl⟩ : syracuseStep 1721795 = 2582693) B2582693
theorem B1721811 : Blo 1721061 1721811 := bstep (se 1 (by rfl) ⟨1291358, by rfl⟩ : syracuseStep 1721811 = 2582717) B2582717
theorem B2581985 : Blo 1721061 2581985 := bstep (se 2 (by rfl) ⟨968244, by rfl⟩ : syracuseStep 2581985 = 1936489) B1936489
theorem B1721827 : Blo 1721061 1721827 := bstep (se 1 (by rfl) ⟨1291370, by rfl⟩ : syracuseStep 1721827 = 2582741) B2582741
theorem B2582003 : Blo 1721061 2582003 := bstep (se 1 (by rfl) ⟨1936502, by rfl⟩ : syracuseStep 2582003 = 3873005) B3873005
theorem B1721843 : Blo 1721061 1721843 := bstep (se 1 (by rfl) ⟨1291382, by rfl⟩ : syracuseStep 1721843 = 2582765) B2582765
theorem B1721859 : Blo 1721061 1721859 := bstep (se 1 (by rfl) ⟨1291394, by rfl⟩ : syracuseStep 1721859 = 2582789) B2582789
theorem B4359683 : Blo 1721061 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B2180611 : Blo 1721061 2180611 := bstep (se 1 (by rfl) ⟨1635458, by rfl⟩ : syracuseStep 2180611 = 3270917) B3270917
theorem B6538765 : Blo 1721061 6538765 := bstep (se 3 (by rfl) ⟨1226018, by rfl⟩ : syracuseStep 6538765 = 2452037) B2452037
theorem B2582033 : Blo 1721061 2582033 := bstep (se 2 (by rfl) ⟨968262, by rfl⟩ : syracuseStep 2582033 = 1936525) B1936525
theorem B1721875 : Blo 1721061 1721875 := bstep (se 1 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 1721875 = 2582813) B2582813
theorem B2582051 : Blo 1721061 2582051 := bstep (se 1 (by rfl) ⟨1936538, by rfl⟩ : syracuseStep 2582051 = 3873077) B3873077
theorem B1721891 : Blo 1721061 1721891 := bstep (se 1 (by rfl) ⟨1291418, by rfl⟩ : syracuseStep 1721891 = 2582837) B2582837
theorem B3491363 : Blo 1721061 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B11036195 : Blo 1721061 11036195 := bstep (se 1 (by rfl) ⟨8277146, by rfl⟩ : syracuseStep 11036195 = 16554293) B16554293
theorem B1721907 : Blo 1721061 1721907 := bstep (se 1 (by rfl) ⟨1291430, by rfl⟩ : syracuseStep 1721907 = 2582861) B2582861
theorem B2582081 : Blo 1721061 2582081 := bstep (se 2 (by rfl) ⟨968280, by rfl⟩ : syracuseStep 2582081 = 1936561) B1936561
theorem B1721923 : Blo 1721061 1721923 := bstep (se 1 (by rfl) ⟨1291442, by rfl⟩ : syracuseStep 1721923 = 2582885) B2582885
theorem B3679825 : Blo 1721061 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B2582099 : Blo 1721061 2582099 := bstep (se 1 (by rfl) ⟨1936574, by rfl⟩ : syracuseStep 2582099 = 3873149) B3873149
theorem B1721939 : Blo 1721061 1721939 := bstep (se 1 (by rfl) ⟨1291454, by rfl⟩ : syracuseStep 1721939 = 2582909) B2582909
theorem B1721955 : Blo 1721061 1721955 := bstep (se 1 (by rfl) ⟨1291466, by rfl⟩ : syracuseStep 1721955 = 2582933) B2582933
theorem B2582129 : Blo 1721061 2582129 := bstep (se 2 (by rfl) ⟨968298, by rfl⟩ : syracuseStep 2582129 = 1936597) B1936597
theorem B1721971 : Blo 1721061 1721971 := bstep (se 1 (by rfl) ⟨1291478, by rfl⟩ : syracuseStep 1721971 = 2582957) B2582957
theorem B2582147 : Blo 1721061 2582147 := bstep (se 1 (by rfl) ⟨1936610, by rfl⟩ : syracuseStep 2582147 = 3873221) B3873221
theorem B1721987 : Blo 1721061 1721987 := bstep (se 1 (by rfl) ⟨1291490, by rfl⟩ : syracuseStep 1721987 = 2582981) B2582981
theorem B5809805 : Blo 1721061 5809805 := bstep (se 3 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 5809805 = 2178677) B2178677
theorem B16557709 : Blo 1721061 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B3876497 : Blo 1721061 3876497 := bstep (se 2 (by rfl) ⟨1453686, by rfl⟩ : syracuseStep 3876497 = 2907373) B2907373
theorem B1722003 : Blo 1721061 1722003 := bstep (se 1 (by rfl) ⟨1291502, by rfl⟩ : syracuseStep 1722003 = 2583005) B2583005
theorem B2582177 : Blo 1721061 2582177 := bstep (se 2 (by rfl) ⟨968316, by rfl⟩ : syracuseStep 2582177 = 1936633) B1936633
theorem B1722019 : Blo 1721061 1722019 := bstep (se 1 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 1722019 = 2583029) B2583029
theorem B3876515 : Blo 1721061 3876515 := bstep (se 1 (by rfl) ⟨2907386, by rfl⟩ : syracuseStep 3876515 = 5814773) B5814773
theorem B2582195 : Blo 1721061 2582195 := bstep (se 1 (by rfl) ⟨1936646, by rfl⟩ : syracuseStep 2582195 = 3873293) B3873293
theorem B1722035 : Blo 1721061 1722035 := bstep (se 1 (by rfl) ⟨1291526, by rfl⟩ : syracuseStep 1722035 = 2583053) B2583053
theorem B5809859 : Blo 1721061 5809859 := bstep (se 1 (by rfl) ⟨4357394, by rfl⟩ : syracuseStep 5809859 = 8714789) B8714789
theorem B1722051 : Blo 1721061 1722051 := bstep (se 1 (by rfl) ⟨1291538, by rfl⟩ : syracuseStep 1722051 = 2583077) B2583077
theorem B8718029 : Blo 1721061 8718029 := bstep (se 3 (by rfl) ⟨1634630, by rfl⟩ : syracuseStep 8718029 = 3269261) B3269261
theorem B2582225 : Blo 1721061 2582225 := bstep (se 2 (by rfl) ⟨968334, by rfl⟩ : syracuseStep 2582225 = 1936669) B1936669
theorem B1722067 : Blo 1721061 1722067 := bstep (se 1 (by rfl) ⟨1291550, by rfl⟩ : syracuseStep 1722067 = 2583101) B2583101
theorem B2582243 : Blo 1721061 2582243 := bstep (se 1 (by rfl) ⟨1936682, by rfl⟩ : syracuseStep 2582243 = 3873365) B3873365
theorem B1722083 : Blo 1721061 1722083 := bstep (se 1 (by rfl) ⟨1291562, by rfl⟩ : syracuseStep 1722083 = 2583125) B2583125
theorem B9807601 : Blo 1721061 9807601 := bstep (se 2 (by rfl) ⟨3677850, by rfl⟩ : syracuseStep 9807601 = 7355701) B7355701
theorem B3270385 : Blo 1721061 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B1722099 : Blo 1721061 1722099 := bstep (se 1 (by rfl) ⟨1291574, by rfl⟩ : syracuseStep 1722099 = 2583149) B2583149
theorem B2582273 : Blo 1721061 2582273 := bstep (se 2 (by rfl) ⟨968352, by rfl⟩ : syracuseStep 2582273 = 1936705) B1936705
theorem B1722115 : Blo 1721061 1722115 := bstep (se 1 (by rfl) ⟨1291586, by rfl⟩ : syracuseStep 1722115 = 2583173) B2583173
theorem B2451217 : Blo 1721061 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B2582291 : Blo 1721061 2582291 := bstep (se 1 (by rfl) ⟨1936718, by rfl⟩ : syracuseStep 2582291 = 3873437) B3873437
theorem B1722131 : Blo 1721061 1722131 := bstep (se 1 (by rfl) ⟨1291598, by rfl⟩ : syracuseStep 1722131 = 2583197) B2583197
theorem B1722147 : Blo 1721061 1722147 := bstep (se 1 (by rfl) ⟨1291610, by rfl⟩ : syracuseStep 1722147 = 2583221) B2583221
theorem B2582321 : Blo 1721061 2582321 := bstep (se 2 (by rfl) ⟨968370, by rfl⟩ : syracuseStep 2582321 = 1936741) B1936741
theorem B1722163 : Blo 1721061 1722163 := bstep (se 1 (by rfl) ⟨1291622, by rfl⟩ : syracuseStep 1722163 = 2583245) B2583245
theorem B2582339 : Blo 1721061 2582339 := bstep (se 1 (by rfl) ⟨1936754, by rfl⟩ : syracuseStep 2582339 = 3873509) B3873509
theorem B1722179 : Blo 1721061 1722179 := bstep (se 1 (by rfl) ⟨1291634, by rfl⟩ : syracuseStep 1722179 = 2583269) B2583269
theorem B1722195 : Blo 1721061 1722195 := bstep (se 1 (by rfl) ⟨1291646, by rfl⟩ : syracuseStep 1722195 = 2583293) B2583293
theorem B2582369 : Blo 1721061 2582369 := bstep (se 2 (by rfl) ⟨968388, by rfl⟩ : syracuseStep 2582369 = 1936777) B1936777
theorem B1722211 : Blo 1721061 1722211 := bstep (se 1 (by rfl) ⟨1291658, by rfl⟩ : syracuseStep 1722211 = 2583317) B2583317
theorem B6203249 : Blo 1721061 6203249 := bstep (se 2 (by rfl) ⟨2326218, by rfl⟩ : syracuseStep 6203249 = 4652437) B4652437
theorem B2582387 : Blo 1721061 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B1722227 : Blo 1721061 1722227 := bstep (se 1 (by rfl) ⟨1291670, by rfl⟩ : syracuseStep 1722227 = 2583341) B2583341
theorem B2451331 : Blo 1721061 2451331 := bstep (se 1 (by rfl) ⟨1838498, by rfl⟩ : syracuseStep 2451331 = 3676997) B3676997
theorem B1722243 : Blo 1721061 1722243 := bstep (se 1 (by rfl) ⟨1291682, by rfl⟩ : syracuseStep 1722243 = 2583365) B2583365
theorem B2582417 : Blo 1721061 2582417 := bstep (se 2 (by rfl) ⟨968406, by rfl⟩ : syracuseStep 2582417 = 1936813) B1936813
theorem B1722259 : Blo 1721061 1722259 := bstep (se 1 (by rfl) ⟨1291694, by rfl⟩ : syracuseStep 1722259 = 2583389) B2583389
theorem B2582435 : Blo 1721061 2582435 := bstep (se 1 (by rfl) ⟨1936826, by rfl⟩ : syracuseStep 2582435 = 3873653) B3873653
theorem B1722275 : Blo 1721061 1722275 := bstep (se 1 (by rfl) ⟨1291706, by rfl⟩ : syracuseStep 1722275 = 2583413) B2583413
theorem B3876785 : Blo 1721061 3876785 := bstep (se 2 (by rfl) ⟨1453794, by rfl⟩ : syracuseStep 3876785 = 2907589) B2907589
theorem B1722291 : Blo 1721061 1722291 := bstep (se 1 (by rfl) ⟨1291718, by rfl⟩ : syracuseStep 1722291 = 2583437) B2583437
theorem B2582465 : Blo 1721061 2582465 := bstep (se 2 (by rfl) ⟨968424, by rfl⟩ : syracuseStep 2582465 = 1936849) B1936849
theorem B1722307 : Blo 1721061 1722307 := bstep (se 1 (by rfl) ⟨1291730, by rfl⟩ : syracuseStep 1722307 = 2583461) B2583461
theorem B3876803 : Blo 1721061 3876803 := bstep (se 1 (by rfl) ⟨2907602, by rfl⟩ : syracuseStep 3876803 = 5815205) B5815205
theorem B5810129 : Blo 1721061 5810129 := bstep (se 2 (by rfl) ⟨2178798, by rfl⟩ : syracuseStep 5810129 = 4357597) B4357597
theorem B2582483 : Blo 1721061 2582483 := bstep (se 1 (by rfl) ⟨1936862, by rfl⟩ : syracuseStep 2582483 = 3873725) B3873725
theorem B1722323 : Blo 1721061 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B1722339 : Blo 1721061 1722339 := bstep (se 1 (by rfl) ⟨1291754, by rfl⟩ : syracuseStep 1722339 = 2583509) B2583509
theorem B7358435 : Blo 1721061 7358435 := bstep (se 1 (by rfl) ⟨5518826, by rfl⟩ : syracuseStep 7358435 = 11037653) B11037653
theorem B2582513 : Blo 1721061 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B1722355 : Blo 1721061 1722355 := bstep (se 1 (by rfl) ⟨1291766, by rfl⟩ : syracuseStep 1722355 = 2583533) B2583533
theorem B2582531 : Blo 1721061 2582531 := bstep (se 1 (by rfl) ⟨1936898, by rfl⟩ : syracuseStep 2582531 = 3873797) B3873797
theorem B1722371 : Blo 1721061 1722371 := bstep (se 1 (by rfl) ⟨1291778, by rfl⟩ : syracuseStep 1722371 = 2583557) B2583557
theorem B1722387 : Blo 1721061 1722387 := bstep (se 1 (by rfl) ⟨1291790, by rfl⟩ : syracuseStep 1722387 = 2583581) B2583581
theorem B2582561 : Blo 1721061 2582561 := bstep (se 2 (by rfl) ⟨968460, by rfl⟩ : syracuseStep 2582561 = 1936921) B1936921
theorem B1722403 : Blo 1721061 1722403 := bstep (se 1 (by rfl) ⟨1291802, by rfl⟩ : syracuseStep 1722403 = 2583605) B2583605
theorem B2582579 : Blo 1721061 2582579 := bstep (se 1 (by rfl) ⟨1936934, by rfl⟩ : syracuseStep 2582579 = 3873869) B3873869
theorem B1722419 : Blo 1721061 1722419 := bstep (se 1 (by rfl) ⟨1291814, by rfl⟩ : syracuseStep 1722419 = 2583629) B2583629
theorem B1722435 : Blo 1721061 1722435 := bstep (se 1 (by rfl) ⟨1291826, by rfl⟩ : syracuseStep 1722435 = 2583653) B2583653
theorem B2582609 : Blo 1721061 2582609 := bstep (se 2 (by rfl) ⟨968478, by rfl⟩ : syracuseStep 2582609 = 1936957) B1936957
theorem B1722451 : Blo 1721061 1722451 := bstep (se 1 (by rfl) ⟨1291838, by rfl⟩ : syracuseStep 1722451 = 2583677) B2583677
theorem B2582627 : Blo 1721061 2582627 := bstep (se 1 (by rfl) ⟨1936970, by rfl⟩ : syracuseStep 2582627 = 3873941) B3873941
theorem B1722467 : Blo 1721061 1722467 := bstep (se 1 (by rfl) ⟨1291850, by rfl⟩ : syracuseStep 1722467 = 2583701) B2583701
theorem B6629489 : Blo 1721061 6629489 := bstep (se 2 (by rfl) ⟨2486058, by rfl⟩ : syracuseStep 6629489 = 4972117) B4972117
theorem B1722483 : Blo 1721061 1722483 := bstep (se 1 (by rfl) ⟨1291862, by rfl⟩ : syracuseStep 1722483 = 2583725) B2583725
theorem B2582657 : Blo 1721061 2582657 := bstep (se 2 (by rfl) ⟨968496, by rfl⟩ : syracuseStep 2582657 = 1936993) B1936993
theorem B1722499 : Blo 1721061 1722499 := bstep (se 1 (by rfl) ⟨1291874, by rfl⟩ : syracuseStep 1722499 = 2583749) B2583749
theorem B2582675 : Blo 1721061 2582675 := bstep (se 1 (by rfl) ⟨1937006, by rfl⟩ : syracuseStep 2582675 = 3874013) B3874013
theorem B1722515 : Blo 1721061 1722515 := bstep (se 1 (by rfl) ⟨1291886, by rfl⟩ : syracuseStep 1722515 = 2583773) B2583773
theorem B1722531 : Blo 1721061 1722531 := bstep (se 1 (by rfl) ⟨1291898, by rfl⟩ : syracuseStep 1722531 = 2583797) B2583797
theorem B2582705 : Blo 1721061 2582705 := bstep (se 2 (by rfl) ⟨968514, by rfl⟩ : syracuseStep 2582705 = 1937029) B1937029
theorem B1722547 : Blo 1721061 1722547 := bstep (se 1 (by rfl) ⟨1291910, by rfl⟩ : syracuseStep 1722547 = 2583821) B2583821
theorem B2582723 : Blo 1721061 2582723 := bstep (se 1 (by rfl) ⟨1937042, by rfl⟩ : syracuseStep 2582723 = 3874085) B3874085
theorem B1722563 : Blo 1721061 1722563 := bstep (se 1 (by rfl) ⟨1291922, by rfl⟩ : syracuseStep 1722563 = 2583845) B2583845
theorem B1722579 : Blo 1721061 1722579 := bstep (se 1 (by rfl) ⟨1291934, by rfl⟩ : syracuseStep 1722579 = 2583869) B2583869
theorem B2582753 : Blo 1721061 2582753 := bstep (se 2 (by rfl) ⟨968532, by rfl⟩ : syracuseStep 2582753 = 1937065) B1937065
theorem B1722595 : Blo 1721061 1722595 := bstep (se 1 (by rfl) ⟨1291946, by rfl⟩ : syracuseStep 1722595 = 2583893) B2583893
theorem B2582771 : Blo 1721061 2582771 := bstep (se 1 (by rfl) ⟨1937078, by rfl⟩ : syracuseStep 2582771 = 3874157) B3874157
theorem B1722611 : Blo 1721061 1722611 := bstep (se 1 (by rfl) ⟨1291958, by rfl⟩ : syracuseStep 1722611 = 2583917) B2583917
theorem B1722627 : Blo 1721061 1722627 := bstep (se 1 (by rfl) ⟨1291970, by rfl⟩ : syracuseStep 1722627 = 2583941) B2583941
theorem B2582801 : Blo 1721061 2582801 := bstep (se 2 (by rfl) ⟨968550, by rfl⟩ : syracuseStep 2582801 = 1937101) B1937101
theorem B1722643 : Blo 1721061 1722643 := bstep (se 1 (by rfl) ⟨1291982, by rfl⟩ : syracuseStep 1722643 = 2583965) B2583965
theorem B2582819 : Blo 1721061 2582819 := bstep (se 1 (by rfl) ⟨1937114, by rfl⟩ : syracuseStep 2582819 = 3874229) B3874229
theorem B6539555 : Blo 1721061 6539555 := bstep (se 1 (by rfl) ⟨4904666, by rfl⟩ : syracuseStep 6539555 = 9809333) B9809333
theorem B1722659 : Blo 1721061 1722659 := bstep (se 1 (by rfl) ⟨1291994, by rfl⟩ : syracuseStep 1722659 = 2583989) B2583989
theorem B1722675 : Blo 1721061 1722675 := bstep (se 1 (by rfl) ⟨1292006, by rfl⟩ : syracuseStep 1722675 = 2584013) B2584013
theorem B2582849 : Blo 1721061 2582849 := bstep (se 2 (by rfl) ⟨968568, by rfl⟩ : syracuseStep 2582849 = 1937137) B1937137
theorem B1722691 : Blo 1721061 1722691 := bstep (se 1 (by rfl) ⟨1292018, by rfl⟩ : syracuseStep 1722691 = 2584037) B2584037
theorem B2582867 : Blo 1721061 2582867 := bstep (se 1 (by rfl) ⟨1937150, by rfl⟩ : syracuseStep 2582867 = 3874301) B3874301
theorem B1722707 : Blo 1721061 1722707 := bstep (se 1 (by rfl) ⟨1292030, by rfl⟩ : syracuseStep 1722707 = 2584061) B2584061
theorem B1722723 : Blo 1721061 1722723 := bstep (se 1 (by rfl) ⟨1292042, by rfl⟩ : syracuseStep 1722723 = 2584085) B2584085
theorem B2582897 : Blo 1721061 2582897 := bstep (se 2 (by rfl) ⟨968586, by rfl⟩ : syracuseStep 2582897 = 1937173) B1937173
theorem B1722739 : Blo 1721061 1722739 := bstep (se 1 (by rfl) ⟨1292054, by rfl⟩ : syracuseStep 1722739 = 2584109) B2584109
theorem B2582915 : Blo 1721061 2582915 := bstep (se 1 (by rfl) ⟨1937186, by rfl⟩ : syracuseStep 2582915 = 3874373) B3874373
theorem B1722755 : Blo 1721061 1722755 := bstep (se 1 (by rfl) ⟨1292066, by rfl⟩ : syracuseStep 1722755 = 2584133) B2584133
theorem B1722771 : Blo 1721061 1722771 := bstep (se 1 (by rfl) ⟨1292078, by rfl⟩ : syracuseStep 1722771 = 2584157) B2584157
theorem B2582945 : Blo 1721061 2582945 := bstep (se 2 (by rfl) ⟨968604, by rfl⟩ : syracuseStep 2582945 = 1937209) B1937209
theorem B1722787 : Blo 1721061 1722787 := bstep (se 1 (by rfl) ⟨1292090, by rfl⟩ : syracuseStep 1722787 = 2584181) B2584181
theorem B4360625 : Blo 1721061 4360625 := bstep (se 2 (by rfl) ⟨1635234, by rfl⟩ : syracuseStep 4360625 = 3270469) B3270469
theorem B2582963 : Blo 1721061 2582963 := bstep (se 1 (by rfl) ⟨1937222, by rfl⟩ : syracuseStep 2582963 = 3874445) B3874445
theorem B1722803 : Blo 1721061 1722803 := bstep (se 1 (by rfl) ⟨1292102, by rfl⟩ : syracuseStep 1722803 = 2584205) B2584205
theorem B1722819 : Blo 1721061 1722819 := bstep (se 1 (by rfl) ⟨1292114, by rfl⟩ : syracuseStep 1722819 = 2584229) B2584229
theorem B2582993 : Blo 1721061 2582993 := bstep (se 2 (by rfl) ⟨968622, by rfl⟩ : syracuseStep 2582993 = 1937245) B1937245
theorem B1722835 : Blo 1721061 1722835 := bstep (se 1 (by rfl) ⟨1292126, by rfl⟩ : syracuseStep 1722835 = 2584253) B2584253
theorem B2583011 : Blo 1721061 2583011 := bstep (se 1 (by rfl) ⟨1937258, by rfl⟩ : syracuseStep 2583011 = 3874517) B3874517
theorem B4360675 : Blo 1721061 4360675 := bstep (se 1 (by rfl) ⟨3270506, by rfl⟩ : syracuseStep 4360675 = 6541013) B6541013
theorem B1722851 : Blo 1721061 1722851 := bstep (se 1 (by rfl) ⟨1292138, by rfl⟩ : syracuseStep 1722851 = 2584277) B2584277
theorem B5810669 : Blo 1721061 5810669 := bstep (se 3 (by rfl) ⟨1089500, by rfl⟩ : syracuseStep 5810669 = 2179001) B2179001
theorem B1722867 : Blo 1721061 1722867 := bstep (se 1 (by rfl) ⟨1292150, by rfl⟩ : syracuseStep 1722867 = 2584301) B2584301
theorem B2583041 : Blo 1721061 2583041 := bstep (se 2 (by rfl) ⟨968640, by rfl⟩ : syracuseStep 2583041 = 1937281) B1937281
theorem B1722883 : Blo 1721061 1722883 := bstep (se 1 (by rfl) ⟨1292162, by rfl⟩ : syracuseStep 1722883 = 2584325) B2584325
theorem B10471949 : Blo 1721061 10471949 := bstep (se 3 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 10471949 = 3926981) B3926981
theorem B2583059 : Blo 1721061 2583059 := bstep (se 1 (by rfl) ⟨1937294, by rfl⟩ : syracuseStep 2583059 = 3874589) B3874589
theorem B1722899 : Blo 1721061 1722899 := bstep (se 1 (by rfl) ⟨1292174, by rfl⟩ : syracuseStep 1722899 = 2584349) B2584349
theorem B5810723 : Blo 1721061 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B11782691 : Blo 1721061 11782691 := bstep (se 1 (by rfl) ⟨8837018, by rfl⟩ : syracuseStep 11782691 = 17674037) B17674037
theorem B1722915 : Blo 1721061 1722915 := bstep (se 1 (by rfl) ⟨1292186, by rfl⟩ : syracuseStep 1722915 = 2584373) B2584373
theorem B2583089 : Blo 1721061 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B1722931 : Blo 1721061 1722931 := bstep (se 1 (by rfl) ⟨1292198, by rfl⟩ : syracuseStep 1722931 = 2584397) B2584397
theorem B2583107 : Blo 1721061 2583107 := bstep (se 1 (by rfl) ⟨1937330, by rfl⟩ : syracuseStep 2583107 = 3874661) B3874661
theorem B1722947 : Blo 1721061 1722947 := bstep (se 1 (by rfl) ⟨1292210, by rfl⟩ : syracuseStep 1722947 = 2584421) B2584421
theorem B1722963 : Blo 1721061 1722963 := bstep (se 1 (by rfl) ⟨1292222, by rfl⟩ : syracuseStep 1722963 = 2584445) B2584445
theorem B2583137 : Blo 1721061 2583137 := bstep (se 2 (by rfl) ⟨968676, by rfl⟩ : syracuseStep 2583137 = 1937353) B1937353
theorem B1722979 : Blo 1721061 1722979 := bstep (se 1 (by rfl) ⟨1292234, by rfl⟩ : syracuseStep 1722979 = 2584469) B2584469
theorem B4360817 : Blo 1721061 4360817 := bstep (se 2 (by rfl) ⟨1635306, by rfl⟩ : syracuseStep 4360817 = 3270613) B3270613
theorem B2583155 : Blo 1721061 2583155 := bstep (se 1 (by rfl) ⟨1937366, by rfl⟩ : syracuseStep 2583155 = 3874733) B3874733
theorem B1722995 : Blo 1721061 1722995 := bstep (se 1 (by rfl) ⟨1292246, by rfl⟩ : syracuseStep 1722995 = 2584493) B2584493
theorem B1723011 : Blo 1721061 1723011 := bstep (se 1 (by rfl) ⟨1292258, by rfl⟩ : syracuseStep 1723011 = 2584517) B2584517
theorem B2583185 : Blo 1721061 2583185 := bstep (se 2 (by rfl) ⟨968694, by rfl⟩ : syracuseStep 2583185 = 1937389) B1937389
theorem B1723027 : Blo 1721061 1723027 := bstep (se 1 (by rfl) ⟨1292270, by rfl⟩ : syracuseStep 1723027 = 2584541) B2584541
theorem B2583203 : Blo 1721061 2583203 := bstep (se 1 (by rfl) ⟨1937402, by rfl⟩ : syracuseStep 2583203 = 3874805) B3874805
theorem B1723043 : Blo 1721061 1723043 := bstep (se 1 (by rfl) ⟨1292282, by rfl⟩ : syracuseStep 1723043 = 2584565) B2584565
theorem B8841905 : Blo 1721061 8841905 := bstep (se 2 (by rfl) ⟨3315714, by rfl⟩ : syracuseStep 8841905 = 6631429) B6631429
theorem B1723059 : Blo 1721061 1723059 := bstep (se 1 (by rfl) ⟨1292294, by rfl⟩ : syracuseStep 1723059 = 2584589) B2584589
theorem B2583233 : Blo 1721061 2583233 := bstep (se 2 (by rfl) ⟨968712, by rfl⟩ : syracuseStep 2583233 = 1937425) B1937425
theorem B19876549 : Blo 1721061 19876549 := bstep (se 4 (by rfl) ⟨1863426, by rfl⟩ : syracuseStep 19876549 = 3726853) B3726853
theorem B2583251 : Blo 1721061 2583251 := bstep (se 1 (by rfl) ⟨1937438, by rfl⟩ : syracuseStep 2583251 = 3874877) B3874877
theorem B4655843 : Blo 1721061 4655843 := bstep (se 1 (by rfl) ⟨3491882, by rfl⟩ : syracuseStep 4655843 = 6983765) B6983765
theorem B2583281 : Blo 1721061 2583281 := bstep (se 2 (by rfl) ⟨968730, by rfl⟩ : syracuseStep 2583281 = 1937461) B1937461
theorem B14920433 : Blo 1721061 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B2583299 : Blo 1721061 2583299 := bstep (se 1 (by rfl) ⟨1937474, by rfl⟩ : syracuseStep 2583299 = 3874949) B3874949
theorem B2583329 : Blo 1721061 2583329 := bstep (se 2 (by rfl) ⟨968748, by rfl⟩ : syracuseStep 2583329 = 1937497) B1937497
theorem B5810993 : Blo 1721061 5810993 := bstep (se 2 (by rfl) ⟨2179122, by rfl⟩ : syracuseStep 5810993 = 4358245) B4358245
theorem B2583347 : Blo 1721061 2583347 := bstep (se 1 (by rfl) ⟨1937510, by rfl⟩ : syracuseStep 2583347 = 3875021) B3875021
theorem B2583377 : Blo 1721061 2583377 := bstep (se 2 (by rfl) ⟨968766, by rfl⟩ : syracuseStep 2583377 = 1937533) B1937533
theorem B2583395 : Blo 1721061 2583395 := bstep (se 1 (by rfl) ⟨1937546, by rfl⟩ : syracuseStep 2583395 = 3875093) B3875093
theorem B2583425 : Blo 1721061 2583425 := bstep (se 2 (by rfl) ⟨968784, by rfl⟩ : syracuseStep 2583425 = 1937569) B1937569
theorem B3025795 : Blo 1721061 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B2583443 : Blo 1721061 2583443 := bstep (se 1 (by rfl) ⟨1937582, by rfl⟩ : syracuseStep 2583443 = 3875165) B3875165
theorem B1936291 : Blo 1721061 1936291 := bstep (se 1 (by rfl) ⟨1452218, by rfl⟩ : syracuseStep 1936291 = 2904437) B2904437
theorem B2583473 : Blo 1721061 2583473 := bstep (se 2 (by rfl) ⟨968802, by rfl⟩ : syracuseStep 2583473 = 1937605) B1937605
theorem B6540209 : Blo 1721061 6540209 := bstep (se 2 (by rfl) ⟨2452578, by rfl⟩ : syracuseStep 6540209 = 4905157) B4905157
theorem B2583491 : Blo 1721061 2583491 := bstep (se 1 (by rfl) ⟨1937618, by rfl⟩ : syracuseStep 2583491 = 3875237) B3875237
theorem B2583521 : Blo 1721061 2583521 := bstep (se 2 (by rfl) ⟨968820, by rfl⟩ : syracuseStep 2583521 = 1937641) B1937641
theorem B6204401 : Blo 1721061 6204401 := bstep (se 2 (by rfl) ⟨2326650, by rfl⟩ : syracuseStep 6204401 = 4653301) B4653301
theorem B2583539 : Blo 1721061 2583539 := bstep (se 1 (by rfl) ⟨1937654, by rfl⟩ : syracuseStep 2583539 = 3875309) B3875309
theorem B2583569 : Blo 1721061 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B2583587 : Blo 1721061 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B4901933 : Blo 1721061 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B1936435 : Blo 1721061 1936435 := bstep (se 1 (by rfl) ⟨1452326, by rfl⟩ : syracuseStep 1936435 = 2904653) B2904653
theorem B2583617 : Blo 1721061 2583617 := bstep (se 2 (by rfl) ⟨968856, by rfl⟩ : syracuseStep 2583617 = 1937713) B1937713
theorem B2583635 : Blo 1721061 2583635 := bstep (se 1 (by rfl) ⟨1937726, by rfl⟩ : syracuseStep 2583635 = 3875453) B3875453
theorem B2583665 : Blo 1721061 2583665 := bstep (se 2 (by rfl) ⟨968874, by rfl⟩ : syracuseStep 2583665 = 1937749) B1937749
theorem B2583683 : Blo 1721061 2583683 := bstep (se 1 (by rfl) ⟨1937762, by rfl⟩ : syracuseStep 2583683 = 3875525) B3875525
theorem B7457933 : Blo 1721061 7457933 := bstep (se 3 (by rfl) ⟨1398362, by rfl⟩ : syracuseStep 7457933 = 2796725) B2796725
theorem B2583713 : Blo 1721061 2583713 := bstep (se 2 (by rfl) ⟨968892, by rfl⟩ : syracuseStep 2583713 = 1937785) B1937785
theorem B9809059 : Blo 1721061 9809059 := bstep (se 1 (by rfl) ⟨7356794, by rfl⟩ : syracuseStep 9809059 = 14713589) B14713589
theorem B2583731 : Blo 1721061 2583731 := bstep (se 1 (by rfl) ⟨1937798, by rfl⟩ : syracuseStep 2583731 = 3875597) B3875597
theorem B1936579 : Blo 1721061 1936579 := bstep (se 1 (by rfl) ⟨1452434, by rfl⟩ : syracuseStep 1936579 = 2904869) B2904869
theorem B2452675 : Blo 1721061 2452675 := bstep (se 1 (by rfl) ⟨1839506, by rfl⟩ : syracuseStep 2452675 = 3679013) B3679013
theorem B11029709 : Blo 1721061 11029709 := bstep (se 3 (by rfl) ⟨2068070, by rfl⟩ : syracuseStep 11029709 = 4136141) B4136141
theorem B2583761 : Blo 1721061 2583761 := bstep (se 2 (by rfl) ⟨968910, by rfl⟩ : syracuseStep 2583761 = 1937821) B1937821
theorem B16542947 : Blo 1721061 16542947 := bstep (se 1 (by rfl) ⟨12407210, by rfl⟩ : syracuseStep 16542947 = 24814421) B24814421
theorem B4902115 : Blo 1721061 4902115 := bstep (se 1 (by rfl) ⟨3676586, by rfl⟩ : syracuseStep 4902115 = 7353173) B7353173
theorem B2583779 : Blo 1721061 2583779 := bstep (se 1 (by rfl) ⟨1937834, by rfl⟩ : syracuseStep 2583779 = 3875669) B3875669
theorem B2583809 : Blo 1721061 2583809 := bstep (se 2 (by rfl) ⟨968928, by rfl⟩ : syracuseStep 2583809 = 1937857) B1937857
theorem B2067715 : Blo 1721061 2067715 := bstep (se 1 (by rfl) ⟨1550786, by rfl⟩ : syracuseStep 2067715 = 3101573) B3101573
theorem B13077773 : Blo 1721061 13077773 := bstep (se 3 (by rfl) ⟨2452082, by rfl⟩ : syracuseStep 13077773 = 4904165) B4904165
theorem B2583827 : Blo 1721061 2583827 := bstep (se 1 (by rfl) ⟨1937870, by rfl⟩ : syracuseStep 2583827 = 3875741) B3875741
theorem B2583857 : Blo 1721061 2583857 := bstep (se 2 (by rfl) ⟨968946, by rfl⟩ : syracuseStep 2583857 = 1937893) B1937893
theorem B19623221 : Blo 1721061 19623221 := bstep (se 5 (by rfl) ⟨919838, by rfl⟩ : syracuseStep 19623221 = 1839677) B1839677
theorem B2583875 : Blo 1721061 2583875 := bstep (se 1 (by rfl) ⟨1937906, by rfl⟩ : syracuseStep 2583875 = 3875813) B3875813
theorem B5811533 : Blo 1721061 5811533 := bstep (se 3 (by rfl) ⟨1089662, by rfl⟩ : syracuseStep 5811533 = 2179325) B2179325
theorem B1936723 : Blo 1721061 1936723 := bstep (se 1 (by rfl) ⟨1452542, by rfl⟩ : syracuseStep 1936723 = 2905085) B2905085
theorem B2583905 : Blo 1721061 2583905 := bstep (se 2 (by rfl) ⟨968964, by rfl⟩ : syracuseStep 2583905 = 1937929) B1937929
theorem B2583923 : Blo 1721061 2583923 := bstep (se 1 (by rfl) ⟨1937942, by rfl⟩ : syracuseStep 2583923 = 3875885) B3875885
theorem B4902275 : Blo 1721061 4902275 := bstep (se 1 (by rfl) ⟨3676706, by rfl⟩ : syracuseStep 4902275 = 7353413) B7353413
theorem B2985347 : Blo 1721061 2985347 := bstep (se 1 (by rfl) ⟨2239010, by rfl⟩ : syracuseStep 2985347 = 4478021) B4478021
theorem B5811587 : Blo 1721061 5811587 := bstep (se 1 (by rfl) ⟨4358690, by rfl⟩ : syracuseStep 5811587 = 8717381) B8717381
theorem B2583953 : Blo 1721061 2583953 := bstep (se 2 (by rfl) ⟨968982, by rfl⟩ : syracuseStep 2583953 = 1937965) B1937965
theorem B2583971 : Blo 1721061 2583971 := bstep (se 1 (by rfl) ⟨1937978, by rfl⟩ : syracuseStep 2583971 = 3875957) B3875957
theorem B2584001 : Blo 1721061 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B2584019 : Blo 1721061 2584019 := bstep (se 1 (by rfl) ⟨1938014, by rfl⟩ : syracuseStep 2584019 = 3876029) B3876029
theorem B1936867 : Blo 1721061 1936867 := bstep (se 1 (by rfl) ⟨1452650, by rfl⟩ : syracuseStep 1936867 = 2905301) B2905301
theorem B2584049 : Blo 1721061 2584049 := bstep (se 2 (by rfl) ⟨969018, by rfl⟩ : syracuseStep 2584049 = 1938037) B1938037
theorem B2584067 : Blo 1721061 2584067 := bstep (se 1 (by rfl) ⟨1938050, by rfl⟩ : syracuseStep 2584067 = 3876101) B3876101
theorem B2584097 : Blo 1721061 2584097 := bstep (se 2 (by rfl) ⟨969036, by rfl⟩ : syracuseStep 2584097 = 1938073) B1938073
theorem B2584115 : Blo 1721061 2584115 := bstep (se 1 (by rfl) ⟨1938086, by rfl⟩ : syracuseStep 2584115 = 3876173) B3876173
theorem B2584145 : Blo 1721061 2584145 := bstep (se 2 (by rfl) ⟨969054, by rfl⟩ : syracuseStep 2584145 = 1938109) B1938109
theorem B5238371 : Blo 1721061 5238371 := bstep (se 1 (by rfl) ⟨3928778, by rfl⟩ : syracuseStep 5238371 = 7857557) B7857557
theorem B2584163 : Blo 1721061 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B1937011 : Blo 1721061 1937011 := bstep (se 1 (by rfl) ⟨1452758, by rfl⟩ : syracuseStep 1937011 = 2905517) B2905517
theorem B2584193 : Blo 1721061 2584193 := bstep (se 2 (by rfl) ⟨969072, by rfl⟩ : syracuseStep 2584193 = 1938145) B1938145
theorem B2068099 : Blo 1721061 2068099 := bstep (se 1 (by rfl) ⟨1551074, by rfl⟩ : syracuseStep 2068099 = 3102149) B3102149
theorem B5811857 : Blo 1721061 5811857 := bstep (se 2 (by rfl) ⟨2179446, by rfl⟩ : syracuseStep 5811857 = 4358893) B4358893
theorem B2584211 : Blo 1721061 2584211 := bstep (se 1 (by rfl) ⟨1938158, by rfl⟩ : syracuseStep 2584211 = 3876317) B3876317
theorem B9809585 : Blo 1721061 9809585 := bstep (se 2 (by rfl) ⟨3678594, by rfl⟩ : syracuseStep 9809585 = 7357189) B7357189
theorem B2584241 : Blo 1721061 2584241 := bstep (se 2 (by rfl) ⟨969090, by rfl⟩ : syracuseStep 2584241 = 1938181) B1938181
theorem B2584259 : Blo 1721061 2584259 := bstep (se 1 (by rfl) ⟨1938194, by rfl⟩ : syracuseStep 2584259 = 3876389) B3876389
theorem B2584289 : Blo 1721061 2584289 := bstep (se 2 (by rfl) ⟨969108, by rfl⟩ : syracuseStep 2584289 = 1938217) B1938217
theorem B1838819 : Blo 1721061 1838819 := bstep (se 1 (by rfl) ⟨1379114, by rfl⟩ : syracuseStep 1838819 = 2758229) B2758229
theorem B14708465 : Blo 1721061 14708465 := bstep (se 2 (by rfl) ⟨5515674, by rfl⟩ : syracuseStep 14708465 = 11031349) B11031349
theorem B2584307 : Blo 1721061 2584307 := bstep (se 1 (by rfl) ⟨1938230, by rfl⟩ : syracuseStep 2584307 = 3876461) B3876461
theorem B1937155 : Blo 1721061 1937155 := bstep (se 1 (by rfl) ⟨1452866, by rfl⟩ : syracuseStep 1937155 = 2905733) B2905733
theorem B2584337 : Blo 1721061 2584337 := bstep (se 2 (by rfl) ⟨969126, by rfl⟩ : syracuseStep 2584337 = 1938253) B1938253
theorem B179031829 : Blo 1721061 179031829 := bstep (se 6 (by rfl) ⟨4196058, by rfl⟩ : syracuseStep 179031829 = 8392117) B8392117
theorem B2584355 : Blo 1721061 2584355 := bstep (se 1 (by rfl) ⟨1938266, by rfl⟩ : syracuseStep 2584355 = 3876533) B3876533
theorem B2584385 : Blo 1721061 2584385 := bstep (se 2 (by rfl) ⟨969144, by rfl⟩ : syracuseStep 2584385 = 1938289) B1938289
theorem B2584403 : Blo 1721061 2584403 := bstep (se 1 (by rfl) ⟨1938302, by rfl⟩ : syracuseStep 2584403 = 3876605) B3876605
theorem B4968305 : Blo 1721061 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B2584433 : Blo 1721061 2584433 := bstep (se 2 (by rfl) ⟨969162, by rfl⟩ : syracuseStep 2584433 = 1938325) B1938325
theorem B2584451 : Blo 1721061 2584451 := bstep (se 1 (by rfl) ⟨1938338, by rfl⟩ : syracuseStep 2584451 = 3876677) B3876677
theorem B1937299 : Blo 1721061 1937299 := bstep (se 1 (by rfl) ⟨1452974, by rfl⟩ : syracuseStep 1937299 = 2905949) B2905949
theorem B2584481 : Blo 1721061 2584481 := bstep (se 2 (by rfl) ⟨969180, by rfl⟩ : syracuseStep 2584481 = 1938361) B1938361
theorem B2584499 : Blo 1721061 2584499 := bstep (se 1 (by rfl) ⟨1938374, by rfl⟩ : syracuseStep 2584499 = 3876749) B3876749
theorem B2584529 : Blo 1721061 2584529 := bstep (se 2 (by rfl) ⟨969198, by rfl⟩ : syracuseStep 2584529 = 1938397) B1938397
theorem B11186147 : Blo 1721061 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B2584547 : Blo 1721061 2584547 := bstep (se 1 (by rfl) ⟨1938410, by rfl⟩ : syracuseStep 2584547 = 3876821) B3876821
theorem B2584577 : Blo 1721061 2584577 := bstep (se 2 (by rfl) ⟨969216, by rfl⟩ : syracuseStep 2584577 = 1938433) B1938433
theorem B1937443 : Blo 1721061 1937443 := bstep (se 1 (by rfl) ⟨1453082, by rfl⟩ : syracuseStep 1937443 = 2906165) B2906165
theorem B6983729 : Blo 1721061 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B5812397 : Blo 1721061 5812397 := bstep (se 3 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 5812397 = 2179649) B2179649
theorem B1937587 : Blo 1721061 1937587 := bstep (se 1 (by rfl) ⟨1453190, by rfl⟩ : syracuseStep 1937587 = 2906381) B2906381
theorem B37761221 : Blo 1721061 37761221 := bstep (se 4 (by rfl) ⟨3540114, by rfl⟩ : syracuseStep 37761221 = 7080229) B7080229
theorem B5517521 : Blo 1721061 5517521 := bstep (se 2 (by rfl) ⟨2069070, by rfl⟩ : syracuseStep 5517521 = 4138141) B4138141
theorem B2945249 : Blo 1721061 2945249 := bstep (se 2 (by rfl) ⟨1104468, by rfl⟩ : syracuseStep 2945249 = 2208937) B2208937
theorem B5812451 : Blo 1721061 5812451 := bstep (se 1 (by rfl) ⟨4359338, by rfl⟩ : syracuseStep 5812451 = 8718677) B8718677
theorem B6205681 : Blo 1721061 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B9310469 : Blo 1721061 9310469 := bstep (se 4 (by rfl) ⟨872856, by rfl⟩ : syracuseStep 9310469 = 1745713) B1745713
theorem B2617633 : Blo 1721061 2617633 := bstep (se 2 (by rfl) ⟨981612, by rfl⟩ : syracuseStep 2617633 = 1963225) B1963225
theorem B1937731 : Blo 1721061 1937731 := bstep (se 1 (by rfl) ⟨1453298, by rfl⟩ : syracuseStep 1937731 = 2906597) B2906597
theorem B2904403 : Blo 1721061 2904403 := bstep (se 1 (by rfl) ⟨2178302, by rfl⟩ : syracuseStep 2904403 = 4356605) B4356605
theorem B6541667 : Blo 1721061 6541667 := bstep (se 1 (by rfl) ⟨4906250, by rfl⟩ : syracuseStep 6541667 = 9812501) B9812501
theorem B6541681 : Blo 1721061 6541681 := bstep (se 2 (by rfl) ⟨2453130, by rfl⟩ : syracuseStep 6541681 = 4906261) B4906261
theorem B7459235 : Blo 1721061 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4903345 : Blo 1721061 4903345 := bstep (se 2 (by rfl) ⟨1838754, by rfl⟩ : syracuseStep 4903345 = 3677509) B3677509
theorem B17912261 : Blo 1721061 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B1937875 : Blo 1721061 1937875 := bstep (se 1 (by rfl) ⟨1453406, by rfl⟩ : syracuseStep 1937875 = 2906813) B2906813
theorem B2904545 : Blo 1721061 2904545 := bstep (se 2 (by rfl) ⟨1089204, by rfl⟩ : syracuseStep 2904545 = 2178409) B2178409
theorem B26513891 : Blo 1721061 26513891 := bstep (se 1 (by rfl) ⟨19885418, by rfl⟩ : syracuseStep 26513891 = 39770837) B39770837
theorem B5812721 : Blo 1721061 5812721 := bstep (se 2 (by rfl) ⟨2179770, by rfl⟩ : syracuseStep 5812721 = 4359541) B4359541
theorem B2757107 : Blo 1721061 2757107 := bstep (se 1 (by rfl) ⟨2067830, by rfl⟩ : syracuseStep 2757107 = 4135661) B4135661
theorem B8720945 : Blo 1721061 8720945 := bstep (se 2 (by rfl) ⟨3270354, by rfl⟩ : syracuseStep 8720945 = 6540709) B6540709
theorem B2904673 : Blo 1721061 2904673 := bstep (se 2 (by rfl) ⟨1089252, by rfl⟩ : syracuseStep 2904673 = 2178505) B2178505
theorem B1938019 : Blo 1721061 1938019 := bstep (se 1 (by rfl) ⟨1453514, by rfl⟩ : syracuseStep 1938019 = 2907029) B2907029
theorem B70685297 : Blo 1721061 70685297 := bstep (se 2 (by rfl) ⟨26506986, by rfl⟩ : syracuseStep 70685297 = 53013973) B53013973
theorem B2757235 : Blo 1721061 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B2904707 : Blo 1721061 2904707 := bstep (se 1 (by rfl) ⟨2178530, by rfl⟩ : syracuseStep 2904707 = 4357061) B4357061
theorem B1839763 : Blo 1721061 1839763 := bstep (se 1 (by rfl) ⟨1379822, by rfl⟩ : syracuseStep 1839763 = 2759645) B2759645
theorem B2945713 : Blo 1721061 2945713 := bstep (se 2 (by rfl) ⟨1104642, by rfl⟩ : syracuseStep 2945713 = 2209285) B2209285
theorem B10474211 : Blo 1721061 10474211 := bstep (se 1 (by rfl) ⟨7855658, by rfl⟩ : syracuseStep 10474211 = 15711317) B15711317
theorem B1938163 : Blo 1721061 1938163 := bstep (se 1 (by rfl) ⟨1453622, by rfl⟩ : syracuseStep 1938163 = 2907245) B2907245
theorem B2757377 : Blo 1721061 2757377 := bstep (se 2 (by rfl) ⟨1034016, by rfl⟩ : syracuseStep 2757377 = 2068033) B2068033
theorem B2904835 : Blo 1721061 2904835 := bstep (se 1 (by rfl) ⟨2178626, by rfl⟩ : syracuseStep 2904835 = 4357253) B4357253
theorem B3404675 : Blo 1721061 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B5518211 : Blo 1721061 5518211 := bstep (se 1 (by rfl) ⟨4138658, by rfl⟩ : syracuseStep 5518211 = 8277317) B8277317
theorem B1938307 : Blo 1721061 1938307 := bstep (se 1 (by rfl) ⟨1453730, by rfl⟩ : syracuseStep 1938307 = 2907461) B2907461
theorem B2904977 : Blo 1721061 2904977 := bstep (se 2 (by rfl) ⟨1089366, by rfl⟩ : syracuseStep 2904977 = 2178733) B2178733
theorem B2618339 : Blo 1721061 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B5813261 : Blo 1721061 5813261 := bstep (se 3 (by rfl) ⟨1089986, by rfl⟩ : syracuseStep 5813261 = 2179973) B2179973
theorem B2905105 : Blo 1721061 2905105 := bstep (se 2 (by rfl) ⟨1089414, by rfl⟩ : syracuseStep 2905105 = 2178829) B2178829
theorem B2757665 : Blo 1721061 2757665 := bstep (se 2 (by rfl) ⟨1034124, by rfl⟩ : syracuseStep 2757665 = 2068249) B2068249
theorem B2905139 : Blo 1721061 2905139 := bstep (se 1 (by rfl) ⟨2178854, by rfl⟩ : syracuseStep 2905139 = 4357709) B4357709
theorem B5813315 : Blo 1721061 5813315 := bstep (se 1 (by rfl) ⟨4359986, by rfl⟩ : syracuseStep 5813315 = 8719973) B8719973
theorem B9811043 : Blo 1721061 9811043 := bstep (se 1 (by rfl) ⟨7358282, by rfl⟩ : syracuseStep 9811043 = 14716565) B14716565
theorem B11039885 : Blo 1721061 11039885 := bstep (se 3 (by rfl) ⟨2069978, by rfl⟩ : syracuseStep 11039885 = 4139957) B4139957
theorem B2905267 : Blo 1721061 2905267 := bstep (se 1 (by rfl) ⟨2178950, by rfl⟩ : syracuseStep 2905267 = 4357901) B4357901
theorem B3314915 : Blo 1721061 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B2905409 : Blo 1721061 2905409 := bstep (se 2 (by rfl) ⟨1089528, by rfl⟩ : syracuseStep 2905409 = 2179057) B2179057
theorem B5666129 : Blo 1721061 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B5813585 : Blo 1721061 5813585 := bstep (se 2 (by rfl) ⟨2180094, by rfl⟩ : syracuseStep 5813585 = 4360189) B4360189
theorem B10614179 : Blo 1721061 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B2905537 : Blo 1721061 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B2905571 : Blo 1721061 2905571 := bstep (se 1 (by rfl) ⟨2179178, by rfl⟩ : syracuseStep 2905571 = 4358357) B4358357
theorem B13071941 : Blo 1721061 13071941 := bstep (se 4 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 13071941 = 2450989) B2450989
theorem B2905699 : Blo 1721061 2905699 := bstep (se 1 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 2905699 = 4358549) B4358549
theorem B3675793 : Blo 1721061 3675793 := bstep (se 2 (by rfl) ⟨1378422, by rfl⟩ : syracuseStep 3675793 = 2756845) B2756845
theorem B4904621 : Blo 1721061 4904621 := bstep (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) B1839233
theorem B7354061 : Blo 1721061 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B3872465 : Blo 1721061 3872465 := bstep (se 2 (by rfl) ⟨1452174, by rfl⟩ : syracuseStep 3872465 = 2904349) B2904349
theorem B3872483 : Blo 1721061 3872483 := bstep (se 1 (by rfl) ⟨2904362, by rfl⟩ : syracuseStep 3872483 = 5808725) B5808725
theorem B7354097 : Blo 1721061 7354097 := bstep (se 2 (by rfl) ⟨2757786, by rfl⟩ : syracuseStep 7354097 = 5515573) B5515573
theorem B2905841 : Blo 1721061 2905841 := bstep (se 2 (by rfl) ⟨1089690, by rfl⟩ : syracuseStep 2905841 = 2179381) B2179381
theorem B8271629 : Blo 1721061 8271629 := bstep (se 3 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 8271629 = 3101861) B3101861
theorem B2619155 : Blo 1721061 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2758465 : Blo 1721061 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B4904803 : Blo 1721061 4904803 := bstep (se 1 (by rfl) ⟨3678602, by rfl⟩ : syracuseStep 4904803 = 7357205) B7357205
theorem B5814125 : Blo 1721061 5814125 := bstep (se 3 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 5814125 = 2180297) B2180297
theorem B2905969 : Blo 1721061 2905969 := bstep (se 2 (by rfl) ⟨1089738, by rfl⟩ : syracuseStep 2905969 = 2179477) B2179477
theorem B4904849 : Blo 1721061 4904849 := bstep (se 2 (by rfl) ⟨1839318, by rfl⟩ : syracuseStep 4904849 = 3678637) B3678637
theorem B2906003 : Blo 1721061 2906003 := bstep (se 1 (by rfl) ⟨2179502, by rfl⟩ : syracuseStep 2906003 = 4359005) B4359005
theorem B5814179 : Blo 1721061 5814179 := bstep (se 1 (by rfl) ⟨4360634, by rfl⟩ : syracuseStep 5814179 = 8721269) B8721269
theorem B8722403 : Blo 1721061 8722403 := bstep (se 1 (by rfl) ⟨6541802, by rfl⟩ : syracuseStep 8722403 = 13083605) B13083605
theorem B3872753 : Blo 1721061 3872753 := bstep (se 2 (by rfl) ⟨1452282, by rfl⟩ : syracuseStep 3872753 = 2904565) B2904565
theorem B3872771 : Blo 1721061 3872771 := bstep (se 1 (by rfl) ⟨2904578, by rfl⟩ : syracuseStep 3872771 = 5809157) B5809157
theorem B6535181 : Blo 1721061 6535181 := bstep (se 3 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 6535181 = 2450693) B2450693
theorem B2906131 : Blo 1721061 2906131 := bstep (se 1 (by rfl) ⟨2179598, by rfl⟩ : syracuseStep 2906131 = 4359197) B4359197
theorem B13080689 : Blo 1721061 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B2906273 : Blo 1721061 2906273 := bstep (se 2 (by rfl) ⟨1089852, by rfl⟩ : syracuseStep 2906273 = 2179705) B2179705
theorem B5814449 : Blo 1721061 5814449 := bstep (se 2 (by rfl) ⟨2180418, by rfl⟩ : syracuseStep 5814449 = 4360837) B4360837
theorem B3873041 : Blo 1721061 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B2906401 : Blo 1721061 2906401 := bstep (se 2 (by rfl) ⟨1089900, by rfl⟩ : syracuseStep 2906401 = 2179801) B2179801
theorem B3873059 : Blo 1721061 3873059 := bstep (se 1 (by rfl) ⟨2904794, by rfl⟩ : syracuseStep 3873059 = 5809589) B5809589
theorem B2906435 : Blo 1721061 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B12417421 : Blo 1721061 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B2906563 : Blo 1721061 2906563 := bstep (se 1 (by rfl) ⟨2179922, by rfl⟩ : syracuseStep 2906563 = 4359845) B4359845
theorem B4356625 : Blo 1721061 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B3873329 : Blo 1721061 3873329 := bstep (se 2 (by rfl) ⟨1452498, by rfl⟩ : syracuseStep 3873329 = 2904997) B2904997
theorem B3873347 : Blo 1721061 3873347 := bstep (se 1 (by rfl) ⟨2905010, by rfl⟩ : syracuseStep 3873347 = 5810021) B5810021
theorem B2906705 : Blo 1721061 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B5519981 : Blo 1721061 5519981 := bstep (se 3 (by rfl) ⟨1034996, by rfl⟩ : syracuseStep 5519981 = 2069993) B2069993
theorem B5814989 : Blo 1721061 5814989 := bstep (se 3 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 5814989 = 2180621) B2180621
theorem B2906833 : Blo 1721061 2906833 := bstep (se 2 (by rfl) ⟨1090062, by rfl⟩ : syracuseStep 2906833 = 2180125) B2180125
theorem B2906867 : Blo 1721061 2906867 := bstep (se 1 (by rfl) ⟨2180150, by rfl⟩ : syracuseStep 2906867 = 4360301) B4360301
theorem B5815043 : Blo 1721061 5815043 := bstep (se 1 (by rfl) ⟨4361282, by rfl⟩ : syracuseStep 5815043 = 8722565) B8722565
theorem B3103505 : Blo 1721061 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B4356899 : Blo 1721061 4356899 := bstep (se 1 (by rfl) ⟨3267674, by rfl⟩ : syracuseStep 4356899 = 6535349) B6535349
theorem B3873617 : Blo 1721061 3873617 := bstep (se 2 (by rfl) ⟨1452606, by rfl⟩ : syracuseStep 3873617 = 2905213) B2905213
theorem B3873635 : Blo 1721061 3873635 := bstep (se 1 (by rfl) ⟨2905226, by rfl⟩ : syracuseStep 3873635 = 5810453) B5810453
theorem B2906995 : Blo 1721061 2906995 := bstep (se 1 (by rfl) ⟨2180246, by rfl⟩ : syracuseStep 2906995 = 4360493) B4360493
theorem B9804685 : Blo 1721061 9804685 := bstep (se 3 (by rfl) ⟨1838378, by rfl⟩ : syracuseStep 9804685 = 3676757) B3676757
theorem B9812933 : Blo 1721061 9812933 := bstep (se 4 (by rfl) ⟨919962, by rfl⟩ : syracuseStep 9812933 = 1839925) B1839925
theorem B4357091 : Blo 1721061 4357091 := bstep (se 1 (by rfl) ⟨3267818, by rfl⟩ : syracuseStep 4357091 = 6535637) B6535637
theorem B2907137 : Blo 1721061 2907137 := bstep (se 2 (by rfl) ⟨1090176, by rfl⟩ : syracuseStep 2907137 = 2180353) B2180353
theorem B2759683 : Blo 1721061 2759683 := bstep (se 1 (by rfl) ⟨2069762, by rfl⟩ : syracuseStep 2759683 = 4139525) B4139525
theorem B5815313 : Blo 1721061 5815313 := bstep (se 2 (by rfl) ⟨2180742, by rfl⟩ : syracuseStep 5815313 = 4361485) B4361485
theorem B5233709 : Blo 1721061 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B4971629 : Blo 1721061 4971629 := bstep (se 3 (by rfl) ⟨932180, by rfl⟩ : syracuseStep 4971629 = 1864361) B1864361
theorem B3267697 : Blo 1721061 3267697 := bstep (se 2 (by rfl) ⟨1225386, by rfl⟩ : syracuseStep 3267697 = 2450773) B2450773
theorem B3873905 : Blo 1721061 3873905 := bstep (se 2 (by rfl) ⟨1452714, by rfl⟩ : syracuseStep 3873905 = 2905429) B2905429
theorem B2907265 : Blo 1721061 2907265 := bstep (se 2 (by rfl) ⟨1090224, by rfl⟩ : syracuseStep 2907265 = 2180449) B2180449
theorem B3873923 : Blo 1721061 3873923 := bstep (se 1 (by rfl) ⟨2905442, by rfl⟩ : syracuseStep 3873923 = 5810885) B5810885
theorem B2907299 : Blo 1721061 2907299 := bstep (se 1 (by rfl) ⟨2180474, by rfl⟩ : syracuseStep 2907299 = 4360949) B4360949
theorem B4136113 : Blo 1721061 4136113 := bstep (se 2 (by rfl) ⟨1551042, by rfl⟩ : syracuseStep 4136113 = 3102085) B3102085
theorem B9313541 : Blo 1721061 9313541 := bstep (se 4 (by rfl) ⟨873144, by rfl⟩ : syracuseStep 9313541 = 1746289) B1746289
theorem B3267857 : Blo 1721061 3267857 := bstep (se 2 (by rfl) ⟨1225446, by rfl⟩ : syracuseStep 3267857 = 2450893) B2450893
theorem B2907427 : Blo 1721061 2907427 := bstep (se 1 (by rfl) ⟨2180570, by rfl⟩ : syracuseStep 2907427 = 4361141) B4361141
theorem B4906307 : Blo 1721061 4906307 := bstep (se 1 (by rfl) ⟨3679730, by rfl⟩ : syracuseStep 4906307 = 7359461) B7359461
theorem B3874193 : Blo 1721061 3874193 := bstep (se 2 (by rfl) ⟨1452822, by rfl⟩ : syracuseStep 3874193 = 2905645) B2905645
theorem B3874211 : Blo 1721061 3874211 := bstep (se 1 (by rfl) ⟨2905658, by rfl⟩ : syracuseStep 3874211 = 5811317) B5811317
theorem B2907569 : Blo 1721061 2907569 := bstep (se 2 (by rfl) ⟨1090338, by rfl⟩ : syracuseStep 2907569 = 2180677) B2180677
theorem B2178515 : Blo 1721061 2178515 := bstep (se 1 (by rfl) ⟨1633886, by rfl⟩ : syracuseStep 2178515 = 3267773) B3267773
theorem B8715761 : Blo 1721061 8715761 := bstep (se 2 (by rfl) ⟨3268410, by rfl⟩ : syracuseStep 8715761 = 6536821) B6536821
theorem B11787889 : Blo 1721061 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B3268259 : Blo 1721061 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2358947 : Blo 1721061 2358947 := bstep (se 1 (by rfl) ⟨1769210, by rfl⟩ : syracuseStep 2358947 = 3538421) B3538421
theorem B3727025 : Blo 1721061 3727025 := bstep (se 2 (by rfl) ⟨1397634, by rfl⟩ : syracuseStep 3727025 = 2795269) B2795269
theorem B3874481 : Blo 1721061 3874481 := bstep (se 2 (by rfl) ⟨1452930, by rfl⟩ : syracuseStep 3874481 = 2905861) B2905861
theorem B3874499 : Blo 1721061 3874499 := bstep (se 1 (by rfl) ⟨2905874, by rfl⟩ : syracuseStep 3874499 = 5811749) B5811749
theorem B2359057 : Blo 1721061 2359057 := bstep (se 2 (by rfl) ⟨884646, by rfl⟩ : syracuseStep 2359057 = 1769293) B1769293
theorem B2727713 : Blo 1721061 2727713 := bstep (se 2 (by rfl) ⟨1022892, by rfl⟩ : syracuseStep 2727713 = 2045785) B2045785
theorem B1744675 : Blo 1721061 1744675 := bstep (se 1 (by rfl) ⟨1308506, by rfl⟩ : syracuseStep 1744675 = 2617013) B2617013
theorem B6209315 : Blo 1721061 6209315 := bstep (se 1 (by rfl) ⟨4656986, by rfl⟩ : syracuseStep 6209315 = 9313973) B9313973
theorem B8838989 : Blo 1721061 8838989 := bstep (se 3 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 8838989 = 3314621) B3314621
theorem B4358033 : Blo 1721061 4358033 := bstep (se 2 (by rfl) ⟨1634262, by rfl⟩ : syracuseStep 4358033 = 3268525) B3268525
theorem B8388515 : Blo 1721061 8388515 := bstep (se 1 (by rfl) ⟨6291386, by rfl⟩ : syracuseStep 8388515 = 12582773) B12582773
theorem B4358083 : Blo 1721061 4358083 := bstep (se 1 (by rfl) ⟨3268562, by rfl⟩ : syracuseStep 4358083 = 6537125) B6537125
theorem B3874769 : Blo 1721061 3874769 := bstep (se 2 (by rfl) ⟨1453038, by rfl⟩ : syracuseStep 3874769 = 2906077) B2906077
theorem B3874787 : Blo 1721061 3874787 := bstep (se 1 (by rfl) ⟨2906090, by rfl⟩ : syracuseStep 3874787 = 5812181) B5812181
theorem B3874841 : Blo 1721061 3874841 := bstep (se 2 (by rfl) ⟨1453065, by rfl⟩ : syracuseStep 3874841 = 2906131) B2906131
theorem B4358195 : Blo 1721061 4358195 := bstep (se 1 (by rfl) ⟨3268646, by rfl⟩ : syracuseStep 4358195 = 6537293) B6537293
theorem B3874931 : Blo 1721061 3874931 := bstep (se 1 (by rfl) ⟨2906198, by rfl⟩ : syracuseStep 3874931 = 5812397) B5812397
theorem B25174147 : Blo 1721061 25174147 := bstep (se 1 (by rfl) ⟨18880610, by rfl⟩ : syracuseStep 25174147 = 37761221) B37761221
theorem B3678347 : Blo 1721061 3678347 := bstep (se 1 (by rfl) ⟨2758760, by rfl⟩ : syracuseStep 3678347 = 5517521) B5517521
theorem B3874967 : Blo 1721061 3874967 := bstep (se 1 (by rfl) ⟨2906225, by rfl⟩ : syracuseStep 3874967 = 5812451) B5812451
theorem B4972823 : Blo 1721061 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B8274241 : Blo 1721061 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B3875147 : Blo 1721061 3875147 := bstep (se 1 (by rfl) ⟨2906360, by rfl⟩ : syracuseStep 3875147 = 5812721) B5812721
theorem B3876875 : Blo 1721061 3876875 := bstep (se 1 (by rfl) ⟨2907656, by rfl⟩ : syracuseStep 3876875 = 5815313) B5815313
theorem B3490177 : Blo 1721061 3490177 := bstep (se 2 (by rfl) ⟨1308816, by rfl⟩ : syracuseStep 3490177 = 2617633) B2617633
theorem B3875201 : Blo 1721061 3875201 := bstep (se 2 (by rfl) ⟨1453200, by rfl⟩ : syracuseStep 3875201 = 2906401) B2906401
theorem B2179543 : Blo 1721061 2179543 := bstep (se 1 (by rfl) ⟨1634657, by rfl⟩ : syracuseStep 2179543 = 3269315) B3269315
theorem B16556561 : Blo 1721061 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B6537779 : Blo 1721061 6537779 := bstep (se 1 (by rfl) ⟨4903334, by rfl⟩ : syracuseStep 6537779 = 9806669) B9806669
theorem B6537793 : Blo 1721061 6537793 := bstep (se 2 (by rfl) ⟨2451672, by rfl⟩ : syracuseStep 6537793 = 4903345) B4903345
theorem B4358731 : Blo 1721061 4358731 := bstep (se 1 (by rfl) ⟨3269048, by rfl⟩ : syracuseStep 4358731 = 6538097) B6538097
theorem B2269783 : Blo 1721061 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B3875417 : Blo 1721061 3875417 := bstep (se 2 (by rfl) ⟨1453281, by rfl⟩ : syracuseStep 3875417 = 2906563) B2906563
theorem B3875507 : Blo 1721061 3875507 := bstep (se 1 (by rfl) ⟨2906630, by rfl⟩ : syracuseStep 3875507 = 5813261) B5813261
theorem B5808833 : Blo 1721061 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B3875543 : Blo 1721061 3875543 := bstep (se 1 (by rfl) ⟨2906657, by rfl⟩ : syracuseStep 3875543 = 5813315) B5813315
theorem B4358873 : Blo 1721061 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B1721067 : Blo 1721061 1721067 := bstep (se 1 (by rfl) ⟨1290800, by rfl⟩ : syracuseStep 1721067 = 2581601) B2581601
theorem B1721079 : Blo 1721061 1721079 := bstep (se 1 (by rfl) ⟨1290809, by rfl⟩ : syracuseStep 1721079 = 2581619) B2581619
theorem B1721099 : Blo 1721061 1721099 := bstep (se 1 (by rfl) ⟨1290824, by rfl⟩ : syracuseStep 1721099 = 2581649) B2581649
theorem B1721111 : Blo 1721061 1721111 := bstep (se 1 (by rfl) ⟨1290833, by rfl⟩ : syracuseStep 1721111 = 2581667) B2581667
theorem B1721131 : Blo 1721061 1721131 := bstep (se 1 (by rfl) ⟨1290848, by rfl⟩ : syracuseStep 1721131 = 2581697) B2581697
theorem B1721143 : Blo 1721061 1721143 := bstep (se 1 (by rfl) ⟨1290857, by rfl⟩ : syracuseStep 1721143 = 2581715) B2581715
theorem B1721163 : Blo 1721061 1721163 := bstep (se 1 (by rfl) ⟨1290872, by rfl⟩ : syracuseStep 1721163 = 2581745) B2581745
theorem B1721175 : Blo 1721061 1721175 := bstep (se 1 (by rfl) ⟨1290881, by rfl⟩ : syracuseStep 1721175 = 2581763) B2581763
theorem B1721195 : Blo 1721061 1721195 := bstep (se 1 (by rfl) ⟨1290896, by rfl⟩ : syracuseStep 1721195 = 2581793) B2581793
theorem B1721207 : Blo 1721061 1721207 := bstep (se 1 (by rfl) ⟨1290905, by rfl⟩ : syracuseStep 1721207 = 2581811) B2581811
theorem B1721227 : Blo 1721061 1721227 := bstep (se 1 (by rfl) ⟨1290920, by rfl⟩ : syracuseStep 1721227 = 2581841) B2581841
theorem B3777419 : Blo 1721061 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B3875723 : Blo 1721061 3875723 := bstep (se 1 (by rfl) ⟨2906792, by rfl⟩ : syracuseStep 3875723 = 5813585) B5813585
theorem B1721239 : Blo 1721061 1721239 := bstep (se 1 (by rfl) ⟨1290929, by rfl⟩ : syracuseStep 1721239 = 2581859) B2581859
theorem B1721259 : Blo 1721061 1721259 := bstep (se 1 (by rfl) ⟨1290944, by rfl⟩ : syracuseStep 1721259 = 2581889) B2581889
theorem B26502065 : Blo 1721061 26502065 := bstep (se 2 (by rfl) ⟨9938274, by rfl⟩ : syracuseStep 26502065 = 19876549) B19876549
theorem B1721271 : Blo 1721061 1721271 := bstep (se 1 (by rfl) ⟨1290953, by rfl⟩ : syracuseStep 1721271 = 2581907) B2581907
theorem B3875777 : Blo 1721061 3875777 := bstep (se 2 (by rfl) ⟨1453416, by rfl⟩ : syracuseStep 3875777 = 2906833) B2906833
theorem B1721291 : Blo 1721061 1721291 := bstep (se 1 (by rfl) ⟨1290968, by rfl⟩ : syracuseStep 1721291 = 2581937) B2581937
theorem B1721303 : Blo 1721061 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B1721323 : Blo 1721061 1721323 := bstep (se 1 (by rfl) ⟨1290992, by rfl⟩ : syracuseStep 1721323 = 2581985) B2581985
theorem B1721335 : Blo 1721061 1721335 := bstep (se 1 (by rfl) ⟨1291001, by rfl⟩ : syracuseStep 1721335 = 2582003) B2582003
theorem B1721355 : Blo 1721061 1721355 := bstep (se 1 (by rfl) ⟨1291016, by rfl⟩ : syracuseStep 1721355 = 2582033) B2582033
theorem B1721367 : Blo 1721061 1721367 := bstep (se 1 (by rfl) ⟨1291025, by rfl⟩ : syracuseStep 1721367 = 2582051) B2582051
theorem B7357463 : Blo 1721061 7357463 := bstep (se 1 (by rfl) ⟨5518097, by rfl⟩ : syracuseStep 7357463 = 11036195) B11036195
theorem B1721387 : Blo 1721061 1721387 := bstep (se 1 (by rfl) ⟨1291040, by rfl⟩ : syracuseStep 1721387 = 2582081) B2582081
theorem B1721399 : Blo 1721061 1721399 := bstep (se 1 (by rfl) ⟨1291049, by rfl⟩ : syracuseStep 1721399 = 2582099) B2582099
theorem B1721419 : Blo 1721061 1721419 := bstep (se 1 (by rfl) ⟨1291064, by rfl⟩ : syracuseStep 1721419 = 2582129) B2582129
theorem B1721431 : Blo 1721061 1721431 := bstep (se 1 (by rfl) ⟨1291073, by rfl⟩ : syracuseStep 1721431 = 2582147) B2582147
theorem B1721451 : Blo 1721061 1721451 := bstep (se 1 (by rfl) ⟨1291088, by rfl⟩ : syracuseStep 1721451 = 2582177) B2582177
theorem B3269747 : Blo 1721061 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B1721463 : Blo 1721061 1721463 := bstep (se 1 (by rfl) ⟨1291097, by rfl⟩ : syracuseStep 1721463 = 2582195) B2582195
theorem B2581643 : Blo 1721061 2581643 := bstep (se 1 (by rfl) ⟨1936232, by rfl⟩ : syracuseStep 2581643 = 3872465) B3872465
theorem B1721483 : Blo 1721061 1721483 := bstep (se 1 (by rfl) ⟨1291112, by rfl⟩ : syracuseStep 1721483 = 2582225) B2582225
theorem B2581655 : Blo 1721061 2581655 := bstep (se 1 (by rfl) ⟨1936241, by rfl⟩ : syracuseStep 2581655 = 3872483) B3872483
theorem B1721495 : Blo 1721061 1721495 := bstep (se 1 (by rfl) ⟨1291121, by rfl⟩ : syracuseStep 1721495 = 2582243) B2582243
theorem B3875993 : Blo 1721061 3875993 := bstep (se 2 (by rfl) ⟨1453497, by rfl⟩ : syracuseStep 3875993 = 2906995) B2906995
theorem B1721515 : Blo 1721061 1721515 := bstep (se 1 (by rfl) ⟨1291136, by rfl⟩ : syracuseStep 1721515 = 2582273) B2582273
theorem B5514419 : Blo 1721061 5514419 := bstep (se 1 (by rfl) ⟨4135814, by rfl⟩ : syracuseStep 5514419 = 8271629) B8271629
theorem B1721527 : Blo 1721061 1721527 := bstep (se 1 (by rfl) ⟨1291145, by rfl⟩ : syracuseStep 1721527 = 2582291) B2582291
theorem B1721547 : Blo 1721061 1721547 := bstep (se 1 (by rfl) ⟨1291160, by rfl⟩ : syracuseStep 1721547 = 2582321) B2582321
theorem B1721559 : Blo 1721061 1721559 := bstep (se 1 (by rfl) ⟨1291169, by rfl⟩ : syracuseStep 1721559 = 2582339) B2582339
theorem B2581721 : Blo 1721061 2581721 := bstep (se 2 (by rfl) ⟨968145, by rfl⟩ : syracuseStep 2581721 = 1936291) B1936291
theorem B5809373 : Blo 1721061 5809373 := bstep (se 3 (by rfl) ⟨1089257, by rfl⟩ : syracuseStep 5809373 = 2178515) B2178515
theorem B1721579 : Blo 1721061 1721579 := bstep (se 1 (by rfl) ⟨1291184, by rfl⟩ : syracuseStep 1721579 = 2582369) B2582369
theorem B3876083 : Blo 1721061 3876083 := bstep (se 1 (by rfl) ⟨2907062, by rfl⟩ : syracuseStep 3876083 = 5814125) B5814125
theorem B1721591 : Blo 1721061 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B1721611 : Blo 1721061 1721611 := bstep (se 1 (by rfl) ⟨1291208, by rfl⟩ : syracuseStep 1721611 = 2582417) B2582417
theorem B3269899 : Blo 1721061 3269899 := bstep (se 1 (by rfl) ⟨2452424, by rfl⟩ : syracuseStep 3269899 = 4904849) B4904849
theorem B1721623 : Blo 1721061 1721623 := bstep (se 1 (by rfl) ⟨1291217, by rfl⟩ : syracuseStep 1721623 = 2582435) B2582435
theorem B3876119 : Blo 1721061 3876119 := bstep (se 1 (by rfl) ⟨2907089, by rfl⟩ : syracuseStep 3876119 = 5814179) B5814179
theorem B1721643 : Blo 1721061 1721643 := bstep (se 1 (by rfl) ⟨1291232, by rfl⟩ : syracuseStep 1721643 = 2582465) B2582465
theorem B1721655 : Blo 1721061 1721655 := bstep (se 1 (by rfl) ⟨1291241, by rfl⟩ : syracuseStep 1721655 = 2582483) B2582483
theorem B2581835 : Blo 1721061 2581835 := bstep (se 1 (by rfl) ⟨1936376, by rfl⟩ : syracuseStep 2581835 = 3872753) B3872753
theorem B1721675 : Blo 1721061 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B2581847 : Blo 1721061 2581847 := bstep (se 1 (by rfl) ⟨1936385, by rfl⟩ : syracuseStep 2581847 = 3872771) B3872771
theorem B1721687 : Blo 1721061 1721687 := bstep (se 1 (by rfl) ⟨1291265, by rfl⟩ : syracuseStep 1721687 = 2582531) B2582531
theorem B3679577 : Blo 1721061 3679577 := bstep (se 2 (by rfl) ⟨1379841, by rfl⟩ : syracuseStep 3679577 = 2759683) B2759683
theorem B1721707 : Blo 1721061 1721707 := bstep (se 1 (by rfl) ⟨1291280, by rfl⟩ : syracuseStep 1721707 = 2582561) B2582561
theorem B1721719 : Blo 1721061 1721719 := bstep (se 1 (by rfl) ⟨1291289, by rfl⟩ : syracuseStep 1721719 = 2582579) B2582579
theorem B1721739 : Blo 1721061 1721739 := bstep (se 1 (by rfl) ⟨1291304, by rfl⟩ : syracuseStep 1721739 = 2582609) B2582609
theorem B1721751 : Blo 1721061 1721751 := bstep (se 1 (by rfl) ⟨1291313, by rfl⟩ : syracuseStep 1721751 = 2582627) B2582627
theorem B2581913 : Blo 1721061 2581913 := bstep (se 2 (by rfl) ⟨968217, by rfl⟩ : syracuseStep 2581913 = 1936435) B1936435
theorem B1721771 : Blo 1721061 1721771 := bstep (se 1 (by rfl) ⟨1291328, by rfl⟩ : syracuseStep 1721771 = 2582657) B2582657
theorem B1721783 : Blo 1721061 1721783 := bstep (se 1 (by rfl) ⟨1291337, by rfl⟩ : syracuseStep 1721783 = 2582675) B2582675
theorem B1721803 : Blo 1721061 1721803 := bstep (se 1 (by rfl) ⟨1291352, by rfl⟩ : syracuseStep 1721803 = 2582705) B2582705
theorem B3876299 : Blo 1721061 3876299 := bstep (se 1 (by rfl) ⟨2907224, by rfl⟩ : syracuseStep 3876299 = 5814449) B5814449
theorem B1721815 : Blo 1721061 1721815 := bstep (se 1 (by rfl) ⟨1291361, by rfl⟩ : syracuseStep 1721815 = 2582723) B2582723
theorem B1721835 : Blo 1721061 1721835 := bstep (se 1 (by rfl) ⟨1291376, by rfl⟩ : syracuseStep 1721835 = 2582753) B2582753
theorem B1721847 : Blo 1721061 1721847 := bstep (se 1 (by rfl) ⟨1291385, by rfl⟩ : syracuseStep 1721847 = 2582771) B2582771
theorem B3876353 : Blo 1721061 3876353 := bstep (se 2 (by rfl) ⟨1453632, by rfl⟩ : syracuseStep 3876353 = 2907265) B2907265
theorem B2582027 : Blo 1721061 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B1721867 : Blo 1721061 1721867 := bstep (se 1 (by rfl) ⟨1291400, by rfl⟩ : syracuseStep 1721867 = 2582801) B2582801
theorem B2582039 : Blo 1721061 2582039 := bstep (se 1 (by rfl) ⟨1936529, by rfl⟩ : syracuseStep 2582039 = 3873059) B3873059
theorem B1721879 : Blo 1721061 1721879 := bstep (se 1 (by rfl) ⟨1291409, by rfl⟩ : syracuseStep 1721879 = 2582819) B2582819
theorem B4359703 : Blo 1721061 4359703 := bstep (se 1 (by rfl) ⟨3269777, by rfl⟩ : syracuseStep 4359703 = 6539555) B6539555
theorem B1721899 : Blo 1721061 1721899 := bstep (se 1 (by rfl) ⟨1291424, by rfl⟩ : syracuseStep 1721899 = 2582849) B2582849
theorem B1721911 : Blo 1721061 1721911 := bstep (se 1 (by rfl) ⟨1291433, by rfl⟩ : syracuseStep 1721911 = 2582867) B2582867
theorem B5514817 : Blo 1721061 5514817 := bstep (se 2 (by rfl) ⟨2068056, by rfl⟩ : syracuseStep 5514817 = 4136113) B4136113
theorem B1721931 : Blo 1721061 1721931 := bstep (se 1 (by rfl) ⟨1291448, by rfl⟩ : syracuseStep 1721931 = 2582897) B2582897
theorem B1721943 : Blo 1721061 1721943 := bstep (se 1 (by rfl) ⟨1291457, by rfl⟩ : syracuseStep 1721943 = 2582915) B2582915
theorem B2582105 : Blo 1721061 2582105 := bstep (se 2 (by rfl) ⟨968289, by rfl⟩ : syracuseStep 2582105 = 1936579) B1936579
theorem B3270233 : Blo 1721061 3270233 := bstep (se 2 (by rfl) ⟨1226337, by rfl⟩ : syracuseStep 3270233 = 2452675) B2452675
theorem B4654685 : Blo 1721061 4654685 := bstep (se 3 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 4654685 = 1745507) B1745507
theorem B1721963 : Blo 1721061 1721963 := bstep (se 1 (by rfl) ⟨1291472, by rfl⟩ : syracuseStep 1721963 = 2582945) B2582945
theorem B1721975 : Blo 1721061 1721975 := bstep (se 1 (by rfl) ⟨1291481, by rfl⟩ : syracuseStep 1721975 = 2582963) B2582963
theorem B1721995 : Blo 1721061 1721995 := bstep (se 1 (by rfl) ⟨1291496, by rfl⟩ : syracuseStep 1721995 = 2582993) B2582993
theorem B1722007 : Blo 1721061 1722007 := bstep (se 1 (by rfl) ⟨1291505, by rfl⟩ : syracuseStep 1722007 = 2583011) B2583011
theorem B1722027 : Blo 1721061 1722027 := bstep (se 1 (by rfl) ⟨1291520, by rfl⟩ : syracuseStep 1722027 = 2583041) B2583041
theorem B6981299 : Blo 1721061 6981299 := bstep (se 1 (by rfl) ⟨5235974, by rfl⟩ : syracuseStep 6981299 = 10471949) B10471949
theorem B1722039 : Blo 1721061 1722039 := bstep (se 1 (by rfl) ⟨1291529, by rfl⟩ : syracuseStep 1722039 = 2583059) B2583059
theorem B2582219 : Blo 1721061 2582219 := bstep (se 1 (by rfl) ⟨1936664, by rfl⟩ : syracuseStep 2582219 = 3873329) B3873329
theorem B1722059 : Blo 1721061 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B2582231 : Blo 1721061 2582231 := bstep (se 1 (by rfl) ⟨1936673, by rfl⟩ : syracuseStep 2582231 = 3873347) B3873347
theorem B1722071 : Blo 1721061 1722071 := bstep (se 1 (by rfl) ⟨1291553, by rfl⟩ : syracuseStep 1722071 = 2583107) B2583107
theorem B3876569 : Blo 1721061 3876569 := bstep (se 2 (by rfl) ⟨1453713, by rfl⟩ : syracuseStep 3876569 = 2907427) B2907427
theorem B1722091 : Blo 1721061 1722091 := bstep (se 1 (by rfl) ⟨1291568, by rfl⟩ : syracuseStep 1722091 = 2583137) B2583137
theorem B3679987 : Blo 1721061 3679987 := bstep (se 1 (by rfl) ⟨2759990, by rfl⟩ : syracuseStep 3679987 = 5519981) B5519981
theorem B1722103 : Blo 1721061 1722103 := bstep (se 1 (by rfl) ⟨1291577, by rfl⟩ : syracuseStep 1722103 = 2583155) B2583155
theorem B1722123 : Blo 1721061 1722123 := bstep (se 1 (by rfl) ⟨1291592, by rfl⟩ : syracuseStep 1722123 = 2583185) B2583185
theorem B1722135 : Blo 1721061 1722135 := bstep (se 1 (by rfl) ⟨1291601, by rfl⟩ : syracuseStep 1722135 = 2583203) B2583203
theorem B2582297 : Blo 1721061 2582297 := bstep (se 2 (by rfl) ⟨968361, by rfl⟩ : syracuseStep 2582297 = 1936723) B1936723
theorem B1722155 : Blo 1721061 1722155 := bstep (se 1 (by rfl) ⟨1291616, by rfl⟩ : syracuseStep 1722155 = 2583233) B2583233
theorem B3876659 : Blo 1721061 3876659 := bstep (se 1 (by rfl) ⟨2907494, by rfl⟩ : syracuseStep 3876659 = 5814989) B5814989
theorem B1722167 : Blo 1721061 1722167 := bstep (se 1 (by rfl) ⟨1291625, by rfl⟩ : syracuseStep 1722167 = 2583251) B2583251
theorem B1722187 : Blo 1721061 1722187 := bstep (se 1 (by rfl) ⟨1291640, by rfl⟩ : syracuseStep 1722187 = 2583281) B2583281
theorem B9946955 : Blo 1721061 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B1722199 : Blo 1721061 1722199 := bstep (se 1 (by rfl) ⟨1291649, by rfl⟩ : syracuseStep 1722199 = 2583299) B2583299
theorem B3876695 : Blo 1721061 3876695 := bstep (se 1 (by rfl) ⟨2907521, by rfl⟩ : syracuseStep 3876695 = 5815043) B5815043
theorem B1722219 : Blo 1721061 1722219 := bstep (se 1 (by rfl) ⟨1291664, by rfl⟩ : syracuseStep 1722219 = 2583329) B2583329
theorem B1722231 : Blo 1721061 1722231 := bstep (se 1 (by rfl) ⟨1291673, by rfl⟩ : syracuseStep 1722231 = 2583347) B2583347
theorem B2582411 : Blo 1721061 2582411 := bstep (se 1 (by rfl) ⟨1936808, by rfl⟩ : syracuseStep 2582411 = 3873617) B3873617
theorem B1722251 : Blo 1721061 1722251 := bstep (se 1 (by rfl) ⟨1291688, by rfl⟩ : syracuseStep 1722251 = 2583377) B2583377
theorem B2582423 : Blo 1721061 2582423 := bstep (se 1 (by rfl) ⟨1936817, by rfl⟩ : syracuseStep 2582423 = 3873635) B3873635
theorem B1722263 : Blo 1721061 1722263 := bstep (se 1 (by rfl) ⟨1291697, by rfl⟩ : syracuseStep 1722263 = 2583395) B2583395
theorem B1722283 : Blo 1721061 1722283 := bstep (se 1 (by rfl) ⟨1291712, by rfl⟩ : syracuseStep 1722283 = 2583425) B2583425
theorem B1722295 : Blo 1721061 1722295 := bstep (se 1 (by rfl) ⟨1291721, by rfl⟩ : syracuseStep 1722295 = 2583443) B2583443
theorem B1722315 : Blo 1721061 1722315 := bstep (se 1 (by rfl) ⟨1291736, by rfl⟩ : syracuseStep 1722315 = 2583473) B2583473
theorem B4360139 : Blo 1721061 4360139 := bstep (se 1 (by rfl) ⟨3270104, by rfl⟩ : syracuseStep 4360139 = 6540209) B6540209
theorem B1722327 : Blo 1721061 1722327 := bstep (se 1 (by rfl) ⟨1291745, by rfl⟩ : syracuseStep 1722327 = 2583491) B2583491
theorem B2582489 : Blo 1721061 2582489 := bstep (se 2 (by rfl) ⟨968433, by rfl⟩ : syracuseStep 2582489 = 1936867) B1936867
theorem B1722347 : Blo 1721061 1722347 := bstep (se 1 (by rfl) ⟨1291760, by rfl⟩ : syracuseStep 1722347 = 2583521) B2583521
theorem B1722359 : Blo 1721061 1722359 := bstep (se 1 (by rfl) ⟨1291769, by rfl⟩ : syracuseStep 1722359 = 2583539) B2583539
theorem B1722379 : Blo 1721061 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B8718353 : Blo 1721061 8718353 := bstep (se 2 (by rfl) ⟨3269382, by rfl⟩ : syracuseStep 8718353 = 6538765) B6538765
theorem B1722391 : Blo 1721061 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B1722411 : Blo 1721061 1722411 := bstep (se 1 (by rfl) ⟨1291808, by rfl⟩ : syracuseStep 1722411 = 2583617) B2583617
theorem B1722423 : Blo 1721061 1722423 := bstep (se 1 (by rfl) ⟨1291817, by rfl⟩ : syracuseStep 1722423 = 2583635) B2583635
theorem B2582603 : Blo 1721061 2582603 := bstep (se 1 (by rfl) ⟨1936952, by rfl⟩ : syracuseStep 2582603 = 3873905) B3873905
theorem B1722443 : Blo 1721061 1722443 := bstep (se 1 (by rfl) ⟨1291832, by rfl⟩ : syracuseStep 1722443 = 2583665) B2583665
theorem B2582615 : Blo 1721061 2582615 := bstep (se 1 (by rfl) ⟨1936961, by rfl⟩ : syracuseStep 2582615 = 3873923) B3873923
theorem B1722455 : Blo 1721061 1722455 := bstep (se 1 (by rfl) ⟨1291841, by rfl⟩ : syracuseStep 1722455 = 2583683) B2583683
theorem B1722475 : Blo 1721061 1722475 := bstep (se 1 (by rfl) ⟨1291856, by rfl⟩ : syracuseStep 1722475 = 2583713) B2583713
theorem B1722487 : Blo 1721061 1722487 := bstep (se 1 (by rfl) ⟨1291865, by rfl⟩ : syracuseStep 1722487 = 2583731) B2583731
theorem B1722507 : Blo 1721061 1722507 := bstep (se 1 (by rfl) ⟨1291880, by rfl⟩ : syracuseStep 1722507 = 2583761) B2583761
theorem B11028631 : Blo 1721061 11028631 := bstep (se 1 (by rfl) ⟨8271473, by rfl⟩ : syracuseStep 11028631 = 16542947) B16542947
theorem B1722519 : Blo 1721061 1722519 := bstep (se 1 (by rfl) ⟨1291889, by rfl⟩ : syracuseStep 1722519 = 2583779) B2583779
theorem B2582681 : Blo 1721061 2582681 := bstep (se 2 (by rfl) ⟨968505, by rfl⟩ : syracuseStep 2582681 = 1937011) B1937011
theorem B1722539 : Blo 1721061 1722539 := bstep (se 1 (by rfl) ⟨1291904, by rfl⟩ : syracuseStep 1722539 = 2583809) B2583809
theorem B8718515 : Blo 1721061 8718515 := bstep (se 1 (by rfl) ⟨6538886, by rfl⟩ : syracuseStep 8718515 = 13077773) B13077773
theorem B1722551 : Blo 1721061 1722551 := bstep (se 1 (by rfl) ⟨1291913, by rfl⟩ : syracuseStep 1722551 = 2583827) B2583827
theorem B4901057 : Blo 1721061 4901057 := bstep (se 2 (by rfl) ⟨1837896, by rfl⟩ : syracuseStep 4901057 = 3675793) B3675793
theorem B1722571 : Blo 1721061 1722571 := bstep (se 1 (by rfl) ⟨1291928, by rfl⟩ : syracuseStep 1722571 = 2583857) B2583857
theorem B1722583 : Blo 1721061 1722583 := bstep (se 1 (by rfl) ⟨1291937, by rfl⟩ : syracuseStep 1722583 = 2583875) B2583875
theorem B3270871 : Blo 1721061 3270871 := bstep (se 1 (by rfl) ⟨2453153, by rfl⟩ : syracuseStep 3270871 = 4906307) B4906307
theorem B1722603 : Blo 1721061 1722603 := bstep (se 1 (by rfl) ⟨1291952, by rfl⟩ : syracuseStep 1722603 = 2583905) B2583905
theorem B1722615 : Blo 1721061 1722615 := bstep (se 1 (by rfl) ⟨1291961, by rfl⟩ : syracuseStep 1722615 = 2583923) B2583923
theorem B2582795 : Blo 1721061 2582795 := bstep (se 1 (by rfl) ⟨1937096, by rfl⟩ : syracuseStep 2582795 = 3874193) B3874193
theorem B1722635 : Blo 1721061 1722635 := bstep (se 1 (by rfl) ⟨1291976, by rfl⟩ : syracuseStep 1722635 = 2583953) B2583953
theorem B2582807 : Blo 1721061 2582807 := bstep (se 1 (by rfl) ⟨1937105, by rfl⟩ : syracuseStep 2582807 = 3874211) B3874211
theorem B1722647 : Blo 1721061 1722647 := bstep (se 1 (by rfl) ⟨1291985, by rfl⟩ : syracuseStep 1722647 = 2583971) B2583971
theorem B1722667 : Blo 1721061 1722667 := bstep (se 1 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 1722667 = 2584001) B2584001
theorem B1722679 : Blo 1721061 1722679 := bstep (se 1 (by rfl) ⟨1292009, by rfl⟩ : syracuseStep 1722679 = 2584019) B2584019
theorem B13076801 : Blo 1721061 13076801 := bstep (se 2 (by rfl) ⟨4903800, by rfl⟩ : syracuseStep 13076801 = 9807601) B9807601
theorem B4360513 : Blo 1721061 4360513 := bstep (se 2 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 4360513 = 3270385) B3270385
theorem B5810507 : Blo 1721061 5810507 := bstep (se 1 (by rfl) ⟨4357880, by rfl⟩ : syracuseStep 5810507 = 8715761) B8715761
theorem B1722699 : Blo 1721061 1722699 := bstep (se 1 (by rfl) ⟨1292024, by rfl⟩ : syracuseStep 1722699 = 2584049) B2584049
theorem B1722711 : Blo 1721061 1722711 := bstep (se 1 (by rfl) ⟨1292033, by rfl⟩ : syracuseStep 1722711 = 2584067) B2584067
theorem B2582873 : Blo 1721061 2582873 := bstep (se 2 (by rfl) ⟨968577, by rfl⟩ : syracuseStep 2582873 = 1937155) B1937155
theorem B14715229 : Blo 1721061 14715229 := bstep (se 3 (by rfl) ⟨2759105, by rfl⟩ : syracuseStep 14715229 = 5518211) B5518211
theorem B1722731 : Blo 1721061 1722731 := bstep (se 1 (by rfl) ⟨1292048, by rfl⟩ : syracuseStep 1722731 = 2584097) B2584097
theorem B238709105 : Blo 1721061 238709105 := bstep (se 2 (by rfl) ⟨89515914, by rfl⟩ : syracuseStep 238709105 = 179031829) B179031829
theorem B1722743 : Blo 1721061 1722743 := bstep (se 1 (by rfl) ⟨1292057, by rfl⟩ : syracuseStep 1722743 = 2584115) B2584115
theorem B1722763 : Blo 1721061 1722763 := bstep (se 1 (by rfl) ⟨1292072, by rfl⟩ : syracuseStep 1722763 = 2584145) B2584145
theorem B3492247 : Blo 1721061 3492247 := bstep (se 1 (by rfl) ⟨2619185, by rfl⟩ : syracuseStep 3492247 = 5238371) B5238371
theorem B1722775 : Blo 1721061 1722775 := bstep (se 1 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 1722775 = 2584163) B2584163
theorem B1722795 : Blo 1721061 1722795 := bstep (se 1 (by rfl) ⟨1292096, by rfl⟩ : syracuseStep 1722795 = 2584193) B2584193
theorem B1722807 : Blo 1721061 1722807 := bstep (se 1 (by rfl) ⟨1292105, by rfl⟩ : syracuseStep 1722807 = 2584211) B2584211
theorem B2484683 : Blo 1721061 2484683 := bstep (se 1 (by rfl) ⟨1863512, by rfl⟩ : syracuseStep 2484683 = 3727025) B3727025
theorem B2582987 : Blo 1721061 2582987 := bstep (se 1 (by rfl) ⟨1937240, by rfl⟩ : syracuseStep 2582987 = 3874481) B3874481
theorem B6539723 : Blo 1721061 6539723 := bstep (se 1 (by rfl) ⟨4904792, by rfl⟩ : syracuseStep 6539723 = 9809585) B9809585
theorem B1722827 : Blo 1721061 1722827 := bstep (se 1 (by rfl) ⟨1292120, by rfl⟩ : syracuseStep 1722827 = 2584241) B2584241
theorem B2582999 : Blo 1721061 2582999 := bstep (se 1 (by rfl) ⟨1937249, by rfl⟩ : syracuseStep 2582999 = 3874499) B3874499
theorem B1722839 : Blo 1721061 1722839 := bstep (se 1 (by rfl) ⟨1292129, by rfl⟩ : syracuseStep 1722839 = 2584259) B2584259
theorem B6539737 : Blo 1721061 6539737 := bstep (se 2 (by rfl) ⟨2452401, by rfl⟩ : syracuseStep 6539737 = 4904803) B4904803
theorem B1722859 : Blo 1721061 1722859 := bstep (se 1 (by rfl) ⟨1292144, by rfl⟩ : syracuseStep 1722859 = 2584289) B2584289
theorem B1722871 : Blo 1721061 1722871 := bstep (se 1 (by rfl) ⟨1292153, by rfl⟩ : syracuseStep 1722871 = 2584307) B2584307
theorem B1722891 : Blo 1721061 1722891 := bstep (se 1 (by rfl) ⟨1292168, by rfl⟩ : syracuseStep 1722891 = 2584337) B2584337
theorem B4139543 : Blo 1721061 4139543 := bstep (se 1 (by rfl) ⟨3104657, by rfl⟩ : syracuseStep 4139543 = 6209315) B6209315
theorem B1722903 : Blo 1721061 1722903 := bstep (se 1 (by rfl) ⟨1292177, by rfl⟩ : syracuseStep 1722903 = 2584355) B2584355
theorem B2583065 : Blo 1721061 2583065 := bstep (se 2 (by rfl) ⟨968649, by rfl⟩ : syracuseStep 2583065 = 1937299) B1937299
theorem B1722923 : Blo 1721061 1722923 := bstep (se 1 (by rfl) ⟨1292192, by rfl⟩ : syracuseStep 1722923 = 2584385) B2584385
theorem B5892659 : Blo 1721061 5892659 := bstep (se 1 (by rfl) ⟨4419494, by rfl⟩ : syracuseStep 5892659 = 8838989) B8838989
theorem B1722935 : Blo 1721061 1722935 := bstep (se 1 (by rfl) ⟨1292201, by rfl⟩ : syracuseStep 1722935 = 2584403) B2584403
theorem B3312203 : Blo 1721061 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B1722955 : Blo 1721061 1722955 := bstep (se 1 (by rfl) ⟨1292216, by rfl⟩ : syracuseStep 1722955 = 2584433) B2584433
theorem B1722967 : Blo 1721061 1722967 := bstep (se 1 (by rfl) ⟨1292225, by rfl⟩ : syracuseStep 1722967 = 2584451) B2584451
theorem B5810777 : Blo 1721061 5810777 := bstep (se 2 (by rfl) ⟨2179041, by rfl⟩ : syracuseStep 5810777 = 4358083) B4358083
theorem B6982237 : Blo 1721061 6982237 := bstep (se 3 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 6982237 = 2618339) B2618339
theorem B1722987 : Blo 1721061 1722987 := bstep (se 1 (by rfl) ⟨1292240, by rfl⟩ : syracuseStep 1722987 = 2584481) B2584481
theorem B1722999 : Blo 1721061 1722999 := bstep (se 1 (by rfl) ⟨1292249, by rfl⟩ : syracuseStep 1722999 = 2584499) B2584499
theorem B2583179 : Blo 1721061 2583179 := bstep (se 1 (by rfl) ⟨1937384, by rfl⟩ : syracuseStep 2583179 = 3874769) B3874769
theorem B1723019 : Blo 1721061 1723019 := bstep (se 1 (by rfl) ⟨1292264, by rfl⟩ : syracuseStep 1723019 = 2584529) B2584529
theorem B2583191 : Blo 1721061 2583191 := bstep (se 1 (by rfl) ⟨1937393, by rfl⟩ : syracuseStep 2583191 = 3874787) B3874787
theorem B7457431 : Blo 1721061 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B1723031 : Blo 1721061 1723031 := bstep (se 1 (by rfl) ⟨1292273, by rfl⟩ : syracuseStep 1723031 = 2584547) B2584547
theorem B1723051 : Blo 1721061 1723051 := bstep (se 1 (by rfl) ⟨1292288, by rfl⟩ : syracuseStep 1723051 = 2584577) B2584577
theorem B4655819 : Blo 1721061 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B2583257 : Blo 1721061 2583257 := bstep (se 2 (by rfl) ⟨968721, by rfl⟩ : syracuseStep 2583257 = 1937443) B1937443
theorem B2583371 : Blo 1721061 2583371 := bstep (se 1 (by rfl) ⟨1937528, by rfl⟩ : syracuseStep 2583371 = 3875057) B3875057
theorem B4139851 : Blo 1721061 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B2583383 : Blo 1721061 2583383 := bstep (se 1 (by rfl) ⟨1937537, by rfl⟩ : syracuseStep 2583383 = 3875075) B3875075
theorem B4361111 : Blo 1721061 4361111 := bstep (se 1 (by rfl) ⟨3270833, by rfl⟩ : syracuseStep 4361111 = 6541667) B6541667
theorem B2583449 : Blo 1721061 2583449 := bstep (se 2 (by rfl) ⟨968793, by rfl⟩ : syracuseStep 2583449 = 1937587) B1937587
theorem B1936363 : Blo 1721061 1936363 := bstep (se 1 (by rfl) ⟨1452272, by rfl⟩ : syracuseStep 1936363 = 2904545) B2904545
theorem B1838071 : Blo 1721061 1838071 := bstep (se 1 (by rfl) ⟨1378553, by rfl⟩ : syracuseStep 1838071 = 2757107) B2757107
theorem B2583563 : Blo 1721061 2583563 := bstep (se 1 (by rfl) ⟨1937672, by rfl⟩ : syracuseStep 2583563 = 3875345) B3875345
theorem B2583575 : Blo 1721061 2583575 := bstep (se 1 (by rfl) ⟨1937681, by rfl⟩ : syracuseStep 2583575 = 3875363) B3875363
theorem B47123531 : Blo 1721061 47123531 := bstep (se 1 (by rfl) ⟨35342648, by rfl⟩ : syracuseStep 47123531 = 70685297) B70685297
theorem B1936471 : Blo 1721061 1936471 := bstep (se 1 (by rfl) ⟨1452353, by rfl⟩ : syracuseStep 1936471 = 2904707) B2904707
theorem B2583641 : Blo 1721061 2583641 := bstep (se 2 (by rfl) ⟨968865, by rfl⟩ : syracuseStep 2583641 = 1937731) B1937731
theorem B6982807 : Blo 1721061 6982807 := bstep (se 1 (by rfl) ⟨5237105, by rfl⟩ : syracuseStep 6982807 = 10474211) B10474211
theorem B1838251 : Blo 1721061 1838251 := bstep (se 1 (by rfl) ⟨1378688, by rfl⟩ : syracuseStep 1838251 = 2757377) B2757377
theorem B12414131 : Blo 1721061 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B7351499 : Blo 1721061 7351499 := bstep (se 1 (by rfl) ⟨5513624, by rfl⟩ : syracuseStep 7351499 = 11027249) B11027249
theorem B2583755 : Blo 1721061 2583755 := bstep (se 1 (by rfl) ⟨1937816, by rfl⟩ : syracuseStep 2583755 = 3875633) B3875633
theorem B2583767 : Blo 1721061 2583767 := bstep (se 1 (by rfl) ⟨1937825, by rfl⟩ : syracuseStep 2583767 = 3875651) B3875651
theorem B1936651 : Blo 1721061 1936651 := bstep (se 1 (by rfl) ⟨1452488, by rfl⟩ : syracuseStep 1936651 = 2904977) B2904977
theorem B5811479 : Blo 1721061 5811479 := bstep (se 1 (by rfl) ⟨4358609, by rfl⟩ : syracuseStep 5811479 = 8717219) B8717219
theorem B2583833 : Blo 1721061 2583833 := bstep (se 2 (by rfl) ⟨968937, by rfl⟩ : syracuseStep 2583833 = 1937875) B1937875
theorem B27913571 : Blo 1721061 27913571 := bstep (se 1 (by rfl) ⟨20935178, by rfl⟩ : syracuseStep 27913571 = 41870357) B41870357
theorem B11029861 : Blo 1721061 11029861 := bstep (se 4 (by rfl) ⟨1034049, by rfl⟩ : syracuseStep 11029861 = 2068099) B2068099
theorem B1936759 : Blo 1721061 1936759 := bstep (se 1 (by rfl) ⟨1452569, by rfl⟩ : syracuseStep 1936759 = 2905139) B2905139
theorem B2583947 : Blo 1721061 2583947 := bstep (se 1 (by rfl) ⟨1937960, by rfl⟩ : syracuseStep 2583947 = 3875921) B3875921
theorem B37219733 : Blo 1721061 37219733 := bstep (se 6 (by rfl) ⟨872337, by rfl⟩ : syracuseStep 37219733 = 1744675) B1744675
theorem B2583959 : Blo 1721061 2583959 := bstep (se 1 (by rfl) ⟨1937969, by rfl⟩ : syracuseStep 2583959 = 3875939) B3875939
theorem B6540695 : Blo 1721061 6540695 := bstep (se 1 (by rfl) ⟨4905521, by rfl⟩ : syracuseStep 6540695 = 9811043) B9811043
theorem B7359923 : Blo 1721061 7359923 := bstep (se 1 (by rfl) ⟨5519942, by rfl⟩ : syracuseStep 7359923 = 11039885) B11039885
theorem B2584025 : Blo 1721061 2584025 := bstep (se 2 (by rfl) ⟨969009, by rfl⟩ : syracuseStep 2584025 = 1938019) B1938019
theorem B2453017 : Blo 1721061 2453017 := bstep (se 2 (by rfl) ⟨919881, by rfl⟩ : syracuseStep 2453017 = 1839763) B1839763
theorem B1936939 : Blo 1721061 1936939 := bstep (se 1 (by rfl) ⟨1452704, by rfl⟩ : syracuseStep 1936939 = 2905409) B2905409
theorem B3927617 : Blo 1721061 3927617 := bstep (se 2 (by rfl) ⟨1472856, by rfl⟩ : syracuseStep 3927617 = 2945713) B2945713
theorem B2584139 : Blo 1721061 2584139 := bstep (se 1 (by rfl) ⟨1938104, by rfl⟩ : syracuseStep 2584139 = 3876209) B3876209
theorem B2584151 : Blo 1721061 2584151 := bstep (se 1 (by rfl) ⟨1938113, by rfl⟩ : syracuseStep 2584151 = 3876227) B3876227
theorem B1937047 : Blo 1721061 1937047 := bstep (se 1 (by rfl) ⟨1452785, by rfl⟩ : syracuseStep 1937047 = 2905571) B2905571
theorem B2584217 : Blo 1721061 2584217 := bstep (se 2 (by rfl) ⟨969081, by rfl⟩ : syracuseStep 2584217 = 1938163) B1938163
theorem B2584331 : Blo 1721061 2584331 := bstep (se 1 (by rfl) ⟨1938248, by rfl⟩ : syracuseStep 2584331 = 3876497) B3876497
theorem B2584343 : Blo 1721061 2584343 := bstep (se 1 (by rfl) ⟨1938257, by rfl⟩ : syracuseStep 2584343 = 3876515) B3876515
theorem B4902707 : Blo 1721061 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B5812019 : Blo 1721061 5812019 := bstep (se 1 (by rfl) ⟨4359014, by rfl⟩ : syracuseStep 5812019 = 8718029) B8718029
theorem B4902731 : Blo 1721061 4902731 := bstep (se 1 (by rfl) ⟨3677048, by rfl⟩ : syracuseStep 4902731 = 7354097) B7354097
theorem B1937227 : Blo 1721061 1937227 := bstep (se 1 (by rfl) ⟨1452920, by rfl⟩ : syracuseStep 1937227 = 2905841) B2905841
theorem B4034393 : Blo 1721061 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B2584409 : Blo 1721061 2584409 := bstep (se 2 (by rfl) ⟨969153, by rfl⟩ : syracuseStep 2584409 = 1938307) B1938307
theorem B1937335 : Blo 1721061 1937335 := bstep (se 1 (by rfl) ⟨1453001, by rfl⟩ : syracuseStep 1937335 = 2906003) B2906003
theorem B2584523 : Blo 1721061 2584523 := bstep (se 1 (by rfl) ⟨1938392, by rfl⟩ : syracuseStep 2584523 = 3876785) B3876785
theorem B2584535 : Blo 1721061 2584535 := bstep (se 1 (by rfl) ⟨1938401, by rfl⟩ : syracuseStep 2584535 = 3876803) B3876803
theorem B5812289 : Blo 1721061 5812289 := bstep (se 2 (by rfl) ⟨2179608, by rfl⟩ : syracuseStep 5812289 = 4359217) B4359217
theorem B4419659 : Blo 1721061 4419659 := bstep (se 1 (by rfl) ⟨3314744, by rfl⟩ : syracuseStep 4419659 = 6629489) B6629489
theorem B8720459 : Blo 1721061 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B9310301 : Blo 1721061 9310301 := bstep (se 3 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 9310301 = 3491363) B3491363
theorem B1937515 : Blo 1721061 1937515 := bstep (se 1 (by rfl) ⟨1453136, by rfl⟩ : syracuseStep 1937515 = 2906273) B2906273
theorem B1937623 : Blo 1721061 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B13078745 : Blo 1721061 13078745 := bstep (se 2 (by rfl) ⟨4904529, by rfl⟩ : syracuseStep 13078745 = 9809059) B9809059
theorem B2756953 : Blo 1721061 2756953 := bstep (se 2 (by rfl) ⟨1033857, by rfl⟩ : syracuseStep 2756953 = 2067715) B2067715
theorem B1937803 : Blo 1721061 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B5894603 : Blo 1721061 5894603 := bstep (se 1 (by rfl) ⟨4420952, by rfl⟩ : syracuseStep 5894603 = 8841905) B8841905
theorem B1937911 : Blo 1721061 1937911 := bstep (se 1 (by rfl) ⟨1453433, by rfl⟩ : syracuseStep 1937911 = 2906867) B2906867
theorem B2069003 : Blo 1721061 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B2904599 : Blo 1721061 2904599 := bstep (se 1 (by rfl) ⟨2178449, by rfl⟩ : syracuseStep 2904599 = 4356899) B4356899
theorem B4903517 : Blo 1721061 4903517 := bstep (se 3 (by rfl) ⟨919409, by rfl⟩ : syracuseStep 4903517 = 1838819) B1838819
theorem B5812829 : Blo 1721061 5812829 := bstep (se 3 (by rfl) ⟨1089905, by rfl⟩ : syracuseStep 5812829 = 2179811) B2179811
theorem B6541955 : Blo 1721061 6541955 := bstep (se 1 (by rfl) ⟨4906466, by rfl⟩ : syracuseStep 6541955 = 9812933) B9812933
theorem B2904727 : Blo 1721061 2904727 := bstep (se 1 (by rfl) ⟨2178545, by rfl⟩ : syracuseStep 2904727 = 4357091) B4357091
theorem B1938091 : Blo 1721061 1938091 := bstep (se 1 (by rfl) ⟨1453568, by rfl⟩ : syracuseStep 1938091 = 2907137) B2907137
theorem B6984413 : Blo 1721061 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B3314419 : Blo 1721061 3314419 := bstep (se 1 (by rfl) ⟨2485814, by rfl⟩ : syracuseStep 3314419 = 4971629) B4971629
theorem B1938199 : Blo 1721061 1938199 := bstep (se 1 (by rfl) ⟨1453649, by rfl⟩ : syracuseStep 1938199 = 2907299) B2907299
theorem B7353139 : Blo 1721061 7353139 := bstep (se 1 (by rfl) ⟨5514854, by rfl⟩ : syracuseStep 7353139 = 11029709) B11029709
theorem B15717185 : Blo 1721061 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B1938379 : Blo 1721061 1938379 := bstep (se 1 (by rfl) ⟨1453784, by rfl⟩ : syracuseStep 1938379 = 2907569) B2907569
theorem B22369373 : Blo 1721061 22369373 := bstep (se 3 (by rfl) ⟨4194257, by rfl⟩ : syracuseStep 22369373 = 8388515) B8388515
theorem B2905355 : Blo 1721061 2905355 := bstep (se 1 (by rfl) ⟨2179016, by rfl⟩ : syracuseStep 2905355 = 4358033) B4358033
theorem B2905483 : Blo 1721061 2905483 := bstep (se 1 (by rfl) ⟨2179112, by rfl⟩ : syracuseStep 2905483 = 4358225) B4358225
theorem B7353773 : Blo 1721061 7353773 := bstep (se 3 (by rfl) ⟨1378832, by rfl⟩ : syracuseStep 7353773 = 2757665) B2757665
theorem B6378955 : Blo 1721061 6378955 := bstep (se 1 (by rfl) ⟨4784216, by rfl⟩ : syracuseStep 6378955 = 9568433) B9568433
theorem B1963499 : Blo 1721061 1963499 := bstep (se 1 (by rfl) ⟨1472624, by rfl⟩ : syracuseStep 1963499 = 2945249) B2945249
theorem B2905625 : Blo 1721061 2905625 := bstep (se 2 (by rfl) ⟨1089609, by rfl⟩ : syracuseStep 2905625 = 2179219) B2179219
theorem B3102337 : Blo 1721061 3102337 := bstep (se 2 (by rfl) ⟨1163376, by rfl⟩ : syracuseStep 3102337 = 2326753) B2326753
theorem B6624899 : Blo 1721061 6624899 := bstep (se 1 (by rfl) ⟨4968674, by rfl⟩ : syracuseStep 6624899 = 9937349) B9937349
theorem B11941507 : Blo 1721061 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B17675927 : Blo 1721061 17675927 := bstep (se 1 (by rfl) ⟨13256945, by rfl⟩ : syracuseStep 17675927 = 26513891) B26513891
theorem B2905753 : Blo 1721061 2905753 := bstep (se 2 (by rfl) ⟨1089657, by rfl⟩ : syracuseStep 2905753 = 2179315) B2179315
theorem B5813963 : Blo 1721061 5813963 := bstep (se 1 (by rfl) ⟨4360472, by rfl⟩ : syracuseStep 5813963 = 8720945) B8720945
theorem B6534877 : Blo 1721061 6534877 := bstep (se 3 (by rfl) ⟨1225289, by rfl⟩ : syracuseStep 6534877 = 2450579) B2450579
theorem B3872537 : Blo 1721061 3872537 := bstep (se 2 (by rfl) ⟨1452201, by rfl⟩ : syracuseStep 3872537 = 2904403) B2904403
theorem B3675955 : Blo 1721061 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B8722241 : Blo 1721061 8722241 := bstep (se 2 (by rfl) ⟨3270840, by rfl⟩ : syracuseStep 8722241 = 6541681) B6541681
theorem B3872627 : Blo 1721061 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B3872663 : Blo 1721061 3872663 := bstep (se 1 (by rfl) ⟨2904497, by rfl⟩ : syracuseStep 3872663 = 5808995) B5808995
theorem B5814233 : Blo 1721061 5814233 := bstep (se 2 (by rfl) ⟨2180337, by rfl⟩ : syracuseStep 5814233 = 4360675) B4360675
theorem B24827917 : Blo 1721061 24827917 := bstep (se 3 (by rfl) ⟨4655234, by rfl⟩ : syracuseStep 24827917 = 9310469) B9310469
theorem B3872843 : Blo 1721061 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B3872897 : Blo 1721061 3872897 := bstep (se 2 (by rfl) ⟨1452336, by rfl⟩ : syracuseStep 3872897 = 2904673) B2904673
theorem B2209943 : Blo 1721061 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B3676313 : Blo 1721061 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B2906327 : Blo 1721061 2906327 := bstep (se 1 (by rfl) ⟨2179745, by rfl⟩ : syracuseStep 2906327 = 4359491) B4359491
theorem B31414513 : Blo 1721061 31414513 := bstep (se 2 (by rfl) ⟨11780442, by rfl⟩ : syracuseStep 31414513 = 23560885) B23560885
theorem B7076119 : Blo 1721061 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B2906455 : Blo 1721061 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B3873113 : Blo 1721061 3873113 := bstep (se 2 (by rfl) ⟨1452417, by rfl⟩ : syracuseStep 3873113 = 2904835) B2904835
theorem B4905305 : Blo 1721061 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B7960925 : Blo 1721061 7960925 := bstep (se 3 (by rfl) ⟨1492673, by rfl⟩ : syracuseStep 7960925 = 2985347) B2985347
theorem B8714627 : Blo 1721061 8714627 := bstep (se 1 (by rfl) ⟨6535970, by rfl⟩ : syracuseStep 8714627 = 13071941) B13071941
theorem B3103129 : Blo 1721061 3103129 := bstep (se 2 (by rfl) ⟨1163673, by rfl⟩ : syracuseStep 3103129 = 2327347) B2327347
theorem B3873203 : Blo 1721061 3873203 := bstep (se 1 (by rfl) ⟨2904902, by rfl⟩ : syracuseStep 3873203 = 5809805) B5809805
theorem B3873239 : Blo 1721061 3873239 := bstep (se 1 (by rfl) ⟨2904929, by rfl⟩ : syracuseStep 3873239 = 5809859) B5809859
theorem B14703065 : Blo 1721061 14703065 := bstep (se 2 (by rfl) ⟨5513649, by rfl⟩ : syracuseStep 14703065 = 11027299) B11027299
theorem B13072913 : Blo 1721061 13072913 := bstep (se 2 (by rfl) ⟨4902342, by rfl⟩ : syracuseStep 13072913 = 9804685) B9804685
theorem B4135499 : Blo 1721061 4135499 := bstep (se 1 (by rfl) ⟨3101624, by rfl⟩ : syracuseStep 4135499 = 6203249) B6203249
theorem B3873419 : Blo 1721061 3873419 := bstep (se 1 (by rfl) ⟨2905064, by rfl⟩ : syracuseStep 3873419 = 5810129) B5810129
theorem B4905623 : Blo 1721061 4905623 := bstep (se 1 (by rfl) ⟨3679217, by rfl⟩ : syracuseStep 4905623 = 7358435) B7358435
theorem B5814935 : Blo 1721061 5814935 := bstep (se 1 (by rfl) ⟨4361201, by rfl⟩ : syracuseStep 5814935 = 8722403) B8722403
theorem B4356787 : Blo 1721061 4356787 := bstep (se 1 (by rfl) ⟨3267590, by rfl⟩ : syracuseStep 4356787 = 6535181) B6535181
theorem B3873473 : Blo 1721061 3873473 := bstep (se 2 (by rfl) ⟨1452552, by rfl⟩ : syracuseStep 3873473 = 2905105) B2905105
theorem B44718797 : Blo 1721061 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B4356929 : Blo 1721061 4356929 := bstep (se 2 (by rfl) ⟨1633848, by rfl⟩ : syracuseStep 4356929 = 3267697) B3267697
theorem B3873689 : Blo 1721061 3873689 := bstep (se 2 (by rfl) ⟨1452633, by rfl⟩ : syracuseStep 3873689 = 2905267) B2905267
theorem B2907083 : Blo 1721061 2907083 := bstep (se 1 (by rfl) ⟨2180312, by rfl⟩ : syracuseStep 2907083 = 4360625) B4360625
theorem B6536153 : Blo 1721061 6536153 := bstep (se 2 (by rfl) ⟨2451057, by rfl⟩ : syracuseStep 6536153 = 4902115) B4902115
theorem B3873779 : Blo 1721061 3873779 := bstep (se 1 (by rfl) ⟨2905334, by rfl⟩ : syracuseStep 3873779 = 5810669) B5810669
theorem B14711813 : Blo 1721061 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B3873815 : Blo 1721061 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B7855127 : Blo 1721061 7855127 := bstep (se 1 (by rfl) ⟨5891345, by rfl⟩ : syracuseStep 7855127 = 11782691) B11782691
theorem B2907211 : Blo 1721061 2907211 := bstep (se 1 (by rfl) ⟨2180408, by rfl⟩ : syracuseStep 2907211 = 4360817) B4360817
theorem B6290525 : Blo 1721061 6290525 := bstep (se 3 (by rfl) ⟨1179473, by rfl⟩ : syracuseStep 6290525 = 2358947) B2358947
theorem B3103895 : Blo 1721061 3103895 := bstep (se 1 (by rfl) ⟨2327921, by rfl⟩ : syracuseStep 3103895 = 4655843) B4655843
theorem B3873995 : Blo 1721061 3873995 := bstep (se 1 (by rfl) ⟨2905496, by rfl⟩ : syracuseStep 3873995 = 5810993) B5810993
theorem B2907353 : Blo 1721061 2907353 := bstep (se 2 (by rfl) ⟨1090257, by rfl⟩ : syracuseStep 2907353 = 2180515) B2180515
theorem B3874049 : Blo 1721061 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B4136267 : Blo 1721061 4136267 := bstep (se 1 (by rfl) ⟨3102200, by rfl⟩ : syracuseStep 4136267 = 6204401) B6204401
theorem B2907481 : Blo 1721061 2907481 := bstep (se 2 (by rfl) ⟨1090305, by rfl⟩ : syracuseStep 2907481 = 2180611) B2180611
theorem B3489139 : Blo 1721061 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B3267955 : Blo 1721061 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B7273901 : Blo 1721061 7273901 := bstep (se 3 (by rfl) ⟨1363856, by rfl⟩ : syracuseStep 7273901 = 2727713) B2727713
theorem B4971955 : Blo 1721061 4971955 := bstep (se 1 (by rfl) ⟨3728966, by rfl⟩ : syracuseStep 4971955 = 7457933) B7457933
theorem B4906433 : Blo 1721061 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B3874265 : Blo 1721061 3874265 := bstep (se 2 (by rfl) ⟨1452849, by rfl⟩ : syracuseStep 3874265 = 2905699) B2905699
theorem B6209027 : Blo 1721061 6209027 := bstep (se 1 (by rfl) ⟨4656770, by rfl⟩ : syracuseStep 6209027 = 9313541) B9313541
theorem B2178571 : Blo 1721061 2178571 := bstep (se 1 (by rfl) ⟨1633928, by rfl⟩ : syracuseStep 2178571 = 3267857) B3267857
theorem B22076945 : Blo 1721061 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B13082147 : Blo 1721061 13082147 := bstep (se 1 (by rfl) ⟨9811610, by rfl⟩ : syracuseStep 13082147 = 19623221) B19623221
theorem B3874355 : Blo 1721061 3874355 := bstep (se 1 (by rfl) ⟨2905766, by rfl⟩ : syracuseStep 3874355 = 5811533) B5811533
theorem B3268183 : Blo 1721061 3268183 := bstep (se 1 (by rfl) ⟨2451137, by rfl⟩ : syracuseStep 3268183 = 4902275) B4902275
theorem B3874391 : Blo 1721061 3874391 := bstep (se 1 (by rfl) ⟨2905793, by rfl⟩ : syracuseStep 3874391 = 5811587) B5811587
theorem B3268289 : Blo 1721061 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B3145409 : Blo 1721061 3145409 := bstep (se 2 (by rfl) ⟨1179528, by rfl⟩ : syracuseStep 3145409 = 2359057) B2359057
theorem B3874571 : Blo 1721061 3874571 := bstep (se 1 (by rfl) ⟨2905928, by rfl⟩ : syracuseStep 3874571 = 5811857) B5811857
theorem B2178839 : Blo 1721061 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B3874625 : Blo 1721061 3874625 := bstep (se 2 (by rfl) ⟨1452984, by rfl⟩ : syracuseStep 3874625 = 2905969) B2905969
theorem B9805643 : Blo 1721061 9805643 := bstep (se 1 (by rfl) ⟨7354232, by rfl⟩ : syracuseStep 9805643 = 14708465) B14708465
theorem B3268441 : Blo 1721061 3268441 := bstep (se 2 (by rfl) ⟨1225665, by rfl⟩ : syracuseStep 3268441 = 2451331) B2451331
theorem B33103889 : Blo 1721061 33103889 := bstep (se 2 (by rfl) ⟨12413958, by rfl⟩ : syracuseStep 33103889 = 24827917) B24827917
theorem B3874859 : Blo 1721061 3874859 := bstep (se 1 (by rfl) ⟨2906144, by rfl⟩ : syracuseStep 3874859 = 5812289) B5812289
theorem B14704841 : Blo 1721061 14704841 := bstep (se 2 (by rfl) ⟨5514315, by rfl⟩ : syracuseStep 14704841 = 11028631) B11028631
theorem B41886017 : Blo 1721061 41886017 := bstep (se 2 (by rfl) ⟨15707256, by rfl⟩ : syracuseStep 41886017 = 31414513) B31414513
theorem B4358519 : Blo 1721061 4358519 := bstep (se 1 (by rfl) ⟨3268889, by rfl⟩ : syracuseStep 4358519 = 6537779) B6537779
theorem B3269011 : Blo 1721061 3269011 := bstep (se 1 (by rfl) ⟨2451758, by rfl⟩ : syracuseStep 3269011 = 4903517) B4903517
theorem B3875219 : Blo 1721061 3875219 := bstep (se 1 (by rfl) ⟨2906414, by rfl⟩ : syracuseStep 3875219 = 5812829) B5812829
theorem B3875273 : Blo 1721061 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B19620305 : Blo 1721061 19620305 := bstep (se 2 (by rfl) ⟨7357614, by rfl⟩ : syracuseStep 19620305 = 14715229) B14715229
theorem B4653569 : Blo 1721061 4653569 := bstep (se 2 (by rfl) ⟨1745088, by rfl⟩ : syracuseStep 4653569 = 3490177) B3490177
theorem B10478123 : Blo 1721061 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B8717057 : Blo 1721061 8717057 := bstep (se 2 (by rfl) ⟨3268896, by rfl⟩ : syracuseStep 8717057 = 6537793) B6537793
theorem B1721095 : Blo 1721061 1721095 := bstep (se 1 (by rfl) ⟨1290821, by rfl⟩ : syracuseStep 1721095 = 2581643) B2581643
theorem B1721103 : Blo 1721061 1721103 := bstep (se 1 (by rfl) ⟨1290827, by rfl⟩ : syracuseStep 1721103 = 2581655) B2581655
theorem B1721147 : Blo 1721061 1721147 := bstep (se 1 (by rfl) ⟨1290860, by rfl⟩ : syracuseStep 1721147 = 2581721) B2581721
theorem B1721223 : Blo 1721061 1721223 := bstep (se 1 (by rfl) ⟨1290917, by rfl⟩ : syracuseStep 1721223 = 2581835) B2581835
theorem B1721231 : Blo 1721061 1721231 := bstep (se 1 (by rfl) ⟨1290923, by rfl⟩ : syracuseStep 1721231 = 2581847) B2581847
theorem B5809049 : Blo 1721061 5809049 := bstep (se 2 (by rfl) ⟨2178393, by rfl⟩ : syracuseStep 5809049 = 4356787) B4356787
theorem B1721275 : Blo 1721061 1721275 := bstep (se 1 (by rfl) ⟨1290956, by rfl⟩ : syracuseStep 1721275 = 2581913) B2581913
theorem B1721351 : Blo 1721061 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B1721359 : Blo 1721061 1721359 := bstep (se 1 (by rfl) ⟨1291019, by rfl⟩ : syracuseStep 1721359 = 2582039) B2582039
theorem B1721403 : Blo 1721061 1721403 := bstep (se 1 (by rfl) ⟨1291052, by rfl⟩ : syracuseStep 1721403 = 2582105) B2582105
theorem B4416599 : Blo 1721061 4416599 := bstep (se 1 (by rfl) ⟨3312449, by rfl⟩ : syracuseStep 4416599 = 6624899) B6624899
theorem B4654199 : Blo 1721061 4654199 := bstep (se 1 (by rfl) ⟨3490649, by rfl⟩ : syracuseStep 4654199 = 6981299) B6981299
theorem B1721479 : Blo 1721061 1721479 := bstep (se 1 (by rfl) ⟨1291109, by rfl⟩ : syracuseStep 1721479 = 2582219) B2582219
theorem B3875975 : Blo 1721061 3875975 := bstep (se 1 (by rfl) ⟨2906981, by rfl⟩ : syracuseStep 3875975 = 5813963) B5813963
theorem B1721487 : Blo 1721061 1721487 := bstep (se 1 (by rfl) ⟨1291115, by rfl⟩ : syracuseStep 1721487 = 2582231) B2582231
theorem B2581691 : Blo 1721061 2581691 := bstep (se 1 (by rfl) ⟨1936268, by rfl⟩ : syracuseStep 2581691 = 3872537) B3872537
theorem B1721531 : Blo 1721061 1721531 := bstep (se 1 (by rfl) ⟨1291148, by rfl⟩ : syracuseStep 1721531 = 2582297) B2582297
theorem B2581751 : Blo 1721061 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B1721607 : Blo 1721061 1721607 := bstep (se 1 (by rfl) ⟨1291205, by rfl⟩ : syracuseStep 1721607 = 2582411) B2582411
theorem B2581775 : Blo 1721061 2581775 := bstep (se 1 (by rfl) ⟨1936331, by rfl⟩ : syracuseStep 2581775 = 3872663) B3872663
theorem B1721615 : Blo 1721061 1721615 := bstep (se 1 (by rfl) ⟨1291211, by rfl⟩ : syracuseStep 1721615 = 2582423) B2582423
theorem B5235997 : Blo 1721061 5235997 := bstep (se 3 (by rfl) ⟨981749, by rfl⟩ : syracuseStep 5235997 = 1963499) B1963499
theorem B2581817 : Blo 1721061 2581817 := bstep (se 2 (by rfl) ⟨968181, by rfl⟩ : syracuseStep 2581817 = 1936363) B1936363
theorem B1721659 : Blo 1721061 1721659 := bstep (se 1 (by rfl) ⟨1291244, by rfl⟩ : syracuseStep 1721659 = 2582489) B2582489
theorem B3876155 : Blo 1721061 3876155 := bstep (se 1 (by rfl) ⟨2907116, by rfl⟩ : syracuseStep 3876155 = 5814233) B5814233
theorem B2581895 : Blo 1721061 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B1721735 : Blo 1721061 1721735 := bstep (se 1 (by rfl) ⟨1291301, by rfl⟩ : syracuseStep 1721735 = 2582603) B2582603
theorem B1721743 : Blo 1721061 1721743 := bstep (se 1 (by rfl) ⟨1291307, by rfl⟩ : syracuseStep 1721743 = 2582615) B2582615
theorem B2581931 : Blo 1721061 2581931 := bstep (se 1 (by rfl) ⟨1936448, by rfl⟩ : syracuseStep 2581931 = 3872897) B3872897
theorem B3876281 : Blo 1721061 3876281 := bstep (se 2 (by rfl) ⟨1453605, by rfl⟩ : syracuseStep 3876281 = 2907211) B2907211
theorem B1721787 : Blo 1721061 1721787 := bstep (se 1 (by rfl) ⟨1291340, by rfl⟩ : syracuseStep 1721787 = 2582681) B2582681
theorem B2581961 : Blo 1721061 2581961 := bstep (se 2 (by rfl) ⟨968235, by rfl⟩ : syracuseStep 2581961 = 1936471) B1936471
theorem B1721863 : Blo 1721061 1721863 := bstep (se 1 (by rfl) ⟨1291397, by rfl⟩ : syracuseStep 1721863 = 2582795) B2582795
theorem B1721871 : Blo 1721061 1721871 := bstep (se 1 (by rfl) ⟨1291403, by rfl⟩ : syracuseStep 1721871 = 2582807) B2582807
theorem B8717867 : Blo 1721061 8717867 := bstep (se 1 (by rfl) ⟨6538400, by rfl⟩ : syracuseStep 8717867 = 13076801) B13076801
theorem B2451001 : Blo 1721061 2451001 := bstep (se 2 (by rfl) ⟨919125, by rfl⟩ : syracuseStep 2451001 = 1838251) B1838251
theorem B2582075 : Blo 1721061 2582075 := bstep (se 1 (by rfl) ⟨1936556, by rfl⟩ : syracuseStep 2582075 = 3873113) B3873113
theorem B1721915 : Blo 1721061 1721915 := bstep (se 1 (by rfl) ⟨1291436, by rfl⟩ : syracuseStep 1721915 = 2582873) B2582873
theorem B3270203 : Blo 1721061 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B159139403 : Blo 1721061 159139403 := bstep (se 1 (by rfl) ⟨119354552, by rfl⟩ : syracuseStep 159139403 = 238709105) B238709105
theorem B5809751 : Blo 1721061 5809751 := bstep (se 1 (by rfl) ⟨4357313, by rfl⟩ : syracuseStep 5809751 = 8714627) B8714627
theorem B2582135 : Blo 1721061 2582135 := bstep (se 1 (by rfl) ⟨1936601, by rfl⟩ : syracuseStep 2582135 = 3873203) B3873203
theorem B1721991 : Blo 1721061 1721991 := bstep (se 1 (by rfl) ⟨1291493, by rfl⟩ : syracuseStep 1721991 = 2582987) B2582987
theorem B4359815 : Blo 1721061 4359815 := bstep (se 1 (by rfl) ⟨3269861, by rfl⟩ : syracuseStep 4359815 = 6539723) B6539723
theorem B2582159 : Blo 1721061 2582159 := bstep (se 1 (by rfl) ⟨1936619, by rfl⟩ : syracuseStep 2582159 = 3873239) B3873239
theorem B1721999 : Blo 1721061 1721999 := bstep (se 1 (by rfl) ⟨1291499, by rfl⟩ : syracuseStep 1721999 = 2582999) B2582999
theorem B2582201 : Blo 1721061 2582201 := bstep (se 2 (by rfl) ⟨968325, by rfl⟩ : syracuseStep 2582201 = 1936651) B1936651
theorem B4359865 : Blo 1721061 4359865 := bstep (se 2 (by rfl) ⟨1634949, by rfl⟩ : syracuseStep 4359865 = 3269899) B3269899
theorem B1722043 : Blo 1721061 1722043 := bstep (se 1 (by rfl) ⟨1291532, by rfl⟩ : syracuseStep 1722043 = 2583065) B2583065
theorem B2582279 : Blo 1721061 2582279 := bstep (se 1 (by rfl) ⟨1936709, by rfl⟩ : syracuseStep 2582279 = 3873419) B3873419
theorem B1722119 : Blo 1721061 1722119 := bstep (se 1 (by rfl) ⟨1291589, by rfl⟩ : syracuseStep 1722119 = 2583179) B2583179
theorem B1722127 : Blo 1721061 1722127 := bstep (se 1 (by rfl) ⟨1291595, by rfl⟩ : syracuseStep 1722127 = 2583191) B2583191
theorem B3876623 : Blo 1721061 3876623 := bstep (se 1 (by rfl) ⟨2907467, by rfl⟩ : syracuseStep 3876623 = 5814935) B5814935
theorem B3876641 : Blo 1721061 3876641 := bstep (se 2 (by rfl) ⟨1453740, by rfl⟩ : syracuseStep 3876641 = 2907481) B2907481
theorem B2582315 : Blo 1721061 2582315 := bstep (se 1 (by rfl) ⟨1936736, by rfl⟩ : syracuseStep 2582315 = 3873473) B3873473
theorem B14706481 : Blo 1721061 14706481 := bstep (se 2 (by rfl) ⟨5514930, by rfl⟩ : syracuseStep 14706481 = 11029861) B11029861
theorem B29812531 : Blo 1721061 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B1722171 : Blo 1721061 1722171 := bstep (se 1 (by rfl) ⟨1291628, by rfl⟩ : syracuseStep 1722171 = 2583257) B2583257
theorem B2582345 : Blo 1721061 2582345 := bstep (se 2 (by rfl) ⟨968379, by rfl⟩ : syracuseStep 2582345 = 1936759) B1936759
theorem B1722247 : Blo 1721061 1722247 := bstep (se 1 (by rfl) ⟨1291685, by rfl⟩ : syracuseStep 1722247 = 2583371) B2583371
theorem B1722255 : Blo 1721061 1722255 := bstep (se 1 (by rfl) ⟨1291691, by rfl⟩ : syracuseStep 1722255 = 2583383) B2583383
theorem B6629273 : Blo 1721061 6629273 := bstep (se 2 (by rfl) ⟨2485977, by rfl⟩ : syracuseStep 6629273 = 4971955) B4971955
theorem B2582459 : Blo 1721061 2582459 := bstep (se 1 (by rfl) ⟨1936844, by rfl⟩ : syracuseStep 2582459 = 3873689) B3873689
theorem B1722299 : Blo 1721061 1722299 := bstep (se 1 (by rfl) ⟨1291724, by rfl⟩ : syracuseStep 1722299 = 2583449) B2583449
theorem B2582519 : Blo 1721061 2582519 := bstep (se 1 (by rfl) ⟨1936889, by rfl⟩ : syracuseStep 2582519 = 3873779) B3873779
theorem B9807875 : Blo 1721061 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B1722375 : Blo 1721061 1722375 := bstep (se 1 (by rfl) ⟨1291781, by rfl⟩ : syracuseStep 1722375 = 2583563) B2583563
theorem B2582543 : Blo 1721061 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B5236751 : Blo 1721061 5236751 := bstep (se 1 (by rfl) ⟨3927563, by rfl⟩ : syracuseStep 5236751 = 7855127) B7855127
theorem B1722383 : Blo 1721061 1722383 := bstep (se 1 (by rfl) ⟨1291787, by rfl⟩ : syracuseStep 1722383 = 2583575) B2583575
theorem B3270689 : Blo 1721061 3270689 := bstep (se 2 (by rfl) ⟨1226508, by rfl⟩ : syracuseStep 3270689 = 2453017) B2453017
theorem B2582585 : Blo 1721061 2582585 := bstep (se 2 (by rfl) ⟨968469, by rfl⟩ : syracuseStep 2582585 = 1936939) B1936939
theorem B1722427 : Blo 1721061 1722427 := bstep (se 1 (by rfl) ⟨1291820, by rfl⟩ : syracuseStep 1722427 = 2583641) B2583641
theorem B5810237 : Blo 1721061 5810237 := bstep (se 3 (by rfl) ⟨1089419, by rfl⟩ : syracuseStep 5810237 = 2178839) B2178839
theorem B26503285 : Blo 1721061 26503285 := bstep (se 5 (by rfl) ⟨1242341, by rfl⟩ : syracuseStep 26503285 = 2484683) B2484683
theorem B8276087 : Blo 1721061 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B16550021 : Blo 1721061 16550021 := bstep (se 4 (by rfl) ⟨1551564, by rfl⟩ : syracuseStep 16550021 = 3103129) B3103129
theorem B4900999 : Blo 1721061 4900999 := bstep (se 1 (by rfl) ⟨3675749, by rfl⟩ : syracuseStep 4900999 = 7351499) B7351499
theorem B2582663 : Blo 1721061 2582663 := bstep (se 1 (by rfl) ⟨1936997, by rfl⟩ : syracuseStep 2582663 = 3873995) B3873995
theorem B1722503 : Blo 1721061 1722503 := bstep (se 1 (by rfl) ⟨1291877, by rfl⟩ : syracuseStep 1722503 = 2583755) B2583755
theorem B1722511 : Blo 1721061 1722511 := bstep (se 1 (by rfl) ⟨1291883, by rfl⟩ : syracuseStep 1722511 = 2583767) B2583767
theorem B2582699 : Blo 1721061 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1722555 : Blo 1721061 1722555 := bstep (se 1 (by rfl) ⟨1291916, by rfl⟩ : syracuseStep 1722555 = 2583833) B2583833
theorem B2582729 : Blo 1721061 2582729 := bstep (se 2 (by rfl) ⟨968523, by rfl⟩ : syracuseStep 2582729 = 1937047) B1937047
theorem B1722631 : Blo 1721061 1722631 := bstep (se 1 (by rfl) ⟨1291973, by rfl⟩ : syracuseStep 1722631 = 2583947) B2583947
theorem B1722639 : Blo 1721061 1722639 := bstep (se 1 (by rfl) ⟨1291979, by rfl⟩ : syracuseStep 1722639 = 2583959) B2583959
theorem B4360463 : Blo 1721061 4360463 := bstep (se 1 (by rfl) ⟨3270347, by rfl⟩ : syracuseStep 4360463 = 6540695) B6540695
theorem B3270955 : Blo 1721061 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B2582843 : Blo 1721061 2582843 := bstep (se 1 (by rfl) ⟨1937132, by rfl⟩ : syracuseStep 2582843 = 3874265) B3874265
theorem B1722683 : Blo 1721061 1722683 := bstep (se 1 (by rfl) ⟨1292012, by rfl⟩ : syracuseStep 1722683 = 2584025) B2584025
theorem B4139351 : Blo 1721061 4139351 := bstep (se 1 (by rfl) ⟨3104513, by rfl⟩ : syracuseStep 4139351 = 6209027) B6209027
theorem B2582903 : Blo 1721061 2582903 := bstep (se 1 (by rfl) ⟨1937177, by rfl⟩ : syracuseStep 2582903 = 3874355) B3874355
theorem B1722759 : Blo 1721061 1722759 := bstep (se 1 (by rfl) ⟨1292069, by rfl⟩ : syracuseStep 1722759 = 2584139) B2584139
theorem B2582927 : Blo 1721061 2582927 := bstep (se 1 (by rfl) ⟨1937195, by rfl⟩ : syracuseStep 2582927 = 3874391) B3874391
theorem B1722767 : Blo 1721061 1722767 := bstep (se 1 (by rfl) ⟨1292075, by rfl⟩ : syracuseStep 1722767 = 2584151) B2584151
theorem B4901273 : Blo 1721061 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B2582969 : Blo 1721061 2582969 := bstep (se 2 (by rfl) ⟨968613, by rfl⟩ : syracuseStep 2582969 = 1937227) B1937227
theorem B1722811 : Blo 1721061 1722811 := bstep (se 1 (by rfl) ⟨1292108, by rfl⟩ : syracuseStep 1722811 = 2584217) B2584217
theorem B2583047 : Blo 1721061 2583047 := bstep (se 1 (by rfl) ⟨1937285, by rfl⟩ : syracuseStep 2583047 = 3874571) B3874571
theorem B1722887 : Blo 1721061 1722887 := bstep (se 1 (by rfl) ⟨1292165, by rfl⟩ : syracuseStep 1722887 = 2584331) B2584331
theorem B1722895 : Blo 1721061 1722895 := bstep (se 1 (by rfl) ⟨1292171, by rfl⟩ : syracuseStep 1722895 = 2584343) B2584343
theorem B2583083 : Blo 1721061 2583083 := bstep (se 1 (by rfl) ⟨1937312, by rfl⟩ : syracuseStep 2583083 = 3874625) B3874625
theorem B2689595 : Blo 1721061 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B1722939 : Blo 1721061 1722939 := bstep (se 1 (by rfl) ⟨1292204, by rfl⟩ : syracuseStep 1722939 = 2584409) B2584409
theorem B2583113 : Blo 1721061 2583113 := bstep (se 2 (by rfl) ⟨968667, by rfl⟩ : syracuseStep 2583113 = 1937335) B1937335
theorem B1723015 : Blo 1721061 1723015 := bstep (se 1 (by rfl) ⟨1292261, by rfl⟩ : syracuseStep 1723015 = 2584523) B2584523
theorem B1723023 : Blo 1721061 1723023 := bstep (se 1 (by rfl) ⟨1292267, by rfl⟩ : syracuseStep 1723023 = 2584535) B2584535
theorem B2583227 : Blo 1721061 2583227 := bstep (se 1 (by rfl) ⟨1937420, by rfl⟩ : syracuseStep 2583227 = 3874841) B3874841
theorem B2583287 : Blo 1721061 2583287 := bstep (se 1 (by rfl) ⟨1937465, by rfl⟩ : syracuseStep 2583287 = 3874931) B3874931
theorem B2452231 : Blo 1721061 2452231 := bstep (se 1 (by rfl) ⟨1839173, by rfl⟩ : syracuseStep 2452231 = 3678347) B3678347
theorem B2583311 : Blo 1721061 2583311 := bstep (se 1 (by rfl) ⟨1937483, by rfl⟩ : syracuseStep 2583311 = 3874967) B3874967
theorem B2583353 : Blo 1721061 2583353 := bstep (se 2 (by rfl) ⟨968757, by rfl⟩ : syracuseStep 2583353 = 1937515) B1937515
theorem B8719163 : Blo 1721061 8719163 := bstep (se 1 (by rfl) ⟨6539372, by rfl⟩ : syracuseStep 8719163 = 13078745) B13078745
theorem B33565529 : Blo 1721061 33565529 := bstep (se 2 (by rfl) ⟨12587073, by rfl⟩ : syracuseStep 33565529 = 25174147) B25174147
theorem B2583431 : Blo 1721061 2583431 := bstep (se 1 (by rfl) ⟨1937573, by rfl⟩ : syracuseStep 2583431 = 3875147) B3875147
theorem B2583467 : Blo 1721061 2583467 := bstep (se 1 (by rfl) ⟨1937600, by rfl⟩ : syracuseStep 2583467 = 3875201) B3875201
theorem B2583497 : Blo 1721061 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B4361161 : Blo 1721061 4361161 := bstep (se 2 (by rfl) ⟨1635435, by rfl⟩ : syracuseStep 4361161 = 3270871) B3270871
theorem B8719325 : Blo 1721061 8719325 := bstep (se 3 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 8719325 = 3269747) B3269747
theorem B11037707 : Blo 1721061 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B1936399 : Blo 1721061 1936399 := bstep (se 1 (by rfl) ⟨1452299, by rfl⟩ : syracuseStep 1936399 = 2904599) B2904599
theorem B2583611 : Blo 1721061 2583611 := bstep (se 1 (by rfl) ⟨1937708, by rfl⟩ : syracuseStep 2583611 = 3875417) B3875417
theorem B5893181 : Blo 1721061 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B4361303 : Blo 1721061 4361303 := bstep (se 1 (by rfl) ⟨3270977, by rfl⟩ : syracuseStep 4361303 = 6541955) B6541955
theorem B2583671 : Blo 1721061 2583671 := bstep (se 1 (by rfl) ⟨1937753, by rfl⟩ : syracuseStep 2583671 = 3875507) B3875507
theorem B2583695 : Blo 1721061 2583695 := bstep (se 1 (by rfl) ⟨1937771, by rfl⟩ : syracuseStep 2583695 = 3875543) B3875543
theorem B4656275 : Blo 1721061 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B2583737 : Blo 1721061 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B4656329 : Blo 1721061 4656329 := bstep (se 2 (by rfl) ⟨1746123, by rfl⟩ : syracuseStep 4656329 = 3492247) B3492247
theorem B2583815 : Blo 1721061 2583815 := bstep (se 1 (by rfl) ⟨1937861, by rfl⟩ : syracuseStep 2583815 = 3875723) B3875723
theorem B8719649 : Blo 1721061 8719649 := bstep (se 2 (by rfl) ⟨3269868, by rfl⟩ : syracuseStep 8719649 = 6539737) B6539737
theorem B2583851 : Blo 1721061 2583851 := bstep (se 1 (by rfl) ⟨1937888, by rfl⟩ : syracuseStep 2583851 = 3875777) B3875777
theorem B2583881 : Blo 1721061 2583881 := bstep (se 2 (by rfl) ⟨968955, by rfl⟩ : syracuseStep 2583881 = 1937911) B1937911
theorem B63688037 : Blo 1721061 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B14912915 : Blo 1721061 14912915 := bstep (se 1 (by rfl) ⟨11184686, by rfl⟩ : syracuseStep 14912915 = 22369373) B22369373
theorem B5811641 : Blo 1721061 5811641 := bstep (se 2 (by rfl) ⟨2179365, by rfl⟩ : syracuseStep 5811641 = 4358731) B4358731
theorem B2583995 : Blo 1721061 2583995 := bstep (se 1 (by rfl) ⟨1937996, by rfl⟩ : syracuseStep 2583995 = 3875993) B3875993
theorem B3026377 : Blo 1721061 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B9309649 : Blo 1721061 9309649 := bstep (se 2 (by rfl) ⟨3491118, by rfl⟩ : syracuseStep 9309649 = 6982237) B6982237
theorem B2584055 : Blo 1721061 2584055 := bstep (se 1 (by rfl) ⟨1938041, by rfl⟩ : syracuseStep 2584055 = 3876083) B3876083
theorem B1936903 : Blo 1721061 1936903 := bstep (se 1 (by rfl) ⟨1452677, by rfl⟩ : syracuseStep 1936903 = 2905355) B2905355
theorem B2584079 : Blo 1721061 2584079 := bstep (se 1 (by rfl) ⟨1938059, by rfl⟩ : syracuseStep 2584079 = 3876119) B3876119
theorem B2584121 : Blo 1721061 2584121 := bstep (se 2 (by rfl) ⟨969045, by rfl⟩ : syracuseStep 2584121 = 1938091) B1938091
theorem B2453051 : Blo 1721061 2453051 := bstep (se 1 (by rfl) ⟨1839788, by rfl⟩ : syracuseStep 2453051 = 3679577) B3679577
theorem B21229133 : Blo 1721061 21229133 := bstep (se 3 (by rfl) ⟨3980462, by rfl⟩ : syracuseStep 21229133 = 7960925) B7960925
theorem B4902515 : Blo 1721061 4902515 := bstep (se 1 (by rfl) ⟨3676886, by rfl⟩ : syracuseStep 4902515 = 7353773) B7353773
theorem B2584199 : Blo 1721061 2584199 := bstep (se 1 (by rfl) ⟨1938149, by rfl⟩ : syracuseStep 2584199 = 3876299) B3876299
theorem B2584235 : Blo 1721061 2584235 := bstep (se 1 (by rfl) ⟨1938176, by rfl⟩ : syracuseStep 2584235 = 3876353) B3876353
theorem B1937083 : Blo 1721061 1937083 := bstep (se 1 (by rfl) ⟨1452812, by rfl⟩ : syracuseStep 1937083 = 2905625) B2905625
theorem B2584265 : Blo 1721061 2584265 := bstep (se 2 (by rfl) ⟨969099, by rfl⟩ : syracuseStep 2584265 = 1938199) B1938199
theorem B11783951 : Blo 1721061 11783951 := bstep (se 1 (by rfl) ⟨8837963, by rfl⟩ : syracuseStep 11783951 = 17675927) B17675927
theorem B2584379 : Blo 1721061 2584379 := bstep (se 1 (by rfl) ⟨1938284, by rfl⟩ : syracuseStep 2584379 = 3876569) B3876569
theorem B2584439 : Blo 1721061 2584439 := bstep (se 1 (by rfl) ⟨1938329, by rfl⟩ : syracuseStep 2584439 = 3876659) B3876659
theorem B6631303 : Blo 1721061 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B2584463 : Blo 1721061 2584463 := bstep (se 1 (by rfl) ⟨1938347, by rfl⟩ : syracuseStep 2584463 = 3876695) B3876695
theorem B2584505 : Blo 1721061 2584505 := bstep (se 2 (by rfl) ⟨969189, by rfl⟩ : syracuseStep 2584505 = 1938379) B1938379
theorem B2584583 : Blo 1721061 2584583 := bstep (se 1 (by rfl) ⟨1938437, by rfl⟩ : syracuseStep 2584583 = 3876875) B3876875
theorem B5812235 : Blo 1721061 5812235 := bstep (se 1 (by rfl) ⟨4359176, by rfl⟩ : syracuseStep 5812235 = 8718353) B8718353
theorem B5517341 : Blo 1721061 5517341 := bstep (se 3 (by rfl) ⟨1034501, by rfl⟩ : syracuseStep 5517341 = 2069003) B2069003
theorem B11038781 : Blo 1721061 11038781 := bstep (se 3 (by rfl) ⟨2069771, by rfl⟩ : syracuseStep 11038781 = 4139543) B4139543
theorem B5812343 : Blo 1721061 5812343 := bstep (se 1 (by rfl) ⟨4359257, by rfl⟩ : syracuseStep 5812343 = 8718515) B8718515
theorem B1937551 : Blo 1721061 1937551 := bstep (se 1 (by rfl) ⟨1453163, by rfl⟩ : syracuseStep 1937551 = 2906327) B2906327
theorem B9310409 : Blo 1721061 9310409 := bstep (se 2 (by rfl) ⟨3491403, by rfl⟩ : syracuseStep 9310409 = 6982807) B6982807
theorem B8720621 : Blo 1721061 8720621 := bstep (se 3 (by rfl) ⟨1635116, by rfl⟩ : syracuseStep 8720621 = 3270233) B3270233
theorem B9802043 : Blo 1721061 9802043 := bstep (se 1 (by rfl) ⟨7351532, by rfl⟩ : syracuseStep 9802043 = 14703065) B14703065
theorem B3928439 : Blo 1721061 3928439 := bstep (se 1 (by rfl) ⟨2946329, by rfl⟩ : syracuseStep 3928439 = 5892659) B5892659
theorem B2756999 : Blo 1721061 2756999 := bstep (se 1 (by rfl) ⟨2067749, by rfl⟩ : syracuseStep 2756999 = 4135499) B4135499
theorem B12415517 : Blo 1721061 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B2904619 : Blo 1721061 2904619 := bstep (se 1 (by rfl) ⟨2178464, by rfl⟩ : syracuseStep 2904619 = 4356929) B4356929
theorem B1938055 : Blo 1721061 1938055 := bstep (se 1 (by rfl) ⟨1453541, by rfl⟩ : syracuseStep 1938055 = 2907083) B2907083
theorem B2904761 : Blo 1721061 2904761 := bstep (se 2 (by rfl) ⟨1089285, by rfl⟩ : syracuseStep 2904761 = 2178571) B2178571
theorem B5812937 : Blo 1721061 5812937 := bstep (se 2 (by rfl) ⟨2179851, by rfl⟩ : syracuseStep 5812937 = 4359703) B4359703
theorem B7353089 : Blo 1721061 7353089 := bstep (se 2 (by rfl) ⟨2757408, by rfl⟩ : syracuseStep 7353089 = 5514817) B5514817
theorem B2069263 : Blo 1721061 2069263 := bstep (se 1 (by rfl) ⟨1551947, by rfl⟩ : syracuseStep 2069263 = 3103895) B3103895
theorem B1938235 : Blo 1721061 1938235 := bstep (se 1 (by rfl) ⟨1453676, by rfl⟩ : syracuseStep 1938235 = 2907353) B2907353
theorem B2757511 : Blo 1721061 2757511 := bstep (se 1 (by rfl) ⟨2068133, by rfl⟩ : syracuseStep 2757511 = 4136267) B4136267
theorem B18609047 : Blo 1721061 18609047 := bstep (se 1 (by rfl) ⟨13956785, by rfl⟩ : syracuseStep 18609047 = 27913571) B27913571
theorem B8713169 : Blo 1721061 8713169 := bstep (se 2 (by rfl) ⟨3267438, by rfl⟩ : syracuseStep 8713169 = 6534877) B6534877
theorem B14717963 : Blo 1721061 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B8721431 : Blo 1721061 8721431 := bstep (se 1 (by rfl) ⟨6541073, by rfl⟩ : syracuseStep 8721431 = 13082147) B13082147
theorem B10073117 : Blo 1721061 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B2618411 : Blo 1721061 2618411 := bstep (se 1 (by rfl) ⟨1963808, by rfl⟩ : syracuseStep 2618411 = 3927617) B3927617
theorem B9803045 : Blo 1721061 9803045 := bstep (se 4 (by rfl) ⟨919035, by rfl⟩ : syracuseStep 9803045 = 1838071) B1838071
theorem B2905463 : Blo 1721061 2905463 := bstep (se 1 (by rfl) ⟨2179097, by rfl⟩ : syracuseStep 2905463 = 4358195) B4358195
theorem B2946439 : Blo 1721061 2946439 := bstep (se 1 (by rfl) ⟨2209829, by rfl⟩ : syracuseStep 2946439 = 4419659) B4419659
theorem B5813639 : Blo 1721061 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B6206867 : Blo 1721061 6206867 := bstep (se 1 (by rfl) ⟨4655150, by rfl⟩ : syracuseStep 6206867 = 9310301) B9310301
theorem B3315215 : Blo 1721061 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B3929735 : Blo 1721061 3929735 := bstep (se 1 (by rfl) ⟨2947301, by rfl⟩ : syracuseStep 3929735 = 5894603) B5894603
theorem B9434825 : Blo 1721061 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B9803501 : Blo 1721061 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B5814017 : Blo 1721061 5814017 := bstep (se 2 (by rfl) ⟨2180256, by rfl⟩ : syracuseStep 5814017 = 4360513) B4360513
theorem B3675937 : Blo 1721061 3675937 := bstep (se 2 (by rfl) ⟨1378476, by rfl⟩ : syracuseStep 3675937 = 2756953) B2756953
theorem B3872555 : Blo 1721061 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B2905915 : Blo 1721061 2905915 := bstep (se 1 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 2905915 = 4358873) B4358873
theorem B2906057 : Blo 1721061 2906057 := bstep (se 2 (by rfl) ⟨1089771, by rfl⟩ : syracuseStep 2906057 = 2179543) B2179543
theorem B17668043 : Blo 1721061 17668043 := bstep (se 1 (by rfl) ⟨13251032, by rfl⟩ : syracuseStep 17668043 = 26502065) B26502065
theorem B4904975 : Blo 1721061 4904975 := bstep (se 1 (by rfl) ⟨3678731, by rfl⟩ : syracuseStep 4904975 = 7357463) B7357463
theorem B35330165 : Blo 1721061 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B3676279 : Blo 1721061 3676279 := bstep (se 1 (by rfl) ⟨2757209, by rfl⟩ : syracuseStep 3676279 = 5514419) B5514419
theorem B3872915 : Blo 1721061 3872915 := bstep (se 1 (by rfl) ⟨2904686, by rfl⟩ : syracuseStep 3872915 = 5809373) B5809373
theorem B3872969 : Blo 1721061 3872969 := bstep (se 2 (by rfl) ⟨1452363, by rfl⟩ : syracuseStep 3872969 = 2904727) B2904727
theorem B9943241 : Blo 1721061 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B3103123 : Blo 1721061 3103123 := bstep (se 1 (by rfl) ⟨2327342, by rfl⟩ : syracuseStep 3103123 = 4654685) B4654685
theorem B9804185 : Blo 1721061 9804185 := bstep (se 2 (by rfl) ⟨3676569, by rfl⟩ : syracuseStep 9804185 = 7353139) B7353139
theorem B5519801 : Blo 1721061 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B5814827 : Blo 1721061 5814827 := bstep (se 1 (by rfl) ⟨4361120, by rfl⟩ : syracuseStep 5814827 = 8722241) B8722241
theorem B17676901 : Blo 1721061 17676901 := bstep (se 4 (by rfl) ⟨1657209, by rfl⟩ : syracuseStep 17676901 = 3314419) B3314419
theorem B2906759 : Blo 1721061 2906759 := bstep (se 1 (by rfl) ⟨2180069, by rfl⟩ : syracuseStep 2906759 = 4360139) B4360139
theorem B3267371 : Blo 1721061 3267371 := bstep (se 1 (by rfl) ⟨2450528, by rfl⟩ : syracuseStep 3267371 = 4901057) B4901057
theorem B3873671 : Blo 1721061 3873671 := bstep (se 1 (by rfl) ⟨2905253, by rfl⟩ : syracuseStep 3873671 = 5810507) B5810507
theorem B44129285 : Blo 1721061 44129285 := bstep (se 4 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 44129285 = 8274241) B8274241
theorem B8715275 : Blo 1721061 8715275 := bstep (se 1 (by rfl) ⟨6536456, by rfl⟩ : syracuseStep 8715275 = 13072913) B13072913
theorem B3873851 : Blo 1721061 3873851 := bstep (se 1 (by rfl) ⟨2905388, by rfl⟩ : syracuseStep 3873851 = 5810777) B5810777
theorem B13081661 : Blo 1721061 13081661 := bstep (se 3 (by rfl) ⟨2452811, by rfl⟩ : syracuseStep 13081661 = 4905623) B4905623
theorem B4652185 : Blo 1721061 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B4357273 : Blo 1721061 4357273 := bstep (se 2 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 4357273 = 3267955) B3267955
theorem B8715437 : Blo 1721061 8715437 := bstep (se 3 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 8715437 = 3268289) B3268289
theorem B3873977 : Blo 1721061 3873977 := bstep (se 2 (by rfl) ⟨1452741, by rfl⟩ : syracuseStep 3873977 = 2905483) B2905483
theorem B2907407 : Blo 1721061 2907407 := bstep (se 1 (by rfl) ⟨2180555, by rfl⟩ : syracuseStep 2907407 = 4361111) B4361111
theorem B4357435 : Blo 1721061 4357435 := bstep (se 1 (by rfl) ⟨3268076, by rfl⟩ : syracuseStep 4357435 = 6536153) B6536153
theorem B31415687 : Blo 1721061 31415687 := bstep (se 1 (by rfl) ⟨23561765, by rfl⟩ : syracuseStep 31415687 = 47123531) B47123531
theorem B4193683 : Blo 1721061 4193683 := bstep (se 1 (by rfl) ⟨3145262, by rfl⟩ : syracuseStep 4193683 = 6290525) B6290525
theorem B4357577 : Blo 1721061 4357577 := bstep (se 2 (by rfl) ⟨1634091, by rfl⟩ : syracuseStep 4357577 = 3268183) B3268183
theorem B13073885 : Blo 1721061 13073885 := bstep (se 3 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 13073885 = 4902707) B4902707
theorem B4136449 : Blo 1721061 4136449 := bstep (se 2 (by rfl) ⟨1551168, by rfl⟩ : syracuseStep 4136449 = 3102337) B3102337
theorem B3874319 : Blo 1721061 3874319 := bstep (se 1 (by rfl) ⟨2905739, by rfl⟩ : syracuseStep 3874319 = 5811479) B5811479
theorem B3874337 : Blo 1721061 3874337 := bstep (se 2 (by rfl) ⟨1452876, by rfl⟩ : syracuseStep 3874337 = 2905753) B2905753
theorem B24813155 : Blo 1721061 24813155 := bstep (se 1 (by rfl) ⟨18609866, by rfl⟩ : syracuseStep 24813155 = 37219733) B37219733
theorem B4849267 : Blo 1721061 4849267 := bstep (se 1 (by rfl) ⟨3636950, by rfl⟩ : syracuseStep 4849267 = 7273901) B7273901
theorem B4906615 : Blo 1721061 4906615 := bstep (se 1 (by rfl) ⟨3679961, by rfl⟩ : syracuseStep 4906615 = 7359923) B7359923
theorem B4906649 : Blo 1721061 4906649 := bstep (se 2 (by rfl) ⟨1839993, by rfl⟩ : syracuseStep 4906649 = 3679987) B3679987
theorem B34021093 : Blo 1721061 34021093 := bstep (se 4 (by rfl) ⟨3189477, by rfl⟩ : syracuseStep 34021093 = 6378955) B6378955
theorem B4357921 : Blo 1721061 4357921 := bstep (se 2 (by rfl) ⟨1634220, by rfl⟩ : syracuseStep 4357921 = 3268441) B3268441
theorem B2096939 : Blo 1721061 2096939 := bstep (se 1 (by rfl) ⟨1572704, by rfl⟩ : syracuseStep 2096939 = 3145409) B3145409
theorem B3874679 : Blo 1721061 3874679 := bstep (se 1 (by rfl) ⟨2906009, by rfl⟩ : syracuseStep 3874679 = 5812019) B5812019
theorem B3268487 : Blo 1721061 3268487 := bstep (se 1 (by rfl) ⟨2451365, by rfl⟩ : syracuseStep 3268487 = 4902731) B4902731
theorem B6537095 : Blo 1721061 6537095 := bstep (se 1 (by rfl) ⟨4902821, by rfl⟩ : syracuseStep 6537095 = 9805643) B9805643
theorem B3874823 : Blo 1721061 3874823 := bstep (se 1 (by rfl) ⟨2906117, by rfl⟩ : syracuseStep 3874823 = 5812235) B5812235
theorem B22069259 : Blo 1721061 22069259 := bstep (se 1 (by rfl) ⟨16551944, by rfl⟩ : syracuseStep 22069259 = 33103889) B33103889
theorem B3678227 : Blo 1721061 3678227 := bstep (se 1 (by rfl) ⟨2758670, by rfl⟩ : syracuseStep 3678227 = 5517341) B5517341
theorem B26861645 : Blo 1721061 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3874895 : Blo 1721061 3874895 := bstep (se 1 (by rfl) ⟨2906171, by rfl⟩ : syracuseStep 3874895 = 5812343) B5812343
theorem B3875291 : Blo 1721061 3875291 := bstep (se 1 (by rfl) ⟨2906468, by rfl⟩ : syracuseStep 3875291 = 5812937) B5812937
theorem B4358681 : Blo 1721061 4358681 := bstep (se 2 (by rfl) ⟨1634505, by rfl⟩ : syracuseStep 4358681 = 3269011) B3269011
theorem B4137497 : Blo 1721061 4137497 := bstep (se 2 (by rfl) ⟨1551561, by rfl⟩ : syracuseStep 4137497 = 3103123) B3103123
theorem B5808779 : Blo 1721061 5808779 := bstep (se 1 (by rfl) ⟨4356584, by rfl⟩ : syracuseStep 5808779 = 8713169) B8713169
theorem B1721127 : Blo 1721061 1721127 := bstep (se 1 (by rfl) ⟨1290845, by rfl⟩ : syracuseStep 1721127 = 2581691) B2581691
theorem B226444085 : Blo 1721061 226444085 := bstep (se 5 (by rfl) ⟨10614566, by rfl⟩ : syracuseStep 226444085 = 21229133) B21229133
theorem B23569201 : Blo 1721061 23569201 := bstep (se 2 (by rfl) ⟨8838450, by rfl⟩ : syracuseStep 23569201 = 17676901) B17676901
theorem B1721167 : Blo 1721061 1721167 := bstep (se 1 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 1721167 = 2581751) B2581751
theorem B1721183 : Blo 1721061 1721183 := bstep (se 1 (by rfl) ⟨1290887, by rfl⟩ : syracuseStep 1721183 = 2581775) B2581775
theorem B1721211 : Blo 1721061 1721211 := bstep (se 1 (by rfl) ⟨1290908, by rfl⟩ : syracuseStep 1721211 = 2581817) B2581817
theorem B1721263 : Blo 1721061 1721263 := bstep (se 1 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 1721263 = 2581895) B2581895
theorem B3875759 : Blo 1721061 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B4137911 : Blo 1721061 4137911 := bstep (se 1 (by rfl) ⟨3103433, by rfl⟩ : syracuseStep 4137911 = 6206867) B6206867
theorem B1721287 : Blo 1721061 1721287 := bstep (se 1 (by rfl) ⟨1290965, by rfl⟩ : syracuseStep 1721287 = 2581931) B2581931
theorem B1721307 : Blo 1721061 1721307 := bstep (se 1 (by rfl) ⟨1290980, by rfl⟩ : syracuseStep 1721307 = 2581961) B2581961
theorem B3269641 : Blo 1721061 3269641 := bstep (se 2 (by rfl) ⟨1226115, by rfl⟩ : syracuseStep 3269641 = 2452231) B2452231
theorem B1721383 : Blo 1721061 1721383 := bstep (se 1 (by rfl) ⟨1291037, by rfl⟩ : syracuseStep 1721383 = 2582075) B2582075
theorem B2180135 : Blo 1721061 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B1721423 : Blo 1721061 1721423 := bstep (se 1 (by rfl) ⟨1291067, by rfl⟩ : syracuseStep 1721423 = 2582135) B2582135
theorem B1721439 : Blo 1721061 1721439 := bstep (se 1 (by rfl) ⟨1291079, by rfl⟩ : syracuseStep 1721439 = 2582159) B2582159
theorem B1721467 : Blo 1721061 1721467 := bstep (se 1 (by rfl) ⟨1291100, by rfl⟩ : syracuseStep 1721467 = 2582201) B2582201
theorem B3876011 : Blo 1721061 3876011 := bstep (se 1 (by rfl) ⟨2907008, by rfl⟩ : syracuseStep 3876011 = 5814017) B5814017
theorem B1721519 : Blo 1721061 1721519 := bstep (se 1 (by rfl) ⟨1291139, by rfl⟩ : syracuseStep 1721519 = 2582279) B2582279
theorem B2581703 : Blo 1721061 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B1721543 : Blo 1721061 1721543 := bstep (se 1 (by rfl) ⟨1291157, by rfl⟩ : syracuseStep 1721543 = 2582315) B2582315
theorem B1721563 : Blo 1721061 1721563 := bstep (se 1 (by rfl) ⟨1291172, by rfl⟩ : syracuseStep 1721563 = 2582345) B2582345
theorem B1721639 : Blo 1721061 1721639 := bstep (se 1 (by rfl) ⟨1291229, by rfl⟩ : syracuseStep 1721639 = 2582459) B2582459
theorem B1721679 : Blo 1721061 1721679 := bstep (se 1 (by rfl) ⟨1291259, by rfl⟩ : syracuseStep 1721679 = 2582519) B2582519
theorem B6538583 : Blo 1721061 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B1721695 : Blo 1721061 1721695 := bstep (se 1 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 1721695 = 2582543) B2582543
theorem B3269983 : Blo 1721061 3269983 := bstep (se 1 (by rfl) ⟨2452487, by rfl⟩ : syracuseStep 3269983 = 4904975) B4904975
theorem B2581865 : Blo 1721061 2581865 := bstep (se 2 (by rfl) ⟨968199, by rfl⟩ : syracuseStep 2581865 = 1936399) B1936399
theorem B2180459 : Blo 1721061 2180459 := bstep (se 1 (by rfl) ⟨1635344, by rfl⟩ : syracuseStep 2180459 = 3270689) B3270689
theorem B1721723 : Blo 1721061 1721723 := bstep (se 1 (by rfl) ⟨1291292, by rfl⟩ : syracuseStep 1721723 = 2582585) B2582585
theorem B8840573 : Blo 1721061 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B23553443 : Blo 1721061 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B1721775 : Blo 1721061 1721775 := bstep (se 1 (by rfl) ⟨1291331, by rfl⟩ : syracuseStep 1721775 = 2582663) B2582663
theorem B2581943 : Blo 1721061 2581943 := bstep (se 1 (by rfl) ⟨1936457, by rfl⟩ : syracuseStep 2581943 = 3872915) B3872915
theorem B1721799 : Blo 1721061 1721799 := bstep (se 1 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 1721799 = 2582699) B2582699
theorem B2581979 : Blo 1721061 2581979 := bstep (se 1 (by rfl) ⟨1936484, by rfl⟩ : syracuseStep 2581979 = 3872969) B3872969
theorem B1721819 : Blo 1721061 1721819 := bstep (se 1 (by rfl) ⟨1291364, by rfl⟩ : syracuseStep 1721819 = 2582729) B2582729
theorem B6202913 : Blo 1721061 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B5809697 : Blo 1721061 5809697 := bstep (se 2 (by rfl) ⟨2178636, by rfl⟩ : syracuseStep 5809697 = 4357273) B4357273
theorem B1721895 : Blo 1721061 1721895 := bstep (se 1 (by rfl) ⟨1291421, by rfl⟩ : syracuseStep 1721895 = 2582843) B2582843
theorem B1721935 : Blo 1721061 1721935 := bstep (se 1 (by rfl) ⟨1291451, by rfl⟩ : syracuseStep 1721935 = 2582903) B2582903
theorem B1721951 : Blo 1721061 1721951 := bstep (se 1 (by rfl) ⟨1291463, by rfl⟩ : syracuseStep 1721951 = 2582927) B2582927
theorem B1721979 : Blo 1721061 1721979 := bstep (se 1 (by rfl) ⟨1291484, by rfl⟩ : syracuseStep 1721979 = 2582969) B2582969
theorem B3679867 : Blo 1721061 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B1722031 : Blo 1721061 1722031 := bstep (se 1 (by rfl) ⟨1291523, by rfl⟩ : syracuseStep 1722031 = 2583047) B2583047
theorem B10479293 : Blo 1721061 10479293 := bstep (se 3 (by rfl) ⟨1964867, by rfl⟩ : syracuseStep 10479293 = 3929735) B3929735
theorem B1722055 : Blo 1721061 1722055 := bstep (se 1 (by rfl) ⟨1291541, by rfl⟩ : syracuseStep 1722055 = 2583083) B2583083
theorem B3876551 : Blo 1721061 3876551 := bstep (se 1 (by rfl) ⟨2907413, by rfl⟩ : syracuseStep 3876551 = 5814827) B5814827
theorem B6981329 : Blo 1721061 6981329 := bstep (se 2 (by rfl) ⟨2617998, by rfl⟩ : syracuseStep 6981329 = 5235997) B5235997
theorem B1722075 : Blo 1721061 1722075 := bstep (se 1 (by rfl) ⟨1291556, by rfl⟩ : syracuseStep 1722075 = 2583113) B2583113
theorem B5809913 : Blo 1721061 5809913 := bstep (se 2 (by rfl) ⟨2178717, by rfl⟩ : syracuseStep 5809913 = 4357435) B4357435
theorem B1722151 : Blo 1721061 1722151 := bstep (se 1 (by rfl) ⟨1291613, by rfl⟩ : syracuseStep 1722151 = 2583227) B2583227
theorem B1722191 : Blo 1721061 1722191 := bstep (se 1 (by rfl) ⟨1291643, by rfl⟩ : syracuseStep 1722191 = 2583287) B2583287
theorem B1722207 : Blo 1721061 1722207 := bstep (se 1 (by rfl) ⟨1291655, by rfl⟩ : syracuseStep 1722207 = 2583311) B2583311
theorem B1722235 : Blo 1721061 1722235 := bstep (se 1 (by rfl) ⟨1291676, by rfl⟩ : syracuseStep 1722235 = 2583353) B2583353
theorem B2582447 : Blo 1721061 2582447 := bstep (se 1 (by rfl) ⟨1936835, by rfl⟩ : syracuseStep 2582447 = 3873671) B3873671
theorem B1722287 : Blo 1721061 1722287 := bstep (se 1 (by rfl) ⟨1291715, by rfl⟩ : syracuseStep 1722287 = 2583431) B2583431
theorem B12412865 : Blo 1721061 12412865 := bstep (se 2 (by rfl) ⟨4654824, by rfl⟩ : syracuseStep 12412865 = 9309649) B9309649
theorem B1722311 : Blo 1721061 1722311 := bstep (se 1 (by rfl) ⟨1291733, by rfl⟩ : syracuseStep 1722311 = 2583467) B2583467
theorem B1722331 : Blo 1721061 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B5515265 : Blo 1721061 5515265 := bstep (se 2 (by rfl) ⟨2068224, by rfl⟩ : syracuseStep 5515265 = 4136449) B4136449
theorem B29419523 : Blo 1721061 29419523 := bstep (se 1 (by rfl) ⟨22064642, by rfl⟩ : syracuseStep 29419523 = 44129285) B44129285
theorem B5810183 : Blo 1721061 5810183 := bstep (se 1 (by rfl) ⟨4357637, by rfl⟩ : syracuseStep 5810183 = 8715275) B8715275
theorem B2582537 : Blo 1721061 2582537 := bstep (se 2 (by rfl) ⟨968451, by rfl⟩ : syracuseStep 2582537 = 1936903) B1936903
theorem B7358471 : Blo 1721061 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B2582567 : Blo 1721061 2582567 := bstep (se 1 (by rfl) ⟨1936925, by rfl⟩ : syracuseStep 2582567 = 3873851) B3873851
theorem B1722407 : Blo 1721061 1722407 := bstep (se 1 (by rfl) ⟨1291805, by rfl⟩ : syracuseStep 1722407 = 2583611) B2583611
theorem B1722447 : Blo 1721061 1722447 := bstep (se 1 (by rfl) ⟨1291835, by rfl⟩ : syracuseStep 1722447 = 2583671) B2583671
theorem B1722463 : Blo 1721061 1722463 := bstep (se 1 (by rfl) ⟨1291847, by rfl⟩ : syracuseStep 1722463 = 2583695) B2583695
theorem B22366309 : Blo 1721061 22366309 := bstep (se 4 (by rfl) ⟨2096841, by rfl⟩ : syracuseStep 22366309 = 4193683) B4193683
theorem B5810291 : Blo 1721061 5810291 := bstep (se 1 (by rfl) ⟨4357718, by rfl⟩ : syracuseStep 5810291 = 8715437) B8715437
theorem B2582651 : Blo 1721061 2582651 := bstep (se 1 (by rfl) ⟨1936988, by rfl⟩ : syracuseStep 2582651 = 3873977) B3873977
theorem B1722491 : Blo 1721061 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B6465689 : Blo 1721061 6465689 := bstep (se 2 (by rfl) ⟨2424633, by rfl⟩ : syracuseStep 6465689 = 4849267) B4849267
theorem B1722543 : Blo 1721061 1722543 := bstep (se 1 (by rfl) ⟨1291907, by rfl⟩ : syracuseStep 1722543 = 2583815) B2583815
theorem B1722567 : Blo 1721061 1722567 := bstep (se 1 (by rfl) ⟨1291925, by rfl⟩ : syracuseStep 1722567 = 2583851) B2583851
theorem B1722587 : Blo 1721061 1722587 := bstep (se 1 (by rfl) ⟨1291940, by rfl⟩ : syracuseStep 1722587 = 2583881) B2583881
theorem B2582777 : Blo 1721061 2582777 := bstep (se 2 (by rfl) ⟨968541, by rfl⟩ : syracuseStep 2582777 = 1937083) B1937083
theorem B1722663 : Blo 1721061 1722663 := bstep (se 1 (by rfl) ⟨1291997, by rfl⟩ : syracuseStep 1722663 = 2583995) B2583995
theorem B45361457 : Blo 1721061 45361457 := bstep (se 2 (by rfl) ⟨17010546, by rfl⟩ : syracuseStep 45361457 = 34021093) B34021093
theorem B1722703 : Blo 1721061 1722703 := bstep (se 1 (by rfl) ⟨1292027, by rfl⟩ : syracuseStep 1722703 = 2584055) B2584055
theorem B2582879 : Blo 1721061 2582879 := bstep (se 1 (by rfl) ⟨1937159, by rfl⟩ : syracuseStep 2582879 = 3874319) B3874319
theorem B1722719 : Blo 1721061 1722719 := bstep (se 1 (by rfl) ⟨1292039, by rfl⟩ : syracuseStep 1722719 = 2584079) B2584079
theorem B2582891 : Blo 1721061 2582891 := bstep (se 1 (by rfl) ⟨1937168, by rfl⟩ : syracuseStep 2582891 = 3874337) B3874337
theorem B1722747 : Blo 1721061 1722747 := bstep (se 1 (by rfl) ⟨1292060, by rfl⟩ : syracuseStep 1722747 = 2584121) B2584121
theorem B4901249 : Blo 1721061 4901249 := bstep (se 2 (by rfl) ⟨1837968, by rfl⟩ : syracuseStep 4901249 = 3675937) B3675937
theorem B5810561 : Blo 1721061 5810561 := bstep (se 2 (by rfl) ⟨2178960, by rfl⟩ : syracuseStep 5810561 = 4357921) B4357921
theorem B16542103 : Blo 1721061 16542103 := bstep (se 1 (by rfl) ⟨12406577, by rfl⟩ : syracuseStep 16542103 = 24813155) B24813155
theorem B39750041 : Blo 1721061 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B1722799 : Blo 1721061 1722799 := bstep (se 1 (by rfl) ⟨1292099, by rfl⟩ : syracuseStep 1722799 = 2584199) B2584199
theorem B3271099 : Blo 1721061 3271099 := bstep (se 1 (by rfl) ⟨2453324, by rfl⟩ : syracuseStep 3271099 = 4906649) B4906649
theorem B1722823 : Blo 1721061 1722823 := bstep (se 1 (by rfl) ⟨1292117, by rfl⟩ : syracuseStep 1722823 = 2584235) B2584235
theorem B1722843 : Blo 1721061 1722843 := bstep (se 1 (by rfl) ⟨1292132, by rfl⟩ : syracuseStep 1722843 = 2584265) B2584265
theorem B8841737 : Blo 1721061 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B1722919 : Blo 1721061 1722919 := bstep (se 1 (by rfl) ⟨1292189, by rfl⟩ : syracuseStep 1722919 = 2584379) B2584379
theorem B2583119 : Blo 1721061 2583119 := bstep (se 1 (by rfl) ⟨1937339, by rfl⟩ : syracuseStep 2583119 = 3874679) B3874679
theorem B1722959 : Blo 1721061 1722959 := bstep (se 1 (by rfl) ⟨1292219, by rfl⟩ : syracuseStep 1722959 = 2584439) B2584439
theorem B1722975 : Blo 1721061 1722975 := bstep (se 1 (by rfl) ⟨1292231, by rfl⟩ : syracuseStep 1722975 = 2584463) B2584463
theorem B1723003 : Blo 1721061 1723003 := bstep (se 1 (by rfl) ⟨1292252, by rfl⟩ : syracuseStep 1723003 = 2584505) B2584505
theorem B1723055 : Blo 1721061 1723055 := bstep (se 1 (by rfl) ⟨1292291, by rfl⟩ : syracuseStep 1723055 = 2584583) B2584583
theorem B2583239 : Blo 1721061 2583239 := bstep (se 1 (by rfl) ⟨1937429, by rfl⟩ : syracuseStep 2583239 = 3874859) B3874859
theorem B7359187 : Blo 1721061 7359187 := bstep (se 1 (by rfl) ⟨5519390, by rfl⟩ : syracuseStep 7359187 = 11038781) B11038781
theorem B4901705 : Blo 1721061 4901705 := bstep (se 2 (by rfl) ⟨1838139, by rfl⟩ : syracuseStep 4901705 = 3676279) B3676279
theorem B2583401 : Blo 1721061 2583401 := bstep (se 2 (by rfl) ⟨968775, by rfl⟩ : syracuseStep 2583401 = 1937551) B1937551
theorem B1837999 : Blo 1721061 1837999 := bstep (se 1 (by rfl) ⟨1378499, by rfl⟩ : syracuseStep 1837999 = 2756999) B2756999
theorem B2583479 : Blo 1721061 2583479 := bstep (se 1 (by rfl) ⟨1937609, by rfl⟩ : syracuseStep 2583479 = 3875219) B3875219
theorem B2583515 : Blo 1721061 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B8277011 : Blo 1721061 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B4361273 : Blo 1721061 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B27929717 : Blo 1721061 27929717 := bstep (se 5 (by rfl) ⟨1309205, by rfl⟩ : syracuseStep 27929717 = 2618411) B2618411
theorem B1936507 : Blo 1721061 1936507 := bstep (se 1 (by rfl) ⟨1452380, by rfl⟩ : syracuseStep 1936507 = 2904761) B2904761
theorem B4902059 : Blo 1721061 4902059 := bstep (se 1 (by rfl) ⟨3676544, by rfl⟩ : syracuseStep 4902059 = 7353089) B7353089
theorem B5811371 : Blo 1721061 5811371 := bstep (se 1 (by rfl) ⟨4358528, by rfl⟩ : syracuseStep 5811371 = 8717057) B8717057
theorem B12406031 : Blo 1721061 12406031 := bstep (se 1 (by rfl) ⟨9304523, by rfl⟩ : syracuseStep 12406031 = 18609047) B18609047
theorem B2944399 : Blo 1721061 2944399 := bstep (se 1 (by rfl) ⟨2208299, by rfl⟩ : syracuseStep 2944399 = 4416599) B4416599
theorem B2583983 : Blo 1721061 2583983 := bstep (se 1 (by rfl) ⟨1937987, by rfl⟩ : syracuseStep 2583983 = 3875975) B3875975
theorem B2584073 : Blo 1721061 2584073 := bstep (se 2 (by rfl) ⟨969027, by rfl⟩ : syracuseStep 2584073 = 1938055) B1938055
theorem B2584103 : Blo 1721061 2584103 := bstep (se 1 (by rfl) ⟨1938077, by rfl⟩ : syracuseStep 2584103 = 3876155) B3876155
theorem B1936975 : Blo 1721061 1936975 := bstep (se 1 (by rfl) ⟨1452731, by rfl⟩ : syracuseStep 1936975 = 2905463) B2905463
theorem B2584187 : Blo 1721061 2584187 := bstep (se 1 (by rfl) ⟨1938140, by rfl⟩ : syracuseStep 2584187 = 3876281) B3876281
theorem B5811911 : Blo 1721061 5811911 := bstep (se 1 (by rfl) ⟨4358933, by rfl⟩ : syracuseStep 5811911 = 8717867) B8717867
theorem B39767773 : Blo 1721061 39767773 := bstep (se 3 (by rfl) ⟨7456457, by rfl⟩ : syracuseStep 39767773 = 14912915) B14912915
theorem B2584313 : Blo 1721061 2584313 := bstep (se 2 (by rfl) ⟨969117, by rfl⟩ : syracuseStep 2584313 = 1938235) B1938235
theorem B2584415 : Blo 1721061 2584415 := bstep (se 1 (by rfl) ⟨1938311, by rfl⟩ : syracuseStep 2584415 = 3876623) B3876623
theorem B2584427 : Blo 1721061 2584427 := bstep (se 1 (by rfl) ⟨1938320, by rfl⟩ : syracuseStep 2584427 = 3876641) B3876641
theorem B4419515 : Blo 1721061 4419515 := bstep (se 1 (by rfl) ⟨3314636, by rfl⟩ : syracuseStep 4419515 = 6629273) B6629273
theorem B1937371 : Blo 1721061 1937371 := bstep (se 1 (by rfl) ⟨1453028, by rfl⟩ : syracuseStep 1937371 = 2906057) B2906057
theorem B5517391 : Blo 1721061 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B6541469 : Blo 1721061 6541469 := bstep (se 3 (by rfl) ⟨1226525, by rfl⟩ : syracuseStep 6541469 = 2453051) B2453051
theorem B1937839 : Blo 1721061 1937839 := bstep (se 1 (by rfl) ⟨1453379, by rfl⟩ : syracuseStep 1937839 = 2906759) B2906759
theorem B3928585 : Blo 1721061 3928585 := bstep (se 2 (by rfl) ⟨1473219, by rfl⟩ : syracuseStep 3928585 = 2946439) B2946439
theorem B5812775 : Blo 1721061 5812775 := bstep (se 1 (by rfl) ⟨4359581, by rfl⟩ : syracuseStep 5812775 = 8719163) B8719163
theorem B22377019 : Blo 1721061 22377019 := bstep (se 1 (by rfl) ⟨16782764, by rfl⟩ : syracuseStep 22377019 = 33565529) B33565529
theorem B4035169 : Blo 1721061 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B5812883 : Blo 1721061 5812883 := bstep (se 1 (by rfl) ⟨4359662, by rfl⟩ : syracuseStep 5812883 = 8719325) B8719325
theorem B3928787 : Blo 1721061 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B8721107 : Blo 1721061 8721107 := bstep (se 1 (by rfl) ⟨6540830, by rfl⟩ : syracuseStep 8721107 = 13081661) B13081661
theorem B5591837 : Blo 1721061 5591837 := bstep (se 3 (by rfl) ⟨1048469, by rfl⟩ : syracuseStep 5591837 = 2096939) B2096939
theorem B6542153 : Blo 1721061 6542153 := bstep (se 2 (by rfl) ⟨2453307, by rfl⟩ : syracuseStep 6542153 = 4906615) B4906615
theorem B1938271 : Blo 1721061 1938271 := bstep (se 1 (by rfl) ⟨1453703, by rfl⟩ : syracuseStep 1938271 = 2907407) B2907407
theorem B5813099 : Blo 1721061 5813099 := bstep (se 1 (by rfl) ⟨4359824, by rfl⟩ : syracuseStep 5813099 = 8719649) B8719649
theorem B5813153 : Blo 1721061 5813153 := bstep (se 2 (by rfl) ⟨2179932, by rfl⟩ : syracuseStep 5813153 = 4359865) B4359865
theorem B20943791 : Blo 1721061 20943791 := bstep (se 1 (by rfl) ⟨15707843, by rfl⟩ : syracuseStep 20943791 = 31415687) B31415687
theorem B2905051 : Blo 1721061 2905051 := bstep (se 1 (by rfl) ⟨2178788, by rfl⟩ : syracuseStep 2905051 = 4357577) B4357577
theorem B19608641 : Blo 1721061 19608641 := bstep (se 2 (by rfl) ⟨7353240, by rfl⟩ : syracuseStep 19608641 = 14706481) B14706481
theorem B13964669 : Blo 1721061 13964669 := bstep (se 3 (by rfl) ⟨2618375, by rfl⟩ : syracuseStep 13964669 = 5236751) B5236751
theorem B9803227 : Blo 1721061 9803227 := bstep (se 1 (by rfl) ⟨7352420, by rfl⟩ : syracuseStep 9803227 = 14704841) B14704841
theorem B6206939 : Blo 1721061 6206939 := bstep (se 1 (by rfl) ⟨4655204, by rfl⟩ : syracuseStep 6206939 = 9310409) B9310409
theorem B35337713 : Blo 1721061 35337713 := bstep (se 2 (by rfl) ⟨13251642, by rfl⟩ : syracuseStep 35337713 = 26503285) B26503285
theorem B5813747 : Blo 1721061 5813747 := bstep (se 1 (by rfl) ⟨4360310, by rfl⟩ : syracuseStep 5813747 = 8720621) B8720621
theorem B6534665 : Blo 1721061 6534665 := bstep (se 2 (by rfl) ⟨2450499, by rfl⟩ : syracuseStep 6534665 = 4900999) B4900999
theorem B6534695 : Blo 1721061 6534695 := bstep (se 1 (by rfl) ⟨4901021, by rfl⟩ : syracuseStep 6534695 = 9802043) B9802043
theorem B27924011 : Blo 1721061 27924011 := bstep (se 1 (by rfl) ⟨20943008, by rfl⟩ : syracuseStep 27924011 = 41886017) B41886017
theorem B2905679 : Blo 1721061 2905679 := bstep (se 1 (by rfl) ⟨2179259, by rfl⟩ : syracuseStep 2905679 = 4358519) B4358519
theorem B13080203 : Blo 1721061 13080203 := bstep (se 1 (by rfl) ⟨9810152, by rfl⟩ : syracuseStep 13080203 = 19620305) B19620305
theorem B6985415 : Blo 1721061 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B26515309 : Blo 1721061 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B3872699 : Blo 1721061 3872699 := bstep (se 1 (by rfl) ⟨2904524, by rfl⟩ : syracuseStep 3872699 = 5809049) B5809049
theorem B9811975 : Blo 1721061 9811975 := bstep (se 1 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 9811975 = 14717963) B14717963
theorem B5814287 : Blo 1721061 5814287 := bstep (se 1 (by rfl) ⟨4360715, by rfl⟩ : syracuseStep 5814287 = 8721431) B8721431
theorem B3872825 : Blo 1721061 3872825 := bstep (se 2 (by rfl) ⟨1452309, by rfl⟩ : syracuseStep 3872825 = 2904619) B2904619
theorem B3102799 : Blo 1721061 3102799 := bstep (se 1 (by rfl) ⟨2327099, by rfl⟩ : syracuseStep 3102799 = 4654199) B4654199
theorem B6535363 : Blo 1721061 6535363 := bstep (se 1 (by rfl) ⟨4901522, by rfl⟩ : syracuseStep 6535363 = 9803045) B9803045
theorem B169834765 : Blo 1721061 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B10475837 : Blo 1721061 10475837 := bstep (se 3 (by rfl) ⟨1964219, by rfl⟩ : syracuseStep 10475837 = 3928439) B3928439
theorem B2759017 : Blo 1721061 2759017 := bstep (se 2 (by rfl) ⟨1034631, by rfl⟩ : syracuseStep 2759017 = 2069263) B2069263
theorem B106092935 : Blo 1721061 106092935 := bstep (se 1 (by rfl) ⟨79569701, by rfl⟩ : syracuseStep 106092935 = 159139403) B159139403
theorem B3873167 : Blo 1721061 3873167 := bstep (se 1 (by rfl) ⟨2904875, by rfl⟩ : syracuseStep 3873167 = 5809751) B5809751
theorem B2906543 : Blo 1721061 2906543 := bstep (se 1 (by rfl) ⟨2179907, by rfl⟩ : syracuseStep 2906543 = 4359815) B4359815
theorem B6289883 : Blo 1721061 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B6535667 : Blo 1721061 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B3676681 : Blo 1721061 3676681 := bstep (se 2 (by rfl) ⟨1378755, by rfl⟩ : syracuseStep 3676681 = 2757511) B2757511
theorem B5814881 : Blo 1721061 5814881 := bstep (se 2 (by rfl) ⟨2180580, by rfl⟩ : syracuseStep 5814881 = 4361161) B4361161
theorem B11778695 : Blo 1721061 11778695 := bstep (se 1 (by rfl) ⟨8834021, by rfl⟩ : syracuseStep 11778695 = 17668043) B17668043
theorem B12409517 : Blo 1721061 12409517 := bstep (se 3 (by rfl) ⟨2326784, by rfl⟩ : syracuseStep 12409517 = 4653569) B4653569
theorem B3873491 : Blo 1721061 3873491 := bstep (se 1 (by rfl) ⟨2905118, by rfl⟩ : syracuseStep 3873491 = 5810237) B5810237
theorem B11033347 : Blo 1721061 11033347 := bstep (se 1 (by rfl) ⟨8275010, by rfl⟩ : syracuseStep 11033347 = 16550021) B16550021
theorem B2906975 : Blo 1721061 2906975 := bstep (se 1 (by rfl) ⟨2180231, by rfl⟩ : syracuseStep 2906975 = 4360463) B4360463
theorem B2759567 : Blo 1721061 2759567 := bstep (se 1 (by rfl) ⟨2069675, by rfl⟩ : syracuseStep 2759567 = 4139351) B4139351
theorem B3267515 : Blo 1721061 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B6536123 : Blo 1721061 6536123 := bstep (se 1 (by rfl) ⟨4902092, by rfl⟩ : syracuseStep 6536123 = 9804185) B9804185
theorem B1793063 : Blo 1721061 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B2178247 : Blo 1721061 2178247 := bstep (se 1 (by rfl) ⟨1633685, by rfl⟩ : syracuseStep 2178247 = 3267371) B3267371
theorem B2907535 : Blo 1721061 2907535 := bstep (se 1 (by rfl) ⟨2180651, by rfl⟩ : syracuseStep 2907535 = 4361303) B4361303
theorem B3268001 : Blo 1721061 3268001 := bstep (se 2 (by rfl) ⟨1225500, by rfl⟩ : syracuseStep 3268001 = 2451001) B2451001
theorem B3104183 : Blo 1721061 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B3104219 : Blo 1721061 3104219 := bstep (se 1 (by rfl) ⟨2328164, by rfl⟩ : syracuseStep 3104219 = 4656329) B4656329
theorem B3874427 : Blo 1721061 3874427 := bstep (se 1 (by rfl) ⟨2905820, by rfl⟩ : syracuseStep 3874427 = 5811641) B5811641
theorem B8715923 : Blo 1721061 8715923 := bstep (se 1 (by rfl) ⟨6536942, by rfl⟩ : syracuseStep 8715923 = 13073885) B13073885
theorem B3268343 : Blo 1721061 3268343 := bstep (se 1 (by rfl) ⟨2451257, by rfl⟩ : syracuseStep 3268343 = 4902515) B4902515
theorem B3874553 : Blo 1721061 3874553 := bstep (se 2 (by rfl) ⟨1452957, by rfl⟩ : syracuseStep 3874553 = 2905915) B2905915
theorem B7855967 : Blo 1721061 7855967 := bstep (se 1 (by rfl) ⟨5891975, by rfl⟩ : syracuseStep 7855967 = 11783951) B11783951
theorem B2178991 : Blo 1721061 2178991 := bstep (se 1 (by rfl) ⟨1634243, by rfl⟩ : syracuseStep 2178991 = 3268487) B3268487
theorem B4358063 : Blo 1721061 4358063 := bstep (se 1 (by rfl) ⟨3268547, by rfl⟩ : syracuseStep 4358063 = 6537095) B6537095
theorem B14712839 : Blo 1721061 14712839 := bstep (se 1 (by rfl) ⟨11034629, by rfl⟩ : syracuseStep 14712839 = 22069259) B22069259
theorem B13082633 : Blo 1721061 13082633 := bstep (se 2 (by rfl) ⟨4905987, by rfl⟩ : syracuseStep 13082633 = 9811975) B9811975
theorem B4137065 : Blo 1721061 4137065 := bstep (se 2 (by rfl) ⟨1551399, by rfl⟩ : syracuseStep 4137065 = 3102799) B3102799
theorem B7356521 : Blo 1721061 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B71631053 : Blo 1721061 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B3875183 : Blo 1721061 3875183 := bstep (se 1 (by rfl) ⟨2906387, by rfl⟩ : syracuseStep 3875183 = 5812775) B5812775
theorem B3875255 : Blo 1721061 3875255 := bstep (se 1 (by rfl) ⟨2906441, by rfl⟩ : syracuseStep 3875255 = 5812883) B5812883
theorem B3678689 : Blo 1721061 3678689 := bstep (se 2 (by rfl) ⟨1379508, by rfl⟩ : syracuseStep 3678689 = 2759017) B2759017
theorem B3727891 : Blo 1721061 3727891 := bstep (se 1 (by rfl) ⟨2795918, by rfl⟩ : syracuseStep 3727891 = 5591837) B5591837
theorem B150962723 : Blo 1721061 150962723 := bstep (se 1 (by rfl) ⟨113222042, by rfl⟩ : syracuseStep 150962723 = 226444085) B226444085
theorem B3875399 : Blo 1721061 3875399 := bstep (se 1 (by rfl) ⟨2906549, by rfl⟩ : syracuseStep 3875399 = 5813099) B5813099
theorem B3875435 : Blo 1721061 3875435 := bstep (se 1 (by rfl) ⟨2906576, by rfl⟩ : syracuseStep 3875435 = 5813153) B5813153
theorem B29836025 : Blo 1721061 29836025 := bstep (se 2 (by rfl) ⟨11188509, by rfl⟩ : syracuseStep 29836025 = 22377019) B22377019
theorem B1721135 : Blo 1721061 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B4359055 : Blo 1721061 4359055 := bstep (se 1 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 4359055 = 6538583) B6538583
theorem B1721243 : Blo 1721061 1721243 := bstep (se 1 (by rfl) ⟨1290932, by rfl⟩ : syracuseStep 1721243 = 2581865) B2581865
theorem B1721295 : Blo 1721061 1721295 := bstep (se 1 (by rfl) ⟨1290971, by rfl⟩ : syracuseStep 1721295 = 2581943) B2581943
theorem B1721319 : Blo 1721061 1721319 := bstep (se 1 (by rfl) ⟨1290989, by rfl⟩ : syracuseStep 1721319 = 2581979) B2581979
theorem B4137959 : Blo 1721061 4137959 := bstep (se 1 (by rfl) ⟨3103469, by rfl⟩ : syracuseStep 4137959 = 6206939) B6206939
theorem B3875831 : Blo 1721061 3875831 := bstep (se 1 (by rfl) ⟨2906873, by rfl⟩ : syracuseStep 3875831 = 5813747) B5813747
theorem B4654219 : Blo 1721061 4654219 := bstep (se 1 (by rfl) ⟨3490664, by rfl⟩ : syracuseStep 4654219 = 6981329) B6981329
theorem B2450665 : Blo 1721061 2450665 := bstep (se 2 (by rfl) ⟨918999, by rfl⟩ : syracuseStep 2450665 = 1837999) B1837999
theorem B1721631 : Blo 1721061 1721631 := bstep (se 1 (by rfl) ⟨1291223, by rfl⟩ : syracuseStep 1721631 = 2582447) B2582447
theorem B2581799 : Blo 1721061 2581799 := bstep (se 1 (by rfl) ⟨1936349, by rfl⟩ : syracuseStep 2581799 = 3872699) B3872699
theorem B8275243 : Blo 1721061 8275243 := bstep (se 1 (by rfl) ⟨6206432, by rfl⟩ : syracuseStep 8275243 = 12412865) B12412865
theorem B94233901 : Blo 1721061 94233901 := bstep (se 3 (by rfl) ⟨17668856, by rfl⟩ : syracuseStep 94233901 = 35337713) B35337713
theorem B19613015 : Blo 1721061 19613015 := bstep (se 1 (by rfl) ⟨14709761, by rfl⟩ : syracuseStep 19613015 = 29419523) B29419523
theorem B1721691 : Blo 1721061 1721691 := bstep (se 1 (by rfl) ⟨1291268, by rfl⟩ : syracuseStep 1721691 = 2582537) B2582537
theorem B4359521 : Blo 1721061 4359521 := bstep (se 2 (by rfl) ⟨1634820, by rfl⟩ : syracuseStep 4359521 = 3269641) B3269641
theorem B3876191 : Blo 1721061 3876191 := bstep (se 1 (by rfl) ⟨2907143, by rfl⟩ : syracuseStep 3876191 = 5814287) B5814287
theorem B23577965 : Blo 1721061 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B1721711 : Blo 1721061 1721711 := bstep (se 1 (by rfl) ⟨1291283, by rfl⟩ : syracuseStep 1721711 = 2582567) B2582567
theorem B2581883 : Blo 1721061 2581883 := bstep (se 1 (by rfl) ⟨1936412, by rfl⟩ : syracuseStep 2581883 = 3872825) B3872825
theorem B1721767 : Blo 1721061 1721767 := bstep (se 1 (by rfl) ⟨1291325, by rfl⟩ : syracuseStep 1721767 = 2582651) B2582651
theorem B16541101 : Blo 1721061 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B4310459 : Blo 1721061 4310459 := bstep (se 1 (by rfl) ⟨3232844, by rfl⟩ : syracuseStep 4310459 = 6465689) B6465689
theorem B2582009 : Blo 1721061 2582009 := bstep (se 2 (by rfl) ⟨968253, by rfl⟩ : syracuseStep 2582009 = 1936507) B1936507
theorem B1721851 : Blo 1721061 1721851 := bstep (se 1 (by rfl) ⟨1291388, by rfl⟩ : syracuseStep 1721851 = 2582777) B2582777
theorem B1721919 : Blo 1721061 1721919 := bstep (se 1 (by rfl) ⟨1291439, by rfl⟩ : syracuseStep 1721919 = 2582879) B2582879
theorem B1721927 : Blo 1721061 1721927 := bstep (se 1 (by rfl) ⟨1291445, by rfl⟩ : syracuseStep 1721927 = 2582891) B2582891
theorem B2582111 : Blo 1721061 2582111 := bstep (se 1 (by rfl) ⟨1936583, by rfl⟩ : syracuseStep 2582111 = 3873167) B3873167
theorem B1722079 : Blo 1721061 1722079 := bstep (se 1 (by rfl) ⟨1291559, by rfl⟩ : syracuseStep 1722079 = 2583119) B2583119
theorem B3876587 : Blo 1721061 3876587 := bstep (se 1 (by rfl) ⟨2907440, by rfl⟩ : syracuseStep 3876587 = 5814881) B5814881
theorem B4359977 : Blo 1721061 4359977 := bstep (se 2 (by rfl) ⟨1634991, by rfl⟩ : syracuseStep 4359977 = 3269983) B3269983
theorem B1722159 : Blo 1721061 1722159 := bstep (se 1 (by rfl) ⟨1291619, by rfl⟩ : syracuseStep 1722159 = 2583239) B2583239
theorem B2582327 : Blo 1721061 2582327 := bstep (se 1 (by rfl) ⟨1936745, by rfl⟩ : syracuseStep 2582327 = 3873491) B3873491
theorem B3925865 : Blo 1721061 3925865 := bstep (se 2 (by rfl) ⟨1472199, by rfl⟩ : syracuseStep 3925865 = 2944399) B2944399
theorem B3876713 : Blo 1721061 3876713 := bstep (se 2 (by rfl) ⟨1453767, by rfl⟩ : syracuseStep 3876713 = 2907535) B2907535
theorem B1722267 : Blo 1721061 1722267 := bstep (se 1 (by rfl) ⟨1291700, by rfl⟩ : syracuseStep 1722267 = 2583401) B2583401
theorem B1722319 : Blo 1721061 1722319 := bstep (se 1 (by rfl) ⟨1291739, by rfl⟩ : syracuseStep 1722319 = 2583479) B2583479
theorem B1722343 : Blo 1721061 1722343 := bstep (se 1 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 1722343 = 2583515) B2583515
theorem B2582633 : Blo 1721061 2582633 := bstep (se 2 (by rfl) ⟨968487, by rfl⟩ : syracuseStep 2582633 = 1936975) B1936975
theorem B1722655 : Blo 1721061 1722655 := bstep (se 1 (by rfl) ⟨1291991, by rfl⟩ : syracuseStep 1722655 = 2583983) B2583983
theorem B1722715 : Blo 1721061 1722715 := bstep (se 1 (by rfl) ⟨1292036, by rfl⟩ : syracuseStep 1722715 = 2584073) B2584073
theorem B1722735 : Blo 1721061 1722735 := bstep (se 1 (by rfl) ⟨1292051, by rfl⟩ : syracuseStep 1722735 = 2584103) B2584103
theorem B7358845 : Blo 1721061 7358845 := bstep (se 3 (by rfl) ⟨1379783, by rfl⟩ : syracuseStep 7358845 = 2759567) B2759567
theorem B2582951 : Blo 1721061 2582951 := bstep (se 1 (by rfl) ⟨1937213, by rfl⟩ : syracuseStep 2582951 = 3874427) B3874427
theorem B1722791 : Blo 1721061 1722791 := bstep (se 1 (by rfl) ⟨1292093, by rfl⟩ : syracuseStep 1722791 = 2584187) B2584187
theorem B5810615 : Blo 1721061 5810615 := bstep (se 1 (by rfl) ⟨4357961, by rfl⟩ : syracuseStep 5810615 = 8715923) B8715923
theorem B2583035 : Blo 1721061 2583035 := bstep (se 1 (by rfl) ⟨1937276, by rfl⟩ : syracuseStep 2583035 = 3874553) B3874553
theorem B1722875 : Blo 1721061 1722875 := bstep (se 1 (by rfl) ⟨1292156, by rfl⟩ : syracuseStep 1722875 = 2584313) B2584313
theorem B5237311 : Blo 1721061 5237311 := bstep (se 1 (by rfl) ⟨3927983, by rfl⟩ : syracuseStep 5237311 = 7855967) B7855967
theorem B1722943 : Blo 1721061 1722943 := bstep (se 1 (by rfl) ⟨1292207, by rfl⟩ : syracuseStep 1722943 = 2584415) B2584415
theorem B1722951 : Blo 1721061 1722951 := bstep (se 1 (by rfl) ⟨1292213, by rfl⟩ : syracuseStep 1722951 = 2584427) B2584427
theorem B2583161 : Blo 1721061 2583161 := bstep (se 2 (by rfl) ⟨968685, by rfl⟩ : syracuseStep 2583161 = 1937371) B1937371
theorem B2583215 : Blo 1721061 2583215 := bstep (se 1 (by rfl) ⟨1937411, by rfl⟩ : syracuseStep 2583215 = 3874823) B3874823
theorem B2452151 : Blo 1721061 2452151 := bstep (se 1 (by rfl) ⟨1839113, by rfl⟩ : syracuseStep 2452151 = 3678227) B3678227
theorem B2583263 : Blo 1721061 2583263 := bstep (se 1 (by rfl) ⟨1937447, by rfl⟩ : syracuseStep 2583263 = 3874895) B3874895
theorem B4360979 : Blo 1721061 4360979 := bstep (se 1 (by rfl) ⟨3270734, by rfl⟩ : syracuseStep 4360979 = 6541469) B6541469
theorem B29821745 : Blo 1721061 29821745 := bstep (se 2 (by rfl) ⟨11183154, by rfl⟩ : syracuseStep 29821745 = 22366309) B22366309
theorem B2583527 : Blo 1721061 2583527 := bstep (se 1 (by rfl) ⟨1937645, by rfl⟩ : syracuseStep 2583527 = 3875291) B3875291
theorem B226446353 : Blo 1721061 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B22056137 : Blo 1721061 22056137 := bstep (se 2 (by rfl) ⟨8271051, by rfl⟩ : syracuseStep 22056137 = 16542103) B16542103
theorem B4361435 : Blo 1721061 4361435 := bstep (se 1 (by rfl) ⟨3271076, by rfl⟩ : syracuseStep 4361435 = 6542153) B6542153
theorem B2583785 : Blo 1721061 2583785 := bstep (se 2 (by rfl) ⟨968919, by rfl⟩ : syracuseStep 2583785 = 1937839) B1937839
theorem B4361465 : Blo 1721061 4361465 := bstep (se 2 (by rfl) ⟨1635549, by rfl⟩ : syracuseStep 4361465 = 3271099) B3271099
theorem B13962527 : Blo 1721061 13962527 := bstep (se 1 (by rfl) ⟨10471895, by rfl⟩ : syracuseStep 13962527 = 20943791) B20943791
theorem B2583839 : Blo 1721061 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B4902241 : Blo 1721061 4902241 := bstep (se 2 (by rfl) ⟨1838340, by rfl⟩ : syracuseStep 4902241 = 3676681) B3676681
theorem B5238113 : Blo 1721061 5238113 := bstep (se 2 (by rfl) ⟨1964292, by rfl⟩ : syracuseStep 5238113 = 3928585) B3928585
theorem B2584007 : Blo 1721061 2584007 := bstep (se 1 (by rfl) ⟨1938005, by rfl⟩ : syracuseStep 2584007 = 3876011) B3876011
theorem B9309779 : Blo 1721061 9309779 := bstep (se 1 (by rfl) ⟨6982334, by rfl⟩ : syracuseStep 9309779 = 13964669) B13964669
theorem B5893715 : Blo 1721061 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B13069997 : Blo 1721061 13069997 := bstep (se 3 (by rfl) ⟨2450624, by rfl⟩ : syracuseStep 13069997 = 4901249) B4901249
theorem B18616007 : Blo 1721061 18616007 := bstep (se 1 (by rfl) ⟨13962005, by rfl⟩ : syracuseStep 18616007 = 27924011) B27924011
theorem B1937119 : Blo 1721061 1937119 := bstep (se 1 (by rfl) ⟨1452839, by rfl⟩ : syracuseStep 1937119 = 2905679) B2905679
theorem B106000109 : Blo 1721061 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B8720135 : Blo 1721061 8720135 := bstep (se 1 (by rfl) ⟨6540101, by rfl⟩ : syracuseStep 8720135 = 13080203) B13080203
theorem B2584361 : Blo 1721061 2584361 := bstep (se 2 (by rfl) ⟨969135, by rfl⟩ : syracuseStep 2584361 = 1938271) B1938271
theorem B4656943 : Blo 1721061 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B2584367 : Blo 1721061 2584367 := bstep (se 1 (by rfl) ⟨1938275, by rfl⟩ : syracuseStep 2584367 = 3876551) B3876551
theorem B30240971 : Blo 1721061 30240971 := bstep (se 1 (by rfl) ⟨22680728, by rfl⟩ : syracuseStep 30240971 = 45361457) B45361457
theorem B6983891 : Blo 1721061 6983891 := bstep (se 1 (by rfl) ⟨5237918, by rfl⟩ : syracuseStep 6983891 = 10475837) B10475837
theorem B125702405 : Blo 1721061 125702405 := bstep (se 4 (by rfl) ⟨11784600, by rfl⟩ : syracuseStep 125702405 = 23569201) B23569201
theorem B2904329 : Blo 1721061 2904329 := bstep (se 2 (by rfl) ⟨1089123, by rfl⟩ : syracuseStep 2904329 = 2178247) B2178247
theorem B1937695 : Blo 1721061 1937695 := bstep (se 1 (by rfl) ⟨1453271, by rfl⟩ : syracuseStep 1937695 = 2906543) B2906543
theorem B7852463 : Blo 1721061 7852463 := bstep (se 1 (by rfl) ⟨5889347, by rfl⟩ : syracuseStep 7852463 = 11778695) B11778695
theorem B1937983 : Blo 1721061 1937983 := bstep (se 1 (by rfl) ⟨1453487, by rfl⟩ : syracuseStep 1937983 = 2906975) B2906975
theorem B13070969 : Blo 1721061 13070969 := bstep (se 2 (by rfl) ⟨4901613, by rfl⟩ : syracuseStep 13070969 = 9803227) B9803227
theorem B5518007 : Blo 1721061 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B8270687 : Blo 1721061 8270687 := bstep (se 1 (by rfl) ⟨6203015, by rfl⟩ : syracuseStep 8270687 = 12406031) B12406031
theorem B2069455 : Blo 1721061 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B53023697 : Blo 1721061 53023697 := bstep (se 2 (by rfl) ⟨19883886, by rfl⟩ : syracuseStep 53023697 = 39767773) B39767773
theorem B2069479 : Blo 1721061 2069479 := bstep (se 1 (by rfl) ⟨1552109, by rfl⟩ : syracuseStep 2069479 = 3104219) B3104219
theorem B35353745 : Blo 1721061 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B2905321 : Blo 1721061 2905321 := bstep (se 2 (by rfl) ⟨1089495, by rfl⟩ : syracuseStep 2905321 = 2178991) B2178991
theorem B2905375 : Blo 1721061 2905375 := bstep (se 1 (by rfl) ⟨2179031, by rfl⟩ : syracuseStep 2905375 = 4358063) B4358063
theorem B2946343 : Blo 1721061 2946343 := bstep (se 1 (by rfl) ⟨2209757, by rfl⟩ : syracuseStep 2946343 = 4419515) B4419515
theorem B4781501 : Blo 1721061 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B5813693 : Blo 1721061 5813693 := bstep (se 3 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 5813693 = 2180135) B2180135
theorem B8713817 : Blo 1721061 8713817 := bstep (se 2 (by rfl) ⟨3267681, by rfl⟩ : syracuseStep 8713817 = 6535363) B6535363
theorem B2905787 : Blo 1721061 2905787 := bstep (se 1 (by rfl) ⟨2179340, by rfl⟩ : syracuseStep 2905787 = 4358681) B4358681
theorem B2758331 : Blo 1721061 2758331 := bstep (se 1 (by rfl) ⟨2068748, by rfl⟩ : syracuseStep 2758331 = 4137497) B4137497
theorem B3872519 : Blo 1721061 3872519 := bstep (se 1 (by rfl) ⟨2904389, by rfl⟩ : syracuseStep 3872519 = 5808779) B5808779
theorem B2619191 : Blo 1721061 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B5814071 : Blo 1721061 5814071 := bstep (se 1 (by rfl) ⟨4360553, by rfl⟩ : syracuseStep 5814071 = 8721107) B8721107
theorem B2758607 : Blo 1721061 2758607 := bstep (se 1 (by rfl) ⟨2068955, by rfl⟩ : syracuseStep 2758607 = 4137911) B4137911
theorem B13072427 : Blo 1721061 13072427 := bstep (se 1 (by rfl) ⟨9804320, by rfl⟩ : syracuseStep 13072427 = 19608641) B19608641
theorem B5380225 : Blo 1721061 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B15702295 : Blo 1721061 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B9812249 : Blo 1721061 9812249 := bstep (se 2 (by rfl) ⟨3679593, by rfl⟩ : syracuseStep 9812249 = 7359187) B7359187
theorem B5814557 : Blo 1721061 5814557 := bstep (se 3 (by rfl) ⟨1090229, by rfl⟩ : syracuseStep 5814557 = 2180459) B2180459
theorem B14711129 : Blo 1721061 14711129 := bstep (se 2 (by rfl) ⟨5516673, by rfl⟩ : syracuseStep 14711129 = 11033347) B11033347
theorem B4356443 : Blo 1721061 4356443 := bstep (se 1 (by rfl) ⟨3267332, by rfl⟩ : syracuseStep 4356443 = 6534665) B6534665
theorem B3873131 : Blo 1721061 3873131 := bstep (se 1 (by rfl) ⟨2904848, by rfl⟩ : syracuseStep 3873131 = 5809697) B5809697
theorem B4356463 : Blo 1721061 4356463 := bstep (se 1 (by rfl) ⟨3267347, by rfl⟩ : syracuseStep 4356463 = 6534695) B6534695
theorem B6986195 : Blo 1721061 6986195 := bstep (se 1 (by rfl) ⟨5239646, by rfl⟩ : syracuseStep 6986195 = 10479293) B10479293
theorem B3873275 : Blo 1721061 3873275 := bstep (se 1 (by rfl) ⟨2904956, by rfl⟩ : syracuseStep 3873275 = 5809913) B5809913
theorem B3873401 : Blo 1721061 3873401 := bstep (se 2 (by rfl) ⟨1452525, by rfl⟩ : syracuseStep 3873401 = 2905051) B2905051
theorem B3676843 : Blo 1721061 3676843 := bstep (se 1 (by rfl) ⟨2757632, by rfl⟩ : syracuseStep 3676843 = 5515265) B5515265
theorem B3873455 : Blo 1721061 3873455 := bstep (se 1 (by rfl) ⟨2905091, by rfl⟩ : syracuseStep 3873455 = 5810183) B5810183
theorem B4905647 : Blo 1721061 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B3873527 : Blo 1721061 3873527 := bstep (se 1 (by rfl) ⟨2905145, by rfl⟩ : syracuseStep 3873527 = 5810291) B5810291
theorem B3873707 : Blo 1721061 3873707 := bstep (se 1 (by rfl) ⟨2905280, by rfl⟩ : syracuseStep 3873707 = 5810561) B5810561
theorem B70728623 : Blo 1721061 70728623 := bstep (se 1 (by rfl) ⟨53046467, by rfl⟩ : syracuseStep 70728623 = 106092935) B106092935
theorem B4193255 : Blo 1721061 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B4357111 : Blo 1721061 4357111 := bstep (se 1 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 4357111 = 6535667) B6535667
theorem B8273011 : Blo 1721061 8273011 := bstep (se 1 (by rfl) ⟨6204758, by rfl⟩ : syracuseStep 8273011 = 12409517) B12409517
theorem B3267803 : Blo 1721061 3267803 := bstep (se 1 (by rfl) ⟨2450852, by rfl⟩ : syracuseStep 3267803 = 4901705) B4901705
theorem B2178343 : Blo 1721061 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B4357415 : Blo 1721061 4357415 := bstep (se 1 (by rfl) ⟨3268061, by rfl⟩ : syracuseStep 4357415 = 6536123) B6536123
theorem B2907515 : Blo 1721061 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B18619811 : Blo 1721061 18619811 := bstep (se 1 (by rfl) ⟨13964858, by rfl⟩ : syracuseStep 18619811 = 27929717) B27929717
theorem B3268039 : Blo 1721061 3268039 := bstep (se 1 (by rfl) ⟨2451029, by rfl⟩ : syracuseStep 3268039 = 4902059) B4902059
theorem B3874247 : Blo 1721061 3874247 := bstep (se 1 (by rfl) ⟨2905685, by rfl⟩ : syracuseStep 3874247 = 5811371) B5811371
theorem B4906489 : Blo 1721061 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B2178667 : Blo 1721061 2178667 := bstep (se 1 (by rfl) ⟨1634000, by rfl⟩ : syracuseStep 2178667 = 3268001) B3268001
theorem B3874607 : Blo 1721061 3874607 := bstep (se 1 (by rfl) ⟨2905955, by rfl⟩ : syracuseStep 3874607 = 5811911) B5811911
theorem B2178895 : Blo 1721061 2178895 := bstep (se 1 (by rfl) ⟨1634171, by rfl⟩ : syracuseStep 2178895 = 3268343) B3268343
theorem B20160647 : Blo 1721061 20160647 := bstep (se 1 (by rfl) ⟨15120485, by rfl⟩ : syracuseStep 20160647 = 30240971) B30240971
theorem B5234975 : Blo 1721061 5234975 := bstep (se 1 (by rfl) ⟨3926231, by rfl⟩ : syracuseStep 5234975 = 7852463) B7852463
theorem B3678671 : Blo 1721061 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B5808617 : Blo 1721061 5808617 := bstep (se 2 (by rfl) ⟨2178231, by rfl⟩ : syracuseStep 5808617 = 4356463) B4356463
theorem B19890683 : Blo 1721061 19890683 := bstep (se 1 (by rfl) ⟨14918012, by rfl⟩ : syracuseStep 19890683 = 29836025) B29836025
theorem B35349131 : Blo 1721061 35349131 := bstep (se 1 (by rfl) ⟨26511848, by rfl⟩ : syracuseStep 35349131 = 53023697) B53023697
theorem B23569163 : Blo 1721061 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B1721199 : Blo 1721061 1721199 := bstep (se 1 (by rfl) ⟨1290899, by rfl⟩ : syracuseStep 1721199 = 2581799) B2581799
theorem B13075343 : Blo 1721061 13075343 := bstep (se 1 (by rfl) ⟨9806507, by rfl⟩ : syracuseStep 13075343 = 19613015) B19613015
theorem B1721255 : Blo 1721061 1721255 := bstep (se 1 (by rfl) ⟨1290941, by rfl⟩ : syracuseStep 1721255 = 2581883) B2581883
theorem B13968301 : Blo 1721061 13968301 := bstep (se 3 (by rfl) ⟨2619056, by rfl⟩ : syracuseStep 13968301 = 5238113) B5238113
theorem B3187667 : Blo 1721061 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B3875795 : Blo 1721061 3875795 := bstep (se 1 (by rfl) ⟨2906846, by rfl⟩ : syracuseStep 3875795 = 5813693) B5813693
theorem B1721339 : Blo 1721061 1721339 := bstep (se 1 (by rfl) ⟨1291004, by rfl⟩ : syracuseStep 1721339 = 2582009) B2582009
theorem B5809211 : Blo 1721061 5809211 := bstep (se 1 (by rfl) ⟨4356908, by rfl⟩ : syracuseStep 5809211 = 8713817) B8713817
theorem B1721407 : Blo 1721061 1721407 := bstep (se 1 (by rfl) ⟨1291055, by rfl⟩ : syracuseStep 1721407 = 2582111) B2582111
theorem B2581679 : Blo 1721061 2581679 := bstep (se 1 (by rfl) ⟨1936259, by rfl⟩ : syracuseStep 2581679 = 3872519) B3872519
theorem B1721551 : Blo 1721061 1721551 := bstep (se 1 (by rfl) ⟨1291163, by rfl⟩ : syracuseStep 1721551 = 2582327) B2582327
theorem B1746127 : Blo 1721061 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B3876047 : Blo 1721061 3876047 := bstep (se 1 (by rfl) ⟨2907035, by rfl⟩ : syracuseStep 3876047 = 5814071) B5814071
theorem B5809481 : Blo 1721061 5809481 := bstep (se 2 (by rfl) ⟨2178555, by rfl⟩ : syracuseStep 5809481 = 4357111) B4357111
theorem B1721755 : Blo 1721061 1721755 := bstep (se 1 (by rfl) ⟨1291316, by rfl⟩ : syracuseStep 1721755 = 2582633) B2582633
theorem B3876371 : Blo 1721061 3876371 := bstep (se 1 (by rfl) ⟨2907278, by rfl⟩ : syracuseStep 3876371 = 5814557) B5814557
theorem B9807419 : Blo 1721061 9807419 := bstep (se 1 (by rfl) ⟨7355564, by rfl⟩ : syracuseStep 9807419 = 14711129) B14711129
theorem B2582087 : Blo 1721061 2582087 := bstep (se 1 (by rfl) ⟨1936565, by rfl⟩ : syracuseStep 2582087 = 3873131) B3873131
theorem B1721967 : Blo 1721061 1721967 := bstep (se 1 (by rfl) ⟨1291475, by rfl⟩ : syracuseStep 1721967 = 2582951) B2582951
theorem B2582183 : Blo 1721061 2582183 := bstep (se 1 (by rfl) ⟨1936637, by rfl⟩ : syracuseStep 2582183 = 3873275) B3873275
theorem B1722023 : Blo 1721061 1722023 := bstep (se 1 (by rfl) ⟨1291517, by rfl⟩ : syracuseStep 1722023 = 2583035) B2583035
theorem B2582267 : Blo 1721061 2582267 := bstep (se 1 (by rfl) ⟨1936700, by rfl⟩ : syracuseStep 2582267 = 3873401) B3873401
theorem B1722107 : Blo 1721061 1722107 := bstep (se 1 (by rfl) ⟨1291580, by rfl⟩ : syracuseStep 1722107 = 2583161) B2583161
theorem B2582303 : Blo 1721061 2582303 := bstep (se 1 (by rfl) ⟨1936727, by rfl⟩ : syracuseStep 2582303 = 3873455) B3873455
theorem B1722143 : Blo 1721061 1722143 := bstep (se 1 (by rfl) ⟨1291607, by rfl⟩ : syracuseStep 1722143 = 2583215) B2583215
theorem B3270431 : Blo 1721061 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B6539069 : Blo 1721061 6539069 := bstep (se 3 (by rfl) ⟨1226075, by rfl⟩ : syracuseStep 6539069 = 2452151) B2452151
theorem B1722175 : Blo 1721061 1722175 := bstep (se 1 (by rfl) ⟨1291631, by rfl⟩ : syracuseStep 1722175 = 2583263) B2583263
theorem B2582351 : Blo 1721061 2582351 := bstep (se 1 (by rfl) ⟨1936763, by rfl⟩ : syracuseStep 2582351 = 3873527) B3873527
theorem B22054801 : Blo 1721061 22054801 := bstep (se 2 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 22054801 = 16541101) B16541101
theorem B2582471 : Blo 1721061 2582471 := bstep (se 1 (by rfl) ⟨1936853, by rfl⟩ : syracuseStep 2582471 = 3873707) B3873707
theorem B1722351 : Blo 1721061 1722351 := bstep (se 1 (by rfl) ⟨1291763, by rfl⟩ : syracuseStep 1722351 = 2583527) B2583527
theorem B150964235 : Blo 1721061 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1722523 : Blo 1721061 1722523 := bstep (se 1 (by rfl) ⟨1291892, by rfl⟩ : syracuseStep 1722523 = 2583785) B2583785
theorem B9308351 : Blo 1721061 9308351 := bstep (se 1 (by rfl) ⟨6981263, by rfl⟩ : syracuseStep 9308351 = 13962527) B13962527
theorem B1722559 : Blo 1721061 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B22055165 : Blo 1721061 22055165 := bstep (se 3 (by rfl) ⟨4135343, by rfl⟩ : syracuseStep 22055165 = 8270687) B8270687
theorem B12413207 : Blo 1721061 12413207 := bstep (se 1 (by rfl) ⟨9309905, by rfl⟩ : syracuseStep 12413207 = 18619811) B18619811
theorem B2582825 : Blo 1721061 2582825 := bstep (se 2 (by rfl) ⟨968559, by rfl⟩ : syracuseStep 2582825 = 1937119) B1937119
theorem B2582831 : Blo 1721061 2582831 := bstep (se 1 (by rfl) ⟨1937123, by rfl⟩ : syracuseStep 2582831 = 3874247) B3874247
theorem B1722671 : Blo 1721061 1722671 := bstep (se 1 (by rfl) ⟨1292003, by rfl⟩ : syracuseStep 1722671 = 2584007) B2584007
theorem B70666739 : Blo 1721061 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B1722907 : Blo 1721061 1722907 := bstep (se 1 (by rfl) ⟨1292180, by rfl⟩ : syracuseStep 1722907 = 2584361) B2584361
theorem B2583071 : Blo 1721061 2583071 := bstep (se 1 (by rfl) ⟨1937303, by rfl⟩ : syracuseStep 2583071 = 3874607) B3874607
theorem B1722911 : Blo 1721061 1722911 := bstep (se 1 (by rfl) ⟨1292183, by rfl⟩ : syracuseStep 1722911 = 2584367) B2584367
theorem B11037221 : Blo 1721061 11037221 := bstep (se 4 (by rfl) ⟨1034739, by rfl⟩ : syracuseStep 11037221 = 2069479) B2069479
theorem B9808559 : Blo 1721061 9808559 := bstep (se 1 (by rfl) ⟨7356419, by rfl⟩ : syracuseStep 9808559 = 14712839) B14712839
theorem B47754035 : Blo 1721061 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B4655927 : Blo 1721061 4655927 := bstep (se 1 (by rfl) ⟨3491945, by rfl⟩ : syracuseStep 4655927 = 6983891) B6983891
theorem B1936219 : Blo 1721061 1936219 := bstep (se 1 (by rfl) ⟨1452164, by rfl⟩ : syracuseStep 1936219 = 2904329) B2904329
theorem B2583455 : Blo 1721061 2583455 := bstep (se 1 (by rfl) ⟨1937591, by rfl⟩ : syracuseStep 2583455 = 3875183) B3875183
theorem B2583503 : Blo 1721061 2583503 := bstep (se 1 (by rfl) ⟨1937627, by rfl⟩ : syracuseStep 2583503 = 3875255) B3875255
theorem B2452459 : Blo 1721061 2452459 := bstep (se 1 (by rfl) ⟨1839344, by rfl⟩ : syracuseStep 2452459 = 3678689) B3678689
theorem B100641815 : Blo 1721061 100641815 := bstep (se 1 (by rfl) ⟨75481361, by rfl⟩ : syracuseStep 100641815 = 150962723) B150962723
theorem B2583593 : Blo 1721061 2583593 := bstep (se 2 (by rfl) ⟨968847, by rfl⟩ : syracuseStep 2583593 = 1937695) B1937695
theorem B2583599 : Blo 1721061 2583599 := bstep (se 1 (by rfl) ⟨1937699, by rfl⟩ : syracuseStep 2583599 = 3875399) B3875399
theorem B2583623 : Blo 1721061 2583623 := bstep (se 1 (by rfl) ⟨1937717, by rfl⟩ : syracuseStep 2583623 = 3875435) B3875435
theorem B2583887 : Blo 1721061 2583887 := bstep (se 1 (by rfl) ⟨1937915, by rfl⟩ : syracuseStep 2583887 = 3875831) B3875831
theorem B6983081 : Blo 1721061 6983081 := bstep (se 2 (by rfl) ⟨2618655, by rfl⟩ : syracuseStep 6983081 = 5237311) B5237311
theorem B2583977 : Blo 1721061 2583977 := bstep (se 2 (by rfl) ⟨968991, by rfl⟩ : syracuseStep 2583977 = 1937983) B1937983
theorem B4902457 : Blo 1721061 4902457 := bstep (se 2 (by rfl) ⟨1838421, by rfl⟩ : syracuseStep 4902457 = 3676843) B3676843
theorem B2584127 : Blo 1721061 2584127 := bstep (se 1 (by rfl) ⟨1938095, by rfl⟩ : syracuseStep 2584127 = 3876191) B3876191
theorem B1937191 : Blo 1721061 1937191 := bstep (se 1 (by rfl) ⟨1452893, by rfl⟩ : syracuseStep 1937191 = 2905787) B2905787
theorem B2584391 : Blo 1721061 2584391 := bstep (se 1 (by rfl) ⟨1938293, by rfl⟩ : syracuseStep 2584391 = 3876587) B3876587
theorem B5812073 : Blo 1721061 5812073 := bstep (se 2 (by rfl) ⟨2179527, by rfl⟩ : syracuseStep 5812073 = 4359055) B4359055
theorem B2584475 : Blo 1721061 2584475 := bstep (se 1 (by rfl) ⟨1938356, by rfl⟩ : syracuseStep 2584475 = 3876713) B3876713
theorem B1839071 : Blo 1721061 1839071 := bstep (se 1 (by rfl) ⟨1379303, by rfl⟩ : syracuseStep 1839071 = 2758607) B2758607
theorem B11030681 : Blo 1721061 11030681 := bstep (se 2 (by rfl) ⟨4136505, by rfl⟩ : syracuseStep 11030681 = 8273011) B8273011
theorem B6205625 : Blo 1721061 6205625 := bstep (se 2 (by rfl) ⟨2327109, by rfl⟩ : syracuseStep 6205625 = 4654219) B4654219
theorem B6541499 : Blo 1721061 6541499 := bstep (se 1 (by rfl) ⟨4906124, by rfl⟩ : syracuseStep 6541499 = 9812249) B9812249
theorem B2904295 : Blo 1721061 2904295 := bstep (se 1 (by rfl) ⟨2178221, by rfl⟩ : syracuseStep 2904295 = 4356443) B4356443
theorem B4657463 : Blo 1721061 4657463 := bstep (se 1 (by rfl) ⟨3493097, by rfl⟩ : syracuseStep 4657463 = 6986195) B6986195
theorem B2904457 : Blo 1721061 2904457 := bstep (se 2 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 2904457 = 2178343) B2178343
theorem B3928457 : Blo 1721061 3928457 := bstep (se 2 (by rfl) ⟨1473171, by rfl⟩ : syracuseStep 3928457 = 2946343) B2946343
theorem B125645201 : Blo 1721061 125645201 := bstep (se 2 (by rfl) ⟨47116950, by rfl⟩ : syracuseStep 125645201 = 94233901) B94233901
theorem B6541985 : Blo 1721061 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B2904889 : Blo 1721061 2904889 := bstep (se 2 (by rfl) ⟨1089333, by rfl⟩ : syracuseStep 2904889 = 2178667) B2178667
theorem B2904943 : Blo 1721061 2904943 := bstep (se 1 (by rfl) ⟨2178707, by rfl⟩ : syracuseStep 2904943 = 4357415) B4357415
theorem B1938343 : Blo 1721061 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B6206519 : Blo 1721061 6206519 := bstep (se 1 (by rfl) ⟨4654889, by rfl⟩ : syracuseStep 6206519 = 9309779) B9309779
theorem B3929143 : Blo 1721061 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B2905193 : Blo 1721061 2905193 := bstep (se 2 (by rfl) ⟨1089447, by rfl⟩ : syracuseStep 2905193 = 2178895) B2178895
theorem B8713331 : Blo 1721061 8713331 := bstep (se 1 (by rfl) ⟨6534998, by rfl⟩ : syracuseStep 8713331 = 13069997) B13069997
theorem B5813423 : Blo 1721061 5813423 := bstep (se 1 (by rfl) ⟨4360067, by rfl⟩ : syracuseStep 5813423 = 8720135) B8720135
theorem B8721755 : Blo 1721061 8721755 := bstep (se 1 (by rfl) ⟨6541316, by rfl⟩ : syracuseStep 8721755 = 13082633) B13082633
theorem B2758043 : Blo 1721061 2758043 := bstep (se 1 (by rfl) ⟨2068532, by rfl⟩ : syracuseStep 2758043 = 4137065) B4137065
theorem B83801603 : Blo 1721061 83801603 := bstep (se 1 (by rfl) ⟨62851202, by rfl⟩ : syracuseStep 83801603 = 125702405) B125702405
theorem B19617389 : Blo 1721061 19617389 := bstep (se 3 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 19617389 = 7356521) B7356521
theorem B20936393 : Blo 1721061 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B8713979 : Blo 1721061 8713979 := bstep (se 1 (by rfl) ⟨6535484, by rfl⟩ : syracuseStep 8713979 = 13070969) B13070969
theorem B9811793 : Blo 1721061 9811793 := bstep (se 2 (by rfl) ⟨3679422, by rfl⟩ : syracuseStep 9811793 = 7358845) B7358845
theorem B8714141 : Blo 1721061 8714141 := bstep (se 3 (by rfl) ⟨1633901, by rfl⟩ : syracuseStep 8714141 = 3267803) B3267803
theorem B2758639 : Blo 1721061 2758639 := bstep (se 1 (by rfl) ⟨2068979, by rfl⟩ : syracuseStep 2758639 = 4137959) B4137959
theorem B28694533 : Blo 1721061 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B4970521 : Blo 1721061 4970521 := bstep (se 2 (by rfl) ⟨1863945, by rfl⟩ : syracuseStep 4970521 = 3727891) B3727891
theorem B2906347 : Blo 1721061 2906347 := bstep (se 1 (by rfl) ⟨2179760, by rfl⟩ : syracuseStep 2906347 = 4359521) B4359521
theorem B15718643 : Blo 1721061 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B2873639 : Blo 1721061 2873639 := bstep (se 1 (by rfl) ⟨2155229, by rfl⟩ : syracuseStep 2873639 = 4310459) B4310459
theorem B2906651 : Blo 1721061 2906651 := bstep (se 1 (by rfl) ⟨2179988, by rfl⟩ : syracuseStep 2906651 = 4359977) B4359977
theorem B2759273 : Blo 1721061 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B8714951 : Blo 1721061 8714951 := bstep (se 1 (by rfl) ⟨6536213, by rfl⟩ : syracuseStep 8714951 = 13072427) B13072427
theorem B24837029 : Blo 1721061 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B3873743 : Blo 1721061 3873743 := bstep (se 1 (by rfl) ⟨2905307, by rfl⟩ : syracuseStep 3873743 = 5810615) B5810615
theorem B3267553 : Blo 1721061 3267553 := bstep (se 2 (by rfl) ⟨1225332, by rfl⟩ : syracuseStep 3267553 = 2450665) B2450665
theorem B3873761 : Blo 1721061 3873761 := bstep (se 2 (by rfl) ⟨1452660, by rfl⟩ : syracuseStep 3873761 = 2905321) B2905321
theorem B3873833 : Blo 1721061 3873833 := bstep (se 2 (by rfl) ⟨1452687, by rfl⟩ : syracuseStep 3873833 = 2905375) B2905375
theorem B11033657 : Blo 1721061 11033657 := bstep (se 2 (by rfl) ⟨4137621, by rfl⟩ : syracuseStep 11033657 = 8275243) B8275243
theorem B6536321 : Blo 1721061 6536321 := bstep (se 2 (by rfl) ⟨2451120, by rfl⟩ : syracuseStep 6536321 = 4902241) B4902241
theorem B7355549 : Blo 1721061 7355549 := bstep (se 3 (by rfl) ⟨1379165, by rfl⟩ : syracuseStep 7355549 = 2758331) B2758331
theorem B2907319 : Blo 1721061 2907319 := bstep (se 1 (by rfl) ⟨2180489, by rfl⟩ : syracuseStep 2907319 = 4360979) B4360979
theorem B19881163 : Blo 1721061 19881163 := bstep (se 1 (by rfl) ⟨14910872, by rfl⟩ : syracuseStep 19881163 = 29821745) B29821745
theorem B4357385 : Blo 1721061 4357385 := bstep (se 2 (by rfl) ⟨1634019, by rfl⟩ : syracuseStep 4357385 = 3268039) B3268039
theorem B47152415 : Blo 1721061 47152415 := bstep (se 1 (by rfl) ⟨35364311, by rfl⟩ : syracuseStep 47152415 = 70728623) B70728623
theorem B14704091 : Blo 1721061 14704091 := bstep (se 1 (by rfl) ⟨11028068, by rfl⟩ : syracuseStep 14704091 = 22056137) B22056137
theorem B2907623 : Blo 1721061 2907623 := bstep (se 1 (by rfl) ⟨2180717, by rfl⟩ : syracuseStep 2907623 = 4361435) B4361435
theorem B2907643 : Blo 1721061 2907643 := bstep (se 1 (by rfl) ⟨2180732, by rfl⟩ : syracuseStep 2907643 = 4361465) B4361465
theorem B10468973 : Blo 1721061 10468973 := bstep (se 3 (by rfl) ⟨1962932, by rfl⟩ : syracuseStep 10468973 = 3925865) B3925865
theorem B12410671 : Blo 1721061 12410671 := bstep (se 1 (by rfl) ⟨9308003, by rfl⟩ : syracuseStep 12410671 = 18616007) B18616007
theorem B11182013 : Blo 1721061 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B6627361 : Blo 1721061 6627361 := bstep (se 2 (by rfl) ⟨2485260, by rfl⟩ : syracuseStep 6627361 = 4970521) B4970521
theorem B4137083 : Blo 1721061 4137083 := bstep (se 1 (by rfl) ⟨3102812, by rfl⟩ : syracuseStep 4137083 = 6205625) B6205625
theorem B3489983 : Blo 1721061 3489983 := bstep (se 1 (by rfl) ⟨2617487, by rfl⟩ : syracuseStep 3489983 = 5234975) B5234975
theorem B3104975 : Blo 1721061 3104975 := bstep (se 1 (by rfl) ⟨2328731, by rfl⟩ : syracuseStep 3104975 = 4657463) B4657463
theorem B83763467 : Blo 1721061 83763467 := bstep (se 1 (by rfl) ⟨62822600, by rfl⟩ : syracuseStep 83763467 = 125645201) B125645201
theorem B3875129 : Blo 1721061 3875129 := bstep (se 2 (by rfl) ⟨1453173, by rfl⟩ : syracuseStep 3875129 = 2906347) B2906347
theorem B15712775 : Blo 1721061 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B8716895 : Blo 1721061 8716895 := bstep (se 1 (by rfl) ⟨6537671, by rfl⟩ : syracuseStep 8716895 = 13075343) B13075343
theorem B4137679 : Blo 1721061 4137679 := bstep (se 1 (by rfl) ⟨3103259, by rfl⟩ : syracuseStep 4137679 = 6206519) B6206519
theorem B5808887 : Blo 1721061 5808887 := bstep (se 1 (by rfl) ⟨4356665, by rfl⟩ : syracuseStep 5808887 = 8713331) B8713331
theorem B125739773 : Blo 1721061 125739773 := bstep (se 3 (by rfl) ⟨23576207, by rfl⟩ : syracuseStep 125739773 = 47152415) B47152415
theorem B1721119 : Blo 1721061 1721119 := bstep (se 1 (by rfl) ⟨1290839, by rfl⟩ : syracuseStep 1721119 = 2581679) B2581679
theorem B3875615 : Blo 1721061 3875615 := bstep (se 1 (by rfl) ⟨2906711, by rfl⟩ : syracuseStep 3875615 = 5813423) B5813423
theorem B6538279 : Blo 1721061 6538279 := bstep (se 1 (by rfl) ⟨4903709, by rfl⟩ : syracuseStep 6538279 = 9807419) B9807419
theorem B1721391 : Blo 1721061 1721391 := bstep (se 1 (by rfl) ⟨1291043, by rfl⟩ : syracuseStep 1721391 = 2582087) B2582087
theorem B1721455 : Blo 1721061 1721455 := bstep (se 1 (by rfl) ⟨1291091, by rfl⟩ : syracuseStep 1721455 = 2582183) B2582183
theorem B2581625 : Blo 1721061 2581625 := bstep (se 2 (by rfl) ⟨968109, by rfl⟩ : syracuseStep 2581625 = 1936219) B1936219
theorem B5809319 : Blo 1721061 5809319 := bstep (se 1 (by rfl) ⟨4356989, by rfl⟩ : syracuseStep 5809319 = 8713979) B8713979
theorem B1721511 : Blo 1721061 1721511 := bstep (se 1 (by rfl) ⟨1291133, by rfl⟩ : syracuseStep 1721511 = 2582267) B2582267
theorem B1721535 : Blo 1721061 1721535 := bstep (se 1 (by rfl) ⟨1291151, by rfl⟩ : syracuseStep 1721535 = 2582303) B2582303
theorem B2180287 : Blo 1721061 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B4359379 : Blo 1721061 4359379 := bstep (se 1 (by rfl) ⟨3269534, by rfl⟩ : syracuseStep 4359379 = 6539069) B6539069
theorem B1721567 : Blo 1721061 1721567 := bstep (se 1 (by rfl) ⟨1291175, by rfl⟩ : syracuseStep 1721567 = 2582351) B2582351
theorem B5809427 : Blo 1721061 5809427 := bstep (se 1 (by rfl) ⟨4357070, by rfl⟩ : syracuseStep 5809427 = 8714141) B8714141
theorem B1721647 : Blo 1721061 1721647 := bstep (se 1 (by rfl) ⟨1291235, by rfl⟩ : syracuseStep 1721647 = 2582471) B2582471
theorem B3269945 : Blo 1721061 3269945 := bstep (se 2 (by rfl) ⟨1226229, by rfl⟩ : syracuseStep 3269945 = 2452459) B2452459
theorem B10479095 : Blo 1721061 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B1721883 : Blo 1721061 1721883 := bstep (se 1 (by rfl) ⟨1291412, by rfl⟩ : syracuseStep 1721883 = 2582825) B2582825
theorem B1721887 : Blo 1721061 1721887 := bstep (se 1 (by rfl) ⟨1291415, by rfl⟩ : syracuseStep 1721887 = 2582831) B2582831
theorem B3876425 : Blo 1721061 3876425 := bstep (se 2 (by rfl) ⟨1453659, by rfl⟩ : syracuseStep 3876425 = 2907319) B2907319
theorem B2328169 : Blo 1721061 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1722047 : Blo 1721061 1722047 := bstep (se 1 (by rfl) ⟨1291535, by rfl⟩ : syracuseStep 1722047 = 2583071) B2583071
theorem B7358147 : Blo 1721061 7358147 := bstep (se 1 (by rfl) ⟨5518610, by rfl⟩ : syracuseStep 7358147 = 11037221) B11037221
theorem B6539039 : Blo 1721061 6539039 := bstep (se 1 (by rfl) ⟨4904279, by rfl⟩ : syracuseStep 6539039 = 9808559) B9808559
theorem B5809967 : Blo 1721061 5809967 := bstep (se 1 (by rfl) ⟨4357475, by rfl⟩ : syracuseStep 5809967 = 8714951) B8714951
theorem B31836023 : Blo 1721061 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B1722303 : Blo 1721061 1722303 := bstep (se 1 (by rfl) ⟨1291727, by rfl⟩ : syracuseStep 1722303 = 2583455) B2583455
theorem B16558019 : Blo 1721061 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B2582495 : Blo 1721061 2582495 := bstep (se 1 (by rfl) ⟨1936871, by rfl⟩ : syracuseStep 2582495 = 3873743) B3873743
theorem B1722335 : Blo 1721061 1722335 := bstep (se 1 (by rfl) ⟨1291751, by rfl⟩ : syracuseStep 1722335 = 2583503) B2583503
theorem B2582507 : Blo 1721061 2582507 := bstep (se 1 (by rfl) ⟨1936880, by rfl⟩ : syracuseStep 2582507 = 3873761) B3873761
theorem B3876857 : Blo 1721061 3876857 := bstep (se 2 (by rfl) ⟨1453821, by rfl⟩ : syracuseStep 3876857 = 2907643) B2907643
theorem B67094543 : Blo 1721061 67094543 := bstep (se 1 (by rfl) ⟨50320907, by rfl⟩ : syracuseStep 67094543 = 100641815) B100641815
theorem B2582555 : Blo 1721061 2582555 := bstep (se 1 (by rfl) ⟨1936916, by rfl⟩ : syracuseStep 2582555 = 3873833) B3873833
theorem B1722395 : Blo 1721061 1722395 := bstep (se 1 (by rfl) ⟨1291796, by rfl⟩ : syracuseStep 1722395 = 2583593) B2583593
theorem B1722399 : Blo 1721061 1722399 := bstep (se 1 (by rfl) ⟨1291799, by rfl⟩ : syracuseStep 1722399 = 2583599) B2583599
theorem B1722415 : Blo 1721061 1722415 := bstep (se 1 (by rfl) ⟨1291811, by rfl⟩ : syracuseStep 1722415 = 2583623) B2583623
theorem B1722591 : Blo 1721061 1722591 := bstep (se 1 (by rfl) ⟨1291943, by rfl⟩ : syracuseStep 1722591 = 2583887) B2583887
theorem B4655387 : Blo 1721061 4655387 := bstep (se 1 (by rfl) ⟨3491540, by rfl⟩ : syracuseStep 4655387 = 6983081) B6983081
theorem B1722651 : Blo 1721061 1722651 := bstep (se 1 (by rfl) ⟨1291988, by rfl⟩ : syracuseStep 1722651 = 2583977) B2583977
theorem B1722751 : Blo 1721061 1722751 := bstep (se 1 (by rfl) ⟨1292063, by rfl⟩ : syracuseStep 1722751 = 2584127) B2584127
theorem B2582921 : Blo 1721061 2582921 := bstep (se 2 (by rfl) ⟨968595, by rfl⟩ : syracuseStep 2582921 = 1937191) B1937191
theorem B1722927 : Blo 1721061 1722927 := bstep (se 1 (by rfl) ⟨1292195, by rfl⟩ : syracuseStep 1722927 = 2584391) B2584391
theorem B1722983 : Blo 1721061 1722983 := bstep (se 1 (by rfl) ⟨1292237, by rfl⟩ : syracuseStep 1722983 = 2584475) B2584475
theorem B38259377 : Blo 1721061 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B4360999 : Blo 1721061 4360999 := bstep (se 1 (by rfl) ⟨3270749, by rfl⟩ : syracuseStep 4360999 = 6541499) B6541499
theorem B2452447 : Blo 1721061 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B4361323 : Blo 1721061 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B2125111 : Blo 1721061 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2583863 : Blo 1721061 2583863 := bstep (se 1 (by rfl) ⟨1937897, by rfl⟩ : syracuseStep 2583863 = 3875795) B3875795
theorem B1936795 : Blo 1721061 1936795 := bstep (se 1 (by rfl) ⟨1452596, by rfl⟩ : syracuseStep 1936795 = 2905193) B2905193
theorem B2584031 : Blo 1721061 2584031 := bstep (se 1 (by rfl) ⟨1938023, by rfl⟩ : syracuseStep 2584031 = 3876047) B3876047
theorem B1838695 : Blo 1721061 1838695 := bstep (se 1 (by rfl) ⟨1379021, by rfl⟩ : syracuseStep 1838695 = 2758043) B2758043
theorem B2584247 : Blo 1721061 2584247 := bstep (se 1 (by rfl) ⟨1938185, by rfl⟩ : syracuseStep 2584247 = 3876371) B3876371
theorem B13078259 : Blo 1721061 13078259 := bstep (se 1 (by rfl) ⟨9808694, by rfl⟩ : syracuseStep 13078259 = 19617389) B19617389
theorem B2584457 : Blo 1721061 2584457 := bstep (se 2 (by rfl) ⟨969171, by rfl⟩ : syracuseStep 2584457 = 1938343) B1938343
theorem B6541195 : Blo 1721061 6541195 := bstep (se 1 (by rfl) ⟨4905896, by rfl⟩ : syracuseStep 6541195 = 9811793) B9811793
theorem B18624401 : Blo 1721061 18624401 := bstep (se 2 (by rfl) ⟨6984150, by rfl⟩ : syracuseStep 18624401 = 13968301) B13968301
theorem B100642823 : Blo 1721061 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B5238857 : Blo 1721061 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B6205567 : Blo 1721061 6205567 := bstep (se 1 (by rfl) ⟨4654175, by rfl⟩ : syracuseStep 6205567 = 9308351) B9308351
theorem B1937767 : Blo 1721061 1937767 := bstep (se 1 (by rfl) ⟨1453325, by rfl⟩ : syracuseStep 1937767 = 2906651) B2906651
theorem B1839515 : Blo 1721061 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B4903699 : Blo 1721061 4903699 := bstep (se 1 (by rfl) ⟨3677774, by rfl⟩ : syracuseStep 4903699 = 7355549) B7355549
theorem B12415805 : Blo 1721061 12415805 := bstep (se 3 (by rfl) ⟨2327963, by rfl⟩ : syracuseStep 12415805 = 4655927) B4655927
theorem B2904923 : Blo 1721061 2904923 := bstep (se 1 (by rfl) ⟨2178692, by rfl⟩ : syracuseStep 2904923 = 4357385) B4357385
theorem B9802727 : Blo 1721061 9802727 := bstep (se 1 (by rfl) ⟨7352045, by rfl⟩ : syracuseStep 9802727 = 14704091) B14704091
theorem B1938415 : Blo 1721061 1938415 := bstep (se 1 (by rfl) ⟨1453811, by rfl⟩ : syracuseStep 1938415 = 2907623) B2907623
theorem B29406401 : Blo 1721061 29406401 := bstep (se 2 (by rfl) ⟨11027400, by rfl⟩ : syracuseStep 29406401 = 22054801) B22054801
theorem B4904189 : Blo 1721061 4904189 := bstep (se 3 (by rfl) ⟨919535, by rfl⟩ : syracuseStep 4904189 = 1839071) B1839071
theorem B13440431 : Blo 1721061 13440431 := bstep (se 1 (by rfl) ⟨10080323, by rfl⟩ : syracuseStep 13440431 = 20160647) B20160647
theorem B3872393 : Blo 1721061 3872393 := bstep (se 2 (by rfl) ⟨1452147, by rfl⟩ : syracuseStep 3872393 = 2904295) B2904295
theorem B3872411 : Blo 1721061 3872411 := bstep (se 1 (by rfl) ⟨2904308, by rfl⟩ : syracuseStep 3872411 = 5808617) B5808617
theorem B13260455 : Blo 1721061 13260455 := bstep (se 1 (by rfl) ⟨9945341, by rfl⟩ : syracuseStep 13260455 = 19890683) B19890683
theorem B29415149 : Blo 1721061 29415149 := bstep (se 3 (by rfl) ⟨5515340, by rfl⟩ : syracuseStep 29415149 = 11030681) B11030681
theorem B23566087 : Blo 1721061 23566087 := bstep (se 1 (by rfl) ⟨17674565, by rfl⟩ : syracuseStep 23566087 = 35349131) B35349131
theorem B3872609 : Blo 1721061 3872609 := bstep (se 2 (by rfl) ⟨1452228, by rfl⟩ : syracuseStep 3872609 = 2904457) B2904457
theorem B3872807 : Blo 1721061 3872807 := bstep (se 1 (by rfl) ⟨2904605, by rfl⟩ : syracuseStep 3872807 = 5809211) B5809211
theorem B33101885 : Blo 1721061 33101885 := bstep (se 3 (by rfl) ⟨6206603, by rfl⟩ : syracuseStep 33101885 = 12413207) B12413207
theorem B3872987 : Blo 1721061 3872987 := bstep (se 1 (by rfl) ⟨2904740, by rfl⟩ : syracuseStep 3872987 = 5809481) B5809481
theorem B5814503 : Blo 1721061 5814503 := bstep (se 1 (by rfl) ⟨4360877, by rfl⟩ : syracuseStep 5814503 = 8721755) B8721755
theorem B55867735 : Blo 1721061 55867735 := bstep (se 1 (by rfl) ⟨41900801, by rfl⟩ : syracuseStep 55867735 = 83801603) B83801603
theorem B10475885 : Blo 1721061 10475885 := bstep (se 3 (by rfl) ⟨1964228, by rfl⟩ : syracuseStep 10475885 = 3928457) B3928457
theorem B3873185 : Blo 1721061 3873185 := bstep (se 2 (by rfl) ⟨1452444, by rfl⟩ : syracuseStep 3873185 = 2904889) B2904889
theorem B13957595 : Blo 1721061 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B3873257 : Blo 1721061 3873257 := bstep (se 2 (by rfl) ⟨1452471, by rfl⟩ : syracuseStep 3873257 = 2904943) B2904943
theorem B4356737 : Blo 1721061 4356737 := bstep (se 2 (by rfl) ⟨1633776, by rfl⟩ : syracuseStep 4356737 = 3267553) B3267553
theorem B14703443 : Blo 1721061 14703443 := bstep (se 1 (by rfl) ⟨11027582, by rfl⟩ : syracuseStep 14703443 = 22055165) B22055165
theorem B1915759 : Blo 1721061 1915759 := bstep (se 1 (by rfl) ⟨1436819, by rfl⟩ : syracuseStep 1915759 = 2873639) B2873639
theorem B26508217 : Blo 1721061 26508217 := bstep (se 2 (by rfl) ⟨9940581, by rfl⟩ : syracuseStep 26508217 = 19881163) B19881163
theorem B27917261 : Blo 1721061 27917261 := bstep (se 3 (by rfl) ⟨5234486, by rfl⟩ : syracuseStep 27917261 = 10468973) B10468973
theorem B47111159 : Blo 1721061 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B7355771 : Blo 1721061 7355771 := bstep (se 1 (by rfl) ⟨5516828, by rfl⟩ : syracuseStep 7355771 = 11033657) B11033657
theorem B6536609 : Blo 1721061 6536609 := bstep (se 2 (by rfl) ⟨2451228, by rfl⟩ : syracuseStep 6536609 = 4902457) B4902457
theorem B4357547 : Blo 1721061 4357547 := bstep (se 1 (by rfl) ⟨3268160, by rfl⟩ : syracuseStep 4357547 = 6536321) B6536321
theorem B16547561 : Blo 1721061 16547561 := bstep (se 2 (by rfl) ⟨6205335, by rfl⟩ : syracuseStep 16547561 = 12410671) B12410671
theorem B3874715 : Blo 1721061 3874715 := bstep (se 1 (by rfl) ⟨2906036, by rfl⟩ : syracuseStep 3874715 = 5812073) B5812073
theorem B7454675 : Blo 1721061 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B3678185 : Blo 1721061 3678185 := bstep (se 2 (by rfl) ⟨1379319, by rfl⟩ : syracuseStep 3678185 = 2758639) B2758639
theorem B2326655 : Blo 1721061 2326655 := bstep (se 1 (by rfl) ⟨1744991, by rfl⟩ : syracuseStep 2326655 = 3489983) B3489983
theorem B8274089 : Blo 1721061 8274089 := bstep (se 2 (by rfl) ⟨3102783, by rfl⟩ : syracuseStep 8274089 = 6205567) B6205567
theorem B74490313 : Blo 1721061 74490313 := bstep (se 2 (by rfl) ⟨27933867, by rfl⟩ : syracuseStep 74490313 = 55867735) B55867735
theorem B1721083 : Blo 1721061 1721083 := bstep (se 1 (by rfl) ⟨1290812, by rfl⟩ : syracuseStep 1721083 = 2581625) B2581625
theorem B19604267 : Blo 1721061 19604267 := bstep (se 1 (by rfl) ⟨14703200, by rfl⟩ : syracuseStep 19604267 = 29406401) B29406401
theorem B3269459 : Blo 1721061 3269459 := bstep (se 1 (by rfl) ⟨2452094, by rfl⟩ : syracuseStep 3269459 = 4904189) B4904189
theorem B2179963 : Blo 1721061 2179963 := bstep (se 1 (by rfl) ⟨1634972, by rfl⟩ : syracuseStep 2179963 = 3269945) B3269945
theorem B6538265 : Blo 1721061 6538265 := bstep (se 2 (by rfl) ⟨2451849, by rfl⟩ : syracuseStep 6538265 = 4903699) B4903699
theorem B2581595 : Blo 1721061 2581595 := bstep (se 1 (by rfl) ⟨1936196, by rfl⟩ : syracuseStep 2581595 = 3872393) B3872393
theorem B2581607 : Blo 1721061 2581607 := bstep (se 1 (by rfl) ⟨1936205, by rfl⟩ : syracuseStep 2581607 = 3872411) B3872411
theorem B8840303 : Blo 1721061 8840303 := bstep (se 1 (by rfl) ⟨6630227, by rfl⟩ : syracuseStep 8840303 = 13260455) B13260455
theorem B35841149 : Blo 1721061 35841149 := bstep (se 3 (by rfl) ⟨6720215, by rfl⟩ : syracuseStep 35841149 = 13440431) B13440431
theorem B4359359 : Blo 1721061 4359359 := bstep (se 1 (by rfl) ⟨3269519, by rfl⟩ : syracuseStep 4359359 = 6539039) B6539039
theorem B2581739 : Blo 1721061 2581739 := bstep (se 1 (by rfl) ⟨1936304, by rfl⟩ : syracuseStep 2581739 = 3872609) B3872609
theorem B1721663 : Blo 1721061 1721663 := bstep (se 1 (by rfl) ⟨1291247, by rfl⟩ : syracuseStep 1721663 = 2582495) B2582495
theorem B1721671 : Blo 1721061 1721671 := bstep (se 1 (by rfl) ⟨1291253, by rfl⟩ : syracuseStep 1721671 = 2582507) B2582507
theorem B44729695 : Blo 1721061 44729695 := bstep (se 1 (by rfl) ⟨33547271, by rfl⟩ : syracuseStep 44729695 = 67094543) B67094543
theorem B1721703 : Blo 1721061 1721703 := bstep (se 1 (by rfl) ⟨1291277, by rfl⟩ : syracuseStep 1721703 = 2582555) B2582555
theorem B2581871 : Blo 1721061 2581871 := bstep (se 1 (by rfl) ⟨1936403, by rfl⟩ : syracuseStep 2581871 = 3872807) B3872807
theorem B8717705 : Blo 1721061 8717705 := bstep (se 2 (by rfl) ⟨3269139, by rfl⟩ : syracuseStep 8717705 = 6538279) B6538279
theorem B2581991 : Blo 1721061 2581991 := bstep (se 1 (by rfl) ⟨1936493, by rfl⟩ : syracuseStep 2581991 = 3872987) B3872987
theorem B3876335 : Blo 1721061 3876335 := bstep (se 1 (by rfl) ⟨2907251, by rfl⟩ : syracuseStep 3876335 = 5814503) B5814503
theorem B1721947 : Blo 1721061 1721947 := bstep (se 1 (by rfl) ⟨1291460, by rfl⟩ : syracuseStep 1721947 = 2582921) B2582921
theorem B2582123 : Blo 1721061 2582123 := bstep (se 1 (by rfl) ⟨1936592, by rfl⟩ : syracuseStep 2582123 = 3873185) B3873185
theorem B2582171 : Blo 1721061 2582171 := bstep (se 1 (by rfl) ⟨1936628, by rfl⟩ : syracuseStep 2582171 = 3873257) B3873257
theorem B2582393 : Blo 1721061 2582393 := bstep (se 2 (by rfl) ⟨968397, by rfl⟩ : syracuseStep 2582393 = 1936795) B1936795
theorem B2451593 : Blo 1721061 2451593 := bstep (se 2 (by rfl) ⟨919347, by rfl⟩ : syracuseStep 2451593 = 1838695) B1838695
theorem B1722575 : Blo 1721061 1722575 := bstep (se 1 (by rfl) ⟨1291931, by rfl⟩ : syracuseStep 1722575 = 2583863) B2583863
theorem B1722687 : Blo 1721061 1722687 := bstep (se 1 (by rfl) ⟨1292015, by rfl⟩ : syracuseStep 1722687 = 2584031) B2584031
theorem B1722831 : Blo 1721061 1722831 := bstep (se 1 (by rfl) ⟨1292123, by rfl⟩ : syracuseStep 1722831 = 2584247) B2584247
theorem B8718839 : Blo 1721061 8718839 := bstep (se 1 (by rfl) ⟨6539129, by rfl⟩ : syracuseStep 8718839 = 13078259) B13078259
theorem B1722971 : Blo 1721061 1722971 := bstep (se 1 (by rfl) ⟨1292228, by rfl⟩ : syracuseStep 1722971 = 2584457) B2584457
theorem B2583143 : Blo 1721061 2583143 := bstep (se 1 (by rfl) ⟨1937357, by rfl⟩ : syracuseStep 2583143 = 3874715) B3874715
theorem B2452123 : Blo 1721061 2452123 := bstep (se 1 (by rfl) ⟨1839092, by rfl⟩ : syracuseStep 2452123 = 3678185) B3678185
theorem B67095215 : Blo 1721061 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B3492571 : Blo 1721061 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B2583419 : Blo 1721061 2583419 := bstep (se 1 (by rfl) ⟨1937564, by rfl⟩ : syracuseStep 2583419 = 3875129) B3875129
theorem B5811263 : Blo 1721061 5811263 := bstep (se 1 (by rfl) ⟨4358447, by rfl⟩ : syracuseStep 5811263 = 8716895) B8716895
theorem B2583689 : Blo 1721061 2583689 := bstep (se 2 (by rfl) ⟨968883, by rfl⟩ : syracuseStep 2583689 = 1937767) B1937767
theorem B2583743 : Blo 1721061 2583743 := bstep (se 1 (by rfl) ⟨1937807, by rfl⟩ : syracuseStep 2583743 = 3875615) B3875615
theorem B8277203 : Blo 1721061 8277203 := bstep (se 1 (by rfl) ⟨6207902, by rfl⟩ : syracuseStep 8277203 = 12415805) B12415805
theorem B1936615 : Blo 1721061 1936615 := bstep (se 1 (by rfl) ⟨1452461, by rfl⟩ : syracuseStep 1936615 = 2904923) B2904923
theorem B5516905 : Blo 1721061 5516905 := bstep (se 2 (by rfl) ⟨2068839, by rfl⟩ : syracuseStep 5516905 = 4137679) B4137679
theorem B2584283 : Blo 1721061 2584283 := bstep (se 1 (by rfl) ⟨1938212, by rfl⟩ : syracuseStep 2584283 = 3876425) B3876425
theorem B35344289 : Blo 1721061 35344289 := bstep (se 2 (by rfl) ⟨13254108, by rfl⟩ : syracuseStep 35344289 = 26508217) B26508217
theorem B11038679 : Blo 1721061 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B2584553 : Blo 1721061 2584553 := bstep (se 2 (by rfl) ⟨969207, by rfl⟩ : syracuseStep 2584553 = 1938415) B1938415
theorem B2584571 : Blo 1721061 2584571 := bstep (se 1 (by rfl) ⟨1938428, by rfl⟩ : syracuseStep 2584571 = 3876857) B3876857
theorem B6983923 : Blo 1721061 6983923 := bstep (se 1 (by rfl) ⟨5237942, by rfl⟩ : syracuseStep 6983923 = 10475885) B10475885
theorem B5812505 : Blo 1721061 5812505 := bstep (se 2 (by rfl) ⟨2179689, by rfl⟩ : syracuseStep 5812505 = 4359379) B4359379
theorem B2904491 : Blo 1721061 2904491 := bstep (se 1 (by rfl) ⟨2178368, by rfl⟩ : syracuseStep 2904491 = 4356737) B4356737
theorem B25506251 : Blo 1721061 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B9802295 : Blo 1721061 9802295 := bstep (se 1 (by rfl) ⟨7351721, by rfl⟩ : syracuseStep 9802295 = 14703443) B14703443
theorem B4903847 : Blo 1721061 4903847 := bstep (se 1 (by rfl) ⟨3677885, by rfl⟩ : syracuseStep 4903847 = 7355771) B7355771
theorem B2905031 : Blo 1721061 2905031 := bstep (se 1 (by rfl) ⟨2178773, by rfl⟩ : syracuseStep 2905031 = 4357547) B4357547
theorem B31421449 : Blo 1721061 31421449 := bstep (se 2 (by rfl) ⟨11783043, by rfl⟩ : syracuseStep 31421449 = 23566087) B23566087
theorem B11031707 : Blo 1721061 11031707 := bstep (se 1 (by rfl) ⟨8273780, by rfl⟩ : syracuseStep 11031707 = 16547561) B16547561
theorem B13079717 : Blo 1721061 13079717 := bstep (se 4 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 13079717 = 2452447) B2452447
theorem B8721593 : Blo 1721061 8721593 := bstep (se 2 (by rfl) ⟨3270597, by rfl⟩ : syracuseStep 8721593 = 6541195) B6541195
theorem B12416267 : Blo 1721061 12416267 := bstep (se 1 (by rfl) ⟨9312200, by rfl⟩ : syracuseStep 12416267 = 18624401) B18624401
theorem B4969783 : Blo 1721061 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B8836481 : Blo 1721061 8836481 := bstep (se 2 (by rfl) ⟨3313680, by rfl⟩ : syracuseStep 8836481 = 6627361) B6627361
theorem B2758055 : Blo 1721061 2758055 := bstep (se 1 (by rfl) ⟨2068541, by rfl⟩ : syracuseStep 2758055 = 4137083) B4137083
theorem B2069983 : Blo 1721061 2069983 := bstep (se 1 (by rfl) ⟨1552487, by rfl⟩ : syracuseStep 2069983 = 3104975) B3104975
theorem B55842311 : Blo 1721061 55842311 := bstep (se 1 (by rfl) ⟨41881733, by rfl⟩ : syracuseStep 55842311 = 83763467) B83763467
theorem B10475183 : Blo 1721061 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B3872591 : Blo 1721061 3872591 := bstep (se 1 (by rfl) ⟨2904443, by rfl⟩ : syracuseStep 3872591 = 5808887) B5808887
theorem B83826515 : Blo 1721061 83826515 := bstep (se 1 (by rfl) ⟨62869886, by rfl⟩ : syracuseStep 83826515 = 125739773) B125739773
theorem B6535151 : Blo 1721061 6535151 := bstep (se 1 (by rfl) ⟨4901363, by rfl⟩ : syracuseStep 6535151 = 9802727) B9802727
theorem B3872879 : Blo 1721061 3872879 := bstep (se 1 (by rfl) ⟨2904659, by rfl⟩ : syracuseStep 3872879 = 5809319) B5809319
theorem B3872951 : Blo 1721061 3872951 := bstep (se 1 (by rfl) ⟨2904713, by rfl⟩ : syracuseStep 3872951 = 5809427) B5809427
theorem B6986063 : Blo 1721061 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B5814665 : Blo 1721061 5814665 := bstep (se 2 (by rfl) ⟨2180499, by rfl⟩ : syracuseStep 5814665 = 4360999) B4360999
theorem B4905373 : Blo 1721061 4905373 := bstep (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) B1839515
theorem B4905431 : Blo 1721061 4905431 := bstep (se 1 (by rfl) ⟨3679073, by rfl⟩ : syracuseStep 4905431 = 7358147) B7358147
theorem B2554345 : Blo 1721061 2554345 := bstep (se 2 (by rfl) ⟨957879, by rfl⟩ : syracuseStep 2554345 = 1915759) B1915759
theorem B19610099 : Blo 1721061 19610099 := bstep (se 1 (by rfl) ⟨14707574, by rfl⟩ : syracuseStep 19610099 = 29415149) B29415149
theorem B3873311 : Blo 1721061 3873311 := bstep (se 1 (by rfl) ⟨2904983, by rfl⟩ : syracuseStep 3873311 = 5809967) B5809967
theorem B21224015 : Blo 1721061 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B22067923 : Blo 1721061 22067923 := bstep (se 1 (by rfl) ⟨16550942, by rfl⟩ : syracuseStep 22067923 = 33101885) B33101885
theorem B5815097 : Blo 1721061 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B3103591 : Blo 1721061 3103591 := bstep (se 1 (by rfl) ⟨2327693, by rfl⟩ : syracuseStep 3103591 = 4655387) B4655387
theorem B2907049 : Blo 1721061 2907049 := bstep (se 2 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 2907049 = 2180287) B2180287
theorem B9305063 : Blo 1721061 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B2833481 : Blo 1721061 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B18611507 : Blo 1721061 18611507 := bstep (se 1 (by rfl) ⟨13958630, by rfl⟩ : syracuseStep 18611507 = 27917261) B27917261
theorem B31407439 : Blo 1721061 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B3104225 : Blo 1721061 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B4357739 : Blo 1721061 4357739 := bstep (se 1 (by rfl) ⟨3268304, by rfl⟩ : syracuseStep 4357739 = 6536609) B6536609
theorem B3875003 : Blo 1721061 3875003 := bstep (se 1 (by rfl) ⟨2906252, by rfl⟩ : syracuseStep 3875003 = 5812505) B5812505
theorem B6537581 : Blo 1721061 6537581 := bstep (se 3 (by rfl) ⟨1225796, by rfl⟩ : syracuseStep 6537581 = 2451593) B2451593
theorem B2179639 : Blo 1721061 2179639 := bstep (se 1 (by rfl) ⟨1634729, by rfl⟩ : syracuseStep 2179639 = 3269459) B3269459
theorem B99320417 : Blo 1721061 99320417 := bstep (se 2 (by rfl) ⟨37245156, by rfl⟩ : syracuseStep 99320417 = 74490313) B74490313
theorem B3269231 : Blo 1721061 3269231 := bstep (se 1 (by rfl) ⟨2451923, by rfl⟩ : syracuseStep 3269231 = 4903847) B4903847
theorem B4358843 : Blo 1721061 4358843 := bstep (se 1 (by rfl) ⟨3269132, by rfl⟩ : syracuseStep 4358843 = 6538265) B6538265
theorem B1721063 : Blo 1721061 1721063 := bstep (se 1 (by rfl) ⟨1290797, by rfl⟩ : syracuseStep 1721063 = 2581595) B2581595
theorem B1721071 : Blo 1721061 1721071 := bstep (se 1 (by rfl) ⟨1290803, by rfl⟩ : syracuseStep 1721071 = 2581607) B2581607
theorem B1721159 : Blo 1721061 1721159 := bstep (se 1 (by rfl) ⟨1290869, by rfl⟩ : syracuseStep 1721159 = 2581739) B2581739
theorem B3269497 : Blo 1721061 3269497 := bstep (se 2 (by rfl) ⟨1226061, by rfl⟩ : syracuseStep 3269497 = 2452123) B2452123
theorem B1721247 : Blo 1721061 1721247 := bstep (se 1 (by rfl) ⟨1290935, by rfl⟩ : syracuseStep 1721247 = 2581871) B2581871
theorem B5890987 : Blo 1721061 5890987 := bstep (se 1 (by rfl) ⟨4418240, by rfl⟩ : syracuseStep 5890987 = 8836481) B8836481
theorem B1721327 : Blo 1721061 1721327 := bstep (se 1 (by rfl) ⟨1290995, by rfl⟩ : syracuseStep 1721327 = 2581991) B2581991
theorem B1721415 : Blo 1721061 1721415 := bstep (se 1 (by rfl) ⟨1291061, by rfl⟩ : syracuseStep 1721415 = 2582123) B2582123
theorem B1721447 : Blo 1721061 1721447 := bstep (se 1 (by rfl) ⟨1291085, by rfl⟩ : syracuseStep 1721447 = 2582171) B2582171
theorem B4138121 : Blo 1721061 4138121 := bstep (se 2 (by rfl) ⟨1551795, by rfl⟩ : syracuseStep 4138121 = 3103591) B3103591
theorem B2581727 : Blo 1721061 2581727 := bstep (se 1 (by rfl) ⟨1936295, by rfl⟩ : syracuseStep 2581727 = 3872591) B3872591
theorem B3876065 : Blo 1721061 3876065 := bstep (se 2 (by rfl) ⟨1453524, by rfl⟩ : syracuseStep 3876065 = 2907049) B2907049
theorem B1721595 : Blo 1721061 1721595 := bstep (se 1 (by rfl) ⟨1291196, by rfl⟩ : syracuseStep 1721595 = 2582393) B2582393
theorem B2581919 : Blo 1721061 2581919 := bstep (se 1 (by rfl) ⟨1936439, by rfl⟩ : syracuseStep 2581919 = 3872879) B3872879
theorem B2581967 : Blo 1721061 2581967 := bstep (se 1 (by rfl) ⟨1936475, by rfl⟩ : syracuseStep 2581967 = 3872951) B3872951
theorem B3876443 : Blo 1721061 3876443 := bstep (se 1 (by rfl) ⟨2907332, by rfl⟩ : syracuseStep 3876443 = 5814665) B5814665
theorem B2582153 : Blo 1721061 2582153 := bstep (se 2 (by rfl) ⟨968307, by rfl⟩ : syracuseStep 2582153 = 1936615) B1936615
theorem B3270287 : Blo 1721061 3270287 := bstep (se 1 (by rfl) ⟨2452715, by rfl⟩ : syracuseStep 3270287 = 4905431) B4905431
theorem B2582207 : Blo 1721061 2582207 := bstep (se 1 (by rfl) ⟨1936655, by rfl⟩ : syracuseStep 2582207 = 3873311) B3873311
theorem B14149343 : Blo 1721061 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B1722095 : Blo 1721061 1722095 := bstep (se 1 (by rfl) ⟨1291571, by rfl⟩ : syracuseStep 1722095 = 2583143) B2583143
theorem B44730143 : Blo 1721061 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B59639593 : Blo 1721061 59639593 := bstep (se 2 (by rfl) ⟨22364847, by rfl⟩ : syracuseStep 59639593 = 44729695) B44729695
theorem B3876731 : Blo 1721061 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B1722279 : Blo 1721061 1722279 := bstep (se 1 (by rfl) ⟨1291709, by rfl⟩ : syracuseStep 1722279 = 2583419) B2583419
theorem B6203375 : Blo 1721061 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B1722459 : Blo 1721061 1722459 := bstep (se 1 (by rfl) ⟨1291844, by rfl⟩ : syracuseStep 1722459 = 2583689) B2583689
theorem B1722495 : Blo 1721061 1722495 := bstep (se 1 (by rfl) ⟨1291871, by rfl⟩ : syracuseStep 1722495 = 2583743) B2583743
theorem B1722855 : Blo 1721061 1722855 := bstep (se 1 (by rfl) ⟨1292141, by rfl⟩ : syracuseStep 1722855 = 2584283) B2584283
theorem B23562859 : Blo 1721061 23562859 := bstep (se 1 (by rfl) ⟨17672144, by rfl⟩ : syracuseStep 23562859 = 35344289) B35344289
theorem B7359119 : Blo 1721061 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B1723035 : Blo 1721061 1723035 := bstep (se 1 (by rfl) ⟨1292276, by rfl⟩ : syracuseStep 1723035 = 2584553) B2584553
theorem B1723047 : Blo 1721061 1723047 := bstep (se 1 (by rfl) ⟨1292285, by rfl⟩ : syracuseStep 1723047 = 2584571) B2584571
theorem B5516059 : Blo 1721061 5516059 := bstep (se 1 (by rfl) ⟨4137044, by rfl⟩ : syracuseStep 5516059 = 8274089) B8274089
theorem B7555949 : Blo 1721061 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B1936327 : Blo 1721061 1936327 := bstep (se 1 (by rfl) ⟨1452245, by rfl⟩ : syracuseStep 1936327 = 2904491) B2904491
theorem B6204413 : Blo 1721061 6204413 := bstep (se 3 (by rfl) ⟨1163327, by rfl⟩ : syracuseStep 6204413 = 2326655) B2326655
theorem B13069511 : Blo 1721061 13069511 := bstep (se 1 (by rfl) ⟨9802133, by rfl⟩ : syracuseStep 13069511 = 19604267) B19604267
theorem B6540497 : Blo 1721061 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B1936687 : Blo 1721061 1936687 := bstep (se 1 (by rfl) ⟨1452515, by rfl⟩ : syracuseStep 1936687 = 2905031) B2905031
theorem B5893535 : Blo 1721061 5893535 := bstep (se 1 (by rfl) ⟨4420151, by rfl⟩ : syracuseStep 5893535 = 8840303) B8840303
theorem B8719811 : Blo 1721061 8719811 := bstep (se 1 (by rfl) ⟨6539858, by rfl⟩ : syracuseStep 8719811 = 13079717) B13079717
theorem B8277511 : Blo 1721061 8277511 := bstep (se 1 (by rfl) ⟨6208133, by rfl⟩ : syracuseStep 8277511 = 12416267) B12416267
theorem B5811803 : Blo 1721061 5811803 := bstep (se 1 (by rfl) ⟨4358852, by rfl⟩ : syracuseStep 5811803 = 8717705) B8717705
theorem B4656761 : Blo 1721061 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2584223 : Blo 1721061 2584223 := bstep (se 1 (by rfl) ⟨1938167, by rfl⟩ : syracuseStep 2584223 = 3876335) B3876335
theorem B37228207 : Blo 1721061 37228207 := bstep (se 1 (by rfl) ⟨27921155, by rfl⟩ : syracuseStep 37228207 = 55842311) B55842311
theorem B4657375 : Blo 1721061 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B5812559 : Blo 1721061 5812559 := bstep (se 1 (by rfl) ⟨4359419, by rfl⟩ : syracuseStep 5812559 = 8718839) B8718839
theorem B5518135 : Blo 1721061 5518135 := bstep (se 1 (by rfl) ⟨4138601, by rfl⟩ : syracuseStep 5518135 = 8277203) B8277203
theorem B12407671 : Blo 1721061 12407671 := bstep (se 1 (by rfl) ⟨9305753, by rfl⟩ : syracuseStep 12407671 = 18611507) B18611507
theorem B2069483 : Blo 1721061 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B2905159 : Blo 1721061 2905159 := bstep (se 1 (by rfl) ⟨2178869, by rfl⟩ : syracuseStep 2905159 = 4357739) B4357739
theorem B167581061 : Blo 1721061 167581061 := bstep (se 4 (by rfl) ⟨15710724, by rfl⟩ : syracuseStep 167581061 = 31421449) B31421449
theorem B17004167 : Blo 1721061 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B9311897 : Blo 1721061 9311897 := bstep (se 2 (by rfl) ⟨3491961, by rfl⟩ : syracuseStep 9311897 = 6983923) B6983923
theorem B6534863 : Blo 1721061 6534863 := bstep (se 1 (by rfl) ⟨4901147, by rfl⟩ : syracuseStep 6534863 = 9802295) B9802295
theorem B23894099 : Blo 1721061 23894099 := bstep (se 1 (by rfl) ⟨17920574, by rfl⟩ : syracuseStep 23894099 = 35841149) B35841149
theorem B7354471 : Blo 1721061 7354471 := bstep (se 1 (by rfl) ⟨5515853, by rfl⟩ : syracuseStep 7354471 = 11031707) B11031707
theorem B5814395 : Blo 1721061 5814395 := bstep (se 1 (by rfl) ⟨4360796, by rfl⟩ : syracuseStep 5814395 = 8721593) B8721593
theorem B2906239 : Blo 1721061 2906239 := bstep (se 1 (by rfl) ⟨2179679, by rfl⟩ : syracuseStep 2906239 = 4359359) B4359359
theorem B29423897 : Blo 1721061 29423897 := bstep (se 2 (by rfl) ⟨11033961, by rfl⟩ : syracuseStep 29423897 = 22067923) B22067923
theorem B7354813 : Blo 1721061 7354813 := bstep (se 3 (by rfl) ⟨1379027, by rfl⟩ : syracuseStep 7354813 = 2758055) B2758055
theorem B2906617 : Blo 1721061 2906617 := bstep (se 2 (by rfl) ⟨1089981, by rfl⟩ : syracuseStep 2906617 = 2179963) B2179963
theorem B55884343 : Blo 1721061 55884343 := bstep (se 1 (by rfl) ⟨41913257, by rfl⟩ : syracuseStep 55884343 = 83826515) B83826515
theorem B4356767 : Blo 1721061 4356767 := bstep (se 1 (by rfl) ⟨3267575, by rfl⟩ : syracuseStep 4356767 = 6535151) B6535151
theorem B13073399 : Blo 1721061 13073399 := bstep (se 1 (by rfl) ⟨9805049, by rfl⟩ : syracuseStep 13073399 = 19610099) B19610099
theorem B6626377 : Blo 1721061 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B41876585 : Blo 1721061 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B27933821 : Blo 1721061 27933821 := bstep (se 3 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 27933821 = 10475183) B10475183
theorem B2759977 : Blo 1721061 2759977 := bstep (se 2 (by rfl) ⟨1034991, by rfl⟩ : syracuseStep 2759977 = 2069983) B2069983
theorem B3874175 : Blo 1721061 3874175 := bstep (se 1 (by rfl) ⟨2905631, by rfl⟩ : syracuseStep 3874175 = 5811263) B5811263
theorem B7355873 : Blo 1721061 7355873 := bstep (se 2 (by rfl) ⟨2758452, by rfl⟩ : syracuseStep 7355873 = 5516905) B5516905
theorem B13623173 : Blo 1721061 13623173 := bstep (se 4 (by rfl) ⟨1277172, by rfl⟩ : syracuseStep 13623173 = 2554345) B2554345
theorem B9805961 : Blo 1721061 9805961 := bstep (se 2 (by rfl) ⟨3677235, by rfl⟩ : syracuseStep 9805961 = 7354471) B7354471
theorem B3874985 : Blo 1721061 3874985 := bstep (se 2 (by rfl) ⟨1453119, by rfl⟩ : syracuseStep 3874985 = 2906239) B2906239
theorem B3875039 : Blo 1721061 3875039 := bstep (se 1 (by rfl) ⟨2906279, by rfl⟩ : syracuseStep 3875039 = 5812559) B5812559
theorem B4358387 : Blo 1721061 4358387 := bstep (se 1 (by rfl) ⟨3268790, by rfl⟩ : syracuseStep 4358387 = 6537581) B6537581
theorem B6209833 : Blo 1721061 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B2179487 : Blo 1721061 2179487 := bstep (se 1 (by rfl) ⟨1634615, by rfl⟩ : syracuseStep 2179487 = 3269231) B3269231
theorem B9806417 : Blo 1721061 9806417 := bstep (se 2 (by rfl) ⟨3677406, by rfl⟩ : syracuseStep 9806417 = 7354813) B7354813
theorem B3875489 : Blo 1721061 3875489 := bstep (se 2 (by rfl) ⟨1453308, by rfl⟩ : syracuseStep 3875489 = 2906617) B2906617
theorem B31417145 : Blo 1721061 31417145 := bstep (se 2 (by rfl) ⟨11781429, by rfl⟩ : syracuseStep 31417145 = 23562859) B23562859
theorem B1721151 : Blo 1721061 1721151 := bstep (se 1 (by rfl) ⟨1290863, by rfl⟩ : syracuseStep 1721151 = 2581727) B2581727
theorem B1721279 : Blo 1721061 1721279 := bstep (se 1 (by rfl) ⟨1290959, by rfl⟩ : syracuseStep 1721279 = 2581919) B2581919
theorem B1721311 : Blo 1721061 1721311 := bstep (se 1 (by rfl) ⟨1290983, by rfl⟩ : syracuseStep 1721311 = 2581967) B2581967
theorem B7357513 : Blo 1721061 7357513 := bstep (se 2 (by rfl) ⟨2759067, by rfl⟩ : syracuseStep 7357513 = 5518135) B5518135
theorem B1721435 : Blo 1721061 1721435 := bstep (se 1 (by rfl) ⟨1291076, by rfl⟩ : syracuseStep 1721435 = 2582153) B2582153
theorem B2180191 : Blo 1721061 2180191 := bstep (se 1 (by rfl) ⟨1635143, by rfl⟩ : syracuseStep 2180191 = 3270287) B3270287
theorem B1721471 : Blo 1721061 1721471 := bstep (se 1 (by rfl) ⟨1291103, by rfl⟩ : syracuseStep 1721471 = 2582207) B2582207
theorem B4359329 : Blo 1721061 4359329 := bstep (se 2 (by rfl) ⟨1634748, by rfl⟩ : syracuseStep 4359329 = 3269497) B3269497
theorem B29820095 : Blo 1721061 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B2581769 : Blo 1721061 2581769 := bstep (se 2 (by rfl) ⟨968163, by rfl⟩ : syracuseStep 2581769 = 1936327) B1936327
theorem B3876263 : Blo 1721061 3876263 := bstep (se 1 (by rfl) ⟨2907197, by rfl⟩ : syracuseStep 3876263 = 5814395) B5814395
theorem B2582249 : Blo 1721061 2582249 := bstep (se 2 (by rfl) ⟨968343, by rfl⟩ : syracuseStep 2582249 = 1936687) B1936687
theorem B11036681 : Blo 1721061 11036681 := bstep (se 2 (by rfl) ⟨4138755, by rfl⟩ : syracuseStep 11036681 = 8277511) B8277511
theorem B18622547 : Blo 1721061 18622547 := bstep (se 1 (by rfl) ⟨13966910, by rfl⟩ : syracuseStep 18622547 = 27933821) B27933821
theorem B4360331 : Blo 1721061 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B31418597 : Blo 1721061 31418597 := bstep (se 4 (by rfl) ⟨2945493, by rfl⟩ : syracuseStep 31418597 = 5890987) B5890987
theorem B49637609 : Blo 1721061 49637609 := bstep (se 2 (by rfl) ⟨18614103, by rfl⟩ : syracuseStep 49637609 = 37228207) B37228207
theorem B2582783 : Blo 1721061 2582783 := bstep (se 1 (by rfl) ⟨1937087, by rfl⟩ : syracuseStep 2582783 = 3874175) B3874175
theorem B1722815 : Blo 1721061 1722815 := bstep (se 1 (by rfl) ⟨1292111, by rfl⟩ : syracuseStep 1722815 = 2584223) B2584223
theorem B2583335 : Blo 1721061 2583335 := bstep (se 1 (by rfl) ⟨1937501, by rfl⟩ : syracuseStep 2583335 = 3875003) B3875003
theorem B2584043 : Blo 1721061 2584043 := bstep (se 1 (by rfl) ⟨1938032, by rfl⟩ : syracuseStep 2584043 = 3876065) B3876065
theorem B2584295 : Blo 1721061 2584295 := bstep (se 1 (by rfl) ⟨1938221, by rfl⟩ : syracuseStep 2584295 = 3876443) B3876443
theorem B9432895 : Blo 1721061 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B2584487 : Blo 1721061 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B15929399 : Blo 1721061 15929399 := bstep (se 1 (by rfl) ⟨11947049, by rfl⟩ : syracuseStep 15929399 = 23894099) B23894099
theorem B8835169 : Blo 1721061 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B19615931 : Blo 1721061 19615931 := bstep (se 1 (by rfl) ⟨14711948, by rfl⟩ : syracuseStep 19615931 = 29423897) B29423897
theorem B2904511 : Blo 1721061 2904511 := bstep (se 1 (by rfl) ⟨2178383, by rfl⟩ : syracuseStep 2904511 = 4356767) B4356767
theorem B8713007 : Blo 1721061 8713007 := bstep (se 1 (by rfl) ⟨6534755, by rfl⟩ : syracuseStep 8713007 = 13069511) B13069511
theorem B3929023 : Blo 1721061 3929023 := bstep (se 1 (by rfl) ⟨2946767, by rfl⟩ : syracuseStep 3929023 = 5893535) B5893535
theorem B5813207 : Blo 1721061 5813207 := bstep (se 1 (by rfl) ⟨4359905, by rfl⟩ : syracuseStep 5813207 = 8719811) B8719811
theorem B4903915 : Blo 1721061 4903915 := bstep (se 1 (by rfl) ⟨3677936, by rfl⟩ : syracuseStep 4903915 = 7355873) B7355873
theorem B9082115 : Blo 1721061 9082115 := bstep (se 1 (by rfl) ⟨6811586, by rfl⟩ : syracuseStep 9082115 = 13623173) B13623173
theorem B5518621 : Blo 1721061 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B66213611 : Blo 1721061 66213611 := bstep (se 1 (by rfl) ⟨49660208, by rfl⟩ : syracuseStep 66213611 = 99320417) B99320417
theorem B2905895 : Blo 1721061 2905895 := bstep (se 1 (by rfl) ⟨2179421, by rfl⟩ : syracuseStep 2905895 = 4358843) B4358843
theorem B2906185 : Blo 1721061 2906185 := bstep (se 2 (by rfl) ⟨1089819, by rfl⟩ : syracuseStep 2906185 = 2179639) B2179639
theorem B74512457 : Blo 1721061 74512457 := bstep (se 2 (by rfl) ⟨27942171, by rfl⟩ : syracuseStep 74512457 = 55884343) B55884343
theorem B2758747 : Blo 1721061 2758747 := bstep (se 1 (by rfl) ⟨2069060, by rfl⟩ : syracuseStep 2758747 = 4138121) B4138121
theorem B111720707 : Blo 1721061 111720707 := bstep (se 1 (by rfl) ⟨83790530, by rfl⟩ : syracuseStep 111720707 = 167581061) B167581061
theorem B7354745 : Blo 1721061 7354745 := bstep (se 2 (by rfl) ⟨2758029, by rfl⟩ : syracuseStep 7354745 = 5516059) B5516059
theorem B11336111 : Blo 1721061 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B6207931 : Blo 1721061 6207931 := bstep (se 1 (by rfl) ⟨4655948, by rfl⟩ : syracuseStep 6207931 = 9311897) B9311897
theorem B4356575 : Blo 1721061 4356575 := bstep (se 1 (by rfl) ⟨3267431, by rfl⟩ : syracuseStep 4356575 = 6534863) B6534863
theorem B4135583 : Blo 1721061 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B3873545 : Blo 1721061 3873545 := bstep (se 2 (by rfl) ⟨1452579, by rfl⟩ : syracuseStep 3873545 = 2905159) B2905159
theorem B14719877 : Blo 1721061 14719877 := bstep (se 4 (by rfl) ⟨1379988, by rfl⟩ : syracuseStep 14719877 = 2759977) B2759977
theorem B4906079 : Blo 1721061 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B5037299 : Blo 1721061 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B66174245 : Blo 1721061 66174245 := bstep (se 4 (by rfl) ⟨6203835, by rfl⟩ : syracuseStep 66174245 = 12407671) B12407671
theorem B8715599 : Blo 1721061 8715599 := bstep (se 1 (by rfl) ⟨6536699, by rfl⟩ : syracuseStep 8715599 = 13073399) B13073399
theorem B4136275 : Blo 1721061 4136275 := bstep (se 1 (by rfl) ⟨3102206, by rfl⟩ : syracuseStep 4136275 = 6204413) B6204413
theorem B27917723 : Blo 1721061 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B79519457 : Blo 1721061 79519457 := bstep (se 2 (by rfl) ⟨29819796, by rfl⟩ : syracuseStep 79519457 = 59639593) B59639593
theorem B3874535 : Blo 1721061 3874535 := bstep (se 1 (by rfl) ⟨2905901, by rfl⟩ : syracuseStep 3874535 = 5811803) B5811803
theorem B3104507 : Blo 1721061 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B6537307 : Blo 1721061 6537307 := bstep (se 1 (by rfl) ⟨4902980, by rfl⟩ : syracuseStep 6537307 = 9805961) B9805961
theorem B3874913 : Blo 1721061 3874913 := bstep (se 2 (by rfl) ⟨1453092, by rfl⟩ : syracuseStep 3874913 = 2906185) B2906185
theorem B3678329 : Blo 1721061 3678329 := bstep (se 2 (by rfl) ⟨1379373, by rfl⟩ : syracuseStep 3678329 = 2758747) B2758747
theorem B11780225 : Blo 1721061 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B6537611 : Blo 1721061 6537611 := bstep (se 1 (by rfl) ⟨4903208, by rfl⟩ : syracuseStep 6537611 = 9806417) B9806417
theorem B5808671 : Blo 1721061 5808671 := bstep (se 1 (by rfl) ⟨4356503, by rfl⟩ : syracuseStep 5808671 = 8713007) B8713007
theorem B3875471 : Blo 1721061 3875471 := bstep (se 1 (by rfl) ⟨2906603, by rfl⟩ : syracuseStep 3875471 = 5813207) B5813207
theorem B6054743 : Blo 1721061 6054743 := bstep (se 1 (by rfl) ⟨4541057, by rfl⟩ : syracuseStep 6054743 = 9082115) B9082115
theorem B1721179 : Blo 1721061 1721179 := bstep (se 1 (by rfl) ⟨1290884, by rfl⟩ : syracuseStep 1721179 = 2581769) B2581769
theorem B1721499 : Blo 1721061 1721499 := bstep (se 1 (by rfl) ⟨1291124, by rfl⟩ : syracuseStep 1721499 = 2582249) B2582249
theorem B6538553 : Blo 1721061 6538553 := bstep (se 2 (by rfl) ⟨2451957, by rfl⟩ : syracuseStep 6538553 = 4903915) B4903915
theorem B7357787 : Blo 1721061 7357787 := bstep (se 1 (by rfl) ⟨5518340, by rfl⟩ : syracuseStep 7357787 = 11036681) B11036681
theorem B1721855 : Blo 1721061 1721855 := bstep (se 1 (by rfl) ⟨1291391, by rfl⟩ : syracuseStep 1721855 = 2582783) B2582783
theorem B11028221 : Blo 1721061 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B2582363 : Blo 1721061 2582363 := bstep (se 1 (by rfl) ⟨1936772, by rfl⟩ : syracuseStep 2582363 = 3873545) B3873545
theorem B1722223 : Blo 1721061 1722223 := bstep (se 1 (by rfl) ⟨1291667, by rfl⟩ : syracuseStep 1722223 = 2583335) B2583335
theorem B3270719 : Blo 1721061 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B44116163 : Blo 1721061 44116163 := bstep (se 1 (by rfl) ⟨33087122, by rfl⟩ : syracuseStep 44116163 = 66174245) B66174245
theorem B5810399 : Blo 1721061 5810399 := bstep (se 1 (by rfl) ⟨4357799, by rfl⟩ : syracuseStep 5810399 = 8715599) B8715599
theorem B1722695 : Blo 1721061 1722695 := bstep (se 1 (by rfl) ⟨1292021, by rfl⟩ : syracuseStep 1722695 = 2584043) B2584043
theorem B12577193 : Blo 1721061 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B53012971 : Blo 1721061 53012971 := bstep (se 1 (by rfl) ⟨39759728, by rfl⟩ : syracuseStep 53012971 = 79519457) B79519457
theorem B2583023 : Blo 1721061 2583023 := bstep (se 1 (by rfl) ⟨1937267, by rfl⟩ : syracuseStep 2583023 = 3874535) B3874535
theorem B1722863 : Blo 1721061 1722863 := bstep (se 1 (by rfl) ⟨1292147, by rfl⟩ : syracuseStep 1722863 = 2584295) B2584295
theorem B1722991 : Blo 1721061 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B10619599 : Blo 1721061 10619599 := bstep (se 1 (by rfl) ⟨7964699, by rfl⟩ : syracuseStep 10619599 = 15929399) B15929399
theorem B2583323 : Blo 1721061 2583323 := bstep (se 1 (by rfl) ⟨1937492, by rfl⟩ : syracuseStep 2583323 = 3874985) B3874985
theorem B13077287 : Blo 1721061 13077287 := bstep (se 1 (by rfl) ⟨9807965, by rfl⟩ : syracuseStep 13077287 = 19615931) B19615931
theorem B2583359 : Blo 1721061 2583359 := bstep (se 1 (by rfl) ⟨1937519, by rfl⟩ : syracuseStep 2583359 = 3875039) B3875039
theorem B2583659 : Blo 1721061 2583659 := bstep (se 1 (by rfl) ⟨1937744, by rfl⟩ : syracuseStep 2583659 = 3875489) B3875489
theorem B8277241 : Blo 1721061 8277241 := bstep (se 2 (by rfl) ⟨3103965, by rfl⟩ : syracuseStep 8277241 = 6207931) B6207931
theorem B2584175 : Blo 1721061 2584175 := bstep (se 1 (by rfl) ⟨1938131, by rfl⟩ : syracuseStep 2584175 = 3876263) B3876263
theorem B5811965 : Blo 1721061 5811965 := bstep (se 3 (by rfl) ⟨1089743, by rfl⟩ : syracuseStep 5811965 = 2179487) B2179487
theorem B44142407 : Blo 1721061 44142407 := bstep (se 1 (by rfl) ⟨33106805, by rfl⟩ : syracuseStep 44142407 = 66213611) B66213611
theorem B1937263 : Blo 1721061 1937263 := bstep (se 1 (by rfl) ⟨1452947, by rfl⟩ : syracuseStep 1937263 = 2905895) B2905895
theorem B5238697 : Blo 1721061 5238697 := bstep (se 2 (by rfl) ⟨1964511, by rfl⟩ : syracuseStep 5238697 = 3929023) B3929023
theorem B12415031 : Blo 1721061 12415031 := bstep (se 1 (by rfl) ⟨9311273, by rfl⟩ : syracuseStep 12415031 = 18622547) B18622547
theorem B9810017 : Blo 1721061 9810017 := bstep (se 2 (by rfl) ⟨3678756, by rfl⟩ : syracuseStep 9810017 = 7357513) B7357513
theorem B33091739 : Blo 1721061 33091739 := bstep (se 1 (by rfl) ⟨24818804, by rfl⟩ : syracuseStep 33091739 = 49637609) B49637609
theorem B4903163 : Blo 1721061 4903163 := bstep (se 1 (by rfl) ⟨3677372, by rfl⟩ : syracuseStep 4903163 = 7354745) B7354745
theorem B7557407 : Blo 1721061 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B2904383 : Blo 1721061 2904383 := bstep (se 1 (by rfl) ⟨2178287, by rfl⟩ : syracuseStep 2904383 = 4356575) B4356575
theorem B8278685 : Blo 1721061 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B2905591 : Blo 1721061 2905591 := bstep (se 1 (by rfl) ⟨2179193, by rfl⟩ : syracuseStep 2905591 = 4358387) B4358387
theorem B8279777 : Blo 1721061 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B20944763 : Blo 1721061 20944763 := bstep (se 1 (by rfl) ⟨15708572, by rfl⟩ : syracuseStep 20944763 = 31417145) B31417145
theorem B3872681 : Blo 1721061 3872681 := bstep (se 2 (by rfl) ⟨1452255, by rfl⟩ : syracuseStep 3872681 = 2904511) B2904511
theorem B2906219 : Blo 1721061 2906219 := bstep (se 1 (by rfl) ⟨2179664, by rfl⟩ : syracuseStep 2906219 = 4359329) B4359329
theorem B19880063 : Blo 1721061 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B49674971 : Blo 1721061 49674971 := bstep (se 1 (by rfl) ⟨37256228, by rfl⟩ : syracuseStep 49674971 = 74512457) B74512457
theorem B2906887 : Blo 1721061 2906887 := bstep (se 1 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 2906887 = 4360331) B4360331
theorem B2906921 : Blo 1721061 2906921 := bstep (se 2 (by rfl) ⟨1090095, by rfl⟩ : syracuseStep 2906921 = 2180191) B2180191
theorem B20945731 : Blo 1721061 20945731 := bstep (se 1 (by rfl) ⟨15709298, by rfl⟩ : syracuseStep 20945731 = 31418597) B31418597
theorem B29432645 : Blo 1721061 29432645 := bstep (se 4 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 29432645 = 5518621) B5518621
theorem B74480471 : Blo 1721061 74480471 := bstep (se 1 (by rfl) ⟨55860353, by rfl⟩ : syracuseStep 74480471 = 111720707) B111720707
theorem B22060133 : Blo 1721061 22060133 := bstep (se 4 (by rfl) ⟨2068137, by rfl⟩ : syracuseStep 22060133 = 4136275) B4136275
theorem B9813251 : Blo 1721061 9813251 := bstep (se 1 (by rfl) ⟨7359938, by rfl⟩ : syracuseStep 9813251 = 14719877) B14719877
theorem B3358199 : Blo 1721061 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B18611815 : Blo 1721061 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B22061159 : Blo 1721061 22061159 := bstep (se 1 (by rfl) ⟨16545869, by rfl⟩ : syracuseStep 22061159 = 33091739) B33091739
theorem B8716409 : Blo 1721061 8716409 := bstep (se 2 (by rfl) ⟨3268653, by rfl⟩ : syracuseStep 8716409 = 6537307) B6537307
theorem B3268775 : Blo 1721061 3268775 := bstep (se 1 (by rfl) ⟨2451581, by rfl⟩ : syracuseStep 3268775 = 4903163) B4903163
theorem B5038271 : Blo 1721061 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B4358407 : Blo 1721061 4358407 := bstep (se 1 (by rfl) ⟨3268805, by rfl⟩ : syracuseStep 4358407 = 6537611) B6537611
theorem B4359035 : Blo 1721061 4359035 := bstep (se 1 (by rfl) ⟨3269276, by rfl⟩ : syracuseStep 4359035 = 6538553) B6538553
theorem B3875849 : Blo 1721061 3875849 := bstep (se 2 (by rfl) ⟨1453443, by rfl⟩ : syracuseStep 3875849 = 2906887) B2906887
theorem B27927641 : Blo 1721061 27927641 := bstep (se 2 (by rfl) ⟨10472865, by rfl⟩ : syracuseStep 27927641 = 20945731) B20945731
theorem B1721575 : Blo 1721061 1721575 := bstep (se 1 (by rfl) ⟨1291181, by rfl⟩ : syracuseStep 1721575 = 2582363) B2582363
theorem B2581787 : Blo 1721061 2581787 := bstep (se 1 (by rfl) ⟨1936340, by rfl⟩ : syracuseStep 2581787 = 3872681) B3872681
theorem B8955197 : Blo 1721061 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B29410775 : Blo 1721061 29410775 := bstep (se 1 (by rfl) ⟨22058081, by rfl⟩ : syracuseStep 29410775 = 44116163) B44116163
theorem B1722015 : Blo 1721061 1722015 := bstep (se 1 (by rfl) ⟨1291511, by rfl⟩ : syracuseStep 1722015 = 2583023) B2583023
theorem B11036321 : Blo 1721061 11036321 := bstep (se 2 (by rfl) ⟨4138620, by rfl⟩ : syracuseStep 11036321 = 8277241) B8277241
theorem B1722215 : Blo 1721061 1722215 := bstep (se 1 (by rfl) ⟨1291661, by rfl⟩ : syracuseStep 1722215 = 2583323) B2583323
theorem B8718191 : Blo 1721061 8718191 := bstep (se 1 (by rfl) ⟨6538643, by rfl⟩ : syracuseStep 8718191 = 13077287) B13077287
theorem B1722239 : Blo 1721061 1722239 := bstep (se 1 (by rfl) ⟨1291679, by rfl⟩ : syracuseStep 1722239 = 2583359) B2583359
theorem B19621763 : Blo 1721061 19621763 := bstep (se 1 (by rfl) ⟨14716322, by rfl⟩ : syracuseStep 19621763 = 29432645) B29432645
theorem B49653647 : Blo 1721061 49653647 := bstep (se 1 (by rfl) ⟨37240235, by rfl⟩ : syracuseStep 49653647 = 74480471) B74480471
theorem B22079405 : Blo 1721061 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B14706755 : Blo 1721061 14706755 := bstep (se 1 (by rfl) ⟨11030066, by rfl⟩ : syracuseStep 14706755 = 22060133) B22060133
theorem B1722439 : Blo 1721061 1722439 := bstep (se 1 (by rfl) ⟨1291829, by rfl⟩ : syracuseStep 1722439 = 2583659) B2583659
theorem B24815753 : Blo 1721061 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B1722783 : Blo 1721061 1722783 := bstep (se 1 (by rfl) ⟨1292087, by rfl⟩ : syracuseStep 1722783 = 2584175) B2584175
theorem B2583017 : Blo 1721061 2583017 := bstep (se 2 (by rfl) ⟨968631, by rfl⟩ : syracuseStep 2583017 = 1937263) B1937263
theorem B29428271 : Blo 1721061 29428271 := bstep (se 1 (by rfl) ⟨22071203, by rfl⟩ : syracuseStep 29428271 = 44142407) B44142407
theorem B8276687 : Blo 1721061 8276687 := bstep (se 1 (by rfl) ⟨6207515, by rfl⟩ : syracuseStep 8276687 = 12415031) B12415031
theorem B2583275 : Blo 1721061 2583275 := bstep (se 1 (by rfl) ⟨1937456, by rfl⟩ : syracuseStep 2583275 = 3874913) B3874913
theorem B6540011 : Blo 1721061 6540011 := bstep (se 1 (by rfl) ⟨4905008, by rfl⟩ : syracuseStep 6540011 = 9810017) B9810017
theorem B1936255 : Blo 1721061 1936255 := bstep (se 1 (by rfl) ⟨1452191, by rfl⟩ : syracuseStep 1936255 = 2904383) B2904383
theorem B9808877 : Blo 1721061 9808877 := bstep (se 3 (by rfl) ⟨1839164, by rfl⟩ : syracuseStep 9808877 = 3678329) B3678329
theorem B2583647 : Blo 1721061 2583647 := bstep (se 1 (by rfl) ⟨1937735, by rfl⟩ : syracuseStep 2583647 = 3875471) B3875471
theorem B70683961 : Blo 1721061 70683961 := bstep (se 2 (by rfl) ⟨26506485, by rfl⟩ : syracuseStep 70683961 = 53012971) B53012971
theorem B14159465 : Blo 1721061 14159465 := bstep (se 2 (by rfl) ⟨5309799, by rfl⟩ : syracuseStep 14159465 = 10619599) B10619599
theorem B7352147 : Blo 1721061 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B13963175 : Blo 1721061 13963175 := bstep (se 1 (by rfl) ⟨10472381, by rfl⟩ : syracuseStep 13963175 = 20944763) B20944763
theorem B1937479 : Blo 1721061 1937479 := bstep (se 1 (by rfl) ⟨1453109, by rfl⟩ : syracuseStep 1937479 = 2906219) B2906219
theorem B8384795 : Blo 1721061 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B33116647 : Blo 1721061 33116647 := bstep (se 1 (by rfl) ⟨24837485, by rfl⟩ : syracuseStep 33116647 = 49674971) B49674971
theorem B1937947 : Blo 1721061 1937947 := bstep (se 1 (by rfl) ⟨1453460, by rfl⟩ : syracuseStep 1937947 = 2906921) B2906921
theorem B6542167 : Blo 1721061 6542167 := bstep (se 1 (by rfl) ⟨4906625, by rfl⟩ : syracuseStep 6542167 = 9813251) B9813251
theorem B6984929 : Blo 1721061 6984929 := bstep (se 2 (by rfl) ⟨2619348, by rfl⟩ : syracuseStep 6984929 = 5238697) B5238697
theorem B7853483 : Blo 1721061 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B8721917 : Blo 1721061 8721917 := bstep (se 3 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 8721917 = 3270719) B3270719
theorem B3872447 : Blo 1721061 3872447 := bstep (se 1 (by rfl) ⟨2904335, by rfl⟩ : syracuseStep 3872447 = 5808671) B5808671
theorem B5519123 : Blo 1721061 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B4905191 : Blo 1721061 4905191 := bstep (se 1 (by rfl) ⟨3678893, by rfl⟩ : syracuseStep 4905191 = 7357787) B7357787
theorem B13253375 : Blo 1721061 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B3873599 : Blo 1721061 3873599 := bstep (se 1 (by rfl) ⟨2905199, by rfl⟩ : syracuseStep 3873599 = 5810399) B5810399
theorem B3874121 : Blo 1721061 3874121 := bstep (se 2 (by rfl) ⟨1452795, by rfl⟩ : syracuseStep 3874121 = 2905591) B2905591
theorem B16145981 : Blo 1721061 16145981 := bstep (se 3 (by rfl) ⟨3027371, by rfl⟩ : syracuseStep 16145981 = 6054743) B6054743
theorem B3874643 : Blo 1721061 3874643 := bstep (se 1 (by rfl) ⟨2905982, by rfl⟩ : syracuseStep 3874643 = 5811965) B5811965
theorem B3358847 : Blo 1721061 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B8716733 : Blo 1721061 8716733 := bstep (se 3 (by rfl) ⟨1634387, by rfl⟩ : syracuseStep 8716733 = 3268775) B3268775
theorem B44155529 : Blo 1721061 44155529 := bstep (se 2 (by rfl) ⟨16558323, by rfl⟩ : syracuseStep 44155529 = 33116647) B33116647
theorem B1721191 : Blo 1721061 1721191 := bstep (se 1 (by rfl) ⟨1290893, by rfl⟩ : syracuseStep 1721191 = 2581787) B2581787
theorem B7357547 : Blo 1721061 7357547 := bstep (se 1 (by rfl) ⟨5518160, by rfl⟩ : syracuseStep 7357547 = 11036321) B11036321
theorem B2581631 : Blo 1721061 2581631 := bstep (se 1 (by rfl) ⟨1936223, by rfl⟩ : syracuseStep 2581631 = 3872447) B3872447
theorem B2581673 : Blo 1721061 2581673 := bstep (se 2 (by rfl) ⟨968127, by rfl⟩ : syracuseStep 2581673 = 1936255) B1936255
theorem B3679415 : Blo 1721061 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B3270127 : Blo 1721061 3270127 := bstep (se 1 (by rfl) ⟨2452595, by rfl⟩ : syracuseStep 3270127 = 4905191) B4905191
theorem B1722011 : Blo 1721061 1722011 := bstep (se 1 (by rfl) ⟨1291508, by rfl⟩ : syracuseStep 1722011 = 2583017) B2583017
theorem B1722183 : Blo 1721061 1722183 := bstep (se 1 (by rfl) ⟨1291637, by rfl⟩ : syracuseStep 1722183 = 2583275) B2583275
theorem B4360007 : Blo 1721061 4360007 := bstep (se 1 (by rfl) ⟨3270005, by rfl⟩ : syracuseStep 4360007 = 6540011) B6540011
theorem B2582399 : Blo 1721061 2582399 := bstep (se 1 (by rfl) ⟨1936799, by rfl⟩ : syracuseStep 2582399 = 3873599) B3873599
theorem B6539251 : Blo 1721061 6539251 := bstep (se 1 (by rfl) ⟨4904438, by rfl⟩ : syracuseStep 6539251 = 9808877) B9808877
theorem B1722431 : Blo 1721061 1722431 := bstep (se 1 (by rfl) ⟨1291823, by rfl⟩ : syracuseStep 1722431 = 2583647) B2583647
theorem B2582747 : Blo 1721061 2582747 := bstep (se 1 (by rfl) ⟨1937060, by rfl⟩ : syracuseStep 2582747 = 3874121) B3874121
theorem B19605725 : Blo 1721061 19605725 := bstep (se 3 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 19605725 = 7352147) B7352147
theorem B9439643 : Blo 1721061 9439643 := bstep (se 1 (by rfl) ⟨7079732, by rfl⟩ : syracuseStep 9439643 = 14159465) B14159465
theorem B2583095 : Blo 1721061 2583095 := bstep (se 1 (by rfl) ⟨1937321, by rfl⟩ : syracuseStep 2583095 = 3874643) B3874643
theorem B9308783 : Blo 1721061 9308783 := bstep (se 1 (by rfl) ⟨6981587, by rfl⟩ : syracuseStep 9308783 = 13963175) B13963175
theorem B14707439 : Blo 1721061 14707439 := bstep (se 1 (by rfl) ⟨11030579, by rfl⟩ : syracuseStep 14707439 = 22061159) B22061159
theorem B5810939 : Blo 1721061 5810939 := bstep (se 1 (by rfl) ⟨4358204, by rfl⟩ : syracuseStep 5810939 = 8716409) B8716409
theorem B2583305 : Blo 1721061 2583305 := bstep (se 2 (by rfl) ⟨968739, by rfl⟩ : syracuseStep 2583305 = 1937479) B1937479
theorem B5589863 : Blo 1721061 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B5811209 : Blo 1721061 5811209 := bstep (se 2 (by rfl) ⟨2179203, by rfl⟩ : syracuseStep 5811209 = 4358407) B4358407
theorem B2583899 : Blo 1721061 2583899 := bstep (se 1 (by rfl) ⟨1937924, by rfl⟩ : syracuseStep 2583899 = 3875849) B3875849
theorem B2583929 : Blo 1721061 2583929 := bstep (se 2 (by rfl) ⟨968973, by rfl⟩ : syracuseStep 2583929 = 1937947) B1937947
theorem B4656619 : Blo 1721061 4656619 := bstep (se 1 (by rfl) ⟨3492464, by rfl⟩ : syracuseStep 4656619 = 6984929) B6984929
theorem B19607183 : Blo 1721061 19607183 := bstep (se 1 (by rfl) ⟨14705387, by rfl⟩ : syracuseStep 19607183 = 29410775) B29410775
theorem B20942621 : Blo 1721061 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B5812127 : Blo 1721061 5812127 := bstep (se 1 (by rfl) ⟨4359095, by rfl⟩ : syracuseStep 5812127 = 8718191) B8718191
theorem B16543835 : Blo 1721061 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B94245281 : Blo 1721061 94245281 := bstep (se 2 (by rfl) ⟨35341980, by rfl⟩ : syracuseStep 94245281 = 70683961) B70683961
theorem B5517791 : Blo 1721061 5517791 := bstep (se 1 (by rfl) ⟨4138343, by rfl⟩ : syracuseStep 5517791 = 8276687) B8276687
theorem B8835583 : Blo 1721061 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B2906023 : Blo 1721061 2906023 := bstep (se 1 (by rfl) ⟨2179517, by rfl⟩ : syracuseStep 2906023 = 4359035) B4359035
theorem B18618427 : Blo 1721061 18618427 := bstep (se 1 (by rfl) ⟨13963820, by rfl⟩ : syracuseStep 18618427 = 27927641) B27927641
theorem B5970131 : Blo 1721061 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B5814611 : Blo 1721061 5814611 := bstep (se 1 (by rfl) ⟨4360958, by rfl⟩ : syracuseStep 5814611 = 8721917) B8721917
theorem B8722889 : Blo 1721061 8722889 := bstep (se 2 (by rfl) ⟨3271083, by rfl⟩ : syracuseStep 8722889 = 6542167) B6542167
theorem B13081175 : Blo 1721061 13081175 := bstep (se 1 (by rfl) ⟨9810881, by rfl⟩ : syracuseStep 13081175 = 19621763) B19621763
theorem B33102431 : Blo 1721061 33102431 := bstep (se 1 (by rfl) ⟨24826823, by rfl⟩ : syracuseStep 33102431 = 49653647) B49653647
theorem B14719603 : Blo 1721061 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B9804503 : Blo 1721061 9804503 := bstep (se 1 (by rfl) ⟨7353377, by rfl⟩ : syracuseStep 9804503 = 14706755) B14706755
theorem B19618847 : Blo 1721061 19618847 := bstep (se 1 (by rfl) ⟨14714135, by rfl⟩ : syracuseStep 19618847 = 29428271) B29428271
theorem B10763987 : Blo 1721061 10763987 := bstep (se 1 (by rfl) ⟨8072990, by rfl⟩ : syracuseStep 10763987 = 16145981) B16145981
theorem B3678527 : Blo 1721061 3678527 := bstep (se 1 (by rfl) ⟨2758895, by rfl⟩ : syracuseStep 3678527 = 5517791) B5517791
theorem B11780777 : Blo 1721061 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B1721087 : Blo 1721061 1721087 := bstep (se 1 (by rfl) ⟨1290815, by rfl⟩ : syracuseStep 1721087 = 2581631) B2581631
theorem B1721115 : Blo 1721061 1721115 := bstep (se 1 (by rfl) ⟨1290836, by rfl⟩ : syracuseStep 1721115 = 2581673) B2581673
theorem B1721599 : Blo 1721061 1721599 := bstep (se 1 (by rfl) ⟨1291199, by rfl⟩ : syracuseStep 1721599 = 2582399) B2582399
theorem B1721831 : Blo 1721061 1721831 := bstep (se 1 (by rfl) ⟨1291373, by rfl⟩ : syracuseStep 1721831 = 2582747) B2582747
theorem B3876407 : Blo 1721061 3876407 := bstep (se 1 (by rfl) ⟨2907305, by rfl⟩ : syracuseStep 3876407 = 5814611) B5814611
theorem B6293095 : Blo 1721061 6293095 := bstep (se 1 (by rfl) ⟨4719821, by rfl⟩ : syracuseStep 6293095 = 9439643) B9439643
theorem B24823421 : Blo 1721061 24823421 := bstep (se 3 (by rfl) ⟨4654391, by rfl⟩ : syracuseStep 24823421 = 9308783) B9308783
theorem B1722063 : Blo 1721061 1722063 := bstep (se 1 (by rfl) ⟨1291547, by rfl⟩ : syracuseStep 1722063 = 2583095) B2583095
theorem B1722203 : Blo 1721061 1722203 := bstep (se 1 (by rfl) ⟨1291652, by rfl⟩ : syracuseStep 1722203 = 2583305) B2583305
theorem B4360169 : Blo 1721061 4360169 := bstep (se 2 (by rfl) ⟨1635063, by rfl⟩ : syracuseStep 4360169 = 3270127) B3270127
theorem B1722599 : Blo 1721061 1722599 := bstep (se 1 (by rfl) ⟨1291949, by rfl⟩ : syracuseStep 1722599 = 2583899) B2583899
theorem B1722619 : Blo 1721061 1722619 := bstep (se 1 (by rfl) ⟨1291964, by rfl⟩ : syracuseStep 1722619 = 2583929) B2583929
theorem B13961747 : Blo 1721061 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B8719001 : Blo 1721061 8719001 := bstep (se 2 (by rfl) ⟨3269625, by rfl⟩ : syracuseStep 8719001 = 6539251) B6539251
theorem B11029223 : Blo 1721061 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B24824569 : Blo 1721061 24824569 := bstep (se 2 (by rfl) ⟨9309213, by rfl⟩ : syracuseStep 24824569 = 18618427) B18618427
theorem B2239231 : Blo 1721061 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B5811155 : Blo 1721061 5811155 := bstep (se 1 (by rfl) ⟨4358366, by rfl⟩ : syracuseStep 5811155 = 8716733) B8716733
theorem B29437019 : Blo 1721061 29437019 := bstep (se 1 (by rfl) ⟨22077764, by rfl⟩ : syracuseStep 29437019 = 44155529) B44155529
theorem B2452943 : Blo 1721061 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B13070483 : Blo 1721061 13070483 := bstep (se 1 (by rfl) ⟨9802862, by rfl⟩ : syracuseStep 13070483 = 19605725) B19605725
theorem B8720783 : Blo 1721061 8720783 := bstep (se 1 (by rfl) ⟨6540587, by rfl⟩ : syracuseStep 8720783 = 13081175) B13081175
theorem B13079231 : Blo 1721061 13079231 := bstep (se 1 (by rfl) ⟨9809423, by rfl⟩ : syracuseStep 13079231 = 19618847) B19618847
theorem B13071455 : Blo 1721061 13071455 := bstep (se 1 (by rfl) ⟨9803591, by rfl⟩ : syracuseStep 13071455 = 19607183) B19607183
theorem B62830187 : Blo 1721061 62830187 := bstep (se 1 (by rfl) ⟨47122640, by rfl⟩ : syracuseStep 62830187 = 94245281) B94245281
theorem B4905031 : Blo 1721061 4905031 := bstep (se 1 (by rfl) ⟨3678773, by rfl⟩ : syracuseStep 4905031 = 7357547) B7357547
theorem B19626137 : Blo 1721061 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B2906671 : Blo 1721061 2906671 := bstep (se 1 (by rfl) ⟨2180003, by rfl⟩ : syracuseStep 2906671 = 4360007) B4360007
theorem B3980087 : Blo 1721061 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B5815259 : Blo 1721061 5815259 := bstep (se 1 (by rfl) ⟨4361444, by rfl⟩ : syracuseStep 5815259 = 8722889) B8722889
theorem B22068287 : Blo 1721061 22068287 := bstep (se 1 (by rfl) ⟨16551215, by rfl⟩ : syracuseStep 22068287 = 33102431) B33102431
theorem B6536335 : Blo 1721061 6536335 := bstep (se 1 (by rfl) ⟨4902251, by rfl⟩ : syracuseStep 6536335 = 9804503) B9804503
theorem B9804959 : Blo 1721061 9804959 := bstep (se 1 (by rfl) ⟨7353719, by rfl⟩ : syracuseStep 9804959 = 14707439) B14707439
theorem B3873959 : Blo 1721061 3873959 := bstep (se 1 (by rfl) ⟨2905469, by rfl⟩ : syracuseStep 3873959 = 5810939) B5810939
theorem B28703965 : Blo 1721061 28703965 := bstep (se 3 (by rfl) ⟨5381993, by rfl⟩ : syracuseStep 28703965 = 10763987) B10763987
theorem B3726575 : Blo 1721061 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B6208825 : Blo 1721061 6208825 := bstep (se 2 (by rfl) ⟨2328309, by rfl⟩ : syracuseStep 6208825 = 4656619) B4656619
theorem B3874139 : Blo 1721061 3874139 := bstep (se 1 (by rfl) ⟨2905604, by rfl⟩ : syracuseStep 3874139 = 5811209) B5811209
theorem B3874697 : Blo 1721061 3874697 := bstep (se 2 (by rfl) ⟨1453011, by rfl⟩ : syracuseStep 3874697 = 2906023) B2906023
theorem B3874751 : Blo 1721061 3874751 := bstep (se 1 (by rfl) ⟨2906063, by rfl⟩ : syracuseStep 3874751 = 5812127) B5812127
theorem B33563173 : Blo 1721061 33563173 := bstep (se 4 (by rfl) ⟨3146547, by rfl⟩ : syracuseStep 33563173 = 6293095) B6293095
theorem B3875561 : Blo 1721061 3875561 := bstep (se 2 (by rfl) ⟨1453335, by rfl⟩ : syracuseStep 3875561 = 2906671) B2906671
theorem B41886791 : Blo 1721061 41886791 := bstep (se 1 (by rfl) ⟨31415093, by rfl⟩ : syracuseStep 41886791 = 62830187) B62830187
theorem B16548947 : Blo 1721061 16548947 := bstep (se 1 (by rfl) ⟨12411710, by rfl⟩ : syracuseStep 16548947 = 24823421) B24823421
theorem B13084091 : Blo 1721061 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B9307831 : Blo 1721061 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B3876839 : Blo 1721061 3876839 := bstep (se 1 (by rfl) ⟨2907629, by rfl⟩ : syracuseStep 3876839 = 5815259) B5815259
theorem B2582639 : Blo 1721061 2582639 := bstep (se 1 (by rfl) ⟨1936979, by rfl⟩ : syracuseStep 2582639 = 3873959) B3873959
theorem B2484383 : Blo 1721061 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2582759 : Blo 1721061 2582759 := bstep (se 1 (by rfl) ⟨1937069, by rfl⟩ : syracuseStep 2582759 = 3874139) B3874139
theorem B2583131 : Blo 1721061 2583131 := bstep (se 1 (by rfl) ⟨1937348, by rfl⟩ : syracuseStep 2583131 = 3874697) B3874697
theorem B2583167 : Blo 1721061 2583167 := bstep (se 1 (by rfl) ⟨1937375, by rfl⟩ : syracuseStep 2583167 = 3874751) B3874751
theorem B6540041 : Blo 1721061 6540041 := bstep (se 2 (by rfl) ⟨2452515, by rfl⟩ : syracuseStep 6540041 = 4905031) B4905031
theorem B2452351 : Blo 1721061 2452351 := bstep (se 1 (by rfl) ⟨1839263, by rfl⟩ : syracuseStep 2452351 = 3678527) B3678527
theorem B8719487 : Blo 1721061 8719487 := bstep (se 1 (by rfl) ⟨6539615, by rfl⟩ : syracuseStep 8719487 = 13079231) B13079231
theorem B33099425 : Blo 1721061 33099425 := bstep (se 2 (by rfl) ⟨12412284, by rfl⟩ : syracuseStep 33099425 = 24824569) B24824569
theorem B2985641 : Blo 1721061 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B2584271 : Blo 1721061 2584271 := bstep (se 1 (by rfl) ⟨1938203, by rfl⟩ : syracuseStep 2584271 = 3876407) B3876407
theorem B6541181 : Blo 1721061 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B8278433 : Blo 1721061 8278433 := bstep (se 2 (by rfl) ⟨3104412, by rfl⟩ : syracuseStep 8278433 = 6208825) B6208825
theorem B5812667 : Blo 1721061 5812667 := bstep (se 1 (by rfl) ⟨4359500, by rfl⟩ : syracuseStep 5812667 = 8719001) B8719001
theorem B7352815 : Blo 1721061 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B19624679 : Blo 1721061 19624679 := bstep (se 1 (by rfl) ⟨14718509, by rfl⟩ : syracuseStep 19624679 = 29437019) B29437019
theorem B8713655 : Blo 1721061 8713655 := bstep (se 1 (by rfl) ⟨6535241, by rfl⟩ : syracuseStep 8713655 = 13070483) B13070483
theorem B5813855 : Blo 1721061 5813855 := bstep (se 1 (by rfl) ⟨4360391, by rfl⟩ : syracuseStep 5813855 = 8720783) B8720783
theorem B7853851 : Blo 1721061 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B8714303 : Blo 1721061 8714303 := bstep (se 1 (by rfl) ⟨6535727, by rfl⟩ : syracuseStep 8714303 = 13071455) B13071455
theorem B2906779 : Blo 1721061 2906779 := bstep (se 1 (by rfl) ⟨2180084, by rfl⟩ : syracuseStep 2906779 = 4360169) B4360169
theorem B8715113 : Blo 1721061 8715113 := bstep (se 2 (by rfl) ⟨3268167, by rfl⟩ : syracuseStep 8715113 = 6536335) B6536335
theorem B38271953 : Blo 1721061 38271953 := bstep (se 2 (by rfl) ⟨14351982, by rfl⟩ : syracuseStep 38271953 = 28703965) B28703965
theorem B2653391 : Blo 1721061 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B3874103 : Blo 1721061 3874103 := bstep (se 1 (by rfl) ⟨2905577, by rfl⟩ : syracuseStep 3874103 = 5811155) B5811155
theorem B14712191 : Blo 1721061 14712191 := bstep (se 1 (by rfl) ⟨11034143, by rfl⟩ : syracuseStep 14712191 = 22068287) B22068287
theorem B6536639 : Blo 1721061 6536639 := bstep (se 1 (by rfl) ⟨4902479, by rfl⟩ : syracuseStep 6536639 = 9804959) B9804959
theorem B3875111 : Blo 1721061 3875111 := bstep (se 1 (by rfl) ⟨2906333, by rfl⟩ : syracuseStep 3875111 = 5812667) B5812667
theorem B13083119 : Blo 1721061 13083119 := bstep (se 1 (by rfl) ⟨9812339, by rfl⟩ : syracuseStep 13083119 = 19624679) B19624679
theorem B3875705 : Blo 1721061 3875705 := bstep (se 2 (by rfl) ⟨1453389, by rfl⟩ : syracuseStep 3875705 = 2906779) B2906779
theorem B5809103 : Blo 1721061 5809103 := bstep (se 1 (by rfl) ⟨4356827, by rfl⟩ : syracuseStep 5809103 = 8713655) B8713655
theorem B3875903 : Blo 1721061 3875903 := bstep (se 1 (by rfl) ⟨2906927, by rfl⟩ : syracuseStep 3875903 = 5813855) B5813855
theorem B3269801 : Blo 1721061 3269801 := bstep (se 2 (by rfl) ⟨1226175, by rfl⟩ : syracuseStep 3269801 = 2452351) B2452351
theorem B5809535 : Blo 1721061 5809535 := bstep (se 1 (by rfl) ⟨4357151, by rfl⟩ : syracuseStep 5809535 = 8714303) B8714303
theorem B1721759 : Blo 1721061 1721759 := bstep (se 1 (by rfl) ⟨1291319, by rfl⟩ : syracuseStep 1721759 = 2582639) B2582639
theorem B1721839 : Blo 1721061 1721839 := bstep (se 1 (by rfl) ⟨1291379, by rfl⟩ : syracuseStep 1721839 = 2582759) B2582759
theorem B1722087 : Blo 1721061 1722087 := bstep (se 1 (by rfl) ⟨1291565, by rfl⟩ : syracuseStep 1722087 = 2583131) B2583131
theorem B1722111 : Blo 1721061 1722111 := bstep (se 1 (by rfl) ⟨1291583, by rfl⟩ : syracuseStep 1722111 = 2583167) B2583167
theorem B4360027 : Blo 1721061 4360027 := bstep (se 1 (by rfl) ⟨3270020, by rfl⟩ : syracuseStep 4360027 = 6540041) B6540041
theorem B5810075 : Blo 1721061 5810075 := bstep (se 1 (by rfl) ⟨4357556, by rfl⟩ : syracuseStep 5810075 = 8715113) B8715113
theorem B2582735 : Blo 1721061 2582735 := bstep (se 1 (by rfl) ⟨1937051, by rfl⟩ : syracuseStep 2582735 = 3874103) B3874103
theorem B9808127 : Blo 1721061 9808127 := bstep (se 1 (by rfl) ⟨7356095, by rfl⟩ : syracuseStep 9808127 = 14712191) B14712191
theorem B10471801 : Blo 1721061 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B1722847 : Blo 1721061 1722847 := bstep (se 1 (by rfl) ⟨1292135, by rfl⟩ : syracuseStep 1722847 = 2584271) B2584271
theorem B102058541 : Blo 1721061 102058541 := bstep (se 3 (by rfl) ⟨19135976, by rfl⟩ : syracuseStep 102058541 = 38271953) B38271953
theorem B4360787 : Blo 1721061 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B2583707 : Blo 1721061 2583707 := bstep (se 1 (by rfl) ⟨1937780, by rfl⟩ : syracuseStep 2583707 = 3875561) B3875561
theorem B2584559 : Blo 1721061 2584559 := bstep (se 1 (by rfl) ⟨1938419, by rfl⟩ : syracuseStep 2584559 = 3876839) B3876839
theorem B5812991 : Blo 1721061 5812991 := bstep (se 1 (by rfl) ⟨4359743, by rfl⟩ : syracuseStep 5812991 = 8719487) B8719487
theorem B22066283 : Blo 1721061 22066283 := bstep (se 1 (by rfl) ⟨16549712, by rfl⟩ : syracuseStep 22066283 = 33099425) B33099425
theorem B5518955 : Blo 1721061 5518955 := bstep (se 1 (by rfl) ⟨4139216, by rfl⟩ : syracuseStep 5518955 = 8278433) B8278433
theorem B6625021 : Blo 1721061 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B9803753 : Blo 1721061 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B27924527 : Blo 1721061 27924527 := bstep (se 1 (by rfl) ⟨20943395, by rfl⟩ : syracuseStep 27924527 = 41886791) B41886791
theorem B44750897 : Blo 1721061 44750897 := bstep (se 2 (by rfl) ⟨16781586, by rfl⟩ : syracuseStep 44750897 = 33563173) B33563173
theorem B11032631 : Blo 1721061 11032631 := bstep (se 1 (by rfl) ⟨8274473, by rfl⟩ : syracuseStep 11032631 = 16548947) B16548947
theorem B8722727 : Blo 1721061 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B1768927 : Blo 1721061 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B12410441 : Blo 1721061 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B4357759 : Blo 1721061 4357759 := bstep (se 1 (by rfl) ⟨3268319, by rfl⟩ : syracuseStep 4357759 = 6536639) B6536639
theorem B1990427 : Blo 1721061 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B74465405 : Blo 1721061 74465405 := bstep (se 3 (by rfl) ⟨13962263, by rfl⟩ : syracuseStep 74465405 = 27924527) B27924527
theorem B3875327 : Blo 1721061 3875327 := bstep (se 1 (by rfl) ⟨2906495, by rfl⟩ : syracuseStep 3875327 = 5812991) B5812991
theorem B2179867 : Blo 1721061 2179867 := bstep (se 1 (by rfl) ⟨1634900, by rfl⟩ : syracuseStep 2179867 = 3269801) B3269801
theorem B1721823 : Blo 1721061 1721823 := bstep (se 1 (by rfl) ⟨1291367, by rfl⟩ : syracuseStep 1721823 = 2582735) B2582735
theorem B6538751 : Blo 1721061 6538751 := bstep (se 1 (by rfl) ⟨4904063, by rfl⟩ : syracuseStep 6538751 = 9808127) B9808127
theorem B1722471 : Blo 1721061 1722471 := bstep (se 1 (by rfl) ⟨1291853, by rfl⟩ : syracuseStep 1722471 = 2583707) B2583707
theorem B5810345 : Blo 1721061 5810345 := bstep (se 2 (by rfl) ⟨2178879, by rfl⟩ : syracuseStep 5810345 = 4357759) B4357759
theorem B1723039 : Blo 1721061 1723039 := bstep (se 1 (by rfl) ⟨1292279, by rfl⟩ : syracuseStep 1723039 = 2584559) B2584559
theorem B2583407 : Blo 1721061 2583407 := bstep (se 1 (by rfl) ⟨1937555, by rfl⟩ : syracuseStep 2583407 = 3875111) B3875111
theorem B13962401 : Blo 1721061 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2583803 : Blo 1721061 2583803 := bstep (se 1 (by rfl) ⟨1937852, by rfl⟩ : syracuseStep 2583803 = 3875705) B3875705
theorem B2583935 : Blo 1721061 2583935 := bstep (se 1 (by rfl) ⟨1937951, by rfl⟩ : syracuseStep 2583935 = 3875903) B3875903
theorem B14717213 : Blo 1721061 14717213 := bstep (se 3 (by rfl) ⟨2759477, by rfl⟩ : syracuseStep 14717213 = 5518955) B5518955
theorem B68039027 : Blo 1721061 68039027 := bstep (se 1 (by rfl) ⟨51029270, by rfl⟩ : syracuseStep 68039027 = 102058541) B102058541
theorem B5813369 : Blo 1721061 5813369 := bstep (se 2 (by rfl) ⟨2180013, by rfl⟩ : syracuseStep 5813369 = 4360027) B4360027
theorem B141333781 : Blo 1721061 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B8722079 : Blo 1721061 8722079 := bstep (se 1 (by rfl) ⟨6541559, by rfl⟩ : syracuseStep 8722079 = 13083119) B13083119
theorem B3872735 : Blo 1721061 3872735 := bstep (se 1 (by rfl) ⟨2904551, by rfl⟩ : syracuseStep 3872735 = 5809103) B5809103
theorem B14710855 : Blo 1721061 14710855 := bstep (se 1 (by rfl) ⟨11033141, by rfl⟩ : syracuseStep 14710855 = 22066283) B22066283
theorem B3873023 : Blo 1721061 3873023 := bstep (se 1 (by rfl) ⟨2904767, by rfl⟩ : syracuseStep 3873023 = 5809535) B5809535
theorem B3873383 : Blo 1721061 3873383 := bstep (se 1 (by rfl) ⟨2905037, by rfl⟩ : syracuseStep 3873383 = 5810075) B5810075
theorem B6535835 : Blo 1721061 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B29833931 : Blo 1721061 29833931 := bstep (se 1 (by rfl) ⟨22375448, by rfl⟩ : syracuseStep 29833931 = 44750897) B44750897
theorem B7355087 : Blo 1721061 7355087 := bstep (se 1 (by rfl) ⟨5516315, by rfl⟩ : syracuseStep 7355087 = 11032631) B11032631
theorem B5815151 : Blo 1721061 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B2907191 : Blo 1721061 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B2358569 : Blo 1721061 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B5307805 : Blo 1721061 5307805 := bstep (se 3 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 5307805 = 1990427) B1990427
theorem B8273627 : Blo 1721061 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B49643603 : Blo 1721061 49643603 := bstep (se 1 (by rfl) ⟨37232702, by rfl⟩ : syracuseStep 49643603 = 74465405) B74465405
theorem B45359351 : Blo 1721061 45359351 := bstep (se 1 (by rfl) ⟨34019513, by rfl⟩ : syracuseStep 45359351 = 68039027) B68039027
theorem B3875579 : Blo 1721061 3875579 := bstep (se 1 (by rfl) ⟨2906684, by rfl⟩ : syracuseStep 3875579 = 5813369) B5813369
theorem B4359167 : Blo 1721061 4359167 := bstep (se 1 (by rfl) ⟨3269375, by rfl⟩ : syracuseStep 4359167 = 6538751) B6538751
theorem B2581823 : Blo 1721061 2581823 := bstep (se 1 (by rfl) ⟨1936367, by rfl⟩ : syracuseStep 2581823 = 3872735) B3872735
theorem B2582015 : Blo 1721061 2582015 := bstep (se 1 (by rfl) ⟨1936511, by rfl⟩ : syracuseStep 2582015 = 3873023) B3873023
theorem B2582255 : Blo 1721061 2582255 := bstep (se 1 (by rfl) ⟨1936691, by rfl⟩ : syracuseStep 2582255 = 3873383) B3873383
theorem B1722271 : Blo 1721061 1722271 := bstep (se 1 (by rfl) ⟨1291703, by rfl⟩ : syracuseStep 1722271 = 2583407) B2583407
theorem B3876767 : Blo 1721061 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B9308267 : Blo 1721061 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1722535 : Blo 1721061 1722535 := bstep (se 1 (by rfl) ⟨1291901, by rfl⟩ : syracuseStep 1722535 = 2583803) B2583803
theorem B1722623 : Blo 1721061 1722623 := bstep (se 1 (by rfl) ⟨1291967, by rfl⟩ : syracuseStep 1722623 = 2583935) B2583935
theorem B5515751 : Blo 1721061 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B19614473 : Blo 1721061 19614473 := bstep (se 2 (by rfl) ⟨7355427, by rfl⟩ : syracuseStep 19614473 = 14710855) B14710855
theorem B2583551 : Blo 1721061 2583551 := bstep (se 1 (by rfl) ⟨1937663, by rfl⟩ : syracuseStep 2583551 = 3875327) B3875327
theorem B188445041 : Blo 1721061 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B4903391 : Blo 1721061 4903391 := bstep (se 1 (by rfl) ⟨3677543, by rfl⟩ : syracuseStep 4903391 = 7355087) B7355087
theorem B79557149 : Blo 1721061 79557149 := bstep (se 3 (by rfl) ⟨14916965, by rfl⟩ : syracuseStep 79557149 = 29833931) B29833931
theorem B1938127 : Blo 1721061 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B9811475 : Blo 1721061 9811475 := bstep (se 1 (by rfl) ⟨7358606, by rfl⟩ : syracuseStep 9811475 = 14717213) B14717213
theorem B6289517 : Blo 1721061 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B2906489 : Blo 1721061 2906489 := bstep (se 2 (by rfl) ⟨1089933, by rfl⟩ : syracuseStep 2906489 = 2179867) B2179867
theorem B5814719 : Blo 1721061 5814719 := bstep (se 1 (by rfl) ⟨4361039, by rfl⟩ : syracuseStep 5814719 = 8722079) B8722079
theorem B3873563 : Blo 1721061 3873563 := bstep (se 1 (by rfl) ⟨2905172, by rfl⟩ : syracuseStep 3873563 = 5810345) B5810345
theorem B4357223 : Blo 1721061 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B7077073 : Blo 1721061 7077073 := bstep (se 2 (by rfl) ⟨2653902, by rfl⟩ : syracuseStep 7077073 = 5307805) B5307805
theorem B33095735 : Blo 1721061 33095735 := bstep (se 1 (by rfl) ⟨24821801, by rfl⟩ : syracuseStep 33095735 = 49643603) B49643603
theorem B3268927 : Blo 1721061 3268927 := bstep (se 1 (by rfl) ⟨2451695, by rfl⟩ : syracuseStep 3268927 = 4903391) B4903391
theorem B1721215 : Blo 1721061 1721215 := bstep (se 1 (by rfl) ⟨1290911, by rfl⟩ : syracuseStep 1721215 = 2581823) B2581823
theorem B1721343 : Blo 1721061 1721343 := bstep (se 1 (by rfl) ⟨1291007, by rfl⟩ : syracuseStep 1721343 = 2582015) B2582015
theorem B1721503 : Blo 1721061 1721503 := bstep (se 1 (by rfl) ⟨1291127, by rfl⟩ : syracuseStep 1721503 = 2582255) B2582255
theorem B3876479 : Blo 1721061 3876479 := bstep (se 1 (by rfl) ⟨2907359, by rfl⟩ : syracuseStep 3876479 = 5814719) B5814719
theorem B13076315 : Blo 1721061 13076315 := bstep (se 1 (by rfl) ⟨9807236, by rfl⟩ : syracuseStep 13076315 = 19614473) B19614473
theorem B2582375 : Blo 1721061 2582375 := bstep (se 1 (by rfl) ⟨1936781, by rfl⟩ : syracuseStep 2582375 = 3873563) B3873563
theorem B1722367 : Blo 1721061 1722367 := bstep (se 1 (by rfl) ⟨1291775, by rfl⟩ : syracuseStep 1722367 = 2583551) B2583551
theorem B30239567 : Blo 1721061 30239567 := bstep (se 1 (by rfl) ⟨22679675, by rfl⟩ : syracuseStep 30239567 = 45359351) B45359351
theorem B53038099 : Blo 1721061 53038099 := bstep (se 1 (by rfl) ⟨39778574, by rfl⟩ : syracuseStep 53038099 = 79557149) B79557149
theorem B2583719 : Blo 1721061 2583719 := bstep (se 1 (by rfl) ⟨1937789, by rfl⟩ : syracuseStep 2583719 = 3875579) B3875579
theorem B2584169 : Blo 1721061 2584169 := bstep (se 2 (by rfl) ⟨969063, by rfl⟩ : syracuseStep 2584169 = 1938127) B1938127
theorem B6540983 : Blo 1721061 6540983 := bstep (se 1 (by rfl) ⟨4905737, by rfl⟩ : syracuseStep 6540983 = 9811475) B9811475
theorem B2584511 : Blo 1721061 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B6205511 : Blo 1721061 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B1937659 : Blo 1721061 1937659 := bstep (se 1 (by rfl) ⟨1453244, by rfl⟩ : syracuseStep 1937659 = 2906489) B2906489
theorem B2904815 : Blo 1721061 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B125630027 : Blo 1721061 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B2906111 : Blo 1721061 2906111 := bstep (se 1 (by rfl) ⟨2179583, by rfl⟩ : syracuseStep 2906111 = 4359167) B4359167
theorem B4193011 : Blo 1721061 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B9436097 : Blo 1721061 9436097 := bstep (se 2 (by rfl) ⟨3538536, by rfl⟩ : syracuseStep 9436097 = 7077073) B7077073
theorem B3677167 : Blo 1721061 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B4137007 : Blo 1721061 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B4358569 : Blo 1721061 4358569 := bstep (se 2 (by rfl) ⟨1634463, by rfl⟩ : syracuseStep 4358569 = 3268927) B3268927
theorem B8717543 : Blo 1721061 8717543 := bstep (se 1 (by rfl) ⟨6538157, by rfl⟩ : syracuseStep 8717543 = 13076315) B13076315
theorem B1721583 : Blo 1721061 1721583 := bstep (se 1 (by rfl) ⟨1291187, by rfl⟩ : syracuseStep 1721583 = 2582375) B2582375
theorem B1722479 : Blo 1721061 1722479 := bstep (se 1 (by rfl) ⟨1291859, by rfl⟩ : syracuseStep 1722479 = 2583719) B2583719
theorem B1722779 : Blo 1721061 1722779 := bstep (se 1 (by rfl) ⟨1292084, by rfl⟩ : syracuseStep 1722779 = 2584169) B2584169
theorem B4360655 : Blo 1721061 4360655 := bstep (se 1 (by rfl) ⟨3270491, by rfl⟩ : syracuseStep 4360655 = 6540983) B6540983
theorem B1723007 : Blo 1721061 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B22063823 : Blo 1721061 22063823 := bstep (se 1 (by rfl) ⟨16547867, by rfl⟩ : syracuseStep 22063823 = 33095735) B33095735
theorem B2583545 : Blo 1721061 2583545 := bstep (se 2 (by rfl) ⟨968829, by rfl⟩ : syracuseStep 2583545 = 1937659) B1937659
theorem B1936543 : Blo 1721061 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B2584319 : Blo 1721061 2584319 := bstep (se 1 (by rfl) ⟨1938239, by rfl⟩ : syracuseStep 2584319 = 3876479) B3876479
theorem B1937407 : Blo 1721061 1937407 := bstep (se 1 (by rfl) ⟨1453055, by rfl⟩ : syracuseStep 1937407 = 2906111) B2906111
theorem B70717465 : Blo 1721061 70717465 := bstep (se 2 (by rfl) ⟨26519049, by rfl⟩ : syracuseStep 70717465 = 53038099) B53038099
theorem B83753351 : Blo 1721061 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B22362725 : Blo 1721061 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B20159711 : Blo 1721061 20159711 := bstep (se 1 (by rfl) ⟨15119783, by rfl⟩ : syracuseStep 20159711 = 30239567) B30239567
theorem B6290731 : Blo 1721061 6290731 := bstep (se 1 (by rfl) ⟨4718048, by rfl⟩ : syracuseStep 6290731 = 9436097) B9436097
theorem B19611557 : Blo 1721061 19611557 := bstep (se 4 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 19611557 = 3677167) B3677167
theorem B94289953 : Blo 1721061 94289953 := bstep (se 2 (by rfl) ⟨35358732, by rfl⟩ : syracuseStep 94289953 = 70717465) B70717465
theorem B2582057 : Blo 1721061 2582057 := bstep (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) B1936543
theorem B1722363 : Blo 1721061 1722363 := bstep (se 1 (by rfl) ⟨1291772, by rfl⟩ : syracuseStep 1722363 = 2583545) B2583545
theorem B1722879 : Blo 1721061 1722879 := bstep (se 1 (by rfl) ⟨1292159, by rfl⟩ : syracuseStep 1722879 = 2584319) B2584319
theorem B2583209 : Blo 1721061 2583209 := bstep (se 2 (by rfl) ⟨968703, by rfl⟩ : syracuseStep 2583209 = 1937407) B1937407
theorem B5516009 : Blo 1721061 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B5811425 : Blo 1721061 5811425 := bstep (se 2 (by rfl) ⟨2179284, by rfl⟩ : syracuseStep 5811425 = 4358569) B4358569
theorem B5811695 : Blo 1721061 5811695 := bstep (se 1 (by rfl) ⟨4358771, by rfl⟩ : syracuseStep 5811695 = 8717543) B8717543
theorem B14709215 : Blo 1721061 14709215 := bstep (se 1 (by rfl) ⟨11031911, by rfl⟩ : syracuseStep 14709215 = 22063823) B22063823
theorem B13439807 : Blo 1721061 13439807 := bstep (se 1 (by rfl) ⟨10079855, by rfl⟩ : syracuseStep 13439807 = 20159711) B20159711
theorem B55835567 : Blo 1721061 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B2907103 : Blo 1721061 2907103 := bstep (se 1 (by rfl) ⟨2180327, by rfl⟩ : syracuseStep 2907103 = 4360655) B4360655
theorem B8387641 : Blo 1721061 8387641 := bstep (se 2 (by rfl) ⟨3145365, by rfl⟩ : syracuseStep 8387641 = 6290731) B6290731
theorem B14908483 : Blo 1721061 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B13074371 : Blo 1721061 13074371 := bstep (se 1 (by rfl) ⟨9805778, by rfl⟩ : syracuseStep 13074371 = 19611557) B19611557
theorem B9806143 : Blo 1721061 9806143 := bstep (se 1 (by rfl) ⟨7354607, by rfl⟩ : syracuseStep 9806143 = 14709215) B14709215
theorem B1721371 : Blo 1721061 1721371 := bstep (se 1 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 1721371 = 2582057) B2582057
theorem B3876137 : Blo 1721061 3876137 := bstep (se 2 (by rfl) ⟨1453551, by rfl⟩ : syracuseStep 3876137 = 2907103) B2907103
theorem B11183521 : Blo 1721061 11183521 := bstep (se 2 (by rfl) ⟨4193820, by rfl⟩ : syracuseStep 11183521 = 8387641) B8387641
theorem B1722139 : Blo 1721061 1722139 := bstep (se 1 (by rfl) ⟨1291604, by rfl⟩ : syracuseStep 1722139 = 2583209) B2583209
theorem B19877977 : Blo 1721061 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B125719937 : Blo 1721061 125719937 := bstep (se 2 (by rfl) ⟨47144976, by rfl⟩ : syracuseStep 125719937 = 94289953) B94289953
theorem B8959871 : Blo 1721061 8959871 := bstep (se 1 (by rfl) ⟨6719903, by rfl⟩ : syracuseStep 8959871 = 13439807) B13439807
theorem B3677339 : Blo 1721061 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B37223711 : Blo 1721061 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B3874283 : Blo 1721061 3874283 := bstep (se 1 (by rfl) ⟨2905712, by rfl⟩ : syracuseStep 3874283 = 5811425) B5811425
theorem B3874463 : Blo 1721061 3874463 := bstep (se 1 (by rfl) ⟨2905847, by rfl⟩ : syracuseStep 3874463 = 5811695) B5811695
theorem B8716247 : Blo 1721061 8716247 := bstep (se 1 (by rfl) ⟨6537185, by rfl⟩ : syracuseStep 8716247 = 13074371) B13074371
theorem B13074857 : Blo 1721061 13074857 := bstep (se 2 (by rfl) ⟨4903071, by rfl⟩ : syracuseStep 13074857 = 9806143) B9806143
theorem B83813291 : Blo 1721061 83813291 := bstep (se 1 (by rfl) ⟨62859968, by rfl⟩ : syracuseStep 83813291 = 125719937) B125719937
theorem B5973247 : Blo 1721061 5973247 := bstep (se 1 (by rfl) ⟨4479935, by rfl⟩ : syracuseStep 5973247 = 8959871) B8959871
theorem B14911361 : Blo 1721061 14911361 := bstep (se 2 (by rfl) ⟨5591760, by rfl⟩ : syracuseStep 14911361 = 11183521) B11183521
theorem B2451559 : Blo 1721061 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B24815807 : Blo 1721061 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B2582855 : Blo 1721061 2582855 := bstep (se 1 (by rfl) ⟨1937141, by rfl⟩ : syracuseStep 2582855 = 3874283) B3874283
theorem B2582975 : Blo 1721061 2582975 := bstep (se 1 (by rfl) ⟨1937231, by rfl⟩ : syracuseStep 2582975 = 3874463) B3874463
theorem B5810831 : Blo 1721061 5810831 := bstep (se 1 (by rfl) ⟨4358123, by rfl⟩ : syracuseStep 5810831 = 8716247) B8716247
theorem B26503969 : Blo 1721061 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B2584091 : Blo 1721061 2584091 := bstep (se 1 (by rfl) ⟨1938068, by rfl⟩ : syracuseStep 2584091 = 3876137) B3876137
theorem B3268745 : Blo 1721061 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B8716571 : Blo 1721061 8716571 := bstep (se 1 (by rfl) ⟨6537428, by rfl⟩ : syracuseStep 8716571 = 13074857) B13074857
theorem B1721903 : Blo 1721061 1721903 := bstep (se 1 (by rfl) ⟨1291427, by rfl⟩ : syracuseStep 1721903 = 2582855) B2582855
theorem B1721983 : Blo 1721061 1721983 := bstep (se 1 (by rfl) ⟨1291487, by rfl⟩ : syracuseStep 1721983 = 2582975) B2582975
theorem B7964329 : Blo 1721061 7964329 := bstep (se 2 (by rfl) ⟨2986623, by rfl⟩ : syracuseStep 7964329 = 5973247) B5973247
theorem B1722727 : Blo 1721061 1722727 := bstep (se 1 (by rfl) ⟨1292045, by rfl⟩ : syracuseStep 1722727 = 2584091) B2584091
theorem B9940907 : Blo 1721061 9940907 := bstep (se 1 (by rfl) ⟨7455680, by rfl⟩ : syracuseStep 9940907 = 14911361) B14911361
theorem B16543871 : Blo 1721061 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B55875527 : Blo 1721061 55875527 := bstep (se 1 (by rfl) ⟨41906645, by rfl⟩ : syracuseStep 55875527 = 83813291) B83813291
theorem B35338625 : Blo 1721061 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B3873887 : Blo 1721061 3873887 := bstep (se 1 (by rfl) ⟨2905415, by rfl⟩ : syracuseStep 3873887 = 5810831) B5810831
theorem B2179163 : Blo 1721061 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B37250351 : Blo 1721061 37250351 := bstep (se 1 (by rfl) ⟨27937763, by rfl⟩ : syracuseStep 37250351 = 55875527) B55875527
theorem B2582591 : Blo 1721061 2582591 := bstep (se 1 (by rfl) ⟨1936943, by rfl⟩ : syracuseStep 2582591 = 3873887) B3873887
theorem B10619105 : Blo 1721061 10619105 := bstep (se 2 (by rfl) ⟨3982164, by rfl⟩ : syracuseStep 10619105 = 7964329) B7964329
theorem B11029247 : Blo 1721061 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B5811047 : Blo 1721061 5811047 := bstep (se 1 (by rfl) ⟨4358285, by rfl⟩ : syracuseStep 5811047 = 8716571) B8716571
theorem B23559083 : Blo 1721061 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B6627271 : Blo 1721061 6627271 := bstep (se 1 (by rfl) ⟨4970453, by rfl⟩ : syracuseStep 6627271 = 9940907) B9940907
theorem B1721727 : Blo 1721061 1721727 := bstep (se 1 (by rfl) ⟨1291295, by rfl⟩ : syracuseStep 1721727 = 2582591) B2582591
theorem B15706055 : Blo 1721061 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B5811101 : Blo 1721061 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B24833567 : Blo 1721061 24833567 := bstep (se 1 (by rfl) ⟨18625175, by rfl⟩ : syracuseStep 24833567 = 37250351) B37250351
theorem B7352831 : Blo 1721061 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B8836361 : Blo 1721061 8836361 := bstep (se 2 (by rfl) ⟨3313635, by rfl⟩ : syracuseStep 8836361 = 6627271) B6627271
theorem B28317613 : Blo 1721061 28317613 := bstep (se 3 (by rfl) ⟨5309552, by rfl⟩ : syracuseStep 28317613 = 10619105) B10619105
theorem B3874031 : Blo 1721061 3874031 := bstep (se 1 (by rfl) ⟨2905523, by rfl⟩ : syracuseStep 3874031 = 5811047) B5811047
theorem B5890907 : Blo 1721061 5890907 := bstep (se 1 (by rfl) ⟨4418180, by rfl⟩ : syracuseStep 5890907 = 8836361) B8836361
theorem B10470703 : Blo 1721061 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B2582687 : Blo 1721061 2582687 := bstep (se 1 (by rfl) ⟨1937015, by rfl⟩ : syracuseStep 2582687 = 3874031) B3874031
theorem B4901887 : Blo 1721061 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B3874067 : Blo 1721061 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B16555711 : Blo 1721061 16555711 := bstep (se 1 (by rfl) ⟨12416783, by rfl⟩ : syracuseStep 16555711 = 24833567) B24833567
theorem B37756817 : Blo 1721061 37756817 := bstep (se 2 (by rfl) ⟨14158806, by rfl⟩ : syracuseStep 37756817 = 28317613) B28317613
theorem B1721791 : Blo 1721061 1721791 := bstep (se 1 (by rfl) ⟨1291343, by rfl⟩ : syracuseStep 1721791 = 2582687) B2582687
theorem B13960937 : Blo 1721061 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B2582711 : Blo 1721061 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B15709085 : Blo 1721061 15709085 := bstep (se 3 (by rfl) ⟨2945453, by rfl⟩ : syracuseStep 15709085 = 5890907) B5890907
theorem B22074281 : Blo 1721061 22074281 := bstep (se 2 (by rfl) ⟨8277855, by rfl⟩ : syracuseStep 22074281 = 16555711) B16555711
theorem B25171211 : Blo 1721061 25171211 := bstep (se 1 (by rfl) ⟨18878408, by rfl⟩ : syracuseStep 25171211 = 37756817) B37756817
theorem B6535849 : Blo 1721061 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B1721807 : Blo 1721061 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B10472723 : Blo 1721061 10472723 := bstep (se 1 (by rfl) ⟨7854542, by rfl⟩ : syracuseStep 10472723 = 15709085) B15709085
theorem B14716187 : Blo 1721061 14716187 := bstep (se 1 (by rfl) ⟨11037140, by rfl⟩ : syracuseStep 14716187 = 22074281) B22074281
theorem B16780807 : Blo 1721061 16780807 := bstep (se 1 (by rfl) ⟨12585605, by rfl⟩ : syracuseStep 16780807 = 25171211) B25171211
theorem B37229165 : Blo 1721061 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B8714465 : Blo 1721061 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 1721061 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B22374409 : Blo 1721061 22374409 := bstep (se 2 (by rfl) ⟨8390403, by rfl⟩ : syracuseStep 22374409 = 16780807) B16780807
theorem B6981815 : Blo 1721061 6981815 := bstep (se 1 (by rfl) ⟨5236361, by rfl⟩ : syracuseStep 6981815 = 10472723) B10472723
theorem B9810791 : Blo 1721061 9810791 := bstep (se 1 (by rfl) ⟨7358093, by rfl⟩ : syracuseStep 9810791 = 14716187) B14716187
theorem B24819443 : Blo 1721061 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B6540527 : Blo 1721061 6540527 := bstep (se 1 (by rfl) ⟨4905395, by rfl⟩ : syracuseStep 6540527 = 9810791) B9810791
theorem B29832545 : Blo 1721061 29832545 := bstep (se 2 (by rfl) ⟨11187204, by rfl⟩ : syracuseStep 29832545 = 22374409) B22374409
theorem B18618173 : Blo 1721061 18618173 := bstep (se 3 (by rfl) ⟨3490907, by rfl⟩ : syracuseStep 18618173 = 6981815) B6981815
theorem B3873095 : Blo 1721061 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B16546295 : Blo 1721061 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B12412115 : Blo 1721061 12412115 := bstep (se 1 (by rfl) ⟨9309086, by rfl⟩ : syracuseStep 12412115 = 18618173) B18618173
theorem B2582063 : Blo 1721061 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B4360351 : Blo 1721061 4360351 := bstep (se 1 (by rfl) ⟨3270263, by rfl⟩ : syracuseStep 4360351 = 6540527) B6540527
theorem B11030863 : Blo 1721061 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B19888363 : Blo 1721061 19888363 := bstep (se 1 (by rfl) ⟨14916272, by rfl⟩ : syracuseStep 19888363 = 29832545) B29832545
theorem B26517817 : Blo 1721061 26517817 := bstep (se 2 (by rfl) ⟨9944181, by rfl⟩ : syracuseStep 26517817 = 19888363) B19888363
theorem B8274743 : Blo 1721061 8274743 := bstep (se 1 (by rfl) ⟨6206057, by rfl⟩ : syracuseStep 8274743 = 12412115) B12412115
theorem B1721375 : Blo 1721061 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B14707817 : Blo 1721061 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B5813801 : Blo 1721061 5813801 := bstep (se 2 (by rfl) ⟨2180175, by rfl⟩ : syracuseStep 5813801 = 4360351) B4360351
theorem B35357089 : Blo 1721061 35357089 := bstep (se 2 (by rfl) ⟨13258908, by rfl⟩ : syracuseStep 35357089 = 26517817) B26517817
theorem B3875867 : Blo 1721061 3875867 := bstep (se 1 (by rfl) ⟨2906900, by rfl⟩ : syracuseStep 3875867 = 5813801) B5813801
theorem B5516495 : Blo 1721061 5516495 := bstep (se 1 (by rfl) ⟨4137371, by rfl⟩ : syracuseStep 5516495 = 8274743) B8274743
theorem B9805211 : Blo 1721061 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B2583911 : Blo 1721061 2583911 := bstep (se 1 (by rfl) ⟨1937933, by rfl⟩ : syracuseStep 2583911 = 3875867) B3875867
theorem B47142785 : Blo 1721061 47142785 := bstep (se 2 (by rfl) ⟨17678544, by rfl⟩ : syracuseStep 47142785 = 35357089) B35357089
theorem B3677663 : Blo 1721061 3677663 := bstep (se 1 (by rfl) ⟨2758247, by rfl⟩ : syracuseStep 3677663 = 5516495) B5516495
theorem B6536807 : Blo 1721061 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B9807101 : Blo 1721061 9807101 := bstep (se 3 (by rfl) ⟨1838831, by rfl⟩ : syracuseStep 9807101 = 3677663) B3677663
theorem B1722607 : Blo 1721061 1722607 := bstep (se 1 (by rfl) ⟨1291955, by rfl⟩ : syracuseStep 1722607 = 2583911) B2583911
theorem B31428523 : Blo 1721061 31428523 := bstep (se 1 (by rfl) ⟨23571392, by rfl⟩ : syracuseStep 31428523 = 47142785) B47142785
theorem B4357871 : Blo 1721061 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B6538067 : Blo 1721061 6538067 := bstep (se 1 (by rfl) ⟨4903550, by rfl⟩ : syracuseStep 6538067 = 9807101) B9807101
theorem B41904697 : Blo 1721061 41904697 := bstep (se 2 (by rfl) ⟨15714261, by rfl⟩ : syracuseStep 41904697 = 31428523) B31428523
theorem B2905247 : Blo 1721061 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B4358711 : Blo 1721061 4358711 := bstep (se 1 (by rfl) ⟨3269033, by rfl⟩ : syracuseStep 4358711 = 6538067) B6538067
theorem B55872929 : Blo 1721061 55872929 := bstep (se 2 (by rfl) ⟨20952348, by rfl⟩ : syracuseStep 55872929 = 41904697) B41904697
theorem B1936831 : Blo 1721061 1936831 := bstep (se 1 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 1936831 = 2905247) B2905247
theorem B2582441 : Blo 1721061 2582441 := bstep (se 2 (by rfl) ⟨968415, by rfl⟩ : syracuseStep 2582441 = 1936831) B1936831
theorem B2905807 : Blo 1721061 2905807 := bstep (se 1 (by rfl) ⟨2179355, by rfl⟩ : syracuseStep 2905807 = 4358711) B4358711
theorem B37248619 : Blo 1721061 37248619 := bstep (se 1 (by rfl) ⟨27936464, by rfl⟩ : syracuseStep 37248619 = 55872929) B55872929
theorem B1721627 : Blo 1721061 1721627 := bstep (se 1 (by rfl) ⟨1291220, by rfl⟩ : syracuseStep 1721627 = 2582441) B2582441
theorem B49664825 : Blo 1721061 49664825 := bstep (se 2 (by rfl) ⟨18624309, by rfl⟩ : syracuseStep 49664825 = 37248619) B37248619
theorem B3874409 : Blo 1721061 3874409 := bstep (se 2 (by rfl) ⟨1452903, by rfl⟩ : syracuseStep 3874409 = 2905807) B2905807
theorem B2582939 : Blo 1721061 2582939 := bstep (se 1 (by rfl) ⟨1937204, by rfl⟩ : syracuseStep 2582939 = 3874409) B3874409
theorem B33109883 : Blo 1721061 33109883 := bstep (se 1 (by rfl) ⟨24832412, by rfl⟩ : syracuseStep 33109883 = 49664825) B49664825
theorem B1721959 : Blo 1721061 1721959 := bstep (se 1 (by rfl) ⟨1291469, by rfl⟩ : syracuseStep 1721959 = 2582939) B2582939
theorem B22073255 : Blo 1721061 22073255 := bstep (se 1 (by rfl) ⟨16554941, by rfl⟩ : syracuseStep 22073255 = 33109883) B33109883
theorem B14715503 : Blo 1721061 14715503 := bstep (se 1 (by rfl) ⟨11036627, by rfl⟩ : syracuseStep 14715503 = 22073255) B22073255
theorem B9810335 : Blo 1721061 9810335 := bstep (se 1 (by rfl) ⟨7357751, by rfl⟩ : syracuseStep 9810335 = 14715503) B14715503
theorem B6540223 : Blo 1721061 6540223 := bstep (se 1 (by rfl) ⟨4905167, by rfl⟩ : syracuseStep 6540223 = 9810335) B9810335
theorem B8720297 : Blo 1721061 8720297 := bstep (se 2 (by rfl) ⟨3270111, by rfl⟩ : syracuseStep 8720297 = 6540223) B6540223
theorem B5813531 : Blo 1721061 5813531 := bstep (se 1 (by rfl) ⟨4360148, by rfl⟩ : syracuseStep 5813531 = 8720297) B8720297
theorem B3875687 : Blo 1721061 3875687 := bstep (se 1 (by rfl) ⟨2906765, by rfl⟩ : syracuseStep 3875687 = 5813531) B5813531
theorem B2583791 : Blo 1721061 2583791 := bstep (se 1 (by rfl) ⟨1937843, by rfl⟩ : syracuseStep 2583791 = 3875687) B3875687
theorem B1722527 : Blo 1721061 1722527 := bstep (se 1 (by rfl) ⟨1291895, by rfl⟩ : syracuseStep 1722527 = 2583791) B2583791

theorem C0 (j : ℕ) (h1 : 430265 ≤ j) (h2 : j ≤ 430764) : Blo 1721061 (4 * j + 3) := by
  interval_cases j
  · exact B1721063
  · exact B1721067
  · exact B1721071
  · exact B1721075
  · exact B1721079
  · exact B1721083
  · exact B1721087
  · exact B1721091
  · exact B1721095
  · exact B1721099
  · exact B1721103
  · exact B1721107
  · exact B1721111
  · exact B1721115
  · exact B1721119
  · exact B1721123
  · exact B1721127
  · exact B1721131
  · exact B1721135
  · exact B1721139
  · exact B1721143
  · exact B1721147
  · exact B1721151
  · exact B1721155
  · exact B1721159
  · exact B1721163
  · exact B1721167
  · exact B1721171
  · exact B1721175
  · exact B1721179
  · exact B1721183
  · exact B1721187
  · exact B1721191
  · exact B1721195
  · exact B1721199
  · exact B1721203
  · exact B1721207
  · exact B1721211
  · exact B1721215
  · exact B1721219
  · exact B1721223
  · exact B1721227
  · exact B1721231
  · exact B1721235
  · exact B1721239
  · exact B1721243
  · exact B1721247
  · exact B1721251
  · exact B1721255
  · exact B1721259
  · exact B1721263
  · exact B1721267
  · exact B1721271
  · exact B1721275
  · exact B1721279
  · exact B1721283
  · exact B1721287
  · exact B1721291
  · exact B1721295
  · exact B1721299
  · exact B1721303
  · exact B1721307
  · exact B1721311
  · exact B1721315
  · exact B1721319
  · exact B1721323
  · exact B1721327
  · exact B1721331
  · exact B1721335
  · exact B1721339
  · exact B1721343
  · exact B1721347
  · exact B1721351
  · exact B1721355
  · exact B1721359
  · exact B1721363
  · exact B1721367
  · exact B1721371
  · exact B1721375
  · exact B1721379
  · exact B1721383
  · exact B1721387
  · exact B1721391
  · exact B1721395
  · exact B1721399
  · exact B1721403
  · exact B1721407
  · exact B1721411
  · exact B1721415
  · exact B1721419
  · exact B1721423
  · exact B1721427
  · exact B1721431
  · exact B1721435
  · exact B1721439
  · exact B1721443
  · exact B1721447
  · exact B1721451
  · exact B1721455
  · exact B1721459
  · exact B1721463
  · exact B1721467
  · exact B1721471
  · exact B1721475
  · exact B1721479
  · exact B1721483
  · exact B1721487
  · exact B1721491
  · exact B1721495
  · exact B1721499
  · exact B1721503
  · exact B1721507
  · exact B1721511
  · exact B1721515
  · exact B1721519
  · exact B1721523
  · exact B1721527
  · exact B1721531
  · exact B1721535
  · exact B1721539
  · exact B1721543
  · exact B1721547
  · exact B1721551
  · exact B1721555
  · exact B1721559
  · exact B1721563
  · exact B1721567
  · exact B1721571
  · exact B1721575
  · exact B1721579
  · exact B1721583
  · exact B1721587
  · exact B1721591
  · exact B1721595
  · exact B1721599
  · exact B1721603
  · exact B1721607
  · exact B1721611
  · exact B1721615
  · exact B1721619
  · exact B1721623
  · exact B1721627
  · exact B1721631
  · exact B1721635
  · exact B1721639
  · exact B1721643
  · exact B1721647
  · exact B1721651
  · exact B1721655
  · exact B1721659
  · exact B1721663
  · exact B1721667
  · exact B1721671
  · exact B1721675
  · exact B1721679
  · exact B1721683
  · exact B1721687
  · exact B1721691
  · exact B1721695
  · exact B1721699
  · exact B1721703
  · exact B1721707
  · exact B1721711
  · exact B1721715
  · exact B1721719
  · exact B1721723
  · exact B1721727
  · exact B1721731
  · exact B1721735
  · exact B1721739
  · exact B1721743
  · exact B1721747
  · exact B1721751
  · exact B1721755
  · exact B1721759
  · exact B1721763
  · exact B1721767
  · exact B1721771
  · exact B1721775
  · exact B1721779
  · exact B1721783
  · exact B1721787
  · exact B1721791
  · exact B1721795
  · exact B1721799
  · exact B1721803
  · exact B1721807
  · exact B1721811
  · exact B1721815
  · exact B1721819
  · exact B1721823
  · exact B1721827
  · exact B1721831
  · exact B1721835
  · exact B1721839
  · exact B1721843
  · exact B1721847
  · exact B1721851
  · exact B1721855
  · exact B1721859
  · exact B1721863
  · exact B1721867
  · exact B1721871
  · exact B1721875
  · exact B1721879
  · exact B1721883
  · exact B1721887
  · exact B1721891
  · exact B1721895
  · exact B1721899
  · exact B1721903
  · exact B1721907
  · exact B1721911
  · exact B1721915
  · exact B1721919
  · exact B1721923
  · exact B1721927
  · exact B1721931
  · exact B1721935
  · exact B1721939
  · exact B1721943
  · exact B1721947
  · exact B1721951
  · exact B1721955
  · exact B1721959
  · exact B1721963
  · exact B1721967
  · exact B1721971
  · exact B1721975
  · exact B1721979
  · exact B1721983
  · exact B1721987
  · exact B1721991
  · exact B1721995
  · exact B1721999
  · exact B1722003
  · exact B1722007
  · exact B1722011
  · exact B1722015
  · exact B1722019
  · exact B1722023
  · exact B1722027
  · exact B1722031
  · exact B1722035
  · exact B1722039
  · exact B1722043
  · exact B1722047
  · exact B1722051
  · exact B1722055
  · exact B1722059
  · exact B1722063
  · exact B1722067
  · exact B1722071
  · exact B1722075
  · exact B1722079
  · exact B1722083
  · exact B1722087
  · exact B1722091
  · exact B1722095
  · exact B1722099
  · exact B1722103
  · exact B1722107
  · exact B1722111
  · exact B1722115
  · exact B1722119
  · exact B1722123
  · exact B1722127
  · exact B1722131
  · exact B1722135
  · exact B1722139
  · exact B1722143
  · exact B1722147
  · exact B1722151
  · exact B1722155
  · exact B1722159
  · exact B1722163
  · exact B1722167
  · exact B1722171
  · exact B1722175
  · exact B1722179
  · exact B1722183
  · exact B1722187
  · exact B1722191
  · exact B1722195
  · exact B1722199
  · exact B1722203
  · exact B1722207
  · exact B1722211
  · exact B1722215
  · exact B1722219
  · exact B1722223
  · exact B1722227
  · exact B1722231
  · exact B1722235
  · exact B1722239
  · exact B1722243
  · exact B1722247
  · exact B1722251
  · exact B1722255
  · exact B1722259
  · exact B1722263
  · exact B1722267
  · exact B1722271
  · exact B1722275
  · exact B1722279
  · exact B1722283
  · exact B1722287
  · exact B1722291
  · exact B1722295
  · exact B1722299
  · exact B1722303
  · exact B1722307
  · exact B1722311
  · exact B1722315
  · exact B1722319
  · exact B1722323
  · exact B1722327
  · exact B1722331
  · exact B1722335
  · exact B1722339
  · exact B1722343
  · exact B1722347
  · exact B1722351
  · exact B1722355
  · exact B1722359
  · exact B1722363
  · exact B1722367
  · exact B1722371
  · exact B1722375
  · exact B1722379
  · exact B1722383
  · exact B1722387
  · exact B1722391
  · exact B1722395
  · exact B1722399
  · exact B1722403
  · exact B1722407
  · exact B1722411
  · exact B1722415
  · exact B1722419
  · exact B1722423
  · exact B1722427
  · exact B1722431
  · exact B1722435
  · exact B1722439
  · exact B1722443
  · exact B1722447
  · exact B1722451
  · exact B1722455
  · exact B1722459
  · exact B1722463
  · exact B1722467
  · exact B1722471
  · exact B1722475
  · exact B1722479
  · exact B1722483
  · exact B1722487
  · exact B1722491
  · exact B1722495
  · exact B1722499
  · exact B1722503
  · exact B1722507
  · exact B1722511
  · exact B1722515
  · exact B1722519
  · exact B1722523
  · exact B1722527
  · exact B1722531
  · exact B1722535
  · exact B1722539
  · exact B1722543
  · exact B1722547
  · exact B1722551
  · exact B1722555
  · exact B1722559
  · exact B1722563
  · exact B1722567
  · exact B1722571
  · exact B1722575
  · exact B1722579
  · exact B1722583
  · exact B1722587
  · exact B1722591
  · exact B1722595
  · exact B1722599
  · exact B1722603
  · exact B1722607
  · exact B1722611
  · exact B1722615
  · exact B1722619
  · exact B1722623
  · exact B1722627
  · exact B1722631
  · exact B1722635
  · exact B1722639
  · exact B1722643
  · exact B1722647
  · exact B1722651
  · exact B1722655
  · exact B1722659
  · exact B1722663
  · exact B1722667
  · exact B1722671
  · exact B1722675
  · exact B1722679
  · exact B1722683
  · exact B1722687
  · exact B1722691
  · exact B1722695
  · exact B1722699
  · exact B1722703
  · exact B1722707
  · exact B1722711
  · exact B1722715
  · exact B1722719
  · exact B1722723
  · exact B1722727
  · exact B1722731
  · exact B1722735
  · exact B1722739
  · exact B1722743
  · exact B1722747
  · exact B1722751
  · exact B1722755
  · exact B1722759
  · exact B1722763
  · exact B1722767
  · exact B1722771
  · exact B1722775
  · exact B1722779
  · exact B1722783
  · exact B1722787
  · exact B1722791
  · exact B1722795
  · exact B1722799
  · exact B1722803
  · exact B1722807
  · exact B1722811
  · exact B1722815
  · exact B1722819
  · exact B1722823
  · exact B1722827
  · exact B1722831
  · exact B1722835
  · exact B1722839
  · exact B1722843
  · exact B1722847
  · exact B1722851
  · exact B1722855
  · exact B1722859
  · exact B1722863
  · exact B1722867
  · exact B1722871
  · exact B1722875
  · exact B1722879
  · exact B1722883
  · exact B1722887
  · exact B1722891
  · exact B1722895
  · exact B1722899
  · exact B1722903
  · exact B1722907
  · exact B1722911
  · exact B1722915
  · exact B1722919
  · exact B1722923
  · exact B1722927
  · exact B1722931
  · exact B1722935
  · exact B1722939
  · exact B1722943
  · exact B1722947
  · exact B1722951
  · exact B1722955
  · exact B1722959
  · exact B1722963
  · exact B1722967
  · exact B1722971
  · exact B1722975
  · exact B1722979
  · exact B1722983
  · exact B1722987
  · exact B1722991
  · exact B1722995
  · exact B1722999
  · exact B1723003
  · exact B1723007
  · exact B1723011
  · exact B1723015
  · exact B1723019
  · exact B1723023
  · exact B1723027
  · exact B1723031
  · exact B1723035
  · exact B1723039
  · exact B1723043
  · exact B1723047
  · exact B1723051
  · exact B1723055
  · exact B1723059

theorem solution (m : ℕ) (hlo : 1721061 ≤ m) (hhi : m ≤ 1723061) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 430265 ≤ j := by omega
    have hj2 : j ≤ 430764 := by omega
    have hb : Blo 1721061 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
