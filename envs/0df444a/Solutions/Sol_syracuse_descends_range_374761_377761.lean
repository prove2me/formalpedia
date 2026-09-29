-- Prove2me | solution 1 for syracuse_descends_range_374761_377761
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:41.761509+00:00
-- url     : https://prove2.me/submissions/f1d40f66-5357-4606-ab54-852a20f2f975

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


theorem B475141 : Blo 374761 475141 := bbase (se 4 (by rfl) ⟨44544, by rfl⟩ : syracuseStep 475141 = 89089) (by norm_num)
theorem B565253 : Blo 374761 565253 := bbase (se 4 (by rfl) ⟨52992, by rfl⟩ : syracuseStep 565253 = 105985) (by norm_num)
theorem B1605653 : Blo 374761 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B565277 : Blo 374761 565277 := bbase (se 3 (by rfl) ⟨105989, by rfl⟩ : syracuseStep 565277 = 211979) (by norm_num)
theorem B843821 : Blo 374761 843821 := bbase (se 3 (by rfl) ⟨158216, by rfl⟩ : syracuseStep 843821 = 316433) (by norm_num)
theorem B565301 : Blo 374761 565301 := bbase (se 5 (by rfl) ⟨26498, by rfl⟩ : syracuseStep 565301 = 52997) (by norm_num)
theorem B901181 : Blo 374761 901181 := bbase (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) (by norm_num)
theorem B565325 : Blo 374761 565325 := bbase (se 3 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 565325 = 211997) (by norm_num)
theorem B475237 : Blo 374761 475237 := bbase (se 4 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 475237 = 89107) (by norm_num)
theorem B565349 : Blo 374761 565349 := bbase (se 4 (by rfl) ⟨53001, by rfl⟩ : syracuseStep 565349 = 106003) (by norm_num)
theorem B843893 : Blo 374761 843893 := bbase (se 5 (by rfl) ⟨39557, by rfl⟩ : syracuseStep 843893 = 79115) (by norm_num)
theorem B565373 : Blo 374761 565373 := bbase (se 3 (by rfl) ⟨106007, by rfl⟩ : syracuseStep 565373 = 212015) (by norm_num)
theorem B401537 : Blo 374761 401537 := bbase (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) (by norm_num)
theorem B950413 : Blo 374761 950413 := bbase (se 3 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 950413 = 356405) (by norm_num)
theorem B565397 : Blo 374761 565397 := bbase (se 6 (by rfl) ⟨13251, by rfl⟩ : syracuseStep 565397 = 26503) (by norm_num)
theorem B565421 : Blo 374761 565421 := bbase (se 3 (by rfl) ⟨106016, by rfl⟩ : syracuseStep 565421 = 212033) (by norm_num)
theorem B843965 : Blo 374761 843965 := bbase (se 3 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 843965 = 316487) (by norm_num)
theorem B712901 : Blo 374761 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B565445 : Blo 374761 565445 := bbase (se 4 (by rfl) ⟨53010, by rfl⟩ : syracuseStep 565445 = 106021) (by norm_num)
theorem B565469 : Blo 374761 565469 := bbase (se 3 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 565469 = 212051) (by norm_num)
theorem B1646837 : Blo 374761 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B565493 : Blo 374761 565493 := bbase (se 5 (by rfl) ⟨26507, by rfl⟩ : syracuseStep 565493 = 53015) (by norm_num)
theorem B950525 : Blo 374761 950525 := bbase (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) (by norm_num)
theorem B844037 : Blo 374761 844037 := bbase (se 4 (by rfl) ⟨79128, by rfl⟩ : syracuseStep 844037 = 158257) (by norm_num)
theorem B565517 : Blo 374761 565517 := bbase (se 3 (by rfl) ⟨106034, by rfl⟩ : syracuseStep 565517 = 212069) (by norm_num)
theorem B475409 : Blo 374761 475409 := bbase (se 2 (by rfl) ⟨178278, by rfl⟩ : syracuseStep 475409 = 356557) (by norm_num)
theorem B1802533 : Blo 374761 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B1524005 : Blo 374761 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B565541 : Blo 374761 565541 := bbase (se 4 (by rfl) ⟨53019, by rfl⟩ : syracuseStep 565541 = 106039) (by norm_num)
theorem B901421 : Blo 374761 901421 := bbase (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) (by norm_num)
theorem B803125 : Blo 374761 803125 := bbase (se 5 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 803125 = 75293) (by norm_num)
theorem B565565 : Blo 374761 565565 := bbase (se 3 (by rfl) ⟨106043, by rfl⟩ : syracuseStep 565565 = 212087) (by norm_num)
theorem B475465 : Blo 374761 475465 := bbase (se 2 (by rfl) ⟨178299, by rfl⟩ : syracuseStep 475465 = 356599) (by norm_num)
theorem B844109 : Blo 374761 844109 := bbase (se 3 (by rfl) ⟨158270, by rfl⟩ : syracuseStep 844109 = 316541) (by norm_num)
theorem B565589 : Blo 374761 565589 := bbase (se 10 (by rfl) ⟨828, by rfl⟩ : syracuseStep 565589 = 1657) (by norm_num)
theorem B713053 : Blo 374761 713053 := bbase (se 3 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 713053 = 267395) (by norm_num)
theorem B565613 : Blo 374761 565613 := bbase (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) (by norm_num)
theorem B1270133 : Blo 374761 1270133 := bbase (se 5 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 1270133 = 119075) (by norm_num)
theorem B1286533 : Blo 374761 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B565637 : Blo 374761 565637 := bbase (se 4 (by rfl) ⟨53028, by rfl⟩ : syracuseStep 565637 = 106057) (by norm_num)
theorem B844181 : Blo 374761 844181 := bbase (se 6 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 844181 = 39571) (by norm_num)
theorem B4882837 : Blo 374761 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B565661 : Blo 374761 565661 := bbase (se 3 (by rfl) ⟨106061, by rfl⟩ : syracuseStep 565661 = 212123) (by norm_num)
theorem B475561 : Blo 374761 475561 := bbase (se 2 (by rfl) ⟨178335, by rfl⟩ : syracuseStep 475561 = 356671) (by norm_num)
theorem B565685 : Blo 374761 565685 := bbase (se 5 (by rfl) ⟨26516, by rfl⟩ : syracuseStep 565685 = 53033) (by norm_num)
theorem B950717 : Blo 374761 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B565709 : Blo 374761 565709 := bbase (se 3 (by rfl) ⟨106070, by rfl⟩ : syracuseStep 565709 = 212141) (by norm_num)
theorem B680405 : Blo 374761 680405 := bbase (se 7 (by rfl) ⟨7973, by rfl⟩ : syracuseStep 680405 = 15947) (by norm_num)
theorem B844253 : Blo 374761 844253 := bbase (se 3 (by rfl) ⟨158297, by rfl⟩ : syracuseStep 844253 = 316595) (by norm_num)
theorem B1524197 : Blo 374761 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B565733 : Blo 374761 565733 := bbase (se 4 (by rfl) ⟨53037, by rfl⟩ : syracuseStep 565733 = 106075) (by norm_num)
theorem B565757 : Blo 374761 565757 := bbase (se 3 (by rfl) ⟨106079, by rfl⟩ : syracuseStep 565757 = 212159) (by norm_num)
theorem B1155589 : Blo 374761 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B565781 : Blo 374761 565781 := bbase (se 6 (by rfl) ⟨13260, by rfl⟩ : syracuseStep 565781 = 26521) (by norm_num)
theorem B844325 : Blo 374761 844325 := bbase (se 4 (by rfl) ⟨79155, by rfl⟩ : syracuseStep 844325 = 158311) (by norm_num)
theorem B1147429 : Blo 374761 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B565805 : Blo 374761 565805 := bbase (se 3 (by rfl) ⟨106088, by rfl⟩ : syracuseStep 565805 = 212177) (by norm_num)
theorem B401981 : Blo 374761 401981 := bbase (se 3 (by rfl) ⟨75371, by rfl⟩ : syracuseStep 401981 = 150743) (by norm_num)
theorem B565829 : Blo 374761 565829 := bbase (se 4 (by rfl) ⟨53046, by rfl⟩ : syracuseStep 565829 = 106093) (by norm_num)
theorem B475733 : Blo 374761 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B1073749 : Blo 374761 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B1147477 : Blo 374761 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B565853 : Blo 374761 565853 := bbase (se 3 (by rfl) ⟨106097, by rfl⟩ : syracuseStep 565853 = 212195) (by norm_num)
theorem B844397 : Blo 374761 844397 := bbase (se 3 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 844397 = 316649) (by norm_num)
theorem B565877 : Blo 374761 565877 := bbase (se 5 (by rfl) ⟨26525, by rfl⟩ : syracuseStep 565877 = 53051) (by norm_num)
theorem B402041 : Blo 374761 402041 := bbase (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) (by norm_num)
theorem B713357 : Blo 374761 713357 := bbase (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) (by norm_num)
theorem B475789 : Blo 374761 475789 := bbase (se 3 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 475789 = 178421) (by norm_num)
theorem B565901 : Blo 374761 565901 := bbase (se 3 (by rfl) ⟨106106, by rfl⟩ : syracuseStep 565901 = 212213) (by norm_num)
theorem B565925 : Blo 374761 565925 := bbase (se 4 (by rfl) ⟨53055, by rfl⟩ : syracuseStep 565925 = 106111) (by norm_num)
theorem B844469 : Blo 374761 844469 := bbase (se 5 (by rfl) ⟨39584, by rfl⟩ : syracuseStep 844469 = 79169) (by norm_num)
theorem B565949 : Blo 374761 565949 := bbase (se 3 (by rfl) ⟨106115, by rfl⟩ : syracuseStep 565949 = 212231) (by norm_num)
theorem B565973 : Blo 374761 565973 := bbase (se 7 (by rfl) ⟨6632, by rfl⟩ : syracuseStep 565973 = 13265) (by norm_num)
theorem B475885 : Blo 374761 475885 := bbase (se 3 (by rfl) ⟨89228, by rfl⟩ : syracuseStep 475885 = 178457) (by norm_num)
theorem B565997 : Blo 374761 565997 := bbase (se 3 (by rfl) ⟨106124, by rfl⟩ : syracuseStep 565997 = 212249) (by norm_num)
theorem B1442549 : Blo 374761 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1909493 : Blo 374761 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B402169 : Blo 374761 402169 := bbase (se 2 (by rfl) ⟨150813, by rfl⟩ : syracuseStep 402169 = 301627) (by norm_num)
theorem B844541 : Blo 374761 844541 := bbase (se 3 (by rfl) ⟨158351, by rfl⟩ : syracuseStep 844541 = 316703) (by norm_num)
theorem B828157 : Blo 374761 828157 := bbase (se 3 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 828157 = 310559) (by norm_num)
theorem B566021 : Blo 374761 566021 := bbase (se 4 (by rfl) ⟨53064, by rfl⟩ : syracuseStep 566021 = 106129) (by norm_num)
theorem B951061 : Blo 374761 951061 := bbase (se 6 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 951061 = 44581) (by norm_num)
theorem B1016597 : Blo 374761 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B566045 : Blo 374761 566045 := bbase (se 3 (by rfl) ⟨106133, by rfl⟩ : syracuseStep 566045 = 212267) (by norm_num)
theorem B803621 : Blo 374761 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B1270565 : Blo 374761 1270565 := bbase (se 4 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 1270565 = 238231) (by norm_num)
theorem B566069 : Blo 374761 566069 := bbase (se 5 (by rfl) ⟨26534, by rfl⟩ : syracuseStep 566069 = 53069) (by norm_num)
theorem B844613 : Blo 374761 844613 := bbase (se 4 (by rfl) ⟨79182, by rfl⟩ : syracuseStep 844613 = 158365) (by norm_num)
theorem B566093 : Blo 374761 566093 := bbase (se 3 (by rfl) ⟨106142, by rfl⟩ : syracuseStep 566093 = 212285) (by norm_num)
theorem B762709 : Blo 374761 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B566117 : Blo 374761 566117 := bbase (se 4 (by rfl) ⟨53073, by rfl⟩ : syracuseStep 566117 = 106147) (by norm_num)
theorem B451441 : Blo 374761 451441 := bbase (se 2 (by rfl) ⟨169290, by rfl⟩ : syracuseStep 451441 = 338581) (by norm_num)
theorem B2417525 : Blo 374761 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B566141 : Blo 374761 566141 := bbase (se 3 (by rfl) ⟨106151, by rfl⟩ : syracuseStep 566141 = 212303) (by norm_num)
theorem B951173 : Blo 374761 951173 := bbase (se 4 (by rfl) ⟨89172, by rfl⟩ : syracuseStep 951173 = 178345) (by norm_num)
theorem B844685 : Blo 374761 844685 := bbase (se 3 (by rfl) ⟨158378, by rfl⟩ : syracuseStep 844685 = 316757) (by norm_num)
theorem B566165 : Blo 374761 566165 := bbase (se 6 (by rfl) ⟨13269, by rfl⟩ : syracuseStep 566165 = 26539) (by norm_num)
theorem B476057 : Blo 374761 476057 := bbase (se 2 (by rfl) ⟨178521, by rfl⟩ : syracuseStep 476057 = 357043) (by norm_num)
theorem B574373 : Blo 374761 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B566189 : Blo 374761 566189 := bbase (se 3 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 566189 = 212321) (by norm_num)
theorem B451513 : Blo 374761 451513 := bbase (se 2 (by rfl) ⟨169317, by rfl⟩ : syracuseStep 451513 = 338635) (by norm_num)
theorem B566213 : Blo 374761 566213 := bbase (se 4 (by rfl) ⟨53082, by rfl⟩ : syracuseStep 566213 = 106165) (by norm_num)
theorem B476113 : Blo 374761 476113 := bbase (se 2 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 476113 = 357085) (by norm_num)
theorem B844757 : Blo 374761 844757 := bbase (se 7 (by rfl) ⟨9899, by rfl⟩ : syracuseStep 844757 = 19799) (by norm_num)
theorem B566237 : Blo 374761 566237 := bbase (se 3 (by rfl) ⟨106169, by rfl⟩ : syracuseStep 566237 = 212339) (by norm_num)
theorem B566261 : Blo 374761 566261 := bbase (se 5 (by rfl) ⟨26543, by rfl⟩ : syracuseStep 566261 = 53087) (by norm_num)
theorem B1606661 : Blo 374761 1606661 := bbase (se 4 (by rfl) ⟨150624, by rfl⟩ : syracuseStep 1606661 = 301249) (by norm_num)
theorem B566285 : Blo 374761 566285 := bbase (se 3 (by rfl) ⟨106178, by rfl⟩ : syracuseStep 566285 = 212357) (by norm_num)
theorem B844829 : Blo 374761 844829 := bbase (se 3 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 844829 = 316811) (by norm_num)
theorem B566309 : Blo 374761 566309 := bbase (se 4 (by rfl) ⟨53091, by rfl⟩ : syracuseStep 566309 = 106183) (by norm_num)
theorem B902189 : Blo 374761 902189 := bbase (se 3 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 902189 = 338321) (by norm_num)
theorem B476209 : Blo 374761 476209 := bbase (se 2 (by rfl) ⟨178578, by rfl⟩ : syracuseStep 476209 = 357157) (by norm_num)
theorem B566333 : Blo 374761 566333 := bbase (se 3 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 566333 = 212375) (by norm_num)
theorem B951365 : Blo 374761 951365 := bbase (se 4 (by rfl) ⟨89190, by rfl⟩ : syracuseStep 951365 = 178381) (by norm_num)
theorem B459857 : Blo 374761 459857 := bbase (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) (by norm_num)
theorem B1426517 : Blo 374761 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B566357 : Blo 374761 566357 := bbase (se 8 (by rfl) ⟨3318, by rfl⟩ : syracuseStep 566357 = 6637) (by norm_num)
theorem B844901 : Blo 374761 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B566381 : Blo 374761 566381 := bbase (se 3 (by rfl) ⟨106196, by rfl⟩ : syracuseStep 566381 = 212393) (by norm_num)
theorem B566405 : Blo 374761 566405 := bbase (se 4 (by rfl) ⟨53100, by rfl⟩ : syracuseStep 566405 = 106201) (by norm_num)
theorem B1901717 : Blo 374761 1901717 := bbase (se 6 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 1901717 = 89143) (by norm_num)
theorem B566429 : Blo 374761 566429 := bbase (se 3 (by rfl) ⟨106205, by rfl⟩ : syracuseStep 566429 = 212411) (by norm_num)
theorem B844973 : Blo 374761 844973 := bbase (se 3 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 844973 = 316865) (by norm_num)
theorem B402613 : Blo 374761 402613 := bbase (se 5 (by rfl) ⟨18872, by rfl⟩ : syracuseStep 402613 = 37745) (by norm_num)
theorem B566453 : Blo 374761 566453 := bbase (se 5 (by rfl) ⟨26552, by rfl⟩ : syracuseStep 566453 = 53105) (by norm_num)
theorem B828613 : Blo 374761 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B566477 : Blo 374761 566477 := bbase (se 3 (by rfl) ⟨106214, by rfl⟩ : syracuseStep 566477 = 212429) (by norm_num)
theorem B1270997 : Blo 374761 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B476381 : Blo 374761 476381 := bbase (se 3 (by rfl) ⟨89321, by rfl⟩ : syracuseStep 476381 = 178643) (by norm_num)
theorem B566501 : Blo 374761 566501 := bbase (se 4 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 566501 = 106219) (by norm_num)
theorem B845045 : Blo 374761 845045 := bbase (se 5 (by rfl) ⟨39611, by rfl⟩ : syracuseStep 845045 = 79223) (by norm_num)
theorem B550141 : Blo 374761 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B566525 : Blo 374761 566525 := bbase (se 3 (by rfl) ⟨106223, by rfl⟩ : syracuseStep 566525 = 212447) (by norm_num)
theorem B476437 : Blo 374761 476437 := bbase (se 6 (by rfl) ⟨11166, by rfl⟩ : syracuseStep 476437 = 22333) (by norm_num)
theorem B566549 : Blo 374761 566549 := bbase (se 6 (by rfl) ⟨13278, by rfl⟩ : syracuseStep 566549 = 26557) (by norm_num)
theorem B402733 : Blo 374761 402733 := bbase (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) (by norm_num)
theorem B566573 : Blo 374761 566573 := bbase (se 3 (by rfl) ⟨106232, by rfl⟩ : syracuseStep 566573 = 212465) (by norm_num)
theorem B845117 : Blo 374761 845117 := bbase (se 3 (by rfl) ⟨158459, by rfl⟩ : syracuseStep 845117 = 316919) (by norm_num)
theorem B2865941 : Blo 374761 2865941 := bbase (se 6 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 2865941 = 134341) (by norm_num)
theorem B566597 : Blo 374761 566597 := bbase (se 4 (by rfl) ⟨53118, by rfl⟩ : syracuseStep 566597 = 106237) (by norm_num)
theorem B566621 : Blo 374761 566621 := bbase (se 3 (by rfl) ⟨106241, by rfl⟩ : syracuseStep 566621 = 212483) (by norm_num)
theorem B1426805 : Blo 374761 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B476533 : Blo 374761 476533 := bbase (se 5 (by rfl) ⟨22337, by rfl⟩ : syracuseStep 476533 = 44675) (by norm_num)
theorem B714109 : Blo 374761 714109 := bbase (se 3 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 714109 = 267791) (by norm_num)
theorem B845189 : Blo 374761 845189 := bbase (se 4 (by rfl) ⟨79236, by rfl⟩ : syracuseStep 845189 = 158473) (by norm_num)
theorem B951709 : Blo 374761 951709 := bbase (se 3 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 951709 = 356891) (by norm_num)
theorem B845261 : Blo 374761 845261 := bbase (se 3 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 845261 = 316973) (by norm_num)
theorem B951821 : Blo 374761 951821 := bbase (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) (by norm_num)
theorem B714253 : Blo 374761 714253 := bbase (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) (by norm_num)
theorem B845333 : Blo 374761 845333 := bbase (se 6 (by rfl) ⟨19812, by rfl⟩ : syracuseStep 845333 = 39625) (by norm_num)
theorem B476705 : Blo 374761 476705 := bbase (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) (by norm_num)
theorem B402985 : Blo 374761 402985 := bbase (se 2 (by rfl) ⟨151119, by rfl⟩ : syracuseStep 402985 = 302239) (by norm_num)
theorem B534061 : Blo 374761 534061 := bbase (se 3 (by rfl) ⟨100136, by rfl⟩ : syracuseStep 534061 = 200273) (by norm_num)
theorem B402989 : Blo 374761 402989 := bbase (se 3 (by rfl) ⟨75560, by rfl⟩ : syracuseStep 402989 = 151121) (by norm_num)
theorem B1525301 : Blo 374761 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B476761 : Blo 374761 476761 := bbase (se 2 (by rfl) ⟨178785, by rfl⟩ : syracuseStep 476761 = 357571) (by norm_num)
theorem B845405 : Blo 374761 845405 := bbase (se 3 (by rfl) ⟨158513, by rfl⟩ : syracuseStep 845405 = 317027) (by norm_num)
theorem B1271429 : Blo 374761 1271429 := bbase (se 4 (by rfl) ⟨119196, by rfl⟩ : syracuseStep 1271429 = 238393) (by norm_num)
theorem B632461 : Blo 374761 632461 := bbase (se 3 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 632461 = 237173) (by norm_num)
theorem B2139797 : Blo 374761 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B804509 : Blo 374761 804509 := bbase (se 3 (by rfl) ⟨150845, by rfl⟩ : syracuseStep 804509 = 301691) (by norm_num)
theorem B845477 : Blo 374761 845477 := bbase (se 4 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 845477 = 158527) (by norm_num)
theorem B714413 : Blo 374761 714413 := bbase (se 3 (by rfl) ⟨133952, by rfl⟩ : syracuseStep 714413 = 267905) (by norm_num)
theorem B1525429 : Blo 374761 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B476857 : Blo 374761 476857 := bbase (se 2 (by rfl) ⟨178821, by rfl⟩ : syracuseStep 476857 = 357643) (by norm_num)
theorem B952013 : Blo 374761 952013 := bbase (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) (by norm_num)
theorem B632549 : Blo 374761 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B845549 : Blo 374761 845549 := bbase (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) (by norm_num)
theorem B804629 : Blo 374761 804629 := bbase (se 6 (by rfl) ⟨18858, by rfl⟩ : syracuseStep 804629 = 37717) (by norm_num)
theorem B4351765 : Blo 374761 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B812837 : Blo 374761 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B845621 : Blo 374761 845621 := bbase (se 5 (by rfl) ⟨39638, by rfl⟩ : syracuseStep 845621 = 79277) (by norm_num)
theorem B714557 : Blo 374761 714557 := bbase (se 3 (by rfl) ⟨133979, by rfl⟩ : syracuseStep 714557 = 267959) (by norm_num)
theorem B1206085 : Blo 374761 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B632677 : Blo 374761 632677 := bbase (se 4 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 632677 = 118627) (by norm_num)
theorem B477029 : Blo 374761 477029 := bbase (se 4 (by rfl) ⟨44721, by rfl⟩ : syracuseStep 477029 = 89443) (by norm_num)
theorem B1083253 : Blo 374761 1083253 := bbase (se 5 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 1083253 = 101555) (by norm_num)
theorem B845693 : Blo 374761 845693 := bbase (se 3 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 845693 = 317135) (by norm_num)
theorem B427933 : Blo 374761 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B477085 : Blo 374761 477085 := bbase (se 3 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 477085 = 178907) (by norm_num)
theorem B452513 : Blo 374761 452513 := bbase (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) (by norm_num)
theorem B632765 : Blo 374761 632765 := bbase (se 3 (by rfl) ⟨118643, by rfl⟩ : syracuseStep 632765 = 237287) (by norm_num)
theorem B845765 : Blo 374761 845765 := bbase (se 4 (by rfl) ⟨79290, by rfl⟩ : syracuseStep 845765 = 158581) (by norm_num)
theorem B1927157 : Blo 374761 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B477181 : Blo 374761 477181 := bbase (se 3 (by rfl) ⟨89471, by rfl⟩ : syracuseStep 477181 = 178943) (by norm_num)
theorem B1910789 : Blo 374761 1910789 := bbase (se 4 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 1910789 = 358273) (by norm_num)
theorem B845837 : Blo 374761 845837 := bbase (se 3 (by rfl) ⟨158594, by rfl⟩ : syracuseStep 845837 = 317189) (by norm_num)
theorem B952357 : Blo 374761 952357 := bbase (se 4 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 952357 = 178567) (by norm_num)
theorem B1271861 : Blo 374761 1271861 := bbase (se 5 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 1271861 = 119237) (by norm_num)
theorem B632893 : Blo 374761 632893 := bbase (se 3 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 632893 = 237335) (by norm_num)
theorem B845909 : Blo 374761 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B714845 : Blo 374761 714845 := bbase (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) (by norm_num)
theorem B764005 : Blo 374761 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B419981 : Blo 374761 419981 := bbase (se 3 (by rfl) ⟨78746, by rfl⟩ : syracuseStep 419981 = 157493) (by norm_num)
theorem B632981 : Blo 374761 632981 := bbase (se 6 (by rfl) ⟨14835, by rfl⟩ : syracuseStep 632981 = 29671) (by norm_num)
theorem B952469 : Blo 374761 952469 := bbase (se 6 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 952469 = 44647) (by norm_num)
theorem B845981 : Blo 374761 845981 := bbase (se 3 (by rfl) ⟨158621, by rfl⟩ : syracuseStep 845981 = 317243) (by norm_num)
theorem B477353 : Blo 374761 477353 := bbase (se 2 (by rfl) ⟨179007, by rfl⟩ : syracuseStep 477353 = 358015) (by norm_num)
theorem B477409 : Blo 374761 477409 := bbase (se 2 (by rfl) ⟨179028, by rfl⟩ : syracuseStep 477409 = 358057) (by norm_num)
theorem B846053 : Blo 374761 846053 := bbase (se 4 (by rfl) ⟨79317, by rfl⟩ : syracuseStep 846053 = 158635) (by norm_num)
theorem B714997 : Blo 374761 714997 := bbase (se 5 (by rfl) ⟨33515, by rfl⟩ : syracuseStep 714997 = 67031) (by norm_num)
theorem B428293 : Blo 374761 428293 := bbase (se 4 (by rfl) ⟨40152, by rfl⟩ : syracuseStep 428293 = 80305) (by norm_num)
theorem B633109 : Blo 374761 633109 := bbase (se 6 (by rfl) ⟨14838, by rfl⟩ : syracuseStep 633109 = 29677) (by norm_num)
theorem B846125 : Blo 374761 846125 := bbase (se 3 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 846125 = 317297) (by norm_num)
theorem B3909941 : Blo 374761 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B534853 : Blo 374761 534853 := bbase (se 4 (by rfl) ⟨50142, by rfl⟩ : syracuseStep 534853 = 100285) (by norm_num)
theorem B477505 : Blo 374761 477505 := bbase (se 2 (by rfl) ⟨179064, by rfl⟩ : syracuseStep 477505 = 358129) (by norm_num)
theorem B952661 : Blo 374761 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B633197 : Blo 374761 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B846197 : Blo 374761 846197 := bbase (se 5 (by rfl) ⟨39665, by rfl⟩ : syracuseStep 846197 = 79331) (by norm_num)
theorem B903565 : Blo 374761 903565 := bbase (se 3 (by rfl) ⟨169418, by rfl⟩ : syracuseStep 903565 = 338837) (by norm_num)
theorem B805261 : Blo 374761 805261 := bbase (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) (by norm_num)
theorem B1903013 : Blo 374761 1903013 := bbase (se 4 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 1903013 = 356815) (by norm_num)
theorem B551333 : Blo 374761 551333 := bbase (se 4 (by rfl) ⟨51687, by rfl⟩ : syracuseStep 551333 = 103375) (by norm_num)
theorem B846269 : Blo 374761 846269 := bbase (se 3 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 846269 = 317351) (by norm_num)
theorem B1272293 : Blo 374761 1272293 := bbase (se 4 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 1272293 = 238555) (by norm_num)
theorem B633325 : Blo 374761 633325 := bbase (se 3 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 633325 = 237497) (by norm_num)
theorem B477677 : Blo 374761 477677 := bbase (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) (by norm_num)
theorem B846341 : Blo 374761 846341 := bbase (se 4 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 846341 = 158689) (by norm_num)
theorem B1427989 : Blo 374761 1427989 := bbase (se 6 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 1427989 = 66937) (by norm_num)
theorem B715301 : Blo 374761 715301 := bbase (se 4 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 715301 = 134119) (by norm_num)
theorem B477733 : Blo 374761 477733 := bbase (se 4 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 477733 = 89575) (by norm_num)
theorem B731693 : Blo 374761 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B510509 : Blo 374761 510509 := bbase (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) (by norm_num)
theorem B633413 : Blo 374761 633413 := bbase (se 4 (by rfl) ⟨59382, by rfl⟩ : syracuseStep 633413 = 118765) (by norm_num)
theorem B846413 : Blo 374761 846413 := bbase (se 3 (by rfl) ⟨158702, by rfl⟩ : syracuseStep 846413 = 317405) (by norm_num)
theorem B453205 : Blo 374761 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B453209 : Blo 374761 453209 := bbase (se 2 (by rfl) ⟨169953, by rfl⟩ : syracuseStep 453209 = 339907) (by norm_num)
theorem B1206917 : Blo 374761 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B477829 : Blo 374761 477829 := bbase (se 4 (by rfl) ⟨44796, by rfl⟩ : syracuseStep 477829 = 89593) (by norm_num)
theorem B535189 : Blo 374761 535189 := bbase (se 6 (by rfl) ⟨12543, by rfl⟩ : syracuseStep 535189 = 25087) (by norm_num)
theorem B846485 : Blo 374761 846485 := bbase (se 6 (by rfl) ⟨19839, by rfl⟩ : syracuseStep 846485 = 39679) (by norm_num)
theorem B953005 : Blo 374761 953005 := bbase (se 3 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 953005 = 357377) (by norm_num)
theorem B1067701 : Blo 374761 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B1378997 : Blo 374761 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B633541 : Blo 374761 633541 := bbase (se 4 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 633541 = 118789) (by norm_num)
theorem B846557 : Blo 374761 846557 := bbase (se 3 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 846557 = 317459) (by norm_num)
theorem B1608437 : Blo 374761 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B633629 : Blo 374761 633629 := bbase (se 3 (by rfl) ⟨118805, by rfl⟩ : syracuseStep 633629 = 237611) (by norm_num)
theorem B953117 : Blo 374761 953117 := bbase (se 3 (by rfl) ⟨178709, by rfl⟩ : syracuseStep 953117 = 357419) (by norm_num)
theorem B846629 : Blo 374761 846629 := bbase (se 4 (by rfl) ⟨79371, by rfl⟩ : syracuseStep 846629 = 158743) (by norm_num)
theorem B478001 : Blo 374761 478001 := bbase (se 2 (by rfl) ⟨179250, by rfl⟩ : syracuseStep 478001 = 358501) (by norm_num)
theorem B854837 : Blo 374761 854837 := bbase (se 5 (by rfl) ⟨40070, by rfl⟩ : syracuseStep 854837 = 80141) (by norm_num)
theorem B1428293 : Blo 374761 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1526597 : Blo 374761 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B478057 : Blo 374761 478057 := bbase (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) (by norm_num)
theorem B535405 : Blo 374761 535405 := bbase (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) (by norm_num)
theorem B846701 : Blo 374761 846701 := bbase (se 3 (by rfl) ⟨158756, by rfl⟩ : syracuseStep 846701 = 317513) (by norm_num)
theorem B1272725 : Blo 374761 1272725 := bbase (se 6 (by rfl) ⟨29829, by rfl⟩ : syracuseStep 1272725 = 59659) (by norm_num)
theorem B633757 : Blo 374761 633757 := bbase (se 3 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 633757 = 237659) (by norm_num)
theorem B813997 : Blo 374761 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B846773 : Blo 374761 846773 := bbase (se 5 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 846773 = 79385) (by norm_num)
theorem B2411477 : Blo 374761 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B953309 : Blo 374761 953309 := bbase (se 3 (by rfl) ⟨178745, by rfl⟩ : syracuseStep 953309 = 357491) (by norm_num)
theorem B633845 : Blo 374761 633845 := bbase (se 5 (by rfl) ⟨29711, by rfl⟩ : syracuseStep 633845 = 59423) (by norm_num)
theorem B846845 : Blo 374761 846845 := bbase (se 3 (by rfl) ⟨158783, by rfl⟩ : syracuseStep 846845 = 317567) (by norm_num)
theorem B846917 : Blo 374761 846917 := bbase (se 4 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 846917 = 158797) (by norm_num)
theorem B453709 : Blo 374761 453709 := bbase (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) (by norm_num)
theorem B633973 : Blo 374761 633973 := bbase (se 5 (by rfl) ⟨29717, by rfl⟩ : syracuseStep 633973 = 59435) (by norm_num)
theorem B601229 : Blo 374761 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B846989 : Blo 374761 846989 := bbase (se 3 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 846989 = 317621) (by norm_num)
theorem B642221 : Blo 374761 642221 := bbase (se 3 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 642221 = 240833) (by norm_num)
theorem B634061 : Blo 374761 634061 := bbase (se 3 (by rfl) ⟨118886, by rfl⟩ : syracuseStep 634061 = 237773) (by norm_num)
theorem B847061 : Blo 374761 847061 := bbase (se 7 (by rfl) ⟨9926, by rfl⟩ : syracuseStep 847061 = 19853) (by norm_num)
theorem B535781 : Blo 374761 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B928997 : Blo 374761 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B765173 : Blo 374761 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B806149 : Blo 374761 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B855317 : Blo 374761 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B716053 : Blo 374761 716053 := bbase (se 6 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 716053 = 33565) (by norm_num)
theorem B1912085 : Blo 374761 1912085 := bbase (se 6 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 1912085 = 89629) (by norm_num)
theorem B847133 : Blo 374761 847133 := bbase (se 3 (by rfl) ⟨158837, by rfl⟩ : syracuseStep 847133 = 317675) (by norm_num)
theorem B1264949 : Blo 374761 1264949 := bbase (se 5 (by rfl) ⟨59294, by rfl⟩ : syracuseStep 1264949 = 118589) (by norm_num)
theorem B953653 : Blo 374761 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B2149685 : Blo 374761 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B1273157 : Blo 374761 1273157 := bbase (se 4 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 1273157 = 238717) (by norm_num)
theorem B634189 : Blo 374761 634189 := bbase (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) (by norm_num)
theorem B847205 : Blo 374761 847205 := bbase (se 4 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 847205 = 158851) (by norm_num)
theorem B806269 : Blo 374761 806269 := bbase (se 3 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 806269 = 302351) (by norm_num)
theorem B2174357 : Blo 374761 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B634277 : Blo 374761 634277 := bbase (se 4 (by rfl) ⟨59463, by rfl⟩ : syracuseStep 634277 = 118927) (by norm_num)
theorem B953765 : Blo 374761 953765 := bbase (se 4 (by rfl) ⟨89415, by rfl⟩ : syracuseStep 953765 = 178831) (by norm_num)
theorem B716197 : Blo 374761 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B847277 : Blo 374761 847277 := bbase (se 3 (by rfl) ⟨158864, by rfl⟩ : syracuseStep 847277 = 317729) (by norm_num)
theorem B847349 : Blo 374761 847349 := bbase (se 5 (by rfl) ⟨39719, by rfl⟩ : syracuseStep 847349 = 79439) (by norm_num)
theorem B724477 : Blo 374761 724477 := bbase (se 3 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 724477 = 271679) (by norm_num)
theorem B634405 : Blo 374761 634405 := bbase (se 4 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 634405 = 118951) (by norm_num)
theorem B1453621 : Blo 374761 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B904765 : Blo 374761 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B847421 : Blo 374761 847421 := bbase (se 3 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 847421 = 317783) (by norm_num)
theorem B1019461 : Blo 374761 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B716357 : Blo 374761 716357 := bbase (se 4 (by rfl) ⟨67158, by rfl⟩ : syracuseStep 716357 = 134317) (by norm_num)
theorem B953957 : Blo 374761 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B634493 : Blo 374761 634493 := bbase (se 3 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 634493 = 237935) (by norm_num)
theorem B806525 : Blo 374761 806525 := bbase (se 3 (by rfl) ⟨151223, by rfl⟩ : syracuseStep 806525 = 302447) (by norm_num)
theorem B675461 : Blo 374761 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B847493 : Blo 374761 847493 := bbase (se 4 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 847493 = 158905) (by norm_num)
theorem B1904309 : Blo 374761 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B847565 : Blo 374761 847565 := bbase (se 3 (by rfl) ⟨158918, by rfl⟩ : syracuseStep 847565 = 317837) (by norm_num)
theorem B716501 : Blo 374761 716501 := bbase (se 7 (by rfl) ⟨8396, by rfl⟩ : syracuseStep 716501 = 16793) (by norm_num)
theorem B1265381 : Blo 374761 1265381 := bbase (se 4 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 1265381 = 237259) (by norm_num)
theorem B421609 : Blo 374761 421609 := bbase (se 2 (by rfl) ⟨158103, by rfl⟩ : syracuseStep 421609 = 316207) (by norm_num)
theorem B1273589 : Blo 374761 1273589 := bbase (se 5 (by rfl) ⟨59699, by rfl⟩ : syracuseStep 1273589 = 119399) (by norm_num)
theorem B634621 : Blo 374761 634621 := bbase (se 3 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 634621 = 237983) (by norm_num)
theorem B1068805 : Blo 374761 1068805 := bbase (se 4 (by rfl) ⟨100200, by rfl⟩ : syracuseStep 1068805 = 200401) (by norm_num)
theorem B421645 : Blo 374761 421645 := bbase (se 3 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 421645 = 158117) (by norm_num)
theorem B642829 : Blo 374761 642829 := bbase (se 3 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 642829 = 241061) (by norm_num)
theorem B847637 : Blo 374761 847637 := bbase (se 6 (by rfl) ⟨19866, by rfl⟩ : syracuseStep 847637 = 39733) (by norm_num)
theorem B421681 : Blo 374761 421681 := bbase (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) (by norm_num)
theorem B421717 : Blo 374761 421717 := bbase (se 9 (by rfl) ⟨1235, by rfl⟩ : syracuseStep 421717 = 2471) (by norm_num)
theorem B634709 : Blo 374761 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B13782869 : Blo 374761 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B675677 : Blo 374761 675677 := bbase (se 3 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 675677 = 253379) (by norm_num)
theorem B847709 : Blo 374761 847709 := bbase (se 3 (by rfl) ⟨158945, by rfl⟩ : syracuseStep 847709 = 317891) (by norm_num)
theorem B2576245 : Blo 374761 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B421753 : Blo 374761 421753 := bbase (se 2 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 421753 = 316315) (by norm_num)
theorem B1699717 : Blo 374761 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B6442901 : Blo 374761 6442901 := bbase (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) (by norm_num)
theorem B421789 : Blo 374761 421789 := bbase (se 3 (by rfl) ⟨79085, by rfl⟩ : syracuseStep 421789 = 158171) (by norm_num)
theorem B675749 : Blo 374761 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B847781 : Blo 374761 847781 := bbase (se 4 (by rfl) ⟨79479, by rfl⟩ : syracuseStep 847781 = 158959) (by norm_num)
theorem B954301 : Blo 374761 954301 := bbase (se 3 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 954301 = 357863) (by norm_num)
theorem B421825 : Blo 374761 421825 := bbase (se 2 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 421825 = 316369) (by norm_num)
theorem B634837 : Blo 374761 634837 := bbase (se 7 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 634837 = 14879) (by norm_num)
theorem B421861 : Blo 374761 421861 := bbase (se 4 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 421861 = 79099) (by norm_num)
theorem B847853 : Blo 374761 847853 := bbase (se 3 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 847853 = 317945) (by norm_num)
theorem B716789 : Blo 374761 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B421897 : Blo 374761 421897 := bbase (se 2 (by rfl) ⟨158211, by rfl⟩ : syracuseStep 421897 = 316423) (by norm_num)
theorem B4296725 : Blo 374761 4296725 := bbase (se 6 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 4296725 = 201409) (by norm_num)
theorem B421933 : Blo 374761 421933 := bbase (se 3 (by rfl) ⟨79112, by rfl⟩ : syracuseStep 421933 = 158225) (by norm_num)
theorem B634925 : Blo 374761 634925 := bbase (se 3 (by rfl) ⟨119048, by rfl⟩ : syracuseStep 634925 = 238097) (by norm_num)
theorem B954413 : Blo 374761 954413 := bbase (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) (by norm_num)
theorem B847925 : Blo 374761 847925 := bbase (se 5 (by rfl) ⟨39746, by rfl⟩ : syracuseStep 847925 = 79493) (by norm_num)
theorem B421969 : Blo 374761 421969 := bbase (se 2 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 421969 = 316477) (by norm_num)
theorem B13176917 : Blo 374761 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B422005 : Blo 374761 422005 := bbase (se 5 (by rfl) ⟨19781, by rfl⟩ : syracuseStep 422005 = 39563) (by norm_num)
theorem B847997 : Blo 374761 847997 := bbase (se 3 (by rfl) ⟨158999, by rfl⟩ : syracuseStep 847997 = 317999) (by norm_num)
theorem B716941 : Blo 374761 716941 := bbase (se 3 (by rfl) ⟨134426, by rfl⟩ : syracuseStep 716941 = 268853) (by norm_num)
theorem B1265813 : Blo 374761 1265813 := bbase (se 6 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 1265813 = 59335) (by norm_num)
theorem B422041 : Blo 374761 422041 := bbase (se 2 (by rfl) ⟨158265, by rfl⟩ : syracuseStep 422041 = 316531) (by norm_num)
theorem B905381 : Blo 374761 905381 := bbase (se 4 (by rfl) ⟨84879, by rfl⟩ : syracuseStep 905381 = 169759) (by norm_num)
theorem B1274021 : Blo 374761 1274021 := bbase (se 4 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 1274021 = 238879) (by norm_num)
theorem B635053 : Blo 374761 635053 := bbase (se 3 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 635053 = 238145) (by norm_num)
theorem B422077 : Blo 374761 422077 := bbase (se 3 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 422077 = 158279) (by norm_num)
theorem B848069 : Blo 374761 848069 := bbase (se 4 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 848069 = 159013) (by norm_num)
theorem B422113 : Blo 374761 422113 := bbase (se 2 (by rfl) ⟨158292, by rfl⟩ : syracuseStep 422113 = 316585) (by norm_num)
theorem B618725 : Blo 374761 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B954605 : Blo 374761 954605 := bbase (se 3 (by rfl) ⟨178988, by rfl⟩ : syracuseStep 954605 = 357977) (by norm_num)
theorem B422149 : Blo 374761 422149 := bbase (se 4 (by rfl) ⟨39576, by rfl⟩ : syracuseStep 422149 = 79153) (by norm_num)
theorem B635141 : Blo 374761 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B848141 : Blo 374761 848141 := bbase (se 3 (by rfl) ⟨159026, by rfl⟩ : syracuseStep 848141 = 318053) (by norm_num)
theorem B676117 : Blo 374761 676117 := bbase (se 6 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 676117 = 31693) (by norm_num)
theorem B422185 : Blo 374761 422185 := bbase (se 2 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 422185 = 316639) (by norm_num)
theorem B2896181 : Blo 374761 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B422221 : Blo 374761 422221 := bbase (se 3 (by rfl) ⟨79166, by rfl⟩ : syracuseStep 422221 = 158333) (by norm_num)
theorem B3207509 : Blo 374761 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B848213 : Blo 374761 848213 := bbase (se 10 (by rfl) ⟨1242, by rfl⟩ : syracuseStep 848213 = 2485) (by norm_num)
theorem B905573 : Blo 374761 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B422257 : Blo 374761 422257 := bbase (se 2 (by rfl) ⟨158346, by rfl⟩ : syracuseStep 422257 = 316693) (by norm_num)
theorem B1806725 : Blo 374761 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B635269 : Blo 374761 635269 := bbase (se 4 (by rfl) ⟨59556, by rfl⟩ : syracuseStep 635269 = 119113) (by norm_num)
theorem B2134421 : Blo 374761 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B422293 : Blo 374761 422293 := bbase (se 6 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 422293 = 19795) (by norm_num)
theorem B848285 : Blo 374761 848285 := bbase (se 3 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 848285 = 318107) (by norm_num)
theorem B422329 : Blo 374761 422329 := bbase (se 2 (by rfl) ⟨158373, by rfl⟩ : syracuseStep 422329 = 316747) (by norm_num)
theorem B1716677 : Blo 374761 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B905669 : Blo 374761 905669 := bbase (se 4 (by rfl) ⟨84906, by rfl⟩ : syracuseStep 905669 = 169813) (by norm_num)
theorem B1208789 : Blo 374761 1208789 := bbase (se 7 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 1208789 = 28331) (by norm_num)
theorem B422365 : Blo 374761 422365 := bbase (se 3 (by rfl) ⟨79193, by rfl⟩ : syracuseStep 422365 = 158387) (by norm_num)
theorem B635357 : Blo 374761 635357 := bbase (se 3 (by rfl) ⟨119129, by rfl⟩ : syracuseStep 635357 = 238259) (by norm_num)
theorem B725477 : Blo 374761 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B848357 : Blo 374761 848357 := bbase (se 4 (by rfl) ⟨79533, by rfl⟩ : syracuseStep 848357 = 159067) (by norm_num)
theorem B422401 : Blo 374761 422401 := bbase (se 2 (by rfl) ⟨158400, by rfl⟩ : syracuseStep 422401 = 316801) (by norm_num)
theorem B1217045 : Blo 374761 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B422437 : Blo 374761 422437 := bbase (se 4 (by rfl) ⟨39603, by rfl⟩ : syracuseStep 422437 = 79207) (by norm_num)
theorem B848429 : Blo 374761 848429 := bbase (se 3 (by rfl) ⟨159080, by rfl⟩ : syracuseStep 848429 = 318161) (by norm_num)
theorem B1266245 : Blo 374761 1266245 := bbase (se 4 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 1266245 = 237421) (by norm_num)
theorem B954949 : Blo 374761 954949 := bbase (se 4 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 954949 = 179053) (by norm_num)
theorem B422473 : Blo 374761 422473 := bbase (se 2 (by rfl) ⟨158427, by rfl⟩ : syracuseStep 422473 = 316855) (by norm_num)
theorem B7246421 : Blo 374761 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B1274453 : Blo 374761 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B856669 : Blo 374761 856669 := bbase (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) (by norm_num)
theorem B635485 : Blo 374761 635485 := bbase (se 3 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 635485 = 238307) (by norm_num)
theorem B422509 : Blo 374761 422509 := bbase (se 3 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 422509 = 158441) (by norm_num)
theorem B602741 : Blo 374761 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B848501 : Blo 374761 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B537205 : Blo 374761 537205 := bbase (se 5 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 537205 = 50363) (by norm_num)
theorem B422545 : Blo 374761 422545 := bbase (se 2 (by rfl) ⟨158454, by rfl⟩ : syracuseStep 422545 = 316909) (by norm_num)
theorem B422581 : Blo 374761 422581 := bbase (se 5 (by rfl) ⟨19808, by rfl⟩ : syracuseStep 422581 = 39617) (by norm_num)
theorem B635573 : Blo 374761 635573 := bbase (se 5 (by rfl) ⟨29792, by rfl⟩ : syracuseStep 635573 = 59585) (by norm_num)
theorem B955061 : Blo 374761 955061 := bbase (se 5 (by rfl) ⟨44768, by rfl⟩ : syracuseStep 955061 = 89537) (by norm_num)
theorem B848573 : Blo 374761 848573 := bbase (se 3 (by rfl) ⟨159107, by rfl⟩ : syracuseStep 848573 = 318215) (by norm_num)
theorem B725701 : Blo 374761 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B1020629 : Blo 374761 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B422617 : Blo 374761 422617 := bbase (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) (by norm_num)
theorem B1200869 : Blo 374761 1200869 := bbase (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) (by norm_num)
theorem B422653 : Blo 374761 422653 := bbase (se 3 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 422653 = 158495) (by norm_num)
theorem B848645 : Blo 374761 848645 := bbase (se 4 (by rfl) ⟨79560, by rfl⟩ : syracuseStep 848645 = 159121) (by norm_num)
theorem B2036501 : Blo 374761 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B422689 : Blo 374761 422689 := bbase (se 2 (by rfl) ⟨158508, by rfl⟩ : syracuseStep 422689 = 317017) (by norm_num)
theorem B635701 : Blo 374761 635701 := bbase (se 5 (by rfl) ⟨29798, by rfl⟩ : syracuseStep 635701 = 59597) (by norm_num)
theorem B422725 : Blo 374761 422725 := bbase (se 4 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 422725 = 79261) (by norm_num)
theorem B848717 : Blo 374761 848717 := bbase (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) (by norm_num)
theorem B1200997 : Blo 374761 1200997 := bbase (se 4 (by rfl) ⟨112593, by rfl⟩ : syracuseStep 1200997 = 225187) (by norm_num)
theorem B422761 : Blo 374761 422761 := bbase (se 2 (by rfl) ⟨158535, by rfl⟩ : syracuseStep 422761 = 317071) (by norm_num)
theorem B955253 : Blo 374761 955253 := bbase (se 5 (by rfl) ⟨44777, by rfl⟩ : syracuseStep 955253 = 89555) (by norm_num)
theorem B1430405 : Blo 374761 1430405 := bbase (se 4 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 1430405 = 268201) (by norm_num)
theorem B422797 : Blo 374761 422797 := bbase (se 3 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 422797 = 158549) (by norm_num)
theorem B635789 : Blo 374761 635789 := bbase (se 3 (by rfl) ⟨119210, by rfl⟩ : syracuseStep 635789 = 238421) (by norm_num)
theorem B676757 : Blo 374761 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B848789 : Blo 374761 848789 := bbase (se 6 (by rfl) ⟨19893, by rfl⟩ : syracuseStep 848789 = 39787) (by norm_num)
theorem B422833 : Blo 374761 422833 := bbase (se 2 (by rfl) ⟨158562, by rfl⟩ : syracuseStep 422833 = 317125) (by norm_num)
theorem B1143733 : Blo 374761 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1905605 : Blo 374761 1905605 := bbase (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) (by norm_num)
theorem B1020869 : Blo 374761 1020869 := bbase (se 4 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 1020869 = 191413) (by norm_num)
theorem B1029077 : Blo 374761 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B422869 : Blo 374761 422869 := bbase (se 7 (by rfl) ⟨4955, by rfl⟩ : syracuseStep 422869 = 9911) (by norm_num)
theorem B848861 : Blo 374761 848861 := bbase (se 3 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 848861 = 318323) (by norm_num)
theorem B562157 : Blo 374761 562157 := bbase (se 3 (by rfl) ⟨105404, by rfl⟩ : syracuseStep 562157 = 210809) (by norm_num)
theorem B1266677 : Blo 374761 1266677 := bbase (se 5 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 1266677 = 118751) (by norm_num)
theorem B422905 : Blo 374761 422905 := bbase (se 2 (by rfl) ⟨158589, by rfl⟩ : syracuseStep 422905 = 317179) (by norm_num)
theorem B562181 : Blo 374761 562181 := bbase (se 4 (by rfl) ⟨52704, by rfl⟩ : syracuseStep 562181 = 105409) (by norm_num)
theorem B1274885 : Blo 374761 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B635917 : Blo 374761 635917 := bbase (se 3 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 635917 = 238469) (by norm_num)
theorem B562205 : Blo 374761 562205 := bbase (se 3 (by rfl) ⟨105413, by rfl⟩ : syracuseStep 562205 = 210827) (by norm_num)
theorem B422941 : Blo 374761 422941 := bbase (se 3 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 422941 = 158603) (by norm_num)
theorem B848933 : Blo 374761 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B562229 : Blo 374761 562229 := bbase (se 5 (by rfl) ⟨26354, by rfl⟩ : syracuseStep 562229 = 52709) (by norm_num)
theorem B603197 : Blo 374761 603197 := bbase (se 3 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 603197 = 226199) (by norm_num)
theorem B422977 : Blo 374761 422977 := bbase (se 2 (by rfl) ⟨158616, by rfl⟩ : syracuseStep 422977 = 317233) (by norm_num)
theorem B562253 : Blo 374761 562253 := bbase (se 3 (by rfl) ⟨105422, by rfl⟩ : syracuseStep 562253 = 210845) (by norm_num)
theorem B562277 : Blo 374761 562277 := bbase (se 4 (by rfl) ⟨52713, by rfl⟩ : syracuseStep 562277 = 105427) (by norm_num)
theorem B1602661 : Blo 374761 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B423013 : Blo 374761 423013 := bbase (se 4 (by rfl) ⟨39657, by rfl⟩ : syracuseStep 423013 = 79315) (by norm_num)
theorem B636005 : Blo 374761 636005 := bbase (se 4 (by rfl) ⟨59625, by rfl⟩ : syracuseStep 636005 = 119251) (by norm_num)
theorem B849005 : Blo 374761 849005 := bbase (se 3 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 849005 = 318377) (by norm_num)
theorem B562301 : Blo 374761 562301 := bbase (se 3 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 562301 = 210863) (by norm_num)
theorem B423049 : Blo 374761 423049 := bbase (se 2 (by rfl) ⟨158643, by rfl⟩ : syracuseStep 423049 = 317287) (by norm_num)
theorem B562325 : Blo 374761 562325 := bbase (se 6 (by rfl) ⟨13179, by rfl⟩ : syracuseStep 562325 = 26359) (by norm_num)
theorem B1430693 : Blo 374761 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B562349 : Blo 374761 562349 := bbase (se 3 (by rfl) ⟨105440, by rfl⟩ : syracuseStep 562349 = 210881) (by norm_num)
theorem B423085 : Blo 374761 423085 := bbase (se 3 (by rfl) ⟨79328, by rfl⟩ : syracuseStep 423085 = 158657) (by norm_num)
theorem B849077 : Blo 374761 849077 := bbase (se 5 (by rfl) ⟨39800, by rfl⟩ : syracuseStep 849077 = 79601) (by norm_num)
theorem B562373 : Blo 374761 562373 := bbase (se 4 (by rfl) ⟨52722, by rfl⟩ : syracuseStep 562373 = 105445) (by norm_num)
theorem B537797 : Blo 374761 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B955597 : Blo 374761 955597 := bbase (se 3 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 955597 = 358349) (by norm_num)
theorem B423121 : Blo 374761 423121 := bbase (se 2 (by rfl) ⟨158670, by rfl⟩ : syracuseStep 423121 = 317341) (by norm_num)
theorem B562397 : Blo 374761 562397 := bbase (se 3 (by rfl) ⟨105449, by rfl⟩ : syracuseStep 562397 = 210899) (by norm_num)
theorem B1070309 : Blo 374761 1070309 := bbase (se 4 (by rfl) ⟨100341, by rfl⟩ : syracuseStep 1070309 = 200683) (by norm_num)
theorem B636133 : Blo 374761 636133 := bbase (se 4 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 636133 = 119275) (by norm_num)
theorem B562421 : Blo 374761 562421 := bbase (se 5 (by rfl) ⟨26363, by rfl⟩ : syracuseStep 562421 = 52727) (by norm_num)
theorem B423157 : Blo 374761 423157 := bbase (se 5 (by rfl) ⟨19835, by rfl⟩ : syracuseStep 423157 = 39671) (by norm_num)
theorem B382201 : Blo 374761 382201 := bbase (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) (by norm_num)
theorem B849149 : Blo 374761 849149 := bbase (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) (by norm_num)
theorem B382217 : Blo 374761 382217 := bbase (se 2 (by rfl) ⟨143331, by rfl⟩ : syracuseStep 382217 = 286663) (by norm_num)
theorem B562445 : Blo 374761 562445 := bbase (se 3 (by rfl) ⟨105458, by rfl⟩ : syracuseStep 562445 = 210917) (by norm_num)
theorem B423193 : Blo 374761 423193 := bbase (se 2 (by rfl) ⟨158697, by rfl⟩ : syracuseStep 423193 = 317395) (by norm_num)
theorem B562469 : Blo 374761 562469 := bbase (se 4 (by rfl) ⟨52731, by rfl⟩ : syracuseStep 562469 = 105463) (by norm_num)
theorem B562493 : Blo 374761 562493 := bbase (se 3 (by rfl) ⟨105467, by rfl⟩ : syracuseStep 562493 = 210935) (by norm_num)
theorem B423229 : Blo 374761 423229 := bbase (se 3 (by rfl) ⟨79355, by rfl⟩ : syracuseStep 423229 = 158711) (by norm_num)
theorem B636221 : Blo 374761 636221 := bbase (se 3 (by rfl) ⟨119291, by rfl⟩ : syracuseStep 636221 = 238583) (by norm_num)
theorem B955709 : Blo 374761 955709 := bbase (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) (by norm_num)
theorem B849221 : Blo 374761 849221 := bbase (se 4 (by rfl) ⟨79614, by rfl⟩ : syracuseStep 849221 = 159229) (by norm_num)
theorem B562517 : Blo 374761 562517 := bbase (se 14 (by rfl) ⟨51, by rfl⟩ : syracuseStep 562517 = 103) (by norm_num)
theorem B423265 : Blo 374761 423265 := bbase (se 2 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 423265 = 317449) (by norm_num)
theorem B1897829 : Blo 374761 1897829 := bbase (se 4 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 1897829 = 355843) (by norm_num)
theorem B562541 : Blo 374761 562541 := bbase (se 3 (by rfl) ⟨105476, by rfl⟩ : syracuseStep 562541 = 210953) (by norm_num)
theorem B816509 : Blo 374761 816509 := bbase (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) (by norm_num)
theorem B562565 : Blo 374761 562565 := bbase (se 4 (by rfl) ⟨52740, by rfl⟩ : syracuseStep 562565 = 105481) (by norm_num)
theorem B423301 : Blo 374761 423301 := bbase (se 4 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 423301 = 79369) (by norm_num)
theorem B849293 : Blo 374761 849293 := bbase (se 3 (by rfl) ⟨159242, by rfl⟩ : syracuseStep 849293 = 318485) (by norm_num)
theorem B562589 : Blo 374761 562589 := bbase (se 3 (by rfl) ⟨105485, by rfl⟩ : syracuseStep 562589 = 210971) (by norm_num)
theorem B1267109 : Blo 374761 1267109 := bbase (se 4 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 1267109 = 237583) (by norm_num)
theorem B423337 : Blo 374761 423337 := bbase (se 2 (by rfl) ⟨158751, by rfl⟩ : syracuseStep 423337 = 317503) (by norm_num)
theorem B562613 : Blo 374761 562613 := bbase (se 5 (by rfl) ⟨26372, by rfl⟩ : syracuseStep 562613 = 52745) (by norm_num)
theorem B636349 : Blo 374761 636349 := bbase (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) (by norm_num)
theorem B562637 : Blo 374761 562637 := bbase (se 3 (by rfl) ⟨105494, by rfl⟩ : syracuseStep 562637 = 210989) (by norm_num)
theorem B423373 : Blo 374761 423373 := bbase (se 3 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 423373 = 158765) (by norm_num)
theorem B849365 : Blo 374761 849365 := bbase (se 7 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 849365 = 19907) (by norm_num)
theorem B562661 : Blo 374761 562661 := bbase (se 4 (by rfl) ⟨52749, by rfl⟩ : syracuseStep 562661 = 105499) (by norm_num)
theorem B726509 : Blo 374761 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B423409 : Blo 374761 423409 := bbase (se 2 (by rfl) ⟨158778, by rfl⟩ : syracuseStep 423409 = 317557) (by norm_num)
theorem B562685 : Blo 374761 562685 := bbase (se 3 (by rfl) ⟨105503, by rfl⟩ : syracuseStep 562685 = 211007) (by norm_num)
theorem B955901 : Blo 374761 955901 := bbase (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) (by norm_num)
theorem B562709 : Blo 374761 562709 := bbase (se 6 (by rfl) ⟨13188, by rfl⟩ : syracuseStep 562709 = 26377) (by norm_num)
theorem B423445 : Blo 374761 423445 := bbase (se 6 (by rfl) ⟨9924, by rfl⟩ : syracuseStep 423445 = 19849) (by norm_num)
theorem B636437 : Blo 374761 636437 := bbase (se 6 (by rfl) ⟨14916, by rfl⟩ : syracuseStep 636437 = 29833) (by norm_num)
theorem B849437 : Blo 374761 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B562733 : Blo 374761 562733 := bbase (se 3 (by rfl) ⟨105512, by rfl⟩ : syracuseStep 562733 = 211025) (by norm_num)
theorem B2135605 : Blo 374761 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B423481 : Blo 374761 423481 := bbase (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) (by norm_num)
theorem B562757 : Blo 374761 562757 := bbase (se 4 (by rfl) ⟨52758, by rfl⟩ : syracuseStep 562757 = 105517) (by norm_num)
theorem B562781 : Blo 374761 562781 := bbase (se 3 (by rfl) ⟨105521, by rfl⟩ : syracuseStep 562781 = 211043) (by norm_num)
theorem B423517 : Blo 374761 423517 := bbase (se 3 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 423517 = 158819) (by norm_num)
theorem B849509 : Blo 374761 849509 := bbase (se 4 (by rfl) ⟨79641, by rfl⟩ : syracuseStep 849509 = 159283) (by norm_num)
theorem B562805 : Blo 374761 562805 := bbase (se 5 (by rfl) ⟨26381, by rfl⟩ : syracuseStep 562805 = 52763) (by norm_num)
theorem B677501 : Blo 374761 677501 := bbase (se 3 (by rfl) ⟨127031, by rfl⟩ : syracuseStep 677501 = 254063) (by norm_num)
theorem B423553 : Blo 374761 423553 := bbase (se 2 (by rfl) ⟨158832, by rfl⟩ : syracuseStep 423553 = 317665) (by norm_num)
theorem B562829 : Blo 374761 562829 := bbase (se 3 (by rfl) ⟨105530, by rfl⟩ : syracuseStep 562829 = 211061) (by norm_num)
theorem B964237 : Blo 374761 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B636565 : Blo 374761 636565 := bbase (se 6 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 636565 = 29839) (by norm_num)
theorem B562853 : Blo 374761 562853 := bbase (se 4 (by rfl) ⟨52767, by rfl⟩ : syracuseStep 562853 = 105535) (by norm_num)
theorem B423589 : Blo 374761 423589 := bbase (se 4 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 423589 = 79423) (by norm_num)
theorem B849581 : Blo 374761 849581 := bbase (se 3 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 849581 = 318593) (by norm_num)
theorem B2291381 : Blo 374761 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B562877 : Blo 374761 562877 := bbase (se 3 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 562877 = 211079) (by norm_num)
theorem B423625 : Blo 374761 423625 := bbase (se 2 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 423625 = 317719) (by norm_num)
theorem B562901 : Blo 374761 562901 := bbase (se 7 (by rfl) ⟨6596, by rfl⟩ : syracuseStep 562901 = 13193) (by norm_num)
theorem B562925 : Blo 374761 562925 := bbase (se 3 (by rfl) ⟨105548, by rfl⟩ : syracuseStep 562925 = 211097) (by norm_num)
theorem B423661 : Blo 374761 423661 := bbase (se 3 (by rfl) ⟨79436, by rfl⟩ : syracuseStep 423661 = 158873) (by norm_num)
theorem B636653 : Blo 374761 636653 := bbase (se 3 (by rfl) ⟨119372, by rfl⟩ : syracuseStep 636653 = 238745) (by norm_num)
theorem B481013 : Blo 374761 481013 := bbase (se 5 (by rfl) ⟨22547, by rfl⟩ : syracuseStep 481013 = 45095) (by norm_num)
theorem B849653 : Blo 374761 849653 := bbase (se 5 (by rfl) ⟨39827, by rfl⟩ : syracuseStep 849653 = 79655) (by norm_num)
theorem B562949 : Blo 374761 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B423697 : Blo 374761 423697 := bbase (se 2 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 423697 = 317773) (by norm_num)
theorem B562973 : Blo 374761 562973 := bbase (se 3 (by rfl) ⟨105557, by rfl⟩ : syracuseStep 562973 = 211115) (by norm_num)
theorem B562997 : Blo 374761 562997 := bbase (se 5 (by rfl) ⟨26390, by rfl⟩ : syracuseStep 562997 = 52781) (by norm_num)
theorem B3094325 : Blo 374761 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B423733 : Blo 374761 423733 := bbase (se 5 (by rfl) ⟨19862, by rfl⟩ : syracuseStep 423733 = 39725) (by norm_num)
theorem B3143477 : Blo 374761 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B849725 : Blo 374761 849725 := bbase (se 3 (by rfl) ⟨159323, by rfl⟩ : syracuseStep 849725 = 318647) (by norm_num)
theorem B563021 : Blo 374761 563021 := bbase (se 3 (by rfl) ⟨105566, by rfl⟩ : syracuseStep 563021 = 211133) (by norm_num)
theorem B800597 : Blo 374761 800597 := bbase (se 9 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 800597 = 4691) (by norm_num)
theorem B1267541 : Blo 374761 1267541 := bbase (se 9 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 1267541 = 7427) (by norm_num)
theorem B423769 : Blo 374761 423769 := bbase (se 2 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 423769 = 317827) (by norm_num)
theorem B563045 : Blo 374761 563045 := bbase (se 4 (by rfl) ⟨52785, by rfl⟩ : syracuseStep 563045 = 105571) (by norm_num)
theorem B636781 : Blo 374761 636781 := bbase (se 3 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 636781 = 238793) (by norm_num)
theorem B563069 : Blo 374761 563069 := bbase (se 3 (by rfl) ⟨105575, by rfl⟩ : syracuseStep 563069 = 211151) (by norm_num)
theorem B423805 : Blo 374761 423805 := bbase (se 3 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 423805 = 158927) (by norm_num)
theorem B1046405 : Blo 374761 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B849797 : Blo 374761 849797 := bbase (se 4 (by rfl) ⟨79668, by rfl⟩ : syracuseStep 849797 = 159337) (by norm_num)
theorem B563093 : Blo 374761 563093 := bbase (se 6 (by rfl) ⟨13197, by rfl⟩ : syracuseStep 563093 = 26395) (by norm_num)
theorem B645013 : Blo 374761 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B423841 : Blo 374761 423841 := bbase (se 2 (by rfl) ⟨158940, by rfl⟩ : syracuseStep 423841 = 317881) (by norm_num)
theorem B563117 : Blo 374761 563117 := bbase (se 3 (by rfl) ⟨105584, by rfl⟩ : syracuseStep 563117 = 211169) (by norm_num)
theorem B563141 : Blo 374761 563141 := bbase (se 4 (by rfl) ⟨52794, by rfl⟩ : syracuseStep 563141 = 105589) (by norm_num)
theorem B423877 : Blo 374761 423877 := bbase (se 4 (by rfl) ⟨39738, by rfl⟩ : syracuseStep 423877 = 79477) (by norm_num)
theorem B636869 : Blo 374761 636869 := bbase (se 4 (by rfl) ⟨59706, by rfl⟩ : syracuseStep 636869 = 119413) (by norm_num)
theorem B849869 : Blo 374761 849869 := bbase (se 3 (by rfl) ⟨159350, by rfl⟩ : syracuseStep 849869 = 318701) (by norm_num)
theorem B563165 : Blo 374761 563165 := bbase (se 3 (by rfl) ⟨105593, by rfl⟩ : syracuseStep 563165 = 211187) (by norm_num)
theorem B423913 : Blo 374761 423913 := bbase (se 2 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 423913 = 317935) (by norm_num)
theorem B563189 : Blo 374761 563189 := bbase (se 5 (by rfl) ⟨26399, by rfl⟩ : syracuseStep 563189 = 52799) (by norm_num)
theorem B563213 : Blo 374761 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B423949 : Blo 374761 423949 := bbase (se 3 (by rfl) ⟨79490, by rfl⟩ : syracuseStep 423949 = 158981) (by norm_num)
theorem B849941 : Blo 374761 849941 := bbase (se 6 (by rfl) ⟨19920, by rfl⟩ : syracuseStep 849941 = 39841) (by norm_num)
theorem B604189 : Blo 374761 604189 := bbase (se 3 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 604189 = 226571) (by norm_num)
theorem B563237 : Blo 374761 563237 := bbase (se 4 (by rfl) ⟨52803, by rfl⟩ : syracuseStep 563237 = 105607) (by norm_num)
theorem B423985 : Blo 374761 423985 := bbase (se 2 (by rfl) ⟨158994, by rfl⟩ : syracuseStep 423985 = 317989) (by norm_num)
theorem B563261 : Blo 374761 563261 := bbase (se 3 (by rfl) ⟨105611, by rfl⟩ : syracuseStep 563261 = 211223) (by norm_num)
theorem B636997 : Blo 374761 636997 := bbase (se 4 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 636997 = 119437) (by norm_num)
theorem B563285 : Blo 374761 563285 := bbase (se 8 (by rfl) ⟨3300, by rfl⟩ : syracuseStep 563285 = 6601) (by norm_num)
theorem B424021 : Blo 374761 424021 := bbase (se 8 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 424021 = 4969) (by norm_num)
theorem B563309 : Blo 374761 563309 := bbase (se 3 (by rfl) ⟨105620, by rfl⟩ : syracuseStep 563309 = 211241) (by norm_num)
theorem B424057 : Blo 374761 424057 := bbase (se 2 (by rfl) ⟨159021, by rfl⟩ : syracuseStep 424057 = 318043) (by norm_num)
theorem B563333 : Blo 374761 563333 := bbase (se 4 (by rfl) ⟨52812, by rfl⟩ : syracuseStep 563333 = 105625) (by norm_num)
theorem B563357 : Blo 374761 563357 := bbase (se 3 (by rfl) ⟨105629, by rfl⟩ : syracuseStep 563357 = 211259) (by norm_num)
theorem B424093 : Blo 374761 424093 := bbase (se 3 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 424093 = 159035) (by norm_num)
theorem B637085 : Blo 374761 637085 := bbase (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) (by norm_num)
theorem B563381 : Blo 374761 563381 := bbase (se 5 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 563381 = 52817) (by norm_num)
theorem B424129 : Blo 374761 424129 := bbase (se 2 (by rfl) ⟨159048, by rfl⟩ : syracuseStep 424129 = 318097) (by norm_num)
theorem B563405 : Blo 374761 563405 := bbase (se 3 (by rfl) ⟨105638, by rfl⟩ : syracuseStep 563405 = 211277) (by norm_num)
theorem B1906901 : Blo 374761 1906901 := bbase (se 7 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 1906901 = 44693) (by norm_num)
theorem B563429 : Blo 374761 563429 := bbase (se 4 (by rfl) ⟨52821, by rfl⟩ : syracuseStep 563429 = 105643) (by norm_num)
theorem B424165 : Blo 374761 424165 := bbase (se 4 (by rfl) ⟨39765, by rfl⟩ : syracuseStep 424165 = 79531) (by norm_num)
theorem B563453 : Blo 374761 563453 := bbase (se 3 (by rfl) ⟨105647, by rfl⟩ : syracuseStep 563453 = 211295) (by norm_num)
theorem B1267973 : Blo 374761 1267973 := bbase (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) (by norm_num)
theorem B424201 : Blo 374761 424201 := bbase (se 2 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 424201 = 318151) (by norm_num)
theorem B792845 : Blo 374761 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B5773589 : Blo 374761 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B563477 : Blo 374761 563477 := bbase (se 6 (by rfl) ⟨13206, by rfl⟩ : syracuseStep 563477 = 26413) (by norm_num)
theorem B6715669 : Blo 374761 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B637213 : Blo 374761 637213 := bbase (se 3 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 637213 = 238955) (by norm_num)
theorem B1358117 : Blo 374761 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B563501 : Blo 374761 563501 := bbase (se 3 (by rfl) ⟨105656, by rfl⟩ : syracuseStep 563501 = 211313) (by norm_num)
theorem B424237 : Blo 374761 424237 := bbase (se 3 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 424237 = 159089) (by norm_num)
theorem B563525 : Blo 374761 563525 := bbase (se 4 (by rfl) ⟨52830, by rfl⟩ : syracuseStep 563525 = 105661) (by norm_num)
theorem B1431877 : Blo 374761 1431877 := bbase (se 4 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 1431877 = 268477) (by norm_num)
theorem B481609 : Blo 374761 481609 := bbase (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) (by norm_num)
theorem B18340181 : Blo 374761 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B424273 : Blo 374761 424273 := bbase (se 2 (by rfl) ⟨159102, by rfl⟩ : syracuseStep 424273 = 318205) (by norm_num)
theorem B563549 : Blo 374761 563549 := bbase (se 3 (by rfl) ⟨105665, by rfl⟩ : syracuseStep 563549 = 211331) (by norm_num)
theorem B563573 : Blo 374761 563573 := bbase (se 5 (by rfl) ⟨26417, by rfl⟩ : syracuseStep 563573 = 52835) (by norm_num)
theorem B424309 : Blo 374761 424309 := bbase (se 5 (by rfl) ⟨19889, by rfl⟩ : syracuseStep 424309 = 39779) (by norm_num)
theorem B637301 : Blo 374761 637301 := bbase (se 5 (by rfl) ⟨29873, by rfl⟩ : syracuseStep 637301 = 59747) (by norm_num)
theorem B1628549 : Blo 374761 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B563597 : Blo 374761 563597 := bbase (se 3 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 563597 = 211349) (by norm_num)
theorem B424345 : Blo 374761 424345 := bbase (se 2 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 424345 = 318259) (by norm_num)
theorem B563621 : Blo 374761 563621 := bbase (se 4 (by rfl) ⟨52839, by rfl⟩ : syracuseStep 563621 = 105679) (by norm_num)
theorem B563645 : Blo 374761 563645 := bbase (se 3 (by rfl) ⟨105683, by rfl⟩ : syracuseStep 563645 = 211367) (by norm_num)
theorem B424381 : Blo 374761 424381 := bbase (se 3 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 424381 = 159143) (by norm_num)
theorem B563669 : Blo 374761 563669 := bbase (se 7 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 563669 = 13211) (by norm_num)
theorem B424417 : Blo 374761 424417 := bbase (se 2 (by rfl) ⟨159156, by rfl⟩ : syracuseStep 424417 = 318313) (by norm_num)
theorem B563693 : Blo 374761 563693 := bbase (se 3 (by rfl) ⟨105692, by rfl⟩ : syracuseStep 563693 = 211385) (by norm_num)
theorem B637429 : Blo 374761 637429 := bbase (se 5 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 637429 = 59759) (by norm_num)
theorem B563717 : Blo 374761 563717 := bbase (se 4 (by rfl) ⟨52848, by rfl⟩ : syracuseStep 563717 = 105697) (by norm_num)
theorem B424453 : Blo 374761 424453 := bbase (se 4 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 424453 = 79585) (by norm_num)
theorem B563741 : Blo 374761 563741 := bbase (se 3 (by rfl) ⟨105701, by rfl⟩ : syracuseStep 563741 = 211403) (by norm_num)
theorem B948773 : Blo 374761 948773 := bbase (se 4 (by rfl) ⟨88947, by rfl⟩ : syracuseStep 948773 = 177895) (by norm_num)
theorem B424489 : Blo 374761 424489 := bbase (se 2 (by rfl) ⟨159183, by rfl⟩ : syracuseStep 424489 = 318367) (by norm_num)
theorem B563765 : Blo 374761 563765 := bbase (se 5 (by rfl) ⟨26426, by rfl⟩ : syracuseStep 563765 = 52853) (by norm_num)
theorem B563789 : Blo 374761 563789 := bbase (se 3 (by rfl) ⟨105710, by rfl⟩ : syracuseStep 563789 = 211421) (by norm_num)
theorem B424525 : Blo 374761 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B612941 : Blo 374761 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B645725 : Blo 374761 645725 := bbase (se 3 (by rfl) ⟨121073, by rfl⟩ : syracuseStep 645725 = 242147) (by norm_num)
theorem B563813 : Blo 374761 563813 := bbase (se 4 (by rfl) ⟨52857, by rfl⟩ : syracuseStep 563813 = 105715) (by norm_num)
theorem B1088101 : Blo 374761 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B424561 : Blo 374761 424561 := bbase (se 2 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 424561 = 318421) (by norm_num)
theorem B1899125 : Blo 374761 1899125 := bbase (se 5 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 1899125 = 178043) (by norm_num)
theorem B1432181 : Blo 374761 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B563837 : Blo 374761 563837 := bbase (se 3 (by rfl) ⟨105719, by rfl⟩ : syracuseStep 563837 = 211439) (by norm_num)
theorem B563861 : Blo 374761 563861 := bbase (se 6 (by rfl) ⟨13215, by rfl⟩ : syracuseStep 563861 = 26431) (by norm_num)
theorem B424597 : Blo 374761 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B604837 : Blo 374761 604837 := bbase (se 4 (by rfl) ⟨56703, by rfl⟩ : syracuseStep 604837 = 113407) (by norm_num)
theorem B563885 : Blo 374761 563885 := bbase (se 3 (by rfl) ⟨105728, by rfl⟩ : syracuseStep 563885 = 211457) (by norm_num)
theorem B1268405 : Blo 374761 1268405 := bbase (se 5 (by rfl) ⟨59456, by rfl⟩ : syracuseStep 1268405 = 118913) (by norm_num)
theorem B3480245 : Blo 374761 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B424633 : Blo 374761 424633 := bbase (se 2 (by rfl) ⟨159237, by rfl⟩ : syracuseStep 424633 = 318475) (by norm_num)
theorem B916157 : Blo 374761 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B563909 : Blo 374761 563909 := bbase (se 4 (by rfl) ⟨52866, by rfl⟩ : syracuseStep 563909 = 105733) (by norm_num)
theorem B801485 : Blo 374761 801485 := bbase (se 3 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 801485 = 300557) (by norm_num)
theorem B563933 : Blo 374761 563933 := bbase (se 3 (by rfl) ⟨105737, by rfl⟩ : syracuseStep 563933 = 211475) (by norm_num)
theorem B424669 : Blo 374761 424669 := bbase (se 3 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 424669 = 159251) (by norm_num)
theorem B1424101 : Blo 374761 1424101 := bbase (se 4 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 1424101 = 267019) (by norm_num)
theorem B563957 : Blo 374761 563957 := bbase (se 5 (by rfl) ⟨26435, by rfl⟩ : syracuseStep 563957 = 52871) (by norm_num)
theorem B424705 : Blo 374761 424705 := bbase (se 2 (by rfl) ⟨159264, by rfl⟩ : syracuseStep 424705 = 318529) (by norm_num)
theorem B563981 : Blo 374761 563981 := bbase (se 3 (by rfl) ⟨105746, by rfl⟩ : syracuseStep 563981 = 211493) (by norm_num)
theorem B1071893 : Blo 374761 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B564005 : Blo 374761 564005 := bbase (se 4 (by rfl) ⟨52875, by rfl⟩ : syracuseStep 564005 = 105751) (by norm_num)
theorem B424741 : Blo 374761 424741 := bbase (se 4 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 424741 = 79639) (by norm_num)
theorem B564029 : Blo 374761 564029 := bbase (se 3 (by rfl) ⟨105755, by rfl⟩ : syracuseStep 564029 = 211511) (by norm_num)
theorem B424777 : Blo 374761 424777 := bbase (se 2 (by rfl) ⟨159291, by rfl⟩ : syracuseStep 424777 = 318583) (by norm_num)
theorem B564053 : Blo 374761 564053 := bbase (se 9 (by rfl) ⟨1652, by rfl⟩ : syracuseStep 564053 = 3305) (by norm_num)
theorem B1358693 : Blo 374761 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B564077 : Blo 374761 564077 := bbase (se 3 (by rfl) ⟨105764, by rfl⟩ : syracuseStep 564077 = 211529) (by norm_num)
theorem B424813 : Blo 374761 424813 := bbase (se 3 (by rfl) ⟨79652, by rfl⟩ : syracuseStep 424813 = 159305) (by norm_num)
theorem B949117 : Blo 374761 949117 := bbase (se 3 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 949117 = 355919) (by norm_num)
theorem B564101 : Blo 374761 564101 := bbase (se 4 (by rfl) ⟨52884, by rfl⟩ : syracuseStep 564101 = 105769) (by norm_num)
theorem B424849 : Blo 374761 424849 := bbase (se 2 (by rfl) ⟨159318, by rfl⟩ : syracuseStep 424849 = 318637) (by norm_num)
theorem B564125 : Blo 374761 564125 := bbase (se 3 (by rfl) ⟨105773, by rfl⟩ : syracuseStep 564125 = 211547) (by norm_num)
theorem B1612709 : Blo 374761 1612709 := bbase (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) (by norm_num)
theorem B564149 : Blo 374761 564149 := bbase (se 5 (by rfl) ⟨26444, by rfl⟩ : syracuseStep 564149 = 52889) (by norm_num)
theorem B572341 : Blo 374761 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B424885 : Blo 374761 424885 := bbase (se 5 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 424885 = 39833) (by norm_num)
theorem B867269 : Blo 374761 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B801733 : Blo 374761 801733 := bbase (se 4 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 801733 = 150325) (by norm_num)
theorem B564173 : Blo 374761 564173 := bbase (se 3 (by rfl) ⟨105782, by rfl⟩ : syracuseStep 564173 = 211565) (by norm_num)
theorem B424921 : Blo 374761 424921 := bbase (se 2 (by rfl) ⟨159345, by rfl⟩ : syracuseStep 424921 = 318691) (by norm_num)
theorem B564197 : Blo 374761 564197 := bbase (se 4 (by rfl) ⟨52893, by rfl⟩ : syracuseStep 564197 = 105787) (by norm_num)
theorem B949229 : Blo 374761 949229 := bbase (se 3 (by rfl) ⟨177980, by rfl⟩ : syracuseStep 949229 = 355961) (by norm_num)
theorem B564221 : Blo 374761 564221 := bbase (se 3 (by rfl) ⟨105791, by rfl⟩ : syracuseStep 564221 = 211583) (by norm_num)
theorem B424957 : Blo 374761 424957 := bbase (se 3 (by rfl) ⟨79679, by rfl⟩ : syracuseStep 424957 = 159359) (by norm_num)
theorem B1424405 : Blo 374761 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B564245 : Blo 374761 564245 := bbase (se 6 (by rfl) ⟨13224, by rfl⟩ : syracuseStep 564245 = 26449) (by norm_num)
theorem B564269 : Blo 374761 564269 := bbase (se 3 (by rfl) ⟨105800, by rfl⟩ : syracuseStep 564269 = 211601) (by norm_num)
theorem B916525 : Blo 374761 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B2407477 : Blo 374761 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B564293 : Blo 374761 564293 := bbase (se 4 (by rfl) ⟨52902, by rfl⟩ : syracuseStep 564293 = 105805) (by norm_num)
theorem B400469 : Blo 374761 400469 := bbase (se 8 (by rfl) ⟨2346, by rfl⟩ : syracuseStep 400469 = 4693) (by norm_num)
theorem B15416405 : Blo 374761 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B564317 : Blo 374761 564317 := bbase (se 3 (by rfl) ⟨105809, by rfl⟩ : syracuseStep 564317 = 211619) (by norm_num)
theorem B1268837 : Blo 374761 1268837 := bbase (se 4 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 1268837 = 237907) (by norm_num)
theorem B564341 : Blo 374761 564341 := bbase (se 5 (by rfl) ⟨26453, by rfl⟩ : syracuseStep 564341 = 52907) (by norm_num)
theorem B564365 : Blo 374761 564365 := bbase (se 3 (by rfl) ⟨105818, by rfl⟩ : syracuseStep 564365 = 211637) (by norm_num)
theorem B564389 : Blo 374761 564389 := bbase (se 4 (by rfl) ⟨52911, by rfl⟩ : syracuseStep 564389 = 105823) (by norm_num)
theorem B1434293 : Blo 374761 1434293 := bbase (se 5 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 1434293 = 134465) (by norm_num)
theorem B949421 : Blo 374761 949421 := bbase (se 3 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 949421 = 356033) (by norm_num)
theorem B2858165 : Blo 374761 2858165 := bbase (se 5 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 2858165 = 267953) (by norm_num)
theorem B564413 : Blo 374761 564413 := bbase (se 3 (by rfl) ⟨105827, by rfl⟩ : syracuseStep 564413 = 211655) (by norm_num)
theorem B564437 : Blo 374761 564437 := bbase (se 7 (by rfl) ⟨6614, by rfl⟩ : syracuseStep 564437 = 13229) (by norm_num)
theorem B564461 : Blo 374761 564461 := bbase (se 3 (by rfl) ⟨105836, by rfl⟩ : syracuseStep 564461 = 211673) (by norm_num)
theorem B580853 : Blo 374761 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B761093 : Blo 374761 761093 := bbase (se 4 (by rfl) ⟨71352, by rfl⟩ : syracuseStep 761093 = 142705) (by norm_num)
theorem B564485 : Blo 374761 564485 := bbase (se 4 (by rfl) ⟨52920, by rfl⟩ : syracuseStep 564485 = 105841) (by norm_num)
theorem B564509 : Blo 374761 564509 := bbase (se 3 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 564509 = 211691) (by norm_num)
theorem B752933 : Blo 374761 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B1015093 : Blo 374761 1015093 := bbase (se 5 (by rfl) ⟨47582, by rfl⟩ : syracuseStep 1015093 = 95165) (by norm_num)
theorem B564533 : Blo 374761 564533 := bbase (se 5 (by rfl) ⟨26462, by rfl⟩ : syracuseStep 564533 = 52925) (by norm_num)
theorem B474437 : Blo 374761 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B400717 : Blo 374761 400717 := bbase (se 3 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 400717 = 150269) (by norm_num)
theorem B564557 : Blo 374761 564557 := bbase (se 3 (by rfl) ⟨105854, by rfl⟩ : syracuseStep 564557 = 211709) (by norm_num)
theorem B15621461 : Blo 374761 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B564581 : Blo 374761 564581 := bbase (se 4 (by rfl) ⟨52929, by rfl⟩ : syracuseStep 564581 = 105859) (by norm_num)
theorem B474493 : Blo 374761 474493 := bbase (se 3 (by rfl) ⟨88967, by rfl⟩ : syracuseStep 474493 = 177935) (by norm_num)
theorem B564605 : Blo 374761 564605 := bbase (se 3 (by rfl) ⟨105863, by rfl⟩ : syracuseStep 564605 = 211727) (by norm_num)
theorem B564629 : Blo 374761 564629 := bbase (se 6 (by rfl) ⟨13233, by rfl⟩ : syracuseStep 564629 = 26467) (by norm_num)
theorem B564653 : Blo 374761 564653 := bbase (se 3 (by rfl) ⟨105872, by rfl⟩ : syracuseStep 564653 = 211745) (by norm_num)
theorem B1072565 : Blo 374761 1072565 := bbase (se 5 (by rfl) ⟨50276, by rfl⟩ : syracuseStep 1072565 = 100553) (by norm_num)
theorem B802237 : Blo 374761 802237 := bbase (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) (by norm_num)
theorem B564677 : Blo 374761 564677 := bbase (se 4 (by rfl) ⟨52938, by rfl⟩ : syracuseStep 564677 = 105877) (by norm_num)
theorem B474589 : Blo 374761 474589 := bbase (se 3 (by rfl) ⟨88985, by rfl⟩ : syracuseStep 474589 = 177971) (by norm_num)
theorem B564701 : Blo 374761 564701 := bbase (se 3 (by rfl) ⟨105881, by rfl⟩ : syracuseStep 564701 = 211763) (by norm_num)
theorem B712165 : Blo 374761 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B1908197 : Blo 374761 1908197 := bbase (se 4 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 1908197 = 357787) (by norm_num)
theorem B843245 : Blo 374761 843245 := bbase (se 3 (by rfl) ⟨158108, by rfl⟩ : syracuseStep 843245 = 316217) (by norm_num)
theorem B2137589 : Blo 374761 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B564725 : Blo 374761 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B949765 : Blo 374761 949765 := bbase (se 4 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 949765 = 178081) (by norm_num)
theorem B564749 : Blo 374761 564749 := bbase (se 3 (by rfl) ⟨105890, by rfl⟩ : syracuseStep 564749 = 211781) (by norm_num)
theorem B1269269 : Blo 374761 1269269 := bbase (se 6 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 1269269 = 59497) (by norm_num)
theorem B564773 : Blo 374761 564773 := bbase (se 4 (by rfl) ⟨52947, by rfl⟩ : syracuseStep 564773 = 105895) (by norm_num)
theorem B843317 : Blo 374761 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B564797 : Blo 374761 564797 := bbase (se 3 (by rfl) ⟨105899, by rfl⟩ : syracuseStep 564797 = 211799) (by norm_num)
theorem B20012629 : Blo 374761 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B2850389 : Blo 374761 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B564821 : Blo 374761 564821 := bbase (se 8 (by rfl) ⟨3309, by rfl⟩ : syracuseStep 564821 = 6619) (by norm_num)
theorem B564845 : Blo 374761 564845 := bbase (se 3 (by rfl) ⟨105908, by rfl⟩ : syracuseStep 564845 = 211817) (by norm_num)
theorem B712309 : Blo 374761 712309 := bbase (se 5 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 712309 = 66779) (by norm_num)
theorem B949877 : Blo 374761 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B843389 : Blo 374761 843389 := bbase (se 3 (by rfl) ⟨158135, by rfl⟩ : syracuseStep 843389 = 316271) (by norm_num)
theorem B564869 : Blo 374761 564869 := bbase (se 4 (by rfl) ⟨52956, by rfl⟩ : syracuseStep 564869 = 105913) (by norm_num)
theorem B474761 : Blo 374761 474761 := bbase (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) (by norm_num)
theorem B917149 : Blo 374761 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B564893 : Blo 374761 564893 := bbase (se 3 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 564893 = 211835) (by norm_num)
theorem B1203893 : Blo 374761 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B564917 : Blo 374761 564917 := bbase (se 5 (by rfl) ⟨26480, by rfl⟩ : syracuseStep 564917 = 52961) (by norm_num)
theorem B474817 : Blo 374761 474817 := bbase (se 2 (by rfl) ⟨178056, by rfl⟩ : syracuseStep 474817 = 356113) (by norm_num)
theorem B450245 : Blo 374761 450245 := bbase (se 4 (by rfl) ⟨42210, by rfl⟩ : syracuseStep 450245 = 84421) (by norm_num)
theorem B843461 : Blo 374761 843461 := bbase (se 4 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 843461 = 158149) (by norm_num)
theorem B900805 : Blo 374761 900805 := bbase (se 4 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 900805 = 168901) (by norm_num)
theorem B564941 : Blo 374761 564941 := bbase (se 3 (by rfl) ⟨105926, by rfl⟩ : syracuseStep 564941 = 211853) (by norm_num)
theorem B564965 : Blo 374761 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B564989 : Blo 374761 564989 := bbase (se 3 (by rfl) ⟨105935, by rfl⟩ : syracuseStep 564989 = 211871) (by norm_num)
theorem B401161 : Blo 374761 401161 := bbase (se 2 (by rfl) ⟨150435, by rfl⟩ : syracuseStep 401161 = 300871) (by norm_num)
theorem B843533 : Blo 374761 843533 := bbase (se 3 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 843533 = 316325) (by norm_num)
theorem B712469 : Blo 374761 712469 := bbase (se 6 (by rfl) ⟨16698, by rfl⟩ : syracuseStep 712469 = 33397) (by norm_num)
theorem B565013 : Blo 374761 565013 := bbase (se 6 (by rfl) ⟨13242, by rfl⟩ : syracuseStep 565013 = 26485) (by norm_num)
theorem B474913 : Blo 374761 474913 := bbase (se 2 (by rfl) ⟨178092, by rfl⟩ : syracuseStep 474913 = 356185) (by norm_num)
theorem B565037 : Blo 374761 565037 := bbase (se 3 (by rfl) ⟨105944, by rfl⟩ : syracuseStep 565037 = 211889) (by norm_num)
theorem B950069 : Blo 374761 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B1834805 : Blo 374761 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B507709 : Blo 374761 507709 := bbase (se 3 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 507709 = 190391) (by norm_num)
theorem B401221 : Blo 374761 401221 := bbase (se 4 (by rfl) ⟨37614, by rfl⟩ : syracuseStep 401221 = 75229) (by norm_num)
theorem B565061 : Blo 374761 565061 := bbase (se 4 (by rfl) ⟨52974, by rfl⟩ : syracuseStep 565061 = 105949) (by norm_num)
theorem B843605 : Blo 374761 843605 := bbase (se 9 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 843605 = 4943) (by norm_num)
theorem B565085 : Blo 374761 565085 := bbase (se 3 (by rfl) ⟨105953, by rfl⟩ : syracuseStep 565085 = 211907) (by norm_num)
theorem B1072997 : Blo 374761 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B565109 : Blo 374761 565109 := bbase (se 5 (by rfl) ⟨26489, by rfl⟩ : syracuseStep 565109 = 52979) (by norm_num)
theorem B1900421 : Blo 374761 1900421 := bbase (se 4 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 1900421 = 356329) (by norm_num)
theorem B565133 : Blo 374761 565133 := bbase (se 3 (by rfl) ⟨105962, by rfl⟩ : syracuseStep 565133 = 211925) (by norm_num)
theorem B843677 : Blo 374761 843677 := bbase (se 3 (by rfl) ⟨158189, by rfl⟩ : syracuseStep 843677 = 316379) (by norm_num)
theorem B712613 : Blo 374761 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B565157 : Blo 374761 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B901037 : Blo 374761 901037 := bbase (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) (by norm_num)
theorem B565181 : Blo 374761 565181 := bbase (se 3 (by rfl) ⟨105971, by rfl⟩ : syracuseStep 565181 = 211943) (by norm_num)
theorem B1269701 : Blo 374761 1269701 := bbase (se 4 (by rfl) ⟨119034, by rfl⟩ : syracuseStep 1269701 = 238069) (by norm_num)
theorem B475085 : Blo 374761 475085 := bbase (se 3 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 475085 = 178157) (by norm_num)
theorem B565205 : Blo 374761 565205 := bbase (se 7 (by rfl) ⟨6623, by rfl⟩ : syracuseStep 565205 = 13247) (by norm_num)
theorem B843749 : Blo 374761 843749 := bbase (se 4 (by rfl) ⟨79101, by rfl⟩ : syracuseStep 843749 = 158203) (by norm_num)
theorem B565229 : Blo 374761 565229 := bbase (se 3 (by rfl) ⟨105980, by rfl⟩ : syracuseStep 565229 = 211961) (by norm_num)
theorem B1351669 : Blo 374761 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B376835 : Blo 374761 376835 := bstep (se 1 (by rfl) ⟨282626, by rfl⟩ : syracuseStep 376835 = 565253) B565253
theorem B565265 : Blo 374761 565265 := bstep (se 2 (by rfl) ⟨211974, by rfl⟩ : syracuseStep 565265 = 423949) B423949
theorem B376851 : Blo 374761 376851 := bstep (se 1 (by rfl) ⟨282638, by rfl⟩ : syracuseStep 376851 = 565277) B565277
theorem B565283 : Blo 374761 565283 := bstep (se 1 (by rfl) ⟨423962, by rfl⟩ : syracuseStep 565283 = 847925) B847925
theorem B376867 : Blo 374761 376867 := bstep (se 1 (by rfl) ⟨282650, by rfl⟩ : syracuseStep 376867 = 565301) B565301
theorem B1269809 : Blo 374761 1269809 := bstep (se 2 (by rfl) ⟨476178, by rfl⟩ : syracuseStep 1269809 = 952357) B952357
theorem B376883 : Blo 374761 376883 := bstep (se 1 (by rfl) ⟨282662, by rfl⟩ : syracuseStep 376883 = 565325) B565325
theorem B565313 : Blo 374761 565313 := bstep (se 2 (by rfl) ⟨211992, by rfl⟩ : syracuseStep 565313 = 423985) B423985
theorem B376899 : Blo 374761 376899 := bstep (se 1 (by rfl) ⟨282674, by rfl⟩ : syracuseStep 376899 = 565349) B565349
theorem B843857 : Blo 374761 843857 := bstep (se 2 (by rfl) ⟨316446, by rfl⟩ : syracuseStep 843857 = 632893) B632893
theorem B565331 : Blo 374761 565331 := bstep (se 1 (by rfl) ⟨423998, by rfl⟩ : syracuseStep 565331 = 847997) B847997
theorem B376915 : Blo 374761 376915 := bstep (se 1 (by rfl) ⟨282686, by rfl⟩ : syracuseStep 376915 = 565373) B565373
theorem B843875 : Blo 374761 843875 := bstep (se 1 (by rfl) ⟨632906, by rfl⟩ : syracuseStep 843875 = 1265813) B1265813
theorem B376931 : Blo 374761 376931 := bstep (se 1 (by rfl) ⟨282698, by rfl⟩ : syracuseStep 376931 = 565397) B565397
theorem B565361 : Blo 374761 565361 := bstep (se 2 (by rfl) ⟨212010, by rfl⟩ : syracuseStep 565361 = 424021) B424021
theorem B376947 : Blo 374761 376947 := bstep (se 1 (by rfl) ⟨282710, by rfl⟩ : syracuseStep 376947 = 565421) B565421
theorem B565379 : Blo 374761 565379 := bstep (se 1 (by rfl) ⟨424034, by rfl⟩ : syracuseStep 565379 = 848069) B848069
theorem B376963 : Blo 374761 376963 := bstep (se 1 (by rfl) ⟨282722, by rfl⟩ : syracuseStep 376963 = 565445) B565445
theorem B376979 : Blo 374761 376979 := bstep (se 1 (by rfl) ⟨282734, by rfl⟩ : syracuseStep 376979 = 565469) B565469
theorem B1097891 : Blo 374761 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B565409 : Blo 374761 565409 := bstep (se 2 (by rfl) ⟨212028, by rfl⟩ : syracuseStep 565409 = 424057) B424057
theorem B376995 : Blo 374761 376995 := bstep (se 1 (by rfl) ⟨282746, by rfl⟩ : syracuseStep 376995 = 565493) B565493
theorem B565427 : Blo 374761 565427 := bstep (se 1 (by rfl) ⟨424070, by rfl⟩ : syracuseStep 565427 = 848141) B848141
theorem B377011 : Blo 374761 377011 := bstep (se 1 (by rfl) ⟨282758, by rfl⟩ : syracuseStep 377011 = 565517) B565517
theorem B1016003 : Blo 374761 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B377027 : Blo 374761 377027 := bstep (se 1 (by rfl) ⟨282770, by rfl⟩ : syracuseStep 377027 = 565541) B565541
theorem B6119621 : Blo 374761 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B565457 : Blo 374761 565457 := bstep (se 2 (by rfl) ⟨212046, by rfl⟩ : syracuseStep 565457 = 424093) B424093
theorem B377043 : Blo 374761 377043 := bstep (se 1 (by rfl) ⟨282782, by rfl⟩ : syracuseStep 377043 = 565565) B565565
theorem B2138339 : Blo 374761 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B565475 : Blo 374761 565475 := bstep (se 1 (by rfl) ⟨424106, by rfl⟩ : syracuseStep 565475 = 848213) B848213
theorem B377059 : Blo 374761 377059 := bstep (se 1 (by rfl) ⟨282794, by rfl⟩ : syracuseStep 377059 = 565589) B565589
theorem B377075 : Blo 374761 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B565505 : Blo 374761 565505 := bstep (se 2 (by rfl) ⟨212064, by rfl⟩ : syracuseStep 565505 = 424129) B424129
theorem B1204483 : Blo 374761 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B377091 : Blo 374761 377091 := bstep (se 1 (by rfl) ⟨282818, by rfl⟩ : syracuseStep 377091 = 565637) B565637
theorem B565523 : Blo 374761 565523 := bstep (se 1 (by rfl) ⟨424142, by rfl⟩ : syracuseStep 565523 = 848285) B848285
theorem B377107 : Blo 374761 377107 := bstep (se 1 (by rfl) ⟨282830, by rfl⟩ : syracuseStep 377107 = 565661) B565661
theorem B377123 : Blo 374761 377123 := bstep (se 1 (by rfl) ⟨282842, by rfl⟩ : syracuseStep 377123 = 565685) B565685
theorem B565553 : Blo 374761 565553 := bstep (se 2 (by rfl) ⟨212082, by rfl⟩ : syracuseStep 565553 = 424165) B424165
theorem B377139 : Blo 374761 377139 := bstep (se 1 (by rfl) ⟨282854, by rfl⟩ : syracuseStep 377139 = 565709) B565709
theorem B565571 : Blo 374761 565571 := bstep (se 1 (by rfl) ⟨424178, by rfl⟩ : syracuseStep 565571 = 848357) B848357
theorem B377155 : Blo 374761 377155 := bstep (se 1 (by rfl) ⟨282866, by rfl⟩ : syracuseStep 377155 = 565733) B565733
theorem B377171 : Blo 374761 377171 := bstep (se 1 (by rfl) ⟨282878, by rfl⟩ : syracuseStep 377171 = 565757) B565757
theorem B565601 : Blo 374761 565601 := bstep (se 2 (by rfl) ⟨212100, by rfl⟩ : syracuseStep 565601 = 424201) B424201
theorem B811363 : Blo 374761 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B377187 : Blo 374761 377187 := bstep (se 1 (by rfl) ⟨282890, by rfl⟩ : syracuseStep 377187 = 565781) B565781
theorem B844145 : Blo 374761 844145 := bstep (se 2 (by rfl) ⟨316554, by rfl⟩ : syracuseStep 844145 = 633109) B633109
theorem B901489 : Blo 374761 901489 := bstep (se 2 (by rfl) ⟨338058, by rfl⟩ : syracuseStep 901489 = 676117) B676117
theorem B565619 : Blo 374761 565619 := bstep (se 1 (by rfl) ⟨424214, by rfl⟩ : syracuseStep 565619 = 848429) B848429
theorem B377203 : Blo 374761 377203 := bstep (se 1 (by rfl) ⟨282902, by rfl⟩ : syracuseStep 377203 = 565805) B565805
theorem B8954225 : Blo 374761 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B844163 : Blo 374761 844163 := bstep (se 1 (by rfl) ⟨633122, by rfl⟩ : syracuseStep 844163 = 1266245) B1266245
theorem B377219 : Blo 374761 377219 := bstep (se 1 (by rfl) ⟨282914, by rfl⟩ : syracuseStep 377219 = 565829) B565829
theorem B565649 : Blo 374761 565649 := bstep (se 2 (by rfl) ⟨212118, by rfl⟩ : syracuseStep 565649 = 424237) B424237
theorem B377235 : Blo 374761 377235 := bstep (se 1 (by rfl) ⟨282926, by rfl⟩ : syracuseStep 377235 = 565853) B565853
theorem B565667 : Blo 374761 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B377251 : Blo 374761 377251 := bstep (se 1 (by rfl) ⟨282938, by rfl⟩ : syracuseStep 377251 = 565877) B565877
theorem B713137 : Blo 374761 713137 := bstep (se 2 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 713137 = 534853) B534853
theorem B1909169 : Blo 374761 1909169 := bstep (se 2 (by rfl) ⟨715938, by rfl⟩ : syracuseStep 1909169 = 1431877) B1431877
theorem B475571 : Blo 374761 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B377267 : Blo 374761 377267 := bstep (se 1 (by rfl) ⟨282950, by rfl⟩ : syracuseStep 377267 = 565901) B565901
theorem B565697 : Blo 374761 565697 := bstep (se 2 (by rfl) ⟨212136, by rfl⟩ : syracuseStep 565697 = 424273) B424273
theorem B377283 : Blo 374761 377283 := bstep (se 1 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 377283 = 565925) B565925
theorem B950737 : Blo 374761 950737 := bstep (se 2 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 950737 = 713053) B713053
theorem B565715 : Blo 374761 565715 := bstep (se 1 (by rfl) ⟨424286, by rfl⟩ : syracuseStep 565715 = 848573) B848573
theorem B377299 : Blo 374761 377299 := bstep (se 1 (by rfl) ⟨282974, by rfl⟩ : syracuseStep 377299 = 565949) B565949
theorem B377315 : Blo 374761 377315 := bstep (se 1 (by rfl) ⟨282986, by rfl⟩ : syracuseStep 377315 = 565973) B565973
theorem B680419 : Blo 374761 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B565745 : Blo 374761 565745 := bstep (se 2 (by rfl) ⟨212154, by rfl⟩ : syracuseStep 565745 = 424309) B424309
theorem B377331 : Blo 374761 377331 := bstep (se 1 (by rfl) ⟨282998, by rfl⟩ : syracuseStep 377331 = 565997) B565997
theorem B565763 : Blo 374761 565763 := bstep (se 1 (by rfl) ⟨424322, by rfl⟩ : syracuseStep 565763 = 848645) B848645
theorem B377347 : Blo 374761 377347 := bstep (se 1 (by rfl) ⟨283010, by rfl⟩ : syracuseStep 377347 = 566021) B566021
theorem B1901069 : Blo 374761 1901069 := bstep (se 3 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 1901069 = 712901) B712901
theorem B1434125 : Blo 374761 1434125 := bstep (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) B537797
theorem B1204753 : Blo 374761 1204753 := bstep (se 2 (by rfl) ⟨451782, by rfl⟩ : syracuseStep 1204753 = 903565) B903565
theorem B1073681 : Blo 374761 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B377363 : Blo 374761 377363 := bstep (se 1 (by rfl) ⟨283022, by rfl⟩ : syracuseStep 377363 = 566045) B566045
theorem B565793 : Blo 374761 565793 := bstep (se 2 (by rfl) ⟨212172, by rfl⟩ : syracuseStep 565793 = 424345) B424345
theorem B377379 : Blo 374761 377379 := bstep (se 1 (by rfl) ⟨283034, by rfl⟩ : syracuseStep 377379 = 566069) B566069
theorem B565811 : Blo 374761 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B377395 : Blo 374761 377395 := bstep (se 1 (by rfl) ⟨283046, by rfl⟩ : syracuseStep 377395 = 566093) B566093
theorem B377411 : Blo 374761 377411 := bstep (se 1 (by rfl) ⟨283058, by rfl⟩ : syracuseStep 377411 = 566117) B566117
theorem B1270349 : Blo 374761 1270349 := bstep (se 3 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 1270349 = 476381) B476381
theorem B565841 : Blo 374761 565841 := bstep (se 2 (by rfl) ⟨212190, by rfl⟩ : syracuseStep 565841 = 424381) B424381
theorem B377427 : Blo 374761 377427 := bstep (se 1 (by rfl) ⟨283070, by rfl⟩ : syracuseStep 377427 = 566141) B566141
theorem B565859 : Blo 374761 565859 := bstep (se 1 (by rfl) ⟨424394, by rfl⟩ : syracuseStep 565859 = 848789) B848789
theorem B377443 : Blo 374761 377443 := bstep (se 1 (by rfl) ⟨283082, by rfl⟩ : syracuseStep 377443 = 566165) B566165
theorem B377459 : Blo 374761 377459 := bstep (se 1 (by rfl) ⟨283094, by rfl⟩ : syracuseStep 377459 = 566189) B566189
theorem B565889 : Blo 374761 565889 := bstep (se 2 (by rfl) ⟨212208, by rfl⟩ : syracuseStep 565889 = 424417) B424417
theorem B1270403 : Blo 374761 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B377475 : Blo 374761 377475 := bstep (se 1 (by rfl) ⟨283106, by rfl⟩ : syracuseStep 377475 = 566213) B566213
theorem B680579 : Blo 374761 680579 := bstep (se 1 (by rfl) ⟨510434, by rfl⟩ : syracuseStep 680579 = 1020869) B1020869
theorem B1548941 : Blo 374761 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B844433 : Blo 374761 844433 := bstep (se 2 (by rfl) ⟨316662, by rfl⟩ : syracuseStep 844433 = 633325) B633325
theorem B565907 : Blo 374761 565907 := bstep (se 1 (by rfl) ⟨424430, by rfl⟩ : syracuseStep 565907 = 848861) B848861
theorem B2040461 : Blo 374761 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B377491 : Blo 374761 377491 := bstep (se 1 (by rfl) ⟨283118, by rfl⟩ : syracuseStep 377491 = 566237) B566237
theorem B844451 : Blo 374761 844451 := bstep (se 1 (by rfl) ⟨633338, by rfl⟩ : syracuseStep 844451 = 1266677) B1266677
theorem B377507 : Blo 374761 377507 := bstep (se 1 (by rfl) ⟨283130, by rfl⟩ : syracuseStep 377507 = 566261) B566261
theorem B565937 : Blo 374761 565937 := bstep (se 2 (by rfl) ⟨212226, by rfl⟩ : syracuseStep 565937 = 424453) B424453
theorem B377523 : Blo 374761 377523 := bstep (se 1 (by rfl) ⟨283142, by rfl⟩ : syracuseStep 377523 = 566285) B566285
theorem B565955 : Blo 374761 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B377539 : Blo 374761 377539 := bstep (se 1 (by rfl) ⟨283154, by rfl⟩ : syracuseStep 377539 = 566309) B566309
theorem B402131 : Blo 374761 402131 := bstep (se 1 (by rfl) ⟨301598, by rfl⟩ : syracuseStep 402131 = 603197) B603197
theorem B377555 : Blo 374761 377555 := bstep (se 1 (by rfl) ⟨283166, by rfl⟩ : syracuseStep 377555 = 566333) B566333
theorem B565985 : Blo 374761 565985 := bstep (se 2 (by rfl) ⟨212244, by rfl⟩ : syracuseStep 565985 = 424489) B424489
theorem B951011 : Blo 374761 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B377571 : Blo 374761 377571 := bstep (se 1 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 377571 = 566357) B566357
theorem B566003 : Blo 374761 566003 := bstep (se 1 (by rfl) ⟨424502, by rfl⟩ : syracuseStep 566003 = 849005) B849005
theorem B377587 : Blo 374761 377587 := bstep (se 1 (by rfl) ⟨283190, by rfl⟩ : syracuseStep 377587 = 566381) B566381
theorem B377603 : Blo 374761 377603 := bstep (se 1 (by rfl) ⟨283202, by rfl⟩ : syracuseStep 377603 = 566405) B566405
theorem B566033 : Blo 374761 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B377619 : Blo 374761 377619 := bstep (se 1 (by rfl) ⟨283214, by rfl⟩ : syracuseStep 377619 = 566429) B566429
theorem B566051 : Blo 374761 566051 := bstep (se 1 (by rfl) ⟨424538, by rfl⟩ : syracuseStep 566051 = 849077) B849077
theorem B377635 : Blo 374761 377635 := bstep (se 1 (by rfl) ⟨283226, by rfl⟩ : syracuseStep 377635 = 566453) B566453
theorem B1450801 : Blo 374761 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B377651 : Blo 374761 377651 := bstep (se 1 (by rfl) ⟨283238, by rfl⟩ : syracuseStep 377651 = 566477) B566477
theorem B566081 : Blo 374761 566081 := bstep (se 2 (by rfl) ⟨212280, by rfl⟩ : syracuseStep 566081 = 424561) B424561
theorem B713539 : Blo 374761 713539 := bstep (se 1 (by rfl) ⟨535154, by rfl⟩ : syracuseStep 713539 = 1070309) B1070309
theorem B377667 : Blo 374761 377667 := bstep (se 1 (by rfl) ⟨283250, by rfl⟩ : syracuseStep 377667 = 566501) B566501
theorem B566099 : Blo 374761 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B377683 : Blo 374761 377683 := bstep (se 1 (by rfl) ⟨283262, by rfl⟩ : syracuseStep 377683 = 566525) B566525
theorem B377699 : Blo 374761 377699 := bstep (se 1 (by rfl) ⟨283274, by rfl⟩ : syracuseStep 377699 = 566549) B566549
theorem B713585 : Blo 374761 713585 := bstep (se 2 (by rfl) ⟨267594, by rfl⟩ : syracuseStep 713585 = 535189) B535189
theorem B566129 : Blo 374761 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B377715 : Blo 374761 377715 := bstep (se 1 (by rfl) ⟨283286, by rfl⟩ : syracuseStep 377715 = 566573) B566573
theorem B566147 : Blo 374761 566147 := bstep (se 1 (by rfl) ⟨424610, by rfl⟩ : syracuseStep 566147 = 849221) B849221
theorem B377731 : Blo 374761 377731 := bstep (se 1 (by rfl) ⟨283298, by rfl⟩ : syracuseStep 377731 = 566597) B566597
theorem B1270673 : Blo 374761 1270673 := bstep (se 2 (by rfl) ⟨476502, by rfl⟩ : syracuseStep 1270673 = 953005) B953005
theorem B377747 : Blo 374761 377747 := bstep (se 1 (by rfl) ⟨283310, by rfl⟩ : syracuseStep 377747 = 566621) B566621
theorem B951203 : Blo 374761 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B566177 : Blo 374761 566177 := bstep (se 2 (by rfl) ⟨212316, by rfl⟩ : syracuseStep 566177 = 424633) B424633
theorem B844721 : Blo 374761 844721 := bstep (se 2 (by rfl) ⟨316770, by rfl⟩ : syracuseStep 844721 = 633541) B633541
theorem B967601 : Blo 374761 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B566195 : Blo 374761 566195 := bstep (se 1 (by rfl) ⟨424646, by rfl⟩ : syracuseStep 566195 = 849293) B849293
theorem B844739 : Blo 374761 844739 := bstep (se 1 (by rfl) ⟨633554, by rfl⟩ : syracuseStep 844739 = 1267109) B1267109
theorem B2147269 : Blo 374761 2147269 := bstep (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) B402613
theorem B566225 : Blo 374761 566225 := bstep (se 2 (by rfl) ⟨212334, by rfl⟩ : syracuseStep 566225 = 424669) B424669
theorem B566243 : Blo 374761 566243 := bstep (se 1 (by rfl) ⟨424682, by rfl⟩ : syracuseStep 566243 = 849365) B849365
theorem B566273 : Blo 374761 566273 := bstep (se 2 (by rfl) ⟨212352, by rfl⟩ : syracuseStep 566273 = 424705) B424705
theorem B566291 : Blo 374761 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B1016867 : Blo 374761 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B566321 : Blo 374761 566321 := bstep (se 2 (by rfl) ⟨212370, by rfl⟩ : syracuseStep 566321 = 424741) B424741
theorem B566339 : Blo 374761 566339 := bstep (se 1 (by rfl) ⟨424754, by rfl⟩ : syracuseStep 566339 = 849509) B849509
theorem B451667 : Blo 374761 451667 := bstep (se 1 (by rfl) ⟨338750, by rfl⟩ : syracuseStep 451667 = 677501) B677501
theorem B566369 : Blo 374761 566369 := bstep (se 2 (by rfl) ⟨212388, by rfl⟩ : syracuseStep 566369 = 424777) B424777
theorem B1426531 : Blo 374761 1426531 := bstep (se 1 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 1426531 = 2139797) B2139797
theorem B1016945 : Blo 374761 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B476275 : Blo 374761 476275 := bstep (se 1 (by rfl) ⟨357206, by rfl⟩ : syracuseStep 476275 = 714413) B714413
theorem B566387 : Blo 374761 566387 := bstep (se 1 (by rfl) ⟨424790, by rfl⟩ : syracuseStep 566387 = 849581) B849581
theorem B713873 : Blo 374761 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B566417 : Blo 374761 566417 := bstep (se 2 (by rfl) ⟨212406, by rfl⟩ : syracuseStep 566417 = 424813) B424813
theorem B566435 : Blo 374761 566435 := bstep (se 1 (by rfl) ⟨424826, by rfl⟩ : syracuseStep 566435 = 849653) B849653
theorem B566465 : Blo 374761 566465 := bstep (se 2 (by rfl) ⟨212424, by rfl⟩ : syracuseStep 566465 = 424849) B424849
theorem B845009 : Blo 374761 845009 := bstep (se 2 (by rfl) ⟨316878, by rfl⟩ : syracuseStep 845009 = 633757) B633757
theorem B476371 : Blo 374761 476371 := bstep (se 1 (by rfl) ⟨357278, by rfl⟩ : syracuseStep 476371 = 714557) B714557
theorem B566483 : Blo 374761 566483 := bstep (se 1 (by rfl) ⟨424862, by rfl⟩ : syracuseStep 566483 = 849725) B849725
theorem B533731 : Blo 374761 533731 := bstep (se 1 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 533731 = 800597) B800597
theorem B845027 : Blo 374761 845027 := bstep (se 1 (by rfl) ⟨633770, by rfl⟩ : syracuseStep 845027 = 1267541) B1267541
theorem B1524977 : Blo 374761 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B763121 : Blo 374761 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B566513 : Blo 374761 566513 := bstep (se 2 (by rfl) ⟨212442, by rfl⟩ : syracuseStep 566513 = 424885) B424885
theorem B566531 : Blo 374761 566531 := bstep (se 1 (by rfl) ⟨424898, by rfl⟩ : syracuseStep 566531 = 849797) B849797
theorem B4064525 : Blo 374761 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B1934605 : Blo 374761 1934605 := bstep (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) B725477
theorem B566561 : Blo 374761 566561 := bstep (se 2 (by rfl) ⟨212460, by rfl⟩ : syracuseStep 566561 = 424921) B424921
theorem B566579 : Blo 374761 566579 := bstep (se 1 (by rfl) ⟨424934, by rfl⟩ : syracuseStep 566579 = 849869) B849869
theorem B2934085 : Blo 374761 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B566609 : Blo 374761 566609 := bstep (se 2 (by rfl) ⟨212478, by rfl⟩ : syracuseStep 566609 = 424957) B424957
theorem B566627 : Blo 374761 566627 := bstep (se 1 (by rfl) ⟨424970, by rfl⟩ : syracuseStep 566627 = 849941) B849941
theorem B1222033 : Blo 374761 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B1271213 : Blo 374761 1271213 := bstep (se 3 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 1271213 = 476705) B476705
theorem B1951181 : Blo 374761 1951181 := bstep (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) B731693
theorem B1074637 : Blo 374761 1074637 := bstep (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) B402989
theorem B1361357 : Blo 374761 1361357 := bstep (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) B510509
theorem B1271267 : Blo 374761 1271267 := bstep (se 1 (by rfl) ⟨953450, by rfl⟩ : syracuseStep 1271267 = 1906901) B1906901
theorem B845297 : Blo 374761 845297 := bstep (se 2 (by rfl) ⟨316986, by rfl⟩ : syracuseStep 845297 = 633973) B633973
theorem B845315 : Blo 374761 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B2606627 : Blo 374761 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1607309 : Blo 374761 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B1074865 : Blo 374761 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B632515 : Blo 374761 632515 := bstep (se 1 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 632515 = 948773) B948773
theorem B476867 : Blo 374761 476867 := bstep (se 1 (by rfl) ⟨357650, by rfl⟩ : syracuseStep 476867 = 715301) B715301
theorem B1353457 : Blo 374761 1353457 := bstep (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) B1015093
theorem B1271537 : Blo 374761 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B804611 : Blo 374761 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B534289 : Blo 374761 534289 := bstep (se 2 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 534289 = 400717) B400717
theorem B845585 : Blo 374761 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B845603 : Blo 374761 845603 := bstep (se 1 (by rfl) ⟨634202, by rfl⟩ : syracuseStep 845603 = 1268405) B1268405
theorem B2320163 : Blo 374761 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B919331 : Blo 374761 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B534323 : Blo 374761 534323 := bstep (se 1 (by rfl) ⟨400742, by rfl⟩ : syracuseStep 534323 = 801485) B801485
theorem B2443085 : Blo 374761 2443085 := bstep (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) B916157
theorem B632657 : Blo 374761 632657 := bstep (se 2 (by rfl) ⟨237246, by rfl⟩ : syracuseStep 632657 = 474493) B474493
theorem B952145 : Blo 374761 952145 := bstep (se 2 (by rfl) ⟨357054, by rfl⟩ : syracuseStep 952145 = 714109) B714109
theorem B1075025 : Blo 374761 1075025 := bstep (se 2 (by rfl) ⟨403134, by rfl⟩ : syracuseStep 1075025 = 806269) B806269
theorem B714595 : Blo 374761 714595 := bstep (se 1 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 714595 = 1071893) B1071893
theorem B1910627 : Blo 374761 1910627 := bstep (se 1 (by rfl) ⟨1432970, by rfl⟩ : syracuseStep 1910627 = 2865941) B2865941
theorem B952195 : Blo 374761 952195 := bstep (se 1 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 952195 = 1428293) B1428293
theorem B1017731 : Blo 374761 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B1075139 : Blo 374761 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B632785 : Blo 374761 632785 := bstep (se 2 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 632785 = 474589) B474589
theorem B1607651 : Blo 374761 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B632819 : Blo 374761 632819 := bstep (se 1 (by rfl) ⟨474614, by rfl⟩ : syracuseStep 632819 = 949229) B949229
theorem B952337 : Blo 374761 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B845873 : Blo 374761 845873 := bstep (se 2 (by rfl) ⟨317202, by rfl⟩ : syracuseStep 845873 = 634405) B634405
theorem B845891 : Blo 374761 845891 := bstep (se 1 (by rfl) ⟨634418, by rfl⟩ : syracuseStep 845891 = 1268837) B1268837
theorem B1206353 : Blo 374761 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B26683505 : Blo 374761 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B632947 : Blo 374761 632947 := bstep (se 1 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 632947 = 949421) B949421
theorem B428147 : Blo 374761 428147 := bstep (se 1 (by rfl) ⟨321110, by rfl⟩ : syracuseStep 428147 = 642221) B642221
theorem B501955 : Blo 374761 501955 := bstep (se 1 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 501955 = 752933) B752933
theorem B1222865 : Blo 374761 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B10414307 : Blo 374761 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B2033905 : Blo 374761 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B633089 : Blo 374761 633089 := bstep (se 2 (by rfl) ⟨237408, by rfl⟩ : syracuseStep 633089 = 474817) B474817
theorem B1272077 : Blo 374761 1272077 := bstep (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) B477029
theorem B715043 : Blo 374761 715043 := bstep (se 1 (by rfl) ⟨536282, by rfl⟩ : syracuseStep 715043 = 1072565) B1072565
theorem B1272131 : Blo 374761 1272131 := bstep (se 1 (by rfl) ⟨954098, by rfl⟩ : syracuseStep 1272131 = 1908197) B1908197
theorem B846161 : Blo 374761 846161 := bstep (se 2 (by rfl) ⟨317310, by rfl⟩ : syracuseStep 846161 = 634621) B634621
theorem B534881 : Blo 374761 534881 := bstep (se 2 (by rfl) ⟨200580, by rfl⟩ : syracuseStep 534881 = 401161) B401161
theorem B846179 : Blo 374761 846179 := bstep (se 1 (by rfl) ⟨634634, by rfl⟩ : syracuseStep 846179 = 1269269) B1269269
theorem B5802353 : Blo 374761 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B633217 : Blo 374761 633217 := bstep (se 2 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 633217 = 474913) B474913
theorem B477571 : Blo 374761 477571 := bstep (se 1 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 477571 = 716357) B716357
theorem B1804685 : Blo 374761 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B633251 : Blo 374761 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B1206701 : Blo 374761 1206701 := bstep (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) B452513
theorem B534961 : Blo 374761 534961 := bstep (se 2 (by rfl) ⟨200610, by rfl⟩ : syracuseStep 534961 = 401221) B401221
theorem B1608113 : Blo 374761 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B477667 : Blo 374761 477667 := bstep (se 1 (by rfl) ⟨358250, by rfl⟩ : syracuseStep 477667 = 716501) B716501
theorem B1444337 : Blo 374761 1444337 := bstep (se 2 (by rfl) ⟨541626, by rfl⟩ : syracuseStep 1444337 = 1083253) B1083253
theorem B3434993 : Blo 374761 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B633379 : Blo 374761 633379 := bstep (se 1 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 633379 = 950069) B950069
theorem B1223203 : Blo 374761 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B5130805 : Blo 374761 5130805 := bstep (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) B481013
theorem B715331 : Blo 374761 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B1272401 : Blo 374761 1272401 := bstep (se 2 (by rfl) ⟨477150, by rfl⟩ : syracuseStep 1272401 = 954301) B954301
theorem B4295267 : Blo 374761 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B846449 : Blo 374761 846449 := bstep (se 2 (by rfl) ⟨317418, by rfl⟩ : syracuseStep 846449 = 634837) B634837
theorem B600691 : Blo 374761 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B846467 : Blo 374761 846467 := bstep (se 1 (by rfl) ⟨634850, by rfl⟩ : syracuseStep 846467 = 1269701) B1269701
theorem B5139085 : Blo 374761 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B1911437 : Blo 374761 1911437 := bstep (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) B716789
theorem B633521 : Blo 374761 633521 := bstep (se 2 (by rfl) ⟨237570, by rfl⟩ : syracuseStep 633521 = 475141) B475141
theorem B6163141 : Blo 374761 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B600787 : Blo 374761 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B8784611 : Blo 374761 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B633649 : Blo 374761 633649 := bstep (se 2 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 633649 = 475237) B475237
theorem B1018673 : Blo 374761 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B3222341 : Blo 374761 3222341 := bstep (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) B604189
theorem B633683 : Blo 374761 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B600947 : Blo 374761 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B2149253 : Blo 374761 2149253 := bstep (se 4 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 2149253 = 402985) B402985
theorem B1067917 : Blo 374761 1067917 := bstep (se 3 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 1067917 = 400469) B400469
theorem B846737 : Blo 374761 846737 := bstep (se 2 (by rfl) ⟨317526, by rfl⟩ : syracuseStep 846737 = 635053) B635053
theorem B846755 : Blo 374761 846755 := bstep (se 1 (by rfl) ⟨635066, by rfl⟩ : syracuseStep 846755 = 1270133) B1270133
theorem B633811 : Blo 374761 633811 := bstep (se 1 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 633811 = 950717) B950717
theorem B805859 : Blo 374761 805859 := bstep (se 1 (by rfl) ⟨604394, by rfl⟩ : syracuseStep 805859 = 1208789) B1208789
theorem B953329 : Blo 374761 953329 := bstep (se 2 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 953329 = 714997) B714997
theorem B2403377 : Blo 374761 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B633953 : Blo 374761 633953 := bstep (se 2 (by rfl) ⟨237732, by rfl⟩ : syracuseStep 633953 = 475465) B475465
theorem B1272941 : Blo 374761 1272941 := bstep (se 3 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 1272941 = 477353) B477353
theorem B1272995 : Blo 374761 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B847025 : Blo 374761 847025 := bstep (se 2 (by rfl) ⟨317634, by rfl⟩ : syracuseStep 847025 = 635269) B635269
theorem B535747 : Blo 374761 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B847043 : Blo 374761 847043 := bstep (se 1 (by rfl) ⟨635282, by rfl⟩ : syracuseStep 847043 = 1270565) B1270565
theorem B634081 : Blo 374761 634081 := bstep (se 2 (by rfl) ⟨237780, by rfl⟩ : syracuseStep 634081 = 475561) B475561
theorem B634115 : Blo 374761 634115 := bstep (se 1 (by rfl) ⟨475586, by rfl⟩ : syracuseStep 634115 = 951173) B951173
theorem B953603 : Blo 374761 953603 := bstep (se 1 (by rfl) ⟨715202, by rfl⟩ : syracuseStep 953603 = 1430405) B1430405
theorem B1649933 : Blo 374761 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B1428749 : Blo 374761 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B1019245 : Blo 374761 1019245 := bstep (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) B382217
theorem B1903985 : Blo 374761 1903985 := bstep (se 2 (by rfl) ⟨713994, by rfl⟩ : syracuseStep 1903985 = 1427989) B1427989
theorem B634243 : Blo 374761 634243 := bstep (se 1 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 634243 = 951365) B951365
theorem B2280845 : Blo 374761 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B1273265 : Blo 374761 1273265 := bstep (se 2 (by rfl) ⟨477474, by rfl⟩ : syracuseStep 1273265 = 954949) B954949
theorem B953795 : Blo 374761 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B1142225 : Blo 374761 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B847313 : Blo 374761 847313 := bstep (se 2 (by rfl) ⟨317742, by rfl⟩ : syracuseStep 847313 = 635485) B635485
theorem B847331 : Blo 374761 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B716273 : Blo 374761 716273 := bstep (se 2 (by rfl) ⟨268602, by rfl⟩ : syracuseStep 716273 = 537205) B537205
theorem B1265165 : Blo 374761 1265165 := bstep (se 3 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 1265165 = 474437) B474437
theorem B634385 : Blo 374761 634385 := bstep (se 2 (by rfl) ⟨237894, by rfl⟩ : syracuseStep 634385 = 475789) B475789
theorem B806449 : Blo 374761 806449 := bstep (se 2 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 806449 = 604837) B604837
theorem B1265219 : Blo 374761 1265219 := bstep (se 1 (by rfl) ⟨948914, by rfl⟩ : syracuseStep 1265219 = 1897829) B1897829
theorem B544339 : Blo 374761 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B634513 : Blo 374761 634513 := bstep (se 2 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 634513 = 475885) B475885
theorem B536225 : Blo 374761 536225 := bstep (se 2 (by rfl) ⟨201084, by rfl⟩ : syracuseStep 536225 = 402169) B402169
theorem B634547 : Blo 374761 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B4419269 : Blo 374761 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B847601 : Blo 374761 847601 := bstep (se 2 (by rfl) ⟨317850, by rfl⟩ : syracuseStep 847601 = 635701) B635701
theorem B847619 : Blo 374761 847619 := bstep (se 1 (by rfl) ⟨635714, by rfl⟩ : syracuseStep 847619 = 1271429) B1271429
theorem B1470221 : Blo 374761 1470221 := bstep (se 3 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 1470221 = 551333) B551333
theorem B536339 : Blo 374761 536339 := bstep (se 1 (by rfl) ⟨402254, by rfl⟩ : syracuseStep 536339 = 804509) B804509
theorem B1527587 : Blo 374761 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B1601329 : Blo 374761 1601329 := bstep (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) B1200997
theorem B634675 : Blo 374761 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B601921 : Blo 374761 601921 := bstep (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) B451441
theorem B421699 : Blo 374761 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B1265489 : Blo 374761 1265489 := bstep (se 2 (by rfl) ⟨474558, by rfl⟩ : syracuseStep 1265489 = 949117) B949117
theorem B536419 : Blo 374761 536419 := bstep (se 1 (by rfl) ⟨402314, by rfl⟩ : syracuseStep 536419 = 804629) B804629
theorem B1814413 : Blo 374761 1814413 := bstep (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) B680405
theorem B1085329 : Blo 374761 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1068977 : Blo 374761 1068977 := bstep (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) B801733
theorem B634817 : Blo 374761 634817 := bstep (se 2 (by rfl) ⟨238056, by rfl⟩ : syracuseStep 634817 = 476113) B476113
theorem B1273805 : Blo 374761 1273805 := bstep (se 3 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 1273805 = 477677) B477677
theorem B1937357 : Blo 374761 1937357 := bstep (se 3 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 1937357 = 726509) B726509
theorem B421843 : Blo 374761 421843 := bstep (se 1 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 421843 = 632765) B632765
theorem B1273859 : Blo 374761 1273859 := bstep (se 1 (by rfl) ⟨955394, by rfl⟩ : syracuseStep 1273859 = 1910789) B1910789
theorem B847889 : Blo 374761 847889 := bstep (se 2 (by rfl) ⟨317958, by rfl⟩ : syracuseStep 847889 = 635917) B635917
theorem B847907 : Blo 374761 847907 := bstep (se 1 (by rfl) ⟨635930, by rfl⟩ : syracuseStep 847907 = 1271861) B1271861
theorem B634945 : Blo 374761 634945 := bstep (se 2 (by rfl) ⟨238104, by rfl⟩ : syracuseStep 634945 = 476209) B476209
theorem B421987 : Blo 374761 421987 := bstep (se 1 (by rfl) ⟨316490, by rfl⟩ : syracuseStep 421987 = 632981) B632981
theorem B634979 : Blo 374761 634979 := bstep (se 1 (by rfl) ⟨476234, by rfl⟩ : syracuseStep 634979 = 952469) B952469
theorem B528563 : Blo 374761 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B905411 : Blo 374761 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B1634509 : Blo 374761 1634509 := bstep (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) B612941
theorem B635107 : Blo 374761 635107 := bstep (se 1 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 635107 = 952661) B952661
theorem B12226787 : Blo 374761 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B1208557 : Blo 374761 1208557 := bstep (se 3 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 1208557 = 453209) B453209
theorem B422131 : Blo 374761 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B1085699 : Blo 374761 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B1274129 : Blo 374761 1274129 := bstep (se 2 (by rfl) ⟨477798, by rfl⟩ : syracuseStep 1274129 = 955597) B955597
theorem B848177 : Blo 374761 848177 := bstep (se 2 (by rfl) ⟨318066, by rfl⟩ : syracuseStep 848177 = 636133) B636133
theorem B848195 : Blo 374761 848195 := bstep (se 1 (by rfl) ⟨636146, by rfl⟩ : syracuseStep 848195 = 1272293) B1272293
theorem B1266029 : Blo 374761 1266029 := bstep (se 3 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 1266029 = 474761) B474761
theorem B635249 : Blo 374761 635249 := bstep (se 2 (by rfl) ⟨238218, by rfl⟩ : syracuseStep 635249 = 476437) B476437
theorem B954737 : Blo 374761 954737 := bstep (se 2 (by rfl) ⟨358026, by rfl⟩ : syracuseStep 954737 = 716053) B716053
theorem B422275 : Blo 374761 422275 := bstep (se 1 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 422275 = 633413) B633413
theorem B2568581 : Blo 374761 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B536977 : Blo 374761 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B430483 : Blo 374761 430483 := bstep (se 1 (by rfl) ⟨322862, by rfl⟩ : syracuseStep 430483 = 645725) B645725
theorem B1266083 : Blo 374761 1266083 := bstep (se 1 (by rfl) ⟨949562, by rfl⟩ : syracuseStep 1266083 = 1899125) B1899125
theorem B954787 : Blo 374761 954787 := bstep (se 1 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 954787 = 1432181) B1432181
theorem B635377 : Blo 374761 635377 := bstep (se 2 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 635377 = 476533) B476533
theorem B1200653 : Blo 374761 1200653 := bstep (se 3 (by rfl) ⟨225122, by rfl⟩ : syracuseStep 1200653 = 450245) B450245
theorem B422419 : Blo 374761 422419 := bstep (se 1 (by rfl) ⟨316814, by rfl⟩ : syracuseStep 422419 = 633629) B633629
theorem B635411 : Blo 374761 635411 := bstep (se 1 (by rfl) ⟨476558, by rfl⟩ : syracuseStep 635411 = 953117) B953117
theorem B569891 : Blo 374761 569891 := bstep (se 1 (by rfl) ⟨427418, by rfl⟩ : syracuseStep 569891 = 854837) B854837
theorem B954929 : Blo 374761 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B905795 : Blo 374761 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B1069649 : Blo 374761 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B848465 : Blo 374761 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B848483 : Blo 374761 848483 := bstep (se 1 (by rfl) ⟨636362, by rfl⟩ : syracuseStep 848483 = 1272725) B1272725
theorem B578179 : Blo 374761 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B3846797 : Blo 374761 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B635539 : Blo 374761 635539 := bstep (se 1 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 635539 = 953309) B953309
theorem B422563 : Blo 374761 422563 := bstep (se 1 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 422563 = 633845) B633845
theorem B1266353 : Blo 374761 1266353 := bstep (se 2 (by rfl) ⟨474882, by rfl⟩ : syracuseStep 1266353 = 949765) B949765
theorem B6861509 : Blo 374761 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B10277603 : Blo 374761 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B2847473 : Blo 374761 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1938161 : Blo 374761 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B2167565 : Blo 374761 2167565 := bstep (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) B812837
theorem B635681 : Blo 374761 635681 := bstep (se 2 (by rfl) ⟨238380, by rfl⟩ : syracuseStep 635681 = 476761) B476761
theorem B1905443 : Blo 374761 1905443 := bstep (se 1 (by rfl) ⟨1429082, by rfl⟩ : syracuseStep 1905443 = 2858165) B2858165
theorem B1274669 : Blo 374761 1274669 := bstep (se 3 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 1274669 = 478001) B478001
theorem B422707 : Blo 374761 422707 := bstep (se 1 (by rfl) ⟨317030, by rfl⟩ : syracuseStep 422707 = 634061) B634061
theorem B619331 : Blo 374761 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B1274723 : Blo 374761 1274723 := bstep (se 1 (by rfl) ⟨956042, by rfl⟩ : syracuseStep 1274723 = 1912085) B1912085
theorem B848753 : Blo 374761 848753 := bstep (se 2 (by rfl) ⟨318282, by rfl⟩ : syracuseStep 848753 = 636565) B636565
theorem B848771 : Blo 374761 848771 := bstep (se 1 (by rfl) ⟨636578, by rfl⟩ : syracuseStep 848771 = 1273157) B1273157
theorem B635809 : Blo 374761 635809 := bstep (se 2 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 635809 = 476857) B476857
theorem B1201073 : Blo 374761 1201073 := bstep (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) B900805
theorem B422851 : Blo 374761 422851 := bstep (se 1 (by rfl) ⟨317138, by rfl⟩ : syracuseStep 422851 = 634277) B634277
theorem B635843 : Blo 374761 635843 := bstep (se 1 (by rfl) ⟨476882, by rfl⟩ : syracuseStep 635843 = 953765) B953765
theorem B562145 : Blo 374761 562145 := bstep (se 2 (by rfl) ⟨210804, by rfl⟩ : syracuseStep 562145 = 421609) B421609
theorem B562163 : Blo 374761 562163 := bstep (se 1 (by rfl) ⟨421622, by rfl⟩ : syracuseStep 562163 = 843245) B843245
theorem B2790413 : Blo 374761 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B562193 : Blo 374761 562193 := bstep (se 2 (by rfl) ⟨210822, by rfl⟩ : syracuseStep 562193 = 421645) B421645
theorem B857105 : Blo 374761 857105 := bstep (se 2 (by rfl) ⟨321414, by rfl⟩ : syracuseStep 857105 = 642829) B642829
theorem B562211 : Blo 374761 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B562241 : Blo 374761 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B635971 : Blo 374761 635971 := bstep (se 1 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 635971 = 953957) B953957
theorem B676945 : Blo 374761 676945 := bstep (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) B507709
theorem B562259 : Blo 374761 562259 := bstep (se 1 (by rfl) ⟨421694, by rfl⟩ : syracuseStep 562259 = 843389) B843389
theorem B422995 : Blo 374761 422995 := bstep (se 1 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 422995 = 634493) B634493
theorem B537683 : Blo 374761 537683 := bstep (se 1 (by rfl) ⟨403262, by rfl⟩ : syracuseStep 537683 = 806525) B806525
theorem B562289 : Blo 374761 562289 := bstep (se 2 (by rfl) ⟨210858, by rfl⟩ : syracuseStep 562289 = 421717) B421717
theorem B562307 : Blo 374761 562307 := bstep (se 1 (by rfl) ⟨421730, by rfl⟩ : syracuseStep 562307 = 843461) B843461
theorem B849041 : Blo 374761 849041 := bstep (se 2 (by rfl) ⟨318390, by rfl⟩ : syracuseStep 849041 = 636781) B636781
theorem B562337 : Blo 374761 562337 := bstep (se 2 (by rfl) ⟨210876, by rfl⟩ : syracuseStep 562337 = 421753) B421753
theorem B849059 : Blo 374761 849059 := bstep (se 1 (by rfl) ⟨636794, by rfl⟩ : syracuseStep 849059 = 1273589) B1273589
theorem B2266289 : Blo 374761 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B562355 : Blo 374761 562355 := bstep (se 1 (by rfl) ⟨421766, by rfl⟩ : syracuseStep 562355 = 843533) B843533
theorem B1266893 : Blo 374761 1266893 := bstep (se 3 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 1266893 = 475085) B475085
theorem B562385 : Blo 374761 562385 := bstep (se 2 (by rfl) ⟨210894, by rfl⟩ : syracuseStep 562385 = 421789) B421789
theorem B570577 : Blo 374761 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B636113 : Blo 374761 636113 := bstep (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) B477085
theorem B562403 : Blo 374761 562403 := bstep (se 1 (by rfl) ⟨421802, by rfl⟩ : syracuseStep 562403 = 843605) B843605
theorem B423139 : Blo 374761 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B9188579 : Blo 374761 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B562433 : Blo 374761 562433 := bstep (se 2 (by rfl) ⟨210912, by rfl⟩ : syracuseStep 562433 = 421825) B421825
theorem B1266947 : Blo 374761 1266947 := bstep (se 1 (by rfl) ⟨950210, by rfl⟩ : syracuseStep 1266947 = 1900421) B1900421
theorem B562451 : Blo 374761 562451 := bstep (se 1 (by rfl) ⟨421838, by rfl⟩ : syracuseStep 562451 = 843677) B843677
theorem B562481 : Blo 374761 562481 := bstep (se 2 (by rfl) ⟨210930, by rfl⟩ : syracuseStep 562481 = 421861) B421861
theorem B562499 : Blo 374761 562499 := bstep (se 1 (by rfl) ⟨421874, by rfl⟩ : syracuseStep 562499 = 843749) B843749
theorem B636241 : Blo 374761 636241 := bstep (se 2 (by rfl) ⟨238590, by rfl⟩ : syracuseStep 636241 = 477181) B477181
theorem B562529 : Blo 374761 562529 := bstep (se 2 (by rfl) ⟨210948, by rfl⟩ : syracuseStep 562529 = 421897) B421897
theorem B1070435 : Blo 374761 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B2864483 : Blo 374761 2864483 := bstep (se 1 (by rfl) ⟨2148362, by rfl⟩ : syracuseStep 2864483 = 4296725) B4296725
theorem B562547 : Blo 374761 562547 := bstep (se 1 (by rfl) ⟨421910, by rfl⟩ : syracuseStep 562547 = 843821) B843821
theorem B423283 : Blo 374761 423283 := bstep (se 1 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 423283 = 634925) B634925
theorem B636275 : Blo 374761 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B562577 : Blo 374761 562577 := bstep (se 2 (by rfl) ⟨210966, by rfl⟩ : syracuseStep 562577 = 421933) B421933
theorem B562595 : Blo 374761 562595 := bstep (se 1 (by rfl) ⟨421946, by rfl⟩ : syracuseStep 562595 = 843893) B843893
theorem B849329 : Blo 374761 849329 := bstep (se 2 (by rfl) ⟨318498, by rfl⟩ : syracuseStep 849329 = 636997) B636997
theorem B562625 : Blo 374761 562625 := bstep (se 2 (by rfl) ⟨210984, by rfl⟩ : syracuseStep 562625 = 421969) B421969
theorem B603587 : Blo 374761 603587 := bstep (se 1 (by rfl) ⟨452690, by rfl⟩ : syracuseStep 603587 = 905381) B905381
theorem B849347 : Blo 374761 849347 := bstep (se 1 (by rfl) ⟨637010, by rfl⟩ : syracuseStep 849347 = 1274021) B1274021
theorem B2405837 : Blo 374761 2405837 := bstep (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) B902189
theorem B562643 : Blo 374761 562643 := bstep (se 1 (by rfl) ⟨421982, by rfl⟩ : syracuseStep 562643 = 843965) B843965
theorem B562673 : Blo 374761 562673 := bstep (se 2 (by rfl) ⟨211002, by rfl⟩ : syracuseStep 562673 = 422005) B422005
theorem B636403 : Blo 374761 636403 := bstep (se 1 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 636403 = 954605) B954605
theorem B562691 : Blo 374761 562691 := bstep (se 1 (by rfl) ⟨422018, by rfl⟩ : syracuseStep 562691 = 844037) B844037
theorem B423427 : Blo 374761 423427 := bstep (se 1 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 423427 = 635141) B635141
theorem B1267217 : Blo 374761 1267217 := bstep (se 2 (by rfl) ⟨475206, by rfl⟩ : syracuseStep 1267217 = 950413) B950413
theorem B955921 : Blo 374761 955921 := bstep (se 2 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 955921 = 716941) B716941
theorem B562721 : Blo 374761 562721 := bstep (se 2 (by rfl) ⟨211020, by rfl⟩ : syracuseStep 562721 = 422041) B422041
theorem B1930787 : Blo 374761 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B1226285 : Blo 374761 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B562739 : Blo 374761 562739 := bstep (se 1 (by rfl) ⟨422054, by rfl⟩ : syracuseStep 562739 = 844109) B844109
theorem B603715 : Blo 374761 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B1906253 : Blo 374761 1906253 := bstep (se 3 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 1906253 = 714845) B714845
theorem B562769 : Blo 374761 562769 := bstep (se 2 (by rfl) ⟨211038, by rfl⟩ : syracuseStep 562769 = 422077) B422077
theorem B1422947 : Blo 374761 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B562787 : Blo 374761 562787 := bstep (se 1 (by rfl) ⟨422090, by rfl⟩ : syracuseStep 562787 = 844181) B844181
theorem B562817 : Blo 374761 562817 := bstep (se 2 (by rfl) ⟨211056, by rfl⟩ : syracuseStep 562817 = 422113) B422113
theorem B1144451 : Blo 374761 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B603779 : Blo 374761 603779 := bstep (se 1 (by rfl) ⟨452834, by rfl⟩ : syracuseStep 603779 = 905669) B905669
theorem B636545 : Blo 374761 636545 := bstep (se 2 (by rfl) ⟨238704, by rfl⟩ : syracuseStep 636545 = 477409) B477409
theorem B562835 : Blo 374761 562835 := bstep (se 1 (by rfl) ⟨422126, by rfl⟩ : syracuseStep 562835 = 844253) B844253
theorem B423571 : Blo 374761 423571 := bstep (se 1 (by rfl) ⟨317678, by rfl⟩ : syracuseStep 423571 = 635357) B635357
theorem B1070765 : Blo 374761 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B562865 : Blo 374761 562865 := bstep (se 2 (by rfl) ⟨211074, by rfl⟩ : syracuseStep 562865 = 422149) B422149
theorem B571057 : Blo 374761 571057 := bstep (se 2 (by rfl) ⟨214146, by rfl⟩ : syracuseStep 571057 = 428293) B428293
theorem B562883 : Blo 374761 562883 := bstep (se 1 (by rfl) ⟨422162, by rfl⟩ : syracuseStep 562883 = 844325) B844325
theorem B1603277 : Blo 374761 1603277 := bstep (se 3 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 1603277 = 601229) B601229
theorem B1119949 : Blo 374761 1119949 := bstep (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) B419981
theorem B849617 : Blo 374761 849617 := bstep (se 2 (by rfl) ⟨318606, by rfl⟩ : syracuseStep 849617 = 637213) B637213
theorem B562913 : Blo 374761 562913 := bstep (se 2 (by rfl) ⟨211092, by rfl⟩ : syracuseStep 562913 = 422185) B422185
theorem B4830947 : Blo 374761 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B849635 : Blo 374761 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B1070833 : Blo 374761 1070833 := bstep (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) B803125
theorem B562931 : Blo 374761 562931 := bstep (se 1 (by rfl) ⟨422198, by rfl⟩ : syracuseStep 562931 = 844397) B844397
theorem B636673 : Blo 374761 636673 := bstep (se 2 (by rfl) ⟨238752, by rfl⟩ : syracuseStep 636673 = 477505) B477505
theorem B562961 : Blo 374761 562961 := bstep (se 2 (by rfl) ⟨211110, by rfl⟩ : syracuseStep 562961 = 422221) B422221
theorem B562979 : Blo 374761 562979 := bstep (se 1 (by rfl) ⟨422234, by rfl⟩ : syracuseStep 562979 = 844469) B844469
theorem B423715 : Blo 374761 423715 := bstep (se 1 (by rfl) ⟨317786, by rfl⟩ : syracuseStep 423715 = 635573) B635573
theorem B636707 : Blo 374761 636707 := bstep (se 1 (by rfl) ⟨477530, by rfl⟩ : syracuseStep 636707 = 955061) B955061
theorem B956195 : Blo 374761 956195 := bstep (se 1 (by rfl) ⟨717146, by rfl⟩ : syracuseStep 956195 = 1434293) B1434293
theorem B563009 : Blo 374761 563009 := bstep (se 2 (by rfl) ⟨211128, by rfl⟩ : syracuseStep 563009 = 422257) B422257
theorem B800579 : Blo 374761 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B563027 : Blo 374761 563027 := bstep (se 1 (by rfl) ⟨422270, by rfl⟩ : syracuseStep 563027 = 844541) B844541
theorem B677731 : Blo 374761 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B1357667 : Blo 374761 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B563057 : Blo 374761 563057 := bstep (se 2 (by rfl) ⟨211146, by rfl⟩ : syracuseStep 563057 = 422293) B422293
theorem B6510449 : Blo 374761 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B563075 : Blo 374761 563075 := bstep (se 1 (by rfl) ⟨422306, by rfl⟩ : syracuseStep 563075 = 844613) B844613
theorem B563105 : Blo 374761 563105 := bstep (se 2 (by rfl) ⟨211164, by rfl⟩ : syracuseStep 563105 = 422329) B422329
theorem B1611683 : Blo 374761 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B636835 : Blo 374761 636835 := bstep (se 1 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 636835 = 955253) B955253
theorem B563123 : Blo 374761 563123 := bstep (se 1 (by rfl) ⟨422342, by rfl⟩ : syracuseStep 563123 = 844685) B844685
theorem B423859 : Blo 374761 423859 := bstep (se 1 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 423859 = 635789) B635789
theorem B382915 : Blo 374761 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B563153 : Blo 374761 563153 := bstep (se 2 (by rfl) ⟨211182, by rfl⟩ : syracuseStep 563153 = 422365) B422365
theorem B563171 : Blo 374761 563171 := bstep (se 1 (by rfl) ⟨422378, by rfl⟩ : syracuseStep 563171 = 844757) B844757
theorem B686051 : Blo 374761 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B374771 : Blo 374761 374771 := bstep (se 1 (by rfl) ⟨281078, by rfl⟩ : syracuseStep 374771 = 562157) B562157
theorem B849905 : Blo 374761 849905 := bstep (se 2 (by rfl) ⟨318714, by rfl⟩ : syracuseStep 849905 = 637429) B637429
theorem B563201 : Blo 374761 563201 := bstep (se 2 (by rfl) ⟨211200, by rfl⟩ : syracuseStep 563201 = 422401) B422401
theorem B374787 : Blo 374761 374787 := bstep (se 1 (by rfl) ⟨281090, by rfl⟩ : syracuseStep 374787 = 562181) B562181
theorem B1071107 : Blo 374761 1071107 := bstep (se 1 (by rfl) ⟨803330, by rfl⟩ : syracuseStep 1071107 = 1606661) B1606661
theorem B849923 : Blo 374761 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B374803 : Blo 374761 374803 := bstep (se 1 (by rfl) ⟨281102, by rfl⟩ : syracuseStep 374803 = 562205) B562205
theorem B563219 : Blo 374761 563219 := bstep (se 1 (by rfl) ⟨422414, by rfl⟩ : syracuseStep 563219 = 844829) B844829
theorem B374819 : Blo 374761 374819 := bstep (se 1 (by rfl) ⟨281114, by rfl⟩ : syracuseStep 374819 = 562229) B562229
theorem B1267757 : Blo 374761 1267757 := bstep (se 3 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 1267757 = 475409) B475409
theorem B563249 : Blo 374761 563249 := bstep (se 2 (by rfl) ⟨211218, by rfl⟩ : syracuseStep 563249 = 422437) B422437
theorem B374835 : Blo 374761 374835 := bstep (se 1 (by rfl) ⟨281126, by rfl⟩ : syracuseStep 374835 = 562253) B562253
theorem B636977 : Blo 374761 636977 := bstep (se 2 (by rfl) ⟨238866, by rfl⟩ : syracuseStep 636977 = 477733) B477733
theorem B374851 : Blo 374761 374851 := bstep (se 1 (by rfl) ⟨281138, by rfl⟩ : syracuseStep 374851 = 562277) B562277
theorem B563267 : Blo 374761 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B424003 : Blo 374761 424003 := bstep (se 1 (by rfl) ⟨318002, by rfl⟩ : syracuseStep 424003 = 636005) B636005
theorem B374867 : Blo 374761 374867 := bstep (se 1 (by rfl) ⟨281150, by rfl⟩ : syracuseStep 374867 = 562301) B562301
theorem B563297 : Blo 374761 563297 := bstep (se 2 (by rfl) ⟨211236, by rfl⟩ : syracuseStep 563297 = 422473) B422473
theorem B374883 : Blo 374761 374883 := bstep (se 1 (by rfl) ⟨281162, by rfl⟩ : syracuseStep 374883 = 562325) B562325
theorem B1267811 : Blo 374761 1267811 := bstep (se 1 (by rfl) ⟨950858, by rfl⟩ : syracuseStep 1267811 = 1901717) B1901717
theorem B424579 : Blo 374761 424579 := bstep (se 1 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 424579 = 636869) B636869
theorem B1431665 : Blo 374761 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B604273 : Blo 374761 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B374899 : Blo 374761 374899 := bstep (se 1 (by rfl) ⟨281174, by rfl⟩ : syracuseStep 374899 = 562349) B562349
theorem B563315 : Blo 374761 563315 := bstep (se 1 (by rfl) ⟨422486, by rfl⟩ : syracuseStep 563315 = 844973) B844973
theorem B1529969 : Blo 374761 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B374915 : Blo 374761 374915 := bstep (se 1 (by rfl) ⟨281186, by rfl⟩ : syracuseStep 374915 = 562373) B562373
theorem B563345 : Blo 374761 563345 := bstep (se 2 (by rfl) ⟨211254, by rfl⟩ : syracuseStep 563345 = 422509) B422509
theorem B374931 : Blo 374761 374931 := bstep (se 1 (by rfl) ⟨281198, by rfl⟩ : syracuseStep 374931 = 562397) B562397
theorem B374947 : Blo 374761 374947 := bstep (se 1 (by rfl) ⟨281210, by rfl⟩ : syracuseStep 374947 = 562421) B562421
theorem B563363 : Blo 374761 563363 := bstep (se 1 (by rfl) ⟨422522, by rfl⟩ : syracuseStep 563363 = 845045) B845045
theorem B374963 : Blo 374761 374963 := bstep (se 1 (by rfl) ⟨281222, by rfl⟩ : syracuseStep 374963 = 562445) B562445
theorem B637105 : Blo 374761 637105 := bstep (se 2 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 637105 = 477829) B477829
theorem B563393 : Blo 374761 563393 := bstep (se 2 (by rfl) ⟨211272, by rfl⟩ : syracuseStep 563393 = 422545) B422545
theorem B374979 : Blo 374761 374979 := bstep (se 1 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 374979 = 562469) B562469
theorem B374995 : Blo 374761 374995 := bstep (se 1 (by rfl) ⟨281246, by rfl⟩ : syracuseStep 374995 = 562493) B562493
theorem B563411 : Blo 374761 563411 := bstep (se 1 (by rfl) ⟨422558, by rfl⟩ : syracuseStep 563411 = 845117) B845117
theorem B424147 : Blo 374761 424147 := bstep (se 1 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 424147 = 636221) B636221
theorem B637139 : Blo 374761 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B375011 : Blo 374761 375011 := bstep (se 1 (by rfl) ⟨281258, by rfl⟩ : syracuseStep 375011 = 562517) B562517
theorem B1423601 : Blo 374761 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B563441 : Blo 374761 563441 := bstep (se 2 (by rfl) ⟨211290, by rfl⟩ : syracuseStep 563441 = 422581) B422581
theorem B375027 : Blo 374761 375027 := bstep (se 1 (by rfl) ⟨281270, by rfl⟩ : syracuseStep 375027 = 562541) B562541
theorem B375043 : Blo 374761 375043 := bstep (se 1 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 375043 = 562565) B562565
theorem B563459 : Blo 374761 563459 := bstep (se 1 (by rfl) ⟨422594, by rfl⟩ : syracuseStep 563459 = 845189) B845189
theorem B375059 : Blo 374761 375059 := bstep (se 1 (by rfl) ⟨281294, by rfl⟩ : syracuseStep 375059 = 562589) B562589
theorem B563489 : Blo 374761 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B375075 : Blo 374761 375075 := bstep (se 1 (by rfl) ⟨281306, by rfl⟩ : syracuseStep 375075 = 562613) B562613
theorem B1898801 : Blo 374761 1898801 := bstep (se 2 (by rfl) ⟨712050, by rfl⟩ : syracuseStep 1898801 = 1424101) B1424101
theorem B375091 : Blo 374761 375091 := bstep (se 1 (by rfl) ⟨281318, by rfl⟩ : syracuseStep 375091 = 562637) B562637
theorem B563507 : Blo 374761 563507 := bstep (se 1 (by rfl) ⟨422630, by rfl⟩ : syracuseStep 563507 = 845261) B845261
theorem B375107 : Blo 374761 375107 := bstep (se 1 (by rfl) ⟨281330, by rfl⟩ : syracuseStep 375107 = 562661) B562661
theorem B563537 : Blo 374761 563537 := bstep (se 2 (by rfl) ⟨211326, by rfl⟩ : syracuseStep 563537 = 422653) B422653
theorem B375123 : Blo 374761 375123 := bstep (se 1 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 375123 = 562685) B562685
theorem B1104209 : Blo 374761 1104209 := bstep (se 2 (by rfl) ⟨414078, by rfl⟩ : syracuseStep 1104209 = 828157) B828157
theorem B637267 : Blo 374761 637267 := bstep (se 1 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 637267 = 955901) B955901
theorem B375139 : Blo 374761 375139 := bstep (se 1 (by rfl) ⟨281354, by rfl⟩ : syracuseStep 375139 = 562709) B562709
theorem B563555 : Blo 374761 563555 := bstep (se 1 (by rfl) ⟨422666, by rfl⟩ : syracuseStep 563555 = 845333) B845333
theorem B424291 : Blo 374761 424291 := bstep (se 1 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 424291 = 636437) B636437
theorem B1268081 : Blo 374761 1268081 := bstep (se 2 (by rfl) ⟨475530, by rfl⟩ : syracuseStep 1268081 = 951061) B951061
theorem B375155 : Blo 374761 375155 := bstep (se 1 (by rfl) ⟨281366, by rfl⟩ : syracuseStep 375155 = 562733) B562733
theorem B563585 : Blo 374761 563585 := bstep (se 2 (by rfl) ⟨211344, by rfl⟩ : syracuseStep 563585 = 422689) B422689
theorem B375171 : Blo 374761 375171 := bstep (se 1 (by rfl) ⟨281378, by rfl⟩ : syracuseStep 375171 = 562757) B562757
theorem B375187 : Blo 374761 375187 := bstep (se 1 (by rfl) ⟨281390, by rfl⟩ : syracuseStep 375187 = 562781) B562781
theorem B563603 : Blo 374761 563603 := bstep (se 1 (by rfl) ⟨422702, by rfl⟩ : syracuseStep 563603 = 845405) B845405
theorem B375203 : Blo 374761 375203 := bstep (se 1 (by rfl) ⟨281402, by rfl⟩ : syracuseStep 375203 = 562805) B562805
theorem B563633 : Blo 374761 563633 := bstep (se 2 (by rfl) ⟨211362, by rfl⟩ : syracuseStep 563633 = 422725) B422725
theorem B375219 : Blo 374761 375219 := bstep (se 1 (by rfl) ⟨281414, by rfl⟩ : syracuseStep 375219 = 562829) B562829
theorem B375235 : Blo 374761 375235 := bstep (se 1 (by rfl) ⟨281426, by rfl⟩ : syracuseStep 375235 = 562853) B562853
theorem B563651 : Blo 374761 563651 := bstep (se 1 (by rfl) ⟨422738, by rfl⟩ : syracuseStep 563651 = 845477) B845477
theorem B375251 : Blo 374761 375251 := bstep (se 1 (by rfl) ⟨281438, by rfl⟩ : syracuseStep 375251 = 562877) B562877
theorem B563681 : Blo 374761 563681 := bstep (se 2 (by rfl) ⟨211380, by rfl⟩ : syracuseStep 563681 = 422761) B422761
theorem B375267 : Blo 374761 375267 := bstep (se 1 (by rfl) ⟨281450, by rfl⟩ : syracuseStep 375267 = 562901) B562901
theorem B637409 : Blo 374761 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B375283 : Blo 374761 375283 := bstep (se 1 (by rfl) ⟨281462, by rfl⟩ : syracuseStep 375283 = 562925) B562925
theorem B563699 : Blo 374761 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B424435 : Blo 374761 424435 := bstep (se 1 (by rfl) ⟨318326, by rfl⟩ : syracuseStep 424435 = 636653) B636653
theorem B375299 : Blo 374761 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B563729 : Blo 374761 563729 := bstep (se 2 (by rfl) ⟨211398, by rfl⟩ : syracuseStep 563729 = 422797) B422797
theorem B375315 : Blo 374761 375315 := bstep (se 1 (by rfl) ⟨281486, by rfl⟩ : syracuseStep 375315 = 562973) B562973
theorem B375331 : Blo 374761 375331 := bstep (se 1 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 375331 = 562997) B562997
theorem B563747 : Blo 374761 563747 := bstep (se 1 (by rfl) ⟨422810, by rfl⟩ : syracuseStep 563747 = 845621) B845621
theorem B2062883 : Blo 374761 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B2095651 : Blo 374761 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B375347 : Blo 374761 375347 := bstep (se 1 (by rfl) ⟨281510, by rfl⟩ : syracuseStep 375347 = 563021) B563021
theorem B563777 : Blo 374761 563777 := bstep (se 2 (by rfl) ⟨211416, by rfl⟩ : syracuseStep 563777 = 422833) B422833
theorem B375363 : Blo 374761 375363 := bstep (se 1 (by rfl) ⟨281522, by rfl⟩ : syracuseStep 375363 = 563045) B563045
theorem B375379 : Blo 374761 375379 := bstep (se 1 (by rfl) ⟨281534, by rfl⟩ : syracuseStep 375379 = 563069) B563069
theorem B563795 : Blo 374761 563795 := bstep (se 1 (by rfl) ⟨422846, by rfl⟩ : syracuseStep 563795 = 845693) B845693
theorem B375395 : Blo 374761 375395 := bstep (se 1 (by rfl) ⟨281546, by rfl⟩ : syracuseStep 375395 = 563093) B563093
theorem B563825 : Blo 374761 563825 := bstep (se 2 (by rfl) ⟨211434, by rfl⟩ : syracuseStep 563825 = 422869) B422869
theorem B375411 : Blo 374761 375411 := bstep (se 1 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 375411 = 563117) B563117
theorem B375427 : Blo 374761 375427 := bstep (se 1 (by rfl) ⟨281570, by rfl⟩ : syracuseStep 375427 = 563141) B563141
theorem B563843 : Blo 374761 563843 := bstep (se 1 (by rfl) ⟨422882, by rfl⟩ : syracuseStep 563843 = 845765) B845765
theorem B2038405 : Blo 374761 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B375443 : Blo 374761 375443 := bstep (se 1 (by rfl) ⟨281582, by rfl⟩ : syracuseStep 375443 = 563165) B563165
theorem B563873 : Blo 374761 563873 := bstep (se 2 (by rfl) ⟨211452, by rfl⟩ : syracuseStep 563873 = 422905) B422905
theorem B375459 : Blo 374761 375459 := bstep (se 1 (by rfl) ⟨281594, by rfl⟩ : syracuseStep 375459 = 563189) B563189
theorem B375475 : Blo 374761 375475 := bstep (se 1 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 375475 = 563213) B563213
theorem B563891 : Blo 374761 563891 := bstep (se 1 (by rfl) ⟨422918, by rfl⟩ : syracuseStep 563891 = 845837) B845837
theorem B375491 : Blo 374761 375491 := bstep (se 1 (by rfl) ⟨281618, by rfl⟩ : syracuseStep 375491 = 563237) B563237
theorem B563921 : Blo 374761 563921 := bstep (se 2 (by rfl) ⟨211470, by rfl⟩ : syracuseStep 563921 = 422941) B422941
theorem B375507 : Blo 374761 375507 := bstep (se 1 (by rfl) ⟨281630, by rfl⟩ : syracuseStep 375507 = 563261) B563261
theorem B375523 : Blo 374761 375523 := bstep (se 1 (by rfl) ⟨281642, by rfl⟩ : syracuseStep 375523 = 563285) B563285
theorem B563939 : Blo 374761 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B3209969 : Blo 374761 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B375539 : Blo 374761 375539 := bstep (se 1 (by rfl) ⟨281654, by rfl⟩ : syracuseStep 375539 = 563309) B563309
theorem B563969 : Blo 374761 563969 := bstep (se 2 (by rfl) ⟨211488, by rfl⟩ : syracuseStep 563969 = 422977) B422977
theorem B375555 : Blo 374761 375555 := bstep (se 1 (by rfl) ⟨281666, by rfl⟩ : syracuseStep 375555 = 563333) B563333
theorem B604945 : Blo 374761 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B375571 : Blo 374761 375571 := bstep (se 1 (by rfl) ⟨281678, by rfl⟩ : syracuseStep 375571 = 563357) B563357
theorem B563987 : Blo 374761 563987 := bstep (se 1 (by rfl) ⟨422990, by rfl⟩ : syracuseStep 563987 = 845981) B845981
theorem B375587 : Blo 374761 375587 := bstep (se 1 (by rfl) ⟨281690, by rfl⟩ : syracuseStep 375587 = 563381) B563381
theorem B2136881 : Blo 374761 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B564017 : Blo 374761 564017 := bstep (se 2 (by rfl) ⟨211506, by rfl⟩ : syracuseStep 564017 = 423013) B423013
theorem B375603 : Blo 374761 375603 := bstep (se 1 (by rfl) ⟨281702, by rfl⟩ : syracuseStep 375603 = 563405) B563405
theorem B424723 : Blo 374761 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B375619 : Blo 374761 375619 := bstep (se 1 (by rfl) ⟨281714, by rfl⟩ : syracuseStep 375619 = 563429) B563429
theorem B564035 : Blo 374761 564035 := bstep (se 1 (by rfl) ⟨423026, by rfl⟩ : syracuseStep 564035 = 846053) B846053
theorem B1071949 : Blo 374761 1071949 := bstep (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) B401981
theorem B375635 : Blo 374761 375635 := bstep (se 1 (by rfl) ⟨281726, by rfl⟩ : syracuseStep 375635 = 563453) B563453
theorem B564065 : Blo 374761 564065 := bstep (se 2 (by rfl) ⟨211524, by rfl⟩ : syracuseStep 564065 = 423049) B423049
theorem B3849059 : Blo 374761 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B375651 : Blo 374761 375651 := bstep (se 1 (by rfl) ⟨281738, by rfl⟩ : syracuseStep 375651 = 563477) B563477
theorem B375667 : Blo 374761 375667 := bstep (se 1 (by rfl) ⟨281750, by rfl⟩ : syracuseStep 375667 = 563501) B563501
theorem B564083 : Blo 374761 564083 := bstep (se 1 (by rfl) ⟨423062, by rfl⟩ : syracuseStep 564083 = 846125) B846125
theorem B375683 : Blo 374761 375683 := bstep (se 1 (by rfl) ⟨281762, by rfl⟩ : syracuseStep 375683 = 563525) B563525
theorem B1268621 : Blo 374761 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B564113 : Blo 374761 564113 := bstep (se 2 (by rfl) ⟨211542, by rfl⟩ : syracuseStep 564113 = 423085) B423085
theorem B375699 : Blo 374761 375699 := bstep (se 1 (by rfl) ⟨281774, by rfl⟩ : syracuseStep 375699 = 563549) B563549
theorem B375715 : Blo 374761 375715 := bstep (se 1 (by rfl) ⟨281786, by rfl⟩ : syracuseStep 375715 = 563573) B563573
theorem B564131 : Blo 374761 564131 := bstep (se 1 (by rfl) ⟨423098, by rfl⟩ : syracuseStep 564131 = 846197) B846197
theorem B424867 : Blo 374761 424867 := bstep (se 1 (by rfl) ⟨318650, by rfl⟩ : syracuseStep 424867 = 637301) B637301
theorem B375731 : Blo 374761 375731 := bstep (se 1 (by rfl) ⟨281798, by rfl⟩ : syracuseStep 375731 = 563597) B563597
theorem B564161 : Blo 374761 564161 := bstep (se 2 (by rfl) ⟨211560, by rfl⟩ : syracuseStep 564161 = 423121) B423121
theorem B375747 : Blo 374761 375747 := bstep (se 1 (by rfl) ⟨281810, by rfl⟩ : syracuseStep 375747 = 563621) B563621
theorem B1268675 : Blo 374761 1268675 := bstep (se 1 (by rfl) ⟨951506, by rfl⟩ : syracuseStep 1268675 = 1903013) B1903013
theorem B375763 : Blo 374761 375763 := bstep (se 1 (by rfl) ⟨281822, by rfl⟩ : syracuseStep 375763 = 563645) B563645
theorem B564179 : Blo 374761 564179 := bstep (se 1 (by rfl) ⟨423134, by rfl⟩ : syracuseStep 564179 = 846269) B846269
theorem B375779 : Blo 374761 375779 := bstep (se 1 (by rfl) ⟨281834, by rfl⟩ : syracuseStep 375779 = 563669) B563669
theorem B1072109 : Blo 374761 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B564209 : Blo 374761 564209 := bstep (se 2 (by rfl) ⟨211578, by rfl⟩ : syracuseStep 564209 = 423157) B423157
theorem B375795 : Blo 374761 375795 := bstep (se 1 (by rfl) ⟨281846, by rfl⟩ : syracuseStep 375795 = 563693) B563693
theorem B375811 : Blo 374761 375811 := bstep (se 1 (by rfl) ⟨281858, by rfl⟩ : syracuseStep 375811 = 563717) B563717
theorem B564227 : Blo 374761 564227 := bstep (se 1 (by rfl) ⟨423170, by rfl⟩ : syracuseStep 564227 = 846341) B846341
theorem B375827 : Blo 374761 375827 := bstep (se 1 (by rfl) ⟨281870, by rfl⟩ : syracuseStep 375827 = 563741) B563741
theorem B564257 : Blo 374761 564257 := bstep (se 2 (by rfl) ⟨211596, by rfl⟩ : syracuseStep 564257 = 423193) B423193
theorem B375843 : Blo 374761 375843 := bstep (se 1 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 375843 = 563765) B563765
theorem B375859 : Blo 374761 375859 := bstep (se 1 (by rfl) ⟨281894, by rfl⟩ : syracuseStep 375859 = 563789) B563789
theorem B564275 : Blo 374761 564275 := bstep (se 1 (by rfl) ⟨423206, by rfl⟩ : syracuseStep 564275 = 846413) B846413
theorem B375875 : Blo 374761 375875 := bstep (se 1 (by rfl) ⟨281906, by rfl⟩ : syracuseStep 375875 = 563813) B563813
theorem B564305 : Blo 374761 564305 := bstep (se 2 (by rfl) ⟨211614, by rfl⟩ : syracuseStep 564305 = 423229) B423229
theorem B375891 : Blo 374761 375891 := bstep (se 1 (by rfl) ⟨281918, by rfl⟩ : syracuseStep 375891 = 563837) B563837
theorem B375907 : Blo 374761 375907 := bstep (se 1 (by rfl) ⟨281930, by rfl⟩ : syracuseStep 375907 = 563861) B563861
theorem B564323 : Blo 374761 564323 := bstep (se 1 (by rfl) ⟨423242, by rfl⟩ : syracuseStep 564323 = 846485) B846485
theorem B375923 : Blo 374761 375923 := bstep (se 1 (by rfl) ⟨281942, by rfl⟩ : syracuseStep 375923 = 563885) B563885
theorem B564353 : Blo 374761 564353 := bstep (se 2 (by rfl) ⟨211632, by rfl⟩ : syracuseStep 564353 = 423265) B423265
theorem B375939 : Blo 374761 375939 := bstep (se 1 (by rfl) ⟨281954, by rfl⟩ : syracuseStep 375939 = 563909) B563909
theorem B375955 : Blo 374761 375955 := bstep (se 1 (by rfl) ⟨281966, by rfl⟩ : syracuseStep 375955 = 563933) B563933
theorem B564371 : Blo 374761 564371 := bstep (se 1 (by rfl) ⟨423278, by rfl⟩ : syracuseStep 564371 = 846557) B846557
theorem B375971 : Blo 374761 375971 := bstep (se 1 (by rfl) ⟨281978, by rfl⟩ : syracuseStep 375971 = 563957) B563957
theorem B1072291 : Blo 374761 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B564401 : Blo 374761 564401 := bstep (se 2 (by rfl) ⟨211650, by rfl⟩ : syracuseStep 564401 = 423301) B423301
theorem B375987 : Blo 374761 375987 := bstep (se 1 (by rfl) ⟨281990, by rfl⟩ : syracuseStep 375987 = 563981) B563981
theorem B376003 : Blo 374761 376003 := bstep (se 1 (by rfl) ⟨282002, by rfl⟩ : syracuseStep 376003 = 564005) B564005
theorem B564419 : Blo 374761 564419 := bstep (se 1 (by rfl) ⟨423314, by rfl⟩ : syracuseStep 564419 = 846629) B846629
theorem B1268945 : Blo 374761 1268945 := bstep (se 2 (by rfl) ⟨475854, by rfl⟩ : syracuseStep 1268945 = 951709) B951709
theorem B376019 : Blo 374761 376019 := bstep (se 1 (by rfl) ⟨282014, by rfl⟩ : syracuseStep 376019 = 564029) B564029
theorem B564449 : Blo 374761 564449 := bstep (se 2 (by rfl) ⟨211668, by rfl⟩ : syracuseStep 564449 = 423337) B423337
theorem B376035 : Blo 374761 376035 := bstep (se 1 (by rfl) ⟨282026, by rfl⟩ : syracuseStep 376035 = 564053) B564053
theorem B376051 : Blo 374761 376051 := bstep (se 1 (by rfl) ⟨282038, by rfl⟩ : syracuseStep 376051 = 564077) B564077
theorem B564467 : Blo 374761 564467 := bstep (se 1 (by rfl) ⟨423350, by rfl⟩ : syracuseStep 564467 = 846701) B846701
theorem B376067 : Blo 374761 376067 := bstep (se 1 (by rfl) ⟨282050, by rfl⟩ : syracuseStep 376067 = 564101) B564101
theorem B564497 : Blo 374761 564497 := bstep (se 2 (by rfl) ⟨211686, by rfl⟩ : syracuseStep 564497 = 423373) B423373
theorem B376083 : Blo 374761 376083 := bstep (se 1 (by rfl) ⟨282062, by rfl⟩ : syracuseStep 376083 = 564125) B564125
theorem B376099 : Blo 374761 376099 := bstep (se 1 (by rfl) ⟨282074, by rfl⟩ : syracuseStep 376099 = 564149) B564149
theorem B564515 : Blo 374761 564515 := bstep (se 1 (by rfl) ⟨423386, by rfl⟩ : syracuseStep 564515 = 846773) B846773
theorem B949553 : Blo 374761 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B376115 : Blo 374761 376115 := bstep (se 1 (by rfl) ⟨282086, by rfl⟩ : syracuseStep 376115 = 564173) B564173
theorem B564545 : Blo 374761 564545 := bstep (se 2 (by rfl) ⟨211704, by rfl⟩ : syracuseStep 564545 = 423409) B423409
theorem B376131 : Blo 374761 376131 := bstep (se 1 (by rfl) ⟨282098, by rfl⟩ : syracuseStep 376131 = 564197) B564197
theorem B965969 : Blo 374761 965969 := bstep (se 2 (by rfl) ⟨362238, by rfl⟩ : syracuseStep 965969 = 724477) B724477
theorem B376147 : Blo 374761 376147 := bstep (se 1 (by rfl) ⟨282110, by rfl⟩ : syracuseStep 376147 = 564221) B564221
theorem B564563 : Blo 374761 564563 := bstep (se 1 (by rfl) ⟨423422, by rfl⟩ : syracuseStep 564563 = 846845) B846845
theorem B949603 : Blo 374761 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B376163 : Blo 374761 376163 := bstep (se 1 (by rfl) ⟨282122, by rfl⟩ : syracuseStep 376163 = 564245) B564245
theorem B564593 : Blo 374761 564593 := bstep (se 2 (by rfl) ⟨211722, by rfl⟩ : syracuseStep 564593 = 423445) B423445
theorem B376179 : Blo 374761 376179 := bstep (se 1 (by rfl) ⟨282134, by rfl⟩ : syracuseStep 376179 = 564269) B564269
theorem B376195 : Blo 374761 376195 := bstep (se 1 (by rfl) ⟨282146, by rfl⟩ : syracuseStep 376195 = 564293) B564293
theorem B564611 : Blo 374761 564611 := bstep (se 1 (by rfl) ⟨423458, by rfl⟩ : syracuseStep 564611 = 846917) B846917
theorem B712081 : Blo 374761 712081 := bstep (se 2 (by rfl) ⟨267030, by rfl⟩ : syracuseStep 712081 = 534061) B534061
theorem B376211 : Blo 374761 376211 := bstep (se 1 (by rfl) ⟨282158, by rfl⟩ : syracuseStep 376211 = 564317) B564317
theorem B564641 : Blo 374761 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B376227 : Blo 374761 376227 := bstep (se 1 (by rfl) ⟨282170, by rfl⟩ : syracuseStep 376227 = 564341) B564341
theorem B1359281 : Blo 374761 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B376243 : Blo 374761 376243 := bstep (se 1 (by rfl) ⟨282182, by rfl⟩ : syracuseStep 376243 = 564365) B564365
theorem B564659 : Blo 374761 564659 := bstep (se 1 (by rfl) ⟨423494, by rfl⟩ : syracuseStep 564659 = 846989) B846989
theorem B376259 : Blo 374761 376259 := bstep (se 1 (by rfl) ⟨282194, by rfl⟩ : syracuseStep 376259 = 564389) B564389
theorem B3440069 : Blo 374761 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B564689 : Blo 374761 564689 := bstep (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) B423517
theorem B376275 : Blo 374761 376275 := bstep (se 1 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 376275 = 564413) B564413
theorem B376291 : Blo 374761 376291 := bstep (se 1 (by rfl) ⟨282218, by rfl⟩ : syracuseStep 376291 = 564437) B564437
theorem B564707 : Blo 374761 564707 := bstep (se 1 (by rfl) ⟨423530, by rfl⟩ : syracuseStep 564707 = 847061) B847061
theorem B949745 : Blo 374761 949745 := bstep (se 2 (by rfl) ⟨356154, by rfl⟩ : syracuseStep 949745 = 712309) B712309
theorem B376307 : Blo 374761 376307 := bstep (se 1 (by rfl) ⟨282230, by rfl⟩ : syracuseStep 376307 = 564461) B564461
theorem B564737 : Blo 374761 564737 := bstep (se 2 (by rfl) ⟨211776, by rfl⟩ : syracuseStep 564737 = 423553) B423553
theorem B507395 : Blo 374761 507395 := bstep (se 1 (by rfl) ⟨380546, by rfl⟩ : syracuseStep 507395 = 761093) B761093
theorem B376323 : Blo 374761 376323 := bstep (se 1 (by rfl) ⟨282242, by rfl⟩ : syracuseStep 376323 = 564485) B564485
theorem B843281 : Blo 374761 843281 := bstep (se 2 (by rfl) ⟨316230, by rfl⟩ : syracuseStep 843281 = 632461) B632461
theorem B1285649 : Blo 374761 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B376339 : Blo 374761 376339 := bstep (se 1 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 376339 = 564509) B564509
theorem B564755 : Blo 374761 564755 := bstep (se 1 (by rfl) ⟨423566, by rfl⟩ : syracuseStep 564755 = 847133) B847133
theorem B843299 : Blo 374761 843299 := bstep (se 1 (by rfl) ⟨632474, by rfl⟩ : syracuseStep 843299 = 1264949) B1264949
theorem B376355 : Blo 374761 376355 := bstep (se 1 (by rfl) ⟨282266, by rfl⟩ : syracuseStep 376355 = 564533) B564533
theorem B1433123 : Blo 374761 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B564785 : Blo 374761 564785 := bstep (se 2 (by rfl) ⟨211794, by rfl⟩ : syracuseStep 564785 = 423589) B423589
theorem B376371 : Blo 374761 376371 := bstep (se 1 (by rfl) ⟨282278, by rfl⟩ : syracuseStep 376371 = 564557) B564557
theorem B376387 : Blo 374761 376387 := bstep (se 1 (by rfl) ⟨282290, by rfl⟩ : syracuseStep 376387 = 564581) B564581
theorem B564803 : Blo 374761 564803 := bstep (se 1 (by rfl) ⟨423602, by rfl⟩ : syracuseStep 564803 = 847205) B847205
theorem B376403 : Blo 374761 376403 := bstep (se 1 (by rfl) ⟨282302, by rfl⟩ : syracuseStep 376403 = 564605) B564605
theorem B564833 : Blo 374761 564833 := bstep (se 2 (by rfl) ⟨211812, by rfl⟩ : syracuseStep 564833 = 423625) B423625
theorem B376419 : Blo 374761 376419 := bstep (se 1 (by rfl) ⟨282314, by rfl⟩ : syracuseStep 376419 = 564629) B564629
theorem B1449571 : Blo 374761 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B376435 : Blo 374761 376435 := bstep (se 1 (by rfl) ⟨282326, by rfl⟩ : syracuseStep 376435 = 564653) B564653
theorem B564851 : Blo 374761 564851 := bstep (se 1 (by rfl) ⟨423638, by rfl⟩ : syracuseStep 564851 = 847277) B847277
theorem B376451 : Blo 374761 376451 := bstep (se 1 (by rfl) ⟨282338, by rfl⟩ : syracuseStep 376451 = 564677) B564677
theorem B2408069 : Blo 374761 2408069 := bstep (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) B451513
theorem B564881 : Blo 374761 564881 := bstep (se 2 (by rfl) ⟨211830, by rfl⟩ : syracuseStep 564881 = 423661) B423661
theorem B376467 : Blo 374761 376467 := bstep (se 1 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 376467 = 564701) B564701
theorem B1425059 : Blo 374761 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B376483 : Blo 374761 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B564899 : Blo 374761 564899 := bstep (se 1 (by rfl) ⟨423674, by rfl⟩ : syracuseStep 564899 = 847349) B847349
theorem B1425073 : Blo 374761 1425073 := bstep (se 2 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 1425073 = 1068805) B1068805
theorem B376499 : Blo 374761 376499 := bstep (se 1 (by rfl) ⟨282374, by rfl⟩ : syracuseStep 376499 = 564749) B564749
theorem B376515 : Blo 374761 376515 := bstep (se 1 (by rfl) ⟨282386, by rfl⟩ : syracuseStep 376515 = 564773) B564773
theorem B564929 : Blo 374761 564929 := bstep (se 2 (by rfl) ⟨211848, by rfl⟩ : syracuseStep 564929 = 423697) B423697
theorem B376531 : Blo 374761 376531 := bstep (se 1 (by rfl) ⟨282398, by rfl⟩ : syracuseStep 376531 = 564797) B564797
theorem B564947 : Blo 374761 564947 := bstep (se 1 (by rfl) ⟨423710, by rfl⟩ : syracuseStep 564947 = 847421) B847421
theorem B1900259 : Blo 374761 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B376547 : Blo 374761 376547 := bstep (se 1 (by rfl) ⟨282410, by rfl⟩ : syracuseStep 376547 = 564821) B564821
theorem B1269485 : Blo 374761 1269485 := bstep (se 3 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 1269485 = 476057) B476057
theorem B564977 : Blo 374761 564977 := bstep (se 2 (by rfl) ⟨211866, by rfl⟩ : syracuseStep 564977 = 423733) B423733
theorem B376563 : Blo 374761 376563 := bstep (se 1 (by rfl) ⟨282422, by rfl⟩ : syracuseStep 376563 = 564845) B564845
theorem B450307 : Blo 374761 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B376579 : Blo 374761 376579 := bstep (se 1 (by rfl) ⟨282434, by rfl⟩ : syracuseStep 376579 = 564869) B564869
theorem B564995 : Blo 374761 564995 := bstep (se 1 (by rfl) ⟨423746, by rfl⟩ : syracuseStep 564995 = 847493) B847493
theorem B1801997 : Blo 374761 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B376595 : Blo 374761 376595 := bstep (se 1 (by rfl) ⟨282446, by rfl⟩ : syracuseStep 376595 = 564893) B564893
theorem B565025 : Blo 374761 565025 := bstep (se 2 (by rfl) ⟨211884, by rfl⟩ : syracuseStep 565025 = 423769) B423769
theorem B802595 : Blo 374761 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B1269539 : Blo 374761 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B376611 : Blo 374761 376611 := bstep (se 1 (by rfl) ⟨282458, by rfl⟩ : syracuseStep 376611 = 564917) B564917
theorem B843569 : Blo 374761 843569 := bstep (se 2 (by rfl) ⟨316338, by rfl⟩ : syracuseStep 843569 = 632677) B632677
theorem B376627 : Blo 374761 376627 := bstep (se 1 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 376627 = 564941) B564941
theorem B565043 : Blo 374761 565043 := bstep (se 1 (by rfl) ⟨423782, by rfl⟩ : syracuseStep 565043 = 847565) B847565
theorem B843587 : Blo 374761 843587 := bstep (se 1 (by rfl) ⟨632690, by rfl⟩ : syracuseStep 843587 = 1265381) B1265381
theorem B376643 : Blo 374761 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B565073 : Blo 374761 565073 := bstep (se 2 (by rfl) ⟨211902, by rfl⟩ : syracuseStep 565073 = 423805) B423805
theorem B376659 : Blo 374761 376659 := bstep (se 1 (by rfl) ⟨282494, by rfl⟩ : syracuseStep 376659 = 564989) B564989
theorem B474979 : Blo 374761 474979 := bstep (se 1 (by rfl) ⟨356234, by rfl⟩ : syracuseStep 474979 = 712469) B712469
theorem B376675 : Blo 374761 376675 := bstep (se 1 (by rfl) ⟨282506, by rfl⟩ : syracuseStep 376675 = 565013) B565013
theorem B565091 : Blo 374761 565091 := bstep (se 1 (by rfl) ⟨423818, by rfl⟩ : syracuseStep 565091 = 847637) B847637
theorem B376691 : Blo 374761 376691 := bstep (se 1 (by rfl) ⟨282518, by rfl⟩ : syracuseStep 376691 = 565037) B565037
theorem B565121 : Blo 374761 565121 := bstep (se 2 (by rfl) ⟨211920, by rfl⟩ : syracuseStep 565121 = 423841) B423841
theorem B376707 : Blo 374761 376707 := bstep (se 1 (by rfl) ⟨282530, by rfl⟩ : syracuseStep 376707 = 565061) B565061
theorem B450451 : Blo 374761 450451 := bstep (se 1 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 450451 = 675677) B675677
theorem B376723 : Blo 374761 376723 := bstep (se 1 (by rfl) ⟨282542, by rfl⟩ : syracuseStep 376723 = 565085) B565085
theorem B565139 : Blo 374761 565139 := bstep (se 1 (by rfl) ⟨423854, by rfl⟩ : syracuseStep 565139 = 847709) B847709
theorem B376739 : Blo 374761 376739 := bstep (se 1 (by rfl) ⟨282554, by rfl⟩ : syracuseStep 376739 = 565109) B565109
theorem B565169 : Blo 374761 565169 := bstep (se 2 (by rfl) ⟨211938, by rfl⟩ : syracuseStep 565169 = 423877) B423877
theorem B376755 : Blo 374761 376755 := bstep (se 1 (by rfl) ⟨282566, by rfl⟩ : syracuseStep 376755 = 565133) B565133
theorem B475075 : Blo 374761 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B376771 : Blo 374761 376771 := bstep (se 1 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 376771 = 565157) B565157
theorem B565187 : Blo 374761 565187 := bstep (se 1 (by rfl) ⟨423890, by rfl⟩ : syracuseStep 565187 = 847781) B847781
theorem B376787 : Blo 374761 376787 := bstep (se 1 (by rfl) ⟨282590, by rfl⟩ : syracuseStep 376787 = 565181) B565181
theorem B376803 : Blo 374761 376803 := bstep (se 1 (by rfl) ⟨282602, by rfl⟩ : syracuseStep 376803 = 565205) B565205
theorem B565217 : Blo 374761 565217 := bstep (se 2 (by rfl) ⟨211956, by rfl⟩ : syracuseStep 565217 = 423913) B423913
theorem B1802225 : Blo 374761 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B376819 : Blo 374761 376819 := bstep (se 1 (by rfl) ⟨282614, by rfl⟩ : syracuseStep 376819 = 565229) B565229
theorem B565235 : Blo 374761 565235 := bstep (se 1 (by rfl) ⟨423926, by rfl⟩ : syracuseStep 565235 = 847853) B847853
theorem B565259 : Blo 374761 565259 := bstep (se 1 (by rfl) ⟨423944, by rfl⟩ : syracuseStep 565259 = 847889) B847889
theorem B376843 : Blo 374761 376843 := bstep (se 1 (by rfl) ⟨282632, by rfl⟩ : syracuseStep 376843 = 565265) B565265
theorem B565271 : Blo 374761 565271 := bstep (se 1 (by rfl) ⟨423953, by rfl⟩ : syracuseStep 565271 = 847907) B847907
theorem B376855 : Blo 374761 376855 := bstep (se 1 (by rfl) ⟨282641, by rfl⟩ : syracuseStep 376855 = 565283) B565283
theorem B376875 : Blo 374761 376875 := bstep (se 1 (by rfl) ⟨282656, by rfl⟩ : syracuseStep 376875 = 565313) B565313
theorem B376887 : Blo 374761 376887 := bstep (se 1 (by rfl) ⟨282665, by rfl⟩ : syracuseStep 376887 = 565331) B565331
theorem B376907 : Blo 374761 376907 := bstep (se 1 (by rfl) ⟨282680, by rfl⟩ : syracuseStep 376907 = 565361) B565361
theorem B376919 : Blo 374761 376919 := bstep (se 1 (by rfl) ⟨282689, by rfl⟩ : syracuseStep 376919 = 565379) B565379
theorem B565337 : Blo 374761 565337 := bstep (se 2 (by rfl) ⟨212001, by rfl⟩ : syracuseStep 565337 = 424003) B424003
theorem B376939 : Blo 374761 376939 := bstep (se 1 (by rfl) ⟨282704, by rfl⟩ : syracuseStep 376939 = 565409) B565409
theorem B376951 : Blo 374761 376951 := bstep (se 1 (by rfl) ⟨282713, by rfl⟩ : syracuseStep 376951 = 565427) B565427
theorem B4079747 : Blo 374761 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B376971 : Blo 374761 376971 := bstep (se 1 (by rfl) ⟨282728, by rfl⟩ : syracuseStep 376971 = 565457) B565457
theorem B1425559 : Blo 374761 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B8151191 : Blo 374761 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B843929 : Blo 374761 843929 := bstep (se 2 (by rfl) ⟨316473, by rfl⟩ : syracuseStep 843929 = 632947) B632947
theorem B376983 : Blo 374761 376983 := bstep (se 1 (by rfl) ⟨282737, by rfl⟩ : syracuseStep 376983 = 565475) B565475
theorem B377003 : Blo 374761 377003 := bstep (se 1 (by rfl) ⟨282752, by rfl⟩ : syracuseStep 377003 = 565505) B565505
theorem B377015 : Blo 374761 377015 := bstep (se 1 (by rfl) ⟨282761, by rfl⟩ : syracuseStep 377015 = 565523) B565523
theorem B565451 : Blo 374761 565451 := bstep (se 1 (by rfl) ⟨424088, by rfl⟩ : syracuseStep 565451 = 848177) B848177
theorem B377035 : Blo 374761 377035 := bstep (se 1 (by rfl) ⟨282776, by rfl⟩ : syracuseStep 377035 = 565553) B565553
theorem B565463 : Blo 374761 565463 := bstep (se 1 (by rfl) ⟨424097, by rfl⟩ : syracuseStep 565463 = 848195) B848195
theorem B377047 : Blo 374761 377047 := bstep (se 1 (by rfl) ⟨282785, by rfl⟩ : syracuseStep 377047 = 565571) B565571
theorem B1204445 : Blo 374761 1204445 := bstep (se 3 (by rfl) ⟨225833, by rfl⟩ : syracuseStep 1204445 = 451667) B451667
theorem B1433821 : Blo 374761 1433821 := bstep (se 3 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 1433821 = 537683) B537683
theorem B377067 : Blo 374761 377067 := bstep (se 1 (by rfl) ⟨282800, by rfl⟩ : syracuseStep 377067 = 565601) B565601
theorem B844019 : Blo 374761 844019 := bstep (se 1 (by rfl) ⟨633014, by rfl⟩ : syracuseStep 844019 = 1266029) B1266029
theorem B377079 : Blo 374761 377079 := bstep (se 1 (by rfl) ⟨282809, by rfl⟩ : syracuseStep 377079 = 565619) B565619
theorem B1712387 : Blo 374761 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B377099 : Blo 374761 377099 := bstep (se 1 (by rfl) ⟨282824, by rfl⟩ : syracuseStep 377099 = 565649) B565649
theorem B2179345 : Blo 374761 2179345 := bstep (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) B1634509
theorem B844055 : Blo 374761 844055 := bstep (se 1 (by rfl) ⟨633041, by rfl⟩ : syracuseStep 844055 = 1266083) B1266083
theorem B377111 : Blo 374761 377111 := bstep (se 1 (by rfl) ⟨282833, by rfl⟩ : syracuseStep 377111 = 565667) B565667
theorem B565529 : Blo 374761 565529 := bstep (se 2 (by rfl) ⟨212073, by rfl⟩ : syracuseStep 565529 = 424147) B424147
theorem B377131 : Blo 374761 377131 := bstep (se 1 (by rfl) ⟨282848, by rfl⟩ : syracuseStep 377131 = 565697) B565697
theorem B4079917 : Blo 374761 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B377143 : Blo 374761 377143 := bstep (se 1 (by rfl) ⟨282857, by rfl⟩ : syracuseStep 377143 = 565715) B565715
theorem B2711873 : Blo 374761 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B377163 : Blo 374761 377163 := bstep (se 1 (by rfl) ⟨282872, by rfl⟩ : syracuseStep 377163 = 565745) B565745
theorem B377175 : Blo 374761 377175 := bstep (se 1 (by rfl) ⟨282881, by rfl⟩ : syracuseStep 377175 = 565763) B565763
theorem B1605977 : Blo 374761 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B377195 : Blo 374761 377195 := bstep (se 1 (by rfl) ⟨282896, by rfl⟩ : syracuseStep 377195 = 565793) B565793
theorem B377207 : Blo 374761 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B713099 : Blo 374761 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B565643 : Blo 374761 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B377227 : Blo 374761 377227 := bstep (se 1 (by rfl) ⟨282920, by rfl⟩ : syracuseStep 377227 = 565841) B565841
theorem B565655 : Blo 374761 565655 := bstep (se 1 (by rfl) ⟨424241, by rfl⟩ : syracuseStep 565655 = 848483) B848483
theorem B377239 : Blo 374761 377239 := bstep (se 1 (by rfl) ⟨282929, by rfl⟩ : syracuseStep 377239 = 565859) B565859
theorem B377259 : Blo 374761 377259 := bstep (se 1 (by rfl) ⟨282944, by rfl⟩ : syracuseStep 377259 = 565889) B565889
theorem B2564531 : Blo 374761 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B377271 : Blo 374761 377271 := bstep (se 1 (by rfl) ⟨282953, by rfl⟩ : syracuseStep 377271 = 565907) B565907
theorem B1360307 : Blo 374761 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B844235 : Blo 374761 844235 := bstep (se 1 (by rfl) ⟨633176, by rfl⟩ : syracuseStep 844235 = 1266353) B1266353
theorem B377291 : Blo 374761 377291 := bstep (se 1 (by rfl) ⟨282968, by rfl⟩ : syracuseStep 377291 = 565937) B565937
theorem B377303 : Blo 374761 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B1081817 : Blo 374761 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B565721 : Blo 374761 565721 := bstep (se 2 (by rfl) ⟨212145, by rfl⟩ : syracuseStep 565721 = 424291) B424291
theorem B1409501 : Blo 374761 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B377323 : Blo 374761 377323 := bstep (se 1 (by rfl) ⟨282992, by rfl⟩ : syracuseStep 377323 = 565985) B565985
theorem B377335 : Blo 374761 377335 := bstep (se 1 (by rfl) ⟨283001, by rfl⟩ : syracuseStep 377335 = 566003) B566003
theorem B844289 : Blo 374761 844289 := bstep (se 2 (by rfl) ⟨316608, by rfl⟩ : syracuseStep 844289 = 633217) B633217
theorem B377355 : Blo 374761 377355 := bstep (se 1 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 377355 = 566033) B566033
theorem B1270295 : Blo 374761 1270295 := bstep (se 1 (by rfl) ⟨952721, by rfl⟩ : syracuseStep 1270295 = 1905443) B1905443
theorem B377367 : Blo 374761 377367 := bstep (se 1 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 377367 = 566051) B566051
theorem B573977 : Blo 374761 573977 := bstep (se 2 (by rfl) ⟨215241, by rfl⟩ : syracuseStep 573977 = 430483) B430483
theorem B377387 : Blo 374761 377387 := bstep (se 1 (by rfl) ⟨283040, by rfl⟩ : syracuseStep 377387 = 566081) B566081
theorem B377399 : Blo 374761 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B950849 : Blo 374761 950849 := bstep (se 2 (by rfl) ⟨356568, by rfl⟩ : syracuseStep 950849 = 713137) B713137
theorem B713281 : Blo 374761 713281 := bstep (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) B534961
theorem B475723 : Blo 374761 475723 := bstep (se 1 (by rfl) ⟨356792, by rfl⟩ : syracuseStep 475723 = 713585) B713585
theorem B565835 : Blo 374761 565835 := bstep (se 1 (by rfl) ⟨424376, by rfl⟩ : syracuseStep 565835 = 848753) B848753
theorem B377419 : Blo 374761 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B565847 : Blo 374761 565847 := bstep (se 1 (by rfl) ⟨424385, by rfl⟩ : syracuseStep 565847 = 848771) B848771
theorem B377431 : Blo 374761 377431 := bstep (se 1 (by rfl) ⟨283073, by rfl⟩ : syracuseStep 377431 = 566147) B566147
theorem B377451 : Blo 374761 377451 := bstep (se 1 (by rfl) ⟨283088, by rfl⟩ : syracuseStep 377451 = 566177) B566177
theorem B377463 : Blo 374761 377463 := bstep (se 1 (by rfl) ⟨283097, by rfl⟩ : syracuseStep 377463 = 566195) B566195
theorem B377483 : Blo 374761 377483 := bstep (se 1 (by rfl) ⟨283112, by rfl⟩ : syracuseStep 377483 = 566225) B566225
theorem B377495 : Blo 374761 377495 := bstep (se 1 (by rfl) ⟨283121, by rfl⟩ : syracuseStep 377495 = 566243) B566243
theorem B565913 : Blo 374761 565913 := bstep (se 2 (by rfl) ⟨212217, by rfl⟩ : syracuseStep 565913 = 424435) B424435
theorem B377515 : Blo 374761 377515 := bstep (se 1 (by rfl) ⟨283136, by rfl⟩ : syracuseStep 377515 = 566273) B566273
theorem B1860275 : Blo 374761 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B377527 : Blo 374761 377527 := bstep (se 1 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 377527 = 566291) B566291
theorem B1606337 : Blo 374761 1606337 := bstep (se 2 (by rfl) ⟨602376, by rfl⟩ : syracuseStep 1606337 = 1204753) B1204753
theorem B377547 : Blo 374761 377547 := bstep (se 1 (by rfl) ⟨283160, by rfl⟩ : syracuseStep 377547 = 566321) B566321
theorem B377559 : Blo 374761 377559 := bstep (se 1 (by rfl) ⟨283169, by rfl⟩ : syracuseStep 377559 = 566339) B566339
theorem B844505 : Blo 374761 844505 := bstep (se 2 (by rfl) ⟨316689, by rfl⟩ : syracuseStep 844505 = 633379) B633379
theorem B1630937 : Blo 374761 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B2794201 : Blo 374761 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B6841073 : Blo 374761 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B377591 : Blo 374761 377591 := bstep (se 1 (by rfl) ⟨283193, by rfl⟩ : syracuseStep 377591 = 566387) B566387
theorem B566027 : Blo 374761 566027 := bstep (se 1 (by rfl) ⟨424520, by rfl⟩ : syracuseStep 566027 = 849041) B849041
theorem B377611 : Blo 374761 377611 := bstep (se 1 (by rfl) ⟨283208, by rfl⟩ : syracuseStep 377611 = 566417) B566417
theorem B817523 : Blo 374761 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B566039 : Blo 374761 566039 := bstep (se 1 (by rfl) ⟨424529, by rfl⟩ : syracuseStep 566039 = 849059) B849059
theorem B377623 : Blo 374761 377623 := bstep (se 1 (by rfl) ⟨283217, by rfl⟩ : syracuseStep 377623 = 566435) B566435
theorem B377643 : Blo 374761 377643 := bstep (se 1 (by rfl) ⟨283232, by rfl⟩ : syracuseStep 377643 = 566465) B566465
theorem B844595 : Blo 374761 844595 := bstep (se 1 (by rfl) ⟨633446, by rfl⟩ : syracuseStep 844595 = 1266893) B1266893
theorem B377655 : Blo 374761 377655 := bstep (se 1 (by rfl) ⟨283241, by rfl⟩ : syracuseStep 377655 = 566483) B566483
theorem B1016651 : Blo 374761 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B377675 : Blo 374761 377675 := bstep (se 1 (by rfl) ⟨283256, by rfl⟩ : syracuseStep 377675 = 566513) B566513
theorem B844631 : Blo 374761 844631 := bstep (se 1 (by rfl) ⟨633473, by rfl⟩ : syracuseStep 844631 = 1266947) B1266947
theorem B377687 : Blo 374761 377687 := bstep (se 1 (by rfl) ⟨283265, by rfl⟩ : syracuseStep 377687 = 566531) B566531
theorem B770905 : Blo 374761 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B566105 : Blo 374761 566105 := bstep (se 2 (by rfl) ⟨212289, by rfl⟩ : syracuseStep 566105 = 424579) B424579
theorem B377707 : Blo 374761 377707 := bstep (se 1 (by rfl) ⟨283280, by rfl⟩ : syracuseStep 377707 = 566561) B566561
theorem B377719 : Blo 374761 377719 := bstep (se 1 (by rfl) ⟨283289, by rfl⟩ : syracuseStep 377719 = 566579) B566579
theorem B377739 : Blo 374761 377739 := bstep (se 1 (by rfl) ⟨283304, by rfl⟩ : syracuseStep 377739 = 566609) B566609
theorem B713623 : Blo 374761 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B1909655 : Blo 374761 1909655 := bstep (se 1 (by rfl) ⟨1432241, by rfl⟩ : syracuseStep 1909655 = 2864483) B2864483
theorem B377751 : Blo 374761 377751 := bstep (se 1 (by rfl) ⟨283313, by rfl⟩ : syracuseStep 377751 = 566627) B566627
theorem B1426349 : Blo 374761 1426349 := bstep (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) B534881
theorem B8217521 : Blo 374761 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B566219 : Blo 374761 566219 := bstep (se 1 (by rfl) ⟨424664, by rfl⟩ : syracuseStep 566219 = 849329) B849329
theorem B402391 : Blo 374761 402391 := bstep (se 1 (by rfl) ⟨301793, by rfl⟩ : syracuseStep 402391 = 603587) B603587
theorem B566231 : Blo 374761 566231 := bstep (se 1 (by rfl) ⟨424673, by rfl⟩ : syracuseStep 566231 = 849347) B849347
theorem B844811 : Blo 374761 844811 := bstep (se 1 (by rfl) ⟨633608, by rfl⟩ : syracuseStep 844811 = 1267217) B1267217
theorem B1287191 : Blo 374761 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B566297 : Blo 374761 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B1270835 : Blo 374761 1270835 := bstep (se 1 (by rfl) ⟨953126, by rfl⟩ : syracuseStep 1270835 = 1906253) B1906253
theorem B844865 : Blo 374761 844865 := bstep (se 2 (by rfl) ⟨316824, by rfl⟩ : syracuseStep 844865 = 633649) B633649
theorem B762967 : Blo 374761 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B951385 : Blo 374761 951385 := bstep (se 2 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 951385 = 713539) B713539
theorem B3204197 : Blo 374761 3204197 := bstep (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) B600787
theorem B713843 : Blo 374761 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B566411 : Blo 374761 566411 := bstep (se 1 (by rfl) ⟨424808, by rfl⟩ : syracuseStep 566411 = 849617) B849617
theorem B3220631 : Blo 374761 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B566423 : Blo 374761 566423 := bstep (se 1 (by rfl) ⟨424817, by rfl⟩ : syracuseStep 566423 = 849635) B849635
theorem B533719 : Blo 374761 533719 := bstep (se 1 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 533719 = 800579) B800579
theorem B566489 : Blo 374761 566489 := bstep (se 2 (by rfl) ⟨212433, by rfl⟩ : syracuseStep 566489 = 424867) B424867
theorem B845081 : Blo 374761 845081 := bstep (se 2 (by rfl) ⟨316905, by rfl⟩ : syracuseStep 845081 = 633811) B633811
theorem B1074455 : Blo 374761 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B1271105 : Blo 374761 1271105 := bstep (se 2 (by rfl) ⟨476664, by rfl⟩ : syracuseStep 1271105 = 953329) B953329
theorem B566603 : Blo 374761 566603 := bstep (se 1 (by rfl) ⟨424952, by rfl⟩ : syracuseStep 566603 = 849905) B849905
theorem B714071 : Blo 374761 714071 := bstep (se 1 (by rfl) ⟨535553, by rfl⟩ : syracuseStep 714071 = 1071107) B1071107
theorem B566615 : Blo 374761 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B1353053 : Blo 374761 1353053 := bstep (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) B507395
theorem B845171 : Blo 374761 845171 := bstep (se 1 (by rfl) ⟨633878, by rfl⟩ : syracuseStep 845171 = 1267757) B1267757
theorem B845207 : Blo 374761 845207 := bstep (se 1 (by rfl) ⟨633905, by rfl⟩ : syracuseStep 845207 = 1267811) B1267811
theorem B902593 : Blo 374761 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B1902041 : Blo 374761 1902041 := bstep (se 2 (by rfl) ⟨713265, by rfl⟩ : syracuseStep 1902041 = 1426531) B1426531
theorem B476695 : Blo 374761 476695 := bstep (se 1 (by rfl) ⟨357521, by rfl⟩ : syracuseStep 476695 = 715043) B715043
theorem B845387 : Blo 374761 845387 := bstep (se 1 (by rfl) ⟨634040, by rfl⟩ : syracuseStep 845387 = 1268081) B1268081
theorem B3868235 : Blo 374761 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B714329 : Blo 374761 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B804467 : Blo 374761 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B845441 : Blo 374761 845441 := bstep (se 2 (by rfl) ⟨317040, by rfl⟩ : syracuseStep 845441 = 634081) B634081
theorem B6125719 : Blo 374761 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B4130509 : Blo 374761 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B2139979 : Blo 374761 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B845657 : Blo 374761 845657 := bstep (se 2 (by rfl) ⟨317121, by rfl⟩ : syracuseStep 845657 = 634243) B634243
theorem B1271645 : Blo 374761 1271645 := bstep (se 3 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 1271645 = 476867) B476867
theorem B2148227 : Blo 374761 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B2566039 : Blo 374761 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B845747 : Blo 374761 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B845783 : Blo 374761 845783 := bstep (se 1 (by rfl) ⟨634337, by rfl⟩ : syracuseStep 845783 = 1268675) B1268675
theorem B714739 : Blo 374761 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B1075265 : Blo 374761 1075265 := bstep (se 2 (by rfl) ⟨403224, by rfl⟩ : syracuseStep 1075265 = 806449) B806449
theorem B804953 : Blo 374761 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B2140253 : Blo 374761 2140253 := bstep (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) B802595
theorem B2402405 : Blo 374761 2402405 := bstep (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) B450451
theorem B845963 : Blo 374761 845963 := bstep (se 1 (by rfl) ⟨634472, by rfl⟩ : syracuseStep 845963 = 1268945) B1268945
theorem B1099955 : Blo 374761 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B952499 : Blo 374761 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B846017 : Blo 374761 846017 := bstep (se 2 (by rfl) ⟨317256, by rfl⟩ : syracuseStep 846017 = 634513) B634513
theorem B633035 : Blo 374761 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B1804609 : Blo 374761 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B1427777 : Blo 374761 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B633163 : Blo 374761 633163 := bstep (se 1 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 633163 = 949745) B949745
theorem B477515 : Blo 374761 477515 := bstep (se 1 (by rfl) ⟨358136, by rfl⟩ : syracuseStep 477515 = 716273) B716273
theorem B600409 : Blo 374761 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B2713949 : Blo 374761 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B846233 : Blo 374761 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B633305 : Blo 374761 633305 := bstep (se 2 (by rfl) ⟨237489, by rfl⟩ : syracuseStep 633305 = 474979) B474979
theorem B903641 : Blo 374761 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B952793 : Blo 374761 952793 := bstep (se 2 (by rfl) ⟨357297, by rfl⟩ : syracuseStep 952793 = 714595) B714595
theorem B715225 : Blo 374761 715225 := bstep (se 2 (by rfl) ⟨268209, by rfl⟩ : syracuseStep 715225 = 536419) B536419
theorem B846323 : Blo 374761 846323 := bstep (se 1 (by rfl) ⟨634742, by rfl⟩ : syracuseStep 846323 = 1269485) B1269485
theorem B2419217 : Blo 374761 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B1018391 : Blo 374761 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B846359 : Blo 374761 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B633433 : Blo 374761 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B510553 : Blo 374761 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B846539 : Blo 374761 846539 := bstep (se 1 (by rfl) ⟨634904, by rfl⟩ : syracuseStep 846539 = 1269809) B1269809
theorem B846593 : Blo 374761 846593 := bstep (se 2 (by rfl) ⟨317472, by rfl⟩ : syracuseStep 846593 = 634945) B634945
theorem B731927 : Blo 374761 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B805697 : Blo 374761 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B723799 : Blo 374761 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B1272779 : Blo 374761 1272779 := bstep (se 1 (by rfl) ⟨954584, by rfl⟩ : syracuseStep 1272779 = 1909169) B1909169
theorem B846809 : Blo 374761 846809 := bstep (se 2 (by rfl) ⟨317553, by rfl⟩ : syracuseStep 846809 = 635107) B635107
theorem B715787 : Blo 374761 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B379927 : Blo 374761 379927 := bstep (se 1 (by rfl) ⟨284945, by rfl⟩ : syracuseStep 379927 = 569891) B569891
theorem B1903661 : Blo 374761 1903661 := bstep (se 3 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 1903661 = 713873) B713873
theorem B846899 : Blo 374761 846899 := bstep (se 1 (by rfl) ⟨635174, by rfl⟩ : syracuseStep 846899 = 1270349) B1270349
theorem B846935 : Blo 374761 846935 := bstep (se 1 (by rfl) ⟨635201, by rfl⟩ : syracuseStep 846935 = 1270403) B1270403
theorem B453719 : Blo 374761 453719 := bstep (se 1 (by rfl) ⟨340289, by rfl⟩ : syracuseStep 453719 = 680579) B680579
theorem B4574339 : Blo 374761 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B6851735 : Blo 374761 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B634007 : Blo 374761 634007 := bstep (se 1 (by rfl) ⟨475505, by rfl⟩ : syracuseStep 634007 = 951011) B951011
theorem B715969 : Blo 374761 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B1273049 : Blo 374761 1273049 := bstep (se 2 (by rfl) ⟨477393, by rfl⟩ : syracuseStep 1273049 = 954787) B954787
theorem B847115 : Blo 374761 847115 := bstep (se 1 (by rfl) ⟨635336, by rfl⟩ : syracuseStep 847115 = 1270673) B1270673
theorem B634135 : Blo 374761 634135 := bstep (se 1 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 634135 = 951203) B951203
theorem B2034989 : Blo 374761 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B847169 : Blo 374761 847169 := bstep (se 2 (by rfl) ⟨317688, by rfl⟩ : syracuseStep 847169 = 635377) B635377
theorem B1510859 : Blo 374761 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B376823 : Blo 374761 376823 := bstep (se 1 (by rfl) ⟨282617, by rfl⟩ : syracuseStep 376823 = 565235) B565235
theorem B6852113 : Blo 374761 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B847385 : Blo 374761 847385 := bstep (se 2 (by rfl) ⟨317769, by rfl⟩ : syracuseStep 847385 = 635539) B635539
theorem B847475 : Blo 374761 847475 := bstep (se 1 (by rfl) ⟨635606, by rfl⟩ : syracuseStep 847475 = 1271213) B1271213
theorem B847511 : Blo 374761 847511 := bstep (se 1 (by rfl) ⟨635633, by rfl⟩ : syracuseStep 847511 = 1271267) B1271267
theorem B806593 : Blo 374761 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B6082253 : Blo 374761 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B4812493 : Blo 374761 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B1429265 : Blo 374761 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B3624749 : Blo 374761 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B1068851 : Blo 374761 1068851 := bstep (se 1 (by rfl) ⟨801638, by rfl⟩ : syracuseStep 1068851 = 1603277) B1603277
theorem B847691 : Blo 374761 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B4566901 : Blo 374761 4566901 := bstep (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) B428147
theorem B847745 : Blo 374761 847745 := bstep (se 2 (by rfl) ⟨317904, by rfl⟩ : syracuseStep 847745 = 635809) B635809
theorem B421771 : Blo 374761 421771 := bstep (se 1 (by rfl) ⟨316328, by rfl⟩ : syracuseStep 421771 = 632657) B632657
theorem B634763 : Blo 374761 634763 := bstep (se 1 (by rfl) ⟨476072, by rfl⟩ : syracuseStep 634763 = 952145) B952145
theorem B716683 : Blo 374761 716683 := bstep (se 1 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 716683 = 1075025) B1075025
theorem B905111 : Blo 374761 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B1273751 : Blo 374761 1273751 := bstep (se 1 (by rfl) ⟨955313, by rfl⟩ : syracuseStep 1273751 = 1910627) B1910627
theorem B2863025 : Blo 374761 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B716759 : Blo 374761 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B421879 : Blo 374761 421879 := bstep (se 1 (by rfl) ⟨316409, by rfl⟩ : syracuseStep 421879 = 632819) B632819
theorem B634891 : Blo 374761 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B637463 : Blo 374761 637463 := bstep (se 1 (by rfl) ⟨478097, by rfl⟩ : syracuseStep 637463 = 956195) B956195
theorem B17789003 : Blo 374761 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B954443 : Blo 374761 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B847961 : Blo 374761 847961 := bstep (se 2 (by rfl) ⟨317985, by rfl⟩ : syracuseStep 847961 = 635971) B635971
theorem B6951005 : Blo 374761 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B2293379 : Blo 374761 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B815243 : Blo 374761 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B6942871 : Blo 374761 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B635033 : Blo 374761 635033 := bstep (se 2 (by rfl) ⟨238137, by rfl⟩ : syracuseStep 635033 = 476275) B476275
theorem B422059 : Blo 374761 422059 := bstep (se 1 (by rfl) ⟨316544, by rfl⟩ : syracuseStep 422059 = 633089) B633089
theorem B848051 : Blo 374761 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B1265867 : Blo 374761 1265867 := bstep (se 1 (by rfl) ⟨949400, by rfl⟩ : syracuseStep 1265867 = 1898801) B1898801
theorem B848087 : Blo 374761 848087 := bstep (se 1 (by rfl) ⟨636065, by rfl⟩ : syracuseStep 848087 = 1272131) B1272131
theorem B1429721 : Blo 374761 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B7737605 : Blo 374761 7737605 := bstep (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) B1450801
theorem B23892245 : Blo 374761 23892245 := bstep (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) B1119949
theorem B422167 : Blo 374761 422167 := bstep (se 1 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 422167 = 633251) B633251
theorem B635161 : Blo 374761 635161 := bstep (se 2 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 635161 = 476371) B476371
theorem B962891 : Blo 374761 962891 := bstep (se 1 (by rfl) ⟨722168, by rfl⟩ : syracuseStep 962891 = 1444337) B1444337
theorem B2289995 : Blo 374761 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1610077 : Blo 374761 1610077 := bstep (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) B603779
theorem B848267 : Blo 374761 848267 := bstep (se 1 (by rfl) ⟨636200, by rfl⟩ : syracuseStep 848267 = 1272401) B1272401
theorem B2863511 : Blo 374761 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B1429933 : Blo 374761 1429933 := bstep (se 3 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 1429933 = 536225) B536225
theorem B3912113 : Blo 374761 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B1274291 : Blo 374761 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B848321 : Blo 374761 848321 := bstep (se 2 (by rfl) ⟨318120, by rfl⟩ : syracuseStep 848321 = 636241) B636241
theorem B422347 : Blo 374761 422347 := bstep (se 1 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 422347 = 633521) B633521
theorem B1266137 : Blo 374761 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B422455 : Blo 374761 422455 := bstep (se 1 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 422455 = 633683) B633683
theorem B537239 : Blo 374761 537239 := bstep (se 1 (by rfl) ⟨402929, by rfl⟩ : syracuseStep 537239 = 805859) B805859
theorem B848537 : Blo 374761 848537 := bstep (se 2 (by rfl) ⟨318201, by rfl⟩ : syracuseStep 848537 = 636403) B636403
theorem B1274561 : Blo 374761 1274561 := bstep (se 2 (by rfl) ⟨477960, by rfl⟩ : syracuseStep 1274561 = 955921) B955921
theorem B1602251 : Blo 374761 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B5780173 : Blo 374761 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B1430237 : Blo 374761 1430237 := bstep (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) B536339
theorem B422635 : Blo 374761 422635 := bstep (se 1 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 422635 = 633953) B633953
theorem B848627 : Blo 374761 848627 := bstep (se 1 (by rfl) ⟨636470, by rfl⟩ : syracuseStep 848627 = 1272941) B1272941
theorem B5788421 : Blo 374761 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B848663 : Blo 374761 848663 := bstep (se 1 (by rfl) ⟨636497, by rfl⟩ : syracuseStep 848663 = 1272995) B1272995
theorem B725785 : Blo 374761 725785 := bstep (se 2 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 725785 = 544339) B544339
theorem B422743 : Blo 374761 422743 := bstep (se 1 (by rfl) ⟨317057, by rfl⟩ : syracuseStep 422743 = 634115) B634115
theorem B635735 : Blo 374761 635735 := bstep (se 1 (by rfl) ⟨476801, by rfl⟩ : syracuseStep 635735 = 953603) B953603
theorem B1651549 : Blo 374761 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B643979 : Blo 374761 643979 := bstep (se 1 (by rfl) ⟨482984, by rfl⟩ : syracuseStep 643979 = 965969) B965969
theorem B848843 : Blo 374761 848843 := bstep (se 1 (by rfl) ⟨636632, by rfl⟩ : syracuseStep 848843 = 1273265) B1273265
theorem B635863 : Blo 374761 635863 := bstep (se 1 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 635863 = 953795) B953795
theorem B848897 : Blo 374761 848897 := bstep (se 2 (by rfl) ⟨318336, by rfl⟩ : syracuseStep 848897 = 636673) B636673
theorem B562187 : Blo 374761 562187 := bstep (se 1 (by rfl) ⟨421640, by rfl⟩ : syracuseStep 562187 = 843281) B843281
theorem B857099 : Blo 374761 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B422923 : Blo 374761 422923 := bstep (se 1 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 422923 = 634385) B634385
theorem B562199 : Blo 374761 562199 := bstep (se 1 (by rfl) ⟨421649, by rfl⟩ : syracuseStep 562199 = 843299) B843299
theorem B955415 : Blo 374761 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B2135105 : Blo 374761 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B562265 : Blo 374761 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B423031 : Blo 374761 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B2946179 : Blo 374761 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1266839 : Blo 374761 1266839 := bstep (se 1 (by rfl) ⟨950129, by rfl⟩ : syracuseStep 1266839 = 1900259) B1900259
theorem B1201331 : Blo 374761 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B980147 : Blo 374761 980147 := bstep (se 1 (by rfl) ⟨735110, by rfl⟩ : syracuseStep 980147 = 1470221) B1470221
theorem B562379 : Blo 374761 562379 := bstep (se 1 (by rfl) ⟨421784, by rfl⟩ : syracuseStep 562379 = 843569) B843569
theorem B562391 : Blo 374761 562391 := bstep (se 1 (by rfl) ⟨421793, by rfl⟩ : syracuseStep 562391 = 843587) B843587
theorem B849113 : Blo 374761 849113 := bstep (se 2 (by rfl) ⟨318417, by rfl⟩ : syracuseStep 849113 = 636835) B636835
theorem B562457 : Blo 374761 562457 := bstep (se 2 (by rfl) ⟨210921, by rfl⟩ : syracuseStep 562457 = 421843) B421843
theorem B423211 : Blo 374761 423211 := bstep (se 1 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 423211 = 634817) B634817
theorem B849203 : Blo 374761 849203 := bstep (se 1 (by rfl) ⟨636902, by rfl⟩ : syracuseStep 849203 = 1273805) B1273805
theorem B1291571 : Blo 374761 1291571 := bstep (se 1 (by rfl) ⟨968678, by rfl⟩ : syracuseStep 1291571 = 1937357) B1937357
theorem B1201483 : Blo 374761 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B849239 : Blo 374761 849239 := bstep (se 1 (by rfl) ⟨636929, by rfl⟩ : syracuseStep 849239 = 1273859) B1273859
theorem B562571 : Blo 374761 562571 := bstep (se 1 (by rfl) ⟨421928, by rfl⟩ : syracuseStep 562571 = 843857) B843857
theorem B562583 : Blo 374761 562583 := bstep (se 1 (by rfl) ⟨421937, by rfl⟩ : syracuseStep 562583 = 843875) B843875
theorem B423319 : Blo 374761 423319 := bstep (se 1 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 423319 = 634979) B634979
theorem B677335 : Blo 374761 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B603607 : Blo 374761 603607 := bstep (se 1 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 603607 = 905411) B905411
theorem B562649 : Blo 374761 562649 := bstep (se 2 (by rfl) ⟨210993, by rfl⟩ : syracuseStep 562649 = 421987) B421987
theorem B849419 : Blo 374761 849419 := bstep (se 1 (by rfl) ⟨637064, by rfl⟩ : syracuseStep 849419 = 1274129) B1274129
theorem B3216941 : Blo 374761 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B849473 : Blo 374761 849473 := bstep (se 2 (by rfl) ⟨318552, by rfl⟩ : syracuseStep 849473 = 637105) B637105
theorem B562763 : Blo 374761 562763 := bstep (se 1 (by rfl) ⟨422072, by rfl⟩ : syracuseStep 562763 = 844145) B844145
theorem B423499 : Blo 374761 423499 := bstep (se 1 (by rfl) ⟨317624, by rfl⟩ : syracuseStep 423499 = 635249) B635249
theorem B636491 : Blo 374761 636491 := bstep (se 1 (by rfl) ⟨477368, by rfl⟩ : syracuseStep 636491 = 954737) B954737
theorem B5969483 : Blo 374761 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B562775 : Blo 374761 562775 := bstep (se 1 (by rfl) ⟨422081, by rfl⟩ : syracuseStep 562775 = 844163) B844163
theorem B1611409 : Blo 374761 1611409 := bstep (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) B1208557
theorem B562841 : Blo 374761 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B800435 : Blo 374761 800435 := bstep (se 1 (by rfl) ⟨600326, by rfl⟩ : syracuseStep 800435 = 1200653) B1200653
theorem B1267379 : Blo 374761 1267379 := bstep (se 1 (by rfl) ⟨950534, by rfl⟩ : syracuseStep 1267379 = 1901069) B1901069
theorem B423607 : Blo 374761 423607 := bstep (se 1 (by rfl) ⟨317705, by rfl⟩ : syracuseStep 423607 = 635411) B635411
theorem B956083 : Blo 374761 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B636619 : Blo 374761 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B603863 : Blo 374761 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B562955 : Blo 374761 562955 := bstep (se 1 (by rfl) ⟨422216, by rfl⟩ : syracuseStep 562955 = 844433) B844433
theorem B562967 : Blo 374761 562967 := bstep (se 1 (by rfl) ⟨422225, by rfl⟩ : syracuseStep 562967 = 844451) B844451
theorem B849689 : Blo 374761 849689 := bstep (se 2 (by rfl) ⟨318633, by rfl⟩ : syracuseStep 849689 = 637267) B637267
theorem B1201985 : Blo 374761 1201985 := bstep (se 2 (by rfl) ⟨450744, by rfl⟩ : syracuseStep 1201985 = 901489) B901489
theorem B1898315 : Blo 374761 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B1292107 : Blo 374761 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B563033 : Blo 374761 563033 := bstep (se 2 (by rfl) ⟨211137, by rfl⟩ : syracuseStep 563033 = 422275) B422275
theorem B636761 : Blo 374761 636761 := bstep (se 2 (by rfl) ⟨238785, by rfl⟩ : syracuseStep 636761 = 477571) B477571
theorem B423787 : Blo 374761 423787 := bstep (se 1 (by rfl) ⟨317840, by rfl⟩ : syracuseStep 423787 = 635681) B635681
theorem B849779 : Blo 374761 849779 := bstep (se 1 (by rfl) ⟨637334, by rfl⟩ : syracuseStep 849779 = 1274669) B1274669
theorem B849815 : Blo 374761 849815 := bstep (se 1 (by rfl) ⟨637361, by rfl⟩ : syracuseStep 849815 = 1274723) B1274723
theorem B1267649 : Blo 374761 1267649 := bstep (se 2 (by rfl) ⟨475368, by rfl⟩ : syracuseStep 1267649 = 950737) B950737
theorem B563147 : Blo 374761 563147 := bstep (se 1 (by rfl) ⟨422360, by rfl⟩ : syracuseStep 563147 = 844721) B844721
theorem B645067 : Blo 374761 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B563159 : Blo 374761 563159 := bstep (se 1 (by rfl) ⟨422369, by rfl⟩ : syracuseStep 563159 = 844739) B844739
theorem B423895 : Blo 374761 423895 := bstep (se 1 (by rfl) ⟨317921, by rfl⟩ : syracuseStep 423895 = 635843) B635843
theorem B636889 : Blo 374761 636889 := bstep (se 2 (by rfl) ⟨238833, by rfl⟩ : syracuseStep 636889 = 477667) B477667
theorem B374763 : Blo 374761 374763 := bstep (se 1 (by rfl) ⟨281072, by rfl⟩ : syracuseStep 374763 = 562145) B562145
theorem B374775 : Blo 374761 374775 := bstep (se 1 (by rfl) ⟨281081, by rfl⟩ : syracuseStep 374775 = 562163) B562163
theorem B374795 : Blo 374761 374795 := bstep (se 1 (by rfl) ⟨281096, by rfl⟩ : syracuseStep 374795 = 562193) B562193
theorem B571403 : Blo 374761 571403 := bstep (se 1 (by rfl) ⟨428552, by rfl⟩ : syracuseStep 571403 = 857105) B857105
theorem B374807 : Blo 374761 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B677911 : Blo 374761 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B563225 : Blo 374761 563225 := bstep (se 2 (by rfl) ⟨211209, by rfl⟩ : syracuseStep 563225 = 422419) B422419
theorem B374827 : Blo 374761 374827 := bstep (se 1 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 374827 = 562241) B562241
theorem B374839 : Blo 374761 374839 := bstep (se 1 (by rfl) ⟨281129, by rfl⟩ : syracuseStep 374839 = 562259) B562259
theorem B374859 : Blo 374761 374859 := bstep (se 1 (by rfl) ⟨281144, by rfl⟩ : syracuseStep 374859 = 562289) B562289
theorem B677963 : Blo 374761 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B374871 : Blo 374761 374871 := bstep (se 1 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 374871 = 562307) B562307
theorem B374891 : Blo 374761 374891 := bstep (se 1 (by rfl) ⟨281168, by rfl⟩ : syracuseStep 374891 = 562337) B562337
theorem B374903 : Blo 374761 374903 := bstep (se 1 (by rfl) ⟨281177, by rfl⟩ : syracuseStep 374903 = 562355) B562355
theorem B374923 : Blo 374761 374923 := bstep (se 1 (by rfl) ⟨281192, by rfl⟩ : syracuseStep 374923 = 562385) B562385
theorem B563339 : Blo 374761 563339 := bstep (se 1 (by rfl) ⟨422504, by rfl⟩ : syracuseStep 563339 = 845009) B845009
theorem B424075 : Blo 374761 424075 := bstep (se 1 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 424075 = 636113) B636113
theorem B374935 : Blo 374761 374935 := bstep (se 1 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 374935 = 562403) B562403
theorem B563351 : Blo 374761 563351 := bstep (se 1 (by rfl) ⟨422513, by rfl⟩ : syracuseStep 563351 = 845027) B845027
theorem B800921 : Blo 374761 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B374955 : Blo 374761 374955 := bstep (se 1 (by rfl) ⟨281216, by rfl⟩ : syracuseStep 374955 = 562433) B562433
theorem B2717873 : Blo 374761 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B2709683 : Blo 374761 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B374967 : Blo 374761 374967 := bstep (se 1 (by rfl) ⟨281225, by rfl⟩ : syracuseStep 374967 = 562451) B562451
theorem B374987 : Blo 374761 374987 := bstep (se 1 (by rfl) ⟨281240, by rfl⟩ : syracuseStep 374987 = 562481) B562481
theorem B374999 : Blo 374761 374999 := bstep (se 1 (by rfl) ⟨281249, by rfl⟩ : syracuseStep 374999 = 562499) B562499
theorem B563417 : Blo 374761 563417 := bstep (se 2 (by rfl) ⟨211281, by rfl⟩ : syracuseStep 563417 = 422563) B422563
theorem B375019 : Blo 374761 375019 := bstep (se 1 (by rfl) ⟨281264, by rfl⟩ : syracuseStep 375019 = 562529) B562529
theorem B375031 : Blo 374761 375031 := bstep (se 1 (by rfl) ⟨281273, by rfl⟩ : syracuseStep 375031 = 562547) B562547
theorem B424183 : Blo 374761 424183 := bstep (se 1 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 424183 = 636275) B636275
theorem B3045637 : Blo 374761 3045637 := bstep (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) B571057
theorem B375051 : Blo 374761 375051 := bstep (se 1 (by rfl) ⟨281288, by rfl⟩ : syracuseStep 375051 = 562577) B562577
theorem B375063 : Blo 374761 375063 := bstep (se 1 (by rfl) ⟨281297, by rfl⟩ : syracuseStep 375063 = 562595) B562595
theorem B375083 : Blo 374761 375083 := bstep (se 1 (by rfl) ⟨281312, by rfl⟩ : syracuseStep 375083 = 562625) B562625
theorem B1300787 : Blo 374761 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B1603891 : Blo 374761 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B375095 : Blo 374761 375095 := bstep (se 1 (by rfl) ⟨281321, by rfl⟩ : syracuseStep 375095 = 562643) B562643
theorem B907571 : Blo 374761 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B375115 : Blo 374761 375115 := bstep (se 1 (by rfl) ⟨281336, by rfl⟩ : syracuseStep 375115 = 562673) B562673
theorem B563531 : Blo 374761 563531 := bstep (se 1 (by rfl) ⟨422648, by rfl⟩ : syracuseStep 563531 = 845297) B845297
theorem B375127 : Blo 374761 375127 := bstep (se 1 (by rfl) ⟨281345, by rfl⟩ : syracuseStep 375127 = 562691) B562691
theorem B563543 : Blo 374761 563543 := bstep (se 1 (by rfl) ⟨422657, by rfl⟩ : syracuseStep 563543 = 845315) B845315
theorem B2677093 : Blo 374761 2677093 := bstep (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) B501955
theorem B375147 : Blo 374761 375147 := bstep (se 1 (by rfl) ⟨281360, by rfl⟩ : syracuseStep 375147 = 562721) B562721
theorem B375159 : Blo 374761 375159 := bstep (se 1 (by rfl) ⟨281369, by rfl⟩ : syracuseStep 375159 = 562739) B562739
theorem B375179 : Blo 374761 375179 := bstep (se 1 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 375179 = 562769) B562769
theorem B948631 : Blo 374761 948631 := bstep (se 1 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 948631 = 1422947) B1422947
theorem B375191 : Blo 374761 375191 := bstep (se 1 (by rfl) ⟨281393, by rfl⟩ : syracuseStep 375191 = 562787) B562787
theorem B563609 : Blo 374761 563609 := bstep (se 2 (by rfl) ⟨211353, by rfl⟩ : syracuseStep 563609 = 422707) B422707
theorem B375211 : Blo 374761 375211 := bstep (se 1 (by rfl) ⟨281408, by rfl⟩ : syracuseStep 375211 = 562817) B562817
theorem B424363 : Blo 374761 424363 := bstep (se 1 (by rfl) ⟨318272, by rfl⟩ : syracuseStep 424363 = 636545) B636545
theorem B1071539 : Blo 374761 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B375223 : Blo 374761 375223 := bstep (se 1 (by rfl) ⟨281417, by rfl⟩ : syracuseStep 375223 = 562835) B562835
theorem B375243 : Blo 374761 375243 := bstep (se 1 (by rfl) ⟨281432, by rfl⟩ : syracuseStep 375243 = 562865) B562865
theorem B375255 : Blo 374761 375255 := bstep (se 1 (by rfl) ⟨281441, by rfl⟩ : syracuseStep 375255 = 562883) B562883
theorem B1268189 : Blo 374761 1268189 := bstep (se 3 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 1268189 = 475571) B475571
theorem B375275 : Blo 374761 375275 := bstep (se 1 (by rfl) ⟨281456, by rfl⟩ : syracuseStep 375275 = 562913) B562913
theorem B375287 : Blo 374761 375287 := bstep (se 1 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 375287 = 562931) B562931
theorem B375307 : Blo 374761 375307 := bstep (se 1 (by rfl) ⟨281480, by rfl⟩ : syracuseStep 375307 = 562961) B562961
theorem B563723 : Blo 374761 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B1423889 : Blo 374761 1423889 := bstep (se 2 (by rfl) ⟨533958, by rfl⟩ : syracuseStep 1423889 = 1067917) B1067917
theorem B375319 : Blo 374761 375319 := bstep (se 1 (by rfl) ⟨281489, by rfl⟩ : syracuseStep 375319 = 562979) B562979
theorem B563735 : Blo 374761 563735 := bstep (se 1 (by rfl) ⟨422801, by rfl⟩ : syracuseStep 563735 = 845603) B845603
theorem B1546775 : Blo 374761 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B424471 : Blo 374761 424471 := bstep (se 1 (by rfl) ⟨318353, by rfl⟩ : syracuseStep 424471 = 636707) B636707
theorem B612887 : Blo 374761 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B375339 : Blo 374761 375339 := bstep (se 1 (by rfl) ⟨281504, by rfl⟩ : syracuseStep 375339 = 563009) B563009
theorem B1628723 : Blo 374761 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B375351 : Blo 374761 375351 := bstep (se 1 (by rfl) ⟨281513, by rfl⟩ : syracuseStep 375351 = 563027) B563027
theorem B375371 : Blo 374761 375371 := bstep (se 1 (by rfl) ⟨281528, by rfl⟩ : syracuseStep 375371 = 563057) B563057
theorem B4340299 : Blo 374761 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B375383 : Blo 374761 375383 := bstep (se 1 (by rfl) ⟨281537, by rfl⟩ : syracuseStep 375383 = 563075) B563075
theorem B563801 : Blo 374761 563801 := bstep (se 2 (by rfl) ⟨211425, by rfl⟩ : syracuseStep 563801 = 422851) B422851
theorem B375403 : Blo 374761 375403 := bstep (se 1 (by rfl) ⟨281552, by rfl⟩ : syracuseStep 375403 = 563105) B563105
theorem B375415 : Blo 374761 375415 := bstep (se 1 (by rfl) ⟨281561, by rfl⟩ : syracuseStep 375415 = 563123) B563123
theorem B375435 : Blo 374761 375435 := bstep (se 1 (by rfl) ⟨281576, by rfl⟩ : syracuseStep 375435 = 563153) B563153
theorem B375447 : Blo 374761 375447 := bstep (se 1 (by rfl) ⟨281585, by rfl⟩ : syracuseStep 375447 = 563171) B563171
theorem B457367 : Blo 374761 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B1071767 : Blo 374761 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B375467 : Blo 374761 375467 := bstep (se 1 (by rfl) ⟨281600, by rfl⟩ : syracuseStep 375467 = 563201) B563201
theorem B375479 : Blo 374761 375479 := bstep (se 1 (by rfl) ⟨281609, by rfl⟩ : syracuseStep 375479 = 563219) B563219
theorem B375499 : Blo 374761 375499 := bstep (se 1 (by rfl) ⟨281624, by rfl⟩ : syracuseStep 375499 = 563249) B563249
theorem B563915 : Blo 374761 563915 := bstep (se 1 (by rfl) ⟨422936, by rfl⟩ : syracuseStep 563915 = 845873) B845873
theorem B424651 : Blo 374761 424651 := bstep (se 1 (by rfl) ⟨318488, by rfl⟩ : syracuseStep 424651 = 636977) B636977
theorem B375511 : Blo 374761 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B563927 : Blo 374761 563927 := bstep (se 1 (by rfl) ⟨422945, by rfl⟩ : syracuseStep 563927 = 845891) B845891
theorem B375531 : Blo 374761 375531 := bstep (se 1 (by rfl) ⟨281648, by rfl⟩ : syracuseStep 375531 = 563297) B563297
theorem B375543 : Blo 374761 375543 := bstep (se 1 (by rfl) ⟨281657, by rfl⟩ : syracuseStep 375543 = 563315) B563315
theorem B375563 : Blo 374761 375563 := bstep (se 1 (by rfl) ⟨281672, by rfl⟩ : syracuseStep 375563 = 563345) B563345
theorem B375575 : Blo 374761 375575 := bstep (se 1 (by rfl) ⟨281681, by rfl⟩ : syracuseStep 375575 = 563363) B563363
theorem B563993 : Blo 374761 563993 := bstep (se 2 (by rfl) ⟨211497, by rfl⟩ : syracuseStep 563993 = 422995) B422995
theorem B375595 : Blo 374761 375595 := bstep (se 1 (by rfl) ⟨281696, by rfl⟩ : syracuseStep 375595 = 563393) B563393
theorem B375607 : Blo 374761 375607 := bstep (se 1 (by rfl) ⟨281705, by rfl⟩ : syracuseStep 375607 = 563411) B563411
theorem B424759 : Blo 374761 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B949067 : Blo 374761 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B375627 : Blo 374761 375627 := bstep (se 1 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 375627 = 563441) B563441
theorem B375639 : Blo 374761 375639 := bstep (se 1 (by rfl) ⟨281729, by rfl⟩ : syracuseStep 375639 = 563459) B563459
theorem B1907549 : Blo 374761 1907549 := bstep (se 3 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 1907549 = 715331) B715331
theorem B375659 : Blo 374761 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B375671 : Blo 374761 375671 := bstep (se 1 (by rfl) ⟨281753, by rfl⟩ : syracuseStep 375671 = 563507) B563507
theorem B375691 : Blo 374761 375691 := bstep (se 1 (by rfl) ⟨281768, by rfl⟩ : syracuseStep 375691 = 563537) B563537
theorem B564107 : Blo 374761 564107 := bstep (se 1 (by rfl) ⟨423080, by rfl⟩ : syracuseStep 564107 = 846161) B846161
theorem B736139 : Blo 374761 736139 := bstep (se 1 (by rfl) ⟨552104, by rfl⟩ : syracuseStep 736139 = 1104209) B1104209
theorem B375703 : Blo 374761 375703 := bstep (se 1 (by rfl) ⟨281777, by rfl⟩ : syracuseStep 375703 = 563555) B563555
theorem B564119 : Blo 374761 564119 := bstep (se 1 (by rfl) ⟨423089, by rfl⟩ : syracuseStep 564119 = 846179) B846179
theorem B375723 : Blo 374761 375723 := bstep (se 1 (by rfl) ⟨281792, by rfl⟩ : syracuseStep 375723 = 563585) B563585
theorem B375735 : Blo 374761 375735 := bstep (se 1 (by rfl) ⟨281801, by rfl⟩ : syracuseStep 375735 = 563603) B563603
theorem B760769 : Blo 374761 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B375755 : Blo 374761 375755 := bstep (se 1 (by rfl) ⟨281816, by rfl⟩ : syracuseStep 375755 = 563633) B563633
theorem B1072075 : Blo 374761 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B375767 : Blo 374761 375767 := bstep (se 1 (by rfl) ⟨281825, by rfl⟩ : syracuseStep 375767 = 563651) B563651
theorem B711641 : Blo 374761 711641 := bstep (se 2 (by rfl) ⟨266865, by rfl⟩ : syracuseStep 711641 = 533731) B533731
theorem B564185 : Blo 374761 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B375787 : Blo 374761 375787 := bstep (se 1 (by rfl) ⟨281840, by rfl⟩ : syracuseStep 375787 = 563681) B563681
theorem B375799 : Blo 374761 375799 := bstep (se 1 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 375799 = 563699) B563699
theorem B375819 : Blo 374761 375819 := bstep (se 1 (by rfl) ⟨281864, by rfl⟩ : syracuseStep 375819 = 563729) B563729
theorem B2579473 : Blo 374761 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B375831 : Blo 374761 375831 := bstep (se 1 (by rfl) ⟨281873, by rfl⟩ : syracuseStep 375831 = 563747) B563747
theorem B1375255 : Blo 374761 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B375851 : Blo 374761 375851 := bstep (se 1 (by rfl) ⟨281888, by rfl⟩ : syracuseStep 375851 = 563777) B563777
theorem B375863 : Blo 374761 375863 := bstep (se 1 (by rfl) ⟨281897, by rfl⟩ : syracuseStep 375863 = 563795) B563795
theorem B375883 : Blo 374761 375883 := bstep (se 1 (by rfl) ⟨281912, by rfl⟩ : syracuseStep 375883 = 563825) B563825
theorem B564299 : Blo 374761 564299 := bstep (se 1 (by rfl) ⟨423224, by rfl⟩ : syracuseStep 564299 = 846449) B846449
theorem B375895 : Blo 374761 375895 := bstep (se 1 (by rfl) ⟨281921, by rfl⟩ : syracuseStep 375895 = 563843) B563843
theorem B564311 : Blo 374761 564311 := bstep (se 1 (by rfl) ⟨423233, by rfl⟩ : syracuseStep 564311 = 846467) B846467
theorem B375915 : Blo 374761 375915 := bstep (se 1 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 375915 = 563873) B563873
theorem B375927 : Blo 374761 375927 := bstep (se 1 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 375927 = 563891) B563891
theorem B375947 : Blo 374761 375947 := bstep (se 1 (by rfl) ⟨281960, by rfl⟩ : syracuseStep 375947 = 563921) B563921
theorem B1358993 : Blo 374761 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B5856407 : Blo 374761 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B375959 : Blo 374761 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B564377 : Blo 374761 564377 := bstep (se 2 (by rfl) ⟨211641, by rfl⟩ : syracuseStep 564377 = 423283) B423283
theorem B375979 : Blo 374761 375979 := bstep (se 1 (by rfl) ⟨281984, by rfl⟩ : syracuseStep 375979 = 563969) B563969
theorem B377579 : Blo 374761 377579 := bstep (se 1 (by rfl) ⟨283184, by rfl⟩ : syracuseStep 377579 = 566369) B566369
theorem B375991 : Blo 374761 375991 := bstep (se 1 (by rfl) ⟨281993, by rfl⟩ : syracuseStep 375991 = 563987) B563987
theorem B949441 : Blo 374761 949441 := bstep (se 2 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 949441 = 712081) B712081
theorem B1629377 : Blo 374761 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B1424587 : Blo 374761 1424587 := bstep (se 1 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 1424587 = 2136881) B2136881
theorem B376011 : Blo 374761 376011 := bstep (se 1 (by rfl) ⟨282008, by rfl⟩ : syracuseStep 376011 = 564017) B564017
theorem B679115 : Blo 374761 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B376023 : Blo 374761 376023 := bstep (se 1 (by rfl) ⟨282017, by rfl⟩ : syracuseStep 376023 = 564035) B564035
theorem B1072349 : Blo 374761 1072349 := bstep (se 3 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 1072349 = 402131) B402131
theorem B376043 : Blo 374761 376043 := bstep (se 1 (by rfl) ⟨282032, by rfl⟩ : syracuseStep 376043 = 564065) B564065
theorem B400631 : Blo 374761 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B376055 : Blo 374761 376055 := bstep (se 1 (by rfl) ⟨282041, by rfl⟩ : syracuseStep 376055 = 564083) B564083
theorem B1432835 : Blo 374761 1432835 := bstep (se 1 (by rfl) ⟨1074626, by rfl⟩ : syracuseStep 1432835 = 2149253) B2149253
theorem B376075 : Blo 374761 376075 := bstep (se 1 (by rfl) ⟨282056, by rfl⟩ : syracuseStep 376075 = 564113) B564113
theorem B564491 : Blo 374761 564491 := bstep (se 1 (by rfl) ⟨423368, by rfl⟩ : syracuseStep 564491 = 846737) B846737
theorem B1432849 : Blo 374761 1432849 := bstep (se 2 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 1432849 = 1074637) B1074637
theorem B376087 : Blo 374761 376087 := bstep (se 1 (by rfl) ⟨282065, by rfl⟩ : syracuseStep 376087 = 564131) B564131
theorem B564503 : Blo 374761 564503 := bstep (se 1 (by rfl) ⟨423377, by rfl⟩ : syracuseStep 564503 = 846755) B846755
theorem B376107 : Blo 374761 376107 := bstep (se 1 (by rfl) ⟨282080, by rfl⟩ : syracuseStep 376107 = 564161) B564161
theorem B376119 : Blo 374761 376119 := bstep (se 1 (by rfl) ⟨282089, by rfl⟩ : syracuseStep 376119 = 564179) B564179
theorem B376139 : Blo 374761 376139 := bstep (se 1 (by rfl) ⟨282104, by rfl⟩ : syracuseStep 376139 = 564209) B564209
theorem B376151 : Blo 374761 376151 := bstep (se 1 (by rfl) ⟨282113, by rfl⟩ : syracuseStep 376151 = 564227) B564227
theorem B564569 : Blo 374761 564569 := bstep (se 2 (by rfl) ⟨211713, by rfl⟩ : syracuseStep 564569 = 423427) B423427
theorem B2145629 : Blo 374761 2145629 := bstep (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) B804611
theorem B376171 : Blo 374761 376171 := bstep (se 1 (by rfl) ⟨282128, by rfl⟩ : syracuseStep 376171 = 564257) B564257
theorem B376183 : Blo 374761 376183 := bstep (se 1 (by rfl) ⟨282137, by rfl⟩ : syracuseStep 376183 = 564275) B564275
theorem B376203 : Blo 374761 376203 := bstep (se 1 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 376203 = 564305) B564305
theorem B376215 : Blo 374761 376215 := bstep (se 1 (by rfl) ⟨282161, by rfl⟩ : syracuseStep 376215 = 564323) B564323
theorem B376235 : Blo 374761 376235 := bstep (se 1 (by rfl) ⟨282176, by rfl⟩ : syracuseStep 376235 = 564353) B564353
theorem B376247 : Blo 374761 376247 := bstep (se 1 (by rfl) ⟨282185, by rfl⟩ : syracuseStep 376247 = 564371) B564371
theorem B376267 : Blo 374761 376267 := bstep (se 1 (by rfl) ⟨282200, by rfl⟩ : syracuseStep 376267 = 564401) B564401
theorem B564683 : Blo 374761 564683 := bstep (se 1 (by rfl) ⟨423512, by rfl⟩ : syracuseStep 564683 = 847025) B847025
theorem B376279 : Blo 374761 376279 := bstep (se 1 (by rfl) ⟨282209, by rfl⟩ : syracuseStep 376279 = 564419) B564419
theorem B564695 : Blo 374761 564695 := bstep (se 1 (by rfl) ⟨423521, by rfl⟩ : syracuseStep 564695 = 847043) B847043
theorem B1932761 : Blo 374761 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1424861 : Blo 374761 1424861 := bstep (se 3 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 1424861 = 534323) B534323
theorem B376299 : Blo 374761 376299 := bstep (se 1 (by rfl) ⟨282224, by rfl⟩ : syracuseStep 376299 = 564449) B564449
theorem B376311 : Blo 374761 376311 := bstep (se 1 (by rfl) ⟨282233, by rfl⟩ : syracuseStep 376311 = 564467) B564467
theorem B376331 : Blo 374761 376331 := bstep (se 1 (by rfl) ⟨282248, by rfl⟩ : syracuseStep 376331 = 564497) B564497
theorem B376343 : Blo 374761 376343 := bstep (se 1 (by rfl) ⟨282257, by rfl⟩ : syracuseStep 376343 = 564515) B564515
theorem B564761 : Blo 374761 564761 := bstep (se 2 (by rfl) ⟨211785, by rfl⟩ : syracuseStep 564761 = 423571) B423571
theorem B376363 : Blo 374761 376363 := bstep (se 1 (by rfl) ⟨282272, by rfl⟩ : syracuseStep 376363 = 564545) B564545
theorem B376375 : Blo 374761 376375 := bstep (se 1 (by rfl) ⟨282281, by rfl⟩ : syracuseStep 376375 = 564563) B564563
theorem B1900097 : Blo 374761 1900097 := bstep (se 2 (by rfl) ⟨712536, by rfl⟩ : syracuseStep 1900097 = 1425073) B1425073
theorem B1433153 : Blo 374761 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B1269323 : Blo 374761 1269323 := bstep (se 1 (by rfl) ⟨951992, by rfl⟩ : syracuseStep 1269323 = 1903985) B1903985
theorem B376395 : Blo 374761 376395 := bstep (se 1 (by rfl) ⟨282296, by rfl⟩ : syracuseStep 376395 = 564593) B564593
theorem B376407 : Blo 374761 376407 := bstep (se 1 (by rfl) ⟨282305, by rfl⟩ : syracuseStep 376407 = 564611) B564611
theorem B843353 : Blo 374761 843353 := bstep (se 2 (by rfl) ⟨316257, by rfl⟩ : syracuseStep 843353 = 632515) B632515
theorem B376427 : Blo 374761 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B376439 : Blo 374761 376439 := bstep (se 1 (by rfl) ⟨282329, by rfl⟩ : syracuseStep 376439 = 564659) B564659
theorem B761483 : Blo 374761 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B376459 : Blo 374761 376459 := bstep (se 1 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 376459 = 564689) B564689
theorem B564875 : Blo 374761 564875 := bstep (se 1 (by rfl) ⟨423656, by rfl⟩ : syracuseStep 564875 = 847313) B847313
theorem B376471 : Blo 374761 376471 := bstep (se 1 (by rfl) ⟨282353, by rfl⟩ : syracuseStep 376471 = 564707) B564707
theorem B564887 : Blo 374761 564887 := bstep (se 1 (by rfl) ⟨423665, by rfl⟩ : syracuseStep 564887 = 847331) B847331
theorem B376491 : Blo 374761 376491 := bstep (se 1 (by rfl) ⟨282368, by rfl⟩ : syracuseStep 376491 = 564737) B564737
theorem B843443 : Blo 374761 843443 := bstep (se 1 (by rfl) ⟨632582, by rfl⟩ : syracuseStep 843443 = 1265165) B1265165
theorem B376503 : Blo 374761 376503 := bstep (se 1 (by rfl) ⟨282377, by rfl⟩ : syracuseStep 376503 = 564755) B564755
theorem B712385 : Blo 374761 712385 := bstep (se 2 (by rfl) ⟨267144, by rfl⟩ : syracuseStep 712385 = 534289) B534289
theorem B376523 : Blo 374761 376523 := bstep (se 1 (by rfl) ⟨282392, by rfl⟩ : syracuseStep 376523 = 564785) B564785
theorem B843479 : Blo 374761 843479 := bstep (se 1 (by rfl) ⟨632609, by rfl⟩ : syracuseStep 843479 = 1265219) B1265219
theorem B376535 : Blo 374761 376535 := bstep (se 1 (by rfl) ⟨282401, by rfl⟩ : syracuseStep 376535 = 564803) B564803
theorem B564953 : Blo 374761 564953 := bstep (se 2 (by rfl) ⟨211857, by rfl⟩ : syracuseStep 564953 = 423715) B423715
theorem B376555 : Blo 374761 376555 := bstep (se 1 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 376555 = 564833) B564833
theorem B376567 : Blo 374761 376567 := bstep (se 1 (by rfl) ⟨282425, by rfl⟩ : syracuseStep 376567 = 564851) B564851
theorem B802561 : Blo 374761 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B1605379 : Blo 374761 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B376587 : Blo 374761 376587 := bstep (se 1 (by rfl) ⟨282440, by rfl⟩ : syracuseStep 376587 = 564881) B564881
theorem B950039 : Blo 374761 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B376599 : Blo 374761 376599 := bstep (se 1 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 376599 = 564899) B564899
theorem B376619 : Blo 374761 376619 := bstep (se 1 (by rfl) ⟨282464, by rfl⟩ : syracuseStep 376619 = 564929) B564929
theorem B3202861 : Blo 374761 3202861 := bstep (se 3 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 3202861 = 1201073) B1201073
theorem B376631 : Blo 374761 376631 := bstep (se 1 (by rfl) ⟨282473, by rfl⟩ : syracuseStep 376631 = 564947) B564947
theorem B376651 : Blo 374761 376651 := bstep (se 1 (by rfl) ⟨282488, by rfl⟩ : syracuseStep 376651 = 564977) B564977
theorem B565067 : Blo 374761 565067 := bstep (se 1 (by rfl) ⟨423800, by rfl⟩ : syracuseStep 565067 = 847601) B847601
theorem B376663 : Blo 374761 376663 := bstep (se 1 (by rfl) ⟨282497, by rfl⟩ : syracuseStep 376663 = 564995) B564995
theorem B565079 : Blo 374761 565079 := bstep (se 1 (by rfl) ⟨423809, by rfl⟩ : syracuseStep 565079 = 847619) B847619
theorem B1269593 : Blo 374761 1269593 := bstep (se 2 (by rfl) ⟨476097, by rfl⟩ : syracuseStep 1269593 = 952195) B952195
theorem B3628901 : Blo 374761 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B376683 : Blo 374761 376683 := bstep (se 1 (by rfl) ⟨282512, by rfl⟩ : syracuseStep 376683 = 565025) B565025
theorem B376695 : Blo 374761 376695 := bstep (se 1 (by rfl) ⟨282521, by rfl⟩ : syracuseStep 376695 = 565043) B565043
theorem B424939 : Blo 374761 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B843659 : Blo 374761 843659 := bstep (se 1 (by rfl) ⟨632744, by rfl⟩ : syracuseStep 843659 = 1265489) B1265489
theorem B376715 : Blo 374761 376715 := bstep (se 1 (by rfl) ⟨282536, by rfl⟩ : syracuseStep 376715 = 565073) B565073
theorem B376727 : Blo 374761 376727 := bstep (se 1 (by rfl) ⟨282545, by rfl⟩ : syracuseStep 376727 = 565091) B565091
theorem B565145 : Blo 374761 565145 := bstep (se 2 (by rfl) ⟨211929, by rfl⟩ : syracuseStep 565145 = 423859) B423859
theorem B376747 : Blo 374761 376747 := bstep (se 1 (by rfl) ⟨282560, by rfl⟩ : syracuseStep 376747 = 565121) B565121
theorem B376759 : Blo 374761 376759 := bstep (se 1 (by rfl) ⟨282569, by rfl⟩ : syracuseStep 376759 = 565139) B565139
theorem B843713 : Blo 374761 843713 := bstep (se 2 (by rfl) ⟨316392, by rfl⟩ : syracuseStep 843713 = 632785) B632785
theorem B712651 : Blo 374761 712651 := bstep (se 1 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 712651 = 1068977) B1068977
theorem B376779 : Blo 374761 376779 := bstep (se 1 (by rfl) ⟨282584, by rfl⟩ : syracuseStep 376779 = 565169) B565169
theorem B376791 : Blo 374761 376791 := bstep (se 1 (by rfl) ⟨282593, by rfl⟩ : syracuseStep 376791 = 565187) B565187
theorem B376811 : Blo 374761 376811 := bstep (se 1 (by rfl) ⟨282608, by rfl⟩ : syracuseStep 376811 = 565217) B565217
theorem B376839 : Blo 374761 376839 := bstep (se 1 (by rfl) ⟨282629, by rfl⟩ : syracuseStep 376839 = 565259) B565259
theorem B376847 : Blo 374761 376847 := bstep (se 1 (by rfl) ⟨282635, by rfl⟩ : syracuseStep 376847 = 565271) B565271
theorem B2285597 : Blo 374761 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1523741 : Blo 374761 1523741 := bstep (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) B571403
theorem B565307 : Blo 374761 565307 := bstep (se 1 (by rfl) ⟨423980, by rfl⟩ : syracuseStep 565307 = 847961) B847961
theorem B376891 : Blo 374761 376891 := bstep (se 1 (by rfl) ⟨282668, by rfl⟩ : syracuseStep 376891 = 565337) B565337
theorem B2719831 : Blo 374761 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B565367 : Blo 374761 565367 := bstep (se 1 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 565367 = 848051) B848051
theorem B843911 : Blo 374761 843911 := bstep (se 1 (by rfl) ⟨632933, by rfl⟩ : syracuseStep 843911 = 1265867) B1265867
theorem B376967 : Blo 374761 376967 := bstep (se 1 (by rfl) ⟨282725, by rfl⟩ : syracuseStep 376967 = 565451) B565451
theorem B565391 : Blo 374761 565391 := bstep (se 1 (by rfl) ⟨424043, by rfl⟩ : syracuseStep 565391 = 848087) B848087
theorem B376975 : Blo 374761 376975 := bstep (se 1 (by rfl) ⟨282731, by rfl⟩ : syracuseStep 376975 = 565463) B565463
theorem B802963 : Blo 374761 802963 := bstep (se 1 (by rfl) ⟨602222, by rfl⟩ : syracuseStep 802963 = 1204445) B1204445
theorem B565433 : Blo 374761 565433 := bstep (se 2 (by rfl) ⟨212037, by rfl⟩ : syracuseStep 565433 = 424075) B424075
theorem B377019 : Blo 374761 377019 := bstep (se 1 (by rfl) ⟨282764, by rfl⟩ : syracuseStep 377019 = 565529) B565529
theorem B9257161 : Blo 374761 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B1900745 : Blo 374761 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B475399 : Blo 374761 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B565511 : Blo 374761 565511 := bstep (se 1 (by rfl) ⟨424133, by rfl⟩ : syracuseStep 565511 = 848267) B848267
theorem B377095 : Blo 374761 377095 := bstep (se 1 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 377095 = 565643) B565643
theorem B1909007 : Blo 374761 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B377103 : Blo 374761 377103 := bstep (se 1 (by rfl) ⟨282827, by rfl⟩ : syracuseStep 377103 = 565655) B565655
theorem B565547 : Blo 374761 565547 := bstep (se 1 (by rfl) ⟨424160, by rfl⟩ : syracuseStep 565547 = 848321) B848321
theorem B844091 : Blo 374761 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B377147 : Blo 374761 377147 := bstep (se 1 (by rfl) ⟨282860, by rfl⟩ : syracuseStep 377147 = 565721) B565721
theorem B565577 : Blo 374761 565577 := bstep (se 2 (by rfl) ⟨212091, by rfl⟩ : syracuseStep 565577 = 424183) B424183
theorem B377223 : Blo 374761 377223 := bstep (se 1 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 377223 = 565835) B565835
theorem B377231 : Blo 374761 377231 := bstep (se 1 (by rfl) ⟨282923, by rfl⟩ : syracuseStep 377231 = 565847) B565847
theorem B5439889 : Blo 374761 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B2138521 : Blo 374761 2138521 := bstep (se 2 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 2138521 = 1603891) B1603891
theorem B844217 : Blo 374761 844217 := bstep (se 2 (by rfl) ⟨316581, by rfl⟩ : syracuseStep 844217 = 633163) B633163
theorem B565691 : Blo 374761 565691 := bstep (se 1 (by rfl) ⟨424268, by rfl⟩ : syracuseStep 565691 = 848537) B848537
theorem B377275 : Blo 374761 377275 := bstep (se 1 (by rfl) ⟨282956, by rfl⟩ : syracuseStep 377275 = 565913) B565913
theorem B2146769 : Blo 374761 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B565751 : Blo 374761 565751 := bstep (se 1 (by rfl) ⟨424313, by rfl⟩ : syracuseStep 565751 = 848627) B848627
theorem B3858947 : Blo 374761 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B377351 : Blo 374761 377351 := bstep (se 1 (by rfl) ⟨283013, by rfl⟩ : syracuseStep 377351 = 566027) B566027
theorem B565775 : Blo 374761 565775 := bstep (se 1 (by rfl) ⟨424331, by rfl⟩ : syracuseStep 565775 = 848663) B848663
theorem B377359 : Blo 374761 377359 := bstep (se 1 (by rfl) ⟨283019, by rfl⟩ : syracuseStep 377359 = 566039) B566039
theorem B15483413 : Blo 374761 15483413 := bstep (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) B725785
theorem B1810973 : Blo 374761 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B565817 : Blo 374761 565817 := bstep (se 2 (by rfl) ⟨212181, by rfl⟩ : syracuseStep 565817 = 424363) B424363
theorem B377403 : Blo 374761 377403 := bstep (se 1 (by rfl) ⟨283052, by rfl⟩ : syracuseStep 377403 = 566105) B566105
theorem B950899 : Blo 374761 950899 := bstep (se 1 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 950899 = 1426349) B1426349
theorem B565895 : Blo 374761 565895 := bstep (se 1 (by rfl) ⟨424421, by rfl⟩ : syracuseStep 565895 = 848843) B848843
theorem B377479 : Blo 374761 377479 := bstep (se 1 (by rfl) ⟨283109, by rfl⟩ : syracuseStep 377479 = 566219) B566219
theorem B377487 : Blo 374761 377487 := bstep (se 1 (by rfl) ⟨283115, by rfl⟩ : syracuseStep 377487 = 566231) B566231
theorem B565931 : Blo 374761 565931 := bstep (se 1 (by rfl) ⟨424448, by rfl⟩ : syracuseStep 565931 = 848897) B848897
theorem B377531 : Blo 374761 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B680737 : Blo 374761 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B565961 : Blo 374761 565961 := bstep (se 2 (by rfl) ⟨212235, by rfl⟩ : syracuseStep 565961 = 424471) B424471
theorem B475895 : Blo 374761 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B951041 : Blo 374761 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B377607 : Blo 374761 377607 := bstep (se 1 (by rfl) ⟨283205, by rfl⟩ : syracuseStep 377607 = 566411) B566411
theorem B844559 : Blo 374761 844559 := bstep (se 1 (by rfl) ⟨633419, by rfl⟩ : syracuseStep 844559 = 1266839) B1266839
theorem B2147087 : Blo 374761 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B377615 : Blo 374761 377615 := bstep (se 1 (by rfl) ⟨283211, by rfl⟩ : syracuseStep 377615 = 566423) B566423
theorem B844577 : Blo 374761 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B566075 : Blo 374761 566075 := bstep (se 1 (by rfl) ⟨424556, by rfl⟩ : syracuseStep 566075 = 849113) B849113
theorem B377659 : Blo 374761 377659 := bstep (se 1 (by rfl) ⟨283244, by rfl⟩ : syracuseStep 377659 = 566489) B566489
theorem B566135 : Blo 374761 566135 := bstep (se 1 (by rfl) ⟨424601, by rfl⟩ : syracuseStep 566135 = 849203) B849203
theorem B861047 : Blo 374761 861047 := bstep (se 1 (by rfl) ⟨645785, by rfl⟩ : syracuseStep 861047 = 1291571) B1291571
theorem B377735 : Blo 374761 377735 := bstep (se 1 (by rfl) ⟨283301, by rfl⟩ : syracuseStep 377735 = 566603) B566603
theorem B476047 : Blo 374761 476047 := bstep (se 1 (by rfl) ⟨357035, by rfl⟩ : syracuseStep 476047 = 714071) B714071
theorem B566159 : Blo 374761 566159 := bstep (se 1 (by rfl) ⟨424619, by rfl⟩ : syracuseStep 566159 = 849239) B849239
theorem B902035 : Blo 374761 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B377743 : Blo 374761 377743 := bstep (se 1 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 377743 = 566615) B566615
theorem B566201 : Blo 374761 566201 := bstep (se 2 (by rfl) ⟨212325, by rfl⟩ : syracuseStep 566201 = 424651) B424651
theorem B566279 : Blo 374761 566279 := bstep (se 1 (by rfl) ⟨424709, by rfl⟩ : syracuseStep 566279 = 849419) B849419
theorem B566315 : Blo 374761 566315 := bstep (se 1 (by rfl) ⟨424736, by rfl⟩ : syracuseStep 566315 = 849473) B849473
theorem B476219 : Blo 374761 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B566345 : Blo 374761 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B533623 : Blo 374761 533623 := bstep (se 1 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 533623 = 800435) B800435
theorem B844919 : Blo 374761 844919 := bstep (se 1 (by rfl) ⟨633689, by rfl⟩ : syracuseStep 844919 = 1267379) B1267379
theorem B402575 : Blo 374761 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B566459 : Blo 374761 566459 := bstep (se 1 (by rfl) ⟨424844, by rfl⟩ : syracuseStep 566459 = 849689) B849689
theorem B951497 : Blo 374761 951497 := bstep (se 2 (by rfl) ⟨356811, by rfl⟩ : syracuseStep 951497 = 713623) B713623
theorem B2409709 : Blo 374761 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B5154029 : Blo 374761 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B566519 : Blo 374761 566519 := bstep (se 1 (by rfl) ⟨424889, by rfl⟩ : syracuseStep 566519 = 849779) B849779
theorem B566543 : Blo 374761 566543 := bstep (se 1 (by rfl) ⟨424907, by rfl⟩ : syracuseStep 566543 = 849815) B849815
theorem B845099 : Blo 374761 845099 := bstep (se 1 (by rfl) ⟨633824, by rfl⟩ : syracuseStep 845099 = 1267649) B1267649
theorem B566585 : Blo 374761 566585 := bstep (se 2 (by rfl) ⟨212469, by rfl⟩ : syracuseStep 566585 = 424939) B424939
theorem B451975 : Blo 374761 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B1426835 : Blo 374761 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B533947 : Blo 374761 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B1017289 : Blo 374761 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B1811915 : Blo 374761 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B951851 : Blo 374761 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B714359 : Blo 374761 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B845459 : Blo 374761 845459 := bstep (se 1 (by rfl) ⟨634094, by rfl⟩ : syracuseStep 845459 = 1268189) B1268189
theorem B1910465 : Blo 374761 1910465 := bstep (se 2 (by rfl) ⟨716424, by rfl⟩ : syracuseStep 1910465 = 1432849) B1432849
theorem B845513 : Blo 374761 845513 := bstep (se 2 (by rfl) ⟨317067, by rfl⟩ : syracuseStep 845513 = 634135) B634135
theorem B6407909 : Blo 374761 6407909 := bstep (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) B1201483
theorem B714511 : Blo 374761 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B3860261 : Blo 374761 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B632711 : Blo 374761 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B1271699 : Blo 374761 1271699 := bstep (se 1 (by rfl) ⟨953774, by rfl⟩ : syracuseStep 1271699 = 1907549) B1907549
theorem B903113 : Blo 374761 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B804809 : Blo 374761 804809 := bstep (se 2 (by rfl) ⟨301803, by rfl⟩ : syracuseStep 804809 = 603607) B603607
theorem B477191 : Blo 374761 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B3049559 : Blo 374761 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B714899 : Blo 374761 714899 := bstep (se 1 (by rfl) ⟨536174, by rfl⟩ : syracuseStep 714899 = 1072349) B1072349
theorem B2148545 : Blo 374761 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B8167625 : Blo 374761 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B1075457 : Blo 374761 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B6416657 : Blo 374761 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B5507345 : Blo 374761 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B2140505 : Blo 374761 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B846215 : Blo 374761 846215 := bstep (se 1 (by rfl) ⟨634661, by rfl⟩ : syracuseStep 846215 = 1269323) B1269323
theorem B4270481 : Blo 374761 4270481 := bstep (se 2 (by rfl) ⟨1601430, by rfl⟩ : syracuseStep 4270481 = 3202861) B3202861
theorem B2853305 : Blo 374761 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B1722809 : Blo 374761 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B6089201 : Blo 374761 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B952843 : Blo 374761 952843 := bstep (se 1 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 952843 = 1429265) B1429265
theorem B633359 : Blo 374761 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B846395 : Blo 374761 846395 := bstep (se 1 (by rfl) ⟨634796, by rfl⟩ : syracuseStep 846395 = 1269593) B1269593
theorem B2419267 : Blo 374761 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B477839 : Blo 374761 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B952985 : Blo 374761 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B846521 : Blo 374761 846521 := bstep (se 2 (by rfl) ⟨317445, by rfl⟩ : syracuseStep 846521 = 634891) B634891
theorem B903881 : Blo 374761 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B5434127 : Blo 374761 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B953147 : Blo 374761 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B15928163 : Blo 374761 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B641927 : Blo 374761 641927 := bstep (se 1 (by rfl) ⟨481445, by rfl⟩ : syracuseStep 641927 = 962891) B962891
theorem B1526663 : Blo 374761 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B2608075 : Blo 374761 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B1911761 : Blo 374761 1911761 := bstep (se 2 (by rfl) ⟨716910, by rfl⟩ : syracuseStep 1911761 = 1433821) B1433821
theorem B846863 : Blo 374761 846863 := bstep (se 1 (by rfl) ⟨635147, by rfl⟩ : syracuseStep 846863 = 1270295) B1270295
theorem B2173981 : Blo 374761 2173981 := bstep (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) B815243
theorem B846881 : Blo 374761 846881 := bstep (se 2 (by rfl) ⟨317580, by rfl⟩ : syracuseStep 846881 = 635161) B635161
theorem B633899 : Blo 374761 633899 := bstep (se 1 (by rfl) ⟨475424, by rfl⟩ : syracuseStep 633899 = 950849) B950849
theorem B1240183 : Blo 374761 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B1068167 : Blo 374761 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B953491 : Blo 374761 953491 := bstep (se 1 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 953491 = 1430237) B1430237
theorem B1264841 : Blo 374761 1264841 := bstep (se 2 (by rfl) ⟨474315, by rfl⟩ : syracuseStep 1264841 = 948631) B948631
theorem B429319 : Blo 374761 429319 := bstep (se 1 (by rfl) ⟨321989, by rfl⟩ : syracuseStep 429319 = 643979) B643979
theorem B1273103 : Blo 374761 1273103 := bstep (se 1 (by rfl) ⟨954827, by rfl⟩ : syracuseStep 1273103 = 1909655) B1909655
theorem B953633 : Blo 374761 953633 := bstep (se 2 (by rfl) ⟨357612, by rfl⟩ : syracuseStep 953633 = 715225) B715225
theorem B4566365 : Blo 374761 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B847223 : Blo 374761 847223 := bstep (se 1 (by rfl) ⟨635417, by rfl⟩ : syracuseStep 847223 = 1270835) B1270835
theorem B634297 : Blo 374761 634297 := bstep (se 2 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 634297 = 475723) B475723
theorem B5787065 : Blo 374761 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B2420189 : Blo 374761 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B716303 : Blo 374761 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B1273373 : Blo 374761 1273373 := bstep (se 3 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 1273373 = 477515) B477515
theorem B847403 : Blo 374761 847403 := bstep (se 1 (by rfl) ⟨635552, by rfl⟩ : syracuseStep 847403 = 1271105) B1271105
theorem B46157525 : Blo 374761 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B536311 : Blo 374761 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B1027873 : Blo 374761 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B2846501 : Blo 374761 2846501 := bstep (se 4 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 2846501 = 533719) B533719
theorem B1265543 : Blo 374761 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B847763 : Blo 374761 847763 := bstep (se 1 (by rfl) ⟨635822, by rfl⟩ : syracuseStep 847763 = 1271645) B1271645
theorem B1429433 : Blo 374761 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B847817 : Blo 374761 847817 := bstep (se 2 (by rfl) ⟨317931, by rfl⟩ : syracuseStep 847817 = 635863) B635863
theorem B716843 : Blo 374761 716843 := bstep (se 1 (by rfl) ⟨537632, by rfl⟩ : syracuseStep 716843 = 1075265) B1075265
theorem B536635 : Blo 374761 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B2715709 : Blo 374761 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B1634365 : Blo 374761 1634365 := bstep (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) B612887
theorem B1601603 : Blo 374761 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B1806455 : Blo 374761 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B733303 : Blo 374761 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B634999 : Blo 374761 634999 := bstep (se 1 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 634999 = 952499) B952499
theorem B422023 : Blo 374761 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B545015 : Blo 374761 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B1265921 : Blo 374761 1265921 := bstep (se 2 (by rfl) ⟨474720, by rfl⟩ : syracuseStep 1265921 = 949441) B949441
theorem B954625 : Blo 374761 954625 := bstep (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) B715969
theorem B422203 : Blo 374761 422203 := bstep (se 1 (by rfl) ⟨316652, by rfl⟩ : syracuseStep 422203 = 633305) B633305
theorem B635195 : Blo 374761 635195 := bstep (se 1 (by rfl) ⟨476396, by rfl⟩ : syracuseStep 635195 = 952793) B952793
theorem B1085815 : Blo 374761 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B487951 : Blo 374761 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B59609621 : Blo 374761 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B537131 : Blo 374761 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B848519 : Blo 374761 848519 := bstep (se 1 (by rfl) ⟨636389, by rfl⟩ : syracuseStep 848519 = 1272779) B1272779
theorem B635593 : Blo 374761 635593 := bstep (se 2 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 635593 = 476695) B476695
theorem B905995 : Blo 374761 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B3904271 : Blo 374761 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B4567823 : Blo 374761 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B422671 : Blo 374761 422671 := bstep (se 1 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 422671 = 634007) B634007
theorem B1086251 : Blo 374761 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B848699 : Blo 374761 848699 := bstep (se 1 (by rfl) ⟨636524, by rfl⟩ : syracuseStep 848699 = 1273049) B1273049
theorem B955223 : Blo 374761 955223 := bstep (se 1 (by rfl) ⟨716417, by rfl⟩ : syracuseStep 955223 = 1432835) B1432835
theorem B1356659 : Blo 374761 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B1430419 : Blo 374761 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B1274777 : Blo 374761 1274777 := bstep (se 2 (by rfl) ⟨478041, by rfl⟩ : syracuseStep 1274777 = 956083) B956083
theorem B848825 : Blo 374761 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B1070081 : Blo 374761 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B4813829 : Blo 374761 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B4568075 : Blo 374761 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B1266731 : Blo 374761 1266731 := bstep (se 1 (by rfl) ⟨950048, by rfl⟩ : syracuseStep 1266731 = 1900097) B1900097
theorem B955435 : Blo 374761 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B562235 : Blo 374761 562235 := bstep (se 1 (by rfl) ⟨421676, by rfl⟩ : syracuseStep 562235 = 843353) B843353
theorem B1528919 : Blo 374761 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B562295 : Blo 374761 562295 := bstep (se 1 (by rfl) ⟨421721, by rfl⟩ : syracuseStep 562295 = 843443) B843443
theorem B562319 : Blo 374761 562319 := bstep (se 1 (by rfl) ⟨421739, by rfl⟩ : syracuseStep 562319 = 843479) B843479
theorem B562361 : Blo 374761 562361 := bstep (se 2 (by rfl) ⟨210885, by rfl⟩ : syracuseStep 562361 = 421771) B421771
theorem B955577 : Blo 374761 955577 := bstep (se 2 (by rfl) ⟨358341, by rfl⟩ : syracuseStep 955577 = 716683) B716683
theorem B3421385 : Blo 374761 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B4273397 : Blo 374761 4273397 := bstep (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) B400631
theorem B562439 : Blo 374761 562439 := bstep (se 1 (by rfl) ⟨421829, by rfl⟩ : syracuseStep 562439 = 843659) B843659
theorem B423175 : Blo 374761 423175 := bstep (se 1 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 423175 = 634763) B634763
theorem B603407 : Blo 374761 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B849167 : Blo 374761 849167 := bstep (se 1 (by rfl) ⟨636875, by rfl⟩ : syracuseStep 849167 = 1273751) B1273751
theorem B849185 : Blo 374761 849185 := bstep (se 2 (by rfl) ⟨318444, by rfl⟩ : syracuseStep 849185 = 636889) B636889
theorem B562475 : Blo 374761 562475 := bstep (se 1 (by rfl) ⟨421856, by rfl⟩ : syracuseStep 562475 = 843713) B843713
theorem B562505 : Blo 374761 562505 := bstep (se 2 (by rfl) ⟨210939, by rfl⟩ : syracuseStep 562505 = 421879) B421879
theorem B11859335 : Blo 374761 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B636295 : Blo 374761 636295 := bstep (se 1 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 636295 = 954443) B954443
theorem B4634003 : Blo 374761 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B562619 : Blo 374761 562619 := bstep (se 1 (by rfl) ⟨421964, by rfl⟩ : syracuseStep 562619 = 843929) B843929
theorem B423355 : Blo 374761 423355 := bstep (se 1 (by rfl) ⟨317516, by rfl⟩ : syracuseStep 423355 = 635033) B635033
theorem B562679 : Blo 374761 562679 := bstep (se 1 (by rfl) ⟨422009, by rfl⟩ : syracuseStep 562679 = 844019) B844019
theorem B5158403 : Blo 374761 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B562703 : Blo 374761 562703 := bstep (se 1 (by rfl) ⟨422027, by rfl⟩ : syracuseStep 562703 = 844055) B844055
theorem B1807915 : Blo 374761 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B562745 : Blo 374761 562745 := bstep (se 2 (by rfl) ⟨211029, by rfl⟩ : syracuseStep 562745 = 422059) B422059
theorem B1070651 : Blo 374761 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B1209917 : Blo 374761 1209917 := bstep (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) B453719
theorem B1709687 : Blo 374761 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B906871 : Blo 374761 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B849527 : Blo 374761 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B562823 : Blo 374761 562823 := bstep (se 1 (by rfl) ⟨422117, by rfl⟩ : syracuseStep 562823 = 844235) B844235
theorem B562859 : Blo 374761 562859 := bstep (se 1 (by rfl) ⟨422144, by rfl⟩ : syracuseStep 562859 = 844289) B844289
theorem B4060849 : Blo 374761 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B382651 : Blo 374761 382651 := bstep (se 1 (by rfl) ⟨286988, by rfl⟩ : syracuseStep 382651 = 573977) B573977
theorem B2905793 : Blo 374761 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B562889 : Blo 374761 562889 := bstep (se 2 (by rfl) ⟨211083, by rfl⟩ : syracuseStep 562889 = 422167) B422167
theorem B2406145 : Blo 374761 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B800545 : Blo 374761 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B1070891 : Blo 374761 1070891 := bstep (se 1 (by rfl) ⟨803168, by rfl⟩ : syracuseStep 1070891 = 1606337) B1606337
theorem B849707 : Blo 374761 849707 := bstep (se 1 (by rfl) ⟨637280, by rfl⟩ : syracuseStep 849707 = 1274561) B1274561
theorem B563003 : Blo 374761 563003 := bstep (se 1 (by rfl) ⟨422252, by rfl⟩ : syracuseStep 563003 = 844505) B844505
theorem B1087291 : Blo 374761 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B4560715 : Blo 374761 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B563063 : Blo 374761 563063 := bstep (se 1 (by rfl) ⟨422297, by rfl⟩ : syracuseStep 563063 = 844595) B844595
theorem B563087 : Blo 374761 563087 := bstep (se 1 (by rfl) ⟨422315, by rfl⟩ : syracuseStep 563087 = 844631) B844631
theorem B423823 : Blo 374761 423823 := bstep (se 1 (by rfl) ⟨317867, by rfl⟩ : syracuseStep 423823 = 635735) B635735
theorem B1906577 : Blo 374761 1906577 := bstep (se 2 (by rfl) ⟨714966, by rfl⟩ : syracuseStep 1906577 = 1429933) B1429933
theorem B563129 : Blo 374761 563129 := bstep (se 2 (by rfl) ⟨211173, by rfl⟩ : syracuseStep 563129 = 422347) B422347
theorem B5478347 : Blo 374761 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B374791 : Blo 374761 374791 := bstep (se 1 (by rfl) ⟨281093, by rfl⟩ : syracuseStep 374791 = 562187) B562187
theorem B563207 : Blo 374761 563207 := bstep (se 1 (by rfl) ⟨422405, by rfl⟩ : syracuseStep 563207 = 844811) B844811
theorem B374799 : Blo 374761 374799 := bstep (se 1 (by rfl) ⟨281099, by rfl⟩ : syracuseStep 374799 = 562199) B562199
theorem B858127 : Blo 374761 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B636943 : Blo 374761 636943 := bstep (se 1 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 636943 = 955415) B955415
theorem B1423403 : Blo 374761 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B563243 : Blo 374761 563243 := bstep (se 1 (by rfl) ⟨422432, by rfl⟩ : syracuseStep 563243 = 844865) B844865
theorem B374843 : Blo 374761 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B2136131 : Blo 374761 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B563273 : Blo 374761 563273 := bstep (se 2 (by rfl) ⟨211227, by rfl⟩ : syracuseStep 563273 = 422455) B422455
theorem B1964119 : Blo 374761 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B800887 : Blo 374761 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B653431 : Blo 374761 653431 := bstep (se 1 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 653431 = 980147) B980147
theorem B374919 : Blo 374761 374919 := bstep (se 1 (by rfl) ⟨281189, by rfl⟩ : syracuseStep 374919 = 562379) B562379
theorem B374927 : Blo 374761 374927 := bstep (se 1 (by rfl) ⟨281195, by rfl⟩ : syracuseStep 374927 = 562391) B562391
theorem B374971 : Blo 374761 374971 := bstep (se 1 (by rfl) ⟨281228, by rfl⟩ : syracuseStep 374971 = 562457) B562457
theorem B563387 : Blo 374761 563387 := bstep (se 1 (by rfl) ⟨422540, by rfl⟩ : syracuseStep 563387 = 845081) B845081
theorem B563447 : Blo 374761 563447 := bstep (se 1 (by rfl) ⟨422585, by rfl⟩ : syracuseStep 563447 = 845171) B845171
theorem B375047 : Blo 374761 375047 := bstep (se 1 (by rfl) ⟨281285, by rfl⟩ : syracuseStep 375047 = 562571) B562571
theorem B375055 : Blo 374761 375055 := bstep (se 1 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 375055 = 562583) B562583
theorem B563471 : Blo 374761 563471 := bstep (se 1 (by rfl) ⟨422603, by rfl⟩ : syracuseStep 563471 = 845207) B845207
theorem B7706897 : Blo 374761 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B563513 : Blo 374761 563513 := bstep (se 2 (by rfl) ⟨211317, by rfl⟩ : syracuseStep 563513 = 422635) B422635
theorem B375099 : Blo 374761 375099 := bstep (se 1 (by rfl) ⟨281324, by rfl⟩ : syracuseStep 375099 = 562649) B562649
theorem B1268027 : Blo 374761 1268027 := bstep (se 1 (by rfl) ⟨951020, by rfl⟩ : syracuseStep 1268027 = 1902041) B1902041
theorem B2144627 : Blo 374761 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B375175 : Blo 374761 375175 := bstep (se 1 (by rfl) ⟨281381, by rfl⟩ : syracuseStep 375175 = 562763) B562763
theorem B563591 : Blo 374761 563591 := bstep (se 1 (by rfl) ⟨422693, by rfl⟩ : syracuseStep 563591 = 845387) B845387
theorem B2578823 : Blo 374761 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B424327 : Blo 374761 424327 := bstep (se 1 (by rfl) ⟨318245, by rfl⟩ : syracuseStep 424327 = 636491) B636491
theorem B3979655 : Blo 374761 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B375183 : Blo 374761 375183 := bstep (se 1 (by rfl) ⟨281387, by rfl⟩ : syracuseStep 375183 = 562775) B562775
theorem B563627 : Blo 374761 563627 := bstep (se 1 (by rfl) ⟨422720, by rfl⟩ : syracuseStep 563627 = 845441) B845441
theorem B375227 : Blo 374761 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B563657 : Blo 374761 563657 := bstep (se 2 (by rfl) ⟨211371, by rfl⟩ : syracuseStep 563657 = 422743) B422743
theorem B2202065 : Blo 374761 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B375303 : Blo 374761 375303 := bstep (se 1 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 375303 = 562955) B562955
theorem B375311 : Blo 374761 375311 := bstep (se 1 (by rfl) ⟨281483, by rfl⟩ : syracuseStep 375311 = 562967) B562967
theorem B801323 : Blo 374761 801323 := bstep (se 1 (by rfl) ⟨600992, by rfl⟩ : syracuseStep 801323 = 1201985) B1201985
theorem B375355 : Blo 374761 375355 := bstep (se 1 (by rfl) ⟨281516, by rfl⟩ : syracuseStep 375355 = 563033) B563033
theorem B563771 : Blo 374761 563771 := bstep (se 1 (by rfl) ⟨422828, by rfl⟩ : syracuseStep 563771 = 845657) B845657
theorem B424507 : Blo 374761 424507 := bstep (se 1 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 424507 = 636761) B636761
theorem B3758669 : Blo 374761 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1432151 : Blo 374761 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B563831 : Blo 374761 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B375431 : Blo 374761 375431 := bstep (se 1 (by rfl) ⟨281573, by rfl⟩ : syracuseStep 375431 = 563147) B563147
theorem B375439 : Blo 374761 375439 := bstep (se 1 (by rfl) ⟨281579, by rfl⟩ : syracuseStep 375439 = 563159) B563159
theorem B563855 : Blo 374761 563855 := bstep (se 1 (by rfl) ⟨422891, by rfl⟩ : syracuseStep 563855 = 845783) B845783
theorem B563897 : Blo 374761 563897 := bstep (se 2 (by rfl) ⟨211461, by rfl⟩ : syracuseStep 563897 = 422923) B422923
theorem B375483 : Blo 374761 375483 := bstep (se 1 (by rfl) ⟨281612, by rfl⟩ : syracuseStep 375483 = 563225) B563225
theorem B3439297 : Blo 374761 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B506569 : Blo 374761 506569 := bstep (se 2 (by rfl) ⟨189963, by rfl⟩ : syracuseStep 506569 = 379927) B379927
theorem B1833673 : Blo 374761 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B375559 : Blo 374761 375559 := bstep (se 1 (by rfl) ⟨281669, by rfl⟩ : syracuseStep 375559 = 563339) B563339
theorem B563975 : Blo 374761 563975 := bstep (se 1 (by rfl) ⟨422981, by rfl⟩ : syracuseStep 563975 = 845963) B845963
theorem B375567 : Blo 374761 375567 := bstep (se 1 (by rfl) ⟨281675, by rfl⟩ : syracuseStep 375567 = 563351) B563351
theorem B1268513 : Blo 374761 1268513 := bstep (se 2 (by rfl) ⟨475692, by rfl⟩ : syracuseStep 1268513 = 951385) B951385
theorem B564011 : Blo 374761 564011 := bstep (se 1 (by rfl) ⟨423008, by rfl⟩ : syracuseStep 564011 = 846017) B846017
theorem B375611 : Blo 374761 375611 := bstep (se 1 (by rfl) ⟨281708, by rfl⟩ : syracuseStep 375611 = 563417) B563417
theorem B564041 : Blo 374761 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B867191 : Blo 374761 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B375687 : Blo 374761 375687 := bstep (se 1 (by rfl) ⟨281765, by rfl⟩ : syracuseStep 375687 = 563531) B563531
theorem B375695 : Blo 374761 375695 := bstep (se 1 (by rfl) ⟨281771, by rfl⟩ : syracuseStep 375695 = 563543) B563543
theorem B1809299 : Blo 374761 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1899449 : Blo 374761 1899449 := bstep (se 2 (by rfl) ⟨712293, by rfl⟩ : syracuseStep 1899449 = 1424587) B1424587
theorem B375739 : Blo 374761 375739 := bstep (se 1 (by rfl) ⟨281804, by rfl⟩ : syracuseStep 375739 = 563609) B563609
theorem B564155 : Blo 374761 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B564215 : Blo 374761 564215 := bstep (se 1 (by rfl) ⟨423161, by rfl⟩ : syracuseStep 564215 = 846323) B846323
theorem B375815 : Blo 374761 375815 := bstep (se 1 (by rfl) ⟨281861, by rfl⟩ : syracuseStep 375815 = 563723) B563723
theorem B949259 : Blo 374761 949259 := bstep (se 1 (by rfl) ⟨711944, by rfl⟩ : syracuseStep 949259 = 1423889) B1423889
theorem B1612811 : Blo 374761 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B375823 : Blo 374761 375823 := bstep (se 1 (by rfl) ⟨281867, by rfl⟩ : syracuseStep 375823 = 563735) B563735
theorem B564239 : Blo 374761 564239 := bstep (se 1 (by rfl) ⟨423179, by rfl⟩ : syracuseStep 564239 = 846359) B846359
theorem B1031183 : Blo 374761 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B424975 : Blo 374761 424975 := bstep (se 1 (by rfl) ⟨318731, by rfl⟩ : syracuseStep 424975 = 637463) B637463
theorem B564281 : Blo 374761 564281 := bstep (se 2 (by rfl) ⟨211605, by rfl⟩ : syracuseStep 564281 = 423211) B423211
theorem B375867 : Blo 374761 375867 := bstep (se 1 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 375867 = 563801) B563801
theorem B1219645 : Blo 374761 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B1432637 : Blo 374761 1432637 := bstep (se 3 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 1432637 = 537239) B537239
theorem B375943 : Blo 374761 375943 := bstep (se 1 (by rfl) ⟨281957, by rfl⟩ : syracuseStep 375943 = 563915) B563915
theorem B564359 : Blo 374761 564359 := bstep (se 1 (by rfl) ⟨423269, by rfl⟩ : syracuseStep 564359 = 846539) B846539
theorem B375951 : Blo 374761 375951 := bstep (se 1 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 375951 = 563927) B563927
theorem B564395 : Blo 374761 564395 := bstep (se 1 (by rfl) ⟨423296, by rfl⟩ : syracuseStep 564395 = 846593) B846593
theorem B375995 : Blo 374761 375995 := bstep (se 1 (by rfl) ⟨281996, by rfl⟩ : syracuseStep 375995 = 563993) B563993
theorem B14277829 : Blo 374761 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B564425 : Blo 374761 564425 := bstep (se 2 (by rfl) ⟨211659, by rfl⟩ : syracuseStep 564425 = 423319) B423319
theorem B376071 : Blo 374761 376071 := bstep (se 1 (by rfl) ⟨282053, by rfl⟩ : syracuseStep 376071 = 564107) B564107
theorem B490759 : Blo 374761 490759 := bstep (se 1 (by rfl) ⟨368069, by rfl⟩ : syracuseStep 490759 = 736139) B736139
theorem B376079 : Blo 374761 376079 := bstep (se 1 (by rfl) ⟨282059, by rfl⟩ : syracuseStep 376079 = 564119) B564119
theorem B507179 : Blo 374761 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B474427 : Blo 374761 474427 := bstep (se 1 (by rfl) ⟨355820, by rfl⟩ : syracuseStep 474427 = 711641) B711641
theorem B376123 : Blo 374761 376123 := bstep (se 1 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 376123 = 564185) B564185
theorem B564539 : Blo 374761 564539 := bstep (se 1 (by rfl) ⟨423404, by rfl⟩ : syracuseStep 564539 = 846809) B846809
theorem B1269107 : Blo 374761 1269107 := bstep (se 1 (by rfl) ⟨951830, by rfl⟩ : syracuseStep 1269107 = 1903661) B1903661
theorem B564599 : Blo 374761 564599 := bstep (se 1 (by rfl) ⟨423449, by rfl⟩ : syracuseStep 564599 = 846899) B846899
theorem B376199 : Blo 374761 376199 := bstep (se 1 (by rfl) ⟨282149, by rfl⟩ : syracuseStep 376199 = 564299) B564299
theorem B376207 : Blo 374761 376207 := bstep (se 1 (by rfl) ⟨282155, by rfl⟩ : syracuseStep 376207 = 564311) B564311
theorem B564623 : Blo 374761 564623 := bstep (se 1 (by rfl) ⟨423467, by rfl⟩ : syracuseStep 564623 = 846935) B846935
theorem B564665 : Blo 374761 564665 := bstep (se 2 (by rfl) ⟨211749, by rfl⟩ : syracuseStep 564665 = 423499) B423499
theorem B376251 : Blo 374761 376251 := bstep (se 1 (by rfl) ⟨282188, by rfl⟩ : syracuseStep 376251 = 564377) B564377
theorem B376327 : Blo 374761 376327 := bstep (se 1 (by rfl) ⟨282245, by rfl⟩ : syracuseStep 376327 = 564491) B564491
theorem B564743 : Blo 374761 564743 := bstep (se 1 (by rfl) ⟨423557, by rfl⟩ : syracuseStep 564743 = 847115) B847115
theorem B376335 : Blo 374761 376335 := bstep (se 1 (by rfl) ⟨282251, by rfl⟩ : syracuseStep 376335 = 564503) B564503
theorem B2711069 : Blo 374761 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B564779 : Blo 374761 564779 := bstep (se 1 (by rfl) ⟨423584, by rfl⟩ : syracuseStep 564779 = 847169) B847169
theorem B376379 : Blo 374761 376379 := bstep (se 1 (by rfl) ⟨282284, by rfl⟩ : syracuseStep 376379 = 564569) B564569
theorem B564809 : Blo 374761 564809 := bstep (se 2 (by rfl) ⟨211803, by rfl⟩ : syracuseStep 564809 = 423607) B423607
theorem B376455 : Blo 374761 376455 := bstep (se 1 (by rfl) ⟨282341, by rfl⟩ : syracuseStep 376455 = 564683) B564683
theorem B1007239 : Blo 374761 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B376463 : Blo 374761 376463 := bstep (se 1 (by rfl) ⟨282347, by rfl⟩ : syracuseStep 376463 = 564695) B564695
theorem B949907 : Blo 374761 949907 := bstep (se 1 (by rfl) ⟨712430, by rfl⟩ : syracuseStep 949907 = 1424861) B1424861
theorem B376507 : Blo 374761 376507 := bstep (se 1 (by rfl) ⟨282380, by rfl⟩ : syracuseStep 376507 = 564761) B564761
theorem B564923 : Blo 374761 564923 := bstep (se 1 (by rfl) ⟨423692, by rfl⟩ : syracuseStep 564923 = 847385) B847385
theorem B3440357 : Blo 374761 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B564983 : Blo 374761 564983 := bstep (se 1 (by rfl) ⟨423737, by rfl⟩ : syracuseStep 564983 = 847475) B847475
theorem B507655 : Blo 374761 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B376583 : Blo 374761 376583 := bstep (se 1 (by rfl) ⟨282437, by rfl⟩ : syracuseStep 376583 = 564875) B564875
theorem B376591 : Blo 374761 376591 := bstep (se 1 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 376591 = 564887) B564887
theorem B565007 : Blo 374761 565007 := bstep (se 1 (by rfl) ⟨423755, by rfl⟩ : syracuseStep 565007 = 847511) B847511
theorem B2146085 : Blo 374761 2146085 := bstep (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) B402391
theorem B474923 : Blo 374761 474923 := bstep (se 1 (by rfl) ⟨356192, by rfl⟩ : syracuseStep 474923 = 712385) B712385
theorem B4054835 : Blo 374761 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B565049 : Blo 374761 565049 := bstep (se 2 (by rfl) ⟨211893, by rfl⟩ : syracuseStep 565049 = 423787) B423787
theorem B376635 : Blo 374761 376635 := bstep (se 1 (by rfl) ⟨282476, by rfl⟩ : syracuseStep 376635 = 564953) B564953
theorem B2416499 : Blo 374761 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B712567 : Blo 374761 712567 := bstep (se 1 (by rfl) ⟨534425, by rfl⟩ : syracuseStep 712567 = 1068851) B1068851
theorem B376711 : Blo 374761 376711 := bstep (se 1 (by rfl) ⟨282533, by rfl⟩ : syracuseStep 376711 = 565067) B565067
theorem B565127 : Blo 374761 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B376719 : Blo 374761 376719 := bstep (se 1 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 376719 = 565079) B565079
theorem B565163 : Blo 374761 565163 := bstep (se 1 (by rfl) ⟨423872, by rfl⟩ : syracuseStep 565163 = 847745) B847745
theorem B950201 : Blo 374761 950201 := bstep (se 2 (by rfl) ⟨356325, by rfl⟩ : syracuseStep 950201 = 712651) B712651
theorem B376763 : Blo 374761 376763 := bstep (se 1 (by rfl) ⟨282572, by rfl⟩ : syracuseStep 376763 = 565145) B565145
theorem B565193 : Blo 374761 565193 := bstep (se 2 (by rfl) ⟨211947, by rfl⟩ : syracuseStep 565193 = 423895) B423895
theorem B1908683 : Blo 374761 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B1523731 : Blo 374761 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B376871 : Blo 374761 376871 := bstep (se 1 (by rfl) ⟨282653, by rfl⟩ : syracuseStep 376871 = 565307) B565307
theorem B1204303 : Blo 374761 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B376911 : Blo 374761 376911 := bstep (se 1 (by rfl) ⟨282683, by rfl⟩ : syracuseStep 376911 = 565367) B565367
theorem B3620945 : Blo 374761 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B2179153 : Blo 374761 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B376927 : Blo 374761 376927 := bstep (se 1 (by rfl) ⟨282695, by rfl⟩ : syracuseStep 376927 = 565391) B565391
theorem B376955 : Blo 374761 376955 := bstep (se 1 (by rfl) ⟨282716, by rfl⟩ : syracuseStep 376955 = 565433) B565433
theorem B1269917 : Blo 374761 1269917 := bstep (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) B476219
theorem B843947 : Blo 374761 843947 := bstep (se 1 (by rfl) ⟨632960, by rfl⟩ : syracuseStep 843947 = 1265921) B1265921
theorem B377007 : Blo 374761 377007 := bstep (se 1 (by rfl) ⟨282755, by rfl⟩ : syracuseStep 377007 = 565511) B565511
theorem B377031 : Blo 374761 377031 := bstep (se 1 (by rfl) ⟨282773, by rfl⟩ : syracuseStep 377031 = 565547) B565547
theorem B377051 : Blo 374761 377051 := bstep (se 1 (by rfl) ⟨282788, by rfl⟩ : syracuseStep 377051 = 565577) B565577
theorem B377127 : Blo 374761 377127 := bstep (se 1 (by rfl) ⟨282845, by rfl⟩ : syracuseStep 377127 = 565691) B565691
theorem B16253237 : Blo 374761 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B377167 : Blo 374761 377167 := bstep (se 1 (by rfl) ⟨282875, by rfl⟩ : syracuseStep 377167 = 565751) B565751
theorem B2572631 : Blo 374761 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B377183 : Blo 374761 377183 := bstep (se 1 (by rfl) ⟨282887, by rfl⟩ : syracuseStep 377183 = 565775) B565775
theorem B10322275 : Blo 374761 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B39739747 : Blo 374761 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B377211 : Blo 374761 377211 := bstep (se 1 (by rfl) ⟨282908, by rfl⟩ : syracuseStep 377211 = 565817) B565817
theorem B1073533 : Blo 374761 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B565679 : Blo 374761 565679 := bstep (se 1 (by rfl) ⟨424259, by rfl⟩ : syracuseStep 565679 = 848519) B848519
theorem B377263 : Blo 374761 377263 := bstep (se 1 (by rfl) ⟨282947, by rfl⟩ : syracuseStep 377263 = 565895) B565895
theorem B377287 : Blo 374761 377287 := bstep (se 1 (by rfl) ⟨282965, by rfl⟩ : syracuseStep 377287 = 565931) B565931
theorem B377307 : Blo 374761 377307 := bstep (se 1 (by rfl) ⟨282980, by rfl⟩ : syracuseStep 377307 = 565961) B565961
theorem B565769 : Blo 374761 565769 := bstep (se 2 (by rfl) ⟨212163, by rfl⟩ : syracuseStep 565769 = 424327) B424327
theorem B2851361 : Blo 374761 2851361 := bstep (se 2 (by rfl) ⟨1069260, by rfl⟩ : syracuseStep 2851361 = 2138521) B2138521
theorem B565799 : Blo 374761 565799 := bstep (se 1 (by rfl) ⟨424349, by rfl⟩ : syracuseStep 565799 = 848699) B848699
theorem B377383 : Blo 374761 377383 := bstep (se 1 (by rfl) ⟨283037, by rfl⟩ : syracuseStep 377383 = 566075) B566075
theorem B377423 : Blo 374761 377423 := bstep (se 1 (by rfl) ⟨283067, by rfl⟩ : syracuseStep 377423 = 566135) B566135
theorem B574031 : Blo 374761 574031 := bstep (se 1 (by rfl) ⟨430523, by rfl⟩ : syracuseStep 574031 = 861047) B861047
theorem B377439 : Blo 374761 377439 := bstep (se 1 (by rfl) ⟨283079, by rfl⟩ : syracuseStep 377439 = 566159) B566159
theorem B565883 : Blo 374761 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B377467 : Blo 374761 377467 := bstep (se 1 (by rfl) ⟨283100, by rfl⟩ : syracuseStep 377467 = 566201) B566201
theorem B713387 : Blo 374761 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B377519 : Blo 374761 377519 := bstep (se 1 (by rfl) ⟨283139, by rfl⟩ : syracuseStep 377519 = 566279) B566279
theorem B2867885 : Blo 374761 2867885 := bstep (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) B1075457
theorem B1270457 : Blo 374761 1270457 := bstep (se 2 (by rfl) ⟨476421, by rfl⟩ : syracuseStep 1270457 = 952843) B952843
theorem B844487 : Blo 374761 844487 := bstep (se 1 (by rfl) ⟨633365, by rfl⟩ : syracuseStep 844487 = 1266731) B1266731
theorem B377543 : Blo 374761 377543 := bstep (se 1 (by rfl) ⟨283157, by rfl⟩ : syracuseStep 377543 = 566315) B566315
theorem B377563 : Blo 374761 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B566009 : Blo 374761 566009 := bstep (se 2 (by rfl) ⟨212253, by rfl⟩ : syracuseStep 566009 = 424507) B424507
theorem B1352477 : Blo 374761 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B377639 : Blo 374761 377639 := bstep (se 1 (by rfl) ⟨283229, by rfl⟩ : syracuseStep 377639 = 566459) B566459
theorem B377679 : Blo 374761 377679 := bstep (se 1 (by rfl) ⟨283259, by rfl⟩ : syracuseStep 377679 = 566519) B566519
theorem B566111 : Blo 374761 566111 := bstep (se 1 (by rfl) ⟨424583, by rfl⟩ : syracuseStep 566111 = 849167) B849167
theorem B377695 : Blo 374761 377695 := bstep (se 1 (by rfl) ⟨283271, by rfl⟩ : syracuseStep 377695 = 566543) B566543
theorem B566123 : Blo 374761 566123 := bstep (se 1 (by rfl) ⟨424592, by rfl⟩ : syracuseStep 566123 = 849185) B849185
theorem B377723 : Blo 374761 377723 := bstep (se 1 (by rfl) ⟨283292, by rfl⟩ : syracuseStep 377723 = 566585) B566585
theorem B7906223 : Blo 374761 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B951223 : Blo 374761 951223 := bstep (se 1 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 951223 = 1426835) B1426835
theorem B3089335 : Blo 374761 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B2040805 : Blo 374761 2040805 := bstep (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) B382651
theorem B713767 : Blo 374761 713767 := bstep (se 1 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 713767 = 1070651) B1070651
theorem B566351 : Blo 374761 566351 := bstep (se 1 (by rfl) ⟨424763, by rfl⟩ : syracuseStep 566351 = 849527) B849527
theorem B2573507 : Blo 374761 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B713927 : Blo 374761 713927 := bstep (se 1 (by rfl) ⟨535445, by rfl⟩ : syracuseStep 713927 = 1070891) B1070891
theorem B566471 : Blo 374761 566471 := bstep (se 1 (by rfl) ⟨424853, by rfl⟩ : syracuseStep 566471 = 849707) B849707
theorem B9250037 : Blo 374761 9250037 := bstep (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) B867191
theorem B1271051 : Blo 374761 1271051 := bstep (se 1 (by rfl) ⟨953288, by rfl⟩ : syracuseStep 1271051 = 1906577) B1906577
theorem B566633 : Blo 374761 566633 := bstep (se 2 (by rfl) ⟨212487, by rfl⟩ : syracuseStep 566633 = 424975) B424975
theorem B1910141 : Blo 374761 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B2033039 : Blo 374761 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B476599 : Blo 374761 476599 := bstep (se 1 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 476599 = 714899) B714899
theorem B5481989 : Blo 374761 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B5137931 : Blo 374761 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B4277771 : Blo 374761 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B3671563 : Blo 374761 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1271321 : Blo 374761 1271321 := bstep (se 2 (by rfl) ⟨476745, by rfl⟩ : syracuseStep 1271321 = 953491) B953491
theorem B845351 : Blo 374761 845351 := bstep (se 1 (by rfl) ⟨634013, by rfl⟩ : syracuseStep 845351 = 1268027) B1268027
theorem B1427003 : Blo 374761 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B1902203 : Blo 374761 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B1468043 : Blo 374761 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B3212945 : Blo 374761 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B534215 : Blo 374761 534215 := bstep (se 1 (by rfl) ⟨400661, by rfl⟩ : syracuseStep 534215 = 801323) B801323
theorem B24323813 : Blo 374761 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B632569 : Blo 374761 632569 := bstep (se 2 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 632569 = 474427) B474427
theorem B3622751 : Blo 374761 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B845675 : Blo 374761 845675 := bstep (se 1 (by rfl) ⟨634256, by rfl⟩ : syracuseStep 845675 = 1268513) B1268513
theorem B10618775 : Blo 374761 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B845729 : Blo 374761 845729 := bstep (se 2 (by rfl) ⟨317148, by rfl⟩ : syracuseStep 845729 = 634297) B634297
theorem B427951 : Blo 374761 427951 := bstep (se 1 (by rfl) ⟨320963, by rfl⟩ : syracuseStep 427951 = 641927) B641927
theorem B1017775 : Blo 374761 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B1206199 : Blo 374761 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B632839 : Blo 374761 632839 := bstep (se 1 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 632839 = 949259) B949259
theorem B1075207 : Blo 374761 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B2410553 : Blo 374761 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B4810853 : Blo 374761 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B846071 : Blo 374761 846071 := bstep (se 1 (by rfl) ⟨634553, by rfl⟩ : syracuseStep 846071 = 1269107) B1269107
theorem B715081 : Blo 374761 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B952681 : Blo 374761 952681 := bstep (se 2 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 952681 = 714511) B714511
theorem B1067393 : Blo 374761 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B633271 : Blo 374761 633271 := bstep (se 1 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 633271 = 949907) B949907
theorem B30771683 : Blo 374761 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B633467 : Blo 374761 633467 := bstep (se 1 (by rfl) ⟨475100, by rfl⟩ : syracuseStep 633467 = 950201) B950201
theorem B952955 : Blo 374761 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B1272455 : Blo 374761 1272455 := bstep (se 1 (by rfl) ⟨954341, by rfl⟩ : syracuseStep 1272455 = 1908683) B1908683
theorem B1272509 : Blo 374761 1272509 := bstep (se 3 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 1272509 = 477191) B477191
theorem B477895 : Blo 374761 477895 := bstep (se 1 (by rfl) ⟨358421, by rfl⟩ : syracuseStep 477895 = 716843) B716843
theorem B1067735 : Blo 374761 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B1067849 : Blo 374761 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B846665 : Blo 374761 846665 := bstep (se 2 (by rfl) ⟨317499, by rfl⟩ : syracuseStep 846665 = 634999) B634999
theorem B871241 : Blo 374761 871241 := bstep (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) B653431
theorem B1272671 : Blo 374761 1272671 := bstep (se 1 (by rfl) ⟨954503, by rfl⟩ : syracuseStep 1272671 = 1909007) B1909007
theorem B2862053 : Blo 374761 2862053 := bstep (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) B536635
theorem B1272833 : Blo 374761 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B633865 : Blo 374761 633865 := bstep (se 2 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 633865 = 475399) B475399
theorem B1207315 : Blo 374761 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B634027 : Blo 374761 634027 := bstep (se 1 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 634027 = 951041) B951041
theorem B7253185 : Blo 374761 7253185 := bstep (se 2 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 7253185 = 5439889) B5439889
theorem B904439 : Blo 374761 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B3910949 : Blo 374761 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1453373 : Blo 374761 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B1609085 : Blo 374761 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B1019279 : Blo 374761 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B2280923 : Blo 374761 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B634331 : Blo 374761 634331 := bstep (se 1 (by rfl) ⟨475748, by rfl⟩ : syracuseStep 634331 = 951497) B951497
theorem B3436019 : Blo 374761 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B675425 : Blo 374761 675425 := bstep (se 2 (by rfl) ⟨253284, by rfl⟩ : syracuseStep 675425 = 506569) B506569
theorem B2444897 : Blo 374761 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B847457 : Blo 374761 847457 := bstep (se 2 (by rfl) ⟨317796, by rfl⟩ : syracuseStep 847457 = 635593) B635593
theorem B1207943 : Blo 374761 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B634567 : Blo 374761 634567 := bstep (se 1 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 634567 = 951851) B951851
theorem B806611 : Blo 374761 806611 := bstep (se 1 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 806611 = 1209917) B1209917
theorem B1273643 : Blo 374761 1273643 := bstep (se 1 (by rfl) ⟨955232, by rfl⟩ : syracuseStep 1273643 = 1910465) B1910465
theorem B1937195 : Blo 374761 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B4271939 : Blo 374761 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B634729 : Blo 374761 634729 := bstep (se 2 (by rfl) ⟨238023, by rfl⟩ : syracuseStep 634729 = 476047) B476047
theorem B421807 : Blo 374761 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B847799 : Blo 374761 847799 := bstep (se 1 (by rfl) ⟨635849, by rfl⟩ : syracuseStep 847799 = 1271699) B1271699
theorem B3477433 : Blo 374761 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B602075 : Blo 374761 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B536539 : Blo 374761 536539 := bstep (se 1 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 536539 = 804809) B804809
theorem B2289701 : Blo 374761 2289701 := bstep (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) B429319
theorem B2617381 : Blo 374761 2617381 := bstep (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) B490759
theorem B1273913 : Blo 374761 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B1626193 : Blo 374761 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1429751 : Blo 374761 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B2846987 : Blo 374761 2846987 := bstep (se 1 (by rfl) ⟨2135240, by rfl⟩ : syracuseStep 2846987 = 4270481) B4270481
theorem B4559165 : Blo 374761 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B1904957 : Blo 374761 1904957 := bstep (se 3 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 1904957 = 714359) B714359
theorem B4059467 : Blo 374761 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B422239 : Blo 374761 422239 := bstep (se 1 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 422239 = 633359) B633359
theorem B1274237 : Blo 374761 1274237 := bstep (se 3 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 1274237 = 477839) B477839
theorem B954767 : Blo 374761 954767 := bstep (se 1 (by rfl) ⟨716075, by rfl⟩ : syracuseStep 954767 = 1432151) B1432151
theorem B635323 : Blo 374761 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B602587 : Blo 374761 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B602633 : Blo 374761 602633 := bstep (se 2 (by rfl) ⟨225987, by rfl⟩ : syracuseStep 602633 = 451975) B451975
theorem B848393 : Blo 374761 848393 := bstep (se 2 (by rfl) ⟨318147, by rfl⟩ : syracuseStep 848393 = 636295) B636295
theorem B635431 : Blo 374761 635431 := bstep (se 1 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 635431 = 953147) B953147
theorem B1356385 : Blo 374761 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B1266299 : Blo 374761 1266299 := bstep (se 1 (by rfl) ⟨949724, by rfl⟩ : syracuseStep 1266299 = 1899449) B1899449
theorem B1274507 : Blo 374761 1274507 := bstep (se 1 (by rfl) ⟨955880, by rfl⟩ : syracuseStep 1274507 = 1911761) B1911761
theorem B422599 : Blo 374761 422599 := bstep (se 1 (by rfl) ⟨316949, by rfl⟩ : syracuseStep 422599 = 633899) B633899
theorem B955091 : Blo 374761 955091 := bstep (se 1 (by rfl) ⟨716318, by rfl⟩ : syracuseStep 955091 = 1432637) B1432637
theorem B1266461 : Blo 374761 1266461 := bstep (se 3 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 1266461 = 474923) B474923
theorem B2896669 : Blo 374761 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B1209161 : Blo 374761 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B848735 : Blo 374761 848735 := bstep (se 1 (by rfl) ⟨636551, by rfl⟩ : syracuseStep 848735 = 1273103) B1273103
theorem B635755 : Blo 374761 635755 := bstep (se 1 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 635755 = 953633) B953633
theorem B3044243 : Blo 374761 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B3208193 : Blo 374761 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B676873 : Blo 374761 676873 := bstep (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) B507655
theorem B1807379 : Blo 374761 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B848915 : Blo 374761 848915 := bstep (se 1 (by rfl) ⟨636686, by rfl⟩ : syracuseStep 848915 = 1273373) B1273373
theorem B1897667 : Blo 374761 1897667 := bstep (se 1 (by rfl) ⟨1423250, by rfl⟩ : syracuseStep 1897667 = 2846501) B2846501
theorem B1430723 : Blo 374761 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B1610999 : Blo 374761 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B1144169 : Blo 374761 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B849257 : Blo 374761 849257 := bstep (se 2 (by rfl) ⟨318471, by rfl⟩ : syracuseStep 849257 = 636943) B636943
theorem B2602405 : Blo 374761 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B562607 : Blo 374761 562607 := bstep (se 1 (by rfl) ⟨421955, by rfl⟩ : syracuseStep 562607 = 843911) B843911
theorem B3626441 : Blo 374761 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B2618825 : Blo 374761 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1267163 : Blo 374761 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B5445083 : Blo 374761 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B562697 : Blo 374761 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B1070617 : Blo 374761 1070617 := bstep (se 2 (by rfl) ⟨401481, by rfl⟩ : syracuseStep 1070617 = 802963) B802963
theorem B562727 : Blo 374761 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B423463 : Blo 374761 423463 := bstep (se 1 (by rfl) ⟨317597, by rfl⟩ : syracuseStep 423463 = 635195) B635195
theorem B12342881 : Blo 374761 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B562811 : Blo 374761 562811 := bstep (se 1 (by rfl) ⟨422108, by rfl⟩ : syracuseStep 562811 = 844217) B844217
theorem B1431179 : Blo 374761 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B2848445 : Blo 374761 2848445 := bstep (se 3 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 2848445 = 1068167) B1068167
theorem B562937 : Blo 374761 562937 := bstep (se 2 (by rfl) ⟨211101, by rfl⟩ : syracuseStep 562937 = 422203) B422203
theorem B1447753 : Blo 374761 1447753 := bstep (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) B1085815
theorem B2602847 : Blo 374761 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B563039 : Blo 374761 563039 := bstep (se 1 (by rfl) ⟨422279, by rfl⟩ : syracuseStep 563039 = 844559) B844559
theorem B3045215 : Blo 374761 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1431391 : Blo 374761 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B563051 : Blo 374761 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B636815 : Blo 374761 636815 := bstep (se 1 (by rfl) ⟨477611, by rfl⟩ : syracuseStep 636815 = 955223) B955223
theorem B849851 : Blo 374761 849851 := bstep (se 1 (by rfl) ⟨637388, by rfl⟩ : syracuseStep 849851 = 1274777) B1274777
theorem B3209219 : Blo 374761 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B3045383 : Blo 374761 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B374823 : Blo 374761 374823 := bstep (se 1 (by rfl) ⟨281117, by rfl⟩ : syracuseStep 374823 = 562235) B562235
theorem B374863 : Blo 374761 374863 := bstep (se 1 (by rfl) ⟨281147, by rfl⟩ : syracuseStep 374863 = 562295) B562295
theorem B563279 : Blo 374761 563279 := bstep (se 1 (by rfl) ⟨422459, by rfl⟩ : syracuseStep 563279 = 844919) B844919
theorem B3225689 : Blo 374761 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B374879 : Blo 374761 374879 := bstep (se 1 (by rfl) ⟨281159, by rfl⟩ : syracuseStep 374879 = 562319) B562319
theorem B374907 : Blo 374761 374907 := bstep (se 1 (by rfl) ⟨281180, by rfl⟩ : syracuseStep 374907 = 562361) B562361
theorem B637051 : Blo 374761 637051 := bstep (se 1 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 637051 = 955577) B955577
theorem B1267865 : Blo 374761 1267865 := bstep (se 2 (by rfl) ⟨475449, by rfl⟩ : syracuseStep 1267865 = 950899) B950899
theorem B2848931 : Blo 374761 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B374959 : Blo 374761 374959 := bstep (se 1 (by rfl) ⟨281219, by rfl⟩ : syracuseStep 374959 = 562439) B562439
theorem B374983 : Blo 374761 374983 := bstep (se 1 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 374983 = 562475) B562475
theorem B563399 : Blo 374761 563399 := bstep (se 1 (by rfl) ⟨422549, by rfl⟩ : syracuseStep 563399 = 845099) B845099
theorem B375003 : Blo 374761 375003 := bstep (se 1 (by rfl) ⟨281252, by rfl⟩ : syracuseStep 375003 = 562505) B562505
theorem B4585729 : Blo 374761 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B375079 : Blo 374761 375079 := bstep (se 1 (by rfl) ⟨281309, by rfl⟩ : syracuseStep 375079 = 562619) B562619
theorem B375119 : Blo 374761 375119 := bstep (se 1 (by rfl) ⟨281339, by rfl⟩ : syracuseStep 375119 = 562679) B562679
theorem B3438935 : Blo 374761 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B375135 : Blo 374761 375135 := bstep (se 1 (by rfl) ⟨281351, by rfl⟩ : syracuseStep 375135 = 562703) B562703
theorem B563561 : Blo 374761 563561 := bstep (se 2 (by rfl) ⟨211335, by rfl⟩ : syracuseStep 563561 = 422671) B422671
theorem B375163 : Blo 374761 375163 := bstep (se 1 (by rfl) ⟨281372, by rfl⟩ : syracuseStep 375163 = 562745) B562745
theorem B907649 : Blo 374761 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B375215 : Blo 374761 375215 := bstep (se 1 (by rfl) ⟨281411, by rfl⟩ : syracuseStep 375215 = 562823) B562823
theorem B563639 : Blo 374761 563639 := bstep (se 1 (by rfl) ⟨422729, by rfl⟩ : syracuseStep 563639 = 845459) B845459
theorem B375239 : Blo 374761 375239 := bstep (se 1 (by rfl) ⟨281429, by rfl⟩ : syracuseStep 375239 = 562859) B562859
theorem B375259 : Blo 374761 375259 := bstep (se 1 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 375259 = 562889) B562889
theorem B563675 : Blo 374761 563675 := bstep (se 1 (by rfl) ⟨422756, by rfl⟩ : syracuseStep 563675 = 845513) B845513
theorem B4594157 : Blo 374761 4594157 := bstep (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) B1722809
theorem B1907225 : Blo 374761 1907225 := bstep (se 2 (by rfl) ⟨715209, by rfl⟩ : syracuseStep 1907225 = 1430419) B1430419
theorem B375335 : Blo 374761 375335 := bstep (se 1 (by rfl) ⟨281501, by rfl⟩ : syracuseStep 375335 = 563003) B563003
theorem B375375 : Blo 374761 375375 := bstep (se 1 (by rfl) ⟨281531, by rfl⟩ : syracuseStep 375375 = 563063) B563063
theorem B375391 : Blo 374761 375391 := bstep (se 1 (by rfl) ⟨281543, by rfl⟩ : syracuseStep 375391 = 563087) B563087
theorem B375419 : Blo 374761 375419 := bstep (se 1 (by rfl) ⟨281564, by rfl⟩ : syracuseStep 375419 = 563129) B563129
theorem B3652231 : Blo 374761 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B375471 : Blo 374761 375471 := bstep (se 1 (by rfl) ⟨281603, by rfl⟩ : syracuseStep 375471 = 563207) B563207
theorem B948935 : Blo 374761 948935 := bstep (se 1 (by rfl) ⟨711701, by rfl⟩ : syracuseStep 948935 = 1423403) B1423403
theorem B375495 : Blo 374761 375495 := bstep (se 1 (by rfl) ⟨281621, by rfl⟩ : syracuseStep 375495 = 563243) B563243
theorem B2898641 : Blo 374761 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1424087 : Blo 374761 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B375515 : Blo 374761 375515 := bstep (se 1 (by rfl) ⟨281636, by rfl⟩ : syracuseStep 375515 = 563273) B563273
theorem B4831973 : Blo 374761 4831973 := bstep (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) B905995
theorem B1432349 : Blo 374761 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B375591 : Blo 374761 375591 := bstep (se 1 (by rfl) ⟨281693, by rfl⟩ : syracuseStep 375591 = 563387) B563387
theorem B1432363 : Blo 374761 1432363 := bstep (se 1 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 1432363 = 2148545) B2148545
theorem B711497 : Blo 374761 711497 := bstep (se 2 (by rfl) ⟨266811, by rfl⟩ : syracuseStep 711497 = 533623) B533623
theorem B1653577 : Blo 374761 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B375631 : Blo 374761 375631 := bstep (se 1 (by rfl) ⟨281723, by rfl⟩ : syracuseStep 375631 = 563447) B563447
theorem B375647 : Blo 374761 375647 := bstep (se 1 (by rfl) ⟨281735, by rfl⟩ : syracuseStep 375647 = 563471) B563471
theorem B375675 : Blo 374761 375675 := bstep (se 1 (by rfl) ⟨281756, by rfl⟩ : syracuseStep 375675 = 563513) B563513
theorem B375727 : Blo 374761 375727 := bstep (se 1 (by rfl) ⟨281795, by rfl⟩ : syracuseStep 375727 = 563591) B563591
theorem B564143 : Blo 374761 564143 := bstep (se 1 (by rfl) ⟨423107, by rfl⟩ : syracuseStep 564143 = 846215) B846215
theorem B19037105 : Blo 374761 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1719215 : Blo 374761 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B2653103 : Blo 374761 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B375751 : Blo 374761 375751 := bstep (se 1 (by rfl) ⟨281813, by rfl⟩ : syracuseStep 375751 = 563627) B563627
theorem B375771 : Blo 374761 375771 := bstep (se 1 (by rfl) ⟨281828, by rfl⟩ : syracuseStep 375771 = 563657) B563657
theorem B564233 : Blo 374761 564233 := bstep (se 2 (by rfl) ⟨211587, by rfl⟩ : syracuseStep 564233 = 423175) B423175
theorem B375847 : Blo 374761 375847 := bstep (se 1 (by rfl) ⟨281885, by rfl⟩ : syracuseStep 375847 = 563771) B563771
theorem B564263 : Blo 374761 564263 := bstep (se 1 (by rfl) ⟨423197, by rfl⟩ : syracuseStep 564263 = 846395) B846395
theorem B2505779 : Blo 374761 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B375887 : Blo 374761 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B375903 : Blo 374761 375903 := bstep (se 1 (by rfl) ⟨281927, by rfl⟩ : syracuseStep 375903 = 563855) B563855
theorem B375931 : Blo 374761 375931 := bstep (se 1 (by rfl) ⟨281948, by rfl⟩ : syracuseStep 375931 = 563897) B563897
theorem B564347 : Blo 374761 564347 := bstep (se 1 (by rfl) ⟨423260, by rfl⟩ : syracuseStep 564347 = 846521) B846521
theorem B375983 : Blo 374761 375983 := bstep (se 1 (by rfl) ⟨281987, by rfl⟩ : syracuseStep 375983 = 563975) B563975
theorem B376007 : Blo 374761 376007 := bstep (se 1 (by rfl) ⟨282005, by rfl⟩ : syracuseStep 376007 = 564011) B564011
theorem B376027 : Blo 374761 376027 := bstep (se 1 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 376027 = 564041) B564041
theorem B711929 : Blo 374761 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B564473 : Blo 374761 564473 := bstep (se 2 (by rfl) ⟨211677, by rfl⟩ : syracuseStep 564473 = 423355) B423355
theorem B376103 : Blo 374761 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B1269053 : Blo 374761 1269053 := bstep (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) B475895
theorem B376143 : Blo 374761 376143 := bstep (se 1 (by rfl) ⟨282107, by rfl⟩ : syracuseStep 376143 = 564215) B564215
theorem B376159 : Blo 374761 376159 := bstep (se 1 (by rfl) ⟨282119, by rfl⟩ : syracuseStep 376159 = 564239) B564239
theorem B687455 : Blo 374761 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B564575 : Blo 374761 564575 := bstep (se 1 (by rfl) ⟨423431, by rfl⟩ : syracuseStep 564575 = 846863) B846863
theorem B564587 : Blo 374761 564587 := bstep (se 1 (by rfl) ⟨423440, by rfl⟩ : syracuseStep 564587 = 846881) B846881
theorem B376187 : Blo 374761 376187 := bstep (se 1 (by rfl) ⟨282140, by rfl⟩ : syracuseStep 376187 = 564281) B564281
theorem B376239 : Blo 374761 376239 := bstep (se 1 (by rfl) ⟨282179, by rfl⟩ : syracuseStep 376239 = 564359) B564359
theorem B376263 : Blo 374761 376263 := bstep (se 1 (by rfl) ⟨282197, by rfl⟩ : syracuseStep 376263 = 564395) B564395
theorem B843227 : Blo 374761 843227 := bstep (se 1 (by rfl) ⟨632420, by rfl⟩ : syracuseStep 843227 = 1264841) B1264841
theorem B376283 : Blo 374761 376283 := bstep (se 1 (by rfl) ⟨282212, by rfl⟩ : syracuseStep 376283 = 564425) B564425
theorem B1342985 : Blo 374761 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B376359 : Blo 374761 376359 := bstep (se 1 (by rfl) ⟨282269, by rfl⟩ : syracuseStep 376359 = 564539) B564539
theorem B5414465 : Blo 374761 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B376399 : Blo 374761 376399 := bstep (se 1 (by rfl) ⟨282299, by rfl⟩ : syracuseStep 376399 = 564599) B564599
theorem B564815 : Blo 374761 564815 := bstep (se 1 (by rfl) ⟨423611, by rfl⟩ : syracuseStep 564815 = 847223) B847223
theorem B376415 : Blo 374761 376415 := bstep (se 1 (by rfl) ⟨282311, by rfl⟩ : syracuseStep 376415 = 564623) B564623
theorem B3858043 : Blo 374761 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B376443 : Blo 374761 376443 := bstep (se 1 (by rfl) ⟨282332, by rfl⟩ : syracuseStep 376443 = 564665) B564665
theorem B1613459 : Blo 374761 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B376495 : Blo 374761 376495 := bstep (se 1 (by rfl) ⟨282371, by rfl⟩ : syracuseStep 376495 = 564743) B564743
theorem B376519 : Blo 374761 376519 := bstep (se 1 (by rfl) ⟨282389, by rfl⟩ : syracuseStep 376519 = 564779) B564779
theorem B564935 : Blo 374761 564935 := bstep (se 1 (by rfl) ⟨423701, by rfl⟩ : syracuseStep 564935 = 847403) B847403
theorem B376539 : Blo 374761 376539 := bstep (se 1 (by rfl) ⟨282404, by rfl⟩ : syracuseStep 376539 = 564809) B564809
theorem B1449721 : Blo 374761 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B376615 : Blo 374761 376615 := bstep (se 1 (by rfl) ⟨282461, by rfl⟩ : syracuseStep 376615 = 564923) B564923
theorem B2293571 : Blo 374761 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B950089 : Blo 374761 950089 := bstep (se 2 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 950089 = 712567) B712567
theorem B376655 : Blo 374761 376655 := bstep (se 1 (by rfl) ⟨282491, by rfl⟩ : syracuseStep 376655 = 564983) B564983
theorem B376671 : Blo 374761 376671 := bstep (se 1 (by rfl) ⟨282503, by rfl⟩ : syracuseStep 376671 = 565007) B565007
theorem B565097 : Blo 374761 565097 := bstep (se 2 (by rfl) ⟨211911, by rfl⟩ : syracuseStep 565097 = 423823) B423823
theorem B2703223 : Blo 374761 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B376699 : Blo 374761 376699 := bstep (se 1 (by rfl) ⟨282524, by rfl⟩ : syracuseStep 376699 = 565049) B565049
theorem B843695 : Blo 374761 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B376751 : Blo 374761 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B565175 : Blo 374761 565175 := bstep (se 1 (by rfl) ⟨423881, by rfl⟩ : syracuseStep 565175 = 847763) B847763
theorem B376775 : Blo 374761 376775 := bstep (se 1 (by rfl) ⟨282581, by rfl⟩ : syracuseStep 376775 = 565163) B565163
theorem B376795 : Blo 374761 376795 := bstep (se 1 (by rfl) ⟨282596, by rfl⟩ : syracuseStep 376795 = 565193) B565193
theorem B565211 : Blo 374761 565211 := bstep (se 1 (by rfl) ⟨423908, by rfl⟩ : syracuseStep 565211 = 847817) B847817
theorem B843785 : Blo 374761 843785 := bstep (se 2 (by rfl) ⟨316419, by rfl⟩ : syracuseStep 843785 = 632839) B632839
theorem B1433609 : Blo 374761 1433609 := bstep (se 2 (by rfl) ⟨537603, by rfl⟩ : syracuseStep 1433609 = 1075207) B1075207
theorem B2031641 : Blo 374761 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B3489841 : Blo 374761 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B1605737 : Blo 374761 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B3039443 : Blo 374761 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B1269971 : Blo 374761 1269971 := bstep (se 1 (by rfl) ⟨952478, by rfl⟩ : syracuseStep 1269971 = 1904957) B1904957
theorem B377119 : Blo 374761 377119 := bstep (se 1 (by rfl) ⟨282839, by rfl⟩ : syracuseStep 377119 = 565679) B565679
theorem B401755 : Blo 374761 401755 := bstep (se 1 (by rfl) ⟨301316, by rfl⟩ : syracuseStep 401755 = 602633) B602633
theorem B565595 : Blo 374761 565595 := bstep (se 1 (by rfl) ⟨424196, by rfl⟩ : syracuseStep 565595 = 848393) B848393
theorem B377179 : Blo 374761 377179 := bstep (se 1 (by rfl) ⟨282884, by rfl⟩ : syracuseStep 377179 = 565769) B565769
theorem B1900907 : Blo 374761 1900907 := bstep (se 1 (by rfl) ⟨1425680, by rfl⟩ : syracuseStep 1900907 = 2851361) B2851361
theorem B377199 : Blo 374761 377199 := bstep (se 1 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 377199 = 565799) B565799
theorem B844199 : Blo 374761 844199 := bstep (se 1 (by rfl) ⟨633149, by rfl⟩ : syracuseStep 844199 = 1266299) B1266299
theorem B377255 : Blo 374761 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B13763033 : Blo 374761 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B52986329 : Blo 374761 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B1270241 : Blo 374761 1270241 := bstep (se 2 (by rfl) ⟨476340, by rfl⟩ : syracuseStep 1270241 = 952681) B952681
theorem B377339 : Blo 374761 377339 := bstep (se 1 (by rfl) ⟨283004, by rfl⟩ : syracuseStep 377339 = 566009) B566009
theorem B844307 : Blo 374761 844307 := bstep (se 1 (by rfl) ⟨633230, by rfl⟩ : syracuseStep 844307 = 1266461) B1266461
theorem B565823 : Blo 374761 565823 := bstep (se 1 (by rfl) ⟨424367, by rfl⟩ : syracuseStep 565823 = 848735) B848735
theorem B377407 : Blo 374761 377407 := bstep (se 1 (by rfl) ⟨283055, by rfl⟩ : syracuseStep 377407 = 566111) B566111
theorem B377415 : Blo 374761 377415 := bstep (se 1 (by rfl) ⟨283061, by rfl⟩ : syracuseStep 377415 = 566123) B566123
theorem B844361 : Blo 374761 844361 := bstep (se 2 (by rfl) ⟨316635, by rfl⟩ : syracuseStep 844361 = 633271) B633271
theorem B803449 : Blo 374761 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B2138795 : Blo 374761 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B1204919 : Blo 374761 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B565943 : Blo 374761 565943 := bstep (se 1 (by rfl) ⟨424457, by rfl⟩ : syracuseStep 565943 = 848915) B848915
theorem B377567 : Blo 374761 377567 := bstep (se 1 (by rfl) ⟨283175, by rfl⟩ : syracuseStep 377567 = 566351) B566351
theorem B475951 : Blo 374761 475951 := bstep (se 1 (by rfl) ⟨356963, by rfl⟩ : syracuseStep 475951 = 713927) B713927
theorem B377647 : Blo 374761 377647 := bstep (se 1 (by rfl) ⟨283235, by rfl⟩ : syracuseStep 377647 = 566471) B566471
theorem B1073999 : Blo 374761 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B762779 : Blo 374761 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B566171 : Blo 374761 566171 := bstep (se 1 (by rfl) ⟨424628, by rfl⟩ : syracuseStep 566171 = 849257) B849257
theorem B377755 : Blo 374761 377755 := bstep (se 1 (by rfl) ⟨283316, by rfl⟩ : syracuseStep 377755 = 566633) B566633
theorem B2417627 : Blo 374761 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B844775 : Blo 374761 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B3630055 : Blo 374761 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B3654659 : Blo 374761 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B3425287 : Blo 374761 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B2851847 : Blo 374761 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B951335 : Blo 374761 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B1909817 : Blo 374761 1909817 := bstep (se 2 (by rfl) ⟨716181, by rfl⟩ : syracuseStep 1909817 = 1432363) B1432363
theorem B7079183 : Blo 374761 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B566567 : Blo 374761 566567 := bstep (se 1 (by rfl) ⟨424925, by rfl⟩ : syracuseStep 566567 = 849851) B849851
theorem B2721073 : Blo 374761 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B2139479 : Blo 374761 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B902497 : Blo 374761 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B845153 : Blo 374761 845153 := bstep (se 2 (by rfl) ⟨316932, by rfl⟩ : syracuseStep 845153 = 633865) B633865
theorem B3581293 : Blo 374761 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B1607035 : Blo 374761 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B951689 : Blo 374761 951689 := bstep (se 2 (by rfl) ⟨356883, by rfl⟩ : syracuseStep 951689 = 713767) B713767
theorem B845243 : Blo 374761 845243 := bstep (se 1 (by rfl) ⟨633932, by rfl⟩ : syracuseStep 845243 = 1267865) B1267865
theorem B35276309 : Blo 374761 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B845369 : Blo 374761 845369 := bstep (se 2 (by rfl) ⟨317013, by rfl⟩ : syracuseStep 845369 = 634027) B634027
theorem B20514455 : Blo 374761 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B1271483 : Blo 374761 1271483 := bstep (se 1 (by rfl) ⟨953612, by rfl⟩ : syracuseStep 1271483 = 1907225) B1907225
theorem B4302557 : Blo 374761 4302557 := bstep (se 3 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 4302557 = 1613459) B1613459
theorem B1902365 : Blo 374761 1902365 := bstep (se 3 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 1902365 = 713387) B713387
theorem B632623 : Blo 374761 632623 := bstep (se 1 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 632623 = 948935) B948935
theorem B3221315 : Blo 374761 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B12691403 : Blo 374761 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B1427489 : Blo 374761 1427489 := bstep (se 2 (by rfl) ⟨535308, by rfl⟩ : syracuseStep 1427489 = 1070617) B1070617
theorem B3606605 : Blo 374761 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B2607299 : Blo 374761 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B846035 : Blo 374761 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B968915 : Blo 374761 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B8120573 : Blo 374761 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B846089 : Blo 374761 846089 := bstep (se 2 (by rfl) ⟨317283, by rfl⟩ : syracuseStep 846089 = 634567) B634567
theorem B1075481 : Blo 374761 1075481 := bstep (se 2 (by rfl) ⟨403305, by rfl⟩ : syracuseStep 1075481 = 806611) B806611
theorem B805295 : Blo 374761 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B846305 : Blo 374761 846305 := bstep (se 2 (by rfl) ⟨317364, by rfl⟩ : syracuseStep 846305 = 634729) B634729
theorem B1608265 : Blo 374761 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B715385 : Blo 374761 715385 := bstep (se 2 (by rfl) ⟨268269, by rfl⟩ : syracuseStep 715385 = 536539) B536539
theorem B1526467 : Blo 374761 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B846611 : Blo 374761 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B953167 : Blo 374761 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B2706311 : Blo 374761 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B1715087 : Blo 374761 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B6114305 : Blo 374761 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B953441 : Blo 374761 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B1911923 : Blo 374761 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B846971 : Blo 374761 846971 := bstep (se 1 (by rfl) ⟨635228, by rfl⟩ : syracuseStep 846971 = 1270457) B1270457
theorem B806107 : Blo 374761 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B847097 : Blo 374761 847097 := bstep (se 2 (by rfl) ⟨317661, by rfl⟩ : syracuseStep 847097 = 635323) B635323
theorem B847241 : Blo 374761 847241 := bstep (se 2 (by rfl) ⟨317715, by rfl⟩ : syracuseStep 847241 = 635431) B635431
theorem B9293237 : Blo 374761 9293237 := bstep (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) B871241
theorem B1265111 : Blo 374761 1265111 := bstep (se 1 (by rfl) ⟨948833, by rfl⟩ : syracuseStep 1265111 = 1897667) B1897667
theorem B1715671 : Blo 374761 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B953815 : Blo 374761 953815 := bstep (se 1 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 953815 = 1430723) B1430723
theorem B847367 : Blo 374761 847367 := bstep (se 1 (by rfl) ⟨635525, by rfl⟩ : syracuseStep 847367 = 1271051) B1271051
theorem B4869641 : Blo 374761 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B1273427 : Blo 374761 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B847547 : Blo 374761 847547 := bstep (se 1 (by rfl) ⟨635660, by rfl⟩ : syracuseStep 847547 = 1271321) B1271321
theorem B3862225 : Blo 374761 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B8228587 : Blo 374761 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B978695 : Blo 374761 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B954119 : Blo 374761 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B2141963 : Blo 374761 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B847673 : Blo 374761 847673 := bstep (se 2 (by rfl) ⟨317877, by rfl⟩ : syracuseStep 847673 = 635755) B635755
theorem B16215875 : Blo 374761 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B6983533 : Blo 374761 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B1609753 : Blo 374761 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B2150459 : Blo 374761 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B3207235 : Blo 374761 3207235 := bstep (se 1 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 3207235 = 4810853) B4810853
theorem B9670913 : Blo 374761 9670913 := bstep (se 2 (by rfl) ⟨3626592, by rfl⟩ : syracuseStep 9670913 = 7253185) B7253185
theorem B422311 : Blo 374761 422311 := bstep (se 1 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 422311 = 633467) B633467
theorem B635303 : Blo 374761 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B848303 : Blo 374761 848303 := bstep (se 1 (by rfl) ⟨636227, by rfl⟩ : syracuseStep 848303 = 1272455) B1272455
theorem B848339 : Blo 374761 848339 := bstep (se 1 (by rfl) ⟨636254, by rfl⟩ : syracuseStep 848339 = 1272509) B1272509
theorem B954899 : Blo 374761 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B3469873 : Blo 374761 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B848447 : Blo 374761 848447 := bstep (se 1 (by rfl) ⟨636335, by rfl⟩ : syracuseStep 848447 = 1272671) B1272671
theorem B635465 : Blo 374761 635465 := bstep (se 2 (by rfl) ⟨238299, by rfl⟩ : syracuseStep 635465 = 476599) B476599
theorem B848555 : Blo 374761 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B4895417 : Blo 374761 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B602959 : Blo 374761 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B5428133 : Blo 374761 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B562151 : Blo 374761 562151 := bstep (se 1 (by rfl) ⟨421613, by rfl⟩ : syracuseStep 562151 = 843227) B843227
theorem B1520615 : Blo 374761 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B422887 : Blo 374761 422887 := bstep (se 1 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 422887 = 634331) B634331
theorem B2290679 : Blo 374761 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B3609643 : Blo 374761 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B1266785 : Blo 374761 1266785 := bstep (se 2 (by rfl) ⟨475044, by rfl⟩ : syracuseStep 1266785 = 950089) B950089
theorem B1930337 : Blo 374761 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B21083261 : Blo 374761 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B849095 : Blo 374761 849095 := bstep (se 1 (by rfl) ⟨636821, by rfl⟩ : syracuseStep 849095 = 1273643) B1273643
theorem B1291463 : Blo 374761 1291463 := bstep (se 1 (by rfl) ⟨968597, by rfl⟩ : syracuseStep 1291463 = 1937195) B1937195
theorem B2847959 : Blo 374761 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B1529047 : Blo 374761 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B562409 : Blo 374761 562409 := bstep (se 2 (by rfl) ⟨210903, by rfl⟩ : syracuseStep 562409 = 421807) B421807
theorem B570601 : Blo 374761 570601 := bstep (se 2 (by rfl) ⟨213975, by rfl⟩ : syracuseStep 570601 = 427951) B427951
theorem B562463 : Blo 374761 562463 := bstep (se 1 (by rfl) ⟨421847, by rfl⟩ : syracuseStep 562463 = 843695) B843695
theorem B849275 : Blo 374761 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B2168257 : Blo 374761 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B2905537 : Blo 374761 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B562631 : Blo 374761 562631 := bstep (se 1 (by rfl) ⟨421973, by rfl⟩ : syracuseStep 562631 = 843947) B843947
theorem B849401 : Blo 374761 849401 := bstep (se 2 (by rfl) ⟨318525, by rfl⟩ : syracuseStep 849401 = 637051) B637051
theorem B1897991 : Blo 374761 1897991 := bstep (se 1 (by rfl) ⟨1423493, by rfl⟩ : syracuseStep 1897991 = 2846987) B2846987
theorem B10835491 : Blo 374761 10835491 := bstep (se 1 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 10835491 = 16253237) B16253237
theorem B9655853 : Blo 374761 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B849491 : Blo 374761 849491 := bstep (se 1 (by rfl) ⟨637118, by rfl⟩ : syracuseStep 849491 = 1274237) B1274237
theorem B636511 : Blo 374761 636511 := bstep (se 1 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 636511 = 954767) B954767
theorem B382687 : Blo 374761 382687 := bstep (se 1 (by rfl) ⟨287015, by rfl⟩ : syracuseStep 382687 = 574031) B574031
theorem B849671 : Blo 374761 849671 := bstep (se 1 (by rfl) ⟨637253, by rfl⟩ : syracuseStep 849671 = 1274507) B1274507
theorem B562985 : Blo 374761 562985 := bstep (se 2 (by rfl) ⟨211119, by rfl⟩ : syracuseStep 562985 = 422239) B422239
theorem B562991 : Blo 374761 562991 := bstep (se 1 (by rfl) ⟨422243, by rfl⟩ : syracuseStep 562991 = 844487) B844487
theorem B636727 : Blo 374761 636727 := bstep (se 1 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 636727 = 955091) B955091
theorem B1431377 : Blo 374761 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B2029495 : Blo 374761 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B1898477 : Blo 374761 1898477 := bstep (se 3 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 1898477 = 711929) B711929
theorem B1808513 : Blo 374761 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B6166691 : Blo 374761 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B563465 : Blo 374761 563465 := bstep (se 2 (by rfl) ⟨211299, by rfl⟩ : syracuseStep 563465 = 422599) B422599
theorem B637193 : Blo 374761 637193 := bstep (se 2 (by rfl) ⟨238947, by rfl⟩ : syracuseStep 637193 = 477895) B477895
theorem B375071 : Blo 374761 375071 := bstep (se 1 (by rfl) ⟨281303, by rfl⟩ : syracuseStep 375071 = 562607) B562607
theorem B4290893 : Blo 374761 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B375131 : Blo 374761 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B375151 : Blo 374761 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B563567 : Blo 374761 563567 := bstep (se 1 (by rfl) ⟨422675, by rfl⟩ : syracuseStep 563567 = 845351) B845351
theorem B5421437 : Blo 374761 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B375207 : Blo 374761 375207 := bstep (se 1 (by rfl) ⟨281405, by rfl⟩ : syracuseStep 375207 = 562811) B562811
theorem B1268135 : Blo 374761 1268135 := bstep (se 1 (by rfl) ⟨951101, by rfl⟩ : syracuseStep 1268135 = 1902203) B1902203
theorem B1898963 : Blo 374761 1898963 := bstep (se 1 (by rfl) ⟨1424222, by rfl⟩ : syracuseStep 1898963 = 2848445) B2848445
theorem B375291 : Blo 374761 375291 := bstep (se 1 (by rfl) ⟨281468, by rfl⟩ : syracuseStep 375291 = 562937) B562937
theorem B1735231 : Blo 374761 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B375359 : Blo 374761 375359 := bstep (se 1 (by rfl) ⟨281519, by rfl⟩ : syracuseStep 375359 = 563039) B563039
theorem B2415167 : Blo 374761 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B375367 : Blo 374761 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B563783 : Blo 374761 563783 := bstep (se 1 (by rfl) ⟨422837, by rfl⟩ : syracuseStep 563783 = 845675) B845675
theorem B1268297 : Blo 374761 1268297 := bstep (se 2 (by rfl) ⟨475611, by rfl⟩ : syracuseStep 1268297 = 951223) B951223
theorem B4119113 : Blo 374761 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B424543 : Blo 374761 424543 := bstep (se 1 (by rfl) ⟨318407, by rfl⟩ : syracuseStep 424543 = 636815) B636815
theorem B563819 : Blo 374761 563819 := bstep (se 1 (by rfl) ⟨422864, by rfl⟩ : syracuseStep 563819 = 845729) B845729
theorem B7731845 : Blo 374761 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B2030255 : Blo 374761 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B375519 : Blo 374761 375519 := bstep (se 1 (by rfl) ⟨281639, by rfl⟩ : syracuseStep 375519 = 563279) B563279
theorem B1899287 : Blo 374761 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B375599 : Blo 374761 375599 := bstep (se 1 (by rfl) ⟨281699, by rfl⟩ : syracuseStep 375599 = 563399) B563399
theorem B564047 : Blo 374761 564047 := bstep (se 1 (by rfl) ⟨423035, by rfl⟩ : syracuseStep 564047 = 846071) B846071
theorem B2292623 : Blo 374761 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B375707 : Blo 374761 375707 := bstep (se 1 (by rfl) ⟨281780, by rfl⟩ : syracuseStep 375707 = 563561) B563561
theorem B711595 : Blo 374761 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B605099 : Blo 374761 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B375759 : Blo 374761 375759 := bstep (se 1 (by rfl) ⟨281819, by rfl⟩ : syracuseStep 375759 = 563639) B563639
theorem B375783 : Blo 374761 375783 := bstep (se 1 (by rfl) ⟨281837, by rfl⟩ : syracuseStep 375783 = 563675) B563675
theorem B3062771 : Blo 374761 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B1932427 : Blo 374761 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B711823 : Blo 374761 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B949391 : Blo 374761 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B1424573 : Blo 374761 1424573 := bstep (se 3 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 1424573 = 534215) B534215
theorem B474331 : Blo 374761 474331 := bstep (se 1 (by rfl) ⟨355748, by rfl⟩ : syracuseStep 474331 = 711497) B711497
theorem B711899 : Blo 374761 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B564443 : Blo 374761 564443 := bstep (se 1 (by rfl) ⟨423332, by rfl⟩ : syracuseStep 564443 = 846665) B846665
theorem B376095 : Blo 374761 376095 := bstep (se 1 (by rfl) ⟨282071, by rfl⟩ : syracuseStep 376095 = 564143) B564143
theorem B1146143 : Blo 374761 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B1768735 : Blo 374761 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B1908035 : Blo 374761 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B376155 : Blo 374761 376155 := bstep (se 1 (by rfl) ⟨282116, by rfl⟩ : syracuseStep 376155 = 564233) B564233
theorem B376175 : Blo 374761 376175 := bstep (se 1 (by rfl) ⟨282131, by rfl⟩ : syracuseStep 376175 = 564263) B564263
theorem B1670519 : Blo 374761 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B564617 : Blo 374761 564617 := bstep (se 2 (by rfl) ⟨211731, by rfl⟩ : syracuseStep 564617 = 423463) B423463
theorem B376231 : Blo 374761 376231 := bstep (se 1 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 376231 = 564347) B564347
theorem B5144057 : Blo 374761 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B376315 : Blo 374761 376315 := bstep (se 1 (by rfl) ⟨282236, by rfl⟩ : syracuseStep 376315 = 564473) B564473
theorem B458303 : Blo 374761 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B376383 : Blo 374761 376383 := bstep (se 1 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 376383 = 564575) B564575
theorem B376391 : Blo 374761 376391 := bstep (se 1 (by rfl) ⟨282293, by rfl⟩ : syracuseStep 376391 = 564587) B564587
theorem B679519 : Blo 374761 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B843425 : Blo 374761 843425 := bstep (se 2 (by rfl) ⟨316284, by rfl⟩ : syracuseStep 843425 = 632569) B632569
theorem B376543 : Blo 374761 376543 := bstep (se 1 (by rfl) ⟨282407, by rfl⟩ : syracuseStep 376543 = 564815) B564815
theorem B450283 : Blo 374761 450283 := bstep (se 1 (by rfl) ⟨337712, by rfl⟩ : syracuseStep 450283 = 675425) B675425
theorem B1629931 : Blo 374761 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B564971 : Blo 374761 564971 := bstep (se 1 (by rfl) ⟨423728, by rfl⟩ : syracuseStep 564971 = 847457) B847457
theorem B1908521 : Blo 374761 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B376623 : Blo 374761 376623 := bstep (se 1 (by rfl) ⟨282467, by rfl⟩ : syracuseStep 376623 = 564935) B564935
theorem B3604297 : Blo 374761 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B376731 : Blo 374761 376731 := bstep (se 1 (by rfl) ⟨282548, by rfl⟩ : syracuseStep 376731 = 565097) B565097
theorem B4636577 : Blo 374761 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B376783 : Blo 374761 376783 := bstep (se 1 (by rfl) ⟨282587, by rfl⟩ : syracuseStep 376783 = 565175) B565175
theorem B565199 : Blo 374761 565199 := bstep (se 1 (by rfl) ⟨423899, by rfl⟩ : syracuseStep 565199 = 847799) B847799
theorem B401383 : Blo 374761 401383 := bstep (se 1 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 401383 = 602075) B602075
theorem B376807 : Blo 374761 376807 := bstep (se 1 (by rfl) ⟨282605, by rfl⟩ : syracuseStep 376807 = 565211) B565211
theorem B2146337 : Blo 374761 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B1433639 : Blo 374761 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B4653121 : Blo 374761 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B4276313 : Blo 374761 4276313 := bstep (se 2 (by rfl) ⟨1603617, by rfl⟩ : syracuseStep 4276313 = 3207235) B3207235
theorem B6447275 : Blo 374761 6447275 := bstep (se 1 (by rfl) ⟨4835456, by rfl⟩ : syracuseStep 6447275 = 9670913) B9670913
theorem B377063 : Blo 374761 377063 := bstep (se 1 (by rfl) ⟨282797, by rfl⟩ : syracuseStep 377063 = 565595) B565595
theorem B565535 : Blo 374761 565535 := bstep (se 1 (by rfl) ⟨424151, by rfl⟩ : syracuseStep 565535 = 848303) B848303
theorem B565559 : Blo 374761 565559 := bstep (se 1 (by rfl) ⟨424169, by rfl⟩ : syracuseStep 565559 = 848339) B848339
theorem B9175355 : Blo 374761 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B35324219 : Blo 374761 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B56222029 : Blo 374761 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B565631 : Blo 374761 565631 := bstep (se 1 (by rfl) ⟨424223, by rfl⟩ : syracuseStep 565631 = 848447) B848447
theorem B377215 : Blo 374761 377215 := bstep (se 1 (by rfl) ⟨282911, by rfl⟩ : syracuseStep 377215 = 565823) B565823
theorem B1425863 : Blo 374761 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B565703 : Blo 374761 565703 := bstep (se 1 (by rfl) ⟨424277, by rfl⟩ : syracuseStep 565703 = 848555) B848555
theorem B803279 : Blo 374761 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B377295 : Blo 374761 377295 := bstep (se 1 (by rfl) ⟨282971, by rfl⟩ : syracuseStep 377295 = 565943) B565943
theorem B377447 : Blo 374761 377447 := bstep (se 1 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 377447 = 566171) B566171
theorem B4285061 : Blo 374761 4285061 := bstep (se 4 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 4285061 = 803449) B803449
theorem B1901231 : Blo 374761 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B844523 : Blo 374761 844523 := bstep (se 1 (by rfl) ⟨633392, by rfl⟩ : syracuseStep 844523 = 1266785) B1266785
theorem B1286891 : Blo 374761 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B566057 : Blo 374761 566057 := bstep (se 2 (by rfl) ⟨212271, by rfl⟩ : syracuseStep 566057 = 424543) B424543
theorem B566063 : Blo 374761 566063 := bstep (se 1 (by rfl) ⟨424547, by rfl⟩ : syracuseStep 566063 = 849095) B849095
theorem B860975 : Blo 374761 860975 := bstep (se 1 (by rfl) ⟨645731, by rfl⟩ : syracuseStep 860975 = 1291463) B1291463
theorem B4719455 : Blo 374761 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B377711 : Blo 374761 377711 := bstep (se 1 (by rfl) ⟨283283, by rfl⟩ : syracuseStep 377711 = 566567) B566567
theorem B1426319 : Blo 374761 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B566183 : Blo 374761 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B566267 : Blo 374761 566267 := bstep (se 1 (by rfl) ⟨424700, by rfl⟩ : syracuseStep 566267 = 849401) B849401
theorem B566327 : Blo 374761 566327 := bstep (se 1 (by rfl) ⟨424745, by rfl⟩ : syracuseStep 566327 = 849491) B849491
theorem B803945 : Blo 374761 803945 := bstep (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) B602959
theorem B1270889 : Blo 374761 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B2868371 : Blo 374761 2868371 := bstep (se 1 (by rfl) ⟨2151278, by rfl⟩ : syracuseStep 2868371 = 4302557) B4302557
theorem B566447 : Blo 374761 566447 := bstep (se 1 (by rfl) ⟨424835, by rfl⟩ : syracuseStep 566447 = 849671) B849671
theorem B2147543 : Blo 374761 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B951659 : Blo 374761 951659 := bstep (se 1 (by rfl) ⟨713744, by rfl⟩ : syracuseStep 951659 = 1427489) B1427489
theorem B1205675 : Blo 374761 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B25748941 : Blo 374761 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B1738199 : Blo 374761 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B1222141 : Blo 374761 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B2860595 : Blo 374761 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B3614291 : Blo 374761 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B845423 : Blo 374761 845423 := bstep (se 1 (by rfl) ⟨634067, by rfl⟩ : syracuseStep 845423 = 1268135) B1268135
theorem B632441 : Blo 374761 632441 := bstep (se 2 (by rfl) ⟨237165, by rfl⟩ : syracuseStep 632441 = 474331) B474331
theorem B1074809 : Blo 374761 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B845531 : Blo 374761 845531 := bstep (se 1 (by rfl) ⟨634148, by rfl⟩ : syracuseStep 845531 = 1268297) B1268297
theorem B2746075 : Blo 374761 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B476923 : Blo 374761 476923 := bstep (se 1 (by rfl) ⟨357692, by rfl⟩ : syracuseStep 476923 = 715385) B715385
theorem B5154563 : Blo 374761 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B1353503 : Blo 374761 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B1804207 : Blo 374761 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B403399 : Blo 374761 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B2287561 : Blo 374761 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B1271753 : Blo 374761 1271753 := bstep (se 2 (by rfl) ⟨476907, by rfl⟩ : syracuseStep 1271753 = 953815) B953815
theorem B2041847 : Blo 374761 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B632927 : Blo 374761 632927 := bstep (se 1 (by rfl) ⟨474695, by rfl⟩ : syracuseStep 632927 = 949391) B949391
theorem B764095 : Blo 374761 764095 := bstep (se 1 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 764095 = 1146143) B1146143
theorem B1272023 : Blo 374761 1272023 := bstep (se 1 (by rfl) ⟨954017, by rfl⟩ : syracuseStep 1272023 = 1908035) B1908035
theorem B6195491 : Blo 374761 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B600377 : Blo 374761 600377 := bstep (se 2 (by rfl) ⟨225141, by rfl⟩ : syracuseStep 600377 = 450283) B450283
theorem B10971449 : Blo 374761 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B2173241 : Blo 374761 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B3246427 : Blo 374761 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B2034077 : Blo 374761 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B1427975 : Blo 374761 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B1272347 : Blo 374761 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B2705993 : Blo 374761 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B3091051 : Blo 374761 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B535177 : Blo 374761 535177 := bstep (se 2 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 535177 = 401383) B401383
theorem B1354427 : Blo 374761 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B2026295 : Blo 374761 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B846647 : Blo 374761 846647 := bstep (se 1 (by rfl) ⟨634985, by rfl⟩ : syracuseStep 846647 = 1269971) B1269971
theorem B846827 : Blo 374761 846827 := bstep (se 1 (by rfl) ⟨635120, by rfl⟩ : syracuseStep 846827 = 1270241) B1270241
theorem B535673 : Blo 374761 535673 := bstep (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) B401755
theorem B3624101 : Blo 374761 3624101 := bstep (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) B679519
theorem B1527119 : Blo 374761 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B2436439 : Blo 374761 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B634223 : Blo 374761 634223 := bstep (se 1 (by rfl) ⟨475667, by rfl⟩ : syracuseStep 634223 = 951335) B951335
theorem B1273211 : Blo 374761 1273211 := bstep (se 1 (by rfl) ⟨954908, by rfl⟩ : syracuseStep 1273211 = 1909817) B1909817
theorem B2313641 : Blo 374761 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B2035289 : Blo 374761 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B634459 : Blo 374761 634459 := bstep (se 1 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 634459 = 951689) B951689
theorem B1265327 : Blo 374761 1265327 := bstep (se 1 (by rfl) ⟨948995, by rfl⟩ : syracuseStep 1265327 = 1897991) B1897991
theorem B634601 : Blo 374761 634601 := bstep (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) B475951
theorem B20598533 : Blo 374761 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B13676303 : Blo 374761 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B847655 : Blo 374761 847655 := bstep (se 1 (by rfl) ⟨635741, by rfl⟩ : syracuseStep 847655 = 1271483) B1271483
theorem B954251 : Blo 374761 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B1265651 : Blo 374761 1265651 := bstep (se 1 (by rfl) ⟨949238, by rfl⟩ : syracuseStep 1265651 = 1898477) B1898477
theorem B4567049 : Blo 374761 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B2404403 : Blo 374761 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B4812857 : Blo 374761 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B9433253 : Blo 374761 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B2576569 : Blo 374761 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B716987 : Blo 374761 716987 := bstep (se 1 (by rfl) ⟨537740, by rfl⟩ : syracuseStep 716987 = 1075481) B1075481
theorem B536863 : Blo 374761 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B1265975 : Blo 374761 1265975 := bstep (se 1 (by rfl) ⟨949481, by rfl⟩ : syracuseStep 1265975 = 1898963) B1898963
theorem B1610111 : Blo 374761 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B13054445 : Blo 374761 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B2142713 : Blo 374761 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B1266191 : Blo 374761 1266191 := bstep (se 1 (by rfl) ⟨949643, by rfl⟩ : syracuseStep 1266191 = 1899287) B1899287
theorem B1143391 : Blo 374761 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1528415 : Blo 374761 1528415 := bstep (se 1 (by rfl) ⟨1146311, by rfl⟩ : syracuseStep 1528415 = 2292623) B2292623
theorem B8163989 : Blo 374761 8163989 := bstep (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) B382687
theorem B4076203 : Blo 374761 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B14447321 : Blo 374761 14447321 := bstep (se 2 (by rfl) ⟨5417745, by rfl⟩ : syracuseStep 14447321 = 10835491) B10835491
theorem B635627 : Blo 374761 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B1274615 : Blo 374761 1274615 := bstep (se 1 (by rfl) ⟨955961, by rfl⟩ : syracuseStep 1274615 = 1911923) B1911923
theorem B848681 : Blo 374761 848681 := bstep (se 2 (by rfl) ⟨318255, by rfl⟩ : syracuseStep 848681 = 636511) B636511
theorem B2863997 : Blo 374761 2863997 := bstep (se 3 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 2863997 = 1073999) B1073999
theorem B3429371 : Blo 374761 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B848951 : Blo 374761 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B848969 : Blo 374761 848969 := bstep (se 2 (by rfl) ⟨318363, by rfl⟩ : syracuseStep 848969 = 636727) B636727
theorem B4805729 : Blo 374761 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B562283 : Blo 374761 562283 := bstep (se 1 (by rfl) ⟨421712, by rfl⟩ : syracuseStep 562283 = 843425) B843425
theorem B9311377 : Blo 374761 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B652463 : Blo 374761 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B636079 : Blo 374761 636079 := bstep (se 1 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 636079 = 954119) B954119
theorem B10810583 : Blo 374761 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B562523 : Blo 374761 562523 := bstep (se 1 (by rfl) ⟨421892, by rfl⟩ : syracuseStep 562523 = 843785) B843785
theorem B955739 : Blo 374761 955739 := bstep (se 1 (by rfl) ⟨716804, by rfl⟩ : syracuseStep 955739 = 1433609) B1433609
theorem B1070491 : Blo 374761 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B1267271 : Blo 374761 1267271 := bstep (se 1 (by rfl) ⟨950453, by rfl⟩ : syracuseStep 1267271 = 1900907) B1900907
theorem B562799 : Blo 374761 562799 := bstep (se 1 (by rfl) ⟨422099, by rfl⟩ : syracuseStep 562799 = 844199) B844199
theorem B423535 : Blo 374761 423535 := bstep (se 1 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 423535 = 635303) B635303
theorem B562871 : Blo 374761 562871 := bstep (se 1 (by rfl) ⟨422153, by rfl⟩ : syracuseStep 562871 = 844307) B844307
theorem B636599 : Blo 374761 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B562907 : Blo 374761 562907 := bstep (se 1 (by rfl) ⟨422180, by rfl⟩ : syracuseStep 562907 = 844361) B844361
theorem B423643 : Blo 374761 423643 := bstep (se 1 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 423643 = 635465) B635465
theorem B563081 : Blo 374761 563081 := bstep (se 2 (by rfl) ⟨211155, by rfl⟩ : syracuseStep 563081 = 422311) B422311
theorem B3618755 : Blo 374761 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B1611751 : Blo 374761 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B563183 : Blo 374761 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B374767 : Blo 374761 374767 := bstep (se 1 (by rfl) ⟨281075, by rfl⟩ : syracuseStep 374767 = 562151) B562151
theorem B1013743 : Blo 374761 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B4626497 : Blo 374761 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2144353 : Blo 374761 2144353 := bstep (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) B1608265
theorem B1898639 : Blo 374761 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B374939 : Blo 374761 374939 := bstep (se 1 (by rfl) ⟨281204, by rfl⟩ : syracuseStep 374939 = 562409) B562409
theorem B374975 : Blo 374761 374975 := bstep (se 1 (by rfl) ⟨281231, by rfl⟩ : syracuseStep 374975 = 562463) B562463
theorem B563435 : Blo 374761 563435 := bstep (se 1 (by rfl) ⟨422576, by rfl⟩ : syracuseStep 563435 = 845153) B845153
theorem B563495 : Blo 374761 563495 := bstep (se 1 (by rfl) ⟨422621, by rfl⟩ : syracuseStep 563495 = 845243) B845243
theorem B375087 : Blo 374761 375087 := bstep (se 1 (by rfl) ⟨281315, by rfl⟩ : syracuseStep 375087 = 562631) B562631
theorem B23517539 : Blo 374761 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B563579 : Blo 374761 563579 := bstep (se 1 (by rfl) ⟨422684, by rfl⟩ : syracuseStep 563579 = 845369) B845369
theorem B1268243 : Blo 374761 1268243 := bstep (se 1 (by rfl) ⟨951182, by rfl⟩ : syracuseStep 1268243 = 1902365) B1902365
theorem B375323 : Blo 374761 375323 := bstep (se 1 (by rfl) ⟨281492, by rfl⟩ : syracuseStep 375323 = 562985) B562985
theorem B375327 : Blo 374761 375327 := bstep (se 1 (by rfl) ⟨281495, by rfl⟩ : syracuseStep 375327 = 562991) B562991
theorem B948793 : Blo 374761 948793 := bstep (se 2 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 948793 = 711595) B711595
theorem B8460935 : Blo 374761 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B563849 : Blo 374761 563849 := bstep (se 2 (by rfl) ⟨211443, by rfl⟩ : syracuseStep 563849 = 422887) B422887
theorem B4840073 : Blo 374761 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B4111127 : Blo 374761 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B564023 : Blo 374761 564023 := bstep (se 1 (by rfl) ⟨423017, by rfl⟩ : syracuseStep 564023 = 846035) B846035
theorem B645943 : Blo 374761 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B5413715 : Blo 374761 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B375643 : Blo 374761 375643 := bstep (se 1 (by rfl) ⟨281732, by rfl⟩ : syracuseStep 375643 = 563465) B563465
theorem B564059 : Blo 374761 564059 := bstep (se 1 (by rfl) ⟨423044, by rfl⟩ : syracuseStep 564059 = 846089) B846089
theorem B424795 : Blo 374761 424795 := bstep (se 1 (by rfl) ⟨318596, by rfl⟩ : syracuseStep 424795 = 637193) B637193
theorem B949097 : Blo 374761 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B375711 : Blo 374761 375711 := bstep (se 1 (by rfl) ⟨281783, by rfl⟩ : syracuseStep 375711 = 563567) B563567
theorem B2038729 : Blo 374761 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B760801 : Blo 374761 760801 := bstep (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) B570601
theorem B564203 : Blo 374761 564203 := bstep (se 1 (by rfl) ⟨423152, by rfl⟩ : syracuseStep 564203 = 846305) B846305
theorem B375855 : Blo 374761 375855 := bstep (se 1 (by rfl) ⟨281891, by rfl⟩ : syracuseStep 375855 = 563783) B563783
theorem B3628097 : Blo 374761 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B375879 : Blo 374761 375879 := bstep (se 1 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 375879 = 563819) B563819
theorem B1203329 : Blo 374761 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B4775057 : Blo 374761 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B564407 : Blo 374761 564407 := bstep (se 1 (by rfl) ⟨423305, by rfl⟩ : syracuseStep 564407 = 846611) B846611
theorem B376031 : Blo 374761 376031 := bstep (se 1 (by rfl) ⟨282023, by rfl⟩ : syracuseStep 376031 = 564047) B564047
theorem B2891009 : Blo 374761 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B3874049 : Blo 374761 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B564647 : Blo 374761 564647 := bstep (se 1 (by rfl) ⟨423485, by rfl⟩ : syracuseStep 564647 = 846971) B846971
theorem B949715 : Blo 374761 949715 := bstep (se 1 (by rfl) ⟨712286, by rfl⟩ : syracuseStep 949715 = 1424573) B1424573
theorem B474599 : Blo 374761 474599 := bstep (se 1 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 474599 = 711899) B711899
theorem B376295 : Blo 374761 376295 := bstep (se 1 (by rfl) ⟨282221, by rfl⟩ : syracuseStep 376295 = 564443) B564443
theorem B564731 : Blo 374761 564731 := bstep (se 1 (by rfl) ⟨423548, by rfl⟩ : syracuseStep 564731 = 847097) B847097
theorem B1113679 : Blo 374761 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B376411 : Blo 374761 376411 := bstep (se 1 (by rfl) ⟨282308, by rfl⟩ : syracuseStep 376411 = 564617) B564617
theorem B564827 : Blo 374761 564827 := bstep (se 1 (by rfl) ⟨423620, by rfl⟩ : syracuseStep 564827 = 847241) B847241
theorem B843407 : Blo 374761 843407 := bstep (se 1 (by rfl) ⟨632555, by rfl⟩ : syracuseStep 843407 = 1265111) B1265111
theorem B564911 : Blo 374761 564911 := bstep (se 1 (by rfl) ⟨423683, by rfl⟩ : syracuseStep 564911 = 847367) B847367
theorem B843497 : Blo 374761 843497 := bstep (se 2 (by rfl) ⟨316311, by rfl⟩ : syracuseStep 843497 = 632623) B632623
theorem B565031 : Blo 374761 565031 := bstep (se 1 (by rfl) ⟨423773, by rfl⟩ : syracuseStep 565031 = 847547) B847547
theorem B376647 : Blo 374761 376647 := bstep (se 1 (by rfl) ⟨282485, by rfl⟩ : syracuseStep 376647 = 564971) B564971
theorem B565115 : Blo 374761 565115 := bstep (se 1 (by rfl) ⟨423836, by rfl⟩ : syracuseStep 565115 = 847673) B847673
theorem B376799 : Blo 374761 376799 := bstep (se 1 (by rfl) ⟨282599, by rfl⟩ : syracuseStep 376799 = 565199) B565199
theorem B2850875 : Blo 374761 2850875 := bstep (se 1 (by rfl) ⟨2138156, by rfl⟩ : syracuseStep 2850875 = 4276313) B4276313
theorem B2859137 : Blo 374761 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B377023 : Blo 374761 377023 := bstep (se 1 (by rfl) ⟨282767, by rfl⟩ : syracuseStep 377023 = 565535) B565535
theorem B843983 : Blo 374761 843983 := bstep (se 1 (by rfl) ⟨632987, by rfl⟩ : syracuseStep 843983 = 1265975) B1265975
theorem B377039 : Blo 374761 377039 := bstep (se 1 (by rfl) ⟨282779, by rfl⟩ : syracuseStep 377039 = 565559) B565559
theorem B1073407 : Blo 374761 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B377087 : Blo 374761 377087 := bstep (se 1 (by rfl) ⟨282815, by rfl⟩ : syracuseStep 377087 = 565631) B565631
theorem B950575 : Blo 374761 950575 := bstep (se 1 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 950575 = 1425863) B1425863
theorem B377135 : Blo 374761 377135 := bstep (se 1 (by rfl) ⟨282851, by rfl⟩ : syracuseStep 377135 = 565703) B565703
theorem B844127 : Blo 374761 844127 := bstep (se 1 (by rfl) ⟨633095, by rfl⟩ : syracuseStep 844127 = 1266191) B1266191
theorem B565787 : Blo 374761 565787 := bstep (se 1 (by rfl) ⟨424340, by rfl⟩ : syracuseStep 565787 = 848681) B848681
theorem B377371 : Blo 374761 377371 := bstep (se 1 (by rfl) ⟨283028, by rfl⟩ : syracuseStep 377371 = 566057) B566057
theorem B377375 : Blo 374761 377375 := bstep (se 1 (by rfl) ⟨283031, by rfl⟩ : syracuseStep 377375 = 566063) B566063
theorem B573983 : Blo 374761 573983 := bstep (se 1 (by rfl) ⟨430487, by rfl⟩ : syracuseStep 573983 = 860975) B860975
theorem B3146303 : Blo 374761 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B1909331 : Blo 374761 1909331 := bstep (se 1 (by rfl) ⟨1431998, by rfl⟩ : syracuseStep 1909331 = 2863997) B2863997
theorem B950879 : Blo 374761 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B377455 : Blo 374761 377455 := bstep (se 1 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 377455 = 566183) B566183
theorem B2286247 : Blo 374761 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B377511 : Blo 374761 377511 := bstep (se 1 (by rfl) ⟨283133, by rfl⟩ : syracuseStep 377511 = 566267) B566267
theorem B7709357 : Blo 374761 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B565967 : Blo 374761 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B377551 : Blo 374761 377551 := bstep (se 1 (by rfl) ⟨283163, by rfl⟩ : syracuseStep 377551 = 566327) B566327
theorem B565979 : Blo 374761 565979 := bstep (se 1 (by rfl) ⟨424484, by rfl⟩ : syracuseStep 565979 = 848969) B848969
theorem B3203819 : Blo 374761 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B434975 : Blo 374761 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B377631 : Blo 374761 377631 := bstep (se 1 (by rfl) ⟨283223, by rfl⟩ : syracuseStep 377631 = 566447) B566447
theorem B1524521 : Blo 374761 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B4121401 : Blo 374761 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B803783 : Blo 374761 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B844847 : Blo 374761 844847 := bstep (se 1 (by rfl) ⟨633635, by rfl⟩ : syracuseStep 844847 = 1267271) B1267271
theorem B2409527 : Blo 374761 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B861257 : Blo 374761 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B5424205 : Blo 374761 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B6169709 : Blo 374761 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B566393 : Blo 374761 566393 := bstep (se 2 (by rfl) ⟨212397, by rfl⟩ : syracuseStep 566393 = 424795) B424795
theorem B902335 : Blo 374761 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B1361231 : Blo 374761 1361231 := bstep (se 1 (by rfl) ⟨1020923, by rfl⟩ : syracuseStep 1361231 = 2041847) B2041847
theorem B4130327 : Blo 374761 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B951983 : Blo 374761 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B845495 : Blo 374761 845495 := bstep (se 1 (by rfl) ⟨634121, by rfl⟩ : syracuseStep 845495 = 1268243) B1268243
theorem B1803995 : Blo 374761 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B902951 : Blo 374761 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B1427321 : Blo 374761 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B632731 : Blo 374761 632731 := bstep (se 1 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 632731 = 949097) B949097
theorem B2418731 : Blo 374761 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B1484905 : Blo 374761 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B845945 : Blo 374761 845945 := bstep (se 2 (by rfl) ⟨317229, by rfl⟩ : syracuseStep 845945 = 634459) B634459
theorem B2582699 : Blo 374761 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1018079 : Blo 374761 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B633143 : Blo 374761 633143 := bstep (se 1 (by rfl) ⟨474857, by rfl⟩ : syracuseStep 633143 = 949715) B949715
theorem B13732355 : Blo 374761 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B3050081 : Blo 374761 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B2149001 : Blo 374761 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B6204161 : Blo 374761 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B477991 : Blo 374761 477991 := bstep (se 1 (by rfl) ⟨358493, by rfl⟩ : syracuseStep 477991 = 716987) B716987
theorem B3435425 : Blo 374761 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B1018793 : Blo 374761 1018793 := bstep (se 2 (by rfl) ⟨382047, by rfl⟩ : syracuseStep 1018793 = 764095) B764095
theorem B535519 : Blo 374761 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B1428461 : Blo 374761 1428461 := bstep (se 3 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 1428461 = 535673) B535673
theorem B8702963 : Blo 374761 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B1428475 : Blo 374761 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B715817 : Blo 374761 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B1018943 : Blo 374761 1018943 := bstep (se 1 (by rfl) ⟨764207, by rfl⟩ : syracuseStep 1018943 = 1528415) B1528415
theorem B5442659 : Blo 374761 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B4328569 : Blo 374761 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B2854277 : Blo 374761 2854277 := bstep (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) B535177
theorem B847259 : Blo 374761 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B1265057 : Blo 374761 1265057 := bstep (se 2 (by rfl) ⟨474396, by rfl⟩ : syracuseStep 1265057 = 948793) B948793
theorem B1912247 : Blo 374761 1912247 := bstep (se 1 (by rfl) ⟨1434185, by rfl⟩ : syracuseStep 1912247 = 2868371) B2868371
theorem B1601005 : Blo 374761 1601005 := bstep (se 3 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 1601005 = 600377) B600377
theorem B5795309 : Blo 374761 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B5434937 : Blo 374761 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B634439 : Blo 374761 634439 := bstep (se 1 (by rfl) ⟨475829, by rfl⟩ : syracuseStep 634439 = 951659) B951659
theorem B1158799 : Blo 374761 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B421627 : Blo 374761 421627 := bstep (se 1 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 421627 = 632441) B632441
theorem B716539 : Blo 374761 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B1265597 : Blo 374761 1265597 := bstep (se 3 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 1265597 = 474599) B474599
theorem B2412503 : Blo 374761 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B847835 : Blo 374761 847835 := bstep (se 1 (by rfl) ⟨635876, by rfl⟩ : syracuseStep 847835 = 1271753) B1271753
theorem B3084331 : Blo 374761 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B421951 : Blo 374761 421951 := bstep (se 1 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 421951 = 632927) B632927
theorem B1265759 : Blo 374761 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B848015 : Blo 374761 848015 := bstep (se 1 (by rfl) ⟨636011, by rfl⟩ : syracuseStep 848015 = 1272023) B1272023
theorem B12415169 : Blo 374761 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B848105 : Blo 374761 848105 := bstep (se 2 (by rfl) ⟨318039, by rfl⟩ : syracuseStep 848105 = 636079) B636079
theorem B848231 : Blo 374761 848231 := bstep (se 1 (by rfl) ⟨636173, by rfl⟩ : syracuseStep 848231 = 1272347) B1272347
theorem B5640623 : Blo 374761 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B3248585 : Blo 374761 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B2740751 : Blo 374761 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B3609143 : Blo 374761 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B3183371 : Blo 374761 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B422815 : Blo 374761 422815 := bstep (se 1 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 422815 = 634223) B634223
theorem B848807 : Blo 374761 848807 := bstep (se 1 (by rfl) ⟨636605, by rfl⟩ : syracuseStep 848807 = 1273211) B1273211
theorem B635897 : Blo 374761 635897 := bstep (se 2 (by rfl) ⟨238461, by rfl⟩ : syracuseStep 635897 = 476923) B476923
theorem B2151461 : Blo 374761 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B1356859 : Blo 374761 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B562271 : Blo 374761 562271 := bstep (se 1 (by rfl) ⟨421703, by rfl⟩ : syracuseStep 562271 = 843407) B843407
theorem B562331 : Blo 374761 562331 := bstep (se 1 (by rfl) ⟨421748, by rfl⟩ : syracuseStep 562331 = 843497) B843497
theorem B423067 : Blo 374761 423067 := bstep (se 1 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 423067 = 634601) B634601
theorem B2405609 : Blo 374761 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B636167 : Blo 374761 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B3044699 : Blo 374761 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B1430891 : Blo 374761 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B955759 : Blo 374761 955759 := bstep (se 1 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 955759 = 1433639) B1433639
theorem B1602935 : Blo 374761 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B3208571 : Blo 374761 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B6288835 : Blo 374761 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B4298183 : Blo 374761 4298183 := bstep (se 1 (by rfl) ⟨3223637, by rfl⟩ : syracuseStep 4298183 = 6447275) B6447275
theorem B6116903 : Blo 374761 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B2143853 : Blo 374761 2143853 := bstep (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) B803945
theorem B2856707 : Blo 374761 2856707 := bstep (se 1 (by rfl) ⟨2142530, by rfl⟩ : syracuseStep 2856707 = 4285061) B4285061
theorem B1267487 : Blo 374761 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B9631547 : Blo 374761 9631547 := bstep (se 1 (by rfl) ⟨7223660, by rfl⟩ : syracuseStep 9631547 = 14447321) B14447321
theorem B563015 : Blo 374761 563015 := bstep (se 1 (by rfl) ⟨422261, by rfl⟩ : syracuseStep 563015 = 844523) B844523
theorem B857927 : Blo 374761 857927 := bstep (se 1 (by rfl) ⟨643445, by rfl⟩ : syracuseStep 857927 = 1286891) B1286891
theorem B423751 : Blo 374761 423751 := bstep (se 1 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 423751 = 635627) B635627
theorem B849743 : Blo 374761 849743 := bstep (se 1 (by rfl) ⟨637307, by rfl⟩ : syracuseStep 849743 = 1274615) B1274615
theorem B374855 : Blo 374761 374855 := bstep (se 1 (by rfl) ⟨281141, by rfl⟩ : syracuseStep 374855 = 562283) B562283
theorem B7207055 : Blo 374761 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B1431695 : Blo 374761 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B94197917 : Blo 374761 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B375015 : Blo 374761 375015 := bstep (se 1 (by rfl) ⟨281261, by rfl⟩ : syracuseStep 375015 = 562523) B562523
theorem B637159 : Blo 374761 637159 := bstep (se 1 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 637159 = 955739) B955739
theorem B1907063 : Blo 374761 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B375199 : Blo 374761 375199 := bstep (se 1 (by rfl) ⟨281399, by rfl⟩ : syracuseStep 375199 = 562799) B562799
theorem B563615 : Blo 374761 563615 := bstep (se 1 (by rfl) ⟨422711, by rfl⟩ : syracuseStep 563615 = 845423) B845423
theorem B375247 : Blo 374761 375247 := bstep (se 1 (by rfl) ⟨281435, by rfl⟩ : syracuseStep 375247 = 562871) B562871
theorem B424399 : Blo 374761 424399 := bstep (se 1 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 424399 = 636599) B636599
theorem B375271 : Blo 374761 375271 := bstep (se 1 (by rfl) ⟨281453, by rfl⟩ : syracuseStep 375271 = 562907) B562907
theorem B563687 : Blo 374761 563687 := bstep (se 1 (by rfl) ⟨422765, by rfl⟩ : syracuseStep 563687 = 845531) B845531
theorem B375387 : Blo 374761 375387 := bstep (se 1 (by rfl) ⟨281540, by rfl⟩ : syracuseStep 375387 = 563081) B563081
theorem B2718305 : Blo 374761 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1014401 : Blo 374761 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B375455 : Blo 374761 375455 := bstep (se 1 (by rfl) ⟨281591, by rfl⟩ : syracuseStep 375455 = 563183) B563183
theorem B375623 : Blo 374761 375623 := bstep (se 1 (by rfl) ⟨281717, by rfl⟩ : syracuseStep 375623 = 563435) B563435
theorem B375663 : Blo 374761 375663 := bstep (se 1 (by rfl) ⟨281747, by rfl⟩ : syracuseStep 375663 = 563495) B563495
theorem B7314299 : Blo 374761 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B15678359 : Blo 374761 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B375719 : Blo 374761 375719 := bstep (se 1 (by rfl) ⟨281789, by rfl⟩ : syracuseStep 375719 = 563579) B563579
theorem B299850821 : Blo 374761 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B375899 : Blo 374761 375899 := bstep (se 1 (by rfl) ⟨281924, by rfl⟩ : syracuseStep 375899 = 563849) B563849
theorem B3226715 : Blo 374761 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B1350863 : Blo 374761 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B376015 : Blo 374761 376015 := bstep (se 1 (by rfl) ⟨282011, by rfl⟩ : syracuseStep 376015 = 564023) B564023
theorem B564431 : Blo 374761 564431 := bstep (se 1 (by rfl) ⟨423323, by rfl⟩ : syracuseStep 564431 = 846647) B846647
theorem B376039 : Blo 374761 376039 := bstep (se 1 (by rfl) ⟨282029, by rfl⟩ : syracuseStep 376039 = 564059) B564059
theorem B34331921 : Blo 374761 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B376135 : Blo 374761 376135 := bstep (se 1 (by rfl) ⟨282101, by rfl⟩ : syracuseStep 376135 = 564203) B564203
theorem B564551 : Blo 374761 564551 := bstep (se 1 (by rfl) ⟨423413, by rfl⟩ : syracuseStep 564551 = 846827) B846827
theorem B1629521 : Blo 374761 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B13745501 : Blo 374761 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B802219 : Blo 374761 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B2416067 : Blo 374761 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B376271 : Blo 374761 376271 := bstep (se 1 (by rfl) ⟨282203, by rfl⟩ : syracuseStep 376271 = 564407) B564407
theorem B564713 : Blo 374761 564713 := bstep (se 2 (by rfl) ⟨211767, by rfl⟩ : syracuseStep 564713 = 423535) B423535
theorem B376431 : Blo 374761 376431 := bstep (se 1 (by rfl) ⟨282323, by rfl⟩ : syracuseStep 376431 = 564647) B564647
theorem B3661433 : Blo 374761 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B564857 : Blo 374761 564857 := bstep (se 2 (by rfl) ⟨211821, by rfl⟩ : syracuseStep 564857 = 423643) B423643
theorem B376487 : Blo 374761 376487 := bstep (se 1 (by rfl) ⟨282365, by rfl⟩ : syracuseStep 376487 = 564731) B564731
theorem B376551 : Blo 374761 376551 := bstep (se 1 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 376551 = 564827) B564827
theorem B843551 : Blo 374761 843551 := bstep (se 1 (by rfl) ⟨632663, by rfl⟩ : syracuseStep 843551 = 1265327) B1265327
theorem B376607 : Blo 374761 376607 := bstep (se 1 (by rfl) ⟨282455, by rfl⟩ : syracuseStep 376607 = 564911) B564911
theorem B9117535 : Blo 374761 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B376687 : Blo 374761 376687 := bstep (se 1 (by rfl) ⟨282515, by rfl⟩ : syracuseStep 376687 = 565031) B565031
theorem B565103 : Blo 374761 565103 := bstep (se 1 (by rfl) ⟨423827, by rfl⟩ : syracuseStep 565103 = 847655) B847655
theorem B376743 : Blo 374761 376743 := bstep (se 1 (by rfl) ⟨282557, by rfl⟩ : syracuseStep 376743 = 565115) B565115
theorem B1351657 : Blo 374761 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B843767 : Blo 374761 843767 := bstep (se 1 (by rfl) ⟨632825, by rfl⟩ : syracuseStep 843767 = 1265651) B1265651
theorem B1900583 : Blo 374761 1900583 := bstep (se 1 (by rfl) ⟨1425437, by rfl⟩ : syracuseStep 1900583 = 2850875) B2850875
theorem B4112441 : Blo 374761 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B843839 : Blo 374761 843839 := bstep (se 1 (by rfl) ⟨632879, by rfl⟩ : syracuseStep 843839 = 1265759) B1265759
theorem B565343 : Blo 374761 565343 := bstep (se 1 (by rfl) ⟨424007, by rfl⟩ : syracuseStep 565343 = 848015) B848015
theorem B1908845 : Blo 374761 1908845 := bstep (se 3 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 1908845 = 715817) B715817
theorem B565403 : Blo 374761 565403 := bstep (se 1 (by rfl) ⟨424052, by rfl⟩ : syracuseStep 565403 = 848105) B848105
theorem B565487 : Blo 374761 565487 := bstep (se 1 (by rfl) ⟨424115, by rfl⟩ : syracuseStep 565487 = 848231) B848231
theorem B3760415 : Blo 374761 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B377191 : Blo 374761 377191 := bstep (se 1 (by rfl) ⟨282893, by rfl⟩ : syracuseStep 377191 = 565787) B565787
theorem B2097535 : Blo 374761 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B377311 : Blo 374761 377311 := bstep (se 1 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 377311 = 565967) B565967
theorem B377319 : Blo 374761 377319 := bstep (se 1 (by rfl) ⟨282989, by rfl⟩ : syracuseStep 377319 = 565979) B565979
theorem B2122247 : Blo 374761 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B565865 : Blo 374761 565865 := bstep (se 2 (by rfl) ⟨212199, by rfl⟩ : syracuseStep 565865 = 424399) B424399
theorem B565871 : Blo 374761 565871 := bstep (se 1 (by rfl) ⟨424403, by rfl⟩ : syracuseStep 565871 = 848807) B848807
theorem B1434307 : Blo 374761 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B574171 : Blo 374761 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B4113139 : Blo 374761 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B377595 : Blo 374761 377595 := bstep (se 1 (by rfl) ⟨283196, by rfl⟩ : syracuseStep 377595 = 566393) B566393
theorem B3048329 : Blo 374761 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2139047 : Blo 374761 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B2753551 : Blo 374761 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B844991 : Blo 374761 844991 := bstep (se 1 (by rfl) ⟨633743, by rfl⟩ : syracuseStep 844991 = 1267487) B1267487
theorem B566495 : Blo 374761 566495 := bstep (se 1 (by rfl) ⟨424871, by rfl⟩ : syracuseStep 566495 = 849743) B849743
theorem B951547 : Blo 374761 951547 := bstep (se 1 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 951547 = 1427321) B1427321
theorem B714025 : Blo 374761 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B1271375 : Blo 374761 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B2705069 : Blo 374761 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B2033387 : Blo 374761 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B1812203 : Blo 374761 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B4876199 : Blo 374761 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B952307 : Blo 374761 952307 := bstep (se 1 (by rfl) ⟨714230, by rfl⟩ : syracuseStep 952307 = 1428461) B1428461
theorem B5801975 : Blo 374761 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B4065389 : Blo 374761 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B1902851 : Blo 374761 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B3623291 : Blo 374761 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B1608335 : Blo 374761 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B1612487 : Blo 374761 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B8276779 : Blo 374761 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B6425405 : Blo 374761 6425405 := bstep (se 3 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 6425405 = 2409527) B2409527
theorem B2165723 : Blo 374761 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B1272887 : Blo 374761 1272887 := bstep (se 1 (by rfl) ⟨954665, by rfl⟩ : syracuseStep 1272887 = 1909331) B1909331
theorem B633919 : Blo 374761 633919 := bstep (se 1 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 633919 = 950879) B950879
theorem B5139571 : Blo 374761 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B953927 : Blo 374761 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B1068623 : Blo 374761 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1429235 : Blo 374761 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B634655 : Blo 374761 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B1904471 : Blo 374761 1904471 := bstep (se 1 (by rfl) ⟨1428353, by rfl⟩ : syracuseStep 1904471 = 2856707) B2856707
theorem B601967 : Blo 374761 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B1904633 : Blo 374761 1904633 := bstep (se 2 (by rfl) ⟨714237, by rfl⟩ : syracuseStep 1904633 = 1428475) B1428475
theorem B4804703 : Blo 374761 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B954463 : Blo 374761 954463 := bstep (se 1 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 954463 = 1431695) B1431695
theorem B5771425 : Blo 374761 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B422095 : Blo 374761 422095 := bstep (se 1 (by rfl) ⟨316571, by rfl⟩ : syracuseStep 422095 = 633143) B633143
theorem B9154903 : Blo 374761 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B1274345 : Blo 374761 1274345 := bstep (se 2 (by rfl) ⟨477879, by rfl⟩ : syracuseStep 1274345 = 955759) B955759
theorem B1069625 : Blo 374761 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B8385113 : Blo 374761 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B2290283 : Blo 374761 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B2134673 : Blo 374761 2134673 := bstep (se 2 (by rfl) ⟨800502, by rfl⟩ : syracuseStep 2134673 = 1601005) B1601005
theorem B2151143 : Blo 374761 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B1159933 : Blo 374761 1159933 := bstep (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) B434975
theorem B1545065 : Blo 374761 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1086347 : Blo 374761 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B9163667 : Blo 374761 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1274831 : Blo 374761 1274831 := bstep (se 1 (by rfl) ⟨956123, by rfl⟩ : syracuseStep 1274831 = 1912247) B1912247
theorem B1610711 : Blo 374761 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B3863539 : Blo 374761 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B562169 : Blo 374761 562169 := bstep (se 2 (by rfl) ⟨210813, by rfl⟩ : syracuseStep 562169 = 421627) B421627
theorem B955385 : Blo 374761 955385 := bstep (se 2 (by rfl) ⟨358269, by rfl⟩ : syracuseStep 955385 = 716539) B716539
theorem B422959 : Blo 374761 422959 := bstep (se 1 (by rfl) ⟨317219, by rfl⟩ : syracuseStep 422959 = 634439) B634439
theorem B2143421 : Blo 374761 2143421 := bstep (se 3 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 2143421 = 803783) B803783
theorem B562367 : Blo 374761 562367 := bstep (se 1 (by rfl) ⟨421775, by rfl⟩ : syracuseStep 562367 = 843551) B843551
theorem B562511 : Blo 374761 562511 := bstep (se 1 (by rfl) ⟨421883, by rfl⟩ : syracuseStep 562511 = 843767) B843767
theorem B562601 : Blo 374761 562601 := bstep (se 2 (by rfl) ⟨210975, by rfl⟩ : syracuseStep 562601 = 421951) B421951
theorem B1906091 : Blo 374761 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B562655 : Blo 374761 562655 := bstep (se 1 (by rfl) ⟨421991, by rfl⟩ : syracuseStep 562655 = 843983) B843983
theorem B1979873 : Blo 374761 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B29234677 : Blo 374761 29234677 := bstep (se 5 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 29234677 = 2740751) B2740751
theorem B562751 : Blo 374761 562751 := bstep (se 1 (by rfl) ⟨422063, by rfl⟩ : syracuseStep 562751 = 844127) B844127
theorem B849545 : Blo 374761 849545 := bstep (se 2 (by rfl) ⟨318579, by rfl⟩ : syracuseStep 849545 = 637159) B637159
theorem B1431209 : Blo 374761 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B382655 : Blo 374761 382655 := bstep (se 1 (by rfl) ⟨286991, by rfl⟩ : syracuseStep 382655 = 573983) B573983
theorem B2406095 : Blo 374761 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B1267433 : Blo 374761 1267433 := bstep (se 2 (by rfl) ⟨475287, by rfl⟩ : syracuseStep 1267433 = 950575) B950575
theorem B6887197 : Blo 374761 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B2135879 : Blo 374761 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B423931 : Blo 374761 423931 := bstep (se 1 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 423931 = 635897) B635897
theorem B563231 : Blo 374761 563231 := bstep (se 1 (by rfl) ⟨422423, by rfl⟩ : syracuseStep 563231 = 844847) B844847
theorem B374847 : Blo 374761 374847 := bstep (se 1 (by rfl) ⟨281135, by rfl⟩ : syracuseStep 374847 = 562271) B562271
theorem B374887 : Blo 374761 374887 := bstep (se 1 (by rfl) ⟨281165, by rfl⟩ : syracuseStep 374887 = 562331) B562331
theorem B1603739 : Blo 374761 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B424111 : Blo 374761 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B907487 : Blo 374761 907487 := bstep (se 1 (by rfl) ⟨680615, by rfl⟩ : syracuseStep 907487 = 1361231) B1361231
theorem B2029799 : Blo 374761 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B2865455 : Blo 374761 2865455 := bstep (se 1 (by rfl) ⟨2149091, by rfl⟩ : syracuseStep 2865455 = 4298183) B4298183
theorem B4077935 : Blo 374761 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B637321 : Blo 374761 637321 := bstep (se 2 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 637321 = 477991) B477991
theorem B5495201 : Blo 374761 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B563663 : Blo 374761 563663 := bstep (se 1 (by rfl) ⟨422747, by rfl⟩ : syracuseStep 563663 = 845495) B845495
theorem B1202663 : Blo 374761 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B6421031 : Blo 374761 6421031 := bstep (se 1 (by rfl) ⟨4815773, by rfl⟩ : syracuseStep 6421031 = 9631547) B9631547
theorem B563753 : Blo 374761 563753 := bstep (se 2 (by rfl) ⟨211407, by rfl⟩ : syracuseStep 563753 = 422815) B422815
theorem B375343 : Blo 374761 375343 := bstep (se 1 (by rfl) ⟨281507, by rfl⟩ : syracuseStep 375343 = 563015) B563015
theorem B571951 : Blo 374761 571951 := bstep (se 1 (by rfl) ⟨428963, by rfl⟩ : syracuseStep 571951 = 857927) B857927
theorem B1809145 : Blo 374761 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B563963 : Blo 374761 563963 := bstep (se 1 (by rfl) ⟨422972, by rfl⟩ : syracuseStep 563963 = 845945) B845945
theorem B7232273 : Blo 374761 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B62798611 : Blo 374761 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B678719 : Blo 374761 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B564089 : Blo 374761 564089 := bstep (se 2 (by rfl) ⟨211533, by rfl⟩ : syracuseStep 564089 = 423067) B423067
theorem B1203113 : Blo 374761 1203113 := bstep (se 2 (by rfl) ⟨451167, by rfl⟩ : syracuseStep 1203113 = 902335) B902335
theorem B375743 : Blo 374761 375743 := bstep (se 1 (by rfl) ⟨281807, by rfl⟩ : syracuseStep 375743 = 563615) B563615
theorem B375791 : Blo 374761 375791 := bstep (se 1 (by rfl) ⟨281843, by rfl⟩ : syracuseStep 375791 = 563687) B563687
theorem B1432667 : Blo 374761 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B4136107 : Blo 374761 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B10452239 : Blo 374761 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B679195 : Blo 374761 679195 := bstep (se 1 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 679195 = 1018793) B1018793
theorem B679295 : Blo 374761 679295 := bstep (se 1 (by rfl) ⟨509471, by rfl⟩ : syracuseStep 679295 = 1018943) B1018943
theorem B199900547 : Blo 374761 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B3628439 : Blo 374761 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B900575 : Blo 374761 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B376287 : Blo 374761 376287 := bstep (se 1 (by rfl) ⟨282215, by rfl⟩ : syracuseStep 376287 = 564431) B564431
theorem B22887947 : Blo 374761 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B376367 : Blo 374761 376367 := bstep (se 1 (by rfl) ⟨282275, by rfl⟩ : syracuseStep 376367 = 564551) B564551
theorem B564839 : Blo 374761 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B843371 : Blo 374761 843371 := bstep (se 1 (by rfl) ⟨632528, by rfl⟩ : syracuseStep 843371 = 1265057) B1265057
theorem B376475 : Blo 374761 376475 := bstep (se 1 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 376475 = 564713) B564713
theorem B2440955 : Blo 374761 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B376571 : Blo 374761 376571 := bstep (se 1 (by rfl) ⟨282428, by rfl⟩ : syracuseStep 376571 = 564857) B564857
theorem B565001 : Blo 374761 565001 := bstep (se 2 (by rfl) ⟨211875, by rfl⟩ : syracuseStep 565001 = 423751) B423751
theorem B12156713 : Blo 374761 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B843641 : Blo 374761 843641 := bstep (se 2 (by rfl) ⟨316365, by rfl⟩ : syracuseStep 843641 = 632731) B632731
theorem B376735 : Blo 374761 376735 := bstep (se 1 (by rfl) ⟨282551, by rfl⟩ : syracuseStep 376735 = 565103) B565103
theorem B843731 : Blo 374761 843731 := bstep (se 1 (by rfl) ⟨632798, by rfl⟩ : syracuseStep 843731 = 1265597) B1265597
theorem B1802209 : Blo 374761 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B565223 : Blo 374761 565223 := bstep (se 1 (by rfl) ⟨423917, by rfl⟩ : syracuseStep 565223 = 847835) B847835
theorem B3203135 : Blo 374761 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B376895 : Blo 374761 376895 := bstep (se 1 (by rfl) ⟨282671, by rfl⟩ : syracuseStep 376895 = 565343) B565343
theorem B376935 : Blo 374761 376935 := bstep (se 1 (by rfl) ⟨282701, by rfl⟩ : syracuseStep 376935 = 565403) B565403
theorem B376991 : Blo 374761 376991 := bstep (se 1 (by rfl) ⟨282743, by rfl⟩ : syracuseStep 376991 = 565487) B565487
theorem B2506943 : Blo 374761 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B565481 : Blo 374761 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B377243 : Blo 374761 377243 := bstep (se 1 (by rfl) ⟨282932, by rfl⟩ : syracuseStep 377243 = 565865) B565865
theorem B377247 : Blo 374761 377247 := bstep (se 1 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 377247 = 565871) B565871
theorem B12206537 : Blo 374761 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B1434095 : Blo 374761 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B2032219 : Blo 374761 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B1426031 : Blo 374761 1426031 := bstep (se 1 (by rfl) ⟨1069523, by rfl⟩ : syracuseStep 1426031 = 2139047) B2139047
theorem B1073807 : Blo 374761 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B377663 : Blo 374761 377663 := bstep (se 1 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 377663 = 566495) B566495
theorem B1270727 : Blo 374761 1270727 := bstep (se 1 (by rfl) ⟨953045, by rfl⟩ : syracuseStep 1270727 = 1906091) B1906091
theorem B1319915 : Blo 374761 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B83731481 : Blo 374761 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B11035705 : Blo 374761 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B566363 : Blo 374761 566363 := bstep (se 1 (by rfl) ⟨424772, by rfl⟩ : syracuseStep 566363 = 849545) B849545
theorem B1803379 : Blo 374761 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B844955 : Blo 374761 844955 := bstep (se 1 (by rfl) ⟨633716, by rfl⟩ : syracuseStep 844955 = 1267433) B1267433
theorem B3867983 : Blo 374761 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B3671401 : Blo 374761 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B845225 : Blo 374761 845225 := bstep (se 2 (by rfl) ⟨316959, by rfl⟩ : syracuseStep 845225 = 633919) B633919
theorem B2852333 : Blo 374761 2852333 := bstep (se 3 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 2852333 = 1069625) B1069625
theorem B1353199 : Blo 374761 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B1910303 : Blo 374761 1910303 := bstep (se 1 (by rfl) ⟨1432727, by rfl⟩ : syracuseStep 1910303 = 2865455) B2865455
theorem B5514809 : Blo 374761 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B3663467 : Blo 374761 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B952033 : Blo 374761 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B1074991 : Blo 374761 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B452479 : Blo 374761 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B1443815 : Blo 374761 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B38979569 : Blo 374761 38979569 := bstep (se 2 (by rfl) ⟨14617338, by rfl⟩ : syracuseStep 38979569 = 29234677) B29234677
theorem B452863 : Blo 374761 452863 := bstep (se 1 (by rfl) ⟨339647, by rfl⟩ : syracuseStep 452863 = 679295) B679295
theorem B2418959 : Blo 374761 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B600383 : Blo 374761 600383 := bstep (se 1 (by rfl) ⟨450287, by rfl⟩ : syracuseStep 600383 = 900575) B900575
theorem B952823 : Blo 374761 952823 := bstep (se 1 (by rfl) ⟨714617, by rfl⟩ : syracuseStep 952823 = 1429235) B1429235
theorem B8104475 : Blo 374761 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B2402945 : Blo 374761 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B1272563 : Blo 374761 1272563 := bstep (se 1 (by rfl) ⟨954422, by rfl⟩ : syracuseStep 1272563 = 1908845) B1908845
theorem B1272617 : Blo 374761 1272617 := bstep (se 2 (by rfl) ⟨477231, by rfl⟩ : syracuseStep 1272617 = 954463) B954463
theorem B7695233 : Blo 374761 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B3050405 : Blo 374761 3050405 := bstep (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) B571951
theorem B5590075 : Blo 374761 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B1526855 : Blo 374761 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B2796713 : Blo 374761 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B724231 : Blo 374761 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B1428947 : Blo 374761 1428947 := bstep (se 1 (by rfl) ⟨1071710, by rfl⟩ : syracuseStep 1428947 = 2143421) B2143421
theorem B1912409 : Blo 374761 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B5484185 : Blo 374761 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B2412193 : Blo 374761 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B847583 : Blo 374761 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B954139 : Blo 374761 954139 := bstep (se 1 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 954139 = 1431209) B1431209
theorem B1355591 : Blo 374761 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B1208135 : Blo 374761 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B634871 : Blo 374761 634871 := bstep (se 1 (by rfl) ⟨476153, by rfl⟩ : syracuseStep 634871 = 952307) B952307
theorem B1069159 : Blo 374761 1069159 := bstep (se 1 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 1069159 = 1603739) B1603739
theorem B6852761 : Blo 374761 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B4280687 : Blo 374761 4280687 := bstep (se 1 (by rfl) ⟨3210515, by rfl⟩ : syracuseStep 4280687 = 6421031) B6421031
theorem B905593 : Blo 374761 905593 := bstep (se 2 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 905593 = 679195) B679195
theorem B1020413 : Blo 374761 1020413 := bstep (se 3 (by rfl) ⟨191327, by rfl⟩ : syracuseStep 1020413 = 382655) B382655
theorem B4821515 : Blo 374761 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B848591 : Blo 374761 848591 := bstep (se 1 (by rfl) ⟨636443, by rfl⟩ : syracuseStep 848591 = 1272887) B1272887
theorem B955111 : Blo 374761 955111 := bstep (se 1 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 955111 = 1432667) B1432667
theorem B6968159 : Blo 374761 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B15258631 : Blo 374761 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B635951 : Blo 374761 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B562247 : Blo 374761 562247 := bstep (se 1 (by rfl) ⟨421685, by rfl⟩ : syracuseStep 562247 = 843371) B843371
theorem B1627303 : Blo 374761 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B423103 : Blo 374761 423103 := bstep (se 1 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 423103 = 634655) B634655
theorem B562427 : Blo 374761 562427 := bstep (se 1 (by rfl) ⟨421820, by rfl⟩ : syracuseStep 562427 = 843641) B843641
theorem B562487 : Blo 374761 562487 := bstep (se 1 (by rfl) ⟨421865, by rfl⟩ : syracuseStep 562487 = 843731) B843731
theorem B1267055 : Blo 374761 1267055 := bstep (se 1 (by rfl) ⟨950291, by rfl⟩ : syracuseStep 1267055 = 1900583) B1900583
theorem B2741627 : Blo 374761 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B562559 : Blo 374761 562559 := bstep (se 1 (by rfl) ⟨421919, by rfl⟩ : syracuseStep 562559 = 843839) B843839
theorem B562793 : Blo 374761 562793 := bstep (se 2 (by rfl) ⟨211047, by rfl⟩ : syracuseStep 562793 = 422095) B422095
theorem B849563 : Blo 374761 849563 := bstep (se 1 (by rfl) ⟨637172, by rfl⟩ : syracuseStep 849563 = 1274345) B1274345
theorem B1414831 : Blo 374761 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1423115 : Blo 374761 1423115 := bstep (se 1 (by rfl) ⟨1067336, by rfl⟩ : syracuseStep 1423115 = 2134673) B2134673
theorem B849761 : Blo 374761 849761 := bstep (se 2 (by rfl) ⟨318660, by rfl⟩ : syracuseStep 849761 = 637321) B637321
theorem B1030043 : Blo 374761 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B6109111 : Blo 374761 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B849887 : Blo 374761 849887 := bstep (se 1 (by rfl) ⟨637415, by rfl⟩ : syracuseStep 849887 = 1274831) B1274831
theorem B374779 : Blo 374761 374779 := bstep (se 1 (by rfl) ⟨281084, by rfl⟩ : syracuseStep 374779 = 562169) B562169
theorem B636923 : Blo 374761 636923 := bstep (se 1 (by rfl) ⟨477692, by rfl⟩ : syracuseStep 636923 = 955385) B955385
theorem B374911 : Blo 374761 374911 := bstep (se 1 (by rfl) ⟨281183, by rfl⟩ : syracuseStep 374911 = 562367) B562367
theorem B563327 : Blo 374761 563327 := bstep (se 1 (by rfl) ⟨422495, by rfl⟩ : syracuseStep 563327 = 844991) B844991
theorem B375007 : Blo 374761 375007 := bstep (se 1 (by rfl) ⟨281255, by rfl⟩ : syracuseStep 375007 = 562511) B562511
theorem B375067 : Blo 374761 375067 := bstep (se 1 (by rfl) ⟨281300, by rfl⟩ : syracuseStep 375067 = 562601) B562601
theorem B375103 : Blo 374761 375103 := bstep (se 1 (by rfl) ⟨281327, by rfl⟩ : syracuseStep 375103 = 562655) B562655
theorem B1546577 : Blo 374761 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B375167 : Blo 374761 375167 := bstep (se 1 (by rfl) ⟨281375, by rfl⟩ : syracuseStep 375167 = 562751) B562751
theorem B1604063 : Blo 374761 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B3062245 : Blo 374761 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B1423919 : Blo 374761 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B3250799 : Blo 374761 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B5151385 : Blo 374761 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B375487 : Blo 374761 375487 := bstep (se 1 (by rfl) ⟨281615, by rfl⟩ : syracuseStep 375487 = 563231) B563231
theorem B563945 : Blo 374761 563945 := bstep (se 2 (by rfl) ⟨211479, by rfl⟩ : syracuseStep 563945 = 422959) B422959
theorem B2710259 : Blo 374761 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B604991 : Blo 374761 604991 := bstep (se 1 (by rfl) ⟨453743, by rfl⟩ : syracuseStep 604991 = 907487) B907487
theorem B1268567 : Blo 374761 1268567 := bstep (se 1 (by rfl) ⟨951425, by rfl⟩ : syracuseStep 1268567 = 1902851) B1902851
theorem B2718623 : Blo 374761 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B2415527 : Blo 374761 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B375775 : Blo 374761 375775 := bstep (se 1 (by rfl) ⟨281831, by rfl⟩ : syracuseStep 375775 = 563663) B563663
theorem B801775 : Blo 374761 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B1268729 : Blo 374761 1268729 := bstep (se 2 (by rfl) ⟨475773, by rfl⟩ : syracuseStep 1268729 = 951547) B951547
theorem B375835 : Blo 374761 375835 := bstep (se 1 (by rfl) ⟨281876, by rfl⟩ : syracuseStep 375835 = 563753) B563753
theorem B1072223 : Blo 374761 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B375975 : Blo 374761 375975 := bstep (se 1 (by rfl) ⟨281981, by rfl⟩ : syracuseStep 375975 = 563963) B563963
theorem B4283603 : Blo 374761 4283603 := bstep (se 1 (by rfl) ⟨3212702, by rfl⟩ : syracuseStep 4283603 = 6425405) B6425405
theorem B376059 : Blo 374761 376059 := bstep (se 1 (by rfl) ⟨282044, by rfl⟩ : syracuseStep 376059 = 564089) B564089
theorem B802075 : Blo 374761 802075 := bstep (se 1 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 802075 = 1203113) B1203113
theorem B133267031 : Blo 374761 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B9182929 : Blo 374761 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B712415 : Blo 374761 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B376559 : Blo 374761 376559 := bstep (se 1 (by rfl) ⟨282419, by rfl⟩ : syracuseStep 376559 = 564839) B564839
theorem B376667 : Blo 374761 376667 := bstep (se 1 (by rfl) ⟨282500, by rfl⟩ : syracuseStep 376667 = 565001) B565001
theorem B1269647 : Blo 374761 1269647 := bstep (se 1 (by rfl) ⟨952235, by rfl⟩ : syracuseStep 1269647 = 1904471) B1904471
theorem B401311 : Blo 374761 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B376815 : Blo 374761 376815 := bstep (se 1 (by rfl) ⟨282611, by rfl⟩ : syracuseStep 376815 = 565223) B565223
theorem B565241 : Blo 374761 565241 := bstep (se 2 (by rfl) ⟨211965, by rfl⟩ : syracuseStep 565241 = 423931) B423931
theorem B1269755 : Blo 374761 1269755 := bstep (se 1 (by rfl) ⟨952316, by rfl⟩ : syracuseStep 1269755 = 1904633) B1904633
theorem B1425545 : Blo 374761 1425545 := bstep (se 2 (by rfl) ⟨534579, by rfl⟩ : syracuseStep 1425545 = 1069159) B1069159
theorem B376987 : Blo 374761 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B680275 : Blo 374761 680275 := bstep (se 1 (by rfl) ⟨510206, by rfl⟩ : syracuseStep 680275 = 1020413) B1020413
theorem B950687 : Blo 374761 950687 := bstep (se 1 (by rfl) ⟨713015, by rfl⟩ : syracuseStep 950687 = 1426031) B1426031
theorem B565727 : Blo 374761 565727 := bstep (se 1 (by rfl) ⟨424295, by rfl⟩ : syracuseStep 565727 = 848591) B848591
theorem B6685181 : Blo 374761 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B4645439 : Blo 374761 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B55820987 : Blo 374761 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B16286453 : Blo 374761 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B844703 : Blo 374761 844703 := bstep (se 1 (by rfl) ⟨633527, by rfl⟩ : syracuseStep 844703 = 1267055) B1267055
theorem B1901555 : Blo 374761 1901555 := bstep (se 1 (by rfl) ⟨1426166, by rfl⟩ : syracuseStep 1901555 = 2852333) B2852333
theorem B2442311 : Blo 374761 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B566375 : Blo 374761 566375 := bstep (se 1 (by rfl) ⟨424781, by rfl⟩ : syracuseStep 566375 = 849563) B849563
theorem B566507 : Blo 374761 566507 := bstep (se 1 (by rfl) ⟨424880, by rfl⟩ : syracuseStep 566507 = 849761) B849761
theorem B566591 : Blo 374761 566591 := bstep (se 1 (by rfl) ⟨424943, by rfl⟩ : syracuseStep 566591 = 849887) B849887
theorem B25986379 : Blo 374761 25986379 := bstep (se 1 (by rfl) ⟨19489784, by rfl⟩ : syracuseStep 25986379 = 38979569) B38979569
theorem B21611933 : Blo 374761 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B14714273 : Blo 374761 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B403327 : Blo 374761 403327 := bstep (se 1 (by rfl) ⟨302495, by rfl⟩ : syracuseStep 403327 = 604991) B604991
theorem B845711 : Blo 374761 845711 := bstep (se 1 (by rfl) ⟨634283, by rfl⟩ : syracuseStep 845711 = 1268567) B1268567
theorem B5130155 : Blo 374761 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B1812415 : Blo 374761 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B2033603 : Blo 374761 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B1804265 : Blo 374761 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B845819 : Blo 374761 845819 := bstep (se 1 (by rfl) ⟨634364, by rfl⟩ : syracuseStep 845819 = 1268729) B1268729
theorem B714815 : Blo 374761 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B3221693 : Blo 374761 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B1886441 : Blo 374761 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B952631 : Blo 374761 952631 := bstep (se 1 (by rfl) ⟨714473, by rfl⟩ : syracuseStep 952631 = 1428947) B1428947
theorem B1272185 : Blo 374761 1272185 := bstep (se 2 (by rfl) ⟨477069, by rfl⟩ : syracuseStep 1272185 = 954139) B954139
theorem B88844687 : Blo 374761 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B2746781 : Blo 374761 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B3656123 : Blo 374761 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B535081 : Blo 374761 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B903727 : Blo 374761 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B8145481 : Blo 374761 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B846431 : Blo 374761 846431 := bstep (se 1 (by rfl) ⟨634823, by rfl⟩ : syracuseStep 846431 = 1269647) B1269647
theorem B846503 : Blo 374761 846503 := bstep (se 1 (by rfl) ⟨634877, by rfl⟩ : syracuseStep 846503 = 1269755) B1269755
theorem B2853791 : Blo 374761 2853791 := bstep (se 1 (by rfl) ⟨2140343, by rfl⟩ : syracuseStep 2853791 = 4280687) B4280687
theorem B8137691 : Blo 374761 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B3214343 : Blo 374761 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B715871 : Blo 374761 715871 := bstep (se 1 (by rfl) ⟨536903, by rfl⟩ : syracuseStep 715871 = 1073807) B1073807
theorem B1207457 : Blo 374761 1207457 := bstep (se 2 (by rfl) ⟨452796, by rfl⟩ : syracuseStep 1207457 = 905593) B905593
theorem B847151 : Blo 374761 847151 := bstep (se 1 (by rfl) ⟨635363, by rfl⟩ : syracuseStep 847151 = 1270727) B1270727
theorem B4082993 : Blo 374761 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B376827 : Blo 374761 376827 := bstep (se 1 (by rfl) ⟨282620, by rfl⟩ : syracuseStep 376827 = 565241) B565241
theorem B1601021 : Blo 374761 1601021 := bstep (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) B600383
theorem B6868513 : Blo 374761 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1273481 : Blo 374761 1273481 := bstep (se 2 (by rfl) ⟨477555, by rfl⟩ : syracuseStep 1273481 = 955111) B955111
theorem B7311005 : Blo 374761 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1273535 : Blo 374761 1273535 := bstep (se 1 (by rfl) ⟨955151, by rfl⟩ : syracuseStep 1273535 = 1910303) B1910303
theorem B1069033 : Blo 374761 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B962543 : Blo 374761 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B20344841 : Blo 374761 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B2404505 : Blo 374761 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B1069375 : Blo 374761 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B635215 : Blo 374761 635215 := bstep (se 1 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 635215 = 952823) B952823
theorem B1069433 : Blo 374761 1069433 := bstep (se 2 (by rfl) ⟨401037, by rfl⟩ : syracuseStep 1069433 = 802075) B802075
theorem B2167199 : Blo 374761 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B1601963 : Blo 374761 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B4895201 : Blo 374761 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B1806839 : Blo 374761 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B848375 : Blo 374761 848375 := bstep (se 1 (by rfl) ⟨636281, by rfl⟩ : syracuseStep 848375 = 1272563) B1272563
theorem B848411 : Blo 374761 848411 := bstep (se 1 (by rfl) ⟨636308, by rfl⟩ : syracuseStep 848411 = 1272617) B1272617
theorem B1610351 : Blo 374761 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B1864475 : Blo 374761 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B2855735 : Blo 374761 2855735 := bstep (se 1 (by rfl) ⟨2141801, by rfl⟩ : syracuseStep 2855735 = 4283603) B4283603
theorem B3216257 : Blo 374761 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B12243905 : Blo 374761 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B1274939 : Blo 374761 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B603305 : Blo 374761 603305 := bstep (se 2 (by rfl) ⟨226239, by rfl⟩ : syracuseStep 603305 = 452479) B452479
theorem B3519773 : Blo 374761 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B423247 : Blo 374761 423247 := bstep (se 1 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 423247 = 634871) B634871
theorem B2135423 : Blo 374761 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B4568507 : Blo 374761 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B956063 : Blo 374761 956063 := bstep (se 1 (by rfl) ⟨717047, by rfl⟩ : syracuseStep 956063 = 1434095) B1434095
theorem B603817 : Blo 374761 603817 := bstep (se 2 (by rfl) ⟨226431, by rfl⟩ : syracuseStep 603817 = 452863) B452863
theorem B58824629 : Blo 374761 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B423967 : Blo 374761 423967 := bstep (se 1 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 423967 = 635951) B635951
theorem B374831 : Blo 374761 374831 := bstep (se 1 (by rfl) ⟨281123, by rfl⟩ : syracuseStep 374831 = 562247) B562247
theorem B563303 : Blo 374761 563303 := bstep (se 1 (by rfl) ⟨422477, by rfl⟩ : syracuseStep 563303 = 844955) B844955
theorem B2709625 : Blo 374761 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B374951 : Blo 374761 374951 := bstep (se 1 (by rfl) ⟨281213, by rfl⟩ : syracuseStep 374951 = 562427) B562427
theorem B374991 : Blo 374761 374991 := bstep (se 1 (by rfl) ⟨281243, by rfl⟩ : syracuseStep 374991 = 562487) B562487
theorem B2578655 : Blo 374761 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B375039 : Blo 374761 375039 := bstep (se 1 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 375039 = 562559) B562559
theorem B563483 : Blo 374761 563483 := bstep (se 1 (by rfl) ⟨422612, by rfl⟩ : syracuseStep 563483 = 845225) B845225
theorem B375195 : Blo 374761 375195 := bstep (se 1 (by rfl) ⟨281396, by rfl⟩ : syracuseStep 375195 = 562793) B562793
theorem B948743 : Blo 374761 948743 := bstep (se 1 (by rfl) ⟨711557, by rfl⟩ : syracuseStep 948743 = 1423115) B1423115
theorem B424615 : Blo 374761 424615 := bstep (se 1 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 424615 = 636923) B636923
theorem B7453433 : Blo 374761 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B375551 : Blo 374761 375551 := bstep (se 1 (by rfl) ⟨281663, by rfl⟩ : syracuseStep 375551 = 563327) B563327
theorem B1612639 : Blo 374761 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B2169737 : Blo 374761 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B1031051 : Blo 374761 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B564137 : Blo 374761 564137 := bstep (se 2 (by rfl) ⟨211551, by rfl⟩ : syracuseStep 564137 = 423103) B423103
theorem B965641 : Blo 374761 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B949279 : Blo 374761 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B375963 : Blo 374761 375963 := bstep (se 1 (by rfl) ⟨281972, by rfl⟩ : syracuseStep 375963 = 563945) B563945
theorem B377575 : Blo 374761 377575 := bstep (se 1 (by rfl) ⟨283181, by rfl⟩ : syracuseStep 377575 = 566363) B566363
theorem B1899773 : Blo 374761 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B1269377 : Blo 374761 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B1433321 : Blo 374761 1433321 := bstep (se 2 (by rfl) ⟨537495, by rfl⟩ : syracuseStep 1433321 = 1074991) B1074991
theorem B565055 : Blo 374761 565055 := bstep (se 1 (by rfl) ⟨423791, by rfl⟩ : syracuseStep 565055 = 847583) B847583
theorem B565289 : Blo 374761 565289 := bstep (se 2 (by rfl) ⟨211983, by rfl⟩ : syracuseStep 565289 = 423967) B423967
theorem B950363 : Blo 374761 950363 := bstep (se 1 (by rfl) ⟨712772, by rfl⟩ : syracuseStep 950363 = 1425545) B1425545
theorem B3612833 : Blo 374761 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B712955 : Blo 374761 712955 := bstep (se 1 (by rfl) ⟨534716, by rfl⟩ : syracuseStep 712955 = 1069433) B1069433
theorem B377151 : Blo 374761 377151 := bstep (se 1 (by rfl) ⟨282863, by rfl⟩ : syracuseStep 377151 = 565727) B565727
theorem B1204559 : Blo 374761 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B565583 : Blo 374761 565583 := bstep (se 1 (by rfl) ⟨424187, by rfl⟩ : syracuseStep 565583 = 848375) B848375
theorem B4456787 : Blo 374761 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B565607 : Blo 374761 565607 := bstep (se 1 (by rfl) ⟨424205, by rfl⟩ : syracuseStep 565607 = 848411) B848411
theorem B3096959 : Blo 374761 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B1073567 : Blo 374761 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B1425833 : Blo 374761 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B713441 : Blo 374761 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B1204969 : Blo 374761 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B402203 : Blo 374761 402203 := bstep (se 1 (by rfl) ⟨301652, by rfl⟩ : syracuseStep 402203 = 603305) B603305
theorem B377671 : Blo 374761 377671 := bstep (se 1 (by rfl) ⟨283253, by rfl⟩ : syracuseStep 377671 = 566507) B566507
theorem B377727 : Blo 374761 377727 := bstep (se 1 (by rfl) ⟨283295, by rfl⟩ : syracuseStep 377727 = 566591) B566591
theorem B3220357 : Blo 374761 3220357 := bstep (se 4 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 3220357 = 603817) B603817
theorem B566153 : Blo 374761 566153 := bstep (se 2 (by rfl) ⟨212307, by rfl⟩ : syracuseStep 566153 = 424615) B424615
theorem B39216419 : Blo 374761 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B1287521 : Blo 374761 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B476543 : Blo 374761 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B2147795 : Blo 374761 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B59229791 : Blo 374761 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B632495 : Blo 374761 632495 := bstep (se 1 (by rfl) ⟨474371, by rfl⟩ : syracuseStep 632495 = 948743) B948743
theorem B1902527 : Blo 374761 1902527 := bstep (se 1 (by rfl) ⟨1426895, by rfl⟩ : syracuseStep 1902527 = 2853791) B2853791
theorem B5425127 : Blo 374761 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B477247 : Blo 374761 477247 := bstep (se 1 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 477247 = 715871) B715871
theorem B804971 : Blo 374761 804971 := bstep (se 1 (by rfl) ⟨603728, by rfl⟩ : syracuseStep 804971 = 1207457) B1207457
theorem B2721995 : Blo 374761 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B1067347 : Blo 374761 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B846251 : Blo 374761 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B20122037 : Blo 374761 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B641695 : Blo 374761 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B1444799 : Blo 374761 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B633791 : Blo 374761 633791 := bstep (se 1 (by rfl) ⟨475343, by rfl⟩ : syracuseStep 633791 = 950687) B950687
theorem B1067975 : Blo 374761 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B846953 : Blo 374761 846953 := bstep (se 2 (by rfl) ⟨317607, by rfl⟩ : syracuseStep 846953 = 635215) B635215
theorem B10857635 : Blo 374761 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B1903823 : Blo 374761 1903823 := bstep (se 1 (by rfl) ⟨1427867, by rfl⟩ : syracuseStep 1903823 = 2855735) B2855735
theorem B8162603 : Blo 374761 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B2346515 : Blo 374761 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B9809515 : Blo 374761 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B2150185 : Blo 374761 2150185 := bstep (se 2 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 2150185 = 1612639) B1612639
theorem B13053869 : Blo 374761 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B3420103 : Blo 374761 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B1355735 : Blo 374761 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B1265705 : Blo 374761 1265705 := bstep (se 2 (by rfl) ⟨474639, by rfl⟩ : syracuseStep 1265705 = 949279) B949279
theorem B635087 : Blo 374761 635087 := bstep (se 1 (by rfl) ⟨476315, by rfl⟩ : syracuseStep 635087 = 952631) B952631
theorem B848123 : Blo 374761 848123 := bstep (se 1 (by rfl) ⟨636092, by rfl⟩ : syracuseStep 848123 = 1272185) B1272185
theorem B1831187 : Blo 374761 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B2437415 : Blo 374761 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B34648505 : Blo 374761 34648505 := bstep (se 2 (by rfl) ⟨12993189, by rfl⟩ : syracuseStep 34648505 = 25986379) B25986379
theorem B4968955 : Blo 374761 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B1446491 : Blo 374761 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B2142895 : Blo 374761 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B1266515 : Blo 374761 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B2749469 : Blo 374761 2749469 := bstep (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) B1031051
theorem B848987 : Blo 374761 848987 := bstep (se 1 (by rfl) ⟨636740, by rfl⟩ : syracuseStep 848987 = 1273481) B1273481
theorem B849023 : Blo 374761 849023 := bstep (se 1 (by rfl) ⟨636767, by rfl⟩ : syracuseStep 849023 = 1273535) B1273535
theorem B955547 : Blo 374761 955547 := bstep (se 1 (by rfl) ⟨716660, by rfl⟩ : syracuseStep 955547 = 1433321) B1433321
theorem B537769 : Blo 374761 537769 := bstep (se 2 (by rfl) ⟨201663, by rfl⟩ : syracuseStep 537769 = 403327) B403327
theorem B13563227 : Blo 374761 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B1603003 : Blo 374761 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B907033 : Blo 374761 907033 := bstep (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) B680275
theorem B37213991 : Blo 374761 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B1242983 : Blo 374761 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B2144171 : Blo 374761 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B563135 : Blo 374761 563135 := bstep (se 1 (by rfl) ⟨422351, by rfl⟩ : syracuseStep 563135 = 844703) B844703
theorem B1267703 : Blo 374761 1267703 := bstep (se 1 (by rfl) ⟨950777, by rfl⟩ : syracuseStep 1267703 = 1901555) B1901555
theorem B849959 : Blo 374761 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B1628207 : Blo 374761 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B10860641 : Blo 374761 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B1423615 : Blo 374761 1423615 := bstep (se 1 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 1423615 = 2135423) B2135423
theorem B14407955 : Blo 374761 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B3045671 : Blo 374761 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B637375 : Blo 374761 637375 := bstep (se 1 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 637375 = 956063) B956063
theorem B563807 : Blo 374761 563807 := bstep (se 1 (by rfl) ⟨422855, by rfl⟩ : syracuseStep 563807 = 845711) B845711
theorem B1202843 : Blo 374761 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B563879 : Blo 374761 563879 := bstep (se 1 (by rfl) ⟨422909, by rfl⟩ : syracuseStep 563879 = 845819) B845819
theorem B375535 : Blo 374761 375535 := bstep (se 1 (by rfl) ⟨281651, by rfl⟩ : syracuseStep 375535 = 563303) B563303
theorem B1719103 : Blo 374761 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B375655 : Blo 374761 375655 := bstep (se 1 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 375655 = 563483) B563483
theorem B564287 : Blo 374761 564287 := bstep (se 1 (by rfl) ⟨423215, by rfl⟩ : syracuseStep 564287 = 846431) B846431
theorem B564329 : Blo 374761 564329 := bstep (se 2 (by rfl) ⟨211623, by rfl⟩ : syracuseStep 564329 = 423247) B423247
theorem B564335 : Blo 374761 564335 := bstep (se 1 (by rfl) ⟨423251, by rfl⟩ : syracuseStep 564335 = 846503) B846503
theorem B377583 : Blo 374761 377583 := bstep (se 1 (by rfl) ⟨283187, by rfl⟩ : syracuseStep 377583 = 566375) B566375
theorem B376091 : Blo 374761 376091 := bstep (se 1 (by rfl) ⟨282068, by rfl⟩ : syracuseStep 376091 = 564137) B564137
theorem B9158017 : Blo 374761 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B564767 : Blo 374761 564767 := bstep (se 1 (by rfl) ⟨423575, by rfl⟩ : syracuseStep 564767 = 847151) B847151
theorem B4874003 : Blo 374761 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B376703 : Blo 374761 376703 := bstep (se 1 (by rfl) ⟨282527, by rfl⟩ : syracuseStep 376703 = 565055) B565055
theorem B2416553 : Blo 374761 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B1425377 : Blo 374761 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B843803 : Blo 374761 843803 := bstep (se 1 (by rfl) ⟨632852, by rfl⟩ : syracuseStep 843803 = 1265705) B1265705
theorem B376859 : Blo 374761 376859 := bstep (se 1 (by rfl) ⟨282644, by rfl⟩ : syracuseStep 376859 = 565289) B565289
theorem B7331917 : Blo 374761 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B2408555 : Blo 374761 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B475303 : Blo 374761 475303 := bstep (se 1 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 475303 = 712955) B712955
theorem B565415 : Blo 374761 565415 := bstep (se 1 (by rfl) ⟨424061, by rfl⟩ : syracuseStep 565415 = 848123) B848123
theorem B1220791 : Blo 374761 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B803039 : Blo 374761 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B377055 : Blo 374761 377055 := bstep (se 1 (by rfl) ⟨282791, by rfl⟩ : syracuseStep 377055 = 565583) B565583
theorem B377071 : Blo 374761 377071 := bstep (se 1 (by rfl) ⟨282803, by rfl⟩ : syracuseStep 377071 = 565607) B565607
theorem B950555 : Blo 374761 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B475627 : Blo 374761 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B844343 : Blo 374761 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B377435 : Blo 374761 377435 := bstep (se 1 (by rfl) ⟨283076, by rfl⟩ : syracuseStep 377435 = 566153) B566153
theorem B565991 : Blo 374761 565991 := bstep (se 1 (by rfl) ⟨424493, by rfl⟩ : syracuseStep 565991 = 848987) B848987
theorem B566015 : Blo 374761 566015 := bstep (se 1 (by rfl) ⟨424511, by rfl⟩ : syracuseStep 566015 = 849023) B849023
theorem B47539061 : Blo 374761 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B1606625 : Blo 374761 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B1270781 : Blo 374761 1270781 := bstep (se 3 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 1270781 = 476543) B476543
theorem B8258557 : Blo 374761 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B39486527 : Blo 374761 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B4293809 : Blo 374761 4293809 := bstep (se 2 (by rfl) ⟨1610178, by rfl⟩ : syracuseStep 4293809 = 3220357) B3220357
theorem B845135 : Blo 374761 845135 := bstep (se 1 (by rfl) ⟨633851, by rfl⟩ : syracuseStep 845135 = 1267703) B1267703
theorem B566639 : Blo 374761 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B5441735 : Blo 374761 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B3615293 : Blo 374761 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B8702579 : Blo 374761 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B633575 : Blo 374761 633575 := bstep (se 1 (by rfl) ⟨475181, by rfl⟩ : syracuseStep 633575 = 950363) B950363
theorem B1624943 : Blo 374761 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B715711 : Blo 374761 715711 := bstep (se 1 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 715711 = 1073567) B1073567
theorem B52317413 : Blo 374761 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B26144279 : Blo 374761 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B855593 : Blo 374761 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B421663 : Blo 374761 421663 := bstep (se 1 (by rfl) ⟨316247, by rfl⟩ : syracuseStep 421663 = 632495) B632495
theorem B24809327 : Blo 374761 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1429447 : Blo 374761 1429447 := bstep (se 1 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 1429447 = 2144171) B2144171
theorem B3616751 : Blo 374761 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B1085471 : Blo 374761 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B536647 : Blo 374761 536647 := bstep (se 1 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 536647 = 804971) B804971
theorem B1814663 : Blo 374761 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B9605303 : Blo 374761 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B717025 : Blo 374761 717025 := bstep (se 2 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 717025 = 537769) B537769
theorem B13414691 : Blo 374761 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B12210689 : Blo 374761 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B963199 : Blo 374761 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B422527 : Blo 374761 422527 := bstep (se 1 (by rfl) ⟨316895, by rfl⟩ : syracuseStep 422527 = 633791) B633791
theorem B7238423 : Blo 374761 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B3314621 : Blo 374761 3314621 := bstep (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) B1242983
theorem B1209377 : Blo 374761 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B3249335 : Blo 374761 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B4560137 : Blo 374761 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B1611035 : Blo 374761 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B636329 : Blo 374761 636329 := bstep (se 2 (by rfl) ⟨238623, by rfl⟩ : syracuseStep 636329 = 477247) B477247
theorem B423391 : Blo 374761 423391 := bstep (se 1 (by rfl) ⟨317543, by rfl⟩ : syracuseStep 423391 = 635087) B635087
theorem B23099003 : Blo 374761 23099003 := bstep (se 1 (by rfl) ⟨17324252, by rfl⟩ : syracuseStep 23099003 = 34648505) B34648505
theorem B1898153 : Blo 374761 1898153 := bstep (se 2 (by rfl) ⟨711807, by rfl⟩ : syracuseStep 1898153 = 1423615) B1423615
theorem B964327 : Blo 374761 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B1423129 : Blo 374761 1423129 := bstep (se 2 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 1423129 = 1067347) B1067347
theorem B849833 : Blo 374761 849833 := bstep (se 2 (by rfl) ⟨318687, by rfl⟩ : syracuseStep 849833 = 637375) B637375
theorem B6625273 : Blo 374761 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B2866913 : Blo 374761 2866913 := bstep (se 2 (by rfl) ⟨1075092, by rfl⟩ : syracuseStep 2866913 = 2150185) B2150185
theorem B637031 : Blo 374761 637031 := bstep (se 1 (by rfl) ⟨477773, by rfl⟩ : syracuseStep 637031 = 955547) B955547
theorem B9042151 : Blo 374761 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B2857193 : Blo 374761 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B858347 : Blo 374761 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B1431863 : Blo 374761 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B2292137 : Blo 374761 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B375423 : Blo 374761 375423 := bstep (se 1 (by rfl) ⟨281567, by rfl⟩ : syracuseStep 375423 = 563135) B563135
theorem B1268351 : Blo 374761 1268351 := bstep (se 1 (by rfl) ⟨951263, by rfl⟩ : syracuseStep 1268351 = 1902527) B1902527
theorem B7240427 : Blo 374761 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B2030447 : Blo 374761 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B564167 : Blo 374761 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B375871 : Blo 374761 375871 := bstep (se 1 (by rfl) ⟨281903, by rfl⟩ : syracuseStep 375871 = 563807) B563807
theorem B801895 : Blo 374761 801895 := bstep (se 1 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 801895 = 1202843) B1202843
theorem B375919 : Blo 374761 375919 := bstep (se 1 (by rfl) ⟨281939, by rfl⟩ : syracuseStep 375919 = 563879) B563879
theorem B2137337 : Blo 374761 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B711983 : Blo 374761 711983 := bstep (se 1 (by rfl) ⟨533987, by rfl⟩ : syracuseStep 711983 = 1067975) B1067975
theorem B376191 : Blo 374761 376191 := bstep (se 1 (by rfl) ⟨282143, by rfl⟩ : syracuseStep 376191 = 564287) B564287
theorem B376219 : Blo 374761 376219 := bstep (se 1 (by rfl) ⟨282164, by rfl⟩ : syracuseStep 376219 = 564329) B564329
theorem B564635 : Blo 374761 564635 := bstep (se 1 (by rfl) ⟨423476, by rfl⟩ : syracuseStep 564635 = 846953) B846953
theorem B1072541 : Blo 374761 1072541 := bstep (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) B402203
theorem B376223 : Blo 374761 376223 := bstep (se 1 (by rfl) ⟨282167, by rfl⟩ : syracuseStep 376223 = 564335) B564335
theorem B1269215 : Blo 374761 1269215 := bstep (se 1 (by rfl) ⟨951911, by rfl⟩ : syracuseStep 1269215 = 1903823) B1903823
theorem B1564343 : Blo 374761 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B376511 : Blo 374761 376511 := bstep (se 1 (by rfl) ⟨282383, by rfl⟩ : syracuseStep 376511 = 564767) B564767
theorem B950251 : Blo 374761 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B1605703 : Blo 374761 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B376943 : Blo 374761 376943 := bstep (se 1 (by rfl) ⟨282707, by rfl⟩ : syracuseStep 376943 = 565415) B565415
theorem B377327 : Blo 374761 377327 := bstep (se 1 (by rfl) ⟨282995, by rfl⟩ : syracuseStep 377327 = 565991) B565991
theorem B377343 : Blo 374761 377343 := bstep (se 1 (by rfl) ⟨283007, by rfl⟩ : syracuseStep 377343 = 566015) B566015
theorem B4825615 : Blo 374761 4825615 := bstep (se 1 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 4825615 = 7238423) B7238423
theorem B3040091 : Blo 374761 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B1074023 : Blo 374761 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B377759 : Blo 374761 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B2860109 : Blo 374761 2860109 := bstep (se 3 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 2860109 = 1072541) B1072541
theorem B566555 : Blo 374761 566555 := bstep (se 1 (by rfl) ⟨424916, by rfl⟩ : syracuseStep 566555 = 849833) B849833
theorem B11011409 : Blo 374761 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B2410195 : Blo 374761 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B5801719 : Blo 374761 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B845567 : Blo 374761 845567 := bstep (se 1 (by rfl) ⟨634175, by rfl⟩ : syracuseStep 845567 = 1268351) B1268351
theorem B4826951 : Blo 374761 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B1083295 : Blo 374761 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B1353631 : Blo 374761 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B846143 : Blo 374761 846143 := bstep (se 1 (by rfl) ⟨634607, by rfl⟩ : syracuseStep 846143 = 1269215) B1269215
theorem B1042895 : Blo 374761 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B1911275 : Blo 374761 1911275 := bstep (se 1 (by rfl) ⟨1433456, by rfl⟩ : syracuseStep 1911275 = 2866913) B2866913
theorem B9644669 : Blo 374761 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B8833697 : Blo 374761 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B723647 : Blo 374761 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B715529 : Blo 374761 715529 := bstep (se 2 (by rfl) ⟨268323, by rfl⟩ : syracuseStep 715529 = 536647) B536647
theorem B9775889 : Blo 374761 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B633703 : Blo 374761 633703 := bstep (se 1 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 633703 = 950555) B950555
theorem B633737 : Blo 374761 633737 := bstep (se 2 (by rfl) ⟨237651, by rfl⟩ : syracuseStep 633737 = 475303) B475303
theorem B2141437 : Blo 374761 2141437 := bstep (se 3 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 2141437 = 803039) B803039
theorem B634169 : Blo 374761 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B847187 : Blo 374761 847187 := bstep (se 1 (by rfl) ⟨635390, by rfl⟩ : syracuseStep 847187 = 1270781) B1270781
theorem B26324351 : Blo 374761 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B2862539 : Blo 374761 2862539 := bstep (se 1 (by rfl) ⟨2146904, by rfl⟩ : syracuseStep 2862539 = 4293809) B4293809
theorem B1265435 : Blo 374761 1265435 := bstep (se 1 (by rfl) ⟨949076, by rfl⟩ : syracuseStep 1265435 = 1898153) B1898153
theorem B954281 : Blo 374761 954281 := bstep (se 2 (by rfl) ⟨357855, by rfl⟩ : syracuseStep 954281 = 715711) B715711
theorem B1069193 : Blo 374761 1069193 := bstep (se 2 (by rfl) ⟨400947, by rfl⟩ : syracuseStep 1069193 = 801895) B801895
theorem B1904795 : Blo 374761 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B954575 : Blo 374761 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B1528091 : Blo 374761 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B422383 : Blo 374761 422383 := bstep (se 1 (by rfl) ⟨316787, by rfl⟩ : syracuseStep 422383 = 633575) B633575
theorem B34878275 : Blo 374761 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B17429519 : Blo 374761 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B570395 : Blo 374761 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B1897505 : Blo 374761 1897505 := bstep (se 2 (by rfl) ⟨711564, by rfl⟩ : syracuseStep 1897505 = 1423129) B1423129
theorem B562217 : Blo 374761 562217 := bstep (se 2 (by rfl) ⟨210831, by rfl⟩ : syracuseStep 562217 = 421663) B421663
theorem B1905929 : Blo 374761 1905929 := bstep (se 2 (by rfl) ⟨714723, by rfl⟩ : syracuseStep 1905929 = 1429447) B1429447
theorem B1267001 : Blo 374761 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B562535 : Blo 374761 562535 := bstep (se 1 (by rfl) ⟨421901, by rfl⟩ : syracuseStep 562535 = 843803) B843803
theorem B3225005 : Blo 374761 3225005 := bstep (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) B1209377
theorem B6403535 : Blo 374761 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B1627721 : Blo 374761 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B956033 : Blo 374761 956033 := bstep (se 2 (by rfl) ⟨358512, by rfl⟩ : syracuseStep 956033 = 717025) B717025
theorem B12056201 : Blo 374761 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B8140459 : Blo 374761 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B4839101 : Blo 374761 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B562895 : Blo 374761 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B8664893 : Blo 374761 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B31692707 : Blo 374761 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B2209747 : Blo 374761 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B1071083 : Blo 374761 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B35772509 : Blo 374761 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B1284265 : Blo 374761 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B563369 : Blo 374761 563369 := bstep (se 2 (by rfl) ⟨211263, by rfl⟩ : syracuseStep 563369 = 422527) B422527
theorem B563423 : Blo 374761 563423 := bstep (se 1 (by rfl) ⟨422567, by rfl⟩ : syracuseStep 563423 = 845135) B845135
theorem B424219 : Blo 374761 424219 := bstep (se 1 (by rfl) ⟨318164, by rfl⟩ : syracuseStep 424219 = 636329) B636329
theorem B15399335 : Blo 374761 15399335 := bstep (se 1 (by rfl) ⟨11549501, by rfl⟩ : syracuseStep 15399335 = 23099003) B23099003
theorem B424687 : Blo 374761 424687 := bstep (se 1 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 424687 = 637031) B637031
theorem B3627823 : Blo 374761 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B572231 : Blo 374761 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B564521 : Blo 374761 564521 := bstep (se 2 (by rfl) ⟨211695, by rfl⟩ : syracuseStep 564521 = 423391) B423391
theorem B376111 : Blo 374761 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B1424891 : Blo 374761 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B474655 : Blo 374761 474655 := bstep (se 1 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 474655 = 711983) B711983
theorem B376423 : Blo 374761 376423 := bstep (se 1 (by rfl) ⟨282317, by rfl⟩ : syracuseStep 376423 = 564635) B564635
theorem B1285769 : Blo 374761 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B16539551 : Blo 374761 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B712795 : Blo 374761 712795 := bstep (se 1 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 712795 = 1069193) B1069193
theorem B1269863 : Blo 374761 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B1712353 : Blo 374761 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B565625 : Blo 374761 565625 := bstep (se 2 (by rfl) ⟨212109, by rfl⟩ : syracuseStep 565625 = 424219) B424219
theorem B1270619 : Blo 374761 1270619 := bstep (se 1 (by rfl) ⟨952964, by rfl⟩ : syracuseStep 1270619 = 1905929) B1905929
theorem B377703 : Blo 374761 377703 := bstep (se 1 (by rfl) ⟨283277, by rfl⟩ : syracuseStep 377703 = 566555) B566555
theorem B844667 : Blo 374761 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B7340939 : Blo 374761 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B4269023 : Blo 374761 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B566249 : Blo 374761 566249 := bstep (se 2 (by rfl) ⟨212343, by rfl⟩ : syracuseStep 566249 = 424687) B424687
theorem B8037467 : Blo 374761 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B844937 : Blo 374761 844937 := bstep (se 2 (by rfl) ⟨316851, by rfl⟩ : syracuseStep 844937 = 633703) B633703
theorem B5776595 : Blo 374761 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B21128471 : Blo 374761 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B23848339 : Blo 374761 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B188565077 : Blo 374761 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B10266223 : Blo 374761 10266223 := bstep (se 1 (by rfl) ⟨7699667, by rfl⟩ : syracuseStep 10266223 = 15399335) B15399335
theorem B477019 : Blo 374761 477019 := bstep (se 1 (by rfl) ⟨357764, by rfl⟩ : syracuseStep 477019 = 715529) B715529
theorem B632873 : Blo 374761 632873 := bstep (se 2 (by rfl) ⟨237327, by rfl⟩ : syracuseStep 632873 = 474655) B474655
theorem B5777573 : Blo 374761 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B1525949 : Blo 374761 1525949 := bstep (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) B572231
theorem B17549567 : Blo 374761 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B3213593 : Blo 374761 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B7735625 : Blo 374761 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B1804841 : Blo 374761 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2140937 : Blo 374761 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B1018727 : Blo 374761 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B23252183 : Blo 374761 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B2026727 : Blo 374761 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B716015 : Blo 374761 716015 := bstep (se 1 (by rfl) ⟨537011, by rfl⟩ : syracuseStep 716015 = 1074023) B1074023
theorem B380263 : Blo 374761 380263 := bstep (se 1 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 380263 = 570395) B570395
theorem B6434153 : Blo 374761 6434153 := bstep (se 2 (by rfl) ⟨2412807, by rfl⟩ : syracuseStep 6434153 = 4825615) B4825615
theorem B1265003 : Blo 374761 1265003 := bstep (se 1 (by rfl) ⟨948752, by rfl⟩ : syracuseStep 1265003 = 1897505) B1897505
theorem B2150003 : Blo 374761 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B1085147 : Blo 374761 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B4837097 : Blo 374761 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B2781053 : Blo 374761 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B1274183 : Blo 374761 1274183 := bstep (se 1 (by rfl) ⟨955637, by rfl⟩ : syracuseStep 1274183 = 1911275) B1911275
theorem B2855249 : Blo 374761 2855249 := bstep (se 2 (by rfl) ⟨1070718, by rfl⟩ : syracuseStep 2855249 = 2141437) B2141437
theorem B6517259 : Blo 374761 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B422491 : Blo 374761 422491 := bstep (se 1 (by rfl) ⟨316868, by rfl⟩ : syracuseStep 422491 = 633737) B633737
theorem B422779 : Blo 374761 422779 := bstep (se 1 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 422779 = 634169) B634169
theorem B857179 : Blo 374761 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B636187 : Blo 374761 636187 := bstep (se 1 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 636187 = 954281) B954281
theorem B2856221 : Blo 374761 2856221 := bstep (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) B1071083
theorem B46478717 : Blo 374761 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B636383 : Blo 374761 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B563177 : Blo 374761 563177 := bstep (se 2 (by rfl) ⟨211191, by rfl⟩ : syracuseStep 563177 = 422383) B422383
theorem B374811 : Blo 374761 374811 := bstep (se 1 (by rfl) ⟨281108, by rfl⟩ : syracuseStep 374811 = 562217) B562217
theorem B1906739 : Blo 374761 1906739 := bstep (se 1 (by rfl) ⟨1430054, by rfl⟩ : syracuseStep 1906739 = 2860109) B2860109
theorem B375023 : Blo 374761 375023 := bstep (se 1 (by rfl) ⟨281267, by rfl⟩ : syracuseStep 375023 = 562535) B562535
theorem B637355 : Blo 374761 637355 := bstep (se 1 (by rfl) ⟨478016, by rfl⟩ : syracuseStep 637355 = 956033) B956033
theorem B3226067 : Blo 374761 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B375263 : Blo 374761 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B563711 : Blo 374761 563711 := bstep (se 1 (by rfl) ⟨422783, by rfl⟩ : syracuseStep 563711 = 845567) B845567
theorem B3217967 : Blo 374761 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B375579 : Blo 374761 375579 := bstep (se 1 (by rfl) ⟨281684, by rfl⟩ : syracuseStep 375579 = 563369) B563369
theorem B375615 : Blo 374761 375615 := bstep (se 1 (by rfl) ⟨281711, by rfl⟩ : syracuseStep 375615 = 563423) B563423
theorem B564095 : Blo 374761 564095 := bstep (se 1 (by rfl) ⟨423071, by rfl⟩ : syracuseStep 564095 = 846143) B846143
theorem B6429779 : Blo 374761 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B5889131 : Blo 374761 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B482431 : Blo 374761 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B376347 : Blo 374761 376347 := bstep (se 1 (by rfl) ⟨282260, by rfl⟩ : syracuseStep 376347 = 564521) B564521
theorem B564791 : Blo 374761 564791 := bstep (se 1 (by rfl) ⟨423593, by rfl⟩ : syracuseStep 564791 = 847187) B847187
theorem B10853945 : Blo 374761 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B1908359 : Blo 374761 1908359 := bstep (se 1 (by rfl) ⟨1431269, by rfl⟩ : syracuseStep 1908359 = 2862539) B2862539
theorem B949927 : Blo 374761 949927 := bstep (se 1 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 949927 = 1424891) B1424891
theorem B843623 : Blo 374761 843623 := bstep (se 1 (by rfl) ⟨632717, by rfl⟩ : syracuseStep 843623 = 1265435) B1265435
theorem B11026367 : Blo 374761 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B950393 : Blo 374761 950393 := bstep (se 2 (by rfl) ⟨356397, by rfl⟩ : syracuseStep 950393 = 712795) B712795
theorem B377083 : Blo 374761 377083 := bstep (se 1 (by rfl) ⟨282812, by rfl⟩ : syracuseStep 377083 = 565625) B565625
theorem B377499 : Blo 374761 377499 := bstep (se 1 (by rfl) ⟨283124, by rfl⟩ : syracuseStep 377499 = 566249) B566249
theorem B5358311 : Blo 374761 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B3851063 : Blo 374761 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B1271159 : Blo 374761 1271159 := bstep (se 1 (by rfl) ⟨953369, by rfl⟩ : syracuseStep 1271159 = 1906739) B1906739
theorem B1017299 : Blo 374761 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B11699711 : Blo 374761 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B1427291 : Blo 374761 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B4286519 : Blo 374761 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B3926087 : Blo 374761 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B15501455 : Blo 374761 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B477343 : Blo 374761 477343 := bstep (se 1 (by rfl) ⟨358007, by rfl⟩ : syracuseStep 477343 = 716015) B716015
theorem B7235963 : Blo 374761 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B1272239 : Blo 374761 1272239 := bstep (se 1 (by rfl) ⟨954179, by rfl⟩ : syracuseStep 1272239 = 1908359) B1908359
theorem B723431 : Blo 374761 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B1854035 : Blo 374761 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B7350911 : Blo 374761 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B846575 : Blo 374761 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B1903499 : Blo 374761 1903499 := bstep (se 1 (by rfl) ⟨1427624, by rfl⟩ : syracuseStep 1903499 = 2855249) B2855249
theorem B4344839 : Blo 374761 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B847079 : Blo 374761 847079 := bstep (se 1 (by rfl) ⟨635309, by rfl⟩ : syracuseStep 847079 = 1270619) B1270619
theorem B4893959 : Blo 374761 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B2846015 : Blo 374761 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B14085647 : Blo 374761 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B1904147 : Blo 374761 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B30985811 : Blo 374761 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B125710051 : Blo 374761 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B421915 : Blo 374761 421915 := bstep (se 1 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 421915 = 632873) B632873
theorem B1142905 : Blo 374761 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B643241 : Blo 374761 643241 := bstep (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) B482431
theorem B2142395 : Blo 374761 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B5157083 : Blo 374761 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B2150711 : Blo 374761 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B848249 : Blo 374761 848249 := bstep (se 2 (by rfl) ⟨318093, by rfl⟩ : syracuseStep 848249 = 636187) B636187
theorem B31797785 : Blo 374761 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B1266569 : Blo 374761 1266569 := bstep (se 2 (by rfl) ⟨474963, by rfl⟩ : syracuseStep 1266569 = 949927) B949927
theorem B4289435 : Blo 374761 4289435 := bstep (se 1 (by rfl) ⟨3217076, by rfl⟩ : syracuseStep 4289435 = 6434153) B6434153
theorem B636025 : Blo 374761 636025 := bstep (se 2 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 636025 = 477019) B477019
theorem B3224731 : Blo 374761 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B562415 : Blo 374761 562415 := bstep (se 1 (by rfl) ⟨421811, by rfl⟩ : syracuseStep 562415 = 843623) B843623
theorem B849455 : Blo 374761 849455 := bstep (se 1 (by rfl) ⟨637091, by rfl⟩ : syracuseStep 849455 = 1274183) B1274183
theorem B2283137 : Blo 374761 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B15406861 : Blo 374761 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B563111 : Blo 374761 563111 := bstep (se 1 (by rfl) ⟨422333, by rfl⟩ : syracuseStep 563111 = 844667) B844667
theorem B563291 : Blo 374761 563291 := bstep (se 1 (by rfl) ⟨422468, by rfl⟩ : syracuseStep 563291 = 844937) B844937
theorem B563321 : Blo 374761 563321 := bstep (se 2 (by rfl) ⟨211245, by rfl⟩ : syracuseStep 563321 = 422491) B422491
theorem B424255 : Blo 374761 424255 := bstep (se 1 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 424255 = 636383) B636383
theorem B563705 : Blo 374761 563705 := bstep (se 2 (by rfl) ⟨211389, by rfl⟩ : syracuseStep 563705 = 422779) B422779
theorem B375451 : Blo 374761 375451 := bstep (se 1 (by rfl) ⟨281588, by rfl⟩ : syracuseStep 375451 = 563177) B563177
theorem B424903 : Blo 374761 424903 := bstep (se 1 (by rfl) ⟨318677, by rfl⟩ : syracuseStep 424903 = 637355) B637355
theorem B375807 : Blo 374761 375807 := bstep (se 1 (by rfl) ⟨281855, by rfl⟩ : syracuseStep 375807 = 563711) B563711
theorem B1203227 : Blo 374761 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B2145311 : Blo 374761 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B507017 : Blo 374761 507017 := bstep (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) B380263
theorem B679151 : Blo 374761 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B376063 : Blo 374761 376063 := bstep (se 1 (by rfl) ⟨282047, by rfl⟩ : syracuseStep 376063 = 564095) B564095
theorem B13688297 : Blo 374761 13688297 := bstep (se 2 (by rfl) ⟨5133111, by rfl⟩ : syracuseStep 13688297 = 10266223) B10266223
theorem B1351151 : Blo 374761 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B843335 : Blo 374761 843335 := bstep (se 1 (by rfl) ⟨632501, by rfl⟩ : syracuseStep 843335 = 1265003) B1265003
theorem B376527 : Blo 374761 376527 := bstep (se 1 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 376527 = 564791) B564791
theorem B1433335 : Blo 374761 1433335 := bstep (se 1 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 1433335 = 2150003) B2150003
theorem B1523873 : Blo 374761 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B1433807 : Blo 374761 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B565499 : Blo 374761 565499 := bstep (se 1 (by rfl) ⟨424124, by rfl⟩ : syracuseStep 565499 = 848249) B848249
theorem B1352045 : Blo 374761 1352045 := bstep (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) B507017
theorem B565673 : Blo 374761 565673 := bstep (se 2 (by rfl) ⟨212127, by rfl⟩ : syracuseStep 565673 = 424255) B424255
theorem B3572207 : Blo 374761 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B844379 : Blo 374761 844379 := bstep (se 1 (by rfl) ⟨633284, by rfl⟩ : syracuseStep 844379 = 1266569) B1266569
theorem B2859623 : Blo 374761 2859623 := bstep (se 1 (by rfl) ⟨2144717, by rfl⟩ : syracuseStep 2859623 = 4289435) B4289435
theorem B1811069 : Blo 374761 1811069 := bstep (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) B679151
theorem B7799807 : Blo 374761 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B566303 : Blo 374761 566303 := bstep (se 1 (by rfl) ⟨424727, by rfl⟩ : syracuseStep 566303 = 849455) B849455
theorem B2712797 : Blo 374761 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B951527 : Blo 374761 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B566537 : Blo 374761 566537 := bstep (se 2 (by rfl) ⟨212451, by rfl⟩ : syracuseStep 566537 = 424903) B424903
theorem B4900607 : Blo 374761 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B3262639 : Blo 374761 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B1911113 : Blo 374761 1911113 := bstep (se 2 (by rfl) ⟨716667, by rfl⟩ : syracuseStep 1911113 = 1433335) B1433335
theorem B9390431 : Blo 374761 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B633595 : Blo 374761 633595 := bstep (se 1 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 633595 = 950393) B950393
theorem B428827 : Blo 374761 428827 := bstep (se 1 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 428827 = 643241) B643241
theorem B1428263 : Blo 374761 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B2567375 : Blo 374761 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B847439 : Blo 374761 847439 := bstep (se 1 (by rfl) ⟨635579, by rfl⟩ : syracuseStep 847439 = 1271159) B1271159
theorem B2617391 : Blo 374761 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B10334303 : Blo 374761 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B848033 : Blo 374761 848033 := bstep (se 2 (by rfl) ⟨318012, by rfl⟩ : syracuseStep 848033 = 636025) B636025
theorem B848159 : Blo 374761 848159 := bstep (se 1 (by rfl) ⟨636119, by rfl⟩ : syracuseStep 848159 = 1272239) B1272239
theorem B2896559 : Blo 374761 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B1430207 : Blo 374761 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B1897343 : Blo 374761 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B167613401 : Blo 374761 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B20542481 : Blo 374761 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B562223 : Blo 374761 562223 := bstep (se 1 (by rfl) ⟨421667, by rfl⟩ : syracuseStep 562223 = 843335) B843335
theorem B20657207 : Blo 374761 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B562553 : Blo 374761 562553 := bstep (se 2 (by rfl) ⟨210957, by rfl⟩ : syracuseStep 562553 = 421915) B421915
theorem B3438055 : Blo 374761 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B636457 : Blo 374761 636457 := bstep (se 2 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 636457 = 477343) B477343
theorem B21198523 : Blo 374761 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B374943 : Blo 374761 374943 := bstep (se 1 (by rfl) ⟨281207, by rfl⟩ : syracuseStep 374943 = 562415) B562415
theorem B1522091 : Blo 374761 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B375407 : Blo 374761 375407 := bstep (se 1 (by rfl) ⟨281555, by rfl⟩ : syracuseStep 375407 = 563111) B563111
theorem B2857679 : Blo 374761 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B375527 : Blo 374761 375527 := bstep (se 1 (by rfl) ⟨281645, by rfl⟩ : syracuseStep 375527 = 563291) B563291
theorem B375547 : Blo 374761 375547 := bstep (se 1 (by rfl) ⟨281660, by rfl⟩ : syracuseStep 375547 = 563321) B563321
theorem B4299641 : Blo 374761 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B4823975 : Blo 374761 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B482287 : Blo 374761 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B375803 : Blo 374761 375803 := bstep (se 1 (by rfl) ⟨281852, by rfl⟩ : syracuseStep 375803 = 563705) B563705
theorem B1236023 : Blo 374761 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B564383 : Blo 374761 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B1268999 : Blo 374761 1268999 := bstep (se 1 (by rfl) ⟨951749, by rfl⟩ : syracuseStep 1268999 = 1903499) B1903499
theorem B802151 : Blo 374761 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B564719 : Blo 374761 564719 := bstep (se 1 (by rfl) ⟨423539, by rfl⟩ : syracuseStep 564719 = 847079) B847079
theorem B9125531 : Blo 374761 9125531 := bstep (se 1 (by rfl) ⟨6844148, by rfl⟩ : syracuseStep 9125531 = 13688297) B13688297
theorem B900767 : Blo 374761 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1269431 : Blo 374761 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B6889535 : Blo 374761 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1015915 : Blo 374761 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B565355 : Blo 374761 565355 := bstep (se 1 (by rfl) ⟨424016, by rfl⟩ : syracuseStep 565355 = 848033) B848033
theorem B6979709 : Blo 374761 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B376999 : Blo 374761 376999 := bstep (se 1 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 376999 = 565499) B565499
theorem B565439 : Blo 374761 565439 := bstep (se 1 (by rfl) ⟨424079, by rfl⟩ : syracuseStep 565439 = 848159) B848159
theorem B4350185 : Blo 374761 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B901363 : Blo 374761 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B377115 : Blo 374761 377115 := bstep (se 1 (by rfl) ⟨282836, by rfl⟩ : syracuseStep 377115 = 565673) B565673
theorem B377535 : Blo 374761 377535 := bstep (se 1 (by rfl) ⟨283151, by rfl⟩ : syracuseStep 377535 = 566303) B566303
theorem B13771471 : Blo 374761 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B377691 : Blo 374761 377691 := bstep (se 1 (by rfl) ⟨283268, by rfl⟩ : syracuseStep 377691 = 566537) B566537
theorem B844793 : Blo 374761 844793 := bstep (se 2 (by rfl) ⟨316797, by rfl⟩ : syracuseStep 844793 = 633595) B633595
theorem B6260287 : Blo 374761 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B2402045 : Blo 374761 2402045 := bstep (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) B900767
theorem B952175 : Blo 374761 952175 := bstep (se 1 (by rfl) ⟨714131, by rfl⟩ : syracuseStep 952175 = 1428263) B1428263
theorem B845999 : Blo 374761 845999 := bstep (se 1 (by rfl) ⟨634499, by rfl⟩ : syracuseStep 845999 = 1268999) B1268999
theorem B534767 : Blo 374761 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B28264697 : Blo 374761 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B846287 : Blo 374761 846287 := bstep (se 1 (by rfl) ⟨634715, by rfl⟩ : syracuseStep 846287 = 1269431) B1269431
theorem B1207379 : Blo 374761 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B953471 : Blo 374761 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B1264895 : Blo 374761 1264895 := bstep (se 1 (by rfl) ⟨948671, by rfl⟩ : syracuseStep 1264895 = 1897343) B1897343
theorem B111742267 : Blo 374761 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B634351 : Blo 374761 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B643049 : Blo 374761 643049 := bstep (se 2 (by rfl) ⟨241143, by rfl⟩ : syracuseStep 643049 = 482287) B482287
theorem B1274075 : Blo 374761 1274075 := bstep (se 1 (by rfl) ⟨955556, by rfl⟩ : syracuseStep 1274075 = 1911113) B1911113
theorem B1905119 : Blo 374761 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B3215983 : Blo 374761 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B4584073 : Blo 374761 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B824015 : Blo 374761 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B848609 : Blo 374761 848609 := bstep (se 2 (by rfl) ⟨318228, by rfl⟩ : syracuseStep 848609 = 636457) B636457
theorem B6083687 : Blo 374761 6083687 := bstep (se 1 (by rfl) ⟨4562765, by rfl⟩ : syracuseStep 6083687 = 9125531) B9125531
theorem B955871 : Blo 374761 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B2381471 : Blo 374761 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B562919 : Blo 374761 562919 := bstep (se 1 (by rfl) ⟨422189, by rfl⟩ : syracuseStep 562919 = 844379) B844379
theorem B1906415 : Blo 374761 1906415 := bstep (se 1 (by rfl) ⟨1429811, by rfl⟩ : syracuseStep 1906415 = 2859623) B2859623
theorem B1931039 : Blo 374761 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B5199871 : Blo 374761 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B13694987 : Blo 374761 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B374815 : Blo 374761 374815 := bstep (se 1 (by rfl) ⟨281111, by rfl⟩ : syracuseStep 374815 = 562223) B562223
theorem B1808531 : Blo 374761 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B375035 : Blo 374761 375035 := bstep (se 1 (by rfl) ⟨281276, by rfl⟩ : syracuseStep 375035 = 562553) B562553
theorem B571769 : Blo 374761 571769 := bstep (se 2 (by rfl) ⟨214413, by rfl⟩ : syracuseStep 571769 = 428827) B428827
theorem B3267071 : Blo 374761 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B1014727 : Blo 374761 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B2866427 : Blo 374761 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B376255 : Blo 374761 376255 := bstep (se 1 (by rfl) ⟨282191, by rfl⟩ : syracuseStep 376255 = 564383) B564383
theorem B1711583 : Blo 374761 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B376479 : Blo 374761 376479 := bstep (se 1 (by rfl) ⟨282359, by rfl⟩ : syracuseStep 376479 = 564719) B564719
theorem B564959 : Blo 374761 564959 := bstep (se 1 (by rfl) ⟨423719, by rfl⟩ : syracuseStep 564959 = 847439) B847439
theorem B376903 : Blo 374761 376903 := bstep (se 1 (by rfl) ⟨282677, by rfl⟩ : syracuseStep 376903 = 565355) B565355
theorem B4653139 : Blo 374761 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B376959 : Blo 374761 376959 := bstep (se 1 (by rfl) ⟨282719, by rfl⟩ : syracuseStep 376959 = 565439) B565439
theorem B2900123 : Blo 374761 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B1270079 : Blo 374761 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B549343 : Blo 374761 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B565739 : Blo 374761 565739 := bstep (se 1 (by rfl) ⟨424304, by rfl⟩ : syracuseStep 565739 = 848609) B848609
theorem B1426045 : Blo 374761 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B4055791 : Blo 374761 4055791 := bstep (se 1 (by rfl) ⟨3041843, by rfl⟩ : syracuseStep 4055791 = 6083687) B6083687
theorem B6112097 : Blo 374761 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B1270943 : Blo 374761 1270943 := bstep (se 1 (by rfl) ⟨953207, by rfl⟩ : syracuseStep 1270943 = 1906415) B1906415
theorem B1287359 : Blo 374761 1287359 := bstep (se 1 (by rfl) ⟨965519, by rfl⟩ : syracuseStep 1287359 = 1931039) B1931039
theorem B1352969 : Blo 374761 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B1205687 : Blo 374761 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B18843131 : Blo 374761 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B148989689 : Blo 374761 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B845801 : Blo 374761 845801 := bstep (se 2 (by rfl) ⟨317175, by rfl⟩ : syracuseStep 845801 = 634351) B634351
theorem B804919 : Blo 374761 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B1910951 : Blo 374761 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B1141055 : Blo 374761 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B428699 : Blo 374761 428699 := bstep (se 1 (by rfl) ⟨321524, by rfl⟩ : syracuseStep 428699 = 643049) B643049
theorem B6933161 : Blo 374761 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B1354553 : Blo 374761 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B4287977 : Blo 374761 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B18361961 : Blo 374761 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B1601363 : Blo 374761 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B634783 : Blo 374761 634783 := bstep (se 1 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 634783 = 952175) B952175
theorem B9129991 : Blo 374761 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B381179 : Blo 374761 381179 := bstep (se 1 (by rfl) ⟨285884, by rfl⟩ : syracuseStep 381179 = 571769) B571769
theorem B635647 : Blo 374761 635647 := bstep (se 1 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 635647 = 953471) B953471
theorem B4593023 : Blo 374761 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B849383 : Blo 374761 849383 := bstep (se 1 (by rfl) ⟨637037, by rfl⟩ : syracuseStep 849383 = 1274075) B1274075
theorem B1201817 : Blo 374761 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B563195 : Blo 374761 563195 := bstep (se 1 (by rfl) ⟨422396, by rfl⟩ : syracuseStep 563195 = 844793) B844793
theorem B637247 : Blo 374761 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B1587647 : Blo 374761 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B375279 : Blo 374761 375279 := bstep (se 1 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 375279 = 562919) B562919
theorem B563999 : Blo 374761 563999 := bstep (se 1 (by rfl) ⟨422999, by rfl⟩ : syracuseStep 563999 = 845999) B845999
theorem B564191 : Blo 374761 564191 := bstep (se 1 (by rfl) ⟨423143, by rfl⟩ : syracuseStep 564191 = 846287) B846287
theorem B2178047 : Blo 374761 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B8347049 : Blo 374761 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B843263 : Blo 374761 843263 := bstep (se 1 (by rfl) ⟨632447, by rfl⟩ : syracuseStep 843263 = 1264895) B1264895
theorem B376639 : Blo 374761 376639 := bstep (se 1 (by rfl) ⟨282479, by rfl⟩ : syracuseStep 376639 = 564959) B564959
theorem B12173321 : Blo 374761 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B1073225 : Blo 374761 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B1933415 : Blo 374761 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B377159 : Blo 374761 377159 := bstep (se 1 (by rfl) ⟨282869, by rfl⟩ : syracuseStep 377159 = 565739) B565739
theorem B1016477 : Blo 374761 1016477 := bstep (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) B381179
theorem B1901393 : Blo 374761 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B901979 : Blo 374761 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B803791 : Blo 374761 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B5407721 : Blo 374761 5407721 := bstep (se 2 (by rfl) ⟨2027895, by rfl⟩ : syracuseStep 5407721 = 4055791) B4055791
theorem B566255 : Blo 374761 566255 := bstep (se 1 (by rfl) ⟨424691, by rfl⟩ : syracuseStep 566255 = 849383) B849383
theorem B3204845 : Blo 374761 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B903035 : Blo 374761 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B5564699 : Blo 374761 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B12241307 : Blo 374761 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B846377 : Blo 374761 846377 := bstep (se 2 (by rfl) ⟨317391, by rfl⟩ : syracuseStep 846377 = 634783) B634783
theorem B1067575 : Blo 374761 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B6204185 : Blo 374761 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B846719 : Blo 374761 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B4074731 : Blo 374761 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B847295 : Blo 374761 847295 := bstep (se 1 (by rfl) ⟨635471, by rfl⟩ : syracuseStep 847295 = 1270943) B1270943
theorem B12562087 : Blo 374761 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B847529 : Blo 374761 847529 := bstep (se 2 (by rfl) ⟨317823, by rfl⟩ : syracuseStep 847529 = 635647) B635647
theorem B1273967 : Blo 374761 1273967 := bstep (se 1 (by rfl) ⟨955475, by rfl⟩ : syracuseStep 1273967 = 1910951) B1910951
theorem B1143197 : Blo 374761 1143197 := bstep (se 3 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 1143197 = 428699) B428699
theorem B562175 : Blo 374761 562175 := bstep (se 1 (by rfl) ⟨421631, by rfl⟩ : syracuseStep 562175 = 843263) B843263
theorem B2929829 : Blo 374761 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B858239 : Blo 374761 858239 := bstep (se 1 (by rfl) ⟨643679, by rfl⟩ : syracuseStep 858239 = 1287359) B1287359
theorem B3062015 : Blo 374761 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B99326459 : Blo 374761 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B4233725 : Blo 374761 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B563867 : Blo 374761 563867 := bstep (se 1 (by rfl) ⟨422900, by rfl⟩ : syracuseStep 563867 = 845801) B845801
theorem B375463 : Blo 374761 375463 := bstep (se 1 (by rfl) ⟨281597, by rfl⟩ : syracuseStep 375463 = 563195) B563195
theorem B760703 : Blo 374761 760703 := bstep (se 1 (by rfl) ⟨570527, by rfl⟩ : syracuseStep 760703 = 1141055) B1141055
theorem B424831 : Blo 374761 424831 := bstep (se 1 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 424831 = 637247) B637247
theorem B18488429 : Blo 374761 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B375999 : Blo 374761 375999 := bstep (se 1 (by rfl) ⟨281999, by rfl⟩ : syracuseStep 375999 = 563999) B563999
theorem B376127 : Blo 374761 376127 := bstep (se 1 (by rfl) ⟨282095, by rfl⟩ : syracuseStep 376127 = 564191) B564191
theorem B2858651 : Blo 374761 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B5808125 : Blo 374761 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B762131 : Blo 374761 762131 := bstep (se 1 (by rfl) ⟨571598, by rfl⟩ : syracuseStep 762131 = 1143197) B1143197
theorem B3605147 : Blo 374761 3605147 := bstep (se 1 (by rfl) ⟨2703860, by rfl⟩ : syracuseStep 3605147 = 5407721) B5407721
theorem B377503 : Blo 374761 377503 := bstep (se 1 (by rfl) ⟨283127, by rfl⟩ : syracuseStep 377503 = 566255) B566255
theorem B566441 : Blo 374761 566441 := bstep (se 2 (by rfl) ⟨212415, by rfl⟩ : syracuseStep 566441 = 424831) B424831
theorem B2041343 : Blo 374761 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B8160871 : Blo 374761 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B715483 : Blo 374761 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B1288943 : Blo 374761 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B601319 : Blo 374761 601319 := bstep (se 1 (by rfl) ⟨450989, by rfl⟩ : syracuseStep 601319 = 901979) B901979
theorem B8114165 : Blo 374761 8114165 := bstep (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) B760703
theorem B2822483 : Blo 374761 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B12325619 : Blo 374761 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B2716487 : Blo 374761 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B16749449 : Blo 374761 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B1905767 : Blo 374761 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B3872083 : Blo 374761 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B8115547 : Blo 374761 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B849311 : Blo 374761 849311 := bstep (se 1 (by rfl) ⟨636983, by rfl⟩ : syracuseStep 849311 = 1273967) B1273967
theorem B7812877 : Blo 374761 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B677651 : Blo 374761 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B1267595 : Blo 374761 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B374783 : Blo 374761 374783 := bstep (se 1 (by rfl) ⟨281087, by rfl⟩ : syracuseStep 374783 = 562175) B562175
theorem B1423433 : Blo 374761 1423433 := bstep (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) B1067575
theorem B2136563 : Blo 374761 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B1071721 : Blo 374761 1071721 := bstep (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) B803791
theorem B264870557 : Blo 374761 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B572159 : Blo 374761 572159 := bstep (se 1 (by rfl) ⟨429119, by rfl⟩ : syracuseStep 572159 = 858239) B858239
theorem B3709799 : Blo 374761 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B564251 : Blo 374761 564251 := bstep (se 1 (by rfl) ⟨423188, by rfl⟩ : syracuseStep 564251 = 846377) B846377
theorem B375911 : Blo 374761 375911 := bstep (se 1 (by rfl) ⟨281933, by rfl⟩ : syracuseStep 375911 = 563867) B563867
theorem B4136123 : Blo 374761 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B564479 : Blo 374761 564479 := bstep (se 1 (by rfl) ⟨423359, by rfl⟩ : syracuseStep 564479 = 846719) B846719
theorem B564863 : Blo 374761 564863 := bstep (se 1 (by rfl) ⟨423647, by rfl⟩ : syracuseStep 564863 = 847295) B847295
theorem B2408093 : Blo 374761 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B565019 : Blo 374761 565019 := bstep (se 1 (by rfl) ⟨423764, by rfl⟩ : syracuseStep 565019 = 847529) B847529
theorem B508087 : Blo 374761 508087 := bstep (se 1 (by rfl) ⟨381065, by rfl⟩ : syracuseStep 508087 = 762131) B762131
theorem B1810991 : Blo 374761 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B11166299 : Blo 374761 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B1270511 : Blo 374761 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B377627 : Blo 374761 377627 := bstep (se 1 (by rfl) ⟨283220, by rfl⟩ : syracuseStep 377627 = 566441) B566441
theorem B566207 : Blo 374761 566207 := bstep (se 1 (by rfl) ⟨424655, by rfl⟩ : syracuseStep 566207 = 849311) B849311
theorem B1360895 : Blo 374761 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B845063 : Blo 374761 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B176580371 : Blo 374761 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B5162777 : Blo 374761 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B32868317 : Blo 374761 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B10881161 : Blo 374761 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B5409443 : Blo 374761 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B7228277 : Blo 374761 7228277 := bstep (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) B677651
theorem B2403431 : Blo 374761 2403431 := bstep (se 1 (by rfl) ⟨1802573, by rfl⟩ : syracuseStep 2403431 = 3605147) B3605147
theorem B1428961 : Blo 374761 1428961 := bstep (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) B1071721
theorem B953977 : Blo 374761 953977 := bstep (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) B715483
theorem B381439 : Blo 374761 381439 := bstep (se 1 (by rfl) ⟨286079, by rfl⟩ : syracuseStep 381439 = 572159) B572159
theorem B2757415 : Blo 374761 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B10417169 : Blo 374761 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B7526621 : Blo 374761 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B948955 : Blo 374761 948955 := bstep (se 1 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 948955 = 1423433) B1423433
theorem B1424375 : Blo 374761 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B10820729 : Blo 374761 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B859295 : Blo 374761 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B2473199 : Blo 374761 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B376167 : Blo 374761 376167 := bstep (se 1 (by rfl) ⟨282125, by rfl⟩ : syracuseStep 376167 = 564251) B564251
theorem B400879 : Blo 374761 400879 := bstep (se 1 (by rfl) ⟨300659, by rfl⟩ : syracuseStep 400879 = 601319) B601319
theorem B376319 : Blo 374761 376319 := bstep (se 1 (by rfl) ⟨282239, by rfl⟩ : syracuseStep 376319 = 564479) B564479
theorem B376575 : Blo 374761 376575 := bstep (se 1 (by rfl) ⟨282431, by rfl⟩ : syracuseStep 376575 = 564863) B564863
theorem B1605395 : Blo 374761 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B376679 : Blo 374761 376679 := bstep (se 1 (by rfl) ⟨282509, by rfl⟩ : syracuseStep 376679 = 565019) B565019
theorem B20070989 : Blo 374761 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B377471 : Blo 374761 377471 := bstep (se 1 (by rfl) ⟨283103, by rfl⟩ : syracuseStep 377471 = 566207) B566207
theorem B508585 : Blo 374761 508585 := bstep (se 2 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 508585 = 381439) B381439
theorem B3441851 : Blo 374761 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B3606295 : Blo 374761 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B4818851 : Blo 374761 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B1648799 : Blo 374761 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B1271969 : Blo 374761 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B1207327 : Blo 374761 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B847007 : Blo 374761 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B1265273 : Blo 374761 1265273 := bstep (se 2 (by rfl) ⟨474477, by rfl⟩ : syracuseStep 1265273 = 948955) B948955
theorem B7254107 : Blo 374761 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B1905281 : Blo 374761 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B470880989 : Blo 374761 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B1602287 : Blo 374761 1602287 := bstep (se 1 (by rfl) ⟨1201715, by rfl⟩ : syracuseStep 1602287 = 2403431) B2403431
theorem B7213819 : Blo 374761 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B1070263 : Blo 374761 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B677449 : Blo 374761 677449 := bstep (se 2 (by rfl) ⟨254043, by rfl⟩ : syracuseStep 677449 = 508087) B508087
theorem B7444199 : Blo 374761 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B2291453 : Blo 374761 2291453 := bstep (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) B859295
theorem B6944779 : Blo 374761 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B563375 : Blo 374761 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B3676553 : Blo 374761 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B21912211 : Blo 374761 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B3629053 : Blo 374761 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B949583 : Blo 374761 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B2138021 : Blo 374761 2138021 := bstep (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) B400879
theorem B3613061 : Blo 374761 3613061 := bstep (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) B677449
theorem B1270187 : Blo 374761 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B2294567 : Blo 374761 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B9618425 : Blo 374761 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B3212567 : Blo 374761 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B1099199 : Blo 374761 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B1427017 : Blo 374761 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B2451035 : Blo 374761 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B633055 : Blo 374761 633055 := bstep (se 1 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 633055 = 949583) B949583
theorem B9259705 : Blo 374761 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B4836071 : Blo 374761 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B13380659 : Blo 374761 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B313920659 : Blo 374761 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B1068191 : Blo 374761 1068191 := bstep (se 1 (by rfl) ⟨801143, by rfl⟩ : syracuseStep 1068191 = 1602287) B1602287
theorem B1527635 : Blo 374761 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B1609769 : Blo 374761 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B847979 : Blo 374761 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B4838737 : Blo 374761 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B116865125 : Blo 374761 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B678113 : Blo 374761 678113 := bstep (se 2 (by rfl) ⟨254292, by rfl⟩ : syracuseStep 678113 = 508585) B508585
theorem B4962799 : Blo 374761 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B375583 : Blo 374761 375583 := bstep (se 1 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 375583 = 563375) B563375
theorem B564671 : Blo 374761 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B4808393 : Blo 374761 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B843515 : Blo 374761 843515 := bstep (se 1 (by rfl) ⟨632636, by rfl⟩ : syracuseStep 843515 = 1265273) B1265273
theorem B1425347 : Blo 374761 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B1073179 : Blo 374761 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B565319 : Blo 374761 565319 := bstep (se 1 (by rfl) ⟨423989, by rfl⟩ : syracuseStep 565319 = 847979) B847979
theorem B2408707 : Blo 374761 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B844073 : Blo 374761 844073 := bstep (se 2 (by rfl) ⟨316527, by rfl⟩ : syracuseStep 844073 = 633055) B633055
theorem B12346273 : Blo 374761 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B452075 : Blo 374761 452075 := bstep (se 1 (by rfl) ⟨339056, by rfl⟩ : syracuseStep 452075 = 678113) B678113
theorem B12896189 : Blo 374761 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B1902689 : Blo 374761 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B3205595 : Blo 374761 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B1018423 : Blo 374761 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B846791 : Blo 374761 846791 := bstep (se 1 (by rfl) ⟨635093, by rfl⟩ : syracuseStep 846791 = 1270187) B1270187
theorem B2141711 : Blo 374761 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B1634023 : Blo 374761 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B77910083 : Blo 374761 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B6451649 : Blo 374761 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B562343 : Blo 374761 562343 := bstep (se 1 (by rfl) ⟨421757, by rfl⟩ : syracuseStep 562343 = 843515) B843515
theorem B1529711 : Blo 374761 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B6412283 : Blo 374761 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B2931197 : Blo 374761 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B8920439 : Blo 374761 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B209280439 : Blo 374761 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B712127 : Blo 374761 712127 := bstep (se 1 (by rfl) ⟨534095, by rfl⟩ : syracuseStep 712127 = 1068191) B1068191
theorem B376447 : Blo 374761 376447 := bstep (se 1 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 376447 = 564671) B564671
theorem B6617065 : Blo 374761 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B950231 : Blo 374761 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B376879 : Blo 374761 376879 := bstep (se 1 (by rfl) ⟨282659, by rfl⟩ : syracuseStep 376879 = 565319) B565319
theorem B4301099 : Blo 374761 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B3211609 : Blo 374761 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B1205533 : Blo 374761 1205533 := bstep (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) B452075
theorem B1427807 : Blo 374761 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B633487 : Blo 374761 633487 := bstep (se 1 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 633487 = 950231) B950231
theorem B51940055 : Blo 374761 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B1019807 : Blo 374761 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B8597459 : Blo 374761 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B279040585 : Blo 374761 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B31266101 : Blo 374761 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B1430905 : Blo 374761 1430905 := bstep (se 2 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 1430905 = 1073179) B1073179
theorem B562715 : Blo 374761 562715 := bstep (se 1 (by rfl) ⟨422036, by rfl⟩ : syracuseStep 562715 = 844073) B844073
theorem B1357897 : Blo 374761 1357897 := bstep (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) B1018423
theorem B374895 : Blo 374761 374895 := bstep (se 1 (by rfl) ⟨281171, by rfl⟩ : syracuseStep 374895 = 562343) B562343
theorem B4274855 : Blo 374761 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B1268459 : Blo 374761 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B2137063 : Blo 374761 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B564527 : Blo 374761 564527 := bstep (se 1 (by rfl) ⟨423395, by rfl⟩ : syracuseStep 564527 = 846791) B846791
theorem B65846789 : Blo 374761 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B5946959 : Blo 374761 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B474751 : Blo 374761 474751 := bstep (se 1 (by rfl) ⟨356063, by rfl⟩ : syracuseStep 474751 = 712127) B712127
theorem B2178697 : Blo 374761 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B8822753 : Blo 374761 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B1810529 : Blo 374761 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B2867399 : Blo 374761 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B844649 : Blo 374761 844649 := bstep (se 2 (by rfl) ⟨316743, by rfl⟩ : syracuseStep 844649 = 633487) B633487
theorem B951871 : Blo 374761 951871 := bstep (se 1 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 951871 = 1427807) B1427807
theorem B1607377 : Blo 374761 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B845639 : Blo 374761 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B633001 : Blo 374761 633001 := bstep (se 2 (by rfl) ⟨237375, by rfl⟩ : syracuseStep 633001 = 474751) B474751
theorem B20844067 : Blo 374761 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B2904929 : Blo 374761 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B43897859 : Blo 374761 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B22926557 : Blo 374761 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B4282145 : Blo 374761 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B372054113 : Blo 374761 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B375143 : Blo 374761 375143 := bstep (se 1 (by rfl) ⟨281357, by rfl⟩ : syracuseStep 375143 = 562715) B562715
theorem B2849417 : Blo 374761 2849417 := bstep (se 2 (by rfl) ⟨1068531, by rfl⟩ : syracuseStep 2849417 = 2137063) B2137063
theorem B2849903 : Blo 374761 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B34626703 : Blo 374761 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B1907873 : Blo 374761 1907873 := bstep (se 2 (by rfl) ⟨715452, by rfl⟩ : syracuseStep 1907873 = 1430905) B1430905
theorem B376351 : Blo 374761 376351 := bstep (se 1 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 376351 = 564527) B564527
theorem B3964639 : Blo 374761 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B679871 : Blo 374761 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B5881835 : Blo 374761 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B844001 : Blo 374761 844001 := bstep (se 2 (by rfl) ⟨316500, by rfl⟩ : syracuseStep 844001 = 633001) B633001
theorem B1271915 : Blo 374761 1271915 := bstep (se 1 (by rfl) ⟨953936, by rfl⟩ : syracuseStep 1271915 = 1907873) B1907873
theorem B5286185 : Blo 374761 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B1812989 : Blo 374761 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B1207019 : Blo 374761 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B1911599 : Blo 374761 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B1936619 : Blo 374761 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B29265239 : Blo 374761 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B2854763 : Blo 374761 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B27792089 : Blo 374761 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B2143169 : Blo 374761 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B3921223 : Blo 374761 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B563099 : Blo 374761 563099 := bstep (se 1 (by rfl) ⟨422324, by rfl⟩ : syracuseStep 563099 = 844649) B844649
theorem B15284371 : Blo 374761 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B563759 : Blo 374761 563759 := bstep (se 1 (by rfl) ⟨422819, by rfl⟩ : syracuseStep 563759 = 845639) B845639
theorem B248036075 : Blo 374761 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B46168937 : Blo 374761 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B1899611 : Blo 374761 1899611 := bstep (se 1 (by rfl) ⟨1424708, by rfl⟩ : syracuseStep 1899611 = 2849417) B2849417
theorem B1899935 : Blo 374761 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B1269161 : Blo 374761 1269161 := bstep (se 2 (by rfl) ⟨475935, by rfl⟩ : syracuseStep 1269161 = 951871) B951871
theorem B4834637 : Blo 374761 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B3524123 : Blo 374761 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B5228297 : Blo 374761 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B165357383 : Blo 374761 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B30779291 : Blo 374761 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B846107 : Blo 374761 846107 := bstep (se 1 (by rfl) ⟨634580, by rfl⟩ : syracuseStep 846107 = 1269161) B1269161
theorem B1903175 : Blo 374761 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B1428779 : Blo 374761 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B847943 : Blo 374761 847943 := bstep (se 1 (by rfl) ⟨635957, by rfl⟩ : syracuseStep 847943 = 1271915) B1271915
theorem B1274399 : Blo 374761 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B1266407 : Blo 374761 1266407 := bstep (se 1 (by rfl) ⟨949805, by rfl⟩ : syracuseStep 1266407 = 1899611) B1899611
theorem B1291079 : Blo 374761 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B19510159 : Blo 374761 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B1266623 : Blo 374761 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B562667 : Blo 374761 562667 := bstep (se 1 (by rfl) ⟨422000, by rfl⟩ : syracuseStep 562667 = 844001) B844001
theorem B20379161 : Blo 374761 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B18528059 : Blo 374761 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B375399 : Blo 374761 375399 := bstep (se 1 (by rfl) ⟨281549, by rfl⟩ : syracuseStep 375399 = 563099) B563099
theorem B375839 : Blo 374761 375839 := bstep (se 1 (by rfl) ⟨281879, by rfl⟩ : syracuseStep 375839 = 563759) B563759
theorem B3218717 : Blo 374761 3218717 := bstep (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) B1207019
theorem B565295 : Blo 374761 565295 := bstep (se 1 (by rfl) ⟨423971, by rfl⟩ : syracuseStep 565295 = 847943) B847943
theorem B844271 : Blo 374761 844271 := bstep (se 1 (by rfl) ⟨633203, by rfl⟩ : syracuseStep 844271 = 1266407) B1266407
theorem B860719 : Blo 374761 860719 := bstep (se 1 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 860719 = 1291079) B1291079
theorem B844415 : Blo 374761 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B49408157 : Blo 374761 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B440953021 : Blo 374761 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B952519 : Blo 374761 952519 := bstep (se 1 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 952519 = 1428779) B1428779
theorem B3223091 : Blo 374761 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B3485531 : Blo 374761 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B26013545 : Blo 374761 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B849599 : Blo 374761 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B375111 : Blo 374761 375111 := bstep (se 1 (by rfl) ⟨281333, by rfl⟩ : syracuseStep 375111 = 562667) B562667
theorem B2349415 : Blo 374761 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B20519527 : Blo 374761 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B54344429 : Blo 374761 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B564071 : Blo 374761 564071 := bstep (se 1 (by rfl) ⟨423053, by rfl⟩ : syracuseStep 564071 = 846107) B846107
theorem B1268783 : Blo 374761 1268783 := bstep (se 1 (by rfl) ⟨951587, by rfl⟩ : syracuseStep 1268783 = 1903175) B1903175
theorem B2145811 : Blo 374761 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B376863 : Blo 374761 376863 := bstep (se 1 (by rfl) ⟨282647, by rfl⟩ : syracuseStep 376863 = 565295) B565295
theorem B1270025 : Blo 374761 1270025 := bstep (se 2 (by rfl) ⟨476259, by rfl⟩ : syracuseStep 1270025 = 952519) B952519
theorem B1147625 : Blo 374761 1147625 := bstep (se 2 (by rfl) ⟨430359, by rfl⟩ : syracuseStep 1147625 = 860719) B860719
theorem B566399 : Blo 374761 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B2861081 : Blo 374761 2861081 := bstep (se 2 (by rfl) ⟨1072905, by rfl⟩ : syracuseStep 2861081 = 2145811) B2145811
theorem B845855 : Blo 374761 845855 := bstep (se 1 (by rfl) ⟨634391, by rfl⟩ : syracuseStep 845855 = 1268783) B1268783
theorem B2148727 : Blo 374761 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B131755085 : Blo 374761 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B36229619 : Blo 374761 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B12530213 : Blo 374761 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B9294749 : Blo 374761 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B587937361 : Blo 374761 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B562847 : Blo 374761 562847 := bstep (se 1 (by rfl) ⟨422135, by rfl⟩ : syracuseStep 562847 = 844271) B844271
theorem B562943 : Blo 374761 562943 := bstep (se 1 (by rfl) ⟨422207, by rfl⟩ : syracuseStep 562943 = 844415) B844415
theorem B27359369 : Blo 374761 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B376047 : Blo 374761 376047 := bstep (se 1 (by rfl) ⟨282035, by rfl⟩ : syracuseStep 376047 = 564071) B564071
theorem B17342363 : Blo 374761 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B377599 : Blo 374761 377599 := bstep (se 1 (by rfl) ⟨283199, by rfl⟩ : syracuseStep 377599 = 566399) B566399
theorem B87836723 : Blo 374761 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B11561575 : Blo 374761 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B846683 : Blo 374761 846683 := bstep (se 1 (by rfl) ⟨635012, by rfl⟩ : syracuseStep 846683 = 1270025) B1270025
theorem B24153079 : Blo 374761 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B765083 : Blo 374761 765083 := bstep (se 1 (by rfl) ⟨573812, by rfl⟩ : syracuseStep 765083 = 1147625) B1147625
theorem B6196499 : Blo 374761 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B18239579 : Blo 374761 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B8353475 : Blo 374761 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B2864969 : Blo 374761 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B375231 : Blo 374761 375231 := bstep (se 1 (by rfl) ⟨281423, by rfl⟩ : syracuseStep 375231 = 562847) B562847
theorem B375295 : Blo 374761 375295 := bstep (se 1 (by rfl) ⟨281471, by rfl⟩ : syracuseStep 375295 = 562943) B562943
theorem B1907387 : Blo 374761 1907387 := bstep (se 1 (by rfl) ⟨1430540, by rfl⟩ : syracuseStep 1907387 = 2861081) B2861081
theorem B563903 : Blo 374761 563903 := bstep (se 1 (by rfl) ⟨422927, by rfl⟩ : syracuseStep 563903 = 845855) B845855
theorem B783916481 : Blo 374761 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B2040221 : Blo 374761 2040221 := bstep (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) B765083
theorem B1909979 : Blo 374761 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B32204105 : Blo 374761 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B58557815 : Blo 374761 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B1271591 : Blo 374761 1271591 := bstep (se 1 (by rfl) ⟨953693, by rfl⟩ : syracuseStep 1271591 = 1907387) B1907387
theorem B4130999 : Blo 374761 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B522610987 : Blo 374761 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B12159719 : Blo 374761 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B15415433 : Blo 374761 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B5568983 : Blo 374761 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B375935 : Blo 374761 375935 := bstep (se 1 (by rfl) ⟨281951, by rfl⟩ : syracuseStep 375935 = 563903) B563903
theorem B564455 : Blo 374761 564455 := bstep (se 1 (by rfl) ⟨423341, by rfl⟩ : syracuseStep 564455 = 846683) B846683
theorem B1360147 : Blo 374761 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B2753999 : Blo 374761 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B3712655 : Blo 374761 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B696814649 : Blo 374761 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B1273319 : Blo 374761 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B39038543 : Blo 374761 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B847727 : Blo 374761 847727 := bstep (se 1 (by rfl) ⟨635795, by rfl⟩ : syracuseStep 847727 = 1271591) B1271591
theorem B10276955 : Blo 374761 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B8106479 : Blo 374761 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B21469403 : Blo 374761 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B376303 : Blo 374761 376303 := bstep (se 1 (by rfl) ⟨282227, by rfl⟩ : syracuseStep 376303 = 564455) B564455
theorem B1835999 : Blo 374761 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B14312935 : Blo 374761 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B6851303 : Blo 374761 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B1813529 : Blo 374761 1813529 := bstep (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) B1360147
theorem B9900413 : Blo 374761 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B848879 : Blo 374761 848879 := bstep (se 1 (by rfl) ⟨636659, by rfl⟩ : syracuseStep 848879 = 1273319) B1273319
theorem B5404319 : Blo 374761 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B464543099 : Blo 374761 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B26025695 : Blo 374761 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B565151 : Blo 374761 565151 := bstep (se 1 (by rfl) ⟨423863, by rfl⟩ : syracuseStep 565151 = 847727) B847727
theorem B565919 : Blo 374761 565919 := bstep (se 1 (by rfl) ⟨424439, by rfl⟩ : syracuseStep 565919 = 848879) B848879
theorem B76335653 : Blo 374761 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B1223999 : Blo 374761 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B4567535 : Blo 374761 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B1209019 : Blo 374761 1209019 := bstep (se 1 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 1209019 = 1813529) B1813529
theorem B309695399 : Blo 374761 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B6600275 : Blo 374761 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B3602879 : Blo 374761 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B17350463 : Blo 374761 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B376767 : Blo 374761 376767 := bstep (se 1 (by rfl) ⟨282575, by rfl⟩ : syracuseStep 376767 = 565151) B565151
theorem B377279 : Blo 374761 377279 := bstep (se 1 (by rfl) ⟨282959, by rfl⟩ : syracuseStep 377279 = 565919) B565919
theorem B206463599 : Blo 374761 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B4400183 : Blo 374761 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B2401919 : Blo 374761 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B815999 : Blo 374761 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B3045023 : Blo 374761 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1612025 : Blo 374761 1612025 := bstep (se 2 (by rfl) ⟨604509, by rfl⟩ : syracuseStep 1612025 = 1209019) B1209019
theorem B203561741 : Blo 374761 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B11566975 : Blo 374761 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B137642399 : Blo 374761 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B2933455 : Blo 374761 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B1074683 : Blo 374761 1074683 := bstep (se 1 (by rfl) ⟨806012, by rfl⟩ : syracuseStep 1074683 = 1612025) B1612025
theorem B1601279 : Blo 374761 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B2175997 : Blo 374761 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B15422633 : Blo 374761 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B2030015 : Blo 374761 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B135707827 : Blo 374761 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B10281755 : Blo 374761 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B2901329 : Blo 374761 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1353343 : Blo 374761 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B1067519 : Blo 374761 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B91761599 : Blo 374761 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B3911273 : Blo 374761 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B716455 : Blo 374761 716455 := bstep (se 1 (by rfl) ⟨537341, by rfl⟩ : syracuseStep 716455 = 1074683) B1074683
theorem B180943769 : Blo 374761 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B1934219 : Blo 374761 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B120629179 : Blo 374761 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B1804457 : Blo 374761 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B2607515 : Blo 374761 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B61174399 : Blo 374761 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B955273 : Blo 374761 955273 := bstep (se 2 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 955273 = 716455) B716455
theorem B6854503 : Blo 374761 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B711679 : Blo 374761 711679 := bstep (se 1 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 711679 = 1067519) B1067519
theorem B1738343 : Blo 374761 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B1289479 : Blo 374761 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B1273697 : Blo 374761 1273697 := bstep (se 2 (by rfl) ⟨477636, by rfl⟩ : syracuseStep 1273697 = 955273) B955273
theorem B643355621 : Blo 374761 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B9139337 : Blo 374761 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B81565865 : Blo 374761 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B948905 : Blo 374761 948905 := bstep (se 2 (by rfl) ⟨355839, by rfl⟩ : syracuseStep 948905 = 711679) B711679
theorem B1202971 : Blo 374761 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B632603 : Blo 374761 632603 := bstep (se 1 (by rfl) ⟨474452, by rfl⟩ : syracuseStep 632603 = 948905) B948905
theorem B428903747 : Blo 374761 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B1158895 : Blo 374761 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B849131 : Blo 374761 849131 := bstep (se 1 (by rfl) ⟨636848, by rfl⟩ : syracuseStep 849131 = 1273697) B1273697
theorem B6092891 : Blo 374761 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B1603961 : Blo 374761 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B54377243 : Blo 374761 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B1719305 : Blo 374761 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B566087 : Blo 374761 566087 := bstep (se 1 (by rfl) ⟨424565, by rfl⟩ : syracuseStep 566087 = 849131) B849131
theorem B36251495 : Blo 374761 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B285935831 : Blo 374761 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B421735 : Blo 374761 421735 := bstep (se 1 (by rfl) ⟨316301, by rfl⟩ : syracuseStep 421735 = 632603) B632603
theorem B1069307 : Blo 374761 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B1545193 : Blo 374761 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B4061927 : Blo 374761 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B1146203 : Blo 374761 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B712871 : Blo 374761 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B377391 : Blo 374761 377391 := bstep (se 1 (by rfl) ⟨283043, by rfl⟩ : syracuseStep 377391 = 566087) B566087
theorem B24167663 : Blo 374761 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B764135 : Blo 374761 764135 := bstep (se 1 (by rfl) ⟨573101, by rfl⟩ : syracuseStep 764135 = 1146203) B1146203
theorem B2060257 : Blo 374761 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B190623887 : Blo 374761 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B2707951 : Blo 374761 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B562313 : Blo 374761 562313 := bstep (se 2 (by rfl) ⟨210867, by rfl⟩ : syracuseStep 562313 = 421735) B421735
theorem B127082591 : Blo 374761 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B475247 : Blo 374761 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B509423 : Blo 374761 509423 := bstep (se 1 (by rfl) ⟨382067, by rfl⟩ : syracuseStep 509423 = 764135) B764135
theorem B2747009 : Blo 374761 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B3610601 : Blo 374761 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B374875 : Blo 374761 374875 := bstep (se 1 (by rfl) ⟨281156, by rfl⟩ : syracuseStep 374875 = 562313) B562313
theorem B16111775 : Blo 374761 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B84721727 : Blo 374761 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B10741183 : Blo 374761 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B1831339 : Blo 374761 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B1267325 : Blo 374761 1267325 := bstep (se 3 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 1267325 = 475247) B475247
theorem B1358461 : Blo 374761 1358461 := bstep (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) B509423
theorem B2407067 : Blo 374761 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B2441785 : Blo 374761 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B1811281 : Blo 374761 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B844883 : Blo 374761 844883 := bstep (se 1 (by rfl) ⟨633662, by rfl⟩ : syracuseStep 844883 = 1267325) B1267325
theorem B56481151 : Blo 374761 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B1604711 : Blo 374761 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B57286309 : Blo 374761 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B4279229 : Blo 374761 4279229 := bstep (se 3 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 4279229 = 1604711) B1604711
theorem B3255713 : Blo 374761 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B563255 : Blo 374761 563255 := bstep (se 1 (by rfl) ⟨422441, by rfl⟩ : syracuseStep 563255 = 844883) B844883
theorem B2415041 : Blo 374761 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B75308201 : Blo 374761 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B76381745 : Blo 374761 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B2852819 : Blo 374761 2852819 := bstep (se 1 (by rfl) ⟨2139614, by rfl⟩ : syracuseStep 2852819 = 4279229) B4279229
theorem B1610027 : Blo 374761 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B50205467 : Blo 374761 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B375503 : Blo 374761 375503 := bstep (se 1 (by rfl) ⟨281627, by rfl⟩ : syracuseStep 375503 = 563255) B563255
theorem B203684653 : Blo 374761 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B2170475 : Blo 374761 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B1073351 : Blo 374761 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B1901879 : Blo 374761 1901879 := bstep (se 1 (by rfl) ⟨1426409, by rfl⟩ : syracuseStep 1901879 = 2852819) B2852819
theorem B1446983 : Blo 374761 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B271579537 : Blo 374761 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B133881245 : Blo 374761 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B89254163 : Blo 374761 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B715567 : Blo 374761 715567 := bstep (se 1 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 715567 = 1073351) B1073351
theorem B362106049 : Blo 374761 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B964655 : Blo 374761 964655 := bstep (se 1 (by rfl) ⟨723491, by rfl⟩ : syracuseStep 964655 = 1446983) B1446983
theorem B1267919 : Blo 374761 1267919 := bstep (se 1 (by rfl) ⟨950939, by rfl⟩ : syracuseStep 1267919 = 1901879) B1901879
theorem B845279 : Blo 374761 845279 := bstep (se 1 (by rfl) ⟨633959, by rfl⟩ : syracuseStep 845279 = 1267919) B1267919
theorem B954089 : Blo 374761 954089 := bstep (se 2 (by rfl) ⟨357783, by rfl⟩ : syracuseStep 954089 = 715567) B715567
theorem B643103 : Blo 374761 643103 := bstep (se 1 (by rfl) ⟨482327, by rfl⟩ : syracuseStep 643103 = 964655) B964655
theorem B59502775 : Blo 374761 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B482808065 : Blo 374761 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B5149952693 : Blo 374761 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B428735 : Blo 374761 428735 := bstep (se 1 (by rfl) ⟨321551, by rfl⟩ : syracuseStep 428735 = 643103) B643103
theorem B636059 : Blo 374761 636059 := bstep (se 1 (by rfl) ⟨477044, by rfl⟩ : syracuseStep 636059 = 954089) B954089
theorem B79337033 : Blo 374761 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B563519 : Blo 374761 563519 := bstep (se 1 (by rfl) ⟨422639, by rfl⟩ : syracuseStep 563519 = 845279) B845279
theorem B3433301795 : Blo 374761 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B52891355 : Blo 374761 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B1143293 : Blo 374761 1143293 := bstep (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) B428735
theorem B424039 : Blo 374761 424039 := bstep (se 1 (by rfl) ⟨318029, by rfl⟩ : syracuseStep 424039 = 636059) B636059
theorem B375679 : Blo 374761 375679 := bstep (se 1 (by rfl) ⟨281759, by rfl⟩ : syracuseStep 375679 = 563519) B563519
theorem B565385 : Blo 374761 565385 := bstep (se 2 (by rfl) ⟨212019, by rfl⟩ : syracuseStep 565385 = 424039) B424039
theorem B3048781 : Blo 374761 3048781 := bstep (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) B1143293
theorem B35260903 : Blo 374761 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B2288867863 : Blo 374761 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B376923 : Blo 374761 376923 := bstep (se 1 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 376923 = 565385) B565385
theorem B3051823817 : Blo 374761 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B4065041 : Blo 374761 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B188058149 : Blo 374761 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B125372099 : Blo 374761 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B8138196845 : Blo 374761 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B2710027 : Blo 374761 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B3613369 : Blo 374761 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B5425464563 : Blo 374761 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B83581399 : Blo 374761 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B4817825 : Blo 374761 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B3616976375 : Blo 374761 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B111441865 : Blo 374761 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B3211883 : Blo 374761 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B2411317583 : Blo 374761 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B148589153 : Blo 374761 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B99059435 : Blo 374761 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B2141255 : Blo 374761 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B1607545055 : Blo 374761 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B1427503 : Blo 374761 1427503 := bstep (se 1 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 1427503 = 2141255) B2141255
theorem B1071696703 : Blo 374761 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B66039623 : Blo 374761 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 374761 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B1903337 : Blo 374761 1903337 := bstep (se 2 (by rfl) ⟨713751, by rfl⟩ : syracuseStep 1903337 = 1427503) B1427503
theorem B1428928937 : Blo 374761 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B952619291 : Blo 374761 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B29350943 : Blo 374761 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B1268891 : Blo 374761 1268891 := bstep (se 1 (by rfl) ⟨951668, by rfl⟩ : syracuseStep 1268891 = 1903337) B1903337
theorem B845927 : Blo 374761 845927 := bstep (se 1 (by rfl) ⟨634445, by rfl⟩ : syracuseStep 845927 = 1268891) B1268891
theorem B635079527 : Blo 374761 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B19567295 : Blo 374761 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 374761 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B563951 : Blo 374761 563951 := bstep (se 1 (by rfl) ⟨422963, by rfl⟩ : syracuseStep 563951 = 845927) B845927
theorem B423386351 : Blo 374761 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B282257567 : Blo 374761 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B8696575 : Blo 374761 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B375967 : Blo 374761 375967 := bstep (se 1 (by rfl) ⟨281975, by rfl⟩ : syracuseStep 375967 = 563951) B563951
theorem B188171711 : Blo 374761 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B11595433 : Blo 374761 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 374761 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B125447807 : Blo 374761 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B10307051 : Blo 374761 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B83631871 : Blo 374761 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B6871367 : Blo 374761 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B446036645 : Blo 374761 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B4580911 : Blo 374761 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B297357763 : Blo 374761 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 374761 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B6107881 : Blo 374761 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 374761 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B264318011 : Blo 374761 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 374761 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B5429227 : Blo 374761 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B117474671 : Blo 374761 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B7238969 : Blo 374761 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 374761 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B313265789 : Blo 374761 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 374761 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B3217319 : Blo 374761 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B139229239 : Blo 374761 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B2144879 : Blo 374761 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B185638985 : Blo 374761 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B1429919 : Blo 374761 1429919 := bstep (se 1 (by rfl) ⟨1072439, by rfl⟩ : syracuseStep 1429919 = 2144879) B2144879
theorem B123759323 : Blo 374761 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B953279 : Blo 374761 953279 := bstep (se 1 (by rfl) ⟨714959, by rfl⟩ : syracuseStep 953279 = 1429919) B1429919
theorem B82506215 : Blo 374761 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B635519 : Blo 374761 635519 := bstep (se 1 (by rfl) ⟨476639, by rfl⟩ : syracuseStep 635519 = 953279) B953279
theorem B55004143 : Blo 374761 55004143 := bstep (se 1 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 55004143 = 82506215) B82506215
theorem B423679 : Blo 374761 423679 := bstep (se 1 (by rfl) ⟨317759, by rfl⟩ : syracuseStep 423679 = 635519) B635519
theorem B73338857 : Blo 374761 73338857 := bstep (se 2 (by rfl) ⟨27502071, by rfl⟩ : syracuseStep 73338857 = 55004143) B55004143
theorem B564905 : Blo 374761 564905 := bstep (se 2 (by rfl) ⟨211839, by rfl⟩ : syracuseStep 564905 = 423679) B423679
theorem B48892571 : Blo 374761 48892571 := bstep (se 1 (by rfl) ⟨36669428, by rfl⟩ : syracuseStep 48892571 = 73338857) B73338857
theorem B376603 : Blo 374761 376603 := bstep (se 1 (by rfl) ⟨282452, by rfl⟩ : syracuseStep 376603 = 564905) B564905
theorem B32595047 : Blo 374761 32595047 := bstep (se 1 (by rfl) ⟨24446285, by rfl⟩ : syracuseStep 32595047 = 48892571) B48892571
theorem B21730031 : Blo 374761 21730031 := bstep (se 1 (by rfl) ⟨16297523, by rfl⟩ : syracuseStep 21730031 = 32595047) B32595047
theorem B14486687 : Blo 374761 14486687 := bstep (se 1 (by rfl) ⟨10865015, by rfl⟩ : syracuseStep 14486687 = 21730031) B21730031
theorem B9657791 : Blo 374761 9657791 := bstep (se 1 (by rfl) ⟨7243343, by rfl⟩ : syracuseStep 9657791 = 14486687) B14486687
theorem B6438527 : Blo 374761 6438527 := bstep (se 1 (by rfl) ⟨4828895, by rfl⟩ : syracuseStep 6438527 = 9657791) B9657791
theorem B4292351 : Blo 374761 4292351 := bstep (se 1 (by rfl) ⟨3219263, by rfl⟩ : syracuseStep 4292351 = 6438527) B6438527
theorem B2861567 : Blo 374761 2861567 := bstep (se 1 (by rfl) ⟨2146175, by rfl⟩ : syracuseStep 2861567 = 4292351) B4292351
theorem B1907711 : Blo 374761 1907711 := bstep (se 1 (by rfl) ⟨1430783, by rfl⟩ : syracuseStep 1907711 = 2861567) B2861567
theorem B1271807 : Blo 374761 1271807 := bstep (se 1 (by rfl) ⟨953855, by rfl⟩ : syracuseStep 1271807 = 1907711) B1907711
theorem B847871 : Blo 374761 847871 := bstep (se 1 (by rfl) ⟨635903, by rfl⟩ : syracuseStep 847871 = 1271807) B1271807
theorem B565247 : Blo 374761 565247 := bstep (se 1 (by rfl) ⟨423935, by rfl⟩ : syracuseStep 565247 = 847871) B847871
theorem B376831 : Blo 374761 376831 := bstep (se 1 (by rfl) ⟨282623, by rfl⟩ : syracuseStep 376831 = 565247) B565247

theorem C0 (j : ℕ) (h1 : 93690 ≤ j) (h2 : j ≤ 94389) : Blo 374761 (4 * j + 3) := by
  interval_cases j
  · exact B374763
  · exact B374767
  · exact B374771
  · exact B374775
  · exact B374779
  · exact B374783
  · exact B374787
  · exact B374791
  · exact B374795
  · exact B374799
  · exact B374803
  · exact B374807
  · exact B374811
  · exact B374815
  · exact B374819
  · exact B374823
  · exact B374827
  · exact B374831
  · exact B374835
  · exact B374839
  · exact B374843
  · exact B374847
  · exact B374851
  · exact B374855
  · exact B374859
  · exact B374863
  · exact B374867
  · exact B374871
  · exact B374875
  · exact B374879
  · exact B374883
  · exact B374887
  · exact B374891
  · exact B374895
  · exact B374899
  · exact B374903
  · exact B374907
  · exact B374911
  · exact B374915
  · exact B374919
  · exact B374923
  · exact B374927
  · exact B374931
  · exact B374935
  · exact B374939
  · exact B374943
  · exact B374947
  · exact B374951
  · exact B374955
  · exact B374959
  · exact B374963
  · exact B374967
  · exact B374971
  · exact B374975
  · exact B374979
  · exact B374983
  · exact B374987
  · exact B374991
  · exact B374995
  · exact B374999
  · exact B375003
  · exact B375007
  · exact B375011
  · exact B375015
  · exact B375019
  · exact B375023
  · exact B375027
  · exact B375031
  · exact B375035
  · exact B375039
  · exact B375043
  · exact B375047
  · exact B375051
  · exact B375055
  · exact B375059
  · exact B375063
  · exact B375067
  · exact B375071
  · exact B375075
  · exact B375079
  · exact B375083
  · exact B375087
  · exact B375091
  · exact B375095
  · exact B375099
  · exact B375103
  · exact B375107
  · exact B375111
  · exact B375115
  · exact B375119
  · exact B375123
  · exact B375127
  · exact B375131
  · exact B375135
  · exact B375139
  · exact B375143
  · exact B375147
  · exact B375151
  · exact B375155
  · exact B375159
  · exact B375163
  · exact B375167
  · exact B375171
  · exact B375175
  · exact B375179
  · exact B375183
  · exact B375187
  · exact B375191
  · exact B375195
  · exact B375199
  · exact B375203
  · exact B375207
  · exact B375211
  · exact B375215
  · exact B375219
  · exact B375223
  · exact B375227
  · exact B375231
  · exact B375235
  · exact B375239
  · exact B375243
  · exact B375247
  · exact B375251
  · exact B375255
  · exact B375259
  · exact B375263
  · exact B375267
  · exact B375271
  · exact B375275
  · exact B375279
  · exact B375283
  · exact B375287
  · exact B375291
  · exact B375295
  · exact B375299
  · exact B375303
  · exact B375307
  · exact B375311
  · exact B375315
  · exact B375319
  · exact B375323
  · exact B375327
  · exact B375331
  · exact B375335
  · exact B375339
  · exact B375343
  · exact B375347
  · exact B375351
  · exact B375355
  · exact B375359
  · exact B375363
  · exact B375367
  · exact B375371
  · exact B375375
  · exact B375379
  · exact B375383
  · exact B375387
  · exact B375391
  · exact B375395
  · exact B375399
  · exact B375403
  · exact B375407
  · exact B375411
  · exact B375415
  · exact B375419
  · exact B375423
  · exact B375427
  · exact B375431
  · exact B375435
  · exact B375439
  · exact B375443
  · exact B375447
  · exact B375451
  · exact B375455
  · exact B375459
  · exact B375463
  · exact B375467
  · exact B375471
  · exact B375475
  · exact B375479
  · exact B375483
  · exact B375487
  · exact B375491
  · exact B375495
  · exact B375499
  · exact B375503
  · exact B375507
  · exact B375511
  · exact B375515
  · exact B375519
  · exact B375523
  · exact B375527
  · exact B375531
  · exact B375535
  · exact B375539
  · exact B375543
  · exact B375547
  · exact B375551
  · exact B375555
  · exact B375559
  · exact B375563
  · exact B375567
  · exact B375571
  · exact B375575
  · exact B375579
  · exact B375583
  · exact B375587
  · exact B375591
  · exact B375595
  · exact B375599
  · exact B375603
  · exact B375607
  · exact B375611
  · exact B375615
  · exact B375619
  · exact B375623
  · exact B375627
  · exact B375631
  · exact B375635
  · exact B375639
  · exact B375643
  · exact B375647
  · exact B375651
  · exact B375655
  · exact B375659
  · exact B375663
  · exact B375667
  · exact B375671
  · exact B375675
  · exact B375679
  · exact B375683
  · exact B375687
  · exact B375691
  · exact B375695
  · exact B375699
  · exact B375703
  · exact B375707
  · exact B375711
  · exact B375715
  · exact B375719
  · exact B375723
  · exact B375727
  · exact B375731
  · exact B375735
  · exact B375739
  · exact B375743
  · exact B375747
  · exact B375751
  · exact B375755
  · exact B375759
  · exact B375763
  · exact B375767
  · exact B375771
  · exact B375775
  · exact B375779
  · exact B375783
  · exact B375787
  · exact B375791
  · exact B375795
  · exact B375799
  · exact B375803
  · exact B375807
  · exact B375811
  · exact B375815
  · exact B375819
  · exact B375823
  · exact B375827
  · exact B375831
  · exact B375835
  · exact B375839
  · exact B375843
  · exact B375847
  · exact B375851
  · exact B375855
  · exact B375859
  · exact B375863
  · exact B375867
  · exact B375871
  · exact B375875
  · exact B375879
  · exact B375883
  · exact B375887
  · exact B375891
  · exact B375895
  · exact B375899
  · exact B375903
  · exact B375907
  · exact B375911
  · exact B375915
  · exact B375919
  · exact B375923
  · exact B375927
  · exact B375931
  · exact B375935
  · exact B375939
  · exact B375943
  · exact B375947
  · exact B375951
  · exact B375955
  · exact B375959
  · exact B375963
  · exact B375967
  · exact B375971
  · exact B375975
  · exact B375979
  · exact B375983
  · exact B375987
  · exact B375991
  · exact B375995
  · exact B375999
  · exact B376003
  · exact B376007
  · exact B376011
  · exact B376015
  · exact B376019
  · exact B376023
  · exact B376027
  · exact B376031
  · exact B376035
  · exact B376039
  · exact B376043
  · exact B376047
  · exact B376051
  · exact B376055
  · exact B376059
  · exact B376063
  · exact B376067
  · exact B376071
  · exact B376075
  · exact B376079
  · exact B376083
  · exact B376087
  · exact B376091
  · exact B376095
  · exact B376099
  · exact B376103
  · exact B376107
  · exact B376111
  · exact B376115
  · exact B376119
  · exact B376123
  · exact B376127
  · exact B376131
  · exact B376135
  · exact B376139
  · exact B376143
  · exact B376147
  · exact B376151
  · exact B376155
  · exact B376159
  · exact B376163
  · exact B376167
  · exact B376171
  · exact B376175
  · exact B376179
  · exact B376183
  · exact B376187
  · exact B376191
  · exact B376195
  · exact B376199
  · exact B376203
  · exact B376207
  · exact B376211
  · exact B376215
  · exact B376219
  · exact B376223
  · exact B376227
  · exact B376231
  · exact B376235
  · exact B376239
  · exact B376243
  · exact B376247
  · exact B376251
  · exact B376255
  · exact B376259
  · exact B376263
  · exact B376267
  · exact B376271
  · exact B376275
  · exact B376279
  · exact B376283
  · exact B376287
  · exact B376291
  · exact B376295
  · exact B376299
  · exact B376303
  · exact B376307
  · exact B376311
  · exact B376315
  · exact B376319
  · exact B376323
  · exact B376327
  · exact B376331
  · exact B376335
  · exact B376339
  · exact B376343
  · exact B376347
  · exact B376351
  · exact B376355
  · exact B376359
  · exact B376363
  · exact B376367
  · exact B376371
  · exact B376375
  · exact B376379
  · exact B376383
  · exact B376387
  · exact B376391
  · exact B376395
  · exact B376399
  · exact B376403
  · exact B376407
  · exact B376411
  · exact B376415
  · exact B376419
  · exact B376423
  · exact B376427
  · exact B376431
  · exact B376435
  · exact B376439
  · exact B376443
  · exact B376447
  · exact B376451
  · exact B376455
  · exact B376459
  · exact B376463
  · exact B376467
  · exact B376471
  · exact B376475
  · exact B376479
  · exact B376483
  · exact B376487
  · exact B376491
  · exact B376495
  · exact B376499
  · exact B376503
  · exact B376507
  · exact B376511
  · exact B376515
  · exact B376519
  · exact B376523
  · exact B376527
  · exact B376531
  · exact B376535
  · exact B376539
  · exact B376543
  · exact B376547
  · exact B376551
  · exact B376555
  · exact B376559
  · exact B376563
  · exact B376567
  · exact B376571
  · exact B376575
  · exact B376579
  · exact B376583
  · exact B376587
  · exact B376591
  · exact B376595
  · exact B376599
  · exact B376603
  · exact B376607
  · exact B376611
  · exact B376615
  · exact B376619
  · exact B376623
  · exact B376627
  · exact B376631
  · exact B376635
  · exact B376639
  · exact B376643
  · exact B376647
  · exact B376651
  · exact B376655
  · exact B376659
  · exact B376663
  · exact B376667
  · exact B376671
  · exact B376675
  · exact B376679
  · exact B376683
  · exact B376687
  · exact B376691
  · exact B376695
  · exact B376699
  · exact B376703
  · exact B376707
  · exact B376711
  · exact B376715
  · exact B376719
  · exact B376723
  · exact B376727
  · exact B376731
  · exact B376735
  · exact B376739
  · exact B376743
  · exact B376747
  · exact B376751
  · exact B376755
  · exact B376759
  · exact B376763
  · exact B376767
  · exact B376771
  · exact B376775
  · exact B376779
  · exact B376783
  · exact B376787
  · exact B376791
  · exact B376795
  · exact B376799
  · exact B376803
  · exact B376807
  · exact B376811
  · exact B376815
  · exact B376819
  · exact B376823
  · exact B376827
  · exact B376831
  · exact B376835
  · exact B376839
  · exact B376843
  · exact B376847
  · exact B376851
  · exact B376855
  · exact B376859
  · exact B376863
  · exact B376867
  · exact B376871
  · exact B376875
  · exact B376879
  · exact B376883
  · exact B376887
  · exact B376891
  · exact B376895
  · exact B376899
  · exact B376903
  · exact B376907
  · exact B376911
  · exact B376915
  · exact B376919
  · exact B376923
  · exact B376927
  · exact B376931
  · exact B376935
  · exact B376939
  · exact B376943
  · exact B376947
  · exact B376951
  · exact B376955
  · exact B376959
  · exact B376963
  · exact B376967
  · exact B376971
  · exact B376975
  · exact B376979
  · exact B376983
  · exact B376987
  · exact B376991
  · exact B376995
  · exact B376999
  · exact B377003
  · exact B377007
  · exact B377011
  · exact B377015
  · exact B377019
  · exact B377023
  · exact B377027
  · exact B377031
  · exact B377035
  · exact B377039
  · exact B377043
  · exact B377047
  · exact B377051
  · exact B377055
  · exact B377059
  · exact B377063
  · exact B377067
  · exact B377071
  · exact B377075
  · exact B377079
  · exact B377083
  · exact B377087
  · exact B377091
  · exact B377095
  · exact B377099
  · exact B377103
  · exact B377107
  · exact B377111
  · exact B377115
  · exact B377119
  · exact B377123
  · exact B377127
  · exact B377131
  · exact B377135
  · exact B377139
  · exact B377143
  · exact B377147
  · exact B377151
  · exact B377155
  · exact B377159
  · exact B377163
  · exact B377167
  · exact B377171
  · exact B377175
  · exact B377179
  · exact B377183
  · exact B377187
  · exact B377191
  · exact B377195
  · exact B377199
  · exact B377203
  · exact B377207
  · exact B377211
  · exact B377215
  · exact B377219
  · exact B377223
  · exact B377227
  · exact B377231
  · exact B377235
  · exact B377239
  · exact B377243
  · exact B377247
  · exact B377251
  · exact B377255
  · exact B377259
  · exact B377263
  · exact B377267
  · exact B377271
  · exact B377275
  · exact B377279
  · exact B377283
  · exact B377287
  · exact B377291
  · exact B377295
  · exact B377299
  · exact B377303
  · exact B377307
  · exact B377311
  · exact B377315
  · exact B377319
  · exact B377323
  · exact B377327
  · exact B377331
  · exact B377335
  · exact B377339
  · exact B377343
  · exact B377347
  · exact B377351
  · exact B377355
  · exact B377359
  · exact B377363
  · exact B377367
  · exact B377371
  · exact B377375
  · exact B377379
  · exact B377383
  · exact B377387
  · exact B377391
  · exact B377395
  · exact B377399
  · exact B377403
  · exact B377407
  · exact B377411
  · exact B377415
  · exact B377419
  · exact B377423
  · exact B377427
  · exact B377431
  · exact B377435
  · exact B377439
  · exact B377443
  · exact B377447
  · exact B377451
  · exact B377455
  · exact B377459
  · exact B377463
  · exact B377467
  · exact B377471
  · exact B377475
  · exact B377479
  · exact B377483
  · exact B377487
  · exact B377491
  · exact B377495
  · exact B377499
  · exact B377503
  · exact B377507
  · exact B377511
  · exact B377515
  · exact B377519
  · exact B377523
  · exact B377527
  · exact B377531
  · exact B377535
  · exact B377539
  · exact B377543
  · exact B377547
  · exact B377551
  · exact B377555
  · exact B377559

theorem C1 (j : ℕ) (h1 : 94390 ≤ j) (h2 : j ≤ 94439) : Blo 374761 (4 * j + 3) := by
  interval_cases j
  · exact B377563
  · exact B377567
  · exact B377571
  · exact B377575
  · exact B377579
  · exact B377583
  · exact B377587
  · exact B377591
  · exact B377595
  · exact B377599
  · exact B377603
  · exact B377607
  · exact B377611
  · exact B377615
  · exact B377619
  · exact B377623
  · exact B377627
  · exact B377631
  · exact B377635
  · exact B377639
  · exact B377643
  · exact B377647
  · exact B377651
  · exact B377655
  · exact B377659
  · exact B377663
  · exact B377667
  · exact B377671
  · exact B377675
  · exact B377679
  · exact B377683
  · exact B377687
  · exact B377691
  · exact B377695
  · exact B377699
  · exact B377703
  · exact B377707
  · exact B377711
  · exact B377715
  · exact B377719
  · exact B377723
  · exact B377727
  · exact B377731
  · exact B377735
  · exact B377739
  · exact B377743
  · exact B377747
  · exact B377751
  · exact B377755
  · exact B377759

theorem solution (m : ℕ) (hlo : 374761 ≤ m) (hhi : m ≤ 377761) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 93690 ≤ j := by omega
    have hj2 : j ≤ 94439 := by omega
    have hb : Blo 374761 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 94390 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
